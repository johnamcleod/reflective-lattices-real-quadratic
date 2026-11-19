import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_0_352 : subd9_0 [1, 2, 3] = true := by decide +kernel
theorem subd9_0_353 : subd9_0 [1, 2, 4] = true := by decide +kernel
theorem subd9_0_354 : subd9_0 [1, 2, 5] = true := by decide +kernel
theorem subd9_0_355 : subd9_0 [1, 2, 6] = true := by decide +kernel
theorem subd9_0_356 : subd9_0 [1, 3] = true := by decide +kernel
theorem subd9_0_357 : subd9_0 [1, 4] = true := by decide +kernel
theorem subd9_0_358 : subd9_0 [1, 5] = true := by decide +kernel
theorem subd9_0_359 : subd9_0 [1, 6] = true := by decide +kernel
theorem subd9_0_360 : subd9_0 [2, -7] = true := by decide +kernel
theorem subd9_0_361 : subd9_0 [2, -6] = true := by decide +kernel
theorem subd9_0_362 : subd9_0 [2, -5] = true := by decide +kernel
theorem subd9_0_363 : subd9_0 [2, -4] = true := by decide +kernel
theorem subd9_0_364 : subd9_0 [2, -3] = true := by decide +kernel
theorem subd9_0_365 : subd9_0 [2, -2] = true := by decide +kernel
theorem subd9_0_366 : subd9_0 [2, -1, -6] = true := by decide +kernel
theorem subd9_0_367 : subd9_0 [2, -1, -5] = true := by decide +kernel
theorem subd9_0_368 : subd9_0 [2, -1, -4] = true := by decide +kernel
theorem subd9_0_369 : subd9_0 [2, -1, -3] = true := by decide +kernel
theorem subd9_0_370 : subd9_0 [2, -1, -2] = true := by decide +kernel
theorem subd9_0_371 : subd9_0 [2, -1, -1] = true := by decide +kernel
theorem subd9_0_372 : subd9_0 [2, -1, 0] = true := by decide +kernel
theorem subd9_0_373 : subd9_0 [2, -1, 1] = true := by decide +kernel
theorem subd9_0_374 : subd9_0 [2, -1, 2] = true := by decide +kernel
theorem subd9_0_375 : subd9_0 [2, -1, 3] = true := by decide +kernel
theorem subd9_0_376 : subd9_0 [2, -1, 4] = true := by decide +kernel
theorem subd9_0_377 : subd9_0 [2, -1, 5] = true := by decide +kernel
theorem subd9_0_378 : subd9_0 [2, -1, 6] = true := by decide +kernel
theorem subd9_0_379 : subd9_0 [2, -1, 7] = true := by decide +kernel
theorem subd9_0_380 : subd9_0 [2, 0, -7] = true := by decide +kernel
theorem subd9_0_381 : subd9_0 [2, 0, -6] = true := by decide +kernel
theorem subd9_0_382 : subd9_0 [2, 0, -5] = true := by decide +kernel
theorem subd9_0_383 : subd9_0 [2, 0, -4] = true := by decide +kernel
theorem sbd9_0_11 : ∀ q ∈ blkd9_0_11, subd9_0 q = true := by
  unfold blkd9_0_11
  exact List.forall_mem_cons.2 ⟨subd9_0_352, List.forall_mem_cons.2 ⟨subd9_0_353, List.forall_mem_cons.2 ⟨subd9_0_354, List.forall_mem_cons.2 ⟨subd9_0_355, List.forall_mem_cons.2 ⟨subd9_0_356, List.forall_mem_cons.2 ⟨subd9_0_357, List.forall_mem_cons.2 ⟨subd9_0_358, List.forall_mem_cons.2 ⟨subd9_0_359, List.forall_mem_cons.2 ⟨subd9_0_360, List.forall_mem_cons.2 ⟨subd9_0_361, List.forall_mem_cons.2 ⟨subd9_0_362, List.forall_mem_cons.2 ⟨subd9_0_363, List.forall_mem_cons.2 ⟨subd9_0_364, List.forall_mem_cons.2 ⟨subd9_0_365, List.forall_mem_cons.2 ⟨subd9_0_366, List.forall_mem_cons.2 ⟨subd9_0_367, List.forall_mem_cons.2 ⟨subd9_0_368, List.forall_mem_cons.2 ⟨subd9_0_369, List.forall_mem_cons.2 ⟨subd9_0_370, List.forall_mem_cons.2 ⟨subd9_0_371, List.forall_mem_cons.2 ⟨subd9_0_372, List.forall_mem_cons.2 ⟨subd9_0_373, List.forall_mem_cons.2 ⟨subd9_0_374, List.forall_mem_cons.2 ⟨subd9_0_375, List.forall_mem_cons.2 ⟨subd9_0_376, List.forall_mem_cons.2 ⟨subd9_0_377, List.forall_mem_cons.2 ⟨subd9_0_378, List.forall_mem_cons.2 ⟨subd9_0_379, List.forall_mem_cons.2 ⟨subd9_0_380, List.forall_mem_cons.2 ⟨subd9_0_381, List.forall_mem_cons.2 ⟨subd9_0_382, List.forall_mem_cons.2 ⟨subd9_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_384 : subd9_0 [2, 0, -3] = true := by decide +kernel
theorem subd9_0_385 : subd9_0 [2, 0, -2] = true := by decide +kernel
theorem subd9_0_386 : subd9_0 [2, 0, -1] = true := by decide +kernel
theorem subd9_0_387 : subd9_0 [2, 0, 0] = true := by decide +kernel
theorem subd9_0_388 : subd9_0 [2, 0, 1] = true := by decide +kernel
theorem subd9_0_389 : subd9_0 [2, 0, 2] = true := by decide +kernel
theorem subd9_0_390 : subd9_0 [2, 0, 3] = true := by decide +kernel
theorem subd9_0_391 : subd9_0 [2, 0, 4] = true := by decide +kernel
theorem subd9_0_392 : subd9_0 [2, 0, 5] = true := by decide +kernel
theorem subd9_0_393 : subd9_0 [2, 0, 6] = true := by decide +kernel
theorem subd9_0_394 : subd9_0 [2, 0, 7] = true := by decide +kernel
theorem subd9_0_395 : subd9_0 [2, 1, -7] = true := by decide +kernel
theorem subd9_0_396 : subd9_0 [2, 1, -6] = true := by decide +kernel
theorem subd9_0_397 : subd9_0 [2, 1, -5] = true := by decide +kernel
theorem subd9_0_398 : subd9_0 [2, 1, -4] = true := by decide +kernel
theorem subd9_0_399 : subd9_0 [2, 1, -3] = true := by decide +kernel
theorem subd9_0_400 : subd9_0 [2, 1, -2] = true := by decide +kernel
theorem subd9_0_401 : subd9_0 [2, 1, -1] = true := by decide +kernel
theorem subd9_0_402 : subd9_0 [2, 1, 0] = true := by decide +kernel
theorem subd9_0_403 : subd9_0 [2, 1, 1] = true := by decide +kernel
theorem subd9_0_404 : subd9_0 [2, 1, 2] = true := by decide +kernel
theorem subd9_0_405 : subd9_0 [2, 1, 3] = true := by decide +kernel
theorem subd9_0_406 : subd9_0 [2, 1, 4] = true := by decide +kernel
theorem subd9_0_407 : subd9_0 [2, 1, 5] = true := by decide +kernel
theorem subd9_0_408 : subd9_0 [2, 1, 6] = true := by decide +kernel
theorem subd9_0_409 : subd9_0 [2, 1, 7] = true := by decide +kernel
theorem subd9_0_410 : subd9_0 [2, 2, -7] = true := by decide +kernel
theorem subd9_0_411 : subd9_0 [2, 2, -6] = true := by decide +kernel
theorem subd9_0_412 : subd9_0 [2, 2, -5] = true := by decide +kernel
theorem subd9_0_413 : subd9_0 [2, 2, -4] = true := by decide +kernel
theorem subd9_0_414 : subd9_0 [2, 2, -3] = true := by decide +kernel
theorem subd9_0_415 : subd9_0 [2, 2, -2] = true := by decide +kernel
theorem sbd9_0_12 : ∀ q ∈ blkd9_0_12, subd9_0 q = true := by
  unfold blkd9_0_12
  exact List.forall_mem_cons.2 ⟨subd9_0_384, List.forall_mem_cons.2 ⟨subd9_0_385, List.forall_mem_cons.2 ⟨subd9_0_386, List.forall_mem_cons.2 ⟨subd9_0_387, List.forall_mem_cons.2 ⟨subd9_0_388, List.forall_mem_cons.2 ⟨subd9_0_389, List.forall_mem_cons.2 ⟨subd9_0_390, List.forall_mem_cons.2 ⟨subd9_0_391, List.forall_mem_cons.2 ⟨subd9_0_392, List.forall_mem_cons.2 ⟨subd9_0_393, List.forall_mem_cons.2 ⟨subd9_0_394, List.forall_mem_cons.2 ⟨subd9_0_395, List.forall_mem_cons.2 ⟨subd9_0_396, List.forall_mem_cons.2 ⟨subd9_0_397, List.forall_mem_cons.2 ⟨subd9_0_398, List.forall_mem_cons.2 ⟨subd9_0_399, List.forall_mem_cons.2 ⟨subd9_0_400, List.forall_mem_cons.2 ⟨subd9_0_401, List.forall_mem_cons.2 ⟨subd9_0_402, List.forall_mem_cons.2 ⟨subd9_0_403, List.forall_mem_cons.2 ⟨subd9_0_404, List.forall_mem_cons.2 ⟨subd9_0_405, List.forall_mem_cons.2 ⟨subd9_0_406, List.forall_mem_cons.2 ⟨subd9_0_407, List.forall_mem_cons.2 ⟨subd9_0_408, List.forall_mem_cons.2 ⟨subd9_0_409, List.forall_mem_cons.2 ⟨subd9_0_410, List.forall_mem_cons.2 ⟨subd9_0_411, List.forall_mem_cons.2 ⟨subd9_0_412, List.forall_mem_cons.2 ⟨subd9_0_413, List.forall_mem_cons.2 ⟨subd9_0_414, List.forall_mem_cons.2 ⟨subd9_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_416 : subd9_0 [2, 2, -1] = true := by decide +kernel
theorem subd9_0_417 : subd9_0 [2, 2, 0] = true := by decide +kernel
theorem subd9_0_418 : subd9_0 [2, 2, 1] = true := by decide +kernel
theorem subd9_0_419 : subd9_0 [2, 2, 2] = true := by decide +kernel
theorem subd9_0_420 : subd9_0 [2, 2, 3] = true := by decide +kernel
theorem subd9_0_421 : subd9_0 [2, 2, 4] = true := by decide +kernel
theorem subd9_0_422 : subd9_0 [2, 2, 5] = true := by decide +kernel
theorem subd9_0_423 : subd9_0 [2, 2, 6] = true := by decide +kernel
theorem subd9_0_424 : subd9_0 [2, 3] = true := by decide +kernel
theorem subd9_0_425 : subd9_0 [2, 4] = true := by decide +kernel
theorem subd9_0_426 : subd9_0 [2, 5] = true := by decide +kernel
theorem subd9_0_427 : subd9_0 [2, 6] = true := by decide +kernel
theorem subd9_0_428 : subd9_0 [3, -6] = true := by decide +kernel
theorem subd9_0_429 : subd9_0 [3, -5] = true := by decide +kernel
theorem subd9_0_430 : subd9_0 [3, -4] = true := by decide +kernel
theorem subd9_0_431 : subd9_0 [3, -3] = true := by decide +kernel
theorem subd9_0_432 : subd9_0 [3, -2] = true := by decide +kernel
theorem subd9_0_433 : subd9_0 [3, -1] = true := by decide +kernel
theorem subd9_0_434 : subd9_0 [3, 0] = true := by decide +kernel
theorem subd9_0_435 : subd9_0 [3, 1] = true := by decide +kernel
theorem subd9_0_436 : subd9_0 [3, 2] = true := by decide +kernel
theorem subd9_0_437 : subd9_0 [3, 3] = true := by decide +kernel
theorem subd9_0_438 : subd9_0 [3, 4] = true := by decide +kernel
theorem subd9_0_439 : subd9_0 [3, 5] = true := by decide +kernel
theorem subd9_0_440 : subd9_0 [3, 6] = true := by decide +kernel
theorem subd9_0_441 : subd9_0 [4, -5] = true := by decide +kernel
theorem subd9_0_442 : subd9_0 [4, -4] = true := by decide +kernel
theorem subd9_0_443 : subd9_0 [4, -3] = true := by decide +kernel
theorem subd9_0_444 : subd9_0 [4, -2] = true := by decide +kernel
theorem subd9_0_445 : subd9_0 [4, -1] = true := by decide +kernel
theorem subd9_0_446 : subd9_0 [4, 0] = true := by decide +kernel
theorem subd9_0_447 : subd9_0 [4, 1] = true := by decide +kernel
theorem sbd9_0_13 : ∀ q ∈ blkd9_0_13, subd9_0 q = true := by
  unfold blkd9_0_13
  exact List.forall_mem_cons.2 ⟨subd9_0_416, List.forall_mem_cons.2 ⟨subd9_0_417, List.forall_mem_cons.2 ⟨subd9_0_418, List.forall_mem_cons.2 ⟨subd9_0_419, List.forall_mem_cons.2 ⟨subd9_0_420, List.forall_mem_cons.2 ⟨subd9_0_421, List.forall_mem_cons.2 ⟨subd9_0_422, List.forall_mem_cons.2 ⟨subd9_0_423, List.forall_mem_cons.2 ⟨subd9_0_424, List.forall_mem_cons.2 ⟨subd9_0_425, List.forall_mem_cons.2 ⟨subd9_0_426, List.forall_mem_cons.2 ⟨subd9_0_427, List.forall_mem_cons.2 ⟨subd9_0_428, List.forall_mem_cons.2 ⟨subd9_0_429, List.forall_mem_cons.2 ⟨subd9_0_430, List.forall_mem_cons.2 ⟨subd9_0_431, List.forall_mem_cons.2 ⟨subd9_0_432, List.forall_mem_cons.2 ⟨subd9_0_433, List.forall_mem_cons.2 ⟨subd9_0_434, List.forall_mem_cons.2 ⟨subd9_0_435, List.forall_mem_cons.2 ⟨subd9_0_436, List.forall_mem_cons.2 ⟨subd9_0_437, List.forall_mem_cons.2 ⟨subd9_0_438, List.forall_mem_cons.2 ⟨subd9_0_439, List.forall_mem_cons.2 ⟨subd9_0_440, List.forall_mem_cons.2 ⟨subd9_0_441, List.forall_mem_cons.2 ⟨subd9_0_442, List.forall_mem_cons.2 ⟨subd9_0_443, List.forall_mem_cons.2 ⟨subd9_0_444, List.forall_mem_cons.2 ⟨subd9_0_445, List.forall_mem_cons.2 ⟨subd9_0_446, List.forall_mem_cons.2 ⟨subd9_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_448 : subd9_0 [4, 2] = true := by decide +kernel
theorem subd9_0_449 : subd9_0 [4, 3] = true := by decide +kernel
theorem subd9_0_450 : subd9_0 [4, 4] = true := by decide +kernel
theorem subd9_0_451 : subd9_0 [4, 5] = true := by decide +kernel
theorem subd9_0_452 : subd9_0 [4, 6] = true := by decide +kernel
theorem subd9_0_453 : subd9_0 [5, -4] = true := by decide +kernel
theorem subd9_0_454 : subd9_0 [5, -3] = true := by decide +kernel
theorem subd9_0_455 : subd9_0 [5, -2] = true := by decide +kernel
theorem subd9_0_456 : subd9_0 [5, -1] = true := by decide +kernel
theorem subd9_0_457 : subd9_0 [5, 0] = true := by decide +kernel
theorem subd9_0_458 : subd9_0 [5, 1] = true := by decide +kernel
theorem subd9_0_459 : subd9_0 [5, 2] = true := by decide +kernel
theorem subd9_0_460 : subd9_0 [5, 3] = true := by decide +kernel
theorem subd9_0_461 : subd9_0 [5, 4] = true := by decide +kernel
theorem subd9_0_462 : subd9_0 [5, 5] = true := by decide +kernel
theorem subd9_0_463 : subd9_0 [6, -3] = true := by decide +kernel
theorem subd9_0_464 : subd9_0 [6, -2] = true := by decide +kernel
theorem subd9_0_465 : subd9_0 [6, -1] = true := by decide +kernel
theorem subd9_0_466 : subd9_0 [6, 0] = true := by decide +kernel
theorem subd9_0_467 : subd9_0 [6, 1] = true := by decide +kernel
theorem subd9_0_468 : subd9_0 [6, 2] = true := by decide +kernel
theorem subd9_0_469 : subd9_0 [6, 3] = true := by decide +kernel
theorem subd9_0_470 : subd9_0 [6, 4] = true := by decide +kernel
theorem sbd9_0_14 : ∀ q ∈ blkd9_0_14, subd9_0 q = true := by
  unfold blkd9_0_14
  exact List.forall_mem_cons.2 ⟨subd9_0_448, List.forall_mem_cons.2 ⟨subd9_0_449, List.forall_mem_cons.2 ⟨subd9_0_450, List.forall_mem_cons.2 ⟨subd9_0_451, List.forall_mem_cons.2 ⟨subd9_0_452, List.forall_mem_cons.2 ⟨subd9_0_453, List.forall_mem_cons.2 ⟨subd9_0_454, List.forall_mem_cons.2 ⟨subd9_0_455, List.forall_mem_cons.2 ⟨subd9_0_456, List.forall_mem_cons.2 ⟨subd9_0_457, List.forall_mem_cons.2 ⟨subd9_0_458, List.forall_mem_cons.2 ⟨subd9_0_459, List.forall_mem_cons.2 ⟨subd9_0_460, List.forall_mem_cons.2 ⟨subd9_0_461, List.forall_mem_cons.2 ⟨subd9_0_462, List.forall_mem_cons.2 ⟨subd9_0_463, List.forall_mem_cons.2 ⟨subd9_0_464, List.forall_mem_cons.2 ⟨subd9_0_465, List.forall_mem_cons.2 ⟨subd9_0_466, List.forall_mem_cons.2 ⟨subd9_0_467, List.forall_mem_cons.2 ⟨subd9_0_468, List.forall_mem_cons.2 ⟨subd9_0_469, List.forall_mem_cons.2 ⟨subd9_0_470, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [-2, -1] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-2, 0, -11] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [-2, 0, -10] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [-2, 0, -9] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [-2, 0, -8] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [-2, 0, -7] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [-2, 0, -6] = true := by decide +kernel
theorem subd9_1_7 : subd9_1 [-2, 0, -5] = true := by decide +kernel
theorem subd9_1_8 : subd9_1 [-2, 0, -4] = true := by decide +kernel
theorem subd9_1_9 : subd9_1 [-2, 0, -3] = true := by decide +kernel
theorem subd9_1_10 : subd9_1 [-2, 0, -2] = true := by decide +kernel
theorem subd9_1_11 : subd9_1 [-2, 0, -1] = true := by decide +kernel
theorem subd9_1_12 : subd9_1 [-2, 0, 0] = true := by decide +kernel
theorem subd9_1_13 : subd9_1 [-2, 0, 1] = true := by decide +kernel
theorem subd9_1_14 : subd9_1 [-2, 0, 2] = true := by decide +kernel
theorem subd9_1_15 : subd9_1 [-2, 0, 3] = true := by decide +kernel
theorem subd9_1_16 : subd9_1 [-2, 0, 4] = true := by decide +kernel
theorem subd9_1_17 : subd9_1 [-2, 0, 5] = true := by decide +kernel
theorem subd9_1_18 : subd9_1 [-2, 0, 6] = true := by decide +kernel
theorem subd9_1_19 : subd9_1 [-2, 0, 7] = true := by decide +kernel
theorem subd9_1_20 : subd9_1 [-2, 0, 8] = true := by decide +kernel
theorem subd9_1_21 : subd9_1 [-2, 0, 9] = true := by decide +kernel
theorem subd9_1_22 : subd9_1 [-2, 0, 10] = true := by decide +kernel
theorem subd9_1_23 : subd9_1 [-2, 1, -11] = true := by decide +kernel
theorem subd9_1_24 : subd9_1 [-2, 1, -10] = true := by decide +kernel
theorem subd9_1_25 : subd9_1 [-2, 1, -9] = true := by decide +kernel
theorem subd9_1_26 : subd9_1 [-2, 1, -8] = true := by decide +kernel
theorem subd9_1_27 : subd9_1 [-2, 1, -7] = true := by decide +kernel
theorem subd9_1_28 : subd9_1 [-2, 1, -6] = true := by decide +kernel
theorem subd9_1_29 : subd9_1 [-2, 1, -5] = true := by decide +kernel
theorem subd9_1_30 : subd9_1 [-2, 1, -4] = true := by decide +kernel
theorem subd9_1_31 : subd9_1 [-2, 1, -3] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_cons.2 ⟨subd9_1_7, List.forall_mem_cons.2 ⟨subd9_1_8, List.forall_mem_cons.2 ⟨subd9_1_9, List.forall_mem_cons.2 ⟨subd9_1_10, List.forall_mem_cons.2 ⟨subd9_1_11, List.forall_mem_cons.2 ⟨subd9_1_12, List.forall_mem_cons.2 ⟨subd9_1_13, List.forall_mem_cons.2 ⟨subd9_1_14, List.forall_mem_cons.2 ⟨subd9_1_15, List.forall_mem_cons.2 ⟨subd9_1_16, List.forall_mem_cons.2 ⟨subd9_1_17, List.forall_mem_cons.2 ⟨subd9_1_18, List.forall_mem_cons.2 ⟨subd9_1_19, List.forall_mem_cons.2 ⟨subd9_1_20, List.forall_mem_cons.2 ⟨subd9_1_21, List.forall_mem_cons.2 ⟨subd9_1_22, List.forall_mem_cons.2 ⟨subd9_1_23, List.forall_mem_cons.2 ⟨subd9_1_24, List.forall_mem_cons.2 ⟨subd9_1_25, List.forall_mem_cons.2 ⟨subd9_1_26, List.forall_mem_cons.2 ⟨subd9_1_27, List.forall_mem_cons.2 ⟨subd9_1_28, List.forall_mem_cons.2 ⟨subd9_1_29, List.forall_mem_cons.2 ⟨subd9_1_30, List.forall_mem_cons.2 ⟨subd9_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_32 : subd9_1 [-2, 1, -2] = true := by decide +kernel
theorem subd9_1_33 : subd9_1 [-2, 1, -1] = true := by decide +kernel
theorem subd9_1_34 : subd9_1 [-2, 1, 0] = true := by decide +kernel
theorem subd9_1_35 : subd9_1 [-2, 1, 1] = true := by decide +kernel
theorem subd9_1_36 : subd9_1 [-2, 1, 2] = true := by decide +kernel
theorem subd9_1_37 : subd9_1 [-2, 1, 3] = true := by decide +kernel
theorem subd9_1_38 : subd9_1 [-2, 1, 4] = true := by decide +kernel
theorem subd9_1_39 : subd9_1 [-2, 1, 5] = true := by decide +kernel
theorem subd9_1_40 : subd9_1 [-2, 1, 6] = true := by decide +kernel
theorem subd9_1_41 : subd9_1 [-2, 1, 7] = true := by decide +kernel
theorem subd9_1_42 : subd9_1 [-2, 1, 8] = true := by decide +kernel
theorem subd9_1_43 : subd9_1 [-2, 1, 9] = true := by decide +kernel
theorem subd9_1_44 : subd9_1 [-2, 1, 10] = true := by decide +kernel
theorem subd9_1_45 : subd9_1 [-2, 2] = true := by decide +kernel
theorem subd9_1_46 : subd9_1 [-1, -3] = true := by decide +kernel
theorem subd9_1_47 : subd9_1 [-1, -2] = true := by decide +kernel
theorem subd9_1_48 : subd9_1 [-1, -1, -17] = true := by decide +kernel
theorem subd9_1_49 : subd9_1 [-1, -1, -16] = true := by decide +kernel
theorem subd9_1_50 : subd9_1 [-1, -1, -15] = true := by decide +kernel
theorem subd9_1_51 : subd9_1 [-1, -1, -14] = true := by decide +kernel
theorem subd9_1_52 : subd9_1 [-1, -1, -13] = true := by decide +kernel
theorem subd9_1_53 : subd9_1 [-1, -1, -12] = true := by decide +kernel
theorem subd9_1_54 : subd9_1 [-1, -1, -11] = true := by decide +kernel
theorem subd9_1_55 : subd9_1 [-1, -1, -10] = true := by decide +kernel
theorem subd9_1_56 : subd9_1 [-1, -1, -9] = true := by decide +kernel
theorem subd9_1_57 : subd9_1 [-1, -1, -8] = true := by decide +kernel
theorem subd9_1_58 : subd9_1 [-1, -1, -7] = true := by decide +kernel
theorem subd9_1_59 : subd9_1 [-1, -1, -6] = true := by decide +kernel
theorem subd9_1_60 : subd9_1 [-1, -1, -5] = true := by decide +kernel
theorem subd9_1_61 : subd9_1 [-1, -1, -4] = true := by decide +kernel
theorem subd9_1_62 : subd9_1 [-1, -1, -3] = true := by decide +kernel
theorem subd9_1_63 : subd9_1 [-1, -1, -2] = true := by decide +kernel
theorem sbd9_1_1 : ∀ q ∈ blkd9_1_1, subd9_1 q = true := by
  unfold blkd9_1_1
  exact List.forall_mem_cons.2 ⟨subd9_1_32, List.forall_mem_cons.2 ⟨subd9_1_33, List.forall_mem_cons.2 ⟨subd9_1_34, List.forall_mem_cons.2 ⟨subd9_1_35, List.forall_mem_cons.2 ⟨subd9_1_36, List.forall_mem_cons.2 ⟨subd9_1_37, List.forall_mem_cons.2 ⟨subd9_1_38, List.forall_mem_cons.2 ⟨subd9_1_39, List.forall_mem_cons.2 ⟨subd9_1_40, List.forall_mem_cons.2 ⟨subd9_1_41, List.forall_mem_cons.2 ⟨subd9_1_42, List.forall_mem_cons.2 ⟨subd9_1_43, List.forall_mem_cons.2 ⟨subd9_1_44, List.forall_mem_cons.2 ⟨subd9_1_45, List.forall_mem_cons.2 ⟨subd9_1_46, List.forall_mem_cons.2 ⟨subd9_1_47, List.forall_mem_cons.2 ⟨subd9_1_48, List.forall_mem_cons.2 ⟨subd9_1_49, List.forall_mem_cons.2 ⟨subd9_1_50, List.forall_mem_cons.2 ⟨subd9_1_51, List.forall_mem_cons.2 ⟨subd9_1_52, List.forall_mem_cons.2 ⟨subd9_1_53, List.forall_mem_cons.2 ⟨subd9_1_54, List.forall_mem_cons.2 ⟨subd9_1_55, List.forall_mem_cons.2 ⟨subd9_1_56, List.forall_mem_cons.2 ⟨subd9_1_57, List.forall_mem_cons.2 ⟨subd9_1_58, List.forall_mem_cons.2 ⟨subd9_1_59, List.forall_mem_cons.2 ⟨subd9_1_60, List.forall_mem_cons.2 ⟨subd9_1_61, List.forall_mem_cons.2 ⟨subd9_1_62, List.forall_mem_cons.2 ⟨subd9_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_64 : subd9_1 [-1, -1, -1] = true := by decide +kernel
theorem subd9_1_65 : subd9_1 [-1, -1, 0] = true := by decide +kernel
theorem subd9_1_66 : subd9_1 [-1, -1, 1] = true := by decide +kernel
theorem subd9_1_67 : subd9_1 [-1, -1, 2] = true := by decide +kernel
theorem subd9_1_68 : subd9_1 [-1, -1, 3] = true := by decide +kernel
theorem subd9_1_69 : subd9_1 [-1, -1, 4] = true := by decide +kernel
theorem subd9_1_70 : subd9_1 [-1, -1, 5] = true := by decide +kernel
theorem subd9_1_71 : subd9_1 [-1, -1, 6] = true := by decide +kernel
theorem subd9_1_72 : subd9_1 [-1, -1, 7] = true := by decide +kernel
theorem subd9_1_73 : subd9_1 [-1, -1, 8] = true := by decide +kernel
theorem subd9_1_74 : subd9_1 [-1, -1, 9] = true := by decide +kernel
theorem subd9_1_75 : subd9_1 [-1, -1, 10] = true := by decide +kernel
theorem subd9_1_76 : subd9_1 [-1, -1, 11] = true := by decide +kernel
theorem subd9_1_77 : subd9_1 [-1, -1, 12] = true := by decide +kernel
theorem subd9_1_78 : subd9_1 [-1, -1, 13] = true := by decide +kernel
theorem subd9_1_79 : subd9_1 [-1, -1, 14] = true := by decide +kernel
theorem subd9_1_80 : subd9_1 [-1, -1, 15] = true := by decide +kernel
theorem subd9_1_81 : subd9_1 [-1, 0, -19] = true := by decide +kernel
theorem subd9_1_82 : subd9_1 [-1, 0, -18] = true := by decide +kernel
theorem subd9_1_83 : subd9_1 [-1, 0, -17] = true := by decide +kernel
theorem subd9_1_84 : subd9_1 [-1, 0, -16] = true := by decide +kernel
theorem subd9_1_85 : subd9_1 [-1, 0, -15] = true := by decide +kernel
theorem subd9_1_86 : subd9_1 [-1, 0, -14] = true := by decide +kernel
theorem subd9_1_87 : subd9_1 [-1, 0, -13] = true := by decide +kernel
theorem subd9_1_88 : subd9_1 [-1, 0, -12] = true := by decide +kernel
theorem subd9_1_89 : subd9_1 [-1, 0, -11] = true := by decide +kernel
theorem subd9_1_90 : subd9_1 [-1, 0, -10] = true := by decide +kernel
theorem subd9_1_91 : subd9_1 [-1, 0, -9] = true := by decide +kernel
theorem subd9_1_92 : subd9_1 [-1, 0, -8] = true := by decide +kernel
theorem subd9_1_93 : subd9_1 [-1, 0, -7] = true := by decide +kernel
theorem subd9_1_94 : subd9_1 [-1, 0, -6] = true := by decide +kernel
theorem subd9_1_95 : subd9_1 [-1, 0, -5] = true := by decide +kernel
theorem sbd9_1_2 : ∀ q ∈ blkd9_1_2, subd9_1 q = true := by
  unfold blkd9_1_2
  exact List.forall_mem_cons.2 ⟨subd9_1_64, List.forall_mem_cons.2 ⟨subd9_1_65, List.forall_mem_cons.2 ⟨subd9_1_66, List.forall_mem_cons.2 ⟨subd9_1_67, List.forall_mem_cons.2 ⟨subd9_1_68, List.forall_mem_cons.2 ⟨subd9_1_69, List.forall_mem_cons.2 ⟨subd9_1_70, List.forall_mem_cons.2 ⟨subd9_1_71, List.forall_mem_cons.2 ⟨subd9_1_72, List.forall_mem_cons.2 ⟨subd9_1_73, List.forall_mem_cons.2 ⟨subd9_1_74, List.forall_mem_cons.2 ⟨subd9_1_75, List.forall_mem_cons.2 ⟨subd9_1_76, List.forall_mem_cons.2 ⟨subd9_1_77, List.forall_mem_cons.2 ⟨subd9_1_78, List.forall_mem_cons.2 ⟨subd9_1_79, List.forall_mem_cons.2 ⟨subd9_1_80, List.forall_mem_cons.2 ⟨subd9_1_81, List.forall_mem_cons.2 ⟨subd9_1_82, List.forall_mem_cons.2 ⟨subd9_1_83, List.forall_mem_cons.2 ⟨subd9_1_84, List.forall_mem_cons.2 ⟨subd9_1_85, List.forall_mem_cons.2 ⟨subd9_1_86, List.forall_mem_cons.2 ⟨subd9_1_87, List.forall_mem_cons.2 ⟨subd9_1_88, List.forall_mem_cons.2 ⟨subd9_1_89, List.forall_mem_cons.2 ⟨subd9_1_90, List.forall_mem_cons.2 ⟨subd9_1_91, List.forall_mem_cons.2 ⟨subd9_1_92, List.forall_mem_cons.2 ⟨subd9_1_93, List.forall_mem_cons.2 ⟨subd9_1_94, List.forall_mem_cons.2 ⟨subd9_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
