import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_2_352 : subd19_2 [-1, -3, 2] = true := by decide +kernel
theorem subd19_2_353 : subd19_2 [-1, -3, 3] = true := by decide +kernel
theorem subd19_2_354 : subd19_2 [-1, -3, 4] = true := by decide +kernel
theorem subd19_2_355 : subd19_2 [-1, -3, 5] = true := by decide +kernel
theorem subd19_2_356 : subd19_2 [-1, -3, 6] = true := by decide +kernel
theorem subd19_2_357 : subd19_2 [-1, -2, -8] = true := by decide +kernel
theorem subd19_2_358 : subd19_2 [-1, -2, -7] = true := by decide +kernel
theorem subd19_2_359 : subd19_2 [-1, -2, -6] = true := by decide +kernel
theorem subd19_2_360 : subd19_2 [-1, -2, -5] = true := by decide +kernel
theorem subd19_2_361 : subd19_2 [-1, -2, -4] = true := by decide +kernel
theorem subd19_2_362 : subd19_2 [-1, -2, -3] = true := by decide +kernel
theorem subd19_2_363 : subd19_2 [-1, -2, -2] = true := by decide +kernel
theorem subd19_2_364 : subd19_2 [-1, -2, -1] = true := by decide +kernel
theorem subd19_2_365 : subd19_2 [-1, -2, 0] = true := by decide +kernel
theorem subd19_2_366 : subd19_2 [-1, -2, 1] = true := by decide +kernel
theorem subd19_2_367 : subd19_2 [-1, -2, 2] = true := by decide +kernel
theorem subd19_2_368 : subd19_2 [-1, -2, 3] = true := by decide +kernel
theorem subd19_2_369 : subd19_2 [-1, -2, 4] = true := by decide +kernel
theorem subd19_2_370 : subd19_2 [-1, -2, 5] = true := by decide +kernel
theorem subd19_2_371 : subd19_2 [-1, -2, 6] = true := by decide +kernel
theorem subd19_2_372 : subd19_2 [-1, -2, 7] = true := by decide +kernel
theorem subd19_2_373 : subd19_2 [-1, -1, -8] = true := by decide +kernel
theorem subd19_2_374 : subd19_2 [-1, -1, -7] = true := by decide +kernel
theorem subd19_2_375 : subd19_2 [-1, -1, -6] = true := by decide +kernel
theorem subd19_2_376 : subd19_2 [-1, -1, -5] = true := by decide +kernel
theorem subd19_2_377 : subd19_2 [-1, -1, -4] = true := by decide +kernel
theorem subd19_2_378 : subd19_2 [-1, -1, -3] = true := by decide +kernel
theorem subd19_2_379 : subd19_2 [-1, -1, -2] = true := by decide +kernel
theorem subd19_2_380 : subd19_2 [-1, -1, -1] = true := by decide +kernel
theorem subd19_2_381 : subd19_2 [-1, -1, 0] = true := by decide +kernel
theorem subd19_2_382 : subd19_2 [-1, -1, 1] = true := by decide +kernel
theorem subd19_2_383 : subd19_2 [-1, -1, 2] = true := by decide +kernel
theorem sbd19_2_11 : ∀ q ∈ blkd19_2_11, subd19_2 q = true := by
  unfold blkd19_2_11
  exact List.forall_mem_cons.2 ⟨subd19_2_352, List.forall_mem_cons.2 ⟨subd19_2_353, List.forall_mem_cons.2 ⟨subd19_2_354, List.forall_mem_cons.2 ⟨subd19_2_355, List.forall_mem_cons.2 ⟨subd19_2_356, List.forall_mem_cons.2 ⟨subd19_2_357, List.forall_mem_cons.2 ⟨subd19_2_358, List.forall_mem_cons.2 ⟨subd19_2_359, List.forall_mem_cons.2 ⟨subd19_2_360, List.forall_mem_cons.2 ⟨subd19_2_361, List.forall_mem_cons.2 ⟨subd19_2_362, List.forall_mem_cons.2 ⟨subd19_2_363, List.forall_mem_cons.2 ⟨subd19_2_364, List.forall_mem_cons.2 ⟨subd19_2_365, List.forall_mem_cons.2 ⟨subd19_2_366, List.forall_mem_cons.2 ⟨subd19_2_367, List.forall_mem_cons.2 ⟨subd19_2_368, List.forall_mem_cons.2 ⟨subd19_2_369, List.forall_mem_cons.2 ⟨subd19_2_370, List.forall_mem_cons.2 ⟨subd19_2_371, List.forall_mem_cons.2 ⟨subd19_2_372, List.forall_mem_cons.2 ⟨subd19_2_373, List.forall_mem_cons.2 ⟨subd19_2_374, List.forall_mem_cons.2 ⟨subd19_2_375, List.forall_mem_cons.2 ⟨subd19_2_376, List.forall_mem_cons.2 ⟨subd19_2_377, List.forall_mem_cons.2 ⟨subd19_2_378, List.forall_mem_cons.2 ⟨subd19_2_379, List.forall_mem_cons.2 ⟨subd19_2_380, List.forall_mem_cons.2 ⟨subd19_2_381, List.forall_mem_cons.2 ⟨subd19_2_382, List.forall_mem_cons.2 ⟨subd19_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_384 : subd19_2 [-1, -1, 3] = true := by decide +kernel
theorem subd19_2_385 : subd19_2 [-1, -1, 4] = true := by decide +kernel
theorem subd19_2_386 : subd19_2 [-1, -1, 5] = true := by decide +kernel
theorem subd19_2_387 : subd19_2 [-1, -1, 6] = true := by decide +kernel
theorem subd19_2_388 : subd19_2 [-1, -1, 7] = true := by decide +kernel
theorem subd19_2_389 : subd19_2 [-1, 0, -8] = true := by decide +kernel
theorem subd19_2_390 : subd19_2 [-1, 0, -7] = true := by decide +kernel
theorem subd19_2_391 : subd19_2 [-1, 0, -6] = true := by decide +kernel
theorem subd19_2_392 : subd19_2 [-1, 0, -5] = true := by decide +kernel
theorem subd19_2_393 : subd19_2 [-1, 0, -4] = true := by decide +kernel
theorem subd19_2_394 : subd19_2 [-1, 0, -3] = true := by decide +kernel
theorem subd19_2_395 : subd19_2 [-1, 0, -2] = true := by decide +kernel
theorem subd19_2_396 : subd19_2 [-1, 0, -1] = true := by decide +kernel
theorem subd19_2_397 : subd19_2 [-1, 0, 0] = true := by decide +kernel
theorem subd19_2_398 : subd19_2 [-1, 0, 1] = true := by decide +kernel
theorem subd19_2_399 : subd19_2 [-1, 0, 2] = true := by decide +kernel
theorem subd19_2_400 : subd19_2 [-1, 0, 3] = true := by decide +kernel
theorem subd19_2_401 : subd19_2 [-1, 0, 4] = true := by decide +kernel
theorem subd19_2_402 : subd19_2 [-1, 0, 5] = true := by decide +kernel
theorem subd19_2_403 : subd19_2 [-1, 0, 6] = true := by decide +kernel
theorem subd19_2_404 : subd19_2 [-1, 0, 7] = true := by decide +kernel
theorem subd19_2_405 : subd19_2 [-1, 1, -8] = true := by decide +kernel
theorem subd19_2_406 : subd19_2 [-1, 1, -7] = true := by decide +kernel
theorem subd19_2_407 : subd19_2 [-1, 1, -6] = true := by decide +kernel
theorem subd19_2_408 : subd19_2 [-1, 1, -5] = true := by decide +kernel
theorem subd19_2_409 : subd19_2 [-1, 1, -4] = true := by decide +kernel
theorem subd19_2_410 : subd19_2 [-1, 1, -3] = true := by decide +kernel
theorem subd19_2_411 : subd19_2 [-1, 1, -2] = true := by decide +kernel
theorem subd19_2_412 : subd19_2 [-1, 1, -1] = true := by decide +kernel
theorem subd19_2_413 : subd19_2 [-1, 1, 0] = true := by decide +kernel
theorem subd19_2_414 : subd19_2 [-1, 1, 1] = true := by decide +kernel
theorem subd19_2_415 : subd19_2 [-1, 1, 2] = true := by decide +kernel
theorem sbd19_2_12 : ∀ q ∈ blkd19_2_12, subd19_2 q = true := by
  unfold blkd19_2_12
  exact List.forall_mem_cons.2 ⟨subd19_2_384, List.forall_mem_cons.2 ⟨subd19_2_385, List.forall_mem_cons.2 ⟨subd19_2_386, List.forall_mem_cons.2 ⟨subd19_2_387, List.forall_mem_cons.2 ⟨subd19_2_388, List.forall_mem_cons.2 ⟨subd19_2_389, List.forall_mem_cons.2 ⟨subd19_2_390, List.forall_mem_cons.2 ⟨subd19_2_391, List.forall_mem_cons.2 ⟨subd19_2_392, List.forall_mem_cons.2 ⟨subd19_2_393, List.forall_mem_cons.2 ⟨subd19_2_394, List.forall_mem_cons.2 ⟨subd19_2_395, List.forall_mem_cons.2 ⟨subd19_2_396, List.forall_mem_cons.2 ⟨subd19_2_397, List.forall_mem_cons.2 ⟨subd19_2_398, List.forall_mem_cons.2 ⟨subd19_2_399, List.forall_mem_cons.2 ⟨subd19_2_400, List.forall_mem_cons.2 ⟨subd19_2_401, List.forall_mem_cons.2 ⟨subd19_2_402, List.forall_mem_cons.2 ⟨subd19_2_403, List.forall_mem_cons.2 ⟨subd19_2_404, List.forall_mem_cons.2 ⟨subd19_2_405, List.forall_mem_cons.2 ⟨subd19_2_406, List.forall_mem_cons.2 ⟨subd19_2_407, List.forall_mem_cons.2 ⟨subd19_2_408, List.forall_mem_cons.2 ⟨subd19_2_409, List.forall_mem_cons.2 ⟨subd19_2_410, List.forall_mem_cons.2 ⟨subd19_2_411, List.forall_mem_cons.2 ⟨subd19_2_412, List.forall_mem_cons.2 ⟨subd19_2_413, List.forall_mem_cons.2 ⟨subd19_2_414, List.forall_mem_cons.2 ⟨subd19_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_416 : subd19_2 [-1, 1, 3] = true := by decide +kernel
theorem subd19_2_417 : subd19_2 [-1, 1, 4] = true := by decide +kernel
theorem subd19_2_418 : subd19_2 [-1, 1, 5] = true := by decide +kernel
theorem subd19_2_419 : subd19_2 [-1, 1, 6] = true := by decide +kernel
theorem subd19_2_420 : subd19_2 [-1, 1, 7] = true := by decide +kernel
theorem subd19_2_421 : subd19_2 [-1, 2, -8] = true := by decide +kernel
theorem subd19_2_422 : subd19_2 [-1, 2, -7] = true := by decide +kernel
theorem subd19_2_423 : subd19_2 [-1, 2, -6] = true := by decide +kernel
theorem subd19_2_424 : subd19_2 [-1, 2, -5] = true := by decide +kernel
theorem subd19_2_425 : subd19_2 [-1, 2, -4] = true := by decide +kernel
theorem subd19_2_426 : subd19_2 [-1, 2, -3] = true := by decide +kernel
theorem subd19_2_427 : subd19_2 [-1, 2, -2] = true := by decide +kernel
theorem subd19_2_428 : subd19_2 [-1, 2, -1] = true := by decide +kernel
theorem subd19_2_429 : subd19_2 [-1, 2, 0] = true := by decide +kernel
theorem subd19_2_430 : subd19_2 [-1, 2, 1] = true := by decide +kernel
theorem subd19_2_431 : subd19_2 [-1, 2, 2] = true := by decide +kernel
theorem subd19_2_432 : subd19_2 [-1, 2, 3] = true := by decide +kernel
theorem subd19_2_433 : subd19_2 [-1, 2, 4] = true := by decide +kernel
theorem subd19_2_434 : subd19_2 [-1, 2, 5] = true := by decide +kernel
theorem subd19_2_435 : subd19_2 [-1, 2, 6] = true := by decide +kernel
theorem subd19_2_436 : subd19_2 [-1, 2, 7] = true := by decide +kernel
theorem subd19_2_437 : subd19_2 [-1, 3, -8] = true := by decide +kernel
theorem subd19_2_438 : subd19_2 [-1, 3, -7] = true := by decide +kernel
theorem subd19_2_439 : subd19_2 [-1, 3, -6] = true := by decide +kernel
theorem subd19_2_440 : subd19_2 [-1, 3, -5] = true := by decide +kernel
theorem subd19_2_441 : subd19_2 [-1, 3, -4] = true := by decide +kernel
theorem subd19_2_442 : subd19_2 [-1, 3, -3] = true := by decide +kernel
theorem subd19_2_443 : subd19_2 [-1, 3, -2] = true := by decide +kernel
theorem subd19_2_444 : subd19_2 [-1, 3, -1] = true := by decide +kernel
theorem subd19_2_445 : subd19_2 [-1, 3, 0] = true := by decide +kernel
theorem subd19_2_446 : subd19_2 [-1, 3, 1] = true := by decide +kernel
theorem subd19_2_447 : subd19_2 [-1, 3, 2] = true := by decide +kernel
theorem sbd19_2_13 : ∀ q ∈ blkd19_2_13, subd19_2 q = true := by
  unfold blkd19_2_13
  exact List.forall_mem_cons.2 ⟨subd19_2_416, List.forall_mem_cons.2 ⟨subd19_2_417, List.forall_mem_cons.2 ⟨subd19_2_418, List.forall_mem_cons.2 ⟨subd19_2_419, List.forall_mem_cons.2 ⟨subd19_2_420, List.forall_mem_cons.2 ⟨subd19_2_421, List.forall_mem_cons.2 ⟨subd19_2_422, List.forall_mem_cons.2 ⟨subd19_2_423, List.forall_mem_cons.2 ⟨subd19_2_424, List.forall_mem_cons.2 ⟨subd19_2_425, List.forall_mem_cons.2 ⟨subd19_2_426, List.forall_mem_cons.2 ⟨subd19_2_427, List.forall_mem_cons.2 ⟨subd19_2_428, List.forall_mem_cons.2 ⟨subd19_2_429, List.forall_mem_cons.2 ⟨subd19_2_430, List.forall_mem_cons.2 ⟨subd19_2_431, List.forall_mem_cons.2 ⟨subd19_2_432, List.forall_mem_cons.2 ⟨subd19_2_433, List.forall_mem_cons.2 ⟨subd19_2_434, List.forall_mem_cons.2 ⟨subd19_2_435, List.forall_mem_cons.2 ⟨subd19_2_436, List.forall_mem_cons.2 ⟨subd19_2_437, List.forall_mem_cons.2 ⟨subd19_2_438, List.forall_mem_cons.2 ⟨subd19_2_439, List.forall_mem_cons.2 ⟨subd19_2_440, List.forall_mem_cons.2 ⟨subd19_2_441, List.forall_mem_cons.2 ⟨subd19_2_442, List.forall_mem_cons.2 ⟨subd19_2_443, List.forall_mem_cons.2 ⟨subd19_2_444, List.forall_mem_cons.2 ⟨subd19_2_445, List.forall_mem_cons.2 ⟨subd19_2_446, List.forall_mem_cons.2 ⟨subd19_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_448 : subd19_2 [-1, 3, 3] = true := by decide +kernel
theorem subd19_2_449 : subd19_2 [-1, 3, 4] = true := by decide +kernel
theorem subd19_2_450 : subd19_2 [-1, 3, 5] = true := by decide +kernel
theorem subd19_2_451 : subd19_2 [-1, 3, 6] = true := by decide +kernel
theorem subd19_2_452 : subd19_2 [-1, 3, 7] = true := by decide +kernel
theorem subd19_2_453 : subd19_2 [-1, 4, -7] = true := by decide +kernel
theorem subd19_2_454 : subd19_2 [-1, 4, -6] = true := by decide +kernel
theorem subd19_2_455 : subd19_2 [-1, 4, -5] = true := by decide +kernel
theorem subd19_2_456 : subd19_2 [-1, 4, -4] = true := by decide +kernel
theorem subd19_2_457 : subd19_2 [-1, 4, -3] = true := by decide +kernel
theorem subd19_2_458 : subd19_2 [-1, 4, -2] = true := by decide +kernel
theorem subd19_2_459 : subd19_2 [-1, 4, -1] = true := by decide +kernel
theorem subd19_2_460 : subd19_2 [-1, 4, 0] = true := by decide +kernel
theorem subd19_2_461 : subd19_2 [-1, 4, 1] = true := by decide +kernel
theorem subd19_2_462 : subd19_2 [-1, 4, 2] = true := by decide +kernel
theorem subd19_2_463 : subd19_2 [-1, 4, 3] = true := by decide +kernel
theorem subd19_2_464 : subd19_2 [-1, 4, 4] = true := by decide +kernel
theorem subd19_2_465 : subd19_2 [-1, 4, 5] = true := by decide +kernel
theorem subd19_2_466 : subd19_2 [-1, 4, 6] = true := by decide +kernel
theorem subd19_2_467 : subd19_2 [-1, 5] = true := by decide +kernel
theorem subd19_2_468 : subd19_2 [-1, 6] = true := by decide +kernel
theorem subd19_2_469 : subd19_2 [-1, 7] = true := by decide +kernel
theorem subd19_2_470 : subd19_2 [0, -8] = true := by decide +kernel
theorem subd19_2_471 : subd19_2 [0, -7] = true := by decide +kernel
theorem subd19_2_472 : subd19_2 [0, -6] = true := by decide +kernel
theorem subd19_2_473 : subd19_2 [0, -5] = true := by decide +kernel
theorem subd19_2_474 : subd19_2 [0, -4, -7] = true := by decide +kernel
theorem subd19_2_475 : subd19_2 [0, -4, -6] = true := by decide +kernel
theorem subd19_2_476 : subd19_2 [0, -4, -5] = true := by decide +kernel
theorem subd19_2_477 : subd19_2 [0, -4, -4] = true := by decide +kernel
theorem subd19_2_478 : subd19_2 [0, -4, -3] = true := by decide +kernel
theorem subd19_2_479 : subd19_2 [0, -4, -2] = true := by decide +kernel
theorem sbd19_2_14 : ∀ q ∈ blkd19_2_14, subd19_2 q = true := by
  unfold blkd19_2_14
  exact List.forall_mem_cons.2 ⟨subd19_2_448, List.forall_mem_cons.2 ⟨subd19_2_449, List.forall_mem_cons.2 ⟨subd19_2_450, List.forall_mem_cons.2 ⟨subd19_2_451, List.forall_mem_cons.2 ⟨subd19_2_452, List.forall_mem_cons.2 ⟨subd19_2_453, List.forall_mem_cons.2 ⟨subd19_2_454, List.forall_mem_cons.2 ⟨subd19_2_455, List.forall_mem_cons.2 ⟨subd19_2_456, List.forall_mem_cons.2 ⟨subd19_2_457, List.forall_mem_cons.2 ⟨subd19_2_458, List.forall_mem_cons.2 ⟨subd19_2_459, List.forall_mem_cons.2 ⟨subd19_2_460, List.forall_mem_cons.2 ⟨subd19_2_461, List.forall_mem_cons.2 ⟨subd19_2_462, List.forall_mem_cons.2 ⟨subd19_2_463, List.forall_mem_cons.2 ⟨subd19_2_464, List.forall_mem_cons.2 ⟨subd19_2_465, List.forall_mem_cons.2 ⟨subd19_2_466, List.forall_mem_cons.2 ⟨subd19_2_467, List.forall_mem_cons.2 ⟨subd19_2_468, List.forall_mem_cons.2 ⟨subd19_2_469, List.forall_mem_cons.2 ⟨subd19_2_470, List.forall_mem_cons.2 ⟨subd19_2_471, List.forall_mem_cons.2 ⟨subd19_2_472, List.forall_mem_cons.2 ⟨subd19_2_473, List.forall_mem_cons.2 ⟨subd19_2_474, List.forall_mem_cons.2 ⟨subd19_2_475, List.forall_mem_cons.2 ⟨subd19_2_476, List.forall_mem_cons.2 ⟨subd19_2_477, List.forall_mem_cons.2 ⟨subd19_2_478, List.forall_mem_cons.2 ⟨subd19_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_480 : subd19_2 [0, -4, -1] = true := by decide +kernel
theorem subd19_2_481 : subd19_2 [0, -4, 0] = true := by decide +kernel
theorem subd19_2_482 : subd19_2 [0, -4, 1] = true := by decide +kernel
theorem subd19_2_483 : subd19_2 [0, -4, 2] = true := by decide +kernel
theorem subd19_2_484 : subd19_2 [0, -4, 3] = true := by decide +kernel
theorem subd19_2_485 : subd19_2 [0, -4, 4] = true := by decide +kernel
theorem subd19_2_486 : subd19_2 [0, -4, 5] = true := by decide +kernel
theorem subd19_2_487 : subd19_2 [0, -4, 6] = true := by decide +kernel
theorem subd19_2_488 : subd19_2 [0, -3, -8] = true := by decide +kernel
theorem subd19_2_489 : subd19_2 [0, -3, -7] = true := by decide +kernel
theorem subd19_2_490 : subd19_2 [0, -3, -6] = true := by decide +kernel
theorem subd19_2_491 : subd19_2 [0, -3, -5] = true := by decide +kernel
theorem subd19_2_492 : subd19_2 [0, -3, -4] = true := by decide +kernel
theorem subd19_2_493 : subd19_2 [0, -3, -3] = true := by decide +kernel
theorem subd19_2_494 : subd19_2 [0, -3, -2] = true := by decide +kernel
theorem subd19_2_495 : subd19_2 [0, -3, -1] = true := by decide +kernel
theorem subd19_2_496 : subd19_2 [0, -3, 0] = true := by decide +kernel
theorem subd19_2_497 : subd19_2 [0, -3, 1] = true := by decide +kernel
theorem subd19_2_498 : subd19_2 [0, -3, 2] = true := by decide +kernel
theorem subd19_2_499 : subd19_2 [0, -3, 3] = true := by decide +kernel
theorem subd19_2_500 : subd19_2 [0, -3, 4] = true := by decide +kernel
theorem subd19_2_501 : subd19_2 [0, -3, 5] = true := by decide +kernel
theorem subd19_2_502 : subd19_2 [0, -3, 6] = true := by decide +kernel
theorem subd19_2_503 : subd19_2 [0, -3, 7] = true := by decide +kernel
theorem subd19_2_504 : subd19_2 [0, -2, -8] = true := by decide +kernel
theorem subd19_2_505 : subd19_2 [0, -2, -7] = true := by decide +kernel
theorem subd19_2_506 : subd19_2 [0, -2, -6] = true := by decide +kernel
theorem subd19_2_507 : subd19_2 [0, -2, -5] = true := by decide +kernel
theorem subd19_2_508 : subd19_2 [0, -2, -4] = true := by decide +kernel
theorem subd19_2_509 : subd19_2 [0, -2, -3] = true := by decide +kernel
theorem subd19_2_510 : subd19_2 [0, -2, -2] = true := by decide +kernel
theorem subd19_2_511 : subd19_2 [0, -2, -1] = true := by decide +kernel
theorem sbd19_2_15 : ∀ q ∈ blkd19_2_15, subd19_2 q = true := by
  unfold blkd19_2_15
  exact List.forall_mem_cons.2 ⟨subd19_2_480, List.forall_mem_cons.2 ⟨subd19_2_481, List.forall_mem_cons.2 ⟨subd19_2_482, List.forall_mem_cons.2 ⟨subd19_2_483, List.forall_mem_cons.2 ⟨subd19_2_484, List.forall_mem_cons.2 ⟨subd19_2_485, List.forall_mem_cons.2 ⟨subd19_2_486, List.forall_mem_cons.2 ⟨subd19_2_487, List.forall_mem_cons.2 ⟨subd19_2_488, List.forall_mem_cons.2 ⟨subd19_2_489, List.forall_mem_cons.2 ⟨subd19_2_490, List.forall_mem_cons.2 ⟨subd19_2_491, List.forall_mem_cons.2 ⟨subd19_2_492, List.forall_mem_cons.2 ⟨subd19_2_493, List.forall_mem_cons.2 ⟨subd19_2_494, List.forall_mem_cons.2 ⟨subd19_2_495, List.forall_mem_cons.2 ⟨subd19_2_496, List.forall_mem_cons.2 ⟨subd19_2_497, List.forall_mem_cons.2 ⟨subd19_2_498, List.forall_mem_cons.2 ⟨subd19_2_499, List.forall_mem_cons.2 ⟨subd19_2_500, List.forall_mem_cons.2 ⟨subd19_2_501, List.forall_mem_cons.2 ⟨subd19_2_502, List.forall_mem_cons.2 ⟨subd19_2_503, List.forall_mem_cons.2 ⟨subd19_2_504, List.forall_mem_cons.2 ⟨subd19_2_505, List.forall_mem_cons.2 ⟨subd19_2_506, List.forall_mem_cons.2 ⟨subd19_2_507, List.forall_mem_cons.2 ⟨subd19_2_508, List.forall_mem_cons.2 ⟨subd19_2_509, List.forall_mem_cons.2 ⟨subd19_2_510, List.forall_mem_cons.2 ⟨subd19_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_512 : subd19_2 [0, -2, 0] = true := by decide +kernel
theorem subd19_2_513 : subd19_2 [0, -2, 1] = true := by decide +kernel
theorem subd19_2_514 : subd19_2 [0, -2, 2] = true := by decide +kernel
theorem subd19_2_515 : subd19_2 [0, -2, 3] = true := by decide +kernel
theorem subd19_2_516 : subd19_2 [0, -2, 4] = true := by decide +kernel
theorem subd19_2_517 : subd19_2 [0, -2, 5] = true := by decide +kernel
theorem subd19_2_518 : subd19_2 [0, -2, 6] = true := by decide +kernel
theorem subd19_2_519 : subd19_2 [0, -2, 7] = true := by decide +kernel
theorem subd19_2_520 : subd19_2 [0, -1, -8] = true := by decide +kernel
theorem subd19_2_521 : subd19_2 [0, -1, -7] = true := by decide +kernel
theorem subd19_2_522 : subd19_2 [0, -1, -6] = true := by decide +kernel
theorem subd19_2_523 : subd19_2 [0, -1, -5] = true := by decide +kernel
theorem subd19_2_524 : subd19_2 [0, -1, -4] = true := by decide +kernel
theorem subd19_2_525 : subd19_2 [0, -1, -3] = true := by decide +kernel
theorem subd19_2_526 : subd19_2 [0, -1, -2] = true := by decide +kernel
theorem subd19_2_527 : subd19_2 [0, -1, -1] = true := by decide +kernel
theorem subd19_2_528 : subd19_2 [0, -1, 0] = true := by decide +kernel
theorem subd19_2_529 : subd19_2 [0, -1, 1] = true := by decide +kernel
theorem subd19_2_530 : subd19_2 [0, -1, 2] = true := by decide +kernel
theorem subd19_2_531 : subd19_2 [0, -1, 3] = true := by decide +kernel
theorem subd19_2_532 : subd19_2 [0, -1, 4] = true := by decide +kernel
theorem subd19_2_533 : subd19_2 [0, -1, 5] = true := by decide +kernel
theorem subd19_2_534 : subd19_2 [0, -1, 6] = true := by decide +kernel
theorem subd19_2_535 : subd19_2 [0, -1, 7] = true := by decide +kernel
theorem subd19_2_536 : subd19_2 [0, 0, -8] = true := by decide +kernel
theorem subd19_2_537 : subd19_2 [0, 0, -7] = true := by decide +kernel
theorem subd19_2_538 : subd19_2 [0, 0, -6] = true := by decide +kernel
theorem subd19_2_539 : subd19_2 [0, 0, -5] = true := by decide +kernel
theorem subd19_2_540 : subd19_2 [0, 0, -4] = true := by decide +kernel
theorem subd19_2_541 : subd19_2 [0, 0, -3] = true := by decide +kernel
theorem subd19_2_542 : subd19_2 [0, 0, -2] = true := by decide +kernel
theorem subd19_2_543 : subd19_2 [0, 0, -1] = true := by decide +kernel
theorem sbd19_2_16 : ∀ q ∈ blkd19_2_16, subd19_2 q = true := by
  unfold blkd19_2_16
  exact List.forall_mem_cons.2 ⟨subd19_2_512, List.forall_mem_cons.2 ⟨subd19_2_513, List.forall_mem_cons.2 ⟨subd19_2_514, List.forall_mem_cons.2 ⟨subd19_2_515, List.forall_mem_cons.2 ⟨subd19_2_516, List.forall_mem_cons.2 ⟨subd19_2_517, List.forall_mem_cons.2 ⟨subd19_2_518, List.forall_mem_cons.2 ⟨subd19_2_519, List.forall_mem_cons.2 ⟨subd19_2_520, List.forall_mem_cons.2 ⟨subd19_2_521, List.forall_mem_cons.2 ⟨subd19_2_522, List.forall_mem_cons.2 ⟨subd19_2_523, List.forall_mem_cons.2 ⟨subd19_2_524, List.forall_mem_cons.2 ⟨subd19_2_525, List.forall_mem_cons.2 ⟨subd19_2_526, List.forall_mem_cons.2 ⟨subd19_2_527, List.forall_mem_cons.2 ⟨subd19_2_528, List.forall_mem_cons.2 ⟨subd19_2_529, List.forall_mem_cons.2 ⟨subd19_2_530, List.forall_mem_cons.2 ⟨subd19_2_531, List.forall_mem_cons.2 ⟨subd19_2_532, List.forall_mem_cons.2 ⟨subd19_2_533, List.forall_mem_cons.2 ⟨subd19_2_534, List.forall_mem_cons.2 ⟨subd19_2_535, List.forall_mem_cons.2 ⟨subd19_2_536, List.forall_mem_cons.2 ⟨subd19_2_537, List.forall_mem_cons.2 ⟨subd19_2_538, List.forall_mem_cons.2 ⟨subd19_2_539, List.forall_mem_cons.2 ⟨subd19_2_540, List.forall_mem_cons.2 ⟨subd19_2_541, List.forall_mem_cons.2 ⟨subd19_2_542, List.forall_mem_cons.2 ⟨subd19_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_544 : subd19_2 [0, 0, 0] = true := by decide +kernel
theorem subd19_2_545 : subd19_2 [0, 0, 1] = true := by decide +kernel
theorem subd19_2_546 : subd19_2 [0, 0, 2] = true := by decide +kernel
theorem subd19_2_547 : subd19_2 [0, 0, 3] = true := by decide +kernel
theorem subd19_2_548 : subd19_2 [0, 0, 4] = true := by decide +kernel
theorem subd19_2_549 : subd19_2 [0, 0, 5] = true := by decide +kernel
theorem subd19_2_550 : subd19_2 [0, 0, 6] = true := by decide +kernel
theorem subd19_2_551 : subd19_2 [0, 0, 7] = true := by decide +kernel
theorem subd19_2_552 : subd19_2 [0, 1, -8] = true := by decide +kernel
theorem subd19_2_553 : subd19_2 [0, 1, -7] = true := by decide +kernel
theorem subd19_2_554 : subd19_2 [0, 1, -6] = true := by decide +kernel
theorem subd19_2_555 : subd19_2 [0, 1, -5] = true := by decide +kernel
theorem subd19_2_556 : subd19_2 [0, 1, -4] = true := by decide +kernel
theorem subd19_2_557 : subd19_2 [0, 1, -3] = true := by decide +kernel
theorem subd19_2_558 : subd19_2 [0, 1, -2] = true := by decide +kernel
theorem subd19_2_559 : subd19_2 [0, 1, -1] = true := by decide +kernel
theorem subd19_2_560 : subd19_2 [0, 1, 0] = true := by decide +kernel
theorem subd19_2_561 : subd19_2 [0, 1, 1] = true := by decide +kernel
theorem subd19_2_562 : subd19_2 [0, 1, 2] = true := by decide +kernel
theorem subd19_2_563 : subd19_2 [0, 1, 3] = true := by decide +kernel
theorem subd19_2_564 : subd19_2 [0, 1, 4] = true := by decide +kernel
theorem subd19_2_565 : subd19_2 [0, 1, 5] = true := by decide +kernel
theorem subd19_2_566 : subd19_2 [0, 1, 6] = true := by decide +kernel
theorem subd19_2_567 : subd19_2 [0, 1, 7] = true := by decide +kernel
theorem subd19_2_568 : subd19_2 [0, 2, -8] = true := by decide +kernel
theorem subd19_2_569 : subd19_2 [0, 2, -7] = true := by decide +kernel
theorem subd19_2_570 : subd19_2 [0, 2, -6] = true := by decide +kernel
theorem subd19_2_571 : subd19_2 [0, 2, -5] = true := by decide +kernel
theorem subd19_2_572 : subd19_2 [0, 2, -4] = true := by decide +kernel
theorem subd19_2_573 : subd19_2 [0, 2, -3] = true := by decide +kernel
theorem subd19_2_574 : subd19_2 [0, 2, -2] = true := by decide +kernel
theorem subd19_2_575 : subd19_2 [0, 2, -1] = true := by decide +kernel
theorem sbd19_2_17 : ∀ q ∈ blkd19_2_17, subd19_2 q = true := by
  unfold blkd19_2_17
  exact List.forall_mem_cons.2 ⟨subd19_2_544, List.forall_mem_cons.2 ⟨subd19_2_545, List.forall_mem_cons.2 ⟨subd19_2_546, List.forall_mem_cons.2 ⟨subd19_2_547, List.forall_mem_cons.2 ⟨subd19_2_548, List.forall_mem_cons.2 ⟨subd19_2_549, List.forall_mem_cons.2 ⟨subd19_2_550, List.forall_mem_cons.2 ⟨subd19_2_551, List.forall_mem_cons.2 ⟨subd19_2_552, List.forall_mem_cons.2 ⟨subd19_2_553, List.forall_mem_cons.2 ⟨subd19_2_554, List.forall_mem_cons.2 ⟨subd19_2_555, List.forall_mem_cons.2 ⟨subd19_2_556, List.forall_mem_cons.2 ⟨subd19_2_557, List.forall_mem_cons.2 ⟨subd19_2_558, List.forall_mem_cons.2 ⟨subd19_2_559, List.forall_mem_cons.2 ⟨subd19_2_560, List.forall_mem_cons.2 ⟨subd19_2_561, List.forall_mem_cons.2 ⟨subd19_2_562, List.forall_mem_cons.2 ⟨subd19_2_563, List.forall_mem_cons.2 ⟨subd19_2_564, List.forall_mem_cons.2 ⟨subd19_2_565, List.forall_mem_cons.2 ⟨subd19_2_566, List.forall_mem_cons.2 ⟨subd19_2_567, List.forall_mem_cons.2 ⟨subd19_2_568, List.forall_mem_cons.2 ⟨subd19_2_569, List.forall_mem_cons.2 ⟨subd19_2_570, List.forall_mem_cons.2 ⟨subd19_2_571, List.forall_mem_cons.2 ⟨subd19_2_572, List.forall_mem_cons.2 ⟨subd19_2_573, List.forall_mem_cons.2 ⟨subd19_2_574, List.forall_mem_cons.2 ⟨subd19_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_576 : subd19_2 [0, 2, 0] = true := by decide +kernel
theorem subd19_2_577 : subd19_2 [0, 2, 1] = true := by decide +kernel
theorem subd19_2_578 : subd19_2 [0, 2, 2] = true := by decide +kernel
theorem subd19_2_579 : subd19_2 [0, 2, 3] = true := by decide +kernel
theorem subd19_2_580 : subd19_2 [0, 2, 4] = true := by decide +kernel
theorem subd19_2_581 : subd19_2 [0, 2, 5] = true := by decide +kernel
theorem subd19_2_582 : subd19_2 [0, 2, 6] = true := by decide +kernel
theorem subd19_2_583 : subd19_2 [0, 2, 7] = true := by decide +kernel
theorem subd19_2_584 : subd19_2 [0, 3, -8] = true := by decide +kernel
theorem subd19_2_585 : subd19_2 [0, 3, -7] = true := by decide +kernel
theorem subd19_2_586 : subd19_2 [0, 3, -6] = true := by decide +kernel
theorem subd19_2_587 : subd19_2 [0, 3, -5] = true := by decide +kernel
theorem subd19_2_588 : subd19_2 [0, 3, -4] = true := by decide +kernel
theorem subd19_2_589 : subd19_2 [0, 3, -3] = true := by decide +kernel
theorem subd19_2_590 : subd19_2 [0, 3, -2] = true := by decide +kernel
theorem subd19_2_591 : subd19_2 [0, 3, -1] = true := by decide +kernel
theorem subd19_2_592 : subd19_2 [0, 3, 0] = true := by decide +kernel
theorem subd19_2_593 : subd19_2 [0, 3, 1] = true := by decide +kernel
theorem subd19_2_594 : subd19_2 [0, 3, 2] = true := by decide +kernel
theorem subd19_2_595 : subd19_2 [0, 3, 3] = true := by decide +kernel
theorem subd19_2_596 : subd19_2 [0, 3, 4] = true := by decide +kernel
theorem subd19_2_597 : subd19_2 [0, 3, 5] = true := by decide +kernel
theorem subd19_2_598 : subd19_2 [0, 3, 6] = true := by decide +kernel
theorem subd19_2_599 : subd19_2 [0, 3, 7] = true := by decide +kernel
theorem subd19_2_600 : subd19_2 [0, 4, -7] = true := by decide +kernel
theorem subd19_2_601 : subd19_2 [0, 4, -6] = true := by decide +kernel
theorem subd19_2_602 : subd19_2 [0, 4, -5] = true := by decide +kernel
theorem subd19_2_603 : subd19_2 [0, 4, -4] = true := by decide +kernel
theorem subd19_2_604 : subd19_2 [0, 4, -3] = true := by decide +kernel
theorem subd19_2_605 : subd19_2 [0, 4, -2] = true := by decide +kernel
theorem subd19_2_606 : subd19_2 [0, 4, -1] = true := by decide +kernel
theorem subd19_2_607 : subd19_2 [0, 4, 0] = true := by decide +kernel
theorem sbd19_2_18 : ∀ q ∈ blkd19_2_18, subd19_2 q = true := by
  unfold blkd19_2_18
  exact List.forall_mem_cons.2 ⟨subd19_2_576, List.forall_mem_cons.2 ⟨subd19_2_577, List.forall_mem_cons.2 ⟨subd19_2_578, List.forall_mem_cons.2 ⟨subd19_2_579, List.forall_mem_cons.2 ⟨subd19_2_580, List.forall_mem_cons.2 ⟨subd19_2_581, List.forall_mem_cons.2 ⟨subd19_2_582, List.forall_mem_cons.2 ⟨subd19_2_583, List.forall_mem_cons.2 ⟨subd19_2_584, List.forall_mem_cons.2 ⟨subd19_2_585, List.forall_mem_cons.2 ⟨subd19_2_586, List.forall_mem_cons.2 ⟨subd19_2_587, List.forall_mem_cons.2 ⟨subd19_2_588, List.forall_mem_cons.2 ⟨subd19_2_589, List.forall_mem_cons.2 ⟨subd19_2_590, List.forall_mem_cons.2 ⟨subd19_2_591, List.forall_mem_cons.2 ⟨subd19_2_592, List.forall_mem_cons.2 ⟨subd19_2_593, List.forall_mem_cons.2 ⟨subd19_2_594, List.forall_mem_cons.2 ⟨subd19_2_595, List.forall_mem_cons.2 ⟨subd19_2_596, List.forall_mem_cons.2 ⟨subd19_2_597, List.forall_mem_cons.2 ⟨subd19_2_598, List.forall_mem_cons.2 ⟨subd19_2_599, List.forall_mem_cons.2 ⟨subd19_2_600, List.forall_mem_cons.2 ⟨subd19_2_601, List.forall_mem_cons.2 ⟨subd19_2_602, List.forall_mem_cons.2 ⟨subd19_2_603, List.forall_mem_cons.2 ⟨subd19_2_604, List.forall_mem_cons.2 ⟨subd19_2_605, List.forall_mem_cons.2 ⟨subd19_2_606, List.forall_mem_cons.2 ⟨subd19_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_608 : subd19_2 [0, 4, 1] = true := by decide +kernel
theorem subd19_2_609 : subd19_2 [0, 4, 2] = true := by decide +kernel
theorem subd19_2_610 : subd19_2 [0, 4, 3] = true := by decide +kernel
theorem subd19_2_611 : subd19_2 [0, 4, 4] = true := by decide +kernel
theorem subd19_2_612 : subd19_2 [0, 4, 5] = true := by decide +kernel
theorem subd19_2_613 : subd19_2 [0, 4, 6] = true := by decide +kernel
theorem subd19_2_614 : subd19_2 [0, 5] = true := by decide +kernel
theorem subd19_2_615 : subd19_2 [0, 6] = true := by decide +kernel
theorem subd19_2_616 : subd19_2 [0, 7] = true := by decide +kernel
theorem subd19_2_617 : subd19_2 [1, -8] = true := by decide +kernel
theorem subd19_2_618 : subd19_2 [1, -7] = true := by decide +kernel
theorem subd19_2_619 : subd19_2 [1, -6] = true := by decide +kernel
theorem subd19_2_620 : subd19_2 [1, -5] = true := by decide +kernel
theorem subd19_2_621 : subd19_2 [1, -4, -7] = true := by decide +kernel
theorem subd19_2_622 : subd19_2 [1, -4, -6] = true := by decide +kernel
theorem subd19_2_623 : subd19_2 [1, -4, -5] = true := by decide +kernel
theorem subd19_2_624 : subd19_2 [1, -4, -4] = true := by decide +kernel
theorem subd19_2_625 : subd19_2 [1, -4, -3] = true := by decide +kernel
theorem subd19_2_626 : subd19_2 [1, -4, -2] = true := by decide +kernel
theorem subd19_2_627 : subd19_2 [1, -4, -1] = true := by decide +kernel
theorem subd19_2_628 : subd19_2 [1, -4, 0] = true := by decide +kernel
theorem subd19_2_629 : subd19_2 [1, -4, 1] = true := by decide +kernel
theorem subd19_2_630 : subd19_2 [1, -4, 2] = true := by decide +kernel
theorem subd19_2_631 : subd19_2 [1, -4, 3] = true := by decide +kernel
theorem subd19_2_632 : subd19_2 [1, -4, 4] = true := by decide +kernel
theorem subd19_2_633 : subd19_2 [1, -4, 5] = true := by decide +kernel
theorem subd19_2_634 : subd19_2 [1, -4, 6] = true := by decide +kernel
theorem subd19_2_635 : subd19_2 [1, -3, -8] = true := by decide +kernel
theorem subd19_2_636 : subd19_2 [1, -3, -7] = true := by decide +kernel
theorem subd19_2_637 : subd19_2 [1, -3, -6] = true := by decide +kernel
theorem subd19_2_638 : subd19_2 [1, -3, -5] = true := by decide +kernel
theorem subd19_2_639 : subd19_2 [1, -3, -4] = true := by decide +kernel
theorem sbd19_2_19 : ∀ q ∈ blkd19_2_19, subd19_2 q = true := by
  unfold blkd19_2_19
  exact List.forall_mem_cons.2 ⟨subd19_2_608, List.forall_mem_cons.2 ⟨subd19_2_609, List.forall_mem_cons.2 ⟨subd19_2_610, List.forall_mem_cons.2 ⟨subd19_2_611, List.forall_mem_cons.2 ⟨subd19_2_612, List.forall_mem_cons.2 ⟨subd19_2_613, List.forall_mem_cons.2 ⟨subd19_2_614, List.forall_mem_cons.2 ⟨subd19_2_615, List.forall_mem_cons.2 ⟨subd19_2_616, List.forall_mem_cons.2 ⟨subd19_2_617, List.forall_mem_cons.2 ⟨subd19_2_618, List.forall_mem_cons.2 ⟨subd19_2_619, List.forall_mem_cons.2 ⟨subd19_2_620, List.forall_mem_cons.2 ⟨subd19_2_621, List.forall_mem_cons.2 ⟨subd19_2_622, List.forall_mem_cons.2 ⟨subd19_2_623, List.forall_mem_cons.2 ⟨subd19_2_624, List.forall_mem_cons.2 ⟨subd19_2_625, List.forall_mem_cons.2 ⟨subd19_2_626, List.forall_mem_cons.2 ⟨subd19_2_627, List.forall_mem_cons.2 ⟨subd19_2_628, List.forall_mem_cons.2 ⟨subd19_2_629, List.forall_mem_cons.2 ⟨subd19_2_630, List.forall_mem_cons.2 ⟨subd19_2_631, List.forall_mem_cons.2 ⟨subd19_2_632, List.forall_mem_cons.2 ⟨subd19_2_633, List.forall_mem_cons.2 ⟨subd19_2_634, List.forall_mem_cons.2 ⟨subd19_2_635, List.forall_mem_cons.2 ⟨subd19_2_636, List.forall_mem_cons.2 ⟨subd19_2_637, List.forall_mem_cons.2 ⟨subd19_2_638, List.forall_mem_cons.2 ⟨subd19_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_640 : subd19_2 [1, -3, -3] = true := by decide +kernel
theorem subd19_2_641 : subd19_2 [1, -3, -2] = true := by decide +kernel
theorem subd19_2_642 : subd19_2 [1, -3, -1] = true := by decide +kernel
theorem subd19_2_643 : subd19_2 [1, -3, 0] = true := by decide +kernel
theorem subd19_2_644 : subd19_2 [1, -3, 1] = true := by decide +kernel
theorem subd19_2_645 : subd19_2 [1, -3, 2] = true := by decide +kernel
theorem subd19_2_646 : subd19_2 [1, -3, 3] = true := by decide +kernel
theorem subd19_2_647 : subd19_2 [1, -3, 4] = true := by decide +kernel
theorem subd19_2_648 : subd19_2 [1, -3, 5] = true := by decide +kernel
theorem subd19_2_649 : subd19_2 [1, -3, 6] = true := by decide +kernel
theorem subd19_2_650 : subd19_2 [1, -3, 7] = true := by decide +kernel
theorem subd19_2_651 : subd19_2 [1, -2, -8] = true := by decide +kernel
theorem subd19_2_652 : subd19_2 [1, -2, -7] = true := by decide +kernel
theorem subd19_2_653 : subd19_2 [1, -2, -6] = true := by decide +kernel
theorem subd19_2_654 : subd19_2 [1, -2, -5] = true := by decide +kernel
theorem subd19_2_655 : subd19_2 [1, -2, -4] = true := by decide +kernel
theorem subd19_2_656 : subd19_2 [1, -2, -3] = true := by decide +kernel
theorem subd19_2_657 : subd19_2 [1, -2, -2] = true := by decide +kernel
theorem subd19_2_658 : subd19_2 [1, -2, -1] = true := by decide +kernel
theorem subd19_2_659 : subd19_2 [1, -2, 0] = true := by decide +kernel
theorem subd19_2_660 : subd19_2 [1, -2, 1] = true := by decide +kernel
theorem subd19_2_661 : subd19_2 [1, -2, 2] = true := by decide +kernel
theorem subd19_2_662 : subd19_2 [1, -2, 3] = true := by decide +kernel
theorem subd19_2_663 : subd19_2 [1, -2, 4] = true := by decide +kernel
theorem subd19_2_664 : subd19_2 [1, -2, 5] = true := by decide +kernel
theorem subd19_2_665 : subd19_2 [1, -2, 6] = true := by decide +kernel
theorem subd19_2_666 : subd19_2 [1, -2, 7] = true := by decide +kernel
theorem subd19_2_667 : subd19_2 [1, -1, -8] = true := by decide +kernel
theorem subd19_2_668 : subd19_2 [1, -1, -7] = true := by decide +kernel
theorem subd19_2_669 : subd19_2 [1, -1, -6] = true := by decide +kernel
theorem subd19_2_670 : subd19_2 [1, -1, -5] = true := by decide +kernel
theorem subd19_2_671 : subd19_2 [1, -1, -4] = true := by decide +kernel
theorem sbd19_2_20 : ∀ q ∈ blkd19_2_20, subd19_2 q = true := by
  unfold blkd19_2_20
  exact List.forall_mem_cons.2 ⟨subd19_2_640, List.forall_mem_cons.2 ⟨subd19_2_641, List.forall_mem_cons.2 ⟨subd19_2_642, List.forall_mem_cons.2 ⟨subd19_2_643, List.forall_mem_cons.2 ⟨subd19_2_644, List.forall_mem_cons.2 ⟨subd19_2_645, List.forall_mem_cons.2 ⟨subd19_2_646, List.forall_mem_cons.2 ⟨subd19_2_647, List.forall_mem_cons.2 ⟨subd19_2_648, List.forall_mem_cons.2 ⟨subd19_2_649, List.forall_mem_cons.2 ⟨subd19_2_650, List.forall_mem_cons.2 ⟨subd19_2_651, List.forall_mem_cons.2 ⟨subd19_2_652, List.forall_mem_cons.2 ⟨subd19_2_653, List.forall_mem_cons.2 ⟨subd19_2_654, List.forall_mem_cons.2 ⟨subd19_2_655, List.forall_mem_cons.2 ⟨subd19_2_656, List.forall_mem_cons.2 ⟨subd19_2_657, List.forall_mem_cons.2 ⟨subd19_2_658, List.forall_mem_cons.2 ⟨subd19_2_659, List.forall_mem_cons.2 ⟨subd19_2_660, List.forall_mem_cons.2 ⟨subd19_2_661, List.forall_mem_cons.2 ⟨subd19_2_662, List.forall_mem_cons.2 ⟨subd19_2_663, List.forall_mem_cons.2 ⟨subd19_2_664, List.forall_mem_cons.2 ⟨subd19_2_665, List.forall_mem_cons.2 ⟨subd19_2_666, List.forall_mem_cons.2 ⟨subd19_2_667, List.forall_mem_cons.2 ⟨subd19_2_668, List.forall_mem_cons.2 ⟨subd19_2_669, List.forall_mem_cons.2 ⟨subd19_2_670, List.forall_mem_cons.2 ⟨subd19_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_672 : subd19_2 [1, -1, -3] = true := by decide +kernel
theorem subd19_2_673 : subd19_2 [1, -1, -2] = true := by decide +kernel
theorem subd19_2_674 : subd19_2 [1, -1, -1] = true := by decide +kernel
theorem subd19_2_675 : subd19_2 [1, -1, 0] = true := by decide +kernel
theorem subd19_2_676 : subd19_2 [1, -1, 1] = true := by decide +kernel
theorem subd19_2_677 : subd19_2 [1, -1, 2] = true := by decide +kernel
theorem subd19_2_678 : subd19_2 [1, -1, 3] = true := by decide +kernel
theorem subd19_2_679 : subd19_2 [1, -1, 4] = true := by decide +kernel
theorem subd19_2_680 : subd19_2 [1, -1, 5] = true := by decide +kernel
theorem subd19_2_681 : subd19_2 [1, -1, 6] = true := by decide +kernel
theorem subd19_2_682 : subd19_2 [1, -1, 7] = true := by decide +kernel
theorem subd19_2_683 : subd19_2 [1, 0, -8] = true := by decide +kernel
theorem subd19_2_684 : subd19_2 [1, 0, -7] = true := by decide +kernel
theorem subd19_2_685 : subd19_2 [1, 0, -6] = true := by decide +kernel
theorem subd19_2_686 : subd19_2 [1, 0, -5] = true := by decide +kernel
theorem subd19_2_687 : subd19_2 [1, 0, -4] = true := by decide +kernel
theorem subd19_2_688 : subd19_2 [1, 0, -3] = true := by decide +kernel
theorem subd19_2_689 : subd19_2 [1, 0, -2] = true := by decide +kernel
theorem subd19_2_690 : subd19_2 [1, 0, -1] = true := by decide +kernel
theorem subd19_2_691 : subd19_2 [1, 0, 0] = true := by decide +kernel
theorem subd19_2_692 : subd19_2 [1, 0, 1] = true := by decide +kernel
theorem subd19_2_693 : subd19_2 [1, 0, 2] = true := by decide +kernel
theorem subd19_2_694 : subd19_2 [1, 0, 3] = true := by decide +kernel
theorem subd19_2_695 : subd19_2 [1, 0, 4] = true := by decide +kernel
theorem subd19_2_696 : subd19_2 [1, 0, 5] = true := by decide +kernel
theorem subd19_2_697 : subd19_2 [1, 0, 6] = true := by decide +kernel
theorem subd19_2_698 : subd19_2 [1, 0, 7] = true := by decide +kernel
theorem subd19_2_699 : subd19_2 [1, 1, -8] = true := by decide +kernel
theorem subd19_2_700 : subd19_2 [1, 1, -7] = true := by decide +kernel
theorem subd19_2_701 : subd19_2 [1, 1, -6] = true := by decide +kernel
theorem subd19_2_702 : subd19_2 [1, 1, -5] = true := by decide +kernel
theorem subd19_2_703 : subd19_2 [1, 1, -4] = true := by decide +kernel
theorem sbd19_2_21 : ∀ q ∈ blkd19_2_21, subd19_2 q = true := by
  unfold blkd19_2_21
  exact List.forall_mem_cons.2 ⟨subd19_2_672, List.forall_mem_cons.2 ⟨subd19_2_673, List.forall_mem_cons.2 ⟨subd19_2_674, List.forall_mem_cons.2 ⟨subd19_2_675, List.forall_mem_cons.2 ⟨subd19_2_676, List.forall_mem_cons.2 ⟨subd19_2_677, List.forall_mem_cons.2 ⟨subd19_2_678, List.forall_mem_cons.2 ⟨subd19_2_679, List.forall_mem_cons.2 ⟨subd19_2_680, List.forall_mem_cons.2 ⟨subd19_2_681, List.forall_mem_cons.2 ⟨subd19_2_682, List.forall_mem_cons.2 ⟨subd19_2_683, List.forall_mem_cons.2 ⟨subd19_2_684, List.forall_mem_cons.2 ⟨subd19_2_685, List.forall_mem_cons.2 ⟨subd19_2_686, List.forall_mem_cons.2 ⟨subd19_2_687, List.forall_mem_cons.2 ⟨subd19_2_688, List.forall_mem_cons.2 ⟨subd19_2_689, List.forall_mem_cons.2 ⟨subd19_2_690, List.forall_mem_cons.2 ⟨subd19_2_691, List.forall_mem_cons.2 ⟨subd19_2_692, List.forall_mem_cons.2 ⟨subd19_2_693, List.forall_mem_cons.2 ⟨subd19_2_694, List.forall_mem_cons.2 ⟨subd19_2_695, List.forall_mem_cons.2 ⟨subd19_2_696, List.forall_mem_cons.2 ⟨subd19_2_697, List.forall_mem_cons.2 ⟨subd19_2_698, List.forall_mem_cons.2 ⟨subd19_2_699, List.forall_mem_cons.2 ⟨subd19_2_700, List.forall_mem_cons.2 ⟨subd19_2_701, List.forall_mem_cons.2 ⟨subd19_2_702, List.forall_mem_cons.2 ⟨subd19_2_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_704 : subd19_2 [1, 1, -3] = true := by decide +kernel
theorem subd19_2_705 : subd19_2 [1, 1, -2] = true := by decide +kernel
theorem subd19_2_706 : subd19_2 [1, 1, -1] = true := by decide +kernel
theorem subd19_2_707 : subd19_2 [1, 1, 0] = true := by decide +kernel
theorem subd19_2_708 : subd19_2 [1, 1, 1] = true := by decide +kernel
theorem subd19_2_709 : subd19_2 [1, 1, 2] = true := by decide +kernel
theorem subd19_2_710 : subd19_2 [1, 1, 3] = true := by decide +kernel
theorem subd19_2_711 : subd19_2 [1, 1, 4] = true := by decide +kernel
theorem subd19_2_712 : subd19_2 [1, 1, 5] = true := by decide +kernel
theorem subd19_2_713 : subd19_2 [1, 1, 6] = true := by decide +kernel
theorem subd19_2_714 : subd19_2 [1, 1, 7] = true := by decide +kernel
theorem subd19_2_715 : subd19_2 [1, 2, -8] = true := by decide +kernel
theorem subd19_2_716 : subd19_2 [1, 2, -7] = true := by decide +kernel
theorem subd19_2_717 : subd19_2 [1, 2, -6] = true := by decide +kernel
theorem subd19_2_718 : subd19_2 [1, 2, -5] = true := by decide +kernel
theorem subd19_2_719 : subd19_2 [1, 2, -4] = true := by decide +kernel
theorem subd19_2_720 : subd19_2 [1, 2, -3] = true := by decide +kernel
theorem subd19_2_721 : subd19_2 [1, 2, -2] = true := by decide +kernel
theorem subd19_2_722 : subd19_2 [1, 2, -1] = true := by decide +kernel
theorem subd19_2_723 : subd19_2 [1, 2, 0] = true := by decide +kernel
theorem subd19_2_724 : subd19_2 [1, 2, 1] = true := by decide +kernel
theorem subd19_2_725 : subd19_2 [1, 2, 2] = true := by decide +kernel
theorem subd19_2_726 : subd19_2 [1, 2, 3] = true := by decide +kernel
theorem subd19_2_727 : subd19_2 [1, 2, 4] = true := by decide +kernel
theorem subd19_2_728 : subd19_2 [1, 2, 5] = true := by decide +kernel
theorem subd19_2_729 : subd19_2 [1, 2, 6] = true := by decide +kernel
theorem subd19_2_730 : subd19_2 [1, 2, 7] = true := by decide +kernel
theorem subd19_2_731 : subd19_2 [1, 3, -7] = true := by decide +kernel
theorem subd19_2_732 : subd19_2 [1, 3, -6] = true := by decide +kernel
theorem subd19_2_733 : subd19_2 [1, 3, -5] = true := by decide +kernel
theorem subd19_2_734 : subd19_2 [1, 3, -4] = true := by decide +kernel
theorem subd19_2_735 : subd19_2 [1, 3, -3] = true := by decide +kernel
theorem sbd19_2_22 : ∀ q ∈ blkd19_2_22, subd19_2 q = true := by
  unfold blkd19_2_22
  exact List.forall_mem_cons.2 ⟨subd19_2_704, List.forall_mem_cons.2 ⟨subd19_2_705, List.forall_mem_cons.2 ⟨subd19_2_706, List.forall_mem_cons.2 ⟨subd19_2_707, List.forall_mem_cons.2 ⟨subd19_2_708, List.forall_mem_cons.2 ⟨subd19_2_709, List.forall_mem_cons.2 ⟨subd19_2_710, List.forall_mem_cons.2 ⟨subd19_2_711, List.forall_mem_cons.2 ⟨subd19_2_712, List.forall_mem_cons.2 ⟨subd19_2_713, List.forall_mem_cons.2 ⟨subd19_2_714, List.forall_mem_cons.2 ⟨subd19_2_715, List.forall_mem_cons.2 ⟨subd19_2_716, List.forall_mem_cons.2 ⟨subd19_2_717, List.forall_mem_cons.2 ⟨subd19_2_718, List.forall_mem_cons.2 ⟨subd19_2_719, List.forall_mem_cons.2 ⟨subd19_2_720, List.forall_mem_cons.2 ⟨subd19_2_721, List.forall_mem_cons.2 ⟨subd19_2_722, List.forall_mem_cons.2 ⟨subd19_2_723, List.forall_mem_cons.2 ⟨subd19_2_724, List.forall_mem_cons.2 ⟨subd19_2_725, List.forall_mem_cons.2 ⟨subd19_2_726, List.forall_mem_cons.2 ⟨subd19_2_727, List.forall_mem_cons.2 ⟨subd19_2_728, List.forall_mem_cons.2 ⟨subd19_2_729, List.forall_mem_cons.2 ⟨subd19_2_730, List.forall_mem_cons.2 ⟨subd19_2_731, List.forall_mem_cons.2 ⟨subd19_2_732, List.forall_mem_cons.2 ⟨subd19_2_733, List.forall_mem_cons.2 ⟨subd19_2_734, List.forall_mem_cons.2 ⟨subd19_2_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_736 : subd19_2 [1, 3, -2] = true := by decide +kernel
theorem subd19_2_737 : subd19_2 [1, 3, -1] = true := by decide +kernel
theorem subd19_2_738 : subd19_2 [1, 3, 0] = true := by decide +kernel
theorem subd19_2_739 : subd19_2 [1, 3, 1] = true := by decide +kernel
theorem subd19_2_740 : subd19_2 [1, 3, 2] = true := by decide +kernel
theorem subd19_2_741 : subd19_2 [1, 3, 3] = true := by decide +kernel
theorem subd19_2_742 : subd19_2 [1, 3, 4] = true := by decide +kernel
theorem subd19_2_743 : subd19_2 [1, 3, 5] = true := by decide +kernel
theorem subd19_2_744 : subd19_2 [1, 3, 6] = true := by decide +kernel
theorem subd19_2_745 : subd19_2 [1, 3, 7] = true := by decide +kernel
theorem subd19_2_746 : subd19_2 [1, 4] = true := by decide +kernel
theorem subd19_2_747 : subd19_2 [1, 5] = true := by decide +kernel
theorem subd19_2_748 : subd19_2 [1, 6] = true := by decide +kernel
theorem subd19_2_749 : subd19_2 [2, -8] = true := by decide +kernel
theorem subd19_2_750 : subd19_2 [2, -7] = true := by decide +kernel
theorem subd19_2_751 : subd19_2 [2, -6] = true := by decide +kernel
theorem subd19_2_752 : subd19_2 [2, -5] = true := by decide +kernel
theorem subd19_2_753 : subd19_2 [2, -4, -7] = true := by decide +kernel
theorem subd19_2_754 : subd19_2 [2, -4, -6] = true := by decide +kernel
theorem subd19_2_755 : subd19_2 [2, -4, -5] = true := by decide +kernel
theorem subd19_2_756 : subd19_2 [2, -4, -4] = true := by decide +kernel
theorem subd19_2_757 : subd19_2 [2, -4, -3] = true := by decide +kernel
theorem subd19_2_758 : subd19_2 [2, -4, -2] = true := by decide +kernel
theorem subd19_2_759 : subd19_2 [2, -4, -1] = true := by decide +kernel
theorem subd19_2_760 : subd19_2 [2, -4, 0] = true := by decide +kernel
theorem subd19_2_761 : subd19_2 [2, -4, 1] = true := by decide +kernel
theorem subd19_2_762 : subd19_2 [2, -4, 2] = true := by decide +kernel
theorem subd19_2_763 : subd19_2 [2, -4, 3] = true := by decide +kernel
theorem subd19_2_764 : subd19_2 [2, -4, 4] = true := by decide +kernel
theorem subd19_2_765 : subd19_2 [2, -4, 5] = true := by decide +kernel
theorem subd19_2_766 : subd19_2 [2, -4, 6] = true := by decide +kernel
theorem subd19_2_767 : subd19_2 [2, -4, 7] = true := by decide +kernel
theorem sbd19_2_23 : ∀ q ∈ blkd19_2_23, subd19_2 q = true := by
  unfold blkd19_2_23
  exact List.forall_mem_cons.2 ⟨subd19_2_736, List.forall_mem_cons.2 ⟨subd19_2_737, List.forall_mem_cons.2 ⟨subd19_2_738, List.forall_mem_cons.2 ⟨subd19_2_739, List.forall_mem_cons.2 ⟨subd19_2_740, List.forall_mem_cons.2 ⟨subd19_2_741, List.forall_mem_cons.2 ⟨subd19_2_742, List.forall_mem_cons.2 ⟨subd19_2_743, List.forall_mem_cons.2 ⟨subd19_2_744, List.forall_mem_cons.2 ⟨subd19_2_745, List.forall_mem_cons.2 ⟨subd19_2_746, List.forall_mem_cons.2 ⟨subd19_2_747, List.forall_mem_cons.2 ⟨subd19_2_748, List.forall_mem_cons.2 ⟨subd19_2_749, List.forall_mem_cons.2 ⟨subd19_2_750, List.forall_mem_cons.2 ⟨subd19_2_751, List.forall_mem_cons.2 ⟨subd19_2_752, List.forall_mem_cons.2 ⟨subd19_2_753, List.forall_mem_cons.2 ⟨subd19_2_754, List.forall_mem_cons.2 ⟨subd19_2_755, List.forall_mem_cons.2 ⟨subd19_2_756, List.forall_mem_cons.2 ⟨subd19_2_757, List.forall_mem_cons.2 ⟨subd19_2_758, List.forall_mem_cons.2 ⟨subd19_2_759, List.forall_mem_cons.2 ⟨subd19_2_760, List.forall_mem_cons.2 ⟨subd19_2_761, List.forall_mem_cons.2 ⟨subd19_2_762, List.forall_mem_cons.2 ⟨subd19_2_763, List.forall_mem_cons.2 ⟨subd19_2_764, List.forall_mem_cons.2 ⟨subd19_2_765, List.forall_mem_cons.2 ⟨subd19_2_766, List.forall_mem_cons.2 ⟨subd19_2_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_768 : subd19_2 [2, -3, -7] = true := by decide +kernel
theorem subd19_2_769 : subd19_2 [2, -3, -6] = true := by decide +kernel
theorem subd19_2_770 : subd19_2 [2, -3, -5] = true := by decide +kernel
theorem subd19_2_771 : subd19_2 [2, -3, -4] = true := by decide +kernel
theorem subd19_2_772 : subd19_2 [2, -3, -3] = true := by decide +kernel
theorem subd19_2_773 : subd19_2 [2, -3, -2] = true := by decide +kernel
theorem subd19_2_774 : subd19_2 [2, -3, -1] = true := by decide +kernel
theorem subd19_2_775 : subd19_2 [2, -3, 0] = true := by decide +kernel
theorem subd19_2_776 : subd19_2 [2, -3, 1] = true := by decide +kernel
theorem subd19_2_777 : subd19_2 [2, -3, 2] = true := by decide +kernel
theorem subd19_2_778 : subd19_2 [2, -3, 3] = true := by decide +kernel
theorem subd19_2_779 : subd19_2 [2, -3, 4] = true := by decide +kernel
theorem subd19_2_780 : subd19_2 [2, -3, 5] = true := by decide +kernel
theorem subd19_2_781 : subd19_2 [2, -3, 6] = true := by decide +kernel
theorem subd19_2_782 : subd19_2 [2, -3, 7] = true := by decide +kernel
theorem subd19_2_783 : subd19_2 [2, -2, -8] = true := by decide +kernel
theorem subd19_2_784 : subd19_2 [2, -2, -7] = true := by decide +kernel
theorem subd19_2_785 : subd19_2 [2, -2, -6] = true := by decide +kernel
theorem subd19_2_786 : subd19_2 [2, -2, -5] = true := by decide +kernel
theorem subd19_2_787 : subd19_2 [2, -2, -4] = true := by decide +kernel
theorem subd19_2_788 : subd19_2 [2, -2, -3] = true := by decide +kernel
theorem subd19_2_789 : subd19_2 [2, -2, -2] = true := by decide +kernel
theorem subd19_2_790 : subd19_2 [2, -2, -1] = true := by decide +kernel
theorem subd19_2_791 : subd19_2 [2, -2, 0] = true := by decide +kernel
theorem subd19_2_792 : subd19_2 [2, -2, 1] = true := by decide +kernel
theorem subd19_2_793 : subd19_2 [2, -2, 2] = true := by decide +kernel
theorem subd19_2_794 : subd19_2 [2, -2, 3] = true := by decide +kernel
theorem subd19_2_795 : subd19_2 [2, -2, 4] = true := by decide +kernel
theorem subd19_2_796 : subd19_2 [2, -2, 5] = true := by decide +kernel
theorem subd19_2_797 : subd19_2 [2, -2, 6] = true := by decide +kernel
theorem subd19_2_798 : subd19_2 [2, -2, 7] = true := by decide +kernel
theorem subd19_2_799 : subd19_2 [2, -1, -8] = true := by decide +kernel
theorem sbd19_2_24 : ∀ q ∈ blkd19_2_24, subd19_2 q = true := by
  unfold blkd19_2_24
  exact List.forall_mem_cons.2 ⟨subd19_2_768, List.forall_mem_cons.2 ⟨subd19_2_769, List.forall_mem_cons.2 ⟨subd19_2_770, List.forall_mem_cons.2 ⟨subd19_2_771, List.forall_mem_cons.2 ⟨subd19_2_772, List.forall_mem_cons.2 ⟨subd19_2_773, List.forall_mem_cons.2 ⟨subd19_2_774, List.forall_mem_cons.2 ⟨subd19_2_775, List.forall_mem_cons.2 ⟨subd19_2_776, List.forall_mem_cons.2 ⟨subd19_2_777, List.forall_mem_cons.2 ⟨subd19_2_778, List.forall_mem_cons.2 ⟨subd19_2_779, List.forall_mem_cons.2 ⟨subd19_2_780, List.forall_mem_cons.2 ⟨subd19_2_781, List.forall_mem_cons.2 ⟨subd19_2_782, List.forall_mem_cons.2 ⟨subd19_2_783, List.forall_mem_cons.2 ⟨subd19_2_784, List.forall_mem_cons.2 ⟨subd19_2_785, List.forall_mem_cons.2 ⟨subd19_2_786, List.forall_mem_cons.2 ⟨subd19_2_787, List.forall_mem_cons.2 ⟨subd19_2_788, List.forall_mem_cons.2 ⟨subd19_2_789, List.forall_mem_cons.2 ⟨subd19_2_790, List.forall_mem_cons.2 ⟨subd19_2_791, List.forall_mem_cons.2 ⟨subd19_2_792, List.forall_mem_cons.2 ⟨subd19_2_793, List.forall_mem_cons.2 ⟨subd19_2_794, List.forall_mem_cons.2 ⟨subd19_2_795, List.forall_mem_cons.2 ⟨subd19_2_796, List.forall_mem_cons.2 ⟨subd19_2_797, List.forall_mem_cons.2 ⟨subd19_2_798, List.forall_mem_cons.2 ⟨subd19_2_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_800 : subd19_2 [2, -1, -7] = true := by decide +kernel
theorem subd19_2_801 : subd19_2 [2, -1, -6] = true := by decide +kernel
theorem subd19_2_802 : subd19_2 [2, -1, -5] = true := by decide +kernel
theorem subd19_2_803 : subd19_2 [2, -1, -4] = true := by decide +kernel
theorem subd19_2_804 : subd19_2 [2, -1, -3] = true := by decide +kernel
theorem subd19_2_805 : subd19_2 [2, -1, -2] = true := by decide +kernel
theorem subd19_2_806 : subd19_2 [2, -1, -1] = true := by decide +kernel
theorem subd19_2_807 : subd19_2 [2, -1, 0] = true := by decide +kernel
theorem subd19_2_808 : subd19_2 [2, -1, 1] = true := by decide +kernel
theorem subd19_2_809 : subd19_2 [2, -1, 2] = true := by decide +kernel
theorem subd19_2_810 : subd19_2 [2, -1, 3] = true := by decide +kernel
theorem subd19_2_811 : subd19_2 [2, -1, 4] = true := by decide +kernel
theorem subd19_2_812 : subd19_2 [2, -1, 5] = true := by decide +kernel
theorem subd19_2_813 : subd19_2 [2, -1, 6] = true := by decide +kernel
theorem subd19_2_814 : subd19_2 [2, -1, 7] = true := by decide +kernel
theorem subd19_2_815 : subd19_2 [2, 0, -8] = true := by decide +kernel
theorem subd19_2_816 : subd19_2 [2, 0, -7] = true := by decide +kernel
theorem subd19_2_817 : subd19_2 [2, 0, -6] = true := by decide +kernel
theorem subd19_2_818 : subd19_2 [2, 0, -5] = true := by decide +kernel
theorem subd19_2_819 : subd19_2 [2, 0, -4] = true := by decide +kernel
theorem subd19_2_820 : subd19_2 [2, 0, -3] = true := by decide +kernel
theorem subd19_2_821 : subd19_2 [2, 0, -2] = true := by decide +kernel
theorem subd19_2_822 : subd19_2 [2, 0, -1] = true := by decide +kernel
theorem subd19_2_823 : subd19_2 [2, 0, 0] = true := by decide +kernel
theorem subd19_2_824 : subd19_2 [2, 0, 1] = true := by decide +kernel
theorem subd19_2_825 : subd19_2 [2, 0, 2] = true := by decide +kernel
theorem subd19_2_826 : subd19_2 [2, 0, 3] = true := by decide +kernel
theorem subd19_2_827 : subd19_2 [2, 0, 4] = true := by decide +kernel
theorem subd19_2_828 : subd19_2 [2, 0, 5] = true := by decide +kernel
theorem subd19_2_829 : subd19_2 [2, 0, 6] = true := by decide +kernel
theorem subd19_2_830 : subd19_2 [2, 0, 7] = true := by decide +kernel
theorem subd19_2_831 : subd19_2 [2, 1, -8] = true := by decide +kernel
theorem sbd19_2_25 : ∀ q ∈ blkd19_2_25, subd19_2 q = true := by
  unfold blkd19_2_25
  exact List.forall_mem_cons.2 ⟨subd19_2_800, List.forall_mem_cons.2 ⟨subd19_2_801, List.forall_mem_cons.2 ⟨subd19_2_802, List.forall_mem_cons.2 ⟨subd19_2_803, List.forall_mem_cons.2 ⟨subd19_2_804, List.forall_mem_cons.2 ⟨subd19_2_805, List.forall_mem_cons.2 ⟨subd19_2_806, List.forall_mem_cons.2 ⟨subd19_2_807, List.forall_mem_cons.2 ⟨subd19_2_808, List.forall_mem_cons.2 ⟨subd19_2_809, List.forall_mem_cons.2 ⟨subd19_2_810, List.forall_mem_cons.2 ⟨subd19_2_811, List.forall_mem_cons.2 ⟨subd19_2_812, List.forall_mem_cons.2 ⟨subd19_2_813, List.forall_mem_cons.2 ⟨subd19_2_814, List.forall_mem_cons.2 ⟨subd19_2_815, List.forall_mem_cons.2 ⟨subd19_2_816, List.forall_mem_cons.2 ⟨subd19_2_817, List.forall_mem_cons.2 ⟨subd19_2_818, List.forall_mem_cons.2 ⟨subd19_2_819, List.forall_mem_cons.2 ⟨subd19_2_820, List.forall_mem_cons.2 ⟨subd19_2_821, List.forall_mem_cons.2 ⟨subd19_2_822, List.forall_mem_cons.2 ⟨subd19_2_823, List.forall_mem_cons.2 ⟨subd19_2_824, List.forall_mem_cons.2 ⟨subd19_2_825, List.forall_mem_cons.2 ⟨subd19_2_826, List.forall_mem_cons.2 ⟨subd19_2_827, List.forall_mem_cons.2 ⟨subd19_2_828, List.forall_mem_cons.2 ⟨subd19_2_829, List.forall_mem_cons.2 ⟨subd19_2_830, List.forall_mem_cons.2 ⟨subd19_2_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_832 : subd19_2 [2, 1, -7] = true := by decide +kernel
theorem subd19_2_833 : subd19_2 [2, 1, -6] = true := by decide +kernel
theorem subd19_2_834 : subd19_2 [2, 1, -5] = true := by decide +kernel
theorem subd19_2_835 : subd19_2 [2, 1, -4] = true := by decide +kernel
theorem subd19_2_836 : subd19_2 [2, 1, -3] = true := by decide +kernel
theorem subd19_2_837 : subd19_2 [2, 1, -2] = true := by decide +kernel
theorem subd19_2_838 : subd19_2 [2, 1, -1] = true := by decide +kernel
theorem subd19_2_839 : subd19_2 [2, 1, 0] = true := by decide +kernel
theorem subd19_2_840 : subd19_2 [2, 1, 1] = true := by decide +kernel
theorem subd19_2_841 : subd19_2 [2, 1, 2] = true := by decide +kernel
theorem subd19_2_842 : subd19_2 [2, 1, 3] = true := by decide +kernel
theorem subd19_2_843 : subd19_2 [2, 1, 4] = true := by decide +kernel
theorem subd19_2_844 : subd19_2 [2, 1, 5] = true := by decide +kernel
theorem subd19_2_845 : subd19_2 [2, 1, 6] = true := by decide +kernel
theorem subd19_2_846 : subd19_2 [2, 1, 7] = true := by decide +kernel
theorem subd19_2_847 : subd19_2 [2, 2, -7] = true := by decide +kernel
theorem subd19_2_848 : subd19_2 [2, 2, -6] = true := by decide +kernel
theorem subd19_2_849 : subd19_2 [2, 2, -5] = true := by decide +kernel
theorem subd19_2_850 : subd19_2 [2, 2, -4] = true := by decide +kernel
theorem subd19_2_851 : subd19_2 [2, 2, -3] = true := by decide +kernel
theorem subd19_2_852 : subd19_2 [2, 2, -2] = true := by decide +kernel
theorem subd19_2_853 : subd19_2 [2, 2, -1] = true := by decide +kernel
theorem subd19_2_854 : subd19_2 [2, 2, 0] = true := by decide +kernel
theorem subd19_2_855 : subd19_2 [2, 2, 1] = true := by decide +kernel
theorem subd19_2_856 : subd19_2 [2, 2, 2] = true := by decide +kernel
theorem subd19_2_857 : subd19_2 [2, 2, 3] = true := by decide +kernel
theorem subd19_2_858 : subd19_2 [2, 2, 4] = true := by decide +kernel
theorem subd19_2_859 : subd19_2 [2, 2, 5] = true := by decide +kernel
theorem subd19_2_860 : subd19_2 [2, 2, 6] = true := by decide +kernel
theorem subd19_2_861 : subd19_2 [2, 2, 7] = true := by decide +kernel
theorem subd19_2_862 : subd19_2 [2, 3, -7] = true := by decide +kernel
theorem subd19_2_863 : subd19_2 [2, 3, -6] = true := by decide +kernel
theorem sbd19_2_26 : ∀ q ∈ blkd19_2_26, subd19_2 q = true := by
  unfold blkd19_2_26
  exact List.forall_mem_cons.2 ⟨subd19_2_832, List.forall_mem_cons.2 ⟨subd19_2_833, List.forall_mem_cons.2 ⟨subd19_2_834, List.forall_mem_cons.2 ⟨subd19_2_835, List.forall_mem_cons.2 ⟨subd19_2_836, List.forall_mem_cons.2 ⟨subd19_2_837, List.forall_mem_cons.2 ⟨subd19_2_838, List.forall_mem_cons.2 ⟨subd19_2_839, List.forall_mem_cons.2 ⟨subd19_2_840, List.forall_mem_cons.2 ⟨subd19_2_841, List.forall_mem_cons.2 ⟨subd19_2_842, List.forall_mem_cons.2 ⟨subd19_2_843, List.forall_mem_cons.2 ⟨subd19_2_844, List.forall_mem_cons.2 ⟨subd19_2_845, List.forall_mem_cons.2 ⟨subd19_2_846, List.forall_mem_cons.2 ⟨subd19_2_847, List.forall_mem_cons.2 ⟨subd19_2_848, List.forall_mem_cons.2 ⟨subd19_2_849, List.forall_mem_cons.2 ⟨subd19_2_850, List.forall_mem_cons.2 ⟨subd19_2_851, List.forall_mem_cons.2 ⟨subd19_2_852, List.forall_mem_cons.2 ⟨subd19_2_853, List.forall_mem_cons.2 ⟨subd19_2_854, List.forall_mem_cons.2 ⟨subd19_2_855, List.forall_mem_cons.2 ⟨subd19_2_856, List.forall_mem_cons.2 ⟨subd19_2_857, List.forall_mem_cons.2 ⟨subd19_2_858, List.forall_mem_cons.2 ⟨subd19_2_859, List.forall_mem_cons.2 ⟨subd19_2_860, List.forall_mem_cons.2 ⟨subd19_2_861, List.forall_mem_cons.2 ⟨subd19_2_862, List.forall_mem_cons.2 ⟨subd19_2_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
