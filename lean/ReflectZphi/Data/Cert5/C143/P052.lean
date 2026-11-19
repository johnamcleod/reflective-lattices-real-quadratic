import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd17_3_352 : subd17_3 [-2, 4, -5] = true := by decide +kernel
theorem subd17_3_353 : subd17_3 [-2, 4, -4] = true := by decide +kernel
theorem subd17_3_354 : subd17_3 [-2, 4, -3] = true := by decide +kernel
theorem subd17_3_355 : subd17_3 [-2, 4, -2] = true := by decide +kernel
theorem subd17_3_356 : subd17_3 [-2, 4, -1] = true := by decide +kernel
theorem subd17_3_357 : subd17_3 [-2, 4, 0] = true := by decide +kernel
theorem subd17_3_358 : subd17_3 [-2, 4, 1] = true := by decide +kernel
theorem subd17_3_359 : subd17_3 [-2, 4, 2] = true := by decide +kernel
theorem subd17_3_360 : subd17_3 [-2, 4, 3] = true := by decide +kernel
theorem subd17_3_361 : subd17_3 [-2, 4, 4] = true := by decide +kernel
theorem subd17_3_362 : subd17_3 [-2, 4, 5] = true := by decide +kernel
theorem subd17_3_363 : subd17_3 [-2, 4, 6] = true := by decide +kernel
theorem subd17_3_364 : subd17_3 [-2, 4, 7] = true := by decide +kernel
theorem subd17_3_365 : subd17_3 [-2, 5] = true := by decide +kernel
theorem subd17_3_366 : subd17_3 [-2, 6] = true := by decide +kernel
theorem subd17_3_367 : subd17_3 [-1, -8] = true := by decide +kernel
theorem subd17_3_368 : subd17_3 [-1, -7] = true := by decide +kernel
theorem subd17_3_369 : subd17_3 [-1, -6] = true := by decide +kernel
theorem subd17_3_370 : subd17_3 [-1, -5, -7] = true := by decide +kernel
theorem subd17_3_371 : subd17_3 [-1, -5, -6] = true := by decide +kernel
theorem subd17_3_372 : subd17_3 [-1, -5, -5] = true := by decide +kernel
theorem subd17_3_373 : subd17_3 [-1, -5, -4] = true := by decide +kernel
theorem subd17_3_374 : subd17_3 [-1, -5, -3] = true := by decide +kernel
theorem subd17_3_375 : subd17_3 [-1, -5, -2] = true := by decide +kernel
theorem subd17_3_376 : subd17_3 [-1, -5, -1] = true := by decide +kernel
theorem subd17_3_377 : subd17_3 [-1, -5, 0] = true := by decide +kernel
theorem subd17_3_378 : subd17_3 [-1, -5, 1] = true := by decide +kernel
theorem subd17_3_379 : subd17_3 [-1, -5, 2] = true := by decide +kernel
theorem subd17_3_380 : subd17_3 [-1, -5, 3] = true := by decide +kernel
theorem subd17_3_381 : subd17_3 [-1, -5, 4] = true := by decide +kernel
theorem subd17_3_382 : subd17_3 [-1, -5, 5] = true := by decide +kernel
theorem subd17_3_383 : subd17_3 [-1, -5, 6] = true := by decide +kernel
theorem sbd17_3_11 : ∀ q ∈ blkd17_3_11, subd17_3 q = true := by
  unfold blkd17_3_11
  exact List.forall_mem_cons.2 ⟨subd17_3_352, List.forall_mem_cons.2 ⟨subd17_3_353, List.forall_mem_cons.2 ⟨subd17_3_354, List.forall_mem_cons.2 ⟨subd17_3_355, List.forall_mem_cons.2 ⟨subd17_3_356, List.forall_mem_cons.2 ⟨subd17_3_357, List.forall_mem_cons.2 ⟨subd17_3_358, List.forall_mem_cons.2 ⟨subd17_3_359, List.forall_mem_cons.2 ⟨subd17_3_360, List.forall_mem_cons.2 ⟨subd17_3_361, List.forall_mem_cons.2 ⟨subd17_3_362, List.forall_mem_cons.2 ⟨subd17_3_363, List.forall_mem_cons.2 ⟨subd17_3_364, List.forall_mem_cons.2 ⟨subd17_3_365, List.forall_mem_cons.2 ⟨subd17_3_366, List.forall_mem_cons.2 ⟨subd17_3_367, List.forall_mem_cons.2 ⟨subd17_3_368, List.forall_mem_cons.2 ⟨subd17_3_369, List.forall_mem_cons.2 ⟨subd17_3_370, List.forall_mem_cons.2 ⟨subd17_3_371, List.forall_mem_cons.2 ⟨subd17_3_372, List.forall_mem_cons.2 ⟨subd17_3_373, List.forall_mem_cons.2 ⟨subd17_3_374, List.forall_mem_cons.2 ⟨subd17_3_375, List.forall_mem_cons.2 ⟨subd17_3_376, List.forall_mem_cons.2 ⟨subd17_3_377, List.forall_mem_cons.2 ⟨subd17_3_378, List.forall_mem_cons.2 ⟨subd17_3_379, List.forall_mem_cons.2 ⟨subd17_3_380, List.forall_mem_cons.2 ⟨subd17_3_381, List.forall_mem_cons.2 ⟨subd17_3_382, List.forall_mem_cons.2 ⟨subd17_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_384 : subd17_3 [-1, -4, -7] = true := by decide +kernel
theorem subd17_3_385 : subd17_3 [-1, -4, -6] = true := by decide +kernel
theorem subd17_3_386 : subd17_3 [-1, -4, -5] = true := by decide +kernel
theorem subd17_3_387 : subd17_3 [-1, -4, -4] = true := by decide +kernel
theorem subd17_3_388 : subd17_3 [-1, -4, -3] = true := by decide +kernel
theorem subd17_3_389 : subd17_3 [-1, -4, -2] = true := by decide +kernel
theorem subd17_3_390 : subd17_3 [-1, -4, -1] = true := by decide +kernel
theorem subd17_3_391 : subd17_3 [-1, -4, 0] = true := by decide +kernel
theorem subd17_3_392 : subd17_3 [-1, -4, 1] = true := by decide +kernel
theorem subd17_3_393 : subd17_3 [-1, -4, 2] = true := by decide +kernel
theorem subd17_3_394 : subd17_3 [-1, -4, 3] = true := by decide +kernel
theorem subd17_3_395 : subd17_3 [-1, -4, 4] = true := by decide +kernel
theorem subd17_3_396 : subd17_3 [-1, -4, 5] = true := by decide +kernel
theorem subd17_3_397 : subd17_3 [-1, -4, 6] = true := by decide +kernel
theorem subd17_3_398 : subd17_3 [-1, -4, 7] = true := by decide +kernel
theorem subd17_3_399 : subd17_3 [-1, -3, -8] = true := by decide +kernel
theorem subd17_3_400 : subd17_3 [-1, -3, -7] = true := by decide +kernel
theorem subd17_3_401 : subd17_3 [-1, -3, -6] = true := by decide +kernel
theorem subd17_3_402 : subd17_3 [-1, -3, -5] = true := by decide +kernel
theorem subd17_3_403 : subd17_3 [-1, -3, -4] = true := by decide +kernel
theorem subd17_3_404 : subd17_3 [-1, -3, -3] = true := by decide +kernel
theorem subd17_3_405 : subd17_3 [-1, -3, -2] = true := by decide +kernel
theorem subd17_3_406 : subd17_3 [-1, -3, -1] = true := by decide +kernel
theorem subd17_3_407 : subd17_3 [-1, -3, 0] = true := by decide +kernel
theorem subd17_3_408 : subd17_3 [-1, -3, 1] = true := by decide +kernel
theorem subd17_3_409 : subd17_3 [-1, -3, 2] = true := by decide +kernel
theorem subd17_3_410 : subd17_3 [-1, -3, 3] = true := by decide +kernel
theorem subd17_3_411 : subd17_3 [-1, -3, 4] = true := by decide +kernel
theorem subd17_3_412 : subd17_3 [-1, -3, 5] = true := by decide +kernel
theorem subd17_3_413 : subd17_3 [-1, -3, 6] = true := by decide +kernel
theorem subd17_3_414 : subd17_3 [-1, -3, 7] = true := by decide +kernel
theorem subd17_3_415 : subd17_3 [-1, -2, -8] = true := by decide +kernel
theorem sbd17_3_12 : ∀ q ∈ blkd17_3_12, subd17_3 q = true := by
  unfold blkd17_3_12
  exact List.forall_mem_cons.2 ⟨subd17_3_384, List.forall_mem_cons.2 ⟨subd17_3_385, List.forall_mem_cons.2 ⟨subd17_3_386, List.forall_mem_cons.2 ⟨subd17_3_387, List.forall_mem_cons.2 ⟨subd17_3_388, List.forall_mem_cons.2 ⟨subd17_3_389, List.forall_mem_cons.2 ⟨subd17_3_390, List.forall_mem_cons.2 ⟨subd17_3_391, List.forall_mem_cons.2 ⟨subd17_3_392, List.forall_mem_cons.2 ⟨subd17_3_393, List.forall_mem_cons.2 ⟨subd17_3_394, List.forall_mem_cons.2 ⟨subd17_3_395, List.forall_mem_cons.2 ⟨subd17_3_396, List.forall_mem_cons.2 ⟨subd17_3_397, List.forall_mem_cons.2 ⟨subd17_3_398, List.forall_mem_cons.2 ⟨subd17_3_399, List.forall_mem_cons.2 ⟨subd17_3_400, List.forall_mem_cons.2 ⟨subd17_3_401, List.forall_mem_cons.2 ⟨subd17_3_402, List.forall_mem_cons.2 ⟨subd17_3_403, List.forall_mem_cons.2 ⟨subd17_3_404, List.forall_mem_cons.2 ⟨subd17_3_405, List.forall_mem_cons.2 ⟨subd17_3_406, List.forall_mem_cons.2 ⟨subd17_3_407, List.forall_mem_cons.2 ⟨subd17_3_408, List.forall_mem_cons.2 ⟨subd17_3_409, List.forall_mem_cons.2 ⟨subd17_3_410, List.forall_mem_cons.2 ⟨subd17_3_411, List.forall_mem_cons.2 ⟨subd17_3_412, List.forall_mem_cons.2 ⟨subd17_3_413, List.forall_mem_cons.2 ⟨subd17_3_414, List.forall_mem_cons.2 ⟨subd17_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_416 : subd17_3 [-1, -2, -7] = true := by decide +kernel
theorem subd17_3_417 : subd17_3 [-1, -2, -6] = true := by decide +kernel
theorem subd17_3_418 : subd17_3 [-1, -2, -5] = true := by decide +kernel
theorem subd17_3_419 : subd17_3 [-1, -2, -4] = true := by decide +kernel
theorem subd17_3_420 : subd17_3 [-1, -2, -3] = true := by decide +kernel
theorem subd17_3_421 : subd17_3 [-1, -2, -2] = true := by decide +kernel
theorem subd17_3_422 : subd17_3 [-1, -2, -1] = true := by decide +kernel
theorem subd17_3_423 : subd17_3 [-1, -2, 0] = true := by decide +kernel
theorem subd17_3_424 : subd17_3 [-1, -2, 1] = true := by decide +kernel
theorem subd17_3_425 : subd17_3 [-1, -2, 2] = true := by decide +kernel
theorem subd17_3_426 : subd17_3 [-1, -2, 3] = true := by decide +kernel
theorem subd17_3_427 : subd17_3 [-1, -2, 4] = true := by decide +kernel
theorem subd17_3_428 : subd17_3 [-1, -2, 5] = true := by decide +kernel
theorem subd17_3_429 : subd17_3 [-1, -2, 6] = true := by decide +kernel
theorem subd17_3_430 : subd17_3 [-1, -2, 7] = true := by decide +kernel
theorem subd17_3_431 : subd17_3 [-1, -2, 8] = true := by decide +kernel
theorem subd17_3_432 : subd17_3 [-1, -1, -8] = true := by decide +kernel
theorem subd17_3_433 : subd17_3 [-1, -1, -7] = true := by decide +kernel
theorem subd17_3_434 : subd17_3 [-1, -1, -6] = true := by decide +kernel
theorem subd17_3_435 : subd17_3 [-1, -1, -5] = true := by decide +kernel
theorem subd17_3_436 : subd17_3 [-1, -1, -4] = true := by decide +kernel
theorem subd17_3_437 : subd17_3 [-1, -1, -3] = true := by decide +kernel
theorem subd17_3_438 : subd17_3 [-1, -1, -2] = true := by decide +kernel
theorem subd17_3_439 : subd17_3 [-1, -1, -1] = true := by decide +kernel
theorem subd17_3_440 : subd17_3 [-1, -1, 0] = true := by decide +kernel
theorem subd17_3_441 : subd17_3 [-1, -1, 1] = true := by decide +kernel
theorem subd17_3_442 : subd17_3 [-1, -1, 2] = true := by decide +kernel
theorem subd17_3_443 : subd17_3 [-1, -1, 3] = true := by decide +kernel
theorem subd17_3_444 : subd17_3 [-1, -1, 4] = true := by decide +kernel
theorem subd17_3_445 : subd17_3 [-1, -1, 5] = true := by decide +kernel
theorem subd17_3_446 : subd17_3 [-1, -1, 6] = true := by decide +kernel
theorem subd17_3_447 : subd17_3 [-1, -1, 7] = true := by decide +kernel
theorem sbd17_3_13 : ∀ q ∈ blkd17_3_13, subd17_3 q = true := by
  unfold blkd17_3_13
  exact List.forall_mem_cons.2 ⟨subd17_3_416, List.forall_mem_cons.2 ⟨subd17_3_417, List.forall_mem_cons.2 ⟨subd17_3_418, List.forall_mem_cons.2 ⟨subd17_3_419, List.forall_mem_cons.2 ⟨subd17_3_420, List.forall_mem_cons.2 ⟨subd17_3_421, List.forall_mem_cons.2 ⟨subd17_3_422, List.forall_mem_cons.2 ⟨subd17_3_423, List.forall_mem_cons.2 ⟨subd17_3_424, List.forall_mem_cons.2 ⟨subd17_3_425, List.forall_mem_cons.2 ⟨subd17_3_426, List.forall_mem_cons.2 ⟨subd17_3_427, List.forall_mem_cons.2 ⟨subd17_3_428, List.forall_mem_cons.2 ⟨subd17_3_429, List.forall_mem_cons.2 ⟨subd17_3_430, List.forall_mem_cons.2 ⟨subd17_3_431, List.forall_mem_cons.2 ⟨subd17_3_432, List.forall_mem_cons.2 ⟨subd17_3_433, List.forall_mem_cons.2 ⟨subd17_3_434, List.forall_mem_cons.2 ⟨subd17_3_435, List.forall_mem_cons.2 ⟨subd17_3_436, List.forall_mem_cons.2 ⟨subd17_3_437, List.forall_mem_cons.2 ⟨subd17_3_438, List.forall_mem_cons.2 ⟨subd17_3_439, List.forall_mem_cons.2 ⟨subd17_3_440, List.forall_mem_cons.2 ⟨subd17_3_441, List.forall_mem_cons.2 ⟨subd17_3_442, List.forall_mem_cons.2 ⟨subd17_3_443, List.forall_mem_cons.2 ⟨subd17_3_444, List.forall_mem_cons.2 ⟨subd17_3_445, List.forall_mem_cons.2 ⟨subd17_3_446, List.forall_mem_cons.2 ⟨subd17_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_448 : subd17_3 [-1, -1, 8] = true := by decide +kernel
theorem subd17_3_449 : subd17_3 [-1, 0, -8] = true := by decide +kernel
theorem subd17_3_450 : subd17_3 [-1, 0, -7] = true := by decide +kernel
theorem subd17_3_451 : subd17_3 [-1, 0, -6] = true := by decide +kernel
theorem subd17_3_452 : subd17_3 [-1, 0, -5] = true := by decide +kernel
theorem subd17_3_453 : subd17_3 [-1, 0, -4] = true := by decide +kernel
theorem subd17_3_454 : subd17_3 [-1, 0, -3] = true := by decide +kernel
theorem subd17_3_455 : subd17_3 [-1, 0, -2] = true := by decide +kernel
theorem subd17_3_456 : subd17_3 [-1, 0, -1] = true := by decide +kernel
theorem subd17_3_457 : subd17_3 [-1, 0, 0] = true := by decide +kernel
theorem subd17_3_458 : subd17_3 [-1, 0, 1] = true := by decide +kernel
theorem subd17_3_459 : subd17_3 [-1, 0, 2] = true := by decide +kernel
theorem subd17_3_460 : subd17_3 [-1, 0, 3] = true := by decide +kernel
theorem subd17_3_461 : subd17_3 [-1, 0, 4] = true := by decide +kernel
theorem subd17_3_462 : subd17_3 [-1, 0, 5] = true := by decide +kernel
theorem subd17_3_463 : subd17_3 [-1, 0, 6] = true := by decide +kernel
theorem subd17_3_464 : subd17_3 [-1, 0, 7] = true := by decide +kernel
theorem subd17_3_465 : subd17_3 [-1, 0, 8] = true := by decide +kernel
theorem subd17_3_466 : subd17_3 [-1, 1, -8] = true := by decide +kernel
theorem subd17_3_467 : subd17_3 [-1, 1, -7] = true := by decide +kernel
theorem subd17_3_468 : subd17_3 [-1, 1, -6] = true := by decide +kernel
theorem subd17_3_469 : subd17_3 [-1, 1, -5] = true := by decide +kernel
theorem subd17_3_470 : subd17_3 [-1, 1, -4] = true := by decide +kernel
theorem subd17_3_471 : subd17_3 [-1, 1, -3] = true := by decide +kernel
theorem subd17_3_472 : subd17_3 [-1, 1, -2] = true := by decide +kernel
theorem subd17_3_473 : subd17_3 [-1, 1, -1] = true := by decide +kernel
theorem subd17_3_474 : subd17_3 [-1, 1, 0] = true := by decide +kernel
theorem subd17_3_475 : subd17_3 [-1, 1, 1] = true := by decide +kernel
theorem subd17_3_476 : subd17_3 [-1, 1, 2] = true := by decide +kernel
theorem subd17_3_477 : subd17_3 [-1, 1, 3] = true := by decide +kernel
theorem subd17_3_478 : subd17_3 [-1, 1, 4] = true := by decide +kernel
theorem subd17_3_479 : subd17_3 [-1, 1, 5] = true := by decide +kernel
theorem sbd17_3_14 : ∀ q ∈ blkd17_3_14, subd17_3 q = true := by
  unfold blkd17_3_14
  exact List.forall_mem_cons.2 ⟨subd17_3_448, List.forall_mem_cons.2 ⟨subd17_3_449, List.forall_mem_cons.2 ⟨subd17_3_450, List.forall_mem_cons.2 ⟨subd17_3_451, List.forall_mem_cons.2 ⟨subd17_3_452, List.forall_mem_cons.2 ⟨subd17_3_453, List.forall_mem_cons.2 ⟨subd17_3_454, List.forall_mem_cons.2 ⟨subd17_3_455, List.forall_mem_cons.2 ⟨subd17_3_456, List.forall_mem_cons.2 ⟨subd17_3_457, List.forall_mem_cons.2 ⟨subd17_3_458, List.forall_mem_cons.2 ⟨subd17_3_459, List.forall_mem_cons.2 ⟨subd17_3_460, List.forall_mem_cons.2 ⟨subd17_3_461, List.forall_mem_cons.2 ⟨subd17_3_462, List.forall_mem_cons.2 ⟨subd17_3_463, List.forall_mem_cons.2 ⟨subd17_3_464, List.forall_mem_cons.2 ⟨subd17_3_465, List.forall_mem_cons.2 ⟨subd17_3_466, List.forall_mem_cons.2 ⟨subd17_3_467, List.forall_mem_cons.2 ⟨subd17_3_468, List.forall_mem_cons.2 ⟨subd17_3_469, List.forall_mem_cons.2 ⟨subd17_3_470, List.forall_mem_cons.2 ⟨subd17_3_471, List.forall_mem_cons.2 ⟨subd17_3_472, List.forall_mem_cons.2 ⟨subd17_3_473, List.forall_mem_cons.2 ⟨subd17_3_474, List.forall_mem_cons.2 ⟨subd17_3_475, List.forall_mem_cons.2 ⟨subd17_3_476, List.forall_mem_cons.2 ⟨subd17_3_477, List.forall_mem_cons.2 ⟨subd17_3_478, List.forall_mem_cons.2 ⟨subd17_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_480 : subd17_3 [-1, 1, 6] = true := by decide +kernel
theorem subd17_3_481 : subd17_3 [-1, 1, 7] = true := by decide +kernel
theorem subd17_3_482 : subd17_3 [-1, 1, 8] = true := by decide +kernel
theorem subd17_3_483 : subd17_3 [-1, 2, -8] = true := by decide +kernel
theorem subd17_3_484 : subd17_3 [-1, 2, -7] = true := by decide +kernel
theorem subd17_3_485 : subd17_3 [-1, 2, -6] = true := by decide +kernel
theorem subd17_3_486 : subd17_3 [-1, 2, -5] = true := by decide +kernel
theorem subd17_3_487 : subd17_3 [-1, 2, -4] = true := by decide +kernel
theorem subd17_3_488 : subd17_3 [-1, 2, -3] = true := by decide +kernel
theorem subd17_3_489 : subd17_3 [-1, 2, -2] = true := by decide +kernel
theorem subd17_3_490 : subd17_3 [-1, 2, -1] = true := by decide +kernel
theorem subd17_3_491 : subd17_3 [-1, 2, 0] = true := by decide +kernel
theorem subd17_3_492 : subd17_3 [-1, 2, 1] = true := by decide +kernel
theorem subd17_3_493 : subd17_3 [-1, 2, 2] = true := by decide +kernel
theorem subd17_3_494 : subd17_3 [-1, 2, 3] = true := by decide +kernel
theorem subd17_3_495 : subd17_3 [-1, 2, 4] = true := by decide +kernel
theorem subd17_3_496 : subd17_3 [-1, 2, 5] = true := by decide +kernel
theorem subd17_3_497 : subd17_3 [-1, 2, 6] = true := by decide +kernel
theorem subd17_3_498 : subd17_3 [-1, 2, 7] = true := by decide +kernel
theorem subd17_3_499 : subd17_3 [-1, 2, 8] = true := by decide +kernel
theorem subd17_3_500 : subd17_3 [-1, 3, -7] = true := by decide +kernel
theorem subd17_3_501 : subd17_3 [-1, 3, -6] = true := by decide +kernel
theorem subd17_3_502 : subd17_3 [-1, 3, -5] = true := by decide +kernel
theorem subd17_3_503 : subd17_3 [-1, 3, -4] = true := by decide +kernel
theorem subd17_3_504 : subd17_3 [-1, 3, -3] = true := by decide +kernel
theorem subd17_3_505 : subd17_3 [-1, 3, -2] = true := by decide +kernel
theorem subd17_3_506 : subd17_3 [-1, 3, -1] = true := by decide +kernel
theorem subd17_3_507 : subd17_3 [-1, 3, 0] = true := by decide +kernel
theorem subd17_3_508 : subd17_3 [-1, 3, 1] = true := by decide +kernel
theorem subd17_3_509 : subd17_3 [-1, 3, 2] = true := by decide +kernel
theorem subd17_3_510 : subd17_3 [-1, 3, 3] = true := by decide +kernel
theorem subd17_3_511 : subd17_3 [-1, 3, 4] = true := by decide +kernel
theorem sbd17_3_15 : ∀ q ∈ blkd17_3_15, subd17_3 q = true := by
  unfold blkd17_3_15
  exact List.forall_mem_cons.2 ⟨subd17_3_480, List.forall_mem_cons.2 ⟨subd17_3_481, List.forall_mem_cons.2 ⟨subd17_3_482, List.forall_mem_cons.2 ⟨subd17_3_483, List.forall_mem_cons.2 ⟨subd17_3_484, List.forall_mem_cons.2 ⟨subd17_3_485, List.forall_mem_cons.2 ⟨subd17_3_486, List.forall_mem_cons.2 ⟨subd17_3_487, List.forall_mem_cons.2 ⟨subd17_3_488, List.forall_mem_cons.2 ⟨subd17_3_489, List.forall_mem_cons.2 ⟨subd17_3_490, List.forall_mem_cons.2 ⟨subd17_3_491, List.forall_mem_cons.2 ⟨subd17_3_492, List.forall_mem_cons.2 ⟨subd17_3_493, List.forall_mem_cons.2 ⟨subd17_3_494, List.forall_mem_cons.2 ⟨subd17_3_495, List.forall_mem_cons.2 ⟨subd17_3_496, List.forall_mem_cons.2 ⟨subd17_3_497, List.forall_mem_cons.2 ⟨subd17_3_498, List.forall_mem_cons.2 ⟨subd17_3_499, List.forall_mem_cons.2 ⟨subd17_3_500, List.forall_mem_cons.2 ⟨subd17_3_501, List.forall_mem_cons.2 ⟨subd17_3_502, List.forall_mem_cons.2 ⟨subd17_3_503, List.forall_mem_cons.2 ⟨subd17_3_504, List.forall_mem_cons.2 ⟨subd17_3_505, List.forall_mem_cons.2 ⟨subd17_3_506, List.forall_mem_cons.2 ⟨subd17_3_507, List.forall_mem_cons.2 ⟨subd17_3_508, List.forall_mem_cons.2 ⟨subd17_3_509, List.forall_mem_cons.2 ⟨subd17_3_510, List.forall_mem_cons.2 ⟨subd17_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_512 : subd17_3 [-1, 3, 5] = true := by decide +kernel
theorem subd17_3_513 : subd17_3 [-1, 3, 6] = true := by decide +kernel
theorem subd17_3_514 : subd17_3 [-1, 3, 7] = true := by decide +kernel
theorem subd17_3_515 : subd17_3 [-1, 3, 8] = true := by decide +kernel
theorem subd17_3_516 : subd17_3 [-1, 4, -6] = true := by decide +kernel
theorem subd17_3_517 : subd17_3 [-1, 4, -5] = true := by decide +kernel
theorem subd17_3_518 : subd17_3 [-1, 4, -4] = true := by decide +kernel
theorem subd17_3_519 : subd17_3 [-1, 4, -3] = true := by decide +kernel
theorem subd17_3_520 : subd17_3 [-1, 4, -2] = true := by decide +kernel
theorem subd17_3_521 : subd17_3 [-1, 4, -1] = true := by decide +kernel
theorem subd17_3_522 : subd17_3 [-1, 4, 0] = true := by decide +kernel
theorem subd17_3_523 : subd17_3 [-1, 4, 1] = true := by decide +kernel
theorem subd17_3_524 : subd17_3 [-1, 4, 2] = true := by decide +kernel
theorem subd17_3_525 : subd17_3 [-1, 4, 3] = true := by decide +kernel
theorem subd17_3_526 : subd17_3 [-1, 4, 4] = true := by decide +kernel
theorem subd17_3_527 : subd17_3 [-1, 4, 5] = true := by decide +kernel
theorem subd17_3_528 : subd17_3 [-1, 4, 6] = true := by decide +kernel
theorem subd17_3_529 : subd17_3 [-1, 4, 7] = true := by decide +kernel
theorem subd17_3_530 : subd17_3 [-1, 5] = true := by decide +kernel
theorem subd17_3_531 : subd17_3 [-1, 6] = true := by decide +kernel
theorem subd17_3_532 : subd17_3 [0, -8] = true := by decide +kernel
theorem subd17_3_533 : subd17_3 [0, -7] = true := by decide +kernel
theorem subd17_3_534 : subd17_3 [0, -6] = true := by decide +kernel
theorem subd17_3_535 : subd17_3 [0, -5] = true := by decide +kernel
theorem subd17_3_536 : subd17_3 [0, -4, -8] = true := by decide +kernel
theorem subd17_3_537 : subd17_3 [0, -4, -7] = true := by decide +kernel
theorem subd17_3_538 : subd17_3 [0, -4, -6] = true := by decide +kernel
theorem subd17_3_539 : subd17_3 [0, -4, -5] = true := by decide +kernel
theorem subd17_3_540 : subd17_3 [0, -4, -4] = true := by decide +kernel
theorem subd17_3_541 : subd17_3 [0, -4, -3] = true := by decide +kernel
theorem subd17_3_542 : subd17_3 [0, -4, -2] = true := by decide +kernel
theorem subd17_3_543 : subd17_3 [0, -4, -1] = true := by decide +kernel
theorem sbd17_3_16 : ∀ q ∈ blkd17_3_16, subd17_3 q = true := by
  unfold blkd17_3_16
  exact List.forall_mem_cons.2 ⟨subd17_3_512, List.forall_mem_cons.2 ⟨subd17_3_513, List.forall_mem_cons.2 ⟨subd17_3_514, List.forall_mem_cons.2 ⟨subd17_3_515, List.forall_mem_cons.2 ⟨subd17_3_516, List.forall_mem_cons.2 ⟨subd17_3_517, List.forall_mem_cons.2 ⟨subd17_3_518, List.forall_mem_cons.2 ⟨subd17_3_519, List.forall_mem_cons.2 ⟨subd17_3_520, List.forall_mem_cons.2 ⟨subd17_3_521, List.forall_mem_cons.2 ⟨subd17_3_522, List.forall_mem_cons.2 ⟨subd17_3_523, List.forall_mem_cons.2 ⟨subd17_3_524, List.forall_mem_cons.2 ⟨subd17_3_525, List.forall_mem_cons.2 ⟨subd17_3_526, List.forall_mem_cons.2 ⟨subd17_3_527, List.forall_mem_cons.2 ⟨subd17_3_528, List.forall_mem_cons.2 ⟨subd17_3_529, List.forall_mem_cons.2 ⟨subd17_3_530, List.forall_mem_cons.2 ⟨subd17_3_531, List.forall_mem_cons.2 ⟨subd17_3_532, List.forall_mem_cons.2 ⟨subd17_3_533, List.forall_mem_cons.2 ⟨subd17_3_534, List.forall_mem_cons.2 ⟨subd17_3_535, List.forall_mem_cons.2 ⟨subd17_3_536, List.forall_mem_cons.2 ⟨subd17_3_537, List.forall_mem_cons.2 ⟨subd17_3_538, List.forall_mem_cons.2 ⟨subd17_3_539, List.forall_mem_cons.2 ⟨subd17_3_540, List.forall_mem_cons.2 ⟨subd17_3_541, List.forall_mem_cons.2 ⟨subd17_3_542, List.forall_mem_cons.2 ⟨subd17_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_544 : subd17_3 [0, -4, 0] = true := by decide +kernel
theorem subd17_3_545 : subd17_3 [0, -4, 1] = true := by decide +kernel
theorem subd17_3_546 : subd17_3 [0, -4, 2] = true := by decide +kernel
theorem subd17_3_547 : subd17_3 [0, -4, 3] = true := by decide +kernel
theorem subd17_3_548 : subd17_3 [0, -4, 4] = true := by decide +kernel
theorem subd17_3_549 : subd17_3 [0, -4, 5] = true := by decide +kernel
theorem subd17_3_550 : subd17_3 [0, -4, 6] = true := by decide +kernel
theorem subd17_3_551 : subd17_3 [0, -3, -8] = true := by decide +kernel
theorem subd17_3_552 : subd17_3 [0, -3, -7] = true := by decide +kernel
theorem subd17_3_553 : subd17_3 [0, -3, -6] = true := by decide +kernel
theorem subd17_3_554 : subd17_3 [0, -3, -5] = true := by decide +kernel
theorem subd17_3_555 : subd17_3 [0, -3, -4] = true := by decide +kernel
theorem subd17_3_556 : subd17_3 [0, -3, -3] = true := by decide +kernel
theorem subd17_3_557 : subd17_3 [0, -3, -2] = true := by decide +kernel
theorem subd17_3_558 : subd17_3 [0, -3, -1] = true := by decide +kernel
theorem subd17_3_559 : subd17_3 [0, -3, 0] = true := by decide +kernel
theorem subd17_3_560 : subd17_3 [0, -3, 1] = true := by decide +kernel
theorem subd17_3_561 : subd17_3 [0, -3, 2] = true := by decide +kernel
theorem subd17_3_562 : subd17_3 [0, -3, 3] = true := by decide +kernel
theorem subd17_3_563 : subd17_3 [0, -3, 4] = true := by decide +kernel
theorem subd17_3_564 : subd17_3 [0, -3, 5] = true := by decide +kernel
theorem subd17_3_565 : subd17_3 [0, -3, 6] = true := by decide +kernel
theorem subd17_3_566 : subd17_3 [0, -3, 7] = true := by decide +kernel
theorem subd17_3_567 : subd17_3 [0, -2, -9] = true := by decide +kernel
theorem subd17_3_568 : subd17_3 [0, -2, -8] = true := by decide +kernel
theorem subd17_3_569 : subd17_3 [0, -2, -7] = true := by decide +kernel
theorem subd17_3_570 : subd17_3 [0, -2, -6] = true := by decide +kernel
theorem subd17_3_571 : subd17_3 [0, -2, -5] = true := by decide +kernel
theorem subd17_3_572 : subd17_3 [0, -2, -4] = true := by decide +kernel
theorem subd17_3_573 : subd17_3 [0, -2, -3] = true := by decide +kernel
theorem subd17_3_574 : subd17_3 [0, -2, -2] = true := by decide +kernel
theorem subd17_3_575 : subd17_3 [0, -2, -1] = true := by decide +kernel
theorem sbd17_3_17 : ∀ q ∈ blkd17_3_17, subd17_3 q = true := by
  unfold blkd17_3_17
  exact List.forall_mem_cons.2 ⟨subd17_3_544, List.forall_mem_cons.2 ⟨subd17_3_545, List.forall_mem_cons.2 ⟨subd17_3_546, List.forall_mem_cons.2 ⟨subd17_3_547, List.forall_mem_cons.2 ⟨subd17_3_548, List.forall_mem_cons.2 ⟨subd17_3_549, List.forall_mem_cons.2 ⟨subd17_3_550, List.forall_mem_cons.2 ⟨subd17_3_551, List.forall_mem_cons.2 ⟨subd17_3_552, List.forall_mem_cons.2 ⟨subd17_3_553, List.forall_mem_cons.2 ⟨subd17_3_554, List.forall_mem_cons.2 ⟨subd17_3_555, List.forall_mem_cons.2 ⟨subd17_3_556, List.forall_mem_cons.2 ⟨subd17_3_557, List.forall_mem_cons.2 ⟨subd17_3_558, List.forall_mem_cons.2 ⟨subd17_3_559, List.forall_mem_cons.2 ⟨subd17_3_560, List.forall_mem_cons.2 ⟨subd17_3_561, List.forall_mem_cons.2 ⟨subd17_3_562, List.forall_mem_cons.2 ⟨subd17_3_563, List.forall_mem_cons.2 ⟨subd17_3_564, List.forall_mem_cons.2 ⟨subd17_3_565, List.forall_mem_cons.2 ⟨subd17_3_566, List.forall_mem_cons.2 ⟨subd17_3_567, List.forall_mem_cons.2 ⟨subd17_3_568, List.forall_mem_cons.2 ⟨subd17_3_569, List.forall_mem_cons.2 ⟨subd17_3_570, List.forall_mem_cons.2 ⟨subd17_3_571, List.forall_mem_cons.2 ⟨subd17_3_572, List.forall_mem_cons.2 ⟨subd17_3_573, List.forall_mem_cons.2 ⟨subd17_3_574, List.forall_mem_cons.2 ⟨subd17_3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_576 : subd17_3 [0, -2, 0] = true := by decide +kernel
theorem subd17_3_577 : subd17_3 [0, -2, 1] = true := by decide +kernel
theorem subd17_3_578 : subd17_3 [0, -2, 2] = true := by decide +kernel
theorem subd17_3_579 : subd17_3 [0, -2, 3] = true := by decide +kernel
theorem subd17_3_580 : subd17_3 [0, -2, 4] = true := by decide +kernel
theorem subd17_3_581 : subd17_3 [0, -2, 5] = true := by decide +kernel
theorem subd17_3_582 : subd17_3 [0, -2, 6] = true := by decide +kernel
theorem subd17_3_583 : subd17_3 [0, -2, 7] = true := by decide +kernel
theorem subd17_3_584 : subd17_3 [0, -1, -9] = true := by decide +kernel
theorem subd17_3_585 : subd17_3 [0, -1, -8] = true := by decide +kernel
theorem subd17_3_586 : subd17_3 [0, -1, -7] = true := by decide +kernel
theorem subd17_3_587 : subd17_3 [0, -1, -6] = true := by decide +kernel
theorem subd17_3_588 : subd17_3 [0, -1, -5] = true := by decide +kernel
theorem subd17_3_589 : subd17_3 [0, -1, -4] = true := by decide +kernel
theorem subd17_3_590 : subd17_3 [0, -1, -3] = true := by decide +kernel
theorem subd17_3_591 : subd17_3 [0, -1, -2] = true := by decide +kernel
theorem subd17_3_592 : subd17_3 [0, -1, -1] = true := by decide +kernel
theorem subd17_3_593 : subd17_3 [0, -1, 0] = true := by decide +kernel
theorem subd17_3_594 : subd17_3 [0, -1, 1] = true := by decide +kernel
theorem subd17_3_595 : subd17_3 [0, -1, 2] = true := by decide +kernel
theorem subd17_3_596 : subd17_3 [0, -1, 3] = true := by decide +kernel
theorem subd17_3_597 : subd17_3 [0, -1, 4] = true := by decide +kernel
theorem subd17_3_598 : subd17_3 [0, -1, 5] = true := by decide +kernel
theorem subd17_3_599 : subd17_3 [0, -1, 6] = true := by decide +kernel
theorem subd17_3_600 : subd17_3 [0, -1, 7] = true := by decide +kernel
theorem subd17_3_601 : subd17_3 [0, -1, 8] = true := by decide +kernel
theorem subd17_3_602 : subd17_3 [0, 0, -9] = true := by decide +kernel
theorem subd17_3_603 : subd17_3 [0, 0, -8] = true := by decide +kernel
theorem subd17_3_604 : subd17_3 [0, 0, -7] = true := by decide +kernel
theorem subd17_3_605 : subd17_3 [0, 0, -6] = true := by decide +kernel
theorem subd17_3_606 : subd17_3 [0, 0, -5] = true := by decide +kernel
theorem subd17_3_607 : subd17_3 [0, 0, -4] = true := by decide +kernel
theorem sbd17_3_18 : ∀ q ∈ blkd17_3_18, subd17_3 q = true := by
  unfold blkd17_3_18
  exact List.forall_mem_cons.2 ⟨subd17_3_576, List.forall_mem_cons.2 ⟨subd17_3_577, List.forall_mem_cons.2 ⟨subd17_3_578, List.forall_mem_cons.2 ⟨subd17_3_579, List.forall_mem_cons.2 ⟨subd17_3_580, List.forall_mem_cons.2 ⟨subd17_3_581, List.forall_mem_cons.2 ⟨subd17_3_582, List.forall_mem_cons.2 ⟨subd17_3_583, List.forall_mem_cons.2 ⟨subd17_3_584, List.forall_mem_cons.2 ⟨subd17_3_585, List.forall_mem_cons.2 ⟨subd17_3_586, List.forall_mem_cons.2 ⟨subd17_3_587, List.forall_mem_cons.2 ⟨subd17_3_588, List.forall_mem_cons.2 ⟨subd17_3_589, List.forall_mem_cons.2 ⟨subd17_3_590, List.forall_mem_cons.2 ⟨subd17_3_591, List.forall_mem_cons.2 ⟨subd17_3_592, List.forall_mem_cons.2 ⟨subd17_3_593, List.forall_mem_cons.2 ⟨subd17_3_594, List.forall_mem_cons.2 ⟨subd17_3_595, List.forall_mem_cons.2 ⟨subd17_3_596, List.forall_mem_cons.2 ⟨subd17_3_597, List.forall_mem_cons.2 ⟨subd17_3_598, List.forall_mem_cons.2 ⟨subd17_3_599, List.forall_mem_cons.2 ⟨subd17_3_600, List.forall_mem_cons.2 ⟨subd17_3_601, List.forall_mem_cons.2 ⟨subd17_3_602, List.forall_mem_cons.2 ⟨subd17_3_603, List.forall_mem_cons.2 ⟨subd17_3_604, List.forall_mem_cons.2 ⟨subd17_3_605, List.forall_mem_cons.2 ⟨subd17_3_606, List.forall_mem_cons.2 ⟨subd17_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_608 : subd17_3 [0, 0, -3] = true := by decide +kernel
theorem subd17_3_609 : subd17_3 [0, 0, -2] = true := by decide +kernel
theorem subd17_3_610 : subd17_3 [0, 0, -1] = true := by decide +kernel
theorem subd17_3_611 : subd17_3 [0, 0, 0] = true := by decide +kernel
theorem subd17_3_612 : subd17_3 [0, 0, 1] = true := by decide +kernel
theorem subd17_3_613 : subd17_3 [0, 0, 2] = true := by decide +kernel
theorem subd17_3_614 : subd17_3 [0, 0, 3] = true := by decide +kernel
theorem subd17_3_615 : subd17_3 [0, 0, 4] = true := by decide +kernel
theorem subd17_3_616 : subd17_3 [0, 0, 5] = true := by decide +kernel
theorem subd17_3_617 : subd17_3 [0, 0, 6] = true := by decide +kernel
theorem subd17_3_618 : subd17_3 [0, 0, 7] = true := by decide +kernel
theorem subd17_3_619 : subd17_3 [0, 0, 8] = true := by decide +kernel
theorem subd17_3_620 : subd17_3 [0, 1, -9] = true := by decide +kernel
theorem subd17_3_621 : subd17_3 [0, 1, -8] = true := by decide +kernel
theorem subd17_3_622 : subd17_3 [0, 1, -7] = true := by decide +kernel
theorem subd17_3_623 : subd17_3 [0, 1, -6] = true := by decide +kernel
theorem subd17_3_624 : subd17_3 [0, 1, -5] = true := by decide +kernel
theorem subd17_3_625 : subd17_3 [0, 1, -4] = true := by decide +kernel
theorem subd17_3_626 : subd17_3 [0, 1, -3] = true := by decide +kernel
theorem subd17_3_627 : subd17_3 [0, 1, -2] = true := by decide +kernel
theorem subd17_3_628 : subd17_3 [0, 1, -1] = true := by decide +kernel
theorem subd17_3_629 : subd17_3 [0, 1, 0] = true := by decide +kernel
theorem subd17_3_630 : subd17_3 [0, 1, 1] = true := by decide +kernel
theorem subd17_3_631 : subd17_3 [0, 1, 2] = true := by decide +kernel
theorem subd17_3_632 : subd17_3 [0, 1, 3] = true := by decide +kernel
theorem subd17_3_633 : subd17_3 [0, 1, 4] = true := by decide +kernel
theorem subd17_3_634 : subd17_3 [0, 1, 5] = true := by decide +kernel
theorem subd17_3_635 : subd17_3 [0, 1, 6] = true := by decide +kernel
theorem subd17_3_636 : subd17_3 [0, 1, 7] = true := by decide +kernel
theorem subd17_3_637 : subd17_3 [0, 1, 8] = true := by decide +kernel
theorem subd17_3_638 : subd17_3 [0, 2, -8] = true := by decide +kernel
theorem subd17_3_639 : subd17_3 [0, 2, -7] = true := by decide +kernel
theorem sbd17_3_19 : ∀ q ∈ blkd17_3_19, subd17_3 q = true := by
  unfold blkd17_3_19
  exact List.forall_mem_cons.2 ⟨subd17_3_608, List.forall_mem_cons.2 ⟨subd17_3_609, List.forall_mem_cons.2 ⟨subd17_3_610, List.forall_mem_cons.2 ⟨subd17_3_611, List.forall_mem_cons.2 ⟨subd17_3_612, List.forall_mem_cons.2 ⟨subd17_3_613, List.forall_mem_cons.2 ⟨subd17_3_614, List.forall_mem_cons.2 ⟨subd17_3_615, List.forall_mem_cons.2 ⟨subd17_3_616, List.forall_mem_cons.2 ⟨subd17_3_617, List.forall_mem_cons.2 ⟨subd17_3_618, List.forall_mem_cons.2 ⟨subd17_3_619, List.forall_mem_cons.2 ⟨subd17_3_620, List.forall_mem_cons.2 ⟨subd17_3_621, List.forall_mem_cons.2 ⟨subd17_3_622, List.forall_mem_cons.2 ⟨subd17_3_623, List.forall_mem_cons.2 ⟨subd17_3_624, List.forall_mem_cons.2 ⟨subd17_3_625, List.forall_mem_cons.2 ⟨subd17_3_626, List.forall_mem_cons.2 ⟨subd17_3_627, List.forall_mem_cons.2 ⟨subd17_3_628, List.forall_mem_cons.2 ⟨subd17_3_629, List.forall_mem_cons.2 ⟨subd17_3_630, List.forall_mem_cons.2 ⟨subd17_3_631, List.forall_mem_cons.2 ⟨subd17_3_632, List.forall_mem_cons.2 ⟨subd17_3_633, List.forall_mem_cons.2 ⟨subd17_3_634, List.forall_mem_cons.2 ⟨subd17_3_635, List.forall_mem_cons.2 ⟨subd17_3_636, List.forall_mem_cons.2 ⟨subd17_3_637, List.forall_mem_cons.2 ⟨subd17_3_638, List.forall_mem_cons.2 ⟨subd17_3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_640 : subd17_3 [0, 2, -6] = true := by decide +kernel
theorem subd17_3_641 : subd17_3 [0, 2, -5] = true := by decide +kernel
theorem subd17_3_642 : subd17_3 [0, 2, -4] = true := by decide +kernel
theorem subd17_3_643 : subd17_3 [0, 2, -3] = true := by decide +kernel
theorem subd17_3_644 : subd17_3 [0, 2, -2] = true := by decide +kernel
theorem subd17_3_645 : subd17_3 [0, 2, -1] = true := by decide +kernel
theorem subd17_3_646 : subd17_3 [0, 2, 0] = true := by decide +kernel
theorem subd17_3_647 : subd17_3 [0, 2, 1] = true := by decide +kernel
theorem subd17_3_648 : subd17_3 [0, 2, 2] = true := by decide +kernel
theorem subd17_3_649 : subd17_3 [0, 2, 3] = true := by decide +kernel
theorem subd17_3_650 : subd17_3 [0, 2, 4] = true := by decide +kernel
theorem subd17_3_651 : subd17_3 [0, 2, 5] = true := by decide +kernel
theorem subd17_3_652 : subd17_3 [0, 2, 6] = true := by decide +kernel
theorem subd17_3_653 : subd17_3 [0, 2, 7] = true := by decide +kernel
theorem subd17_3_654 : subd17_3 [0, 2, 8] = true := by decide +kernel
theorem subd17_3_655 : subd17_3 [0, 3, -8] = true := by decide +kernel
theorem subd17_3_656 : subd17_3 [0, 3, -7] = true := by decide +kernel
theorem subd17_3_657 : subd17_3 [0, 3, -6] = true := by decide +kernel
theorem subd17_3_658 : subd17_3 [0, 3, -5] = true := by decide +kernel
theorem subd17_3_659 : subd17_3 [0, 3, -4] = true := by decide +kernel
theorem subd17_3_660 : subd17_3 [0, 3, -3] = true := by decide +kernel
theorem subd17_3_661 : subd17_3 [0, 3, -2] = true := by decide +kernel
theorem subd17_3_662 : subd17_3 [0, 3, -1] = true := by decide +kernel
theorem subd17_3_663 : subd17_3 [0, 3, 0] = true := by decide +kernel
theorem subd17_3_664 : subd17_3 [0, 3, 1] = true := by decide +kernel
theorem subd17_3_665 : subd17_3 [0, 3, 2] = true := by decide +kernel
theorem subd17_3_666 : subd17_3 [0, 3, 3] = true := by decide +kernel
theorem subd17_3_667 : subd17_3 [0, 3, 4] = true := by decide +kernel
theorem subd17_3_668 : subd17_3 [0, 3, 5] = true := by decide +kernel
theorem subd17_3_669 : subd17_3 [0, 3, 6] = true := by decide +kernel
theorem subd17_3_670 : subd17_3 [0, 3, 7] = true := by decide +kernel
theorem subd17_3_671 : subd17_3 [0, 4, -7] = true := by decide +kernel
theorem sbd17_3_20 : ∀ q ∈ blkd17_3_20, subd17_3 q = true := by
  unfold blkd17_3_20
  exact List.forall_mem_cons.2 ⟨subd17_3_640, List.forall_mem_cons.2 ⟨subd17_3_641, List.forall_mem_cons.2 ⟨subd17_3_642, List.forall_mem_cons.2 ⟨subd17_3_643, List.forall_mem_cons.2 ⟨subd17_3_644, List.forall_mem_cons.2 ⟨subd17_3_645, List.forall_mem_cons.2 ⟨subd17_3_646, List.forall_mem_cons.2 ⟨subd17_3_647, List.forall_mem_cons.2 ⟨subd17_3_648, List.forall_mem_cons.2 ⟨subd17_3_649, List.forall_mem_cons.2 ⟨subd17_3_650, List.forall_mem_cons.2 ⟨subd17_3_651, List.forall_mem_cons.2 ⟨subd17_3_652, List.forall_mem_cons.2 ⟨subd17_3_653, List.forall_mem_cons.2 ⟨subd17_3_654, List.forall_mem_cons.2 ⟨subd17_3_655, List.forall_mem_cons.2 ⟨subd17_3_656, List.forall_mem_cons.2 ⟨subd17_3_657, List.forall_mem_cons.2 ⟨subd17_3_658, List.forall_mem_cons.2 ⟨subd17_3_659, List.forall_mem_cons.2 ⟨subd17_3_660, List.forall_mem_cons.2 ⟨subd17_3_661, List.forall_mem_cons.2 ⟨subd17_3_662, List.forall_mem_cons.2 ⟨subd17_3_663, List.forall_mem_cons.2 ⟨subd17_3_664, List.forall_mem_cons.2 ⟨subd17_3_665, List.forall_mem_cons.2 ⟨subd17_3_666, List.forall_mem_cons.2 ⟨subd17_3_667, List.forall_mem_cons.2 ⟨subd17_3_668, List.forall_mem_cons.2 ⟨subd17_3_669, List.forall_mem_cons.2 ⟨subd17_3_670, List.forall_mem_cons.2 ⟨subd17_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_672 : subd17_3 [0, 4, -6] = true := by decide +kernel
theorem subd17_3_673 : subd17_3 [0, 4, -5] = true := by decide +kernel
theorem subd17_3_674 : subd17_3 [0, 4, -4] = true := by decide +kernel
theorem subd17_3_675 : subd17_3 [0, 4, -3] = true := by decide +kernel
theorem subd17_3_676 : subd17_3 [0, 4, -2] = true := by decide +kernel
theorem subd17_3_677 : subd17_3 [0, 4, -1] = true := by decide +kernel
theorem subd17_3_678 : subd17_3 [0, 4, 0] = true := by decide +kernel
theorem subd17_3_679 : subd17_3 [0, 4, 1] = true := by decide +kernel
theorem subd17_3_680 : subd17_3 [0, 4, 2] = true := by decide +kernel
theorem subd17_3_681 : subd17_3 [0, 4, 3] = true := by decide +kernel
theorem subd17_3_682 : subd17_3 [0, 4, 4] = true := by decide +kernel
theorem subd17_3_683 : subd17_3 [0, 4, 5] = true := by decide +kernel
theorem subd17_3_684 : subd17_3 [0, 4, 6] = true := by decide +kernel
theorem subd17_3_685 : subd17_3 [0, 4, 7] = true := by decide +kernel
theorem subd17_3_686 : subd17_3 [0, 5] = true := by decide +kernel
theorem subd17_3_687 : subd17_3 [0, 6] = true := by decide +kernel
theorem subd17_3_688 : subd17_3 [0, 7] = true := by decide +kernel
theorem subd17_3_689 : subd17_3 [1, -7] = true := by decide +kernel
theorem subd17_3_690 : subd17_3 [1, -6] = true := by decide +kernel
theorem subd17_3_691 : subd17_3 [1, -5] = true := by decide +kernel
theorem subd17_3_692 : subd17_3 [1, -4, -8] = true := by decide +kernel
theorem subd17_3_693 : subd17_3 [1, -4, -7] = true := by decide +kernel
theorem subd17_3_694 : subd17_3 [1, -4, -6] = true := by decide +kernel
theorem subd17_3_695 : subd17_3 [1, -4, -5] = true := by decide +kernel
theorem subd17_3_696 : subd17_3 [1, -4, -4] = true := by decide +kernel
theorem subd17_3_697 : subd17_3 [1, -4, -3] = true := by decide +kernel
theorem subd17_3_698 : subd17_3 [1, -4, -2] = true := by decide +kernel
theorem subd17_3_699 : subd17_3 [1, -4, -1] = true := by decide +kernel
theorem subd17_3_700 : subd17_3 [1, -4, 0] = true := by decide +kernel
theorem subd17_3_701 : subd17_3 [1, -4, 1] = true := by decide +kernel
theorem subd17_3_702 : subd17_3 [1, -4, 2] = true := by decide +kernel
theorem subd17_3_703 : subd17_3 [1, -4, 3] = true := by decide +kernel
theorem sbd17_3_21 : ∀ q ∈ blkd17_3_21, subd17_3 q = true := by
  unfold blkd17_3_21
  exact List.forall_mem_cons.2 ⟨subd17_3_672, List.forall_mem_cons.2 ⟨subd17_3_673, List.forall_mem_cons.2 ⟨subd17_3_674, List.forall_mem_cons.2 ⟨subd17_3_675, List.forall_mem_cons.2 ⟨subd17_3_676, List.forall_mem_cons.2 ⟨subd17_3_677, List.forall_mem_cons.2 ⟨subd17_3_678, List.forall_mem_cons.2 ⟨subd17_3_679, List.forall_mem_cons.2 ⟨subd17_3_680, List.forall_mem_cons.2 ⟨subd17_3_681, List.forall_mem_cons.2 ⟨subd17_3_682, List.forall_mem_cons.2 ⟨subd17_3_683, List.forall_mem_cons.2 ⟨subd17_3_684, List.forall_mem_cons.2 ⟨subd17_3_685, List.forall_mem_cons.2 ⟨subd17_3_686, List.forall_mem_cons.2 ⟨subd17_3_687, List.forall_mem_cons.2 ⟨subd17_3_688, List.forall_mem_cons.2 ⟨subd17_3_689, List.forall_mem_cons.2 ⟨subd17_3_690, List.forall_mem_cons.2 ⟨subd17_3_691, List.forall_mem_cons.2 ⟨subd17_3_692, List.forall_mem_cons.2 ⟨subd17_3_693, List.forall_mem_cons.2 ⟨subd17_3_694, List.forall_mem_cons.2 ⟨subd17_3_695, List.forall_mem_cons.2 ⟨subd17_3_696, List.forall_mem_cons.2 ⟨subd17_3_697, List.forall_mem_cons.2 ⟨subd17_3_698, List.forall_mem_cons.2 ⟨subd17_3_699, List.forall_mem_cons.2 ⟨subd17_3_700, List.forall_mem_cons.2 ⟨subd17_3_701, List.forall_mem_cons.2 ⟨subd17_3_702, List.forall_mem_cons.2 ⟨subd17_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_704 : subd17_3 [1, -4, 4] = true := by decide +kernel
theorem subd17_3_705 : subd17_3 [1, -4, 5] = true := by decide +kernel
theorem subd17_3_706 : subd17_3 [1, -3, -9] = true := by decide +kernel
theorem subd17_3_707 : subd17_3 [1, -3, -8] = true := by decide +kernel
theorem subd17_3_708 : subd17_3 [1, -3, -7] = true := by decide +kernel
theorem subd17_3_709 : subd17_3 [1, -3, -6] = true := by decide +kernel
theorem subd17_3_710 : subd17_3 [1, -3, -5] = true := by decide +kernel
theorem subd17_3_711 : subd17_3 [1, -3, -4] = true := by decide +kernel
theorem subd17_3_712 : subd17_3 [1, -3, -3] = true := by decide +kernel
theorem subd17_3_713 : subd17_3 [1, -3, -2] = true := by decide +kernel
theorem subd17_3_714 : subd17_3 [1, -3, -1] = true := by decide +kernel
theorem subd17_3_715 : subd17_3 [1, -3, 0] = true := by decide +kernel
theorem subd17_3_716 : subd17_3 [1, -3, 1] = true := by decide +kernel
theorem subd17_3_717 : subd17_3 [1, -3, 2] = true := by decide +kernel
theorem subd17_3_718 : subd17_3 [1, -3, 3] = true := by decide +kernel
theorem subd17_3_719 : subd17_3 [1, -3, 4] = true := by decide +kernel
theorem subd17_3_720 : subd17_3 [1, -3, 5] = true := by decide +kernel
theorem subd17_3_721 : subd17_3 [1, -3, 6] = true := by decide +kernel
theorem subd17_3_722 : subd17_3 [1, -2, -9] = true := by decide +kernel
theorem subd17_3_723 : subd17_3 [1, -2, -8] = true := by decide +kernel
theorem subd17_3_724 : subd17_3 [1, -2, -7] = true := by decide +kernel
theorem subd17_3_725 : subd17_3 [1, -2, -6] = true := by decide +kernel
theorem subd17_3_726 : subd17_3 [1, -2, -5] = true := by decide +kernel
theorem subd17_3_727 : subd17_3 [1, -2, -4] = true := by decide +kernel
theorem subd17_3_728 : subd17_3 [1, -2, -3] = true := by decide +kernel
theorem subd17_3_729 : subd17_3 [1, -2, -2] = true := by decide +kernel
theorem subd17_3_730 : subd17_3 [1, -2, -1] = true := by decide +kernel
theorem subd17_3_731 : subd17_3 [1, -2, 0] = true := by decide +kernel
theorem subd17_3_732 : subd17_3 [1, -2, 1] = true := by decide +kernel
theorem subd17_3_733 : subd17_3 [1, -2, 2] = true := by decide +kernel
theorem subd17_3_734 : subd17_3 [1, -2, 3] = true := by decide +kernel
theorem subd17_3_735 : subd17_3 [1, -2, 4] = true := by decide +kernel
theorem sbd17_3_22 : ∀ q ∈ blkd17_3_22, subd17_3 q = true := by
  unfold blkd17_3_22
  exact List.forall_mem_cons.2 ⟨subd17_3_704, List.forall_mem_cons.2 ⟨subd17_3_705, List.forall_mem_cons.2 ⟨subd17_3_706, List.forall_mem_cons.2 ⟨subd17_3_707, List.forall_mem_cons.2 ⟨subd17_3_708, List.forall_mem_cons.2 ⟨subd17_3_709, List.forall_mem_cons.2 ⟨subd17_3_710, List.forall_mem_cons.2 ⟨subd17_3_711, List.forall_mem_cons.2 ⟨subd17_3_712, List.forall_mem_cons.2 ⟨subd17_3_713, List.forall_mem_cons.2 ⟨subd17_3_714, List.forall_mem_cons.2 ⟨subd17_3_715, List.forall_mem_cons.2 ⟨subd17_3_716, List.forall_mem_cons.2 ⟨subd17_3_717, List.forall_mem_cons.2 ⟨subd17_3_718, List.forall_mem_cons.2 ⟨subd17_3_719, List.forall_mem_cons.2 ⟨subd17_3_720, List.forall_mem_cons.2 ⟨subd17_3_721, List.forall_mem_cons.2 ⟨subd17_3_722, List.forall_mem_cons.2 ⟨subd17_3_723, List.forall_mem_cons.2 ⟨subd17_3_724, List.forall_mem_cons.2 ⟨subd17_3_725, List.forall_mem_cons.2 ⟨subd17_3_726, List.forall_mem_cons.2 ⟨subd17_3_727, List.forall_mem_cons.2 ⟨subd17_3_728, List.forall_mem_cons.2 ⟨subd17_3_729, List.forall_mem_cons.2 ⟨subd17_3_730, List.forall_mem_cons.2 ⟨subd17_3_731, List.forall_mem_cons.2 ⟨subd17_3_732, List.forall_mem_cons.2 ⟨subd17_3_733, List.forall_mem_cons.2 ⟨subd17_3_734, List.forall_mem_cons.2 ⟨subd17_3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_736 : subd17_3 [1, -2, 5] = true := by decide +kernel
theorem subd17_3_737 : subd17_3 [1, -2, 6] = true := by decide +kernel
theorem subd17_3_738 : subd17_3 [1, -2, 7] = true := by decide +kernel
theorem subd17_3_739 : subd17_3 [1, -1, -9] = true := by decide +kernel
theorem subd17_3_740 : subd17_3 [1, -1, -8] = true := by decide +kernel
theorem subd17_3_741 : subd17_3 [1, -1, -7] = true := by decide +kernel
theorem subd17_3_742 : subd17_3 [1, -1, -6] = true := by decide +kernel
theorem subd17_3_743 : subd17_3 [1, -1, -5] = true := by decide +kernel
theorem subd17_3_744 : subd17_3 [1, -1, -4] = true := by decide +kernel
theorem subd17_3_745 : subd17_3 [1, -1, -3] = true := by decide +kernel
theorem subd17_3_746 : subd17_3 [1, -1, -2] = true := by decide +kernel
theorem subd17_3_747 : subd17_3 [1, -1, -1] = true := by decide +kernel
theorem subd17_3_748 : subd17_3 [1, -1, 0] = true := by decide +kernel
theorem subd17_3_749 : subd17_3 [1, -1, 1] = true := by decide +kernel
theorem subd17_3_750 : subd17_3 [1, -1, 2] = true := by decide +kernel
theorem subd17_3_751 : subd17_3 [1, -1, 3] = true := by decide +kernel
theorem subd17_3_752 : subd17_3 [1, -1, 4] = true := by decide +kernel
theorem subd17_3_753 : subd17_3 [1, -1, 5] = true := by decide +kernel
theorem subd17_3_754 : subd17_3 [1, -1, 6] = true := by decide +kernel
theorem subd17_3_755 : subd17_3 [1, -1, 7] = true := by decide +kernel
theorem subd17_3_756 : subd17_3 [1, 0, -9] = true := by decide +kernel
theorem subd17_3_757 : subd17_3 [1, 0, -8] = true := by decide +kernel
theorem subd17_3_758 : subd17_3 [1, 0, -7] = true := by decide +kernel
theorem subd17_3_759 : subd17_3 [1, 0, -6] = true := by decide +kernel
theorem subd17_3_760 : subd17_3 [1, 0, -5] = true := by decide +kernel
theorem subd17_3_761 : subd17_3 [1, 0, -4] = true := by decide +kernel
theorem subd17_3_762 : subd17_3 [1, 0, -3] = true := by decide +kernel
theorem subd17_3_763 : subd17_3 [1, 0, -2] = true := by decide +kernel
theorem subd17_3_764 : subd17_3 [1, 0, -1] = true := by decide +kernel
theorem subd17_3_765 : subd17_3 [1, 0, 0] = true := by decide +kernel
theorem subd17_3_766 : subd17_3 [1, 0, 1] = true := by decide +kernel
theorem subd17_3_767 : subd17_3 [1, 0, 2] = true := by decide +kernel
theorem sbd17_3_23 : ∀ q ∈ blkd17_3_23, subd17_3 q = true := by
  unfold blkd17_3_23
  exact List.forall_mem_cons.2 ⟨subd17_3_736, List.forall_mem_cons.2 ⟨subd17_3_737, List.forall_mem_cons.2 ⟨subd17_3_738, List.forall_mem_cons.2 ⟨subd17_3_739, List.forall_mem_cons.2 ⟨subd17_3_740, List.forall_mem_cons.2 ⟨subd17_3_741, List.forall_mem_cons.2 ⟨subd17_3_742, List.forall_mem_cons.2 ⟨subd17_3_743, List.forall_mem_cons.2 ⟨subd17_3_744, List.forall_mem_cons.2 ⟨subd17_3_745, List.forall_mem_cons.2 ⟨subd17_3_746, List.forall_mem_cons.2 ⟨subd17_3_747, List.forall_mem_cons.2 ⟨subd17_3_748, List.forall_mem_cons.2 ⟨subd17_3_749, List.forall_mem_cons.2 ⟨subd17_3_750, List.forall_mem_cons.2 ⟨subd17_3_751, List.forall_mem_cons.2 ⟨subd17_3_752, List.forall_mem_cons.2 ⟨subd17_3_753, List.forall_mem_cons.2 ⟨subd17_3_754, List.forall_mem_cons.2 ⟨subd17_3_755, List.forall_mem_cons.2 ⟨subd17_3_756, List.forall_mem_cons.2 ⟨subd17_3_757, List.forall_mem_cons.2 ⟨subd17_3_758, List.forall_mem_cons.2 ⟨subd17_3_759, List.forall_mem_cons.2 ⟨subd17_3_760, List.forall_mem_cons.2 ⟨subd17_3_761, List.forall_mem_cons.2 ⟨subd17_3_762, List.forall_mem_cons.2 ⟨subd17_3_763, List.forall_mem_cons.2 ⟨subd17_3_764, List.forall_mem_cons.2 ⟨subd17_3_765, List.forall_mem_cons.2 ⟨subd17_3_766, List.forall_mem_cons.2 ⟨subd17_3_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_768 : subd17_3 [1, 0, 3] = true := by decide +kernel
theorem subd17_3_769 : subd17_3 [1, 0, 4] = true := by decide +kernel
theorem subd17_3_770 : subd17_3 [1, 0, 5] = true := by decide +kernel
theorem subd17_3_771 : subd17_3 [1, 0, 6] = true := by decide +kernel
theorem subd17_3_772 : subd17_3 [1, 0, 7] = true := by decide +kernel
theorem subd17_3_773 : subd17_3 [1, 1, -9] = true := by decide +kernel
theorem subd17_3_774 : subd17_3 [1, 1, -8] = true := by decide +kernel
theorem subd17_3_775 : subd17_3 [1, 1, -7] = true := by decide +kernel
theorem subd17_3_776 : subd17_3 [1, 1, -6] = true := by decide +kernel
theorem subd17_3_777 : subd17_3 [1, 1, -5] = true := by decide +kernel
theorem subd17_3_778 : subd17_3 [1, 1, -4] = true := by decide +kernel
theorem subd17_3_779 : subd17_3 [1, 1, -3] = true := by decide +kernel
theorem subd17_3_780 : subd17_3 [1, 1, -2] = true := by decide +kernel
theorem subd17_3_781 : subd17_3 [1, 1, -1] = true := by decide +kernel
theorem subd17_3_782 : subd17_3 [1, 1, 0] = true := by decide +kernel
theorem subd17_3_783 : subd17_3 [1, 1, 1] = true := by decide +kernel
theorem subd17_3_784 : subd17_3 [1, 1, 2] = true := by decide +kernel
theorem subd17_3_785 : subd17_3 [1, 1, 3] = true := by decide +kernel
theorem subd17_3_786 : subd17_3 [1, 1, 4] = true := by decide +kernel
theorem subd17_3_787 : subd17_3 [1, 1, 5] = true := by decide +kernel
theorem subd17_3_788 : subd17_3 [1, 1, 6] = true := by decide +kernel
theorem subd17_3_789 : subd17_3 [1, 1, 7] = true := by decide +kernel
theorem subd17_3_790 : subd17_3 [1, 2, -9] = true := by decide +kernel
theorem subd17_3_791 : subd17_3 [1, 2, -8] = true := by decide +kernel
theorem subd17_3_792 : subd17_3 [1, 2, -7] = true := by decide +kernel
theorem subd17_3_793 : subd17_3 [1, 2, -6] = true := by decide +kernel
theorem subd17_3_794 : subd17_3 [1, 2, -5] = true := by decide +kernel
theorem subd17_3_795 : subd17_3 [1, 2, -4] = true := by decide +kernel
theorem subd17_3_796 : subd17_3 [1, 2, -3] = true := by decide +kernel
theorem subd17_3_797 : subd17_3 [1, 2, -2] = true := by decide +kernel
theorem subd17_3_798 : subd17_3 [1, 2, -1] = true := by decide +kernel
theorem subd17_3_799 : subd17_3 [1, 2, 0] = true := by decide +kernel
theorem sbd17_3_24 : ∀ q ∈ blkd17_3_24, subd17_3 q = true := by
  unfold blkd17_3_24
  exact List.forall_mem_cons.2 ⟨subd17_3_768, List.forall_mem_cons.2 ⟨subd17_3_769, List.forall_mem_cons.2 ⟨subd17_3_770, List.forall_mem_cons.2 ⟨subd17_3_771, List.forall_mem_cons.2 ⟨subd17_3_772, List.forall_mem_cons.2 ⟨subd17_3_773, List.forall_mem_cons.2 ⟨subd17_3_774, List.forall_mem_cons.2 ⟨subd17_3_775, List.forall_mem_cons.2 ⟨subd17_3_776, List.forall_mem_cons.2 ⟨subd17_3_777, List.forall_mem_cons.2 ⟨subd17_3_778, List.forall_mem_cons.2 ⟨subd17_3_779, List.forall_mem_cons.2 ⟨subd17_3_780, List.forall_mem_cons.2 ⟨subd17_3_781, List.forall_mem_cons.2 ⟨subd17_3_782, List.forall_mem_cons.2 ⟨subd17_3_783, List.forall_mem_cons.2 ⟨subd17_3_784, List.forall_mem_cons.2 ⟨subd17_3_785, List.forall_mem_cons.2 ⟨subd17_3_786, List.forall_mem_cons.2 ⟨subd17_3_787, List.forall_mem_cons.2 ⟨subd17_3_788, List.forall_mem_cons.2 ⟨subd17_3_789, List.forall_mem_cons.2 ⟨subd17_3_790, List.forall_mem_cons.2 ⟨subd17_3_791, List.forall_mem_cons.2 ⟨subd17_3_792, List.forall_mem_cons.2 ⟨subd17_3_793, List.forall_mem_cons.2 ⟨subd17_3_794, List.forall_mem_cons.2 ⟨subd17_3_795, List.forall_mem_cons.2 ⟨subd17_3_796, List.forall_mem_cons.2 ⟨subd17_3_797, List.forall_mem_cons.2 ⟨subd17_3_798, List.forall_mem_cons.2 ⟨subd17_3_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_800 : subd17_3 [1, 2, 1] = true := by decide +kernel
theorem subd17_3_801 : subd17_3 [1, 2, 2] = true := by decide +kernel
theorem subd17_3_802 : subd17_3 [1, 2, 3] = true := by decide +kernel
theorem subd17_3_803 : subd17_3 [1, 2, 4] = true := by decide +kernel
theorem subd17_3_804 : subd17_3 [1, 2, 5] = true := by decide +kernel
theorem subd17_3_805 : subd17_3 [1, 2, 6] = true := by decide +kernel
theorem subd17_3_806 : subd17_3 [1, 2, 7] = true := by decide +kernel
theorem subd17_3_807 : subd17_3 [1, 3, -8] = true := by decide +kernel
theorem subd17_3_808 : subd17_3 [1, 3, -7] = true := by decide +kernel
theorem subd17_3_809 : subd17_3 [1, 3, -6] = true := by decide +kernel
theorem subd17_3_810 : subd17_3 [1, 3, -5] = true := by decide +kernel
theorem subd17_3_811 : subd17_3 [1, 3, -4] = true := by decide +kernel
theorem subd17_3_812 : subd17_3 [1, 3, -3] = true := by decide +kernel
theorem subd17_3_813 : subd17_3 [1, 3, -2] = true := by decide +kernel
theorem subd17_3_814 : subd17_3 [1, 3, -1] = true := by decide +kernel
theorem subd17_3_815 : subd17_3 [1, 3, 0] = true := by decide +kernel
theorem subd17_3_816 : subd17_3 [1, 3, 1] = true := by decide +kernel
theorem subd17_3_817 : subd17_3 [1, 3, 2] = true := by decide +kernel
theorem subd17_3_818 : subd17_3 [1, 3, 3] = true := by decide +kernel
theorem subd17_3_819 : subd17_3 [1, 3, 4] = true := by decide +kernel
theorem subd17_3_820 : subd17_3 [1, 3, 5] = true := by decide +kernel
theorem subd17_3_821 : subd17_3 [1, 3, 6] = true := by decide +kernel
theorem subd17_3_822 : subd17_3 [1, 3, 7] = true := by decide +kernel
theorem subd17_3_823 : subd17_3 [1, 4, -8] = true := by decide +kernel
theorem subd17_3_824 : subd17_3 [1, 4, -7] = true := by decide +kernel
theorem subd17_3_825 : subd17_3 [1, 4, -6] = true := by decide +kernel
theorem subd17_3_826 : subd17_3 [1, 4, -5] = true := by decide +kernel
theorem subd17_3_827 : subd17_3 [1, 4, -4] = true := by decide +kernel
theorem subd17_3_828 : subd17_3 [1, 4, -3] = true := by decide +kernel
theorem subd17_3_829 : subd17_3 [1, 4, -2] = true := by decide +kernel
theorem subd17_3_830 : subd17_3 [1, 4, -1] = true := by decide +kernel
theorem subd17_3_831 : subd17_3 [1, 4, 0] = true := by decide +kernel
theorem sbd17_3_25 : ∀ q ∈ blkd17_3_25, subd17_3 q = true := by
  unfold blkd17_3_25
  exact List.forall_mem_cons.2 ⟨subd17_3_800, List.forall_mem_cons.2 ⟨subd17_3_801, List.forall_mem_cons.2 ⟨subd17_3_802, List.forall_mem_cons.2 ⟨subd17_3_803, List.forall_mem_cons.2 ⟨subd17_3_804, List.forall_mem_cons.2 ⟨subd17_3_805, List.forall_mem_cons.2 ⟨subd17_3_806, List.forall_mem_cons.2 ⟨subd17_3_807, List.forall_mem_cons.2 ⟨subd17_3_808, List.forall_mem_cons.2 ⟨subd17_3_809, List.forall_mem_cons.2 ⟨subd17_3_810, List.forall_mem_cons.2 ⟨subd17_3_811, List.forall_mem_cons.2 ⟨subd17_3_812, List.forall_mem_cons.2 ⟨subd17_3_813, List.forall_mem_cons.2 ⟨subd17_3_814, List.forall_mem_cons.2 ⟨subd17_3_815, List.forall_mem_cons.2 ⟨subd17_3_816, List.forall_mem_cons.2 ⟨subd17_3_817, List.forall_mem_cons.2 ⟨subd17_3_818, List.forall_mem_cons.2 ⟨subd17_3_819, List.forall_mem_cons.2 ⟨subd17_3_820, List.forall_mem_cons.2 ⟨subd17_3_821, List.forall_mem_cons.2 ⟨subd17_3_822, List.forall_mem_cons.2 ⟨subd17_3_823, List.forall_mem_cons.2 ⟨subd17_3_824, List.forall_mem_cons.2 ⟨subd17_3_825, List.forall_mem_cons.2 ⟨subd17_3_826, List.forall_mem_cons.2 ⟨subd17_3_827, List.forall_mem_cons.2 ⟨subd17_3_828, List.forall_mem_cons.2 ⟨subd17_3_829, List.forall_mem_cons.2 ⟨subd17_3_830, List.forall_mem_cons.2 ⟨subd17_3_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
