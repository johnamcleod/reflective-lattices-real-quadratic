import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_384 : subd9_1 [1, -2, 12] = true := by decide +kernel
theorem subd9_1_385 : subd9_1 [1, -1, -18] = true := by decide +kernel
theorem subd9_1_386 : subd9_1 [1, -1, -17] = true := by decide +kernel
theorem subd9_1_387 : subd9_1 [1, -1, -16] = true := by decide +kernel
theorem subd9_1_388 : subd9_1 [1, -1, -15] = true := by decide +kernel
theorem subd9_1_389 : subd9_1 [1, -1, -14] = true := by decide +kernel
theorem subd9_1_390 : subd9_1 [1, -1, -13] = true := by decide +kernel
theorem subd9_1_391 : subd9_1 [1, -1, -12] = true := by decide +kernel
theorem subd9_1_392 : subd9_1 [1, -1, -11] = true := by decide +kernel
theorem subd9_1_393 : subd9_1 [1, -1, -10] = true := by decide +kernel
theorem subd9_1_394 : subd9_1 [1, -1, -9] = true := by decide +kernel
theorem subd9_1_395 : subd9_1 [1, -1, -8] = true := by decide +kernel
theorem subd9_1_396 : subd9_1 [1, -1, -7] = true := by decide +kernel
theorem subd9_1_397 : subd9_1 [1, -1, -6] = true := by decide +kernel
theorem subd9_1_398 : subd9_1 [1, -1, -5] = true := by decide +kernel
theorem subd9_1_399 : subd9_1 [1, -1, -4] = true := by decide +kernel
theorem subd9_1_400 : subd9_1 [1, -1, -3] = true := by decide +kernel
theorem subd9_1_401 : subd9_1 [1, -1, -2] = true := by decide +kernel
theorem subd9_1_402 : subd9_1 [1, -1, -1] = true := by decide +kernel
theorem subd9_1_403 : subd9_1 [1, -1, 0] = true := by decide +kernel
theorem subd9_1_404 : subd9_1 [1, -1, 1] = true := by decide +kernel
theorem subd9_1_405 : subd9_1 [1, -1, 2] = true := by decide +kernel
theorem subd9_1_406 : subd9_1 [1, -1, 3] = true := by decide +kernel
theorem subd9_1_407 : subd9_1 [1, -1, 4] = true := by decide +kernel
theorem subd9_1_408 : subd9_1 [1, -1, 5] = true := by decide +kernel
theorem subd9_1_409 : subd9_1 [1, -1, 6] = true := by decide +kernel
theorem subd9_1_410 : subd9_1 [1, -1, 7] = true := by decide +kernel
theorem subd9_1_411 : subd9_1 [1, -1, 8] = true := by decide +kernel
theorem subd9_1_412 : subd9_1 [1, -1, 9] = true := by decide +kernel
theorem subd9_1_413 : subd9_1 [1, -1, 10] = true := by decide +kernel
theorem subd9_1_414 : subd9_1 [1, -1, 11] = true := by decide +kernel
theorem subd9_1_415 : subd9_1 [1, -1, 12] = true := by decide +kernel
theorem sbd9_1_12 : ∀ q ∈ blkd9_1_12, subd9_1 q = true := by
  unfold blkd9_1_12
  exact List.forall_mem_cons.2 ⟨subd9_1_384, List.forall_mem_cons.2 ⟨subd9_1_385, List.forall_mem_cons.2 ⟨subd9_1_386, List.forall_mem_cons.2 ⟨subd9_1_387, List.forall_mem_cons.2 ⟨subd9_1_388, List.forall_mem_cons.2 ⟨subd9_1_389, List.forall_mem_cons.2 ⟨subd9_1_390, List.forall_mem_cons.2 ⟨subd9_1_391, List.forall_mem_cons.2 ⟨subd9_1_392, List.forall_mem_cons.2 ⟨subd9_1_393, List.forall_mem_cons.2 ⟨subd9_1_394, List.forall_mem_cons.2 ⟨subd9_1_395, List.forall_mem_cons.2 ⟨subd9_1_396, List.forall_mem_cons.2 ⟨subd9_1_397, List.forall_mem_cons.2 ⟨subd9_1_398, List.forall_mem_cons.2 ⟨subd9_1_399, List.forall_mem_cons.2 ⟨subd9_1_400, List.forall_mem_cons.2 ⟨subd9_1_401, List.forall_mem_cons.2 ⟨subd9_1_402, List.forall_mem_cons.2 ⟨subd9_1_403, List.forall_mem_cons.2 ⟨subd9_1_404, List.forall_mem_cons.2 ⟨subd9_1_405, List.forall_mem_cons.2 ⟨subd9_1_406, List.forall_mem_cons.2 ⟨subd9_1_407, List.forall_mem_cons.2 ⟨subd9_1_408, List.forall_mem_cons.2 ⟨subd9_1_409, List.forall_mem_cons.2 ⟨subd9_1_410, List.forall_mem_cons.2 ⟨subd9_1_411, List.forall_mem_cons.2 ⟨subd9_1_412, List.forall_mem_cons.2 ⟨subd9_1_413, List.forall_mem_cons.2 ⟨subd9_1_414, List.forall_mem_cons.2 ⟨subd9_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_416 : subd9_1 [1, -1, 13] = true := by decide +kernel
theorem subd9_1_417 : subd9_1 [1, -1, 14] = true := by decide +kernel
theorem subd9_1_418 : subd9_1 [1, -1, 15] = true := by decide +kernel
theorem subd9_1_419 : subd9_1 [1, -1, 16] = true := by decide +kernel
theorem subd9_1_420 : subd9_1 [1, -1, 17] = true := by decide +kernel
theorem subd9_1_421 : subd9_1 [1, 0, -19] = true := by decide +kernel
theorem subd9_1_422 : subd9_1 [1, 0, -18] = true := by decide +kernel
theorem subd9_1_423 : subd9_1 [1, 0, -17] = true := by decide +kernel
theorem subd9_1_424 : subd9_1 [1, 0, -16] = true := by decide +kernel
theorem subd9_1_425 : subd9_1 [1, 0, -15] = true := by decide +kernel
theorem subd9_1_426 : subd9_1 [1, 0, -14] = true := by decide +kernel
theorem subd9_1_427 : subd9_1 [1, 0, -13] = true := by decide +kernel
theorem subd9_1_428 : subd9_1 [1, 0, -12] = true := by decide +kernel
theorem subd9_1_429 : subd9_1 [1, 0, -11] = true := by decide +kernel
theorem subd9_1_430 : subd9_1 [1, 0, -10] = true := by decide +kernel
theorem subd9_1_431 : subd9_1 [1, 0, -9] = true := by decide +kernel
theorem subd9_1_432 : subd9_1 [1, 0, -8] = true := by decide +kernel
theorem subd9_1_433 : subd9_1 [1, 0, -7] = true := by decide +kernel
theorem subd9_1_434 : subd9_1 [1, 0, -6] = true := by decide +kernel
theorem subd9_1_435 : subd9_1 [1, 0, -5] = true := by decide +kernel
theorem subd9_1_436 : subd9_1 [1, 0, -4] = true := by decide +kernel
theorem subd9_1_437 : subd9_1 [1, 0, -3] = true := by decide +kernel
theorem subd9_1_438 : subd9_1 [1, 0, -2] = true := by decide +kernel
theorem subd9_1_439 : subd9_1 [1, 0, -1] = true := by decide +kernel
theorem subd9_1_440 : subd9_1 [1, 0, 0] = true := by decide +kernel
theorem subd9_1_441 : subd9_1 [1, 0, 1] = true := by decide +kernel
theorem subd9_1_442 : subd9_1 [1, 0, 2] = true := by decide +kernel
theorem subd9_1_443 : subd9_1 [1, 0, 3] = true := by decide +kernel
theorem subd9_1_444 : subd9_1 [1, 0, 4] = true := by decide +kernel
theorem subd9_1_445 : subd9_1 [1, 0, 5] = true := by decide +kernel
theorem subd9_1_446 : subd9_1 [1, 0, 6] = true := by decide +kernel
theorem subd9_1_447 : subd9_1 [1, 0, 7] = true := by decide +kernel
theorem sbd9_1_13 : ∀ q ∈ blkd9_1_13, subd9_1 q = true := by
  unfold blkd9_1_13
  exact List.forall_mem_cons.2 ⟨subd9_1_416, List.forall_mem_cons.2 ⟨subd9_1_417, List.forall_mem_cons.2 ⟨subd9_1_418, List.forall_mem_cons.2 ⟨subd9_1_419, List.forall_mem_cons.2 ⟨subd9_1_420, List.forall_mem_cons.2 ⟨subd9_1_421, List.forall_mem_cons.2 ⟨subd9_1_422, List.forall_mem_cons.2 ⟨subd9_1_423, List.forall_mem_cons.2 ⟨subd9_1_424, List.forall_mem_cons.2 ⟨subd9_1_425, List.forall_mem_cons.2 ⟨subd9_1_426, List.forall_mem_cons.2 ⟨subd9_1_427, List.forall_mem_cons.2 ⟨subd9_1_428, List.forall_mem_cons.2 ⟨subd9_1_429, List.forall_mem_cons.2 ⟨subd9_1_430, List.forall_mem_cons.2 ⟨subd9_1_431, List.forall_mem_cons.2 ⟨subd9_1_432, List.forall_mem_cons.2 ⟨subd9_1_433, List.forall_mem_cons.2 ⟨subd9_1_434, List.forall_mem_cons.2 ⟨subd9_1_435, List.forall_mem_cons.2 ⟨subd9_1_436, List.forall_mem_cons.2 ⟨subd9_1_437, List.forall_mem_cons.2 ⟨subd9_1_438, List.forall_mem_cons.2 ⟨subd9_1_439, List.forall_mem_cons.2 ⟨subd9_1_440, List.forall_mem_cons.2 ⟨subd9_1_441, List.forall_mem_cons.2 ⟨subd9_1_442, List.forall_mem_cons.2 ⟨subd9_1_443, List.forall_mem_cons.2 ⟨subd9_1_444, List.forall_mem_cons.2 ⟨subd9_1_445, List.forall_mem_cons.2 ⟨subd9_1_446, List.forall_mem_cons.2 ⟨subd9_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_448 : subd9_1 [1, 0, 8] = true := by decide +kernel
theorem subd9_1_449 : subd9_1 [1, 0, 9] = true := by decide +kernel
theorem subd9_1_450 : subd9_1 [1, 0, 10] = true := by decide +kernel
theorem subd9_1_451 : subd9_1 [1, 0, 11] = true := by decide +kernel
theorem subd9_1_452 : subd9_1 [1, 0, 12] = true := by decide +kernel
theorem subd9_1_453 : subd9_1 [1, 0, 13] = true := by decide +kernel
theorem subd9_1_454 : subd9_1 [1, 0, 14] = true := by decide +kernel
theorem subd9_1_455 : subd9_1 [1, 0, 15] = true := by decide +kernel
theorem subd9_1_456 : subd9_1 [1, 0, 16] = true := by decide +kernel
theorem subd9_1_457 : subd9_1 [1, 0, 17] = true := by decide +kernel
theorem subd9_1_458 : subd9_1 [1, 0, 18] = true := by decide +kernel
theorem subd9_1_459 : subd9_1 [1, 1, -16] = true := by decide +kernel
theorem subd9_1_460 : subd9_1 [1, 1, -15] = true := by decide +kernel
theorem subd9_1_461 : subd9_1 [1, 1, -14] = true := by decide +kernel
theorem subd9_1_462 : subd9_1 [1, 1, -13] = true := by decide +kernel
theorem subd9_1_463 : subd9_1 [1, 1, -12] = true := by decide +kernel
theorem subd9_1_464 : subd9_1 [1, 1, -11] = true := by decide +kernel
theorem subd9_1_465 : subd9_1 [1, 1, -10] = true := by decide +kernel
theorem subd9_1_466 : subd9_1 [1, 1, -9] = true := by decide +kernel
theorem subd9_1_467 : subd9_1 [1, 1, -8] = true := by decide +kernel
theorem subd9_1_468 : subd9_1 [1, 1, -7] = true := by decide +kernel
theorem subd9_1_469 : subd9_1 [1, 1, -6] = true := by decide +kernel
theorem subd9_1_470 : subd9_1 [1, 1, -5] = true := by decide +kernel
theorem subd9_1_471 : subd9_1 [1, 1, -4] = true := by decide +kernel
theorem subd9_1_472 : subd9_1 [1, 1, -3] = true := by decide +kernel
theorem subd9_1_473 : subd9_1 [1, 1, -2] = true := by decide +kernel
theorem subd9_1_474 : subd9_1 [1, 1, -1] = true := by decide +kernel
theorem subd9_1_475 : subd9_1 [1, 1, 0] = true := by decide +kernel
theorem subd9_1_476 : subd9_1 [1, 1, 1] = true := by decide +kernel
theorem subd9_1_477 : subd9_1 [1, 1, 2] = true := by decide +kernel
theorem subd9_1_478 : subd9_1 [1, 1, 3] = true := by decide +kernel
theorem subd9_1_479 : subd9_1 [1, 1, 4] = true := by decide +kernel
theorem sbd9_1_14 : ∀ q ∈ blkd9_1_14, subd9_1 q = true := by
  unfold blkd9_1_14
  exact List.forall_mem_cons.2 ⟨subd9_1_448, List.forall_mem_cons.2 ⟨subd9_1_449, List.forall_mem_cons.2 ⟨subd9_1_450, List.forall_mem_cons.2 ⟨subd9_1_451, List.forall_mem_cons.2 ⟨subd9_1_452, List.forall_mem_cons.2 ⟨subd9_1_453, List.forall_mem_cons.2 ⟨subd9_1_454, List.forall_mem_cons.2 ⟨subd9_1_455, List.forall_mem_cons.2 ⟨subd9_1_456, List.forall_mem_cons.2 ⟨subd9_1_457, List.forall_mem_cons.2 ⟨subd9_1_458, List.forall_mem_cons.2 ⟨subd9_1_459, List.forall_mem_cons.2 ⟨subd9_1_460, List.forall_mem_cons.2 ⟨subd9_1_461, List.forall_mem_cons.2 ⟨subd9_1_462, List.forall_mem_cons.2 ⟨subd9_1_463, List.forall_mem_cons.2 ⟨subd9_1_464, List.forall_mem_cons.2 ⟨subd9_1_465, List.forall_mem_cons.2 ⟨subd9_1_466, List.forall_mem_cons.2 ⟨subd9_1_467, List.forall_mem_cons.2 ⟨subd9_1_468, List.forall_mem_cons.2 ⟨subd9_1_469, List.forall_mem_cons.2 ⟨subd9_1_470, List.forall_mem_cons.2 ⟨subd9_1_471, List.forall_mem_cons.2 ⟨subd9_1_472, List.forall_mem_cons.2 ⟨subd9_1_473, List.forall_mem_cons.2 ⟨subd9_1_474, List.forall_mem_cons.2 ⟨subd9_1_475, List.forall_mem_cons.2 ⟨subd9_1_476, List.forall_mem_cons.2 ⟨subd9_1_477, List.forall_mem_cons.2 ⟨subd9_1_478, List.forall_mem_cons.2 ⟨subd9_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_480 : subd9_1 [1, 1, 5] = true := by decide +kernel
theorem subd9_1_481 : subd9_1 [1, 1, 6] = true := by decide +kernel
theorem subd9_1_482 : subd9_1 [1, 1, 7] = true := by decide +kernel
theorem subd9_1_483 : subd9_1 [1, 1, 8] = true := by decide +kernel
theorem subd9_1_484 : subd9_1 [1, 1, 9] = true := by decide +kernel
theorem subd9_1_485 : subd9_1 [1, 1, 10] = true := by decide +kernel
theorem subd9_1_486 : subd9_1 [1, 1, 11] = true := by decide +kernel
theorem subd9_1_487 : subd9_1 [1, 1, 12] = true := by decide +kernel
theorem subd9_1_488 : subd9_1 [1, 1, 13] = true := by decide +kernel
theorem subd9_1_489 : subd9_1 [1, 1, 14] = true := by decide +kernel
theorem subd9_1_490 : subd9_1 [1, 1, 15] = true := by decide +kernel
theorem subd9_1_491 : subd9_1 [1, 1, 16] = true := by decide +kernel
theorem subd9_1_492 : subd9_1 [1, 2] = true := by decide +kernel
theorem subd9_1_493 : subd9_1 [2, -3] = true := by decide +kernel
theorem subd9_1_494 : subd9_1 [2, -2] = true := by decide +kernel
theorem subd9_1_495 : subd9_1 [2, -1, -11] = true := by decide +kernel
theorem subd9_1_496 : subd9_1 [2, -1, -10] = true := by decide +kernel
theorem subd9_1_497 : subd9_1 [2, -1, -9] = true := by decide +kernel
theorem subd9_1_498 : subd9_1 [2, -1, -8] = true := by decide +kernel
theorem subd9_1_499 : subd9_1 [2, -1, -7] = true := by decide +kernel
theorem subd9_1_500 : subd9_1 [2, -1, -6] = true := by decide +kernel
theorem subd9_1_501 : subd9_1 [2, -1, -5] = true := by decide +kernel
theorem subd9_1_502 : subd9_1 [2, -1, -4] = true := by decide +kernel
theorem subd9_1_503 : subd9_1 [2, -1, -3] = true := by decide +kernel
theorem subd9_1_504 : subd9_1 [2, -1, -2] = true := by decide +kernel
theorem subd9_1_505 : subd9_1 [2, -1, -1] = true := by decide +kernel
theorem subd9_1_506 : subd9_1 [2, -1, 0] = true := by decide +kernel
theorem subd9_1_507 : subd9_1 [2, -1, 1] = true := by decide +kernel
theorem subd9_1_508 : subd9_1 [2, -1, 2] = true := by decide +kernel
theorem subd9_1_509 : subd9_1 [2, -1, 3] = true := by decide +kernel
theorem subd9_1_510 : subd9_1 [2, -1, 4] = true := by decide +kernel
theorem subd9_1_511 : subd9_1 [2, -1, 5] = true := by decide +kernel
theorem sbd9_1_15 : ∀ q ∈ blkd9_1_15, subd9_1 q = true := by
  unfold blkd9_1_15
  exact List.forall_mem_cons.2 ⟨subd9_1_480, List.forall_mem_cons.2 ⟨subd9_1_481, List.forall_mem_cons.2 ⟨subd9_1_482, List.forall_mem_cons.2 ⟨subd9_1_483, List.forall_mem_cons.2 ⟨subd9_1_484, List.forall_mem_cons.2 ⟨subd9_1_485, List.forall_mem_cons.2 ⟨subd9_1_486, List.forall_mem_cons.2 ⟨subd9_1_487, List.forall_mem_cons.2 ⟨subd9_1_488, List.forall_mem_cons.2 ⟨subd9_1_489, List.forall_mem_cons.2 ⟨subd9_1_490, List.forall_mem_cons.2 ⟨subd9_1_491, List.forall_mem_cons.2 ⟨subd9_1_492, List.forall_mem_cons.2 ⟨subd9_1_493, List.forall_mem_cons.2 ⟨subd9_1_494, List.forall_mem_cons.2 ⟨subd9_1_495, List.forall_mem_cons.2 ⟨subd9_1_496, List.forall_mem_cons.2 ⟨subd9_1_497, List.forall_mem_cons.2 ⟨subd9_1_498, List.forall_mem_cons.2 ⟨subd9_1_499, List.forall_mem_cons.2 ⟨subd9_1_500, List.forall_mem_cons.2 ⟨subd9_1_501, List.forall_mem_cons.2 ⟨subd9_1_502, List.forall_mem_cons.2 ⟨subd9_1_503, List.forall_mem_cons.2 ⟨subd9_1_504, List.forall_mem_cons.2 ⟨subd9_1_505, List.forall_mem_cons.2 ⟨subd9_1_506, List.forall_mem_cons.2 ⟨subd9_1_507, List.forall_mem_cons.2 ⟨subd9_1_508, List.forall_mem_cons.2 ⟨subd9_1_509, List.forall_mem_cons.2 ⟨subd9_1_510, List.forall_mem_cons.2 ⟨subd9_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_512 : subd9_1 [2, -1, 6] = true := by decide +kernel
theorem subd9_1_513 : subd9_1 [2, -1, 7] = true := by decide +kernel
theorem subd9_1_514 : subd9_1 [2, -1, 8] = true := by decide +kernel
theorem subd9_1_515 : subd9_1 [2, -1, 9] = true := by decide +kernel
theorem subd9_1_516 : subd9_1 [2, -1, 10] = true := by decide +kernel
theorem subd9_1_517 : subd9_1 [2, 0, -11] = true := by decide +kernel
theorem subd9_1_518 : subd9_1 [2, 0, -10] = true := by decide +kernel
theorem subd9_1_519 : subd9_1 [2, 0, -9] = true := by decide +kernel
theorem subd9_1_520 : subd9_1 [2, 0, -8] = true := by decide +kernel
theorem subd9_1_521 : subd9_1 [2, 0, -7] = true := by decide +kernel
theorem subd9_1_522 : subd9_1 [2, 0, -6] = true := by decide +kernel
theorem subd9_1_523 : subd9_1 [2, 0, -5] = true := by decide +kernel
theorem subd9_1_524 : subd9_1 [2, 0, -4] = true := by decide +kernel
theorem subd9_1_525 : subd9_1 [2, 0, -3] = true := by decide +kernel
theorem subd9_1_526 : subd9_1 [2, 0, -2] = true := by decide +kernel
theorem subd9_1_527 : subd9_1 [2, 0, -1] = true := by decide +kernel
theorem subd9_1_528 : subd9_1 [2, 0, 0] = true := by decide +kernel
theorem subd9_1_529 : subd9_1 [2, 0, 1] = true := by decide +kernel
theorem subd9_1_530 : subd9_1 [2, 0, 2] = true := by decide +kernel
theorem subd9_1_531 : subd9_1 [2, 0, 3] = true := by decide +kernel
theorem subd9_1_532 : subd9_1 [2, 0, 4] = true := by decide +kernel
theorem subd9_1_533 : subd9_1 [2, 0, 5] = true := by decide +kernel
theorem subd9_1_534 : subd9_1 [2, 0, 6] = true := by decide +kernel
theorem subd9_1_535 : subd9_1 [2, 0, 7] = true := by decide +kernel
theorem subd9_1_536 : subd9_1 [2, 0, 8] = true := by decide +kernel
theorem subd9_1_537 : subd9_1 [2, 0, 9] = true := by decide +kernel
theorem subd9_1_538 : subd9_1 [2, 0, 10] = true := by decide +kernel
theorem sbd9_1_16 : ∀ q ∈ blkd9_1_16, subd9_1 q = true := by
  unfold blkd9_1_16
  exact List.forall_mem_cons.2 ⟨subd9_1_512, List.forall_mem_cons.2 ⟨subd9_1_513, List.forall_mem_cons.2 ⟨subd9_1_514, List.forall_mem_cons.2 ⟨subd9_1_515, List.forall_mem_cons.2 ⟨subd9_1_516, List.forall_mem_cons.2 ⟨subd9_1_517, List.forall_mem_cons.2 ⟨subd9_1_518, List.forall_mem_cons.2 ⟨subd9_1_519, List.forall_mem_cons.2 ⟨subd9_1_520, List.forall_mem_cons.2 ⟨subd9_1_521, List.forall_mem_cons.2 ⟨subd9_1_522, List.forall_mem_cons.2 ⟨subd9_1_523, List.forall_mem_cons.2 ⟨subd9_1_524, List.forall_mem_cons.2 ⟨subd9_1_525, List.forall_mem_cons.2 ⟨subd9_1_526, List.forall_mem_cons.2 ⟨subd9_1_527, List.forall_mem_cons.2 ⟨subd9_1_528, List.forall_mem_cons.2 ⟨subd9_1_529, List.forall_mem_cons.2 ⟨subd9_1_530, List.forall_mem_cons.2 ⟨subd9_1_531, List.forall_mem_cons.2 ⟨subd9_1_532, List.forall_mem_cons.2 ⟨subd9_1_533, List.forall_mem_cons.2 ⟨subd9_1_534, List.forall_mem_cons.2 ⟨subd9_1_535, List.forall_mem_cons.2 ⟨subd9_1_536, List.forall_mem_cons.2 ⟨subd9_1_537, List.forall_mem_cons.2 ⟨subd9_1_538, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-6, -2] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-6, -1] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [-6, 0] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [-6, 1] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [-6, 2] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [-6, 3] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [-6, 4] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [-5, -4] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [-5, -3] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [-5, -2] = true := by decide +kernel
theorem subd10_0_10 : subd10_0 [-5, -1] = true := by decide +kernel
theorem subd10_0_11 : subd10_0 [-5, 0] = true := by decide +kernel
theorem subd10_0_12 : subd10_0 [-5, 1] = true := by decide +kernel
theorem subd10_0_13 : subd10_0 [-5, 2] = true := by decide +kernel
theorem subd10_0_14 : subd10_0 [-5, 3] = true := by decide +kernel
theorem subd10_0_15 : subd10_0 [-5, 4] = true := by decide +kernel
theorem subd10_0_16 : subd10_0 [-5, 5] = true := by decide +kernel
theorem subd10_0_17 : subd10_0 [-5, 6] = true := by decide +kernel
theorem subd10_0_18 : subd10_0 [-4, -5] = true := by decide +kernel
theorem subd10_0_19 : subd10_0 [-4, -4] = true := by decide +kernel
theorem subd10_0_20 : subd10_0 [-4, -3] = true := by decide +kernel
theorem subd10_0_21 : subd10_0 [-4, -2] = true := by decide +kernel
theorem subd10_0_22 : subd10_0 [-4, -1] = true := by decide +kernel
theorem subd10_0_23 : subd10_0 [-4, 0] = true := by decide +kernel
theorem subd10_0_24 : subd10_0 [-4, 1] = true := by decide +kernel
theorem subd10_0_25 : subd10_0 [-4, 2] = true := by decide +kernel
theorem subd10_0_26 : subd10_0 [-4, 3] = true := by decide +kernel
theorem subd10_0_27 : subd10_0 [-4, 4] = true := by decide +kernel
theorem subd10_0_28 : subd10_0 [-4, 5] = true := by decide +kernel
theorem subd10_0_29 : subd10_0 [-4, 6] = true := by decide +kernel
theorem subd10_0_30 : subd10_0 [-4, 7] = true := by decide +kernel
theorem subd10_0_31 : subd10_0 [-3, -6] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_cons.2 ⟨subd10_0_10, List.forall_mem_cons.2 ⟨subd10_0_11, List.forall_mem_cons.2 ⟨subd10_0_12, List.forall_mem_cons.2 ⟨subd10_0_13, List.forall_mem_cons.2 ⟨subd10_0_14, List.forall_mem_cons.2 ⟨subd10_0_15, List.forall_mem_cons.2 ⟨subd10_0_16, List.forall_mem_cons.2 ⟨subd10_0_17, List.forall_mem_cons.2 ⟨subd10_0_18, List.forall_mem_cons.2 ⟨subd10_0_19, List.forall_mem_cons.2 ⟨subd10_0_20, List.forall_mem_cons.2 ⟨subd10_0_21, List.forall_mem_cons.2 ⟨subd10_0_22, List.forall_mem_cons.2 ⟨subd10_0_23, List.forall_mem_cons.2 ⟨subd10_0_24, List.forall_mem_cons.2 ⟨subd10_0_25, List.forall_mem_cons.2 ⟨subd10_0_26, List.forall_mem_cons.2 ⟨subd10_0_27, List.forall_mem_cons.2 ⟨subd10_0_28, List.forall_mem_cons.2 ⟨subd10_0_29, List.forall_mem_cons.2 ⟨subd10_0_30, List.forall_mem_cons.2 ⟨subd10_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
