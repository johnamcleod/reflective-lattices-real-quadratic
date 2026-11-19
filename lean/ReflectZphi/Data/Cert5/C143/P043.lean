import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd16_3_384 : subd16_3 [0, 1, -10] = true := by decide +kernel
theorem subd16_3_385 : subd16_3 [0, 1, -9] = true := by decide +kernel
theorem subd16_3_386 : subd16_3 [0, 1, -8] = true := by decide +kernel
theorem subd16_3_387 : subd16_3 [0, 1, -7] = true := by decide +kernel
theorem subd16_3_388 : subd16_3 [0, 1, -6] = true := by decide +kernel
theorem subd16_3_389 : subd16_3 [0, 1, -5] = true := by decide +kernel
theorem subd16_3_390 : subd16_3 [0, 1, -4] = true := by decide +kernel
theorem subd16_3_391 : subd16_3 [0, 1, -3] = true := by decide +kernel
theorem subd16_3_392 : subd16_3 [0, 1, -2] = true := by decide +kernel
theorem subd16_3_393 : subd16_3 [0, 1, -1] = true := by decide +kernel
theorem subd16_3_394 : subd16_3 [0, 1, 0] = true := by decide +kernel
theorem subd16_3_395 : subd16_3 [0, 1, 1] = true := by decide +kernel
theorem subd16_3_396 : subd16_3 [0, 1, 2] = true := by decide +kernel
theorem subd16_3_397 : subd16_3 [0, 1, 3] = true := by decide +kernel
theorem subd16_3_398 : subd16_3 [0, 1, 4] = true := by decide +kernel
theorem subd16_3_399 : subd16_3 [0, 1, 5] = true := by decide +kernel
theorem subd16_3_400 : subd16_3 [0, 1, 6] = true := by decide +kernel
theorem subd16_3_401 : subd16_3 [0, 1, 7] = true := by decide +kernel
theorem subd16_3_402 : subd16_3 [0, 1, 8] = true := by decide +kernel
theorem subd16_3_403 : subd16_3 [0, 1, 9] = true := by decide +kernel
theorem subd16_3_404 : subd16_3 [0, 1, 10] = true := by decide +kernel
theorem subd16_3_405 : subd16_3 [0, 1, 11] = true := by decide +kernel
theorem subd16_3_406 : subd16_3 [0, 2, -12] = true := by decide +kernel
theorem subd16_3_407 : subd16_3 [0, 2, -11] = true := by decide +kernel
theorem subd16_3_408 : subd16_3 [0, 2, -10] = true := by decide +kernel
theorem subd16_3_409 : subd16_3 [0, 2, -9] = true := by decide +kernel
theorem subd16_3_410 : subd16_3 [0, 2, -8] = true := by decide +kernel
theorem subd16_3_411 : subd16_3 [0, 2, -7] = true := by decide +kernel
theorem subd16_3_412 : subd16_3 [0, 2, -6] = true := by decide +kernel
theorem subd16_3_413 : subd16_3 [0, 2, -5] = true := by decide +kernel
theorem subd16_3_414 : subd16_3 [0, 2, -4] = true := by decide +kernel
theorem subd16_3_415 : subd16_3 [0, 2, -3] = true := by decide +kernel
theorem sbd16_3_12 : ∀ q ∈ blkd16_3_12, subd16_3 q = true := by
  unfold blkd16_3_12
  exact List.forall_mem_cons.2 ⟨subd16_3_384, List.forall_mem_cons.2 ⟨subd16_3_385, List.forall_mem_cons.2 ⟨subd16_3_386, List.forall_mem_cons.2 ⟨subd16_3_387, List.forall_mem_cons.2 ⟨subd16_3_388, List.forall_mem_cons.2 ⟨subd16_3_389, List.forall_mem_cons.2 ⟨subd16_3_390, List.forall_mem_cons.2 ⟨subd16_3_391, List.forall_mem_cons.2 ⟨subd16_3_392, List.forall_mem_cons.2 ⟨subd16_3_393, List.forall_mem_cons.2 ⟨subd16_3_394, List.forall_mem_cons.2 ⟨subd16_3_395, List.forall_mem_cons.2 ⟨subd16_3_396, List.forall_mem_cons.2 ⟨subd16_3_397, List.forall_mem_cons.2 ⟨subd16_3_398, List.forall_mem_cons.2 ⟨subd16_3_399, List.forall_mem_cons.2 ⟨subd16_3_400, List.forall_mem_cons.2 ⟨subd16_3_401, List.forall_mem_cons.2 ⟨subd16_3_402, List.forall_mem_cons.2 ⟨subd16_3_403, List.forall_mem_cons.2 ⟨subd16_3_404, List.forall_mem_cons.2 ⟨subd16_3_405, List.forall_mem_cons.2 ⟨subd16_3_406, List.forall_mem_cons.2 ⟨subd16_3_407, List.forall_mem_cons.2 ⟨subd16_3_408, List.forall_mem_cons.2 ⟨subd16_3_409, List.forall_mem_cons.2 ⟨subd16_3_410, List.forall_mem_cons.2 ⟨subd16_3_411, List.forall_mem_cons.2 ⟨subd16_3_412, List.forall_mem_cons.2 ⟨subd16_3_413, List.forall_mem_cons.2 ⟨subd16_3_414, List.forall_mem_cons.2 ⟨subd16_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_416 : subd16_3 [0, 2, -2] = true := by decide +kernel
theorem subd16_3_417 : subd16_3 [0, 2, -1] = true := by decide +kernel
theorem subd16_3_418 : subd16_3 [0, 2, 0] = true := by decide +kernel
theorem subd16_3_419 : subd16_3 [0, 2, 1] = true := by decide +kernel
theorem subd16_3_420 : subd16_3 [0, 2, 2] = true := by decide +kernel
theorem subd16_3_421 : subd16_3 [0, 2, 3] = true := by decide +kernel
theorem subd16_3_422 : subd16_3 [0, 2, 4] = true := by decide +kernel
theorem subd16_3_423 : subd16_3 [0, 2, 5] = true := by decide +kernel
theorem subd16_3_424 : subd16_3 [0, 2, 6] = true := by decide +kernel
theorem subd16_3_425 : subd16_3 [0, 2, 7] = true := by decide +kernel
theorem subd16_3_426 : subd16_3 [0, 2, 8] = true := by decide +kernel
theorem subd16_3_427 : subd16_3 [0, 2, 9] = true := by decide +kernel
theorem subd16_3_428 : subd16_3 [0, 3, -10] = true := by decide +kernel
theorem subd16_3_429 : subd16_3 [0, 3, -9] = true := by decide +kernel
theorem subd16_3_430 : subd16_3 [0, 3, -8] = true := by decide +kernel
theorem subd16_3_431 : subd16_3 [0, 3, -7] = true := by decide +kernel
theorem subd16_3_432 : subd16_3 [0, 3, -6] = true := by decide +kernel
theorem subd16_3_433 : subd16_3 [0, 3, -5] = true := by decide +kernel
theorem subd16_3_434 : subd16_3 [0, 3, -4] = true := by decide +kernel
theorem subd16_3_435 : subd16_3 [0, 3, -3] = true := by decide +kernel
theorem subd16_3_436 : subd16_3 [0, 3, -2] = true := by decide +kernel
theorem subd16_3_437 : subd16_3 [0, 3, -1] = true := by decide +kernel
theorem subd16_3_438 : subd16_3 [0, 3, 0] = true := by decide +kernel
theorem subd16_3_439 : subd16_3 [0, 3, 1] = true := by decide +kernel
theorem subd16_3_440 : subd16_3 [0, 3, 2] = true := by decide +kernel
theorem subd16_3_441 : subd16_3 [0, 3, 3] = true := by decide +kernel
theorem subd16_3_442 : subd16_3 [0, 3, 4] = true := by decide +kernel
theorem subd16_3_443 : subd16_3 [0, 3, 5] = true := by decide +kernel
theorem subd16_3_444 : subd16_3 [0, 3, 6] = true := by decide +kernel
theorem subd16_3_445 : subd16_3 [1, -4] = true := by decide +kernel
theorem subd16_3_446 : subd16_3 [1, -3, -6] = true := by decide +kernel
theorem subd16_3_447 : subd16_3 [1, -3, -5] = true := by decide +kernel
theorem sbd16_3_13 : ∀ q ∈ blkd16_3_13, subd16_3 q = true := by
  unfold blkd16_3_13
  exact List.forall_mem_cons.2 ⟨subd16_3_416, List.forall_mem_cons.2 ⟨subd16_3_417, List.forall_mem_cons.2 ⟨subd16_3_418, List.forall_mem_cons.2 ⟨subd16_3_419, List.forall_mem_cons.2 ⟨subd16_3_420, List.forall_mem_cons.2 ⟨subd16_3_421, List.forall_mem_cons.2 ⟨subd16_3_422, List.forall_mem_cons.2 ⟨subd16_3_423, List.forall_mem_cons.2 ⟨subd16_3_424, List.forall_mem_cons.2 ⟨subd16_3_425, List.forall_mem_cons.2 ⟨subd16_3_426, List.forall_mem_cons.2 ⟨subd16_3_427, List.forall_mem_cons.2 ⟨subd16_3_428, List.forall_mem_cons.2 ⟨subd16_3_429, List.forall_mem_cons.2 ⟨subd16_3_430, List.forall_mem_cons.2 ⟨subd16_3_431, List.forall_mem_cons.2 ⟨subd16_3_432, List.forall_mem_cons.2 ⟨subd16_3_433, List.forall_mem_cons.2 ⟨subd16_3_434, List.forall_mem_cons.2 ⟨subd16_3_435, List.forall_mem_cons.2 ⟨subd16_3_436, List.forall_mem_cons.2 ⟨subd16_3_437, List.forall_mem_cons.2 ⟨subd16_3_438, List.forall_mem_cons.2 ⟨subd16_3_439, List.forall_mem_cons.2 ⟨subd16_3_440, List.forall_mem_cons.2 ⟨subd16_3_441, List.forall_mem_cons.2 ⟨subd16_3_442, List.forall_mem_cons.2 ⟨subd16_3_443, List.forall_mem_cons.2 ⟨subd16_3_444, List.forall_mem_cons.2 ⟨subd16_3_445, List.forall_mem_cons.2 ⟨subd16_3_446, List.forall_mem_cons.2 ⟨subd16_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_448 : subd16_3 [1, -3, -4] = true := by decide +kernel
theorem subd16_3_449 : subd16_3 [1, -3, -3] = true := by decide +kernel
theorem subd16_3_450 : subd16_3 [1, -3, -2] = true := by decide +kernel
theorem subd16_3_451 : subd16_3 [1, -3, -1] = true := by decide +kernel
theorem subd16_3_452 : subd16_3 [1, -3, 0] = true := by decide +kernel
theorem subd16_3_453 : subd16_3 [1, -3, 1] = true := by decide +kernel
theorem subd16_3_454 : subd16_3 [1, -3, 2] = true := by decide +kernel
theorem subd16_3_455 : subd16_3 [1, -3, 3] = true := by decide +kernel
theorem subd16_3_456 : subd16_3 [1, -3, 4] = true := by decide +kernel
theorem subd16_3_457 : subd16_3 [1, -3, 5] = true := by decide +kernel
theorem subd16_3_458 : subd16_3 [1, -3, 6] = true := by decide +kernel
theorem subd16_3_459 : subd16_3 [1, -3, 7] = true := by decide +kernel
theorem subd16_3_460 : subd16_3 [1, -3, 8] = true := by decide +kernel
theorem subd16_3_461 : subd16_3 [1, -2, -10] = true := by decide +kernel
theorem subd16_3_462 : subd16_3 [1, -2, -9] = true := by decide +kernel
theorem subd16_3_463 : subd16_3 [1, -2, -8] = true := by decide +kernel
theorem subd16_3_464 : subd16_3 [1, -2, -7] = true := by decide +kernel
theorem subd16_3_465 : subd16_3 [1, -2, -6] = true := by decide +kernel
theorem subd16_3_466 : subd16_3 [1, -2, -5] = true := by decide +kernel
theorem subd16_3_467 : subd16_3 [1, -2, -4] = true := by decide +kernel
theorem subd16_3_468 : subd16_3 [1, -2, -3] = true := by decide +kernel
theorem subd16_3_469 : subd16_3 [1, -2, -2] = true := by decide +kernel
theorem subd16_3_470 : subd16_3 [1, -2, -1] = true := by decide +kernel
theorem subd16_3_471 : subd16_3 [1, -2, 0] = true := by decide +kernel
theorem subd16_3_472 : subd16_3 [1, -2, 1] = true := by decide +kernel
theorem subd16_3_473 : subd16_3 [1, -2, 2] = true := by decide +kernel
theorem subd16_3_474 : subd16_3 [1, -2, 3] = true := by decide +kernel
theorem subd16_3_475 : subd16_3 [1, -2, 4] = true := by decide +kernel
theorem subd16_3_476 : subd16_3 [1, -2, 5] = true := by decide +kernel
theorem subd16_3_477 : subd16_3 [1, -2, 6] = true := by decide +kernel
theorem subd16_3_478 : subd16_3 [1, -2, 7] = true := by decide +kernel
theorem subd16_3_479 : subd16_3 [1, -2, 8] = true := by decide +kernel
theorem sbd16_3_14 : ∀ q ∈ blkd16_3_14, subd16_3 q = true := by
  unfold blkd16_3_14
  exact List.forall_mem_cons.2 ⟨subd16_3_448, List.forall_mem_cons.2 ⟨subd16_3_449, List.forall_mem_cons.2 ⟨subd16_3_450, List.forall_mem_cons.2 ⟨subd16_3_451, List.forall_mem_cons.2 ⟨subd16_3_452, List.forall_mem_cons.2 ⟨subd16_3_453, List.forall_mem_cons.2 ⟨subd16_3_454, List.forall_mem_cons.2 ⟨subd16_3_455, List.forall_mem_cons.2 ⟨subd16_3_456, List.forall_mem_cons.2 ⟨subd16_3_457, List.forall_mem_cons.2 ⟨subd16_3_458, List.forall_mem_cons.2 ⟨subd16_3_459, List.forall_mem_cons.2 ⟨subd16_3_460, List.forall_mem_cons.2 ⟨subd16_3_461, List.forall_mem_cons.2 ⟨subd16_3_462, List.forall_mem_cons.2 ⟨subd16_3_463, List.forall_mem_cons.2 ⟨subd16_3_464, List.forall_mem_cons.2 ⟨subd16_3_465, List.forall_mem_cons.2 ⟨subd16_3_466, List.forall_mem_cons.2 ⟨subd16_3_467, List.forall_mem_cons.2 ⟨subd16_3_468, List.forall_mem_cons.2 ⟨subd16_3_469, List.forall_mem_cons.2 ⟨subd16_3_470, List.forall_mem_cons.2 ⟨subd16_3_471, List.forall_mem_cons.2 ⟨subd16_3_472, List.forall_mem_cons.2 ⟨subd16_3_473, List.forall_mem_cons.2 ⟨subd16_3_474, List.forall_mem_cons.2 ⟨subd16_3_475, List.forall_mem_cons.2 ⟨subd16_3_476, List.forall_mem_cons.2 ⟨subd16_3_477, List.forall_mem_cons.2 ⟨subd16_3_478, List.forall_mem_cons.2 ⟨subd16_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_480 : subd16_3 [1, -2, 9] = true := by decide +kernel
theorem subd16_3_481 : subd16_3 [1, -2, 10] = true := by decide +kernel
theorem subd16_3_482 : subd16_3 [1, -1, -11] = true := by decide +kernel
theorem subd16_3_483 : subd16_3 [1, -1, -10] = true := by decide +kernel
theorem subd16_3_484 : subd16_3 [1, -1, -9] = true := by decide +kernel
theorem subd16_3_485 : subd16_3 [1, -1, -8] = true := by decide +kernel
theorem subd16_3_486 : subd16_3 [1, -1, -7] = true := by decide +kernel
theorem subd16_3_487 : subd16_3 [1, -1, -6] = true := by decide +kernel
theorem subd16_3_488 : subd16_3 [1, -1, -5] = true := by decide +kernel
theorem subd16_3_489 : subd16_3 [1, -1, -4] = true := by decide +kernel
theorem subd16_3_490 : subd16_3 [1, -1, -3] = true := by decide +kernel
theorem subd16_3_491 : subd16_3 [1, -1, -2] = true := by decide +kernel
theorem subd16_3_492 : subd16_3 [1, -1, -1] = true := by decide +kernel
theorem subd16_3_493 : subd16_3 [1, -1, 0] = true := by decide +kernel
theorem subd16_3_494 : subd16_3 [1, -1, 1] = true := by decide +kernel
theorem subd16_3_495 : subd16_3 [1, -1, 2] = true := by decide +kernel
theorem subd16_3_496 : subd16_3 [1, -1, 3] = true := by decide +kernel
theorem subd16_3_497 : subd16_3 [1, -1, 4] = true := by decide +kernel
theorem subd16_3_498 : subd16_3 [1, -1, 5] = true := by decide +kernel
theorem subd16_3_499 : subd16_3 [1, -1, 6] = true := by decide +kernel
theorem subd16_3_500 : subd16_3 [1, -1, 7] = true := by decide +kernel
theorem subd16_3_501 : subd16_3 [1, -1, 8] = true := by decide +kernel
theorem subd16_3_502 : subd16_3 [1, -1, 9] = true := by decide +kernel
theorem subd16_3_503 : subd16_3 [1, -1, 10] = true := by decide +kernel
theorem subd16_3_504 : subd16_3 [1, -1, 11] = true := by decide +kernel
theorem subd16_3_505 : subd16_3 [1, 0, -12] = true := by decide +kernel
theorem subd16_3_506 : subd16_3 [1, 0, -11] = true := by decide +kernel
theorem subd16_3_507 : subd16_3 [1, 0, -10] = true := by decide +kernel
theorem subd16_3_508 : subd16_3 [1, 0, -9] = true := by decide +kernel
theorem subd16_3_509 : subd16_3 [1, 0, -8] = true := by decide +kernel
theorem subd16_3_510 : subd16_3 [1, 0, -7] = true := by decide +kernel
theorem subd16_3_511 : subd16_3 [1, 0, -6] = true := by decide +kernel
theorem sbd16_3_15 : ∀ q ∈ blkd16_3_15, subd16_3 q = true := by
  unfold blkd16_3_15
  exact List.forall_mem_cons.2 ⟨subd16_3_480, List.forall_mem_cons.2 ⟨subd16_3_481, List.forall_mem_cons.2 ⟨subd16_3_482, List.forall_mem_cons.2 ⟨subd16_3_483, List.forall_mem_cons.2 ⟨subd16_3_484, List.forall_mem_cons.2 ⟨subd16_3_485, List.forall_mem_cons.2 ⟨subd16_3_486, List.forall_mem_cons.2 ⟨subd16_3_487, List.forall_mem_cons.2 ⟨subd16_3_488, List.forall_mem_cons.2 ⟨subd16_3_489, List.forall_mem_cons.2 ⟨subd16_3_490, List.forall_mem_cons.2 ⟨subd16_3_491, List.forall_mem_cons.2 ⟨subd16_3_492, List.forall_mem_cons.2 ⟨subd16_3_493, List.forall_mem_cons.2 ⟨subd16_3_494, List.forall_mem_cons.2 ⟨subd16_3_495, List.forall_mem_cons.2 ⟨subd16_3_496, List.forall_mem_cons.2 ⟨subd16_3_497, List.forall_mem_cons.2 ⟨subd16_3_498, List.forall_mem_cons.2 ⟨subd16_3_499, List.forall_mem_cons.2 ⟨subd16_3_500, List.forall_mem_cons.2 ⟨subd16_3_501, List.forall_mem_cons.2 ⟨subd16_3_502, List.forall_mem_cons.2 ⟨subd16_3_503, List.forall_mem_cons.2 ⟨subd16_3_504, List.forall_mem_cons.2 ⟨subd16_3_505, List.forall_mem_cons.2 ⟨subd16_3_506, List.forall_mem_cons.2 ⟨subd16_3_507, List.forall_mem_cons.2 ⟨subd16_3_508, List.forall_mem_cons.2 ⟨subd16_3_509, List.forall_mem_cons.2 ⟨subd16_3_510, List.forall_mem_cons.2 ⟨subd16_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_512 : subd16_3 [1, 0, -5] = true := by decide +kernel
theorem subd16_3_513 : subd16_3 [1, 0, -4] = true := by decide +kernel
theorem subd16_3_514 : subd16_3 [1, 0, -3] = true := by decide +kernel
theorem subd16_3_515 : subd16_3 [1, 0, -2] = true := by decide +kernel
theorem subd16_3_516 : subd16_3 [1, 0, -1] = true := by decide +kernel
theorem subd16_3_517 : subd16_3 [1, 0, 0] = true := by decide +kernel
theorem subd16_3_518 : subd16_3 [1, 0, 1] = true := by decide +kernel
theorem subd16_3_519 : subd16_3 [1, 0, 2] = true := by decide +kernel
theorem subd16_3_520 : subd16_3 [1, 0, 3] = true := by decide +kernel
theorem subd16_3_521 : subd16_3 [1, 0, 4] = true := by decide +kernel
theorem subd16_3_522 : subd16_3 [1, 0, 5] = true := by decide +kernel
theorem subd16_3_523 : subd16_3 [1, 0, 6] = true := by decide +kernel
theorem subd16_3_524 : subd16_3 [1, 0, 7] = true := by decide +kernel
theorem subd16_3_525 : subd16_3 [1, 0, 8] = true := by decide +kernel
theorem subd16_3_526 : subd16_3 [1, 0, 9] = true := by decide +kernel
theorem subd16_3_527 : subd16_3 [1, 0, 10] = true := by decide +kernel
theorem subd16_3_528 : subd16_3 [1, 0, 11] = true := by decide +kernel
theorem subd16_3_529 : subd16_3 [1, 1, -12] = true := by decide +kernel
theorem subd16_3_530 : subd16_3 [1, 1, -11] = true := by decide +kernel
theorem subd16_3_531 : subd16_3 [1, 1, -10] = true := by decide +kernel
theorem subd16_3_532 : subd16_3 [1, 1, -9] = true := by decide +kernel
theorem subd16_3_533 : subd16_3 [1, 1, -8] = true := by decide +kernel
theorem subd16_3_534 : subd16_3 [1, 1, -7] = true := by decide +kernel
theorem subd16_3_535 : subd16_3 [1, 1, -6] = true := by decide +kernel
theorem subd16_3_536 : subd16_3 [1, 1, -5] = true := by decide +kernel
theorem subd16_3_537 : subd16_3 [1, 1, -4] = true := by decide +kernel
theorem subd16_3_538 : subd16_3 [1, 1, -3] = true := by decide +kernel
theorem subd16_3_539 : subd16_3 [1, 1, -2] = true := by decide +kernel
theorem subd16_3_540 : subd16_3 [1, 1, -1] = true := by decide +kernel
theorem subd16_3_541 : subd16_3 [1, 1, 0] = true := by decide +kernel
theorem subd16_3_542 : subd16_3 [1, 1, 1] = true := by decide +kernel
theorem subd16_3_543 : subd16_3 [1, 1, 2] = true := by decide +kernel
theorem sbd16_3_16 : ∀ q ∈ blkd16_3_16, subd16_3 q = true := by
  unfold blkd16_3_16
  exact List.forall_mem_cons.2 ⟨subd16_3_512, List.forall_mem_cons.2 ⟨subd16_3_513, List.forall_mem_cons.2 ⟨subd16_3_514, List.forall_mem_cons.2 ⟨subd16_3_515, List.forall_mem_cons.2 ⟨subd16_3_516, List.forall_mem_cons.2 ⟨subd16_3_517, List.forall_mem_cons.2 ⟨subd16_3_518, List.forall_mem_cons.2 ⟨subd16_3_519, List.forall_mem_cons.2 ⟨subd16_3_520, List.forall_mem_cons.2 ⟨subd16_3_521, List.forall_mem_cons.2 ⟨subd16_3_522, List.forall_mem_cons.2 ⟨subd16_3_523, List.forall_mem_cons.2 ⟨subd16_3_524, List.forall_mem_cons.2 ⟨subd16_3_525, List.forall_mem_cons.2 ⟨subd16_3_526, List.forall_mem_cons.2 ⟨subd16_3_527, List.forall_mem_cons.2 ⟨subd16_3_528, List.forall_mem_cons.2 ⟨subd16_3_529, List.forall_mem_cons.2 ⟨subd16_3_530, List.forall_mem_cons.2 ⟨subd16_3_531, List.forall_mem_cons.2 ⟨subd16_3_532, List.forall_mem_cons.2 ⟨subd16_3_533, List.forall_mem_cons.2 ⟨subd16_3_534, List.forall_mem_cons.2 ⟨subd16_3_535, List.forall_mem_cons.2 ⟨subd16_3_536, List.forall_mem_cons.2 ⟨subd16_3_537, List.forall_mem_cons.2 ⟨subd16_3_538, List.forall_mem_cons.2 ⟨subd16_3_539, List.forall_mem_cons.2 ⟨subd16_3_540, List.forall_mem_cons.2 ⟨subd16_3_541, List.forall_mem_cons.2 ⟨subd16_3_542, List.forall_mem_cons.2 ⟨subd16_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_544 : subd16_3 [1, 1, 3] = true := by decide +kernel
theorem subd16_3_545 : subd16_3 [1, 1, 4] = true := by decide +kernel
theorem subd16_3_546 : subd16_3 [1, 1, 5] = true := by decide +kernel
theorem subd16_3_547 : subd16_3 [1, 1, 6] = true := by decide +kernel
theorem subd16_3_548 : subd16_3 [1, 1, 7] = true := by decide +kernel
theorem subd16_3_549 : subd16_3 [1, 1, 8] = true := by decide +kernel
theorem subd16_3_550 : subd16_3 [1, 1, 9] = true := by decide +kernel
theorem subd16_3_551 : subd16_3 [1, 1, 10] = true := by decide +kernel
theorem subd16_3_552 : subd16_3 [1, 2, -12] = true := by decide +kernel
theorem subd16_3_553 : subd16_3 [1, 2, -11] = true := by decide +kernel
theorem subd16_3_554 : subd16_3 [1, 2, -10] = true := by decide +kernel
theorem subd16_3_555 : subd16_3 [1, 2, -9] = true := by decide +kernel
theorem subd16_3_556 : subd16_3 [1, 2, -8] = true := by decide +kernel
theorem subd16_3_557 : subd16_3 [1, 2, -7] = true := by decide +kernel
theorem subd16_3_558 : subd16_3 [1, 2, -6] = true := by decide +kernel
theorem subd16_3_559 : subd16_3 [1, 2, -5] = true := by decide +kernel
theorem subd16_3_560 : subd16_3 [1, 2, -4] = true := by decide +kernel
theorem subd16_3_561 : subd16_3 [1, 2, -3] = true := by decide +kernel
theorem subd16_3_562 : subd16_3 [1, 2, -2] = true := by decide +kernel
theorem subd16_3_563 : subd16_3 [1, 2, -1] = true := by decide +kernel
theorem subd16_3_564 : subd16_3 [1, 2, 0] = true := by decide +kernel
theorem subd16_3_565 : subd16_3 [1, 2, 1] = true := by decide +kernel
theorem subd16_3_566 : subd16_3 [1, 2, 2] = true := by decide +kernel
theorem subd16_3_567 : subd16_3 [1, 2, 3] = true := by decide +kernel
theorem subd16_3_568 : subd16_3 [1, 2, 4] = true := by decide +kernel
theorem subd16_3_569 : subd16_3 [1, 2, 5] = true := by decide +kernel
theorem subd16_3_570 : subd16_3 [1, 2, 6] = true := by decide +kernel
theorem subd16_3_571 : subd16_3 [1, 2, 7] = true := by decide +kernel
theorem subd16_3_572 : subd16_3 [1, 2, 8] = true := by decide +kernel
theorem subd16_3_573 : subd16_3 [1, 3, -9] = true := by decide +kernel
theorem subd16_3_574 : subd16_3 [1, 3, -8] = true := by decide +kernel
theorem subd16_3_575 : subd16_3 [1, 3, -7] = true := by decide +kernel
theorem sbd16_3_17 : ∀ q ∈ blkd16_3_17, subd16_3 q = true := by
  unfold blkd16_3_17
  exact List.forall_mem_cons.2 ⟨subd16_3_544, List.forall_mem_cons.2 ⟨subd16_3_545, List.forall_mem_cons.2 ⟨subd16_3_546, List.forall_mem_cons.2 ⟨subd16_3_547, List.forall_mem_cons.2 ⟨subd16_3_548, List.forall_mem_cons.2 ⟨subd16_3_549, List.forall_mem_cons.2 ⟨subd16_3_550, List.forall_mem_cons.2 ⟨subd16_3_551, List.forall_mem_cons.2 ⟨subd16_3_552, List.forall_mem_cons.2 ⟨subd16_3_553, List.forall_mem_cons.2 ⟨subd16_3_554, List.forall_mem_cons.2 ⟨subd16_3_555, List.forall_mem_cons.2 ⟨subd16_3_556, List.forall_mem_cons.2 ⟨subd16_3_557, List.forall_mem_cons.2 ⟨subd16_3_558, List.forall_mem_cons.2 ⟨subd16_3_559, List.forall_mem_cons.2 ⟨subd16_3_560, List.forall_mem_cons.2 ⟨subd16_3_561, List.forall_mem_cons.2 ⟨subd16_3_562, List.forall_mem_cons.2 ⟨subd16_3_563, List.forall_mem_cons.2 ⟨subd16_3_564, List.forall_mem_cons.2 ⟨subd16_3_565, List.forall_mem_cons.2 ⟨subd16_3_566, List.forall_mem_cons.2 ⟨subd16_3_567, List.forall_mem_cons.2 ⟨subd16_3_568, List.forall_mem_cons.2 ⟨subd16_3_569, List.forall_mem_cons.2 ⟨subd16_3_570, List.forall_mem_cons.2 ⟨subd16_3_571, List.forall_mem_cons.2 ⟨subd16_3_572, List.forall_mem_cons.2 ⟨subd16_3_573, List.forall_mem_cons.2 ⟨subd16_3_574, List.forall_mem_cons.2 ⟨subd16_3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_576 : subd16_3 [1, 3, -6] = true := by decide +kernel
theorem subd16_3_577 : subd16_3 [1, 3, -5] = true := by decide +kernel
theorem subd16_3_578 : subd16_3 [1, 3, -4] = true := by decide +kernel
theorem subd16_3_579 : subd16_3 [1, 3, -3] = true := by decide +kernel
theorem subd16_3_580 : subd16_3 [1, 3, -2] = true := by decide +kernel
theorem subd16_3_581 : subd16_3 [1, 3, -1] = true := by decide +kernel
theorem subd16_3_582 : subd16_3 [1, 3, 0] = true := by decide +kernel
theorem subd16_3_583 : subd16_3 [1, 3, 1] = true := by decide +kernel
theorem subd16_3_584 : subd16_3 [1, 3, 2] = true := by decide +kernel
theorem subd16_3_585 : subd16_3 [1, 3, 3] = true := by decide +kernel
theorem subd16_3_586 : subd16_3 [1, 3, 4] = true := by decide +kernel
theorem subd16_3_587 : subd16_3 [1, 3, 5] = true := by decide +kernel
theorem subd16_3_588 : subd16_3 [2, -4] = true := by decide +kernel
theorem subd16_3_589 : subd16_3 [2, -3] = true := by decide +kernel
theorem subd16_3_590 : subd16_3 [2, -2, -8] = true := by decide +kernel
theorem subd16_3_591 : subd16_3 [2, -2, -7] = true := by decide +kernel
theorem subd16_3_592 : subd16_3 [2, -2, -6] = true := by decide +kernel
theorem subd16_3_593 : subd16_3 [2, -2, -5] = true := by decide +kernel
theorem subd16_3_594 : subd16_3 [2, -2, -4] = true := by decide +kernel
theorem subd16_3_595 : subd16_3 [2, -2, -3] = true := by decide +kernel
theorem subd16_3_596 : subd16_3 [2, -2, -2] = true := by decide +kernel
theorem subd16_3_597 : subd16_3 [2, -2, -1] = true := by decide +kernel
theorem subd16_3_598 : subd16_3 [2, -2, 0] = true := by decide +kernel
theorem subd16_3_599 : subd16_3 [2, -2, 1] = true := by decide +kernel
theorem subd16_3_600 : subd16_3 [2, -2, 2] = true := by decide +kernel
theorem subd16_3_601 : subd16_3 [2, -2, 3] = true := by decide +kernel
theorem subd16_3_602 : subd16_3 [2, -2, 4] = true := by decide +kernel
theorem subd16_3_603 : subd16_3 [2, -2, 5] = true := by decide +kernel
theorem subd16_3_604 : subd16_3 [2, -2, 6] = true := by decide +kernel
theorem subd16_3_605 : subd16_3 [2, -2, 7] = true := by decide +kernel
theorem subd16_3_606 : subd16_3 [2, -2, 8] = true := by decide +kernel
theorem subd16_3_607 : subd16_3 [2, -1, -10] = true := by decide +kernel
theorem sbd16_3_18 : ∀ q ∈ blkd16_3_18, subd16_3 q = true := by
  unfold blkd16_3_18
  exact List.forall_mem_cons.2 ⟨subd16_3_576, List.forall_mem_cons.2 ⟨subd16_3_577, List.forall_mem_cons.2 ⟨subd16_3_578, List.forall_mem_cons.2 ⟨subd16_3_579, List.forall_mem_cons.2 ⟨subd16_3_580, List.forall_mem_cons.2 ⟨subd16_3_581, List.forall_mem_cons.2 ⟨subd16_3_582, List.forall_mem_cons.2 ⟨subd16_3_583, List.forall_mem_cons.2 ⟨subd16_3_584, List.forall_mem_cons.2 ⟨subd16_3_585, List.forall_mem_cons.2 ⟨subd16_3_586, List.forall_mem_cons.2 ⟨subd16_3_587, List.forall_mem_cons.2 ⟨subd16_3_588, List.forall_mem_cons.2 ⟨subd16_3_589, List.forall_mem_cons.2 ⟨subd16_3_590, List.forall_mem_cons.2 ⟨subd16_3_591, List.forall_mem_cons.2 ⟨subd16_3_592, List.forall_mem_cons.2 ⟨subd16_3_593, List.forall_mem_cons.2 ⟨subd16_3_594, List.forall_mem_cons.2 ⟨subd16_3_595, List.forall_mem_cons.2 ⟨subd16_3_596, List.forall_mem_cons.2 ⟨subd16_3_597, List.forall_mem_cons.2 ⟨subd16_3_598, List.forall_mem_cons.2 ⟨subd16_3_599, List.forall_mem_cons.2 ⟨subd16_3_600, List.forall_mem_cons.2 ⟨subd16_3_601, List.forall_mem_cons.2 ⟨subd16_3_602, List.forall_mem_cons.2 ⟨subd16_3_603, List.forall_mem_cons.2 ⟨subd16_3_604, List.forall_mem_cons.2 ⟨subd16_3_605, List.forall_mem_cons.2 ⟨subd16_3_606, List.forall_mem_cons.2 ⟨subd16_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_608 : subd16_3 [2, -1, -9] = true := by decide +kernel
theorem subd16_3_609 : subd16_3 [2, -1, -8] = true := by decide +kernel
theorem subd16_3_610 : subd16_3 [2, -1, -7] = true := by decide +kernel
theorem subd16_3_611 : subd16_3 [2, -1, -6] = true := by decide +kernel
theorem subd16_3_612 : subd16_3 [2, -1, -5] = true := by decide +kernel
theorem subd16_3_613 : subd16_3 [2, -1, -4] = true := by decide +kernel
theorem subd16_3_614 : subd16_3 [2, -1, -3] = true := by decide +kernel
theorem subd16_3_615 : subd16_3 [2, -1, -2] = true := by decide +kernel
theorem subd16_3_616 : subd16_3 [2, -1, -1] = true := by decide +kernel
theorem subd16_3_617 : subd16_3 [2, -1, 0] = true := by decide +kernel
theorem subd16_3_618 : subd16_3 [2, -1, 1] = true := by decide +kernel
theorem subd16_3_619 : subd16_3 [2, -1, 2] = true := by decide +kernel
theorem subd16_3_620 : subd16_3 [2, -1, 3] = true := by decide +kernel
theorem subd16_3_621 : subd16_3 [2, -1, 4] = true := by decide +kernel
theorem subd16_3_622 : subd16_3 [2, -1, 5] = true := by decide +kernel
theorem subd16_3_623 : subd16_3 [2, -1, 6] = true := by decide +kernel
theorem subd16_3_624 : subd16_3 [2, -1, 7] = true := by decide +kernel
theorem subd16_3_625 : subd16_3 [2, -1, 8] = true := by decide +kernel
theorem subd16_3_626 : subd16_3 [2, -1, 9] = true := by decide +kernel
theorem subd16_3_627 : subd16_3 [2, 0, -11] = true := by decide +kernel
theorem subd16_3_628 : subd16_3 [2, 0, -10] = true := by decide +kernel
theorem subd16_3_629 : subd16_3 [2, 0, -9] = true := by decide +kernel
theorem subd16_3_630 : subd16_3 [2, 0, -8] = true := by decide +kernel
theorem subd16_3_631 : subd16_3 [2, 0, -7] = true := by decide +kernel
theorem subd16_3_632 : subd16_3 [2, 0, -6] = true := by decide +kernel
theorem subd16_3_633 : subd16_3 [2, 0, -5] = true := by decide +kernel
theorem subd16_3_634 : subd16_3 [2, 0, -4] = true := by decide +kernel
theorem subd16_3_635 : subd16_3 [2, 0, -3] = true := by decide +kernel
theorem subd16_3_636 : subd16_3 [2, 0, -2] = true := by decide +kernel
theorem subd16_3_637 : subd16_3 [2, 0, -1] = true := by decide +kernel
theorem subd16_3_638 : subd16_3 [2, 0, 0] = true := by decide +kernel
theorem subd16_3_639 : subd16_3 [2, 0, 1] = true := by decide +kernel
theorem sbd16_3_19 : ∀ q ∈ blkd16_3_19, subd16_3 q = true := by
  unfold blkd16_3_19
  exact List.forall_mem_cons.2 ⟨subd16_3_608, List.forall_mem_cons.2 ⟨subd16_3_609, List.forall_mem_cons.2 ⟨subd16_3_610, List.forall_mem_cons.2 ⟨subd16_3_611, List.forall_mem_cons.2 ⟨subd16_3_612, List.forall_mem_cons.2 ⟨subd16_3_613, List.forall_mem_cons.2 ⟨subd16_3_614, List.forall_mem_cons.2 ⟨subd16_3_615, List.forall_mem_cons.2 ⟨subd16_3_616, List.forall_mem_cons.2 ⟨subd16_3_617, List.forall_mem_cons.2 ⟨subd16_3_618, List.forall_mem_cons.2 ⟨subd16_3_619, List.forall_mem_cons.2 ⟨subd16_3_620, List.forall_mem_cons.2 ⟨subd16_3_621, List.forall_mem_cons.2 ⟨subd16_3_622, List.forall_mem_cons.2 ⟨subd16_3_623, List.forall_mem_cons.2 ⟨subd16_3_624, List.forall_mem_cons.2 ⟨subd16_3_625, List.forall_mem_cons.2 ⟨subd16_3_626, List.forall_mem_cons.2 ⟨subd16_3_627, List.forall_mem_cons.2 ⟨subd16_3_628, List.forall_mem_cons.2 ⟨subd16_3_629, List.forall_mem_cons.2 ⟨subd16_3_630, List.forall_mem_cons.2 ⟨subd16_3_631, List.forall_mem_cons.2 ⟨subd16_3_632, List.forall_mem_cons.2 ⟨subd16_3_633, List.forall_mem_cons.2 ⟨subd16_3_634, List.forall_mem_cons.2 ⟨subd16_3_635, List.forall_mem_cons.2 ⟨subd16_3_636, List.forall_mem_cons.2 ⟨subd16_3_637, List.forall_mem_cons.2 ⟨subd16_3_638, List.forall_mem_cons.2 ⟨subd16_3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_640 : subd16_3 [2, 0, 2] = true := by decide +kernel
theorem subd16_3_641 : subd16_3 [2, 0, 3] = true := by decide +kernel
theorem subd16_3_642 : subd16_3 [2, 0, 4] = true := by decide +kernel
theorem subd16_3_643 : subd16_3 [2, 0, 5] = true := by decide +kernel
theorem subd16_3_644 : subd16_3 [2, 0, 6] = true := by decide +kernel
theorem subd16_3_645 : subd16_3 [2, 0, 7] = true := by decide +kernel
theorem subd16_3_646 : subd16_3 [2, 0, 8] = true := by decide +kernel
theorem subd16_3_647 : subd16_3 [2, 0, 9] = true := by decide +kernel
theorem subd16_3_648 : subd16_3 [2, 1, -11] = true := by decide +kernel
theorem subd16_3_649 : subd16_3 [2, 1, -10] = true := by decide +kernel
theorem subd16_3_650 : subd16_3 [2, 1, -9] = true := by decide +kernel
theorem subd16_3_651 : subd16_3 [2, 1, -8] = true := by decide +kernel
theorem subd16_3_652 : subd16_3 [2, 1, -7] = true := by decide +kernel
theorem subd16_3_653 : subd16_3 [2, 1, -6] = true := by decide +kernel
theorem subd16_3_654 : subd16_3 [2, 1, -5] = true := by decide +kernel
theorem subd16_3_655 : subd16_3 [2, 1, -4] = true := by decide +kernel
theorem subd16_3_656 : subd16_3 [2, 1, -3] = true := by decide +kernel
theorem subd16_3_657 : subd16_3 [2, 1, -2] = true := by decide +kernel
theorem subd16_3_658 : subd16_3 [2, 1, -1] = true := by decide +kernel
theorem subd16_3_659 : subd16_3 [2, 1, 0] = true := by decide +kernel
theorem subd16_3_660 : subd16_3 [2, 1, 1] = true := by decide +kernel
theorem subd16_3_661 : subd16_3 [2, 1, 2] = true := by decide +kernel
theorem subd16_3_662 : subd16_3 [2, 1, 3] = true := by decide +kernel
theorem subd16_3_663 : subd16_3 [2, 1, 4] = true := by decide +kernel
theorem subd16_3_664 : subd16_3 [2, 1, 5] = true := by decide +kernel
theorem subd16_3_665 : subd16_3 [2, 1, 6] = true := by decide +kernel
theorem subd16_3_666 : subd16_3 [2, 1, 7] = true := by decide +kernel
theorem subd16_3_667 : subd16_3 [2, 1, 8] = true := by decide +kernel
theorem subd16_3_668 : subd16_3 [2, 2, -10] = true := by decide +kernel
theorem subd16_3_669 : subd16_3 [2, 2, -9] = true := by decide +kernel
theorem subd16_3_670 : subd16_3 [2, 2, -8] = true := by decide +kernel
theorem subd16_3_671 : subd16_3 [2, 2, -7] = true := by decide +kernel
theorem sbd16_3_20 : ∀ q ∈ blkd16_3_20, subd16_3 q = true := by
  unfold blkd16_3_20
  exact List.forall_mem_cons.2 ⟨subd16_3_640, List.forall_mem_cons.2 ⟨subd16_3_641, List.forall_mem_cons.2 ⟨subd16_3_642, List.forall_mem_cons.2 ⟨subd16_3_643, List.forall_mem_cons.2 ⟨subd16_3_644, List.forall_mem_cons.2 ⟨subd16_3_645, List.forall_mem_cons.2 ⟨subd16_3_646, List.forall_mem_cons.2 ⟨subd16_3_647, List.forall_mem_cons.2 ⟨subd16_3_648, List.forall_mem_cons.2 ⟨subd16_3_649, List.forall_mem_cons.2 ⟨subd16_3_650, List.forall_mem_cons.2 ⟨subd16_3_651, List.forall_mem_cons.2 ⟨subd16_3_652, List.forall_mem_cons.2 ⟨subd16_3_653, List.forall_mem_cons.2 ⟨subd16_3_654, List.forall_mem_cons.2 ⟨subd16_3_655, List.forall_mem_cons.2 ⟨subd16_3_656, List.forall_mem_cons.2 ⟨subd16_3_657, List.forall_mem_cons.2 ⟨subd16_3_658, List.forall_mem_cons.2 ⟨subd16_3_659, List.forall_mem_cons.2 ⟨subd16_3_660, List.forall_mem_cons.2 ⟨subd16_3_661, List.forall_mem_cons.2 ⟨subd16_3_662, List.forall_mem_cons.2 ⟨subd16_3_663, List.forall_mem_cons.2 ⟨subd16_3_664, List.forall_mem_cons.2 ⟨subd16_3_665, List.forall_mem_cons.2 ⟨subd16_3_666, List.forall_mem_cons.2 ⟨subd16_3_667, List.forall_mem_cons.2 ⟨subd16_3_668, List.forall_mem_cons.2 ⟨subd16_3_669, List.forall_mem_cons.2 ⟨subd16_3_670, List.forall_mem_cons.2 ⟨subd16_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_672 : subd16_3 [2, 2, -6] = true := by decide +kernel
theorem subd16_3_673 : subd16_3 [2, 2, -5] = true := by decide +kernel
theorem subd16_3_674 : subd16_3 [2, 2, -4] = true := by decide +kernel
theorem subd16_3_675 : subd16_3 [2, 2, -3] = true := by decide +kernel
theorem subd16_3_676 : subd16_3 [2, 2, -2] = true := by decide +kernel
theorem subd16_3_677 : subd16_3 [2, 2, -1] = true := by decide +kernel
theorem subd16_3_678 : subd16_3 [2, 2, 0] = true := by decide +kernel
theorem subd16_3_679 : subd16_3 [2, 2, 1] = true := by decide +kernel
theorem subd16_3_680 : subd16_3 [2, 2, 2] = true := by decide +kernel
theorem subd16_3_681 : subd16_3 [2, 2, 3] = true := by decide +kernel
theorem subd16_3_682 : subd16_3 [2, 2, 4] = true := by decide +kernel
theorem subd16_3_683 : subd16_3 [2, 2, 5] = true := by decide +kernel
theorem subd16_3_684 : subd16_3 [2, 2, 6] = true := by decide +kernel
theorem subd16_3_685 : subd16_3 [2, 3] = true := by decide +kernel
theorem subd16_3_686 : subd16_3 [3, -3] = true := by decide +kernel
theorem subd16_3_687 : subd16_3 [3, -2] = true := by decide +kernel
theorem subd16_3_688 : subd16_3 [3, -1, -8] = true := by decide +kernel
theorem subd16_3_689 : subd16_3 [3, -1, -7] = true := by decide +kernel
theorem subd16_3_690 : subd16_3 [3, -1, -6] = true := by decide +kernel
theorem subd16_3_691 : subd16_3 [3, -1, -5] = true := by decide +kernel
theorem subd16_3_692 : subd16_3 [3, -1, -4] = true := by decide +kernel
theorem subd16_3_693 : subd16_3 [3, -1, -3] = true := by decide +kernel
theorem subd16_3_694 : subd16_3 [3, -1, -2] = true := by decide +kernel
theorem subd16_3_695 : subd16_3 [3, -1, -1] = true := by decide +kernel
theorem subd16_3_696 : subd16_3 [3, -1, 0] = true := by decide +kernel
theorem subd16_3_697 : subd16_3 [3, -1, 1] = true := by decide +kernel
theorem subd16_3_698 : subd16_3 [3, -1, 2] = true := by decide +kernel
theorem subd16_3_699 : subd16_3 [3, -1, 3] = true := by decide +kernel
theorem subd16_3_700 : subd16_3 [3, -1, 4] = true := by decide +kernel
theorem subd16_3_701 : subd16_3 [3, -1, 5] = true := by decide +kernel
theorem subd16_3_702 : subd16_3 [3, -1, 6] = true := by decide +kernel
theorem subd16_3_703 : subd16_3 [3, 0, -9] = true := by decide +kernel
theorem sbd16_3_21 : ∀ q ∈ blkd16_3_21, subd16_3 q = true := by
  unfold blkd16_3_21
  exact List.forall_mem_cons.2 ⟨subd16_3_672, List.forall_mem_cons.2 ⟨subd16_3_673, List.forall_mem_cons.2 ⟨subd16_3_674, List.forall_mem_cons.2 ⟨subd16_3_675, List.forall_mem_cons.2 ⟨subd16_3_676, List.forall_mem_cons.2 ⟨subd16_3_677, List.forall_mem_cons.2 ⟨subd16_3_678, List.forall_mem_cons.2 ⟨subd16_3_679, List.forall_mem_cons.2 ⟨subd16_3_680, List.forall_mem_cons.2 ⟨subd16_3_681, List.forall_mem_cons.2 ⟨subd16_3_682, List.forall_mem_cons.2 ⟨subd16_3_683, List.forall_mem_cons.2 ⟨subd16_3_684, List.forall_mem_cons.2 ⟨subd16_3_685, List.forall_mem_cons.2 ⟨subd16_3_686, List.forall_mem_cons.2 ⟨subd16_3_687, List.forall_mem_cons.2 ⟨subd16_3_688, List.forall_mem_cons.2 ⟨subd16_3_689, List.forall_mem_cons.2 ⟨subd16_3_690, List.forall_mem_cons.2 ⟨subd16_3_691, List.forall_mem_cons.2 ⟨subd16_3_692, List.forall_mem_cons.2 ⟨subd16_3_693, List.forall_mem_cons.2 ⟨subd16_3_694, List.forall_mem_cons.2 ⟨subd16_3_695, List.forall_mem_cons.2 ⟨subd16_3_696, List.forall_mem_cons.2 ⟨subd16_3_697, List.forall_mem_cons.2 ⟨subd16_3_698, List.forall_mem_cons.2 ⟨subd16_3_699, List.forall_mem_cons.2 ⟨subd16_3_700, List.forall_mem_cons.2 ⟨subd16_3_701, List.forall_mem_cons.2 ⟨subd16_3_702, List.forall_mem_cons.2 ⟨subd16_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_704 : subd16_3 [3, 0, -8] = true := by decide +kernel
theorem subd16_3_705 : subd16_3 [3, 0, -7] = true := by decide +kernel
theorem subd16_3_706 : subd16_3 [3, 0, -6] = true := by decide +kernel
theorem subd16_3_707 : subd16_3 [3, 0, -5] = true := by decide +kernel
theorem subd16_3_708 : subd16_3 [3, 0, -4] = true := by decide +kernel
theorem subd16_3_709 : subd16_3 [3, 0, -3] = true := by decide +kernel
theorem subd16_3_710 : subd16_3 [3, 0, -2] = true := by decide +kernel
theorem subd16_3_711 : subd16_3 [3, 0, -1] = true := by decide +kernel
theorem subd16_3_712 : subd16_3 [3, 0, 0] = true := by decide +kernel
theorem subd16_3_713 : subd16_3 [3, 0, 1] = true := by decide +kernel
theorem subd16_3_714 : subd16_3 [3, 0, 2] = true := by decide +kernel
theorem subd16_3_715 : subd16_3 [3, 0, 3] = true := by decide +kernel
theorem subd16_3_716 : subd16_3 [3, 0, 4] = true := by decide +kernel
theorem subd16_3_717 : subd16_3 [3, 0, 5] = true := by decide +kernel
theorem subd16_3_718 : subd16_3 [3, 0, 6] = true := by decide +kernel
theorem subd16_3_719 : subd16_3 [3, 1, -9] = true := by decide +kernel
theorem subd16_3_720 : subd16_3 [3, 1, -8] = true := by decide +kernel
theorem subd16_3_721 : subd16_3 [3, 1, -7] = true := by decide +kernel
theorem subd16_3_722 : subd16_3 [3, 1, -6] = true := by decide +kernel
theorem subd16_3_723 : subd16_3 [3, 1, -5] = true := by decide +kernel
theorem subd16_3_724 : subd16_3 [3, 1, -4] = true := by decide +kernel
theorem subd16_3_725 : subd16_3 [3, 1, -3] = true := by decide +kernel
theorem subd16_3_726 : subd16_3 [3, 1, -2] = true := by decide +kernel
theorem subd16_3_727 : subd16_3 [3, 1, -1] = true := by decide +kernel
theorem subd16_3_728 : subd16_3 [3, 1, 0] = true := by decide +kernel
theorem subd16_3_729 : subd16_3 [3, 1, 1] = true := by decide +kernel
theorem subd16_3_730 : subd16_3 [3, 1, 2] = true := by decide +kernel
theorem subd16_3_731 : subd16_3 [3, 1, 3] = true := by decide +kernel
theorem subd16_3_732 : subd16_3 [3, 1, 4] = true := by decide +kernel
theorem subd16_3_733 : subd16_3 [3, 1, 5] = true := by decide +kernel
theorem subd16_3_734 : subd16_3 [3, 2] = true := by decide +kernel
theorem sbd16_3_22 : ∀ q ∈ blkd16_3_22, subd16_3 q = true := by
  unfold blkd16_3_22
  exact List.forall_mem_cons.2 ⟨subd16_3_704, List.forall_mem_cons.2 ⟨subd16_3_705, List.forall_mem_cons.2 ⟨subd16_3_706, List.forall_mem_cons.2 ⟨subd16_3_707, List.forall_mem_cons.2 ⟨subd16_3_708, List.forall_mem_cons.2 ⟨subd16_3_709, List.forall_mem_cons.2 ⟨subd16_3_710, List.forall_mem_cons.2 ⟨subd16_3_711, List.forall_mem_cons.2 ⟨subd16_3_712, List.forall_mem_cons.2 ⟨subd16_3_713, List.forall_mem_cons.2 ⟨subd16_3_714, List.forall_mem_cons.2 ⟨subd16_3_715, List.forall_mem_cons.2 ⟨subd16_3_716, List.forall_mem_cons.2 ⟨subd16_3_717, List.forall_mem_cons.2 ⟨subd16_3_718, List.forall_mem_cons.2 ⟨subd16_3_719, List.forall_mem_cons.2 ⟨subd16_3_720, List.forall_mem_cons.2 ⟨subd16_3_721, List.forall_mem_cons.2 ⟨subd16_3_722, List.forall_mem_cons.2 ⟨subd16_3_723, List.forall_mem_cons.2 ⟨subd16_3_724, List.forall_mem_cons.2 ⟨subd16_3_725, List.forall_mem_cons.2 ⟨subd16_3_726, List.forall_mem_cons.2 ⟨subd16_3_727, List.forall_mem_cons.2 ⟨subd16_3_728, List.forall_mem_cons.2 ⟨subd16_3_729, List.forall_mem_cons.2 ⟨subd16_3_730, List.forall_mem_cons.2 ⟨subd16_3_731, List.forall_mem_cons.2 ⟨subd16_3_732, List.forall_mem_cons.2 ⟨subd16_3_733, List.forall_mem_cons.2 ⟨subd16_3_734, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd17_0 : ldCheck G d17_0.U d17_0.ms ldd17_0 = true := by decide +kernel
theorem pre_okd17_0 : subPre G cell17 d17_0 = true := by decide +kernel
theorem subd17_0_0 : subd17_0 [-3] = true := by decide +kernel
theorem subd17_0_1 : subd17_0 [-2, -4] = true := by decide +kernel
theorem subd17_0_2 : subd17_0 [-2, -3] = true := by decide +kernel
theorem subd17_0_3 : subd17_0 [-2, -2, -11] = true := by decide +kernel
theorem subd17_0_4 : subd17_0 [-2, -2, -10] = true := by decide +kernel
theorem subd17_0_5 : subd17_0 [-2, -2, -9] = true := by decide +kernel
theorem subd17_0_6 : subd17_0 [-2, -2, -8] = true := by decide +kernel
theorem subd17_0_7 : subd17_0 [-2, -2, -7] = true := by decide +kernel
theorem subd17_0_8 : subd17_0 [-2, -2, -6] = true := by decide +kernel
theorem subd17_0_9 : subd17_0 [-2, -2, -5] = true := by decide +kernel
theorem subd17_0_10 : subd17_0 [-2, -2, -4] = true := by decide +kernel
theorem subd17_0_11 : subd17_0 [-2, -2, -3] = true := by decide +kernel
theorem subd17_0_12 : subd17_0 [-2, -2, -2] = true := by decide +kernel
theorem subd17_0_13 : subd17_0 [-2, -2, -1] = true := by decide +kernel
theorem subd17_0_14 : subd17_0 [-2, -2, 0] = true := by decide +kernel
theorem subd17_0_15 : subd17_0 [-2, -2, 1] = true := by decide +kernel
theorem subd17_0_16 : subd17_0 [-2, -2, 2] = true := by decide +kernel
theorem subd17_0_17 : subd17_0 [-2, -2, 3] = true := by decide +kernel
theorem subd17_0_18 : subd17_0 [-2, -2, 4] = true := by decide +kernel
theorem subd17_0_19 : subd17_0 [-2, -2, 5] = true := by decide +kernel
theorem subd17_0_20 : subd17_0 [-2, -2, 6] = true := by decide +kernel
theorem subd17_0_21 : subd17_0 [-2, -2, 7] = true := by decide +kernel
theorem subd17_0_22 : subd17_0 [-2, -2, 8] = true := by decide +kernel
theorem subd17_0_23 : subd17_0 [-2, -2, 9] = true := by decide +kernel
theorem subd17_0_24 : subd17_0 [-2, -1, -13] = true := by decide +kernel
theorem subd17_0_25 : subd17_0 [-2, -1, -12] = true := by decide +kernel
theorem subd17_0_26 : subd17_0 [-2, -1, -11] = true := by decide +kernel
theorem subd17_0_27 : subd17_0 [-2, -1, -10] = true := by decide +kernel
theorem subd17_0_28 : subd17_0 [-2, -1, -9] = true := by decide +kernel
theorem subd17_0_29 : subd17_0 [-2, -1, -8] = true := by decide +kernel
theorem subd17_0_30 : subd17_0 [-2, -1, -7] = true := by decide +kernel
theorem subd17_0_31 : subd17_0 [-2, -1, -6] = true := by decide +kernel
theorem sbd17_0_0 : ∀ q ∈ blkd17_0_0, subd17_0 q = true := by
  unfold blkd17_0_0
  exact List.forall_mem_cons.2 ⟨subd17_0_0, List.forall_mem_cons.2 ⟨subd17_0_1, List.forall_mem_cons.2 ⟨subd17_0_2, List.forall_mem_cons.2 ⟨subd17_0_3, List.forall_mem_cons.2 ⟨subd17_0_4, List.forall_mem_cons.2 ⟨subd17_0_5, List.forall_mem_cons.2 ⟨subd17_0_6, List.forall_mem_cons.2 ⟨subd17_0_7, List.forall_mem_cons.2 ⟨subd17_0_8, List.forall_mem_cons.2 ⟨subd17_0_9, List.forall_mem_cons.2 ⟨subd17_0_10, List.forall_mem_cons.2 ⟨subd17_0_11, List.forall_mem_cons.2 ⟨subd17_0_12, List.forall_mem_cons.2 ⟨subd17_0_13, List.forall_mem_cons.2 ⟨subd17_0_14, List.forall_mem_cons.2 ⟨subd17_0_15, List.forall_mem_cons.2 ⟨subd17_0_16, List.forall_mem_cons.2 ⟨subd17_0_17, List.forall_mem_cons.2 ⟨subd17_0_18, List.forall_mem_cons.2 ⟨subd17_0_19, List.forall_mem_cons.2 ⟨subd17_0_20, List.forall_mem_cons.2 ⟨subd17_0_21, List.forall_mem_cons.2 ⟨subd17_0_22, List.forall_mem_cons.2 ⟨subd17_0_23, List.forall_mem_cons.2 ⟨subd17_0_24, List.forall_mem_cons.2 ⟨subd17_0_25, List.forall_mem_cons.2 ⟨subd17_0_26, List.forall_mem_cons.2 ⟨subd17_0_27, List.forall_mem_cons.2 ⟨subd17_0_28, List.forall_mem_cons.2 ⟨subd17_0_29, List.forall_mem_cons.2 ⟨subd17_0_30, List.forall_mem_cons.2 ⟨subd17_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
