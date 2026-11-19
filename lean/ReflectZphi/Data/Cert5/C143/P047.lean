import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd17_1_416 : subd17_1 [-1, -1, 4] = true := by decide +kernel
theorem subd17_1_417 : subd17_1 [-1, -1, 5] = true := by decide +kernel
theorem subd17_1_418 : subd17_1 [-1, -1, 6] = true := by decide +kernel
theorem subd17_1_419 : subd17_1 [-1, -1, 7] = true := by decide +kernel
theorem subd17_1_420 : subd17_1 [-1, -1, 8] = true := by decide +kernel
theorem subd17_1_421 : subd17_1 [-1, 0, -10] = true := by decide +kernel
theorem subd17_1_422 : subd17_1 [-1, 0, -9] = true := by decide +kernel
theorem subd17_1_423 : subd17_1 [-1, 0, -8] = true := by decide +kernel
theorem subd17_1_424 : subd17_1 [-1, 0, -7] = true := by decide +kernel
theorem subd17_1_425 : subd17_1 [-1, 0, -6] = true := by decide +kernel
theorem subd17_1_426 : subd17_1 [-1, 0, -5] = true := by decide +kernel
theorem subd17_1_427 : subd17_1 [-1, 0, -4] = true := by decide +kernel
theorem subd17_1_428 : subd17_1 [-1, 0, -3] = true := by decide +kernel
theorem subd17_1_429 : subd17_1 [-1, 0, -2] = true := by decide +kernel
theorem subd17_1_430 : subd17_1 [-1, 0, -1] = true := by decide +kernel
theorem subd17_1_431 : subd17_1 [-1, 0, 0] = true := by decide +kernel
theorem subd17_1_432 : subd17_1 [-1, 0, 1] = true := by decide +kernel
theorem subd17_1_433 : subd17_1 [-1, 0, 2] = true := by decide +kernel
theorem subd17_1_434 : subd17_1 [-1, 0, 3] = true := by decide +kernel
theorem subd17_1_435 : subd17_1 [-1, 0, 4] = true := by decide +kernel
theorem subd17_1_436 : subd17_1 [-1, 0, 5] = true := by decide +kernel
theorem subd17_1_437 : subd17_1 [-1, 0, 6] = true := by decide +kernel
theorem subd17_1_438 : subd17_1 [-1, 0, 7] = true := by decide +kernel
theorem subd17_1_439 : subd17_1 [-1, 0, 8] = true := by decide +kernel
theorem subd17_1_440 : subd17_1 [-1, 1, -10] = true := by decide +kernel
theorem subd17_1_441 : subd17_1 [-1, 1, -9] = true := by decide +kernel
theorem subd17_1_442 : subd17_1 [-1, 1, -8] = true := by decide +kernel
theorem subd17_1_443 : subd17_1 [-1, 1, -7] = true := by decide +kernel
theorem subd17_1_444 : subd17_1 [-1, 1, -6] = true := by decide +kernel
theorem subd17_1_445 : subd17_1 [-1, 1, -5] = true := by decide +kernel
theorem subd17_1_446 : subd17_1 [-1, 1, -4] = true := by decide +kernel
theorem subd17_1_447 : subd17_1 [-1, 1, -3] = true := by decide +kernel
theorem sbd17_1_13 : ∀ q ∈ blkd17_1_13, subd17_1 q = true := by
  unfold blkd17_1_13
  exact List.forall_mem_cons.2 ⟨subd17_1_416, List.forall_mem_cons.2 ⟨subd17_1_417, List.forall_mem_cons.2 ⟨subd17_1_418, List.forall_mem_cons.2 ⟨subd17_1_419, List.forall_mem_cons.2 ⟨subd17_1_420, List.forall_mem_cons.2 ⟨subd17_1_421, List.forall_mem_cons.2 ⟨subd17_1_422, List.forall_mem_cons.2 ⟨subd17_1_423, List.forall_mem_cons.2 ⟨subd17_1_424, List.forall_mem_cons.2 ⟨subd17_1_425, List.forall_mem_cons.2 ⟨subd17_1_426, List.forall_mem_cons.2 ⟨subd17_1_427, List.forall_mem_cons.2 ⟨subd17_1_428, List.forall_mem_cons.2 ⟨subd17_1_429, List.forall_mem_cons.2 ⟨subd17_1_430, List.forall_mem_cons.2 ⟨subd17_1_431, List.forall_mem_cons.2 ⟨subd17_1_432, List.forall_mem_cons.2 ⟨subd17_1_433, List.forall_mem_cons.2 ⟨subd17_1_434, List.forall_mem_cons.2 ⟨subd17_1_435, List.forall_mem_cons.2 ⟨subd17_1_436, List.forall_mem_cons.2 ⟨subd17_1_437, List.forall_mem_cons.2 ⟨subd17_1_438, List.forall_mem_cons.2 ⟨subd17_1_439, List.forall_mem_cons.2 ⟨subd17_1_440, List.forall_mem_cons.2 ⟨subd17_1_441, List.forall_mem_cons.2 ⟨subd17_1_442, List.forall_mem_cons.2 ⟨subd17_1_443, List.forall_mem_cons.2 ⟨subd17_1_444, List.forall_mem_cons.2 ⟨subd17_1_445, List.forall_mem_cons.2 ⟨subd17_1_446, List.forall_mem_cons.2 ⟨subd17_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_448 : subd17_1 [-1, 1, -2] = true := by decide +kernel
theorem subd17_1_449 : subd17_1 [-1, 1, -1] = true := by decide +kernel
theorem subd17_1_450 : subd17_1 [-1, 1, 0] = true := by decide +kernel
theorem subd17_1_451 : subd17_1 [-1, 1, 1] = true := by decide +kernel
theorem subd17_1_452 : subd17_1 [-1, 1, 2] = true := by decide +kernel
theorem subd17_1_453 : subd17_1 [-1, 1, 3] = true := by decide +kernel
theorem subd17_1_454 : subd17_1 [-1, 1, 4] = true := by decide +kernel
theorem subd17_1_455 : subd17_1 [-1, 1, 5] = true := by decide +kernel
theorem subd17_1_456 : subd17_1 [-1, 1, 6] = true := by decide +kernel
theorem subd17_1_457 : subd17_1 [-1, 1, 7] = true := by decide +kernel
theorem subd17_1_458 : subd17_1 [-1, 1, 8] = true := by decide +kernel
theorem subd17_1_459 : subd17_1 [-1, 2, -9] = true := by decide +kernel
theorem subd17_1_460 : subd17_1 [-1, 2, -8] = true := by decide +kernel
theorem subd17_1_461 : subd17_1 [-1, 2, -7] = true := by decide +kernel
theorem subd17_1_462 : subd17_1 [-1, 2, -6] = true := by decide +kernel
theorem subd17_1_463 : subd17_1 [-1, 2, -5] = true := by decide +kernel
theorem subd17_1_464 : subd17_1 [-1, 2, -4] = true := by decide +kernel
theorem subd17_1_465 : subd17_1 [-1, 2, -3] = true := by decide +kernel
theorem subd17_1_466 : subd17_1 [-1, 2, -2] = true := by decide +kernel
theorem subd17_1_467 : subd17_1 [-1, 2, -1] = true := by decide +kernel
theorem subd17_1_468 : subd17_1 [-1, 2, 0] = true := by decide +kernel
theorem subd17_1_469 : subd17_1 [-1, 2, 1] = true := by decide +kernel
theorem subd17_1_470 : subd17_1 [-1, 2, 2] = true := by decide +kernel
theorem subd17_1_471 : subd17_1 [-1, 2, 3] = true := by decide +kernel
theorem subd17_1_472 : subd17_1 [-1, 2, 4] = true := by decide +kernel
theorem subd17_1_473 : subd17_1 [-1, 2, 5] = true := by decide +kernel
theorem subd17_1_474 : subd17_1 [-1, 2, 6] = true := by decide +kernel
theorem subd17_1_475 : subd17_1 [-1, 2, 7] = true := by decide +kernel
theorem subd17_1_476 : subd17_1 [-1, 2, 8] = true := by decide +kernel
theorem subd17_1_477 : subd17_1 [-1, 3, -9] = true := by decide +kernel
theorem subd17_1_478 : subd17_1 [-1, 3, -8] = true := by decide +kernel
theorem subd17_1_479 : subd17_1 [-1, 3, -7] = true := by decide +kernel
theorem sbd17_1_14 : ∀ q ∈ blkd17_1_14, subd17_1 q = true := by
  unfold blkd17_1_14
  exact List.forall_mem_cons.2 ⟨subd17_1_448, List.forall_mem_cons.2 ⟨subd17_1_449, List.forall_mem_cons.2 ⟨subd17_1_450, List.forall_mem_cons.2 ⟨subd17_1_451, List.forall_mem_cons.2 ⟨subd17_1_452, List.forall_mem_cons.2 ⟨subd17_1_453, List.forall_mem_cons.2 ⟨subd17_1_454, List.forall_mem_cons.2 ⟨subd17_1_455, List.forall_mem_cons.2 ⟨subd17_1_456, List.forall_mem_cons.2 ⟨subd17_1_457, List.forall_mem_cons.2 ⟨subd17_1_458, List.forall_mem_cons.2 ⟨subd17_1_459, List.forall_mem_cons.2 ⟨subd17_1_460, List.forall_mem_cons.2 ⟨subd17_1_461, List.forall_mem_cons.2 ⟨subd17_1_462, List.forall_mem_cons.2 ⟨subd17_1_463, List.forall_mem_cons.2 ⟨subd17_1_464, List.forall_mem_cons.2 ⟨subd17_1_465, List.forall_mem_cons.2 ⟨subd17_1_466, List.forall_mem_cons.2 ⟨subd17_1_467, List.forall_mem_cons.2 ⟨subd17_1_468, List.forall_mem_cons.2 ⟨subd17_1_469, List.forall_mem_cons.2 ⟨subd17_1_470, List.forall_mem_cons.2 ⟨subd17_1_471, List.forall_mem_cons.2 ⟨subd17_1_472, List.forall_mem_cons.2 ⟨subd17_1_473, List.forall_mem_cons.2 ⟨subd17_1_474, List.forall_mem_cons.2 ⟨subd17_1_475, List.forall_mem_cons.2 ⟨subd17_1_476, List.forall_mem_cons.2 ⟨subd17_1_477, List.forall_mem_cons.2 ⟨subd17_1_478, List.forall_mem_cons.2 ⟨subd17_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_480 : subd17_1 [-1, 3, -6] = true := by decide +kernel
theorem subd17_1_481 : subd17_1 [-1, 3, -5] = true := by decide +kernel
theorem subd17_1_482 : subd17_1 [-1, 3, -4] = true := by decide +kernel
theorem subd17_1_483 : subd17_1 [-1, 3, -3] = true := by decide +kernel
theorem subd17_1_484 : subd17_1 [-1, 3, -2] = true := by decide +kernel
theorem subd17_1_485 : subd17_1 [-1, 3, -1] = true := by decide +kernel
theorem subd17_1_486 : subd17_1 [-1, 3, 0] = true := by decide +kernel
theorem subd17_1_487 : subd17_1 [-1, 3, 1] = true := by decide +kernel
theorem subd17_1_488 : subd17_1 [-1, 3, 2] = true := by decide +kernel
theorem subd17_1_489 : subd17_1 [-1, 3, 3] = true := by decide +kernel
theorem subd17_1_490 : subd17_1 [-1, 3, 4] = true := by decide +kernel
theorem subd17_1_491 : subd17_1 [-1, 3, 5] = true := by decide +kernel
theorem subd17_1_492 : subd17_1 [-1, 3, 6] = true := by decide +kernel
theorem subd17_1_493 : subd17_1 [-1, 3, 7] = true := by decide +kernel
theorem subd17_1_494 : subd17_1 [-1, 4, -8] = true := by decide +kernel
theorem subd17_1_495 : subd17_1 [-1, 4, -7] = true := by decide +kernel
theorem subd17_1_496 : subd17_1 [-1, 4, -6] = true := by decide +kernel
theorem subd17_1_497 : subd17_1 [-1, 4, -5] = true := by decide +kernel
theorem subd17_1_498 : subd17_1 [-1, 4, -4] = true := by decide +kernel
theorem subd17_1_499 : subd17_1 [-1, 4, -3] = true := by decide +kernel
theorem subd17_1_500 : subd17_1 [-1, 4, -2] = true := by decide +kernel
theorem subd17_1_501 : subd17_1 [-1, 4, -1] = true := by decide +kernel
theorem subd17_1_502 : subd17_1 [-1, 4, 0] = true := by decide +kernel
theorem subd17_1_503 : subd17_1 [-1, 4, 1] = true := by decide +kernel
theorem subd17_1_504 : subd17_1 [-1, 4, 2] = true := by decide +kernel
theorem subd17_1_505 : subd17_1 [-1, 4, 3] = true := by decide +kernel
theorem subd17_1_506 : subd17_1 [-1, 4, 4] = true := by decide +kernel
theorem subd17_1_507 : subd17_1 [-1, 4, 5] = true := by decide +kernel
theorem subd17_1_508 : subd17_1 [-1, 4, 6] = true := by decide +kernel
theorem subd17_1_509 : subd17_1 [-1, 5, -7] = true := by decide +kernel
theorem subd17_1_510 : subd17_1 [-1, 5, -6] = true := by decide +kernel
theorem subd17_1_511 : subd17_1 [-1, 5, -5] = true := by decide +kernel
theorem sbd17_1_15 : ∀ q ∈ blkd17_1_15, subd17_1 q = true := by
  unfold blkd17_1_15
  exact List.forall_mem_cons.2 ⟨subd17_1_480, List.forall_mem_cons.2 ⟨subd17_1_481, List.forall_mem_cons.2 ⟨subd17_1_482, List.forall_mem_cons.2 ⟨subd17_1_483, List.forall_mem_cons.2 ⟨subd17_1_484, List.forall_mem_cons.2 ⟨subd17_1_485, List.forall_mem_cons.2 ⟨subd17_1_486, List.forall_mem_cons.2 ⟨subd17_1_487, List.forall_mem_cons.2 ⟨subd17_1_488, List.forall_mem_cons.2 ⟨subd17_1_489, List.forall_mem_cons.2 ⟨subd17_1_490, List.forall_mem_cons.2 ⟨subd17_1_491, List.forall_mem_cons.2 ⟨subd17_1_492, List.forall_mem_cons.2 ⟨subd17_1_493, List.forall_mem_cons.2 ⟨subd17_1_494, List.forall_mem_cons.2 ⟨subd17_1_495, List.forall_mem_cons.2 ⟨subd17_1_496, List.forall_mem_cons.2 ⟨subd17_1_497, List.forall_mem_cons.2 ⟨subd17_1_498, List.forall_mem_cons.2 ⟨subd17_1_499, List.forall_mem_cons.2 ⟨subd17_1_500, List.forall_mem_cons.2 ⟨subd17_1_501, List.forall_mem_cons.2 ⟨subd17_1_502, List.forall_mem_cons.2 ⟨subd17_1_503, List.forall_mem_cons.2 ⟨subd17_1_504, List.forall_mem_cons.2 ⟨subd17_1_505, List.forall_mem_cons.2 ⟨subd17_1_506, List.forall_mem_cons.2 ⟨subd17_1_507, List.forall_mem_cons.2 ⟨subd17_1_508, List.forall_mem_cons.2 ⟨subd17_1_509, List.forall_mem_cons.2 ⟨subd17_1_510, List.forall_mem_cons.2 ⟨subd17_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_512 : subd17_1 [-1, 5, -4] = true := by decide +kernel
theorem subd17_1_513 : subd17_1 [-1, 5, -3] = true := by decide +kernel
theorem subd17_1_514 : subd17_1 [-1, 5, -2] = true := by decide +kernel
theorem subd17_1_515 : subd17_1 [-1, 5, -1] = true := by decide +kernel
theorem subd17_1_516 : subd17_1 [-1, 5, 0] = true := by decide +kernel
theorem subd17_1_517 : subd17_1 [-1, 5, 1] = true := by decide +kernel
theorem subd17_1_518 : subd17_1 [-1, 5, 2] = true := by decide +kernel
theorem subd17_1_519 : subd17_1 [-1, 5, 3] = true := by decide +kernel
theorem subd17_1_520 : subd17_1 [-1, 5, 4] = true := by decide +kernel
theorem subd17_1_521 : subd17_1 [-1, 5, 5] = true := by decide +kernel
theorem subd17_1_522 : subd17_1 [-1, 6] = true := by decide +kernel
theorem subd17_1_523 : subd17_1 [-1, 7] = true := by decide +kernel
theorem subd17_1_524 : subd17_1 [0, -7] = true := by decide +kernel
theorem subd17_1_525 : subd17_1 [0, -6] = true := by decide +kernel
theorem subd17_1_526 : subd17_1 [0, -5, -7] = true := by decide +kernel
theorem subd17_1_527 : subd17_1 [0, -5, -6] = true := by decide +kernel
theorem subd17_1_528 : subd17_1 [0, -5, -5] = true := by decide +kernel
theorem subd17_1_529 : subd17_1 [0, -5, -4] = true := by decide +kernel
theorem subd17_1_530 : subd17_1 [0, -5, -3] = true := by decide +kernel
theorem subd17_1_531 : subd17_1 [0, -5, -2] = true := by decide +kernel
theorem subd17_1_532 : subd17_1 [0, -5, -1] = true := by decide +kernel
theorem subd17_1_533 : subd17_1 [0, -5, 0] = true := by decide +kernel
theorem subd17_1_534 : subd17_1 [0, -5, 1] = true := by decide +kernel
theorem subd17_1_535 : subd17_1 [0, -5, 2] = true := by decide +kernel
theorem subd17_1_536 : subd17_1 [0, -5, 3] = true := by decide +kernel
theorem subd17_1_537 : subd17_1 [0, -5, 4] = true := by decide +kernel
theorem subd17_1_538 : subd17_1 [0, -5, 5] = true := by decide +kernel
theorem subd17_1_539 : subd17_1 [0, -5, 6] = true := by decide +kernel
theorem subd17_1_540 : subd17_1 [0, -4, -8] = true := by decide +kernel
theorem subd17_1_541 : subd17_1 [0, -4, -7] = true := by decide +kernel
theorem subd17_1_542 : subd17_1 [0, -4, -6] = true := by decide +kernel
theorem subd17_1_543 : subd17_1 [0, -4, -5] = true := by decide +kernel
theorem sbd17_1_16 : ∀ q ∈ blkd17_1_16, subd17_1 q = true := by
  unfold blkd17_1_16
  exact List.forall_mem_cons.2 ⟨subd17_1_512, List.forall_mem_cons.2 ⟨subd17_1_513, List.forall_mem_cons.2 ⟨subd17_1_514, List.forall_mem_cons.2 ⟨subd17_1_515, List.forall_mem_cons.2 ⟨subd17_1_516, List.forall_mem_cons.2 ⟨subd17_1_517, List.forall_mem_cons.2 ⟨subd17_1_518, List.forall_mem_cons.2 ⟨subd17_1_519, List.forall_mem_cons.2 ⟨subd17_1_520, List.forall_mem_cons.2 ⟨subd17_1_521, List.forall_mem_cons.2 ⟨subd17_1_522, List.forall_mem_cons.2 ⟨subd17_1_523, List.forall_mem_cons.2 ⟨subd17_1_524, List.forall_mem_cons.2 ⟨subd17_1_525, List.forall_mem_cons.2 ⟨subd17_1_526, List.forall_mem_cons.2 ⟨subd17_1_527, List.forall_mem_cons.2 ⟨subd17_1_528, List.forall_mem_cons.2 ⟨subd17_1_529, List.forall_mem_cons.2 ⟨subd17_1_530, List.forall_mem_cons.2 ⟨subd17_1_531, List.forall_mem_cons.2 ⟨subd17_1_532, List.forall_mem_cons.2 ⟨subd17_1_533, List.forall_mem_cons.2 ⟨subd17_1_534, List.forall_mem_cons.2 ⟨subd17_1_535, List.forall_mem_cons.2 ⟨subd17_1_536, List.forall_mem_cons.2 ⟨subd17_1_537, List.forall_mem_cons.2 ⟨subd17_1_538, List.forall_mem_cons.2 ⟨subd17_1_539, List.forall_mem_cons.2 ⟨subd17_1_540, List.forall_mem_cons.2 ⟨subd17_1_541, List.forall_mem_cons.2 ⟨subd17_1_542, List.forall_mem_cons.2 ⟨subd17_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_544 : subd17_1 [0, -4, -4] = true := by decide +kernel
theorem subd17_1_545 : subd17_1 [0, -4, -3] = true := by decide +kernel
theorem subd17_1_546 : subd17_1 [0, -4, -2] = true := by decide +kernel
theorem subd17_1_547 : subd17_1 [0, -4, -1] = true := by decide +kernel
theorem subd17_1_548 : subd17_1 [0, -4, 0] = true := by decide +kernel
theorem subd17_1_549 : subd17_1 [0, -4, 1] = true := by decide +kernel
theorem subd17_1_550 : subd17_1 [0, -4, 2] = true := by decide +kernel
theorem subd17_1_551 : subd17_1 [0, -4, 3] = true := by decide +kernel
theorem subd17_1_552 : subd17_1 [0, -4, 4] = true := by decide +kernel
theorem subd17_1_553 : subd17_1 [0, -4, 5] = true := by decide +kernel
theorem subd17_1_554 : subd17_1 [0, -4, 6] = true := by decide +kernel
theorem subd17_1_555 : subd17_1 [0, -4, 7] = true := by decide +kernel
theorem subd17_1_556 : subd17_1 [0, -3, -8] = true := by decide +kernel
theorem subd17_1_557 : subd17_1 [0, -3, -7] = true := by decide +kernel
theorem subd17_1_558 : subd17_1 [0, -3, -6] = true := by decide +kernel
theorem subd17_1_559 : subd17_1 [0, -3, -5] = true := by decide +kernel
theorem subd17_1_560 : subd17_1 [0, -3, -4] = true := by decide +kernel
theorem subd17_1_561 : subd17_1 [0, -3, -3] = true := by decide +kernel
theorem subd17_1_562 : subd17_1 [0, -3, -2] = true := by decide +kernel
theorem subd17_1_563 : subd17_1 [0, -3, -1] = true := by decide +kernel
theorem subd17_1_564 : subd17_1 [0, -3, 0] = true := by decide +kernel
theorem subd17_1_565 : subd17_1 [0, -3, 1] = true := by decide +kernel
theorem subd17_1_566 : subd17_1 [0, -3, 2] = true := by decide +kernel
theorem subd17_1_567 : subd17_1 [0, -3, 3] = true := by decide +kernel
theorem subd17_1_568 : subd17_1 [0, -3, 4] = true := by decide +kernel
theorem subd17_1_569 : subd17_1 [0, -3, 5] = true := by decide +kernel
theorem subd17_1_570 : subd17_1 [0, -3, 6] = true := by decide +kernel
theorem subd17_1_571 : subd17_1 [0, -3, 7] = true := by decide +kernel
theorem subd17_1_572 : subd17_1 [0, -3, 8] = true := by decide +kernel
theorem subd17_1_573 : subd17_1 [0, -2, -9] = true := by decide +kernel
theorem subd17_1_574 : subd17_1 [0, -2, -8] = true := by decide +kernel
theorem subd17_1_575 : subd17_1 [0, -2, -7] = true := by decide +kernel
theorem sbd17_1_17 : ∀ q ∈ blkd17_1_17, subd17_1 q = true := by
  unfold blkd17_1_17
  exact List.forall_mem_cons.2 ⟨subd17_1_544, List.forall_mem_cons.2 ⟨subd17_1_545, List.forall_mem_cons.2 ⟨subd17_1_546, List.forall_mem_cons.2 ⟨subd17_1_547, List.forall_mem_cons.2 ⟨subd17_1_548, List.forall_mem_cons.2 ⟨subd17_1_549, List.forall_mem_cons.2 ⟨subd17_1_550, List.forall_mem_cons.2 ⟨subd17_1_551, List.forall_mem_cons.2 ⟨subd17_1_552, List.forall_mem_cons.2 ⟨subd17_1_553, List.forall_mem_cons.2 ⟨subd17_1_554, List.forall_mem_cons.2 ⟨subd17_1_555, List.forall_mem_cons.2 ⟨subd17_1_556, List.forall_mem_cons.2 ⟨subd17_1_557, List.forall_mem_cons.2 ⟨subd17_1_558, List.forall_mem_cons.2 ⟨subd17_1_559, List.forall_mem_cons.2 ⟨subd17_1_560, List.forall_mem_cons.2 ⟨subd17_1_561, List.forall_mem_cons.2 ⟨subd17_1_562, List.forall_mem_cons.2 ⟨subd17_1_563, List.forall_mem_cons.2 ⟨subd17_1_564, List.forall_mem_cons.2 ⟨subd17_1_565, List.forall_mem_cons.2 ⟨subd17_1_566, List.forall_mem_cons.2 ⟨subd17_1_567, List.forall_mem_cons.2 ⟨subd17_1_568, List.forall_mem_cons.2 ⟨subd17_1_569, List.forall_mem_cons.2 ⟨subd17_1_570, List.forall_mem_cons.2 ⟨subd17_1_571, List.forall_mem_cons.2 ⟨subd17_1_572, List.forall_mem_cons.2 ⟨subd17_1_573, List.forall_mem_cons.2 ⟨subd17_1_574, List.forall_mem_cons.2 ⟨subd17_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_576 : subd17_1 [0, -2, -6] = true := by decide +kernel
theorem subd17_1_577 : subd17_1 [0, -2, -5] = true := by decide +kernel
theorem subd17_1_578 : subd17_1 [0, -2, -4] = true := by decide +kernel
theorem subd17_1_579 : subd17_1 [0, -2, -3] = true := by decide +kernel
theorem subd17_1_580 : subd17_1 [0, -2, -2] = true := by decide +kernel
theorem subd17_1_581 : subd17_1 [0, -2, -1] = true := by decide +kernel
theorem subd17_1_582 : subd17_1 [0, -2, 0] = true := by decide +kernel
theorem subd17_1_583 : subd17_1 [0, -2, 1] = true := by decide +kernel
theorem subd17_1_584 : subd17_1 [0, -2, 2] = true := by decide +kernel
theorem subd17_1_585 : subd17_1 [0, -2, 3] = true := by decide +kernel
theorem subd17_1_586 : subd17_1 [0, -2, 4] = true := by decide +kernel
theorem subd17_1_587 : subd17_1 [0, -2, 5] = true := by decide +kernel
theorem subd17_1_588 : subd17_1 [0, -2, 6] = true := by decide +kernel
theorem subd17_1_589 : subd17_1 [0, -2, 7] = true := by decide +kernel
theorem subd17_1_590 : subd17_1 [0, -2, 8] = true := by decide +kernel
theorem subd17_1_591 : subd17_1 [0, -1, -9] = true := by decide +kernel
theorem subd17_1_592 : subd17_1 [0, -1, -8] = true := by decide +kernel
theorem subd17_1_593 : subd17_1 [0, -1, -7] = true := by decide +kernel
theorem subd17_1_594 : subd17_1 [0, -1, -6] = true := by decide +kernel
theorem subd17_1_595 : subd17_1 [0, -1, -5] = true := by decide +kernel
theorem subd17_1_596 : subd17_1 [0, -1, -4] = true := by decide +kernel
theorem subd17_1_597 : subd17_1 [0, -1, -3] = true := by decide +kernel
theorem subd17_1_598 : subd17_1 [0, -1, -2] = true := by decide +kernel
theorem subd17_1_599 : subd17_1 [0, -1, -1] = true := by decide +kernel
theorem subd17_1_600 : subd17_1 [0, -1, 0] = true := by decide +kernel
theorem subd17_1_601 : subd17_1 [0, -1, 1] = true := by decide +kernel
theorem subd17_1_602 : subd17_1 [0, -1, 2] = true := by decide +kernel
theorem subd17_1_603 : subd17_1 [0, -1, 3] = true := by decide +kernel
theorem subd17_1_604 : subd17_1 [0, -1, 4] = true := by decide +kernel
theorem subd17_1_605 : subd17_1 [0, -1, 5] = true := by decide +kernel
theorem subd17_1_606 : subd17_1 [0, -1, 6] = true := by decide +kernel
theorem subd17_1_607 : subd17_1 [0, -1, 7] = true := by decide +kernel
theorem sbd17_1_18 : ∀ q ∈ blkd17_1_18, subd17_1 q = true := by
  unfold blkd17_1_18
  exact List.forall_mem_cons.2 ⟨subd17_1_576, List.forall_mem_cons.2 ⟨subd17_1_577, List.forall_mem_cons.2 ⟨subd17_1_578, List.forall_mem_cons.2 ⟨subd17_1_579, List.forall_mem_cons.2 ⟨subd17_1_580, List.forall_mem_cons.2 ⟨subd17_1_581, List.forall_mem_cons.2 ⟨subd17_1_582, List.forall_mem_cons.2 ⟨subd17_1_583, List.forall_mem_cons.2 ⟨subd17_1_584, List.forall_mem_cons.2 ⟨subd17_1_585, List.forall_mem_cons.2 ⟨subd17_1_586, List.forall_mem_cons.2 ⟨subd17_1_587, List.forall_mem_cons.2 ⟨subd17_1_588, List.forall_mem_cons.2 ⟨subd17_1_589, List.forall_mem_cons.2 ⟨subd17_1_590, List.forall_mem_cons.2 ⟨subd17_1_591, List.forall_mem_cons.2 ⟨subd17_1_592, List.forall_mem_cons.2 ⟨subd17_1_593, List.forall_mem_cons.2 ⟨subd17_1_594, List.forall_mem_cons.2 ⟨subd17_1_595, List.forall_mem_cons.2 ⟨subd17_1_596, List.forall_mem_cons.2 ⟨subd17_1_597, List.forall_mem_cons.2 ⟨subd17_1_598, List.forall_mem_cons.2 ⟨subd17_1_599, List.forall_mem_cons.2 ⟨subd17_1_600, List.forall_mem_cons.2 ⟨subd17_1_601, List.forall_mem_cons.2 ⟨subd17_1_602, List.forall_mem_cons.2 ⟨subd17_1_603, List.forall_mem_cons.2 ⟨subd17_1_604, List.forall_mem_cons.2 ⟨subd17_1_605, List.forall_mem_cons.2 ⟨subd17_1_606, List.forall_mem_cons.2 ⟨subd17_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_608 : subd17_1 [0, -1, 8] = true := by decide +kernel
theorem subd17_1_609 : subd17_1 [0, 0, -9] = true := by decide +kernel
theorem subd17_1_610 : subd17_1 [0, 0, -8] = true := by decide +kernel
theorem subd17_1_611 : subd17_1 [0, 0, -7] = true := by decide +kernel
theorem subd17_1_612 : subd17_1 [0, 0, -6] = true := by decide +kernel
theorem subd17_1_613 : subd17_1 [0, 0, -5] = true := by decide +kernel
theorem subd17_1_614 : subd17_1 [0, 0, -4] = true := by decide +kernel
theorem subd17_1_615 : subd17_1 [0, 0, -3] = true := by decide +kernel
theorem subd17_1_616 : subd17_1 [0, 0, -2] = true := by decide +kernel
theorem subd17_1_617 : subd17_1 [0, 0, -1] = true := by decide +kernel
theorem subd17_1_618 : subd17_1 [0, 0, 0] = true := by decide +kernel
theorem subd17_1_619 : subd17_1 [0, 0, 1] = true := by decide +kernel
theorem subd17_1_620 : subd17_1 [0, 0, 2] = true := by decide +kernel
theorem subd17_1_621 : subd17_1 [0, 0, 3] = true := by decide +kernel
theorem subd17_1_622 : subd17_1 [0, 0, 4] = true := by decide +kernel
theorem subd17_1_623 : subd17_1 [0, 0, 5] = true := by decide +kernel
theorem subd17_1_624 : subd17_1 [0, 0, 6] = true := by decide +kernel
theorem subd17_1_625 : subd17_1 [0, 0, 7] = true := by decide +kernel
theorem subd17_1_626 : subd17_1 [0, 0, 8] = true := by decide +kernel
theorem subd17_1_627 : subd17_1 [0, 1, -9] = true := by decide +kernel
theorem subd17_1_628 : subd17_1 [0, 1, -8] = true := by decide +kernel
theorem subd17_1_629 : subd17_1 [0, 1, -7] = true := by decide +kernel
theorem subd17_1_630 : subd17_1 [0, 1, -6] = true := by decide +kernel
theorem subd17_1_631 : subd17_1 [0, 1, -5] = true := by decide +kernel
theorem subd17_1_632 : subd17_1 [0, 1, -4] = true := by decide +kernel
theorem subd17_1_633 : subd17_1 [0, 1, -3] = true := by decide +kernel
theorem subd17_1_634 : subd17_1 [0, 1, -2] = true := by decide +kernel
theorem subd17_1_635 : subd17_1 [0, 1, -1] = true := by decide +kernel
theorem subd17_1_636 : subd17_1 [0, 1, 0] = true := by decide +kernel
theorem subd17_1_637 : subd17_1 [0, 1, 1] = true := by decide +kernel
theorem subd17_1_638 : subd17_1 [0, 1, 2] = true := by decide +kernel
theorem subd17_1_639 : subd17_1 [0, 1, 3] = true := by decide +kernel
theorem sbd17_1_19 : ∀ q ∈ blkd17_1_19, subd17_1 q = true := by
  unfold blkd17_1_19
  exact List.forall_mem_cons.2 ⟨subd17_1_608, List.forall_mem_cons.2 ⟨subd17_1_609, List.forall_mem_cons.2 ⟨subd17_1_610, List.forall_mem_cons.2 ⟨subd17_1_611, List.forall_mem_cons.2 ⟨subd17_1_612, List.forall_mem_cons.2 ⟨subd17_1_613, List.forall_mem_cons.2 ⟨subd17_1_614, List.forall_mem_cons.2 ⟨subd17_1_615, List.forall_mem_cons.2 ⟨subd17_1_616, List.forall_mem_cons.2 ⟨subd17_1_617, List.forall_mem_cons.2 ⟨subd17_1_618, List.forall_mem_cons.2 ⟨subd17_1_619, List.forall_mem_cons.2 ⟨subd17_1_620, List.forall_mem_cons.2 ⟨subd17_1_621, List.forall_mem_cons.2 ⟨subd17_1_622, List.forall_mem_cons.2 ⟨subd17_1_623, List.forall_mem_cons.2 ⟨subd17_1_624, List.forall_mem_cons.2 ⟨subd17_1_625, List.forall_mem_cons.2 ⟨subd17_1_626, List.forall_mem_cons.2 ⟨subd17_1_627, List.forall_mem_cons.2 ⟨subd17_1_628, List.forall_mem_cons.2 ⟨subd17_1_629, List.forall_mem_cons.2 ⟨subd17_1_630, List.forall_mem_cons.2 ⟨subd17_1_631, List.forall_mem_cons.2 ⟨subd17_1_632, List.forall_mem_cons.2 ⟨subd17_1_633, List.forall_mem_cons.2 ⟨subd17_1_634, List.forall_mem_cons.2 ⟨subd17_1_635, List.forall_mem_cons.2 ⟨subd17_1_636, List.forall_mem_cons.2 ⟨subd17_1_637, List.forall_mem_cons.2 ⟨subd17_1_638, List.forall_mem_cons.2 ⟨subd17_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_640 : subd17_1 [0, 1, 4] = true := by decide +kernel
theorem subd17_1_641 : subd17_1 [0, 1, 5] = true := by decide +kernel
theorem subd17_1_642 : subd17_1 [0, 1, 6] = true := by decide +kernel
theorem subd17_1_643 : subd17_1 [0, 1, 7] = true := by decide +kernel
theorem subd17_1_644 : subd17_1 [0, 1, 8] = true := by decide +kernel
theorem subd17_1_645 : subd17_1 [0, 2, -9] = true := by decide +kernel
theorem subd17_1_646 : subd17_1 [0, 2, -8] = true := by decide +kernel
theorem subd17_1_647 : subd17_1 [0, 2, -7] = true := by decide +kernel
theorem subd17_1_648 : subd17_1 [0, 2, -6] = true := by decide +kernel
theorem subd17_1_649 : subd17_1 [0, 2, -5] = true := by decide +kernel
theorem subd17_1_650 : subd17_1 [0, 2, -4] = true := by decide +kernel
theorem subd17_1_651 : subd17_1 [0, 2, -3] = true := by decide +kernel
theorem subd17_1_652 : subd17_1 [0, 2, -2] = true := by decide +kernel
theorem subd17_1_653 : subd17_1 [0, 2, -1] = true := by decide +kernel
theorem subd17_1_654 : subd17_1 [0, 2, 0] = true := by decide +kernel
theorem subd17_1_655 : subd17_1 [0, 2, 1] = true := by decide +kernel
theorem subd17_1_656 : subd17_1 [0, 2, 2] = true := by decide +kernel
theorem subd17_1_657 : subd17_1 [0, 2, 3] = true := by decide +kernel
theorem subd17_1_658 : subd17_1 [0, 2, 4] = true := by decide +kernel
theorem subd17_1_659 : subd17_1 [0, 2, 5] = true := by decide +kernel
theorem subd17_1_660 : subd17_1 [0, 2, 6] = true := by decide +kernel
theorem subd17_1_661 : subd17_1 [0, 2, 7] = true := by decide +kernel
theorem subd17_1_662 : subd17_1 [0, 2, 8] = true := by decide +kernel
theorem subd17_1_663 : subd17_1 [0, 3, -9] = true := by decide +kernel
theorem subd17_1_664 : subd17_1 [0, 3, -8] = true := by decide +kernel
theorem subd17_1_665 : subd17_1 [0, 3, -7] = true := by decide +kernel
theorem subd17_1_666 : subd17_1 [0, 3, -6] = true := by decide +kernel
theorem subd17_1_667 : subd17_1 [0, 3, -5] = true := by decide +kernel
theorem subd17_1_668 : subd17_1 [0, 3, -4] = true := by decide +kernel
theorem subd17_1_669 : subd17_1 [0, 3, -3] = true := by decide +kernel
theorem subd17_1_670 : subd17_1 [0, 3, -2] = true := by decide +kernel
theorem subd17_1_671 : subd17_1 [0, 3, -1] = true := by decide +kernel
theorem sbd17_1_20 : ∀ q ∈ blkd17_1_20, subd17_1 q = true := by
  unfold blkd17_1_20
  exact List.forall_mem_cons.2 ⟨subd17_1_640, List.forall_mem_cons.2 ⟨subd17_1_641, List.forall_mem_cons.2 ⟨subd17_1_642, List.forall_mem_cons.2 ⟨subd17_1_643, List.forall_mem_cons.2 ⟨subd17_1_644, List.forall_mem_cons.2 ⟨subd17_1_645, List.forall_mem_cons.2 ⟨subd17_1_646, List.forall_mem_cons.2 ⟨subd17_1_647, List.forall_mem_cons.2 ⟨subd17_1_648, List.forall_mem_cons.2 ⟨subd17_1_649, List.forall_mem_cons.2 ⟨subd17_1_650, List.forall_mem_cons.2 ⟨subd17_1_651, List.forall_mem_cons.2 ⟨subd17_1_652, List.forall_mem_cons.2 ⟨subd17_1_653, List.forall_mem_cons.2 ⟨subd17_1_654, List.forall_mem_cons.2 ⟨subd17_1_655, List.forall_mem_cons.2 ⟨subd17_1_656, List.forall_mem_cons.2 ⟨subd17_1_657, List.forall_mem_cons.2 ⟨subd17_1_658, List.forall_mem_cons.2 ⟨subd17_1_659, List.forall_mem_cons.2 ⟨subd17_1_660, List.forall_mem_cons.2 ⟨subd17_1_661, List.forall_mem_cons.2 ⟨subd17_1_662, List.forall_mem_cons.2 ⟨subd17_1_663, List.forall_mem_cons.2 ⟨subd17_1_664, List.forall_mem_cons.2 ⟨subd17_1_665, List.forall_mem_cons.2 ⟨subd17_1_666, List.forall_mem_cons.2 ⟨subd17_1_667, List.forall_mem_cons.2 ⟨subd17_1_668, List.forall_mem_cons.2 ⟨subd17_1_669, List.forall_mem_cons.2 ⟨subd17_1_670, List.forall_mem_cons.2 ⟨subd17_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_672 : subd17_1 [0, 3, 0] = true := by decide +kernel
theorem subd17_1_673 : subd17_1 [0, 3, 1] = true := by decide +kernel
theorem subd17_1_674 : subd17_1 [0, 3, 2] = true := by decide +kernel
theorem subd17_1_675 : subd17_1 [0, 3, 3] = true := by decide +kernel
theorem subd17_1_676 : subd17_1 [0, 3, 4] = true := by decide +kernel
theorem subd17_1_677 : subd17_1 [0, 3, 5] = true := by decide +kernel
theorem subd17_1_678 : subd17_1 [0, 3, 6] = true := by decide +kernel
theorem subd17_1_679 : subd17_1 [0, 3, 7] = true := by decide +kernel
theorem subd17_1_680 : subd17_1 [0, 4, -8] = true := by decide +kernel
theorem subd17_1_681 : subd17_1 [0, 4, -7] = true := by decide +kernel
theorem subd17_1_682 : subd17_1 [0, 4, -6] = true := by decide +kernel
theorem subd17_1_683 : subd17_1 [0, 4, -5] = true := by decide +kernel
theorem subd17_1_684 : subd17_1 [0, 4, -4] = true := by decide +kernel
theorem subd17_1_685 : subd17_1 [0, 4, -3] = true := by decide +kernel
theorem subd17_1_686 : subd17_1 [0, 4, -2] = true := by decide +kernel
theorem subd17_1_687 : subd17_1 [0, 4, -1] = true := by decide +kernel
theorem subd17_1_688 : subd17_1 [0, 4, 0] = true := by decide +kernel
theorem subd17_1_689 : subd17_1 [0, 4, 1] = true := by decide +kernel
theorem subd17_1_690 : subd17_1 [0, 4, 2] = true := by decide +kernel
theorem subd17_1_691 : subd17_1 [0, 4, 3] = true := by decide +kernel
theorem subd17_1_692 : subd17_1 [0, 4, 4] = true := by decide +kernel
theorem subd17_1_693 : subd17_1 [0, 4, 5] = true := by decide +kernel
theorem subd17_1_694 : subd17_1 [0, 4, 6] = true := by decide +kernel
theorem subd17_1_695 : subd17_1 [0, 4, 7] = true := by decide +kernel
theorem subd17_1_696 : subd17_1 [0, 5, -7] = true := by decide +kernel
theorem subd17_1_697 : subd17_1 [0, 5, -6] = true := by decide +kernel
theorem subd17_1_698 : subd17_1 [0, 5, -5] = true := by decide +kernel
theorem subd17_1_699 : subd17_1 [0, 5, -4] = true := by decide +kernel
theorem subd17_1_700 : subd17_1 [0, 5, -3] = true := by decide +kernel
theorem subd17_1_701 : subd17_1 [0, 5, -2] = true := by decide +kernel
theorem subd17_1_702 : subd17_1 [0, 5, -1] = true := by decide +kernel
theorem subd17_1_703 : subd17_1 [0, 5, 0] = true := by decide +kernel
theorem sbd17_1_21 : ∀ q ∈ blkd17_1_21, subd17_1 q = true := by
  unfold blkd17_1_21
  exact List.forall_mem_cons.2 ⟨subd17_1_672, List.forall_mem_cons.2 ⟨subd17_1_673, List.forall_mem_cons.2 ⟨subd17_1_674, List.forall_mem_cons.2 ⟨subd17_1_675, List.forall_mem_cons.2 ⟨subd17_1_676, List.forall_mem_cons.2 ⟨subd17_1_677, List.forall_mem_cons.2 ⟨subd17_1_678, List.forall_mem_cons.2 ⟨subd17_1_679, List.forall_mem_cons.2 ⟨subd17_1_680, List.forall_mem_cons.2 ⟨subd17_1_681, List.forall_mem_cons.2 ⟨subd17_1_682, List.forall_mem_cons.2 ⟨subd17_1_683, List.forall_mem_cons.2 ⟨subd17_1_684, List.forall_mem_cons.2 ⟨subd17_1_685, List.forall_mem_cons.2 ⟨subd17_1_686, List.forall_mem_cons.2 ⟨subd17_1_687, List.forall_mem_cons.2 ⟨subd17_1_688, List.forall_mem_cons.2 ⟨subd17_1_689, List.forall_mem_cons.2 ⟨subd17_1_690, List.forall_mem_cons.2 ⟨subd17_1_691, List.forall_mem_cons.2 ⟨subd17_1_692, List.forall_mem_cons.2 ⟨subd17_1_693, List.forall_mem_cons.2 ⟨subd17_1_694, List.forall_mem_cons.2 ⟨subd17_1_695, List.forall_mem_cons.2 ⟨subd17_1_696, List.forall_mem_cons.2 ⟨subd17_1_697, List.forall_mem_cons.2 ⟨subd17_1_698, List.forall_mem_cons.2 ⟨subd17_1_699, List.forall_mem_cons.2 ⟨subd17_1_700, List.forall_mem_cons.2 ⟨subd17_1_701, List.forall_mem_cons.2 ⟨subd17_1_702, List.forall_mem_cons.2 ⟨subd17_1_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_704 : subd17_1 [0, 5, 1] = true := by decide +kernel
theorem subd17_1_705 : subd17_1 [0, 5, 2] = true := by decide +kernel
theorem subd17_1_706 : subd17_1 [0, 5, 3] = true := by decide +kernel
theorem subd17_1_707 : subd17_1 [0, 5, 4] = true := by decide +kernel
theorem subd17_1_708 : subd17_1 [0, 5, 5] = true := by decide +kernel
theorem subd17_1_709 : subd17_1 [0, 5, 6] = true := by decide +kernel
theorem subd17_1_710 : subd17_1 [0, 6] = true := by decide +kernel
theorem subd17_1_711 : subd17_1 [1, -8] = true := by decide +kernel
theorem subd17_1_712 : subd17_1 [1, -7] = true := by decide +kernel
theorem subd17_1_713 : subd17_1 [1, -6] = true := by decide +kernel
theorem subd17_1_714 : subd17_1 [1, -5, -6] = true := by decide +kernel
theorem subd17_1_715 : subd17_1 [1, -5, -5] = true := by decide +kernel
theorem subd17_1_716 : subd17_1 [1, -5, -4] = true := by decide +kernel
theorem subd17_1_717 : subd17_1 [1, -5, -3] = true := by decide +kernel
theorem subd17_1_718 : subd17_1 [1, -5, -2] = true := by decide +kernel
theorem subd17_1_719 : subd17_1 [1, -5, -1] = true := by decide +kernel
theorem subd17_1_720 : subd17_1 [1, -5, 0] = true := by decide +kernel
theorem subd17_1_721 : subd17_1 [1, -5, 1] = true := by decide +kernel
theorem subd17_1_722 : subd17_1 [1, -5, 2] = true := by decide +kernel
theorem subd17_1_723 : subd17_1 [1, -5, 3] = true := by decide +kernel
theorem subd17_1_724 : subd17_1 [1, -5, 4] = true := by decide +kernel
theorem subd17_1_725 : subd17_1 [1, -5, 5] = true := by decide +kernel
theorem subd17_1_726 : subd17_1 [1, -5, 6] = true := by decide +kernel
theorem subd17_1_727 : subd17_1 [1, -4, -7] = true := by decide +kernel
theorem subd17_1_728 : subd17_1 [1, -4, -6] = true := by decide +kernel
theorem subd17_1_729 : subd17_1 [1, -4, -5] = true := by decide +kernel
theorem subd17_1_730 : subd17_1 [1, -4, -4] = true := by decide +kernel
theorem subd17_1_731 : subd17_1 [1, -4, -3] = true := by decide +kernel
theorem subd17_1_732 : subd17_1 [1, -4, -2] = true := by decide +kernel
theorem subd17_1_733 : subd17_1 [1, -4, -1] = true := by decide +kernel
theorem subd17_1_734 : subd17_1 [1, -4, 0] = true := by decide +kernel
theorem subd17_1_735 : subd17_1 [1, -4, 1] = true := by decide +kernel
theorem sbd17_1_22 : ∀ q ∈ blkd17_1_22, subd17_1 q = true := by
  unfold blkd17_1_22
  exact List.forall_mem_cons.2 ⟨subd17_1_704, List.forall_mem_cons.2 ⟨subd17_1_705, List.forall_mem_cons.2 ⟨subd17_1_706, List.forall_mem_cons.2 ⟨subd17_1_707, List.forall_mem_cons.2 ⟨subd17_1_708, List.forall_mem_cons.2 ⟨subd17_1_709, List.forall_mem_cons.2 ⟨subd17_1_710, List.forall_mem_cons.2 ⟨subd17_1_711, List.forall_mem_cons.2 ⟨subd17_1_712, List.forall_mem_cons.2 ⟨subd17_1_713, List.forall_mem_cons.2 ⟨subd17_1_714, List.forall_mem_cons.2 ⟨subd17_1_715, List.forall_mem_cons.2 ⟨subd17_1_716, List.forall_mem_cons.2 ⟨subd17_1_717, List.forall_mem_cons.2 ⟨subd17_1_718, List.forall_mem_cons.2 ⟨subd17_1_719, List.forall_mem_cons.2 ⟨subd17_1_720, List.forall_mem_cons.2 ⟨subd17_1_721, List.forall_mem_cons.2 ⟨subd17_1_722, List.forall_mem_cons.2 ⟨subd17_1_723, List.forall_mem_cons.2 ⟨subd17_1_724, List.forall_mem_cons.2 ⟨subd17_1_725, List.forall_mem_cons.2 ⟨subd17_1_726, List.forall_mem_cons.2 ⟨subd17_1_727, List.forall_mem_cons.2 ⟨subd17_1_728, List.forall_mem_cons.2 ⟨subd17_1_729, List.forall_mem_cons.2 ⟨subd17_1_730, List.forall_mem_cons.2 ⟨subd17_1_731, List.forall_mem_cons.2 ⟨subd17_1_732, List.forall_mem_cons.2 ⟨subd17_1_733, List.forall_mem_cons.2 ⟨subd17_1_734, List.forall_mem_cons.2 ⟨subd17_1_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_736 : subd17_1 [1, -4, 2] = true := by decide +kernel
theorem subd17_1_737 : subd17_1 [1, -4, 3] = true := by decide +kernel
theorem subd17_1_738 : subd17_1 [1, -4, 4] = true := by decide +kernel
theorem subd17_1_739 : subd17_1 [1, -4, 5] = true := by decide +kernel
theorem subd17_1_740 : subd17_1 [1, -4, 6] = true := by decide +kernel
theorem subd17_1_741 : subd17_1 [1, -4, 7] = true := by decide +kernel
theorem subd17_1_742 : subd17_1 [1, -3, -8] = true := by decide +kernel
theorem subd17_1_743 : subd17_1 [1, -3, -7] = true := by decide +kernel
theorem subd17_1_744 : subd17_1 [1, -3, -6] = true := by decide +kernel
theorem subd17_1_745 : subd17_1 [1, -3, -5] = true := by decide +kernel
theorem subd17_1_746 : subd17_1 [1, -3, -4] = true := by decide +kernel
theorem subd17_1_747 : subd17_1 [1, -3, -3] = true := by decide +kernel
theorem subd17_1_748 : subd17_1 [1, -3, -2] = true := by decide +kernel
theorem subd17_1_749 : subd17_1 [1, -3, -1] = true := by decide +kernel
theorem subd17_1_750 : subd17_1 [1, -3, 0] = true := by decide +kernel
theorem subd17_1_751 : subd17_1 [1, -3, 1] = true := by decide +kernel
theorem subd17_1_752 : subd17_1 [1, -3, 2] = true := by decide +kernel
theorem subd17_1_753 : subd17_1 [1, -3, 3] = true := by decide +kernel
theorem subd17_1_754 : subd17_1 [1, -3, 4] = true := by decide +kernel
theorem subd17_1_755 : subd17_1 [1, -3, 5] = true := by decide +kernel
theorem subd17_1_756 : subd17_1 [1, -3, 6] = true := by decide +kernel
theorem subd17_1_757 : subd17_1 [1, -3, 7] = true := by decide +kernel
theorem subd17_1_758 : subd17_1 [1, -3, 8] = true := by decide +kernel
theorem subd17_1_759 : subd17_1 [1, -2, -9] = true := by decide +kernel
theorem subd17_1_760 : subd17_1 [1, -2, -8] = true := by decide +kernel
theorem subd17_1_761 : subd17_1 [1, -2, -7] = true := by decide +kernel
theorem subd17_1_762 : subd17_1 [1, -2, -6] = true := by decide +kernel
theorem subd17_1_763 : subd17_1 [1, -2, -5] = true := by decide +kernel
theorem subd17_1_764 : subd17_1 [1, -2, -4] = true := by decide +kernel
theorem subd17_1_765 : subd17_1 [1, -2, -3] = true := by decide +kernel
theorem subd17_1_766 : subd17_1 [1, -2, -2] = true := by decide +kernel
theorem subd17_1_767 : subd17_1 [1, -2, -1] = true := by decide +kernel
theorem sbd17_1_23 : ∀ q ∈ blkd17_1_23, subd17_1 q = true := by
  unfold blkd17_1_23
  exact List.forall_mem_cons.2 ⟨subd17_1_736, List.forall_mem_cons.2 ⟨subd17_1_737, List.forall_mem_cons.2 ⟨subd17_1_738, List.forall_mem_cons.2 ⟨subd17_1_739, List.forall_mem_cons.2 ⟨subd17_1_740, List.forall_mem_cons.2 ⟨subd17_1_741, List.forall_mem_cons.2 ⟨subd17_1_742, List.forall_mem_cons.2 ⟨subd17_1_743, List.forall_mem_cons.2 ⟨subd17_1_744, List.forall_mem_cons.2 ⟨subd17_1_745, List.forall_mem_cons.2 ⟨subd17_1_746, List.forall_mem_cons.2 ⟨subd17_1_747, List.forall_mem_cons.2 ⟨subd17_1_748, List.forall_mem_cons.2 ⟨subd17_1_749, List.forall_mem_cons.2 ⟨subd17_1_750, List.forall_mem_cons.2 ⟨subd17_1_751, List.forall_mem_cons.2 ⟨subd17_1_752, List.forall_mem_cons.2 ⟨subd17_1_753, List.forall_mem_cons.2 ⟨subd17_1_754, List.forall_mem_cons.2 ⟨subd17_1_755, List.forall_mem_cons.2 ⟨subd17_1_756, List.forall_mem_cons.2 ⟨subd17_1_757, List.forall_mem_cons.2 ⟨subd17_1_758, List.forall_mem_cons.2 ⟨subd17_1_759, List.forall_mem_cons.2 ⟨subd17_1_760, List.forall_mem_cons.2 ⟨subd17_1_761, List.forall_mem_cons.2 ⟨subd17_1_762, List.forall_mem_cons.2 ⟨subd17_1_763, List.forall_mem_cons.2 ⟨subd17_1_764, List.forall_mem_cons.2 ⟨subd17_1_765, List.forall_mem_cons.2 ⟨subd17_1_766, List.forall_mem_cons.2 ⟨subd17_1_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_768 : subd17_1 [1, -2, 0] = true := by decide +kernel
theorem subd17_1_769 : subd17_1 [1, -2, 1] = true := by decide +kernel
theorem subd17_1_770 : subd17_1 [1, -2, 2] = true := by decide +kernel
theorem subd17_1_771 : subd17_1 [1, -2, 3] = true := by decide +kernel
theorem subd17_1_772 : subd17_1 [1, -2, 4] = true := by decide +kernel
theorem subd17_1_773 : subd17_1 [1, -2, 5] = true := by decide +kernel
theorem subd17_1_774 : subd17_1 [1, -2, 6] = true := by decide +kernel
theorem subd17_1_775 : subd17_1 [1, -2, 7] = true := by decide +kernel
theorem subd17_1_776 : subd17_1 [1, -2, 8] = true := by decide +kernel
theorem subd17_1_777 : subd17_1 [1, -1, -9] = true := by decide +kernel
theorem subd17_1_778 : subd17_1 [1, -1, -8] = true := by decide +kernel
theorem subd17_1_779 : subd17_1 [1, -1, -7] = true := by decide +kernel
theorem subd17_1_780 : subd17_1 [1, -1, -6] = true := by decide +kernel
theorem subd17_1_781 : subd17_1 [1, -1, -5] = true := by decide +kernel
theorem subd17_1_782 : subd17_1 [1, -1, -4] = true := by decide +kernel
theorem subd17_1_783 : subd17_1 [1, -1, -3] = true := by decide +kernel
theorem subd17_1_784 : subd17_1 [1, -1, -2] = true := by decide +kernel
theorem subd17_1_785 : subd17_1 [1, -1, -1] = true := by decide +kernel
theorem subd17_1_786 : subd17_1 [1, -1, 0] = true := by decide +kernel
theorem subd17_1_787 : subd17_1 [1, -1, 1] = true := by decide +kernel
theorem subd17_1_788 : subd17_1 [1, -1, 2] = true := by decide +kernel
theorem subd17_1_789 : subd17_1 [1, -1, 3] = true := by decide +kernel
theorem subd17_1_790 : subd17_1 [1, -1, 4] = true := by decide +kernel
theorem subd17_1_791 : subd17_1 [1, -1, 5] = true := by decide +kernel
theorem subd17_1_792 : subd17_1 [1, -1, 6] = true := by decide +kernel
theorem subd17_1_793 : subd17_1 [1, -1, 7] = true := by decide +kernel
theorem subd17_1_794 : subd17_1 [1, -1, 8] = true := by decide +kernel
theorem subd17_1_795 : subd17_1 [1, -1, 9] = true := by decide +kernel
theorem subd17_1_796 : subd17_1 [1, 0, -9] = true := by decide +kernel
theorem subd17_1_797 : subd17_1 [1, 0, -8] = true := by decide +kernel
theorem subd17_1_798 : subd17_1 [1, 0, -7] = true := by decide +kernel
theorem subd17_1_799 : subd17_1 [1, 0, -6] = true := by decide +kernel
theorem sbd17_1_24 : ∀ q ∈ blkd17_1_24, subd17_1 q = true := by
  unfold blkd17_1_24
  exact List.forall_mem_cons.2 ⟨subd17_1_768, List.forall_mem_cons.2 ⟨subd17_1_769, List.forall_mem_cons.2 ⟨subd17_1_770, List.forall_mem_cons.2 ⟨subd17_1_771, List.forall_mem_cons.2 ⟨subd17_1_772, List.forall_mem_cons.2 ⟨subd17_1_773, List.forall_mem_cons.2 ⟨subd17_1_774, List.forall_mem_cons.2 ⟨subd17_1_775, List.forall_mem_cons.2 ⟨subd17_1_776, List.forall_mem_cons.2 ⟨subd17_1_777, List.forall_mem_cons.2 ⟨subd17_1_778, List.forall_mem_cons.2 ⟨subd17_1_779, List.forall_mem_cons.2 ⟨subd17_1_780, List.forall_mem_cons.2 ⟨subd17_1_781, List.forall_mem_cons.2 ⟨subd17_1_782, List.forall_mem_cons.2 ⟨subd17_1_783, List.forall_mem_cons.2 ⟨subd17_1_784, List.forall_mem_cons.2 ⟨subd17_1_785, List.forall_mem_cons.2 ⟨subd17_1_786, List.forall_mem_cons.2 ⟨subd17_1_787, List.forall_mem_cons.2 ⟨subd17_1_788, List.forall_mem_cons.2 ⟨subd17_1_789, List.forall_mem_cons.2 ⟨subd17_1_790, List.forall_mem_cons.2 ⟨subd17_1_791, List.forall_mem_cons.2 ⟨subd17_1_792, List.forall_mem_cons.2 ⟨subd17_1_793, List.forall_mem_cons.2 ⟨subd17_1_794, List.forall_mem_cons.2 ⟨subd17_1_795, List.forall_mem_cons.2 ⟨subd17_1_796, List.forall_mem_cons.2 ⟨subd17_1_797, List.forall_mem_cons.2 ⟨subd17_1_798, List.forall_mem_cons.2 ⟨subd17_1_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_800 : subd17_1 [1, 0, -5] = true := by decide +kernel
theorem subd17_1_801 : subd17_1 [1, 0, -4] = true := by decide +kernel
theorem subd17_1_802 : subd17_1 [1, 0, -3] = true := by decide +kernel
theorem subd17_1_803 : subd17_1 [1, 0, -2] = true := by decide +kernel
theorem subd17_1_804 : subd17_1 [1, 0, -1] = true := by decide +kernel
theorem subd17_1_805 : subd17_1 [1, 0, 0] = true := by decide +kernel
theorem subd17_1_806 : subd17_1 [1, 0, 1] = true := by decide +kernel
theorem subd17_1_807 : subd17_1 [1, 0, 2] = true := by decide +kernel
theorem subd17_1_808 : subd17_1 [1, 0, 3] = true := by decide +kernel
theorem subd17_1_809 : subd17_1 [1, 0, 4] = true := by decide +kernel
theorem subd17_1_810 : subd17_1 [1, 0, 5] = true := by decide +kernel
theorem subd17_1_811 : subd17_1 [1, 0, 6] = true := by decide +kernel
theorem subd17_1_812 : subd17_1 [1, 0, 7] = true := by decide +kernel
theorem subd17_1_813 : subd17_1 [1, 0, 8] = true := by decide +kernel
theorem subd17_1_814 : subd17_1 [1, 0, 9] = true := by decide +kernel
theorem subd17_1_815 : subd17_1 [1, 1, -9] = true := by decide +kernel
theorem subd17_1_816 : subd17_1 [1, 1, -8] = true := by decide +kernel
theorem subd17_1_817 : subd17_1 [1, 1, -7] = true := by decide +kernel
theorem subd17_1_818 : subd17_1 [1, 1, -6] = true := by decide +kernel
theorem subd17_1_819 : subd17_1 [1, 1, -5] = true := by decide +kernel
theorem subd17_1_820 : subd17_1 [1, 1, -4] = true := by decide +kernel
theorem subd17_1_821 : subd17_1 [1, 1, -3] = true := by decide +kernel
theorem subd17_1_822 : subd17_1 [1, 1, -2] = true := by decide +kernel
theorem subd17_1_823 : subd17_1 [1, 1, -1] = true := by decide +kernel
theorem subd17_1_824 : subd17_1 [1, 1, 0] = true := by decide +kernel
theorem subd17_1_825 : subd17_1 [1, 1, 1] = true := by decide +kernel
theorem subd17_1_826 : subd17_1 [1, 1, 2] = true := by decide +kernel
theorem subd17_1_827 : subd17_1 [1, 1, 3] = true := by decide +kernel
theorem subd17_1_828 : subd17_1 [1, 1, 4] = true := by decide +kernel
theorem subd17_1_829 : subd17_1 [1, 1, 5] = true := by decide +kernel
theorem subd17_1_830 : subd17_1 [1, 1, 6] = true := by decide +kernel
theorem subd17_1_831 : subd17_1 [1, 1, 7] = true := by decide +kernel
theorem sbd17_1_25 : ∀ q ∈ blkd17_1_25, subd17_1 q = true := by
  unfold blkd17_1_25
  exact List.forall_mem_cons.2 ⟨subd17_1_800, List.forall_mem_cons.2 ⟨subd17_1_801, List.forall_mem_cons.2 ⟨subd17_1_802, List.forall_mem_cons.2 ⟨subd17_1_803, List.forall_mem_cons.2 ⟨subd17_1_804, List.forall_mem_cons.2 ⟨subd17_1_805, List.forall_mem_cons.2 ⟨subd17_1_806, List.forall_mem_cons.2 ⟨subd17_1_807, List.forall_mem_cons.2 ⟨subd17_1_808, List.forall_mem_cons.2 ⟨subd17_1_809, List.forall_mem_cons.2 ⟨subd17_1_810, List.forall_mem_cons.2 ⟨subd17_1_811, List.forall_mem_cons.2 ⟨subd17_1_812, List.forall_mem_cons.2 ⟨subd17_1_813, List.forall_mem_cons.2 ⟨subd17_1_814, List.forall_mem_cons.2 ⟨subd17_1_815, List.forall_mem_cons.2 ⟨subd17_1_816, List.forall_mem_cons.2 ⟨subd17_1_817, List.forall_mem_cons.2 ⟨subd17_1_818, List.forall_mem_cons.2 ⟨subd17_1_819, List.forall_mem_cons.2 ⟨subd17_1_820, List.forall_mem_cons.2 ⟨subd17_1_821, List.forall_mem_cons.2 ⟨subd17_1_822, List.forall_mem_cons.2 ⟨subd17_1_823, List.forall_mem_cons.2 ⟨subd17_1_824, List.forall_mem_cons.2 ⟨subd17_1_825, List.forall_mem_cons.2 ⟨subd17_1_826, List.forall_mem_cons.2 ⟨subd17_1_827, List.forall_mem_cons.2 ⟨subd17_1_828, List.forall_mem_cons.2 ⟨subd17_1_829, List.forall_mem_cons.2 ⟨subd17_1_830, List.forall_mem_cons.2 ⟨subd17_1_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_832 : subd17_1 [1, 1, 8] = true := by decide +kernel
theorem subd17_1_833 : subd17_1 [1, 2, -8] = true := by decide +kernel
theorem subd17_1_834 : subd17_1 [1, 2, -7] = true := by decide +kernel
theorem subd17_1_835 : subd17_1 [1, 2, -6] = true := by decide +kernel
theorem subd17_1_836 : subd17_1 [1, 2, -5] = true := by decide +kernel
theorem subd17_1_837 : subd17_1 [1, 2, -4] = true := by decide +kernel
theorem subd17_1_838 : subd17_1 [1, 2, -3] = true := by decide +kernel
theorem subd17_1_839 : subd17_1 [1, 2, -2] = true := by decide +kernel
theorem subd17_1_840 : subd17_1 [1, 2, -1] = true := by decide +kernel
theorem subd17_1_841 : subd17_1 [1, 2, 0] = true := by decide +kernel
theorem subd17_1_842 : subd17_1 [1, 2, 1] = true := by decide +kernel
theorem subd17_1_843 : subd17_1 [1, 2, 2] = true := by decide +kernel
theorem subd17_1_844 : subd17_1 [1, 2, 3] = true := by decide +kernel
theorem subd17_1_845 : subd17_1 [1, 2, 4] = true := by decide +kernel
theorem subd17_1_846 : subd17_1 [1, 2, 5] = true := by decide +kernel
theorem subd17_1_847 : subd17_1 [1, 2, 6] = true := by decide +kernel
theorem subd17_1_848 : subd17_1 [1, 2, 7] = true := by decide +kernel
theorem subd17_1_849 : subd17_1 [1, 2, 8] = true := by decide +kernel
theorem subd17_1_850 : subd17_1 [1, 3, -8] = true := by decide +kernel
theorem subd17_1_851 : subd17_1 [1, 3, -7] = true := by decide +kernel
theorem subd17_1_852 : subd17_1 [1, 3, -6] = true := by decide +kernel
theorem subd17_1_853 : subd17_1 [1, 3, -5] = true := by decide +kernel
theorem subd17_1_854 : subd17_1 [1, 3, -4] = true := by decide +kernel
theorem subd17_1_855 : subd17_1 [1, 3, -3] = true := by decide +kernel
theorem subd17_1_856 : subd17_1 [1, 3, -2] = true := by decide +kernel
theorem subd17_1_857 : subd17_1 [1, 3, -1] = true := by decide +kernel
theorem subd17_1_858 : subd17_1 [1, 3, 0] = true := by decide +kernel
theorem subd17_1_859 : subd17_1 [1, 3, 1] = true := by decide +kernel
theorem subd17_1_860 : subd17_1 [1, 3, 2] = true := by decide +kernel
theorem subd17_1_861 : subd17_1 [1, 3, 3] = true := by decide +kernel
theorem subd17_1_862 : subd17_1 [1, 3, 4] = true := by decide +kernel
theorem subd17_1_863 : subd17_1 [1, 3, 5] = true := by decide +kernel
theorem sbd17_1_26 : ∀ q ∈ blkd17_1_26, subd17_1 q = true := by
  unfold blkd17_1_26
  exact List.forall_mem_cons.2 ⟨subd17_1_832, List.forall_mem_cons.2 ⟨subd17_1_833, List.forall_mem_cons.2 ⟨subd17_1_834, List.forall_mem_cons.2 ⟨subd17_1_835, List.forall_mem_cons.2 ⟨subd17_1_836, List.forall_mem_cons.2 ⟨subd17_1_837, List.forall_mem_cons.2 ⟨subd17_1_838, List.forall_mem_cons.2 ⟨subd17_1_839, List.forall_mem_cons.2 ⟨subd17_1_840, List.forall_mem_cons.2 ⟨subd17_1_841, List.forall_mem_cons.2 ⟨subd17_1_842, List.forall_mem_cons.2 ⟨subd17_1_843, List.forall_mem_cons.2 ⟨subd17_1_844, List.forall_mem_cons.2 ⟨subd17_1_845, List.forall_mem_cons.2 ⟨subd17_1_846, List.forall_mem_cons.2 ⟨subd17_1_847, List.forall_mem_cons.2 ⟨subd17_1_848, List.forall_mem_cons.2 ⟨subd17_1_849, List.forall_mem_cons.2 ⟨subd17_1_850, List.forall_mem_cons.2 ⟨subd17_1_851, List.forall_mem_cons.2 ⟨subd17_1_852, List.forall_mem_cons.2 ⟨subd17_1_853, List.forall_mem_cons.2 ⟨subd17_1_854, List.forall_mem_cons.2 ⟨subd17_1_855, List.forall_mem_cons.2 ⟨subd17_1_856, List.forall_mem_cons.2 ⟨subd17_1_857, List.forall_mem_cons.2 ⟨subd17_1_858, List.forall_mem_cons.2 ⟨subd17_1_859, List.forall_mem_cons.2 ⟨subd17_1_860, List.forall_mem_cons.2 ⟨subd17_1_861, List.forall_mem_cons.2 ⟨subd17_1_862, List.forall_mem_cons.2 ⟨subd17_1_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_864 : subd17_1 [1, 3, 6] = true := by decide +kernel
theorem subd17_1_865 : subd17_1 [1, 3, 7] = true := by decide +kernel
theorem subd17_1_866 : subd17_1 [1, 4, -7] = true := by decide +kernel
theorem subd17_1_867 : subd17_1 [1, 4, -6] = true := by decide +kernel
theorem subd17_1_868 : subd17_1 [1, 4, -5] = true := by decide +kernel
theorem subd17_1_869 : subd17_1 [1, 4, -4] = true := by decide +kernel
theorem subd17_1_870 : subd17_1 [1, 4, -3] = true := by decide +kernel
theorem subd17_1_871 : subd17_1 [1, 4, -2] = true := by decide +kernel
theorem subd17_1_872 : subd17_1 [1, 4, -1] = true := by decide +kernel
theorem subd17_1_873 : subd17_1 [1, 4, 0] = true := by decide +kernel
theorem subd17_1_874 : subd17_1 [1, 4, 1] = true := by decide +kernel
theorem subd17_1_875 : subd17_1 [1, 4, 2] = true := by decide +kernel
theorem subd17_1_876 : subd17_1 [1, 4, 3] = true := by decide +kernel
theorem subd17_1_877 : subd17_1 [1, 4, 4] = true := by decide +kernel
theorem subd17_1_878 : subd17_1 [1, 4, 5] = true := by decide +kernel
theorem subd17_1_879 : subd17_1 [1, 4, 6] = true := by decide +kernel
theorem subd17_1_880 : subd17_1 [1, 4, 7] = true := by decide +kernel
theorem subd17_1_881 : subd17_1 [1, 5] = true := by decide +kernel
theorem subd17_1_882 : subd17_1 [1, 6] = true := by decide +kernel
theorem subd17_1_883 : subd17_1 [2, -8] = true := by decide +kernel
theorem subd17_1_884 : subd17_1 [2, -7] = true := by decide +kernel
theorem subd17_1_885 : subd17_1 [2, -6] = true := by decide +kernel
theorem subd17_1_886 : subd17_1 [2, -5, -6] = true := by decide +kernel
theorem subd17_1_887 : subd17_1 [2, -5, -5] = true := by decide +kernel
theorem subd17_1_888 : subd17_1 [2, -5, -4] = true := by decide +kernel
theorem subd17_1_889 : subd17_1 [2, -5, -3] = true := by decide +kernel
theorem subd17_1_890 : subd17_1 [2, -5, -2] = true := by decide +kernel
theorem subd17_1_891 : subd17_1 [2, -5, -1] = true := by decide +kernel
theorem subd17_1_892 : subd17_1 [2, -5, 0] = true := by decide +kernel
theorem subd17_1_893 : subd17_1 [2, -5, 1] = true := by decide +kernel
theorem subd17_1_894 : subd17_1 [2, -5, 2] = true := by decide +kernel
theorem subd17_1_895 : subd17_1 [2, -5, 3] = true := by decide +kernel
theorem sbd17_1_27 : ∀ q ∈ blkd17_1_27, subd17_1 q = true := by
  unfold blkd17_1_27
  exact List.forall_mem_cons.2 ⟨subd17_1_864, List.forall_mem_cons.2 ⟨subd17_1_865, List.forall_mem_cons.2 ⟨subd17_1_866, List.forall_mem_cons.2 ⟨subd17_1_867, List.forall_mem_cons.2 ⟨subd17_1_868, List.forall_mem_cons.2 ⟨subd17_1_869, List.forall_mem_cons.2 ⟨subd17_1_870, List.forall_mem_cons.2 ⟨subd17_1_871, List.forall_mem_cons.2 ⟨subd17_1_872, List.forall_mem_cons.2 ⟨subd17_1_873, List.forall_mem_cons.2 ⟨subd17_1_874, List.forall_mem_cons.2 ⟨subd17_1_875, List.forall_mem_cons.2 ⟨subd17_1_876, List.forall_mem_cons.2 ⟨subd17_1_877, List.forall_mem_cons.2 ⟨subd17_1_878, List.forall_mem_cons.2 ⟨subd17_1_879, List.forall_mem_cons.2 ⟨subd17_1_880, List.forall_mem_cons.2 ⟨subd17_1_881, List.forall_mem_cons.2 ⟨subd17_1_882, List.forall_mem_cons.2 ⟨subd17_1_883, List.forall_mem_cons.2 ⟨subd17_1_884, List.forall_mem_cons.2 ⟨subd17_1_885, List.forall_mem_cons.2 ⟨subd17_1_886, List.forall_mem_cons.2 ⟨subd17_1_887, List.forall_mem_cons.2 ⟨subd17_1_888, List.forall_mem_cons.2 ⟨subd17_1_889, List.forall_mem_cons.2 ⟨subd17_1_890, List.forall_mem_cons.2 ⟨subd17_1_891, List.forall_mem_cons.2 ⟨subd17_1_892, List.forall_mem_cons.2 ⟨subd17_1_893, List.forall_mem_cons.2 ⟨subd17_1_894, List.forall_mem_cons.2 ⟨subd17_1_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
