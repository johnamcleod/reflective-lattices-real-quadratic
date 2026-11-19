import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_0_416 : subd9_0 [0, 1, 2] = true := by decide +kernel
theorem subd9_0_417 : subd9_0 [0, 1, 3] = true := by decide +kernel
theorem subd9_0_418 : subd9_0 [0, 1, 4] = true := by decide +kernel
theorem subd9_0_419 : subd9_0 [0, 1, 5] = true := by decide +kernel
theorem subd9_0_420 : subd9_0 [0, 1, 6] = true := by decide +kernel
theorem subd9_0_421 : subd9_0 [0, 1, 7] = true := by decide +kernel
theorem subd9_0_422 : subd9_0 [0, 1, 8] = true := by decide +kernel
theorem subd9_0_423 : subd9_0 [0, 1, 9] = true := by decide +kernel
theorem subd9_0_424 : subd9_0 [0, 2, -10] = true := by decide +kernel
theorem subd9_0_425 : subd9_0 [0, 2, -9] = true := by decide +kernel
theorem subd9_0_426 : subd9_0 [0, 2, -8] = true := by decide +kernel
theorem subd9_0_427 : subd9_0 [0, 2, -7] = true := by decide +kernel
theorem subd9_0_428 : subd9_0 [0, 2, -6] = true := by decide +kernel
theorem subd9_0_429 : subd9_0 [0, 2, -5] = true := by decide +kernel
theorem subd9_0_430 : subd9_0 [0, 2, -4] = true := by decide +kernel
theorem subd9_0_431 : subd9_0 [0, 2, -3] = true := by decide +kernel
theorem subd9_0_432 : subd9_0 [0, 2, -2] = true := by decide +kernel
theorem subd9_0_433 : subd9_0 [0, 2, -1] = true := by decide +kernel
theorem subd9_0_434 : subd9_0 [0, 2, 0] = true := by decide +kernel
theorem subd9_0_435 : subd9_0 [0, 2, 1] = true := by decide +kernel
theorem subd9_0_436 : subd9_0 [0, 2, 2] = true := by decide +kernel
theorem subd9_0_437 : subd9_0 [0, 2, 3] = true := by decide +kernel
theorem subd9_0_438 : subd9_0 [0, 2, 4] = true := by decide +kernel
theorem subd9_0_439 : subd9_0 [0, 2, 5] = true := by decide +kernel
theorem subd9_0_440 : subd9_0 [0, 2, 6] = true := by decide +kernel
theorem subd9_0_441 : subd9_0 [0, 2, 7] = true := by decide +kernel
theorem subd9_0_442 : subd9_0 [0, 2, 8] = true := by decide +kernel
theorem subd9_0_443 : subd9_0 [0, 2, 9] = true := by decide +kernel
theorem subd9_0_444 : subd9_0 [0, 3, -8] = true := by decide +kernel
theorem subd9_0_445 : subd9_0 [0, 3, -7] = true := by decide +kernel
theorem subd9_0_446 : subd9_0 [0, 3, -6] = true := by decide +kernel
theorem subd9_0_447 : subd9_0 [0, 3, -5] = true := by decide +kernel
theorem sbd9_0_13 : ∀ q ∈ blkd9_0_13, subd9_0 q = true := by
  unfold blkd9_0_13
  exact List.forall_mem_cons.2 ⟨subd9_0_416, List.forall_mem_cons.2 ⟨subd9_0_417, List.forall_mem_cons.2 ⟨subd9_0_418, List.forall_mem_cons.2 ⟨subd9_0_419, List.forall_mem_cons.2 ⟨subd9_0_420, List.forall_mem_cons.2 ⟨subd9_0_421, List.forall_mem_cons.2 ⟨subd9_0_422, List.forall_mem_cons.2 ⟨subd9_0_423, List.forall_mem_cons.2 ⟨subd9_0_424, List.forall_mem_cons.2 ⟨subd9_0_425, List.forall_mem_cons.2 ⟨subd9_0_426, List.forall_mem_cons.2 ⟨subd9_0_427, List.forall_mem_cons.2 ⟨subd9_0_428, List.forall_mem_cons.2 ⟨subd9_0_429, List.forall_mem_cons.2 ⟨subd9_0_430, List.forall_mem_cons.2 ⟨subd9_0_431, List.forall_mem_cons.2 ⟨subd9_0_432, List.forall_mem_cons.2 ⟨subd9_0_433, List.forall_mem_cons.2 ⟨subd9_0_434, List.forall_mem_cons.2 ⟨subd9_0_435, List.forall_mem_cons.2 ⟨subd9_0_436, List.forall_mem_cons.2 ⟨subd9_0_437, List.forall_mem_cons.2 ⟨subd9_0_438, List.forall_mem_cons.2 ⟨subd9_0_439, List.forall_mem_cons.2 ⟨subd9_0_440, List.forall_mem_cons.2 ⟨subd9_0_441, List.forall_mem_cons.2 ⟨subd9_0_442, List.forall_mem_cons.2 ⟨subd9_0_443, List.forall_mem_cons.2 ⟨subd9_0_444, List.forall_mem_cons.2 ⟨subd9_0_445, List.forall_mem_cons.2 ⟨subd9_0_446, List.forall_mem_cons.2 ⟨subd9_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_448 : subd9_0 [0, 3, -4] = true := by decide +kernel
theorem subd9_0_449 : subd9_0 [0, 3, -3] = true := by decide +kernel
theorem subd9_0_450 : subd9_0 [0, 3, -2] = true := by decide +kernel
theorem subd9_0_451 : subd9_0 [0, 3, -1] = true := by decide +kernel
theorem subd9_0_452 : subd9_0 [0, 3, 0] = true := by decide +kernel
theorem subd9_0_453 : subd9_0 [0, 3, 1] = true := by decide +kernel
theorem subd9_0_454 : subd9_0 [0, 3, 2] = true := by decide +kernel
theorem subd9_0_455 : subd9_0 [0, 3, 3] = true := by decide +kernel
theorem subd9_0_456 : subd9_0 [0, 3, 4] = true := by decide +kernel
theorem subd9_0_457 : subd9_0 [0, 3, 5] = true := by decide +kernel
theorem subd9_0_458 : subd9_0 [0, 3, 6] = true := by decide +kernel
theorem subd9_0_459 : subd9_0 [0, 3, 7] = true := by decide +kernel
theorem subd9_0_460 : subd9_0 [0, 4] = true := by decide +kernel
theorem subd9_0_461 : subd9_0 [1, -5] = true := by decide +kernel
theorem subd9_0_462 : subd9_0 [1, -4] = true := by decide +kernel
theorem subd9_0_463 : subd9_0 [1, -3, -8] = true := by decide +kernel
theorem subd9_0_464 : subd9_0 [1, -3, -7] = true := by decide +kernel
theorem subd9_0_465 : subd9_0 [1, -3, -6] = true := by decide +kernel
theorem subd9_0_466 : subd9_0 [1, -3, -5] = true := by decide +kernel
theorem subd9_0_467 : subd9_0 [1, -3, -4] = true := by decide +kernel
theorem subd9_0_468 : subd9_0 [1, -3, -3] = true := by decide +kernel
theorem subd9_0_469 : subd9_0 [1, -3, -2] = true := by decide +kernel
theorem subd9_0_470 : subd9_0 [1, -3, -1] = true := by decide +kernel
theorem subd9_0_471 : subd9_0 [1, -3, 0] = true := by decide +kernel
theorem subd9_0_472 : subd9_0 [1, -3, 1] = true := by decide +kernel
theorem subd9_0_473 : subd9_0 [1, -3, 2] = true := by decide +kernel
theorem subd9_0_474 : subd9_0 [1, -3, 3] = true := by decide +kernel
theorem subd9_0_475 : subd9_0 [1, -3, 4] = true := by decide +kernel
theorem subd9_0_476 : subd9_0 [1, -3, 5] = true := by decide +kernel
theorem subd9_0_477 : subd9_0 [1, -3, 6] = true := by decide +kernel
theorem subd9_0_478 : subd9_0 [1, -3, 7] = true := by decide +kernel
theorem subd9_0_479 : subd9_0 [1, -2, -10] = true := by decide +kernel
theorem sbd9_0_14 : ∀ q ∈ blkd9_0_14, subd9_0 q = true := by
  unfold blkd9_0_14
  exact List.forall_mem_cons.2 ⟨subd9_0_448, List.forall_mem_cons.2 ⟨subd9_0_449, List.forall_mem_cons.2 ⟨subd9_0_450, List.forall_mem_cons.2 ⟨subd9_0_451, List.forall_mem_cons.2 ⟨subd9_0_452, List.forall_mem_cons.2 ⟨subd9_0_453, List.forall_mem_cons.2 ⟨subd9_0_454, List.forall_mem_cons.2 ⟨subd9_0_455, List.forall_mem_cons.2 ⟨subd9_0_456, List.forall_mem_cons.2 ⟨subd9_0_457, List.forall_mem_cons.2 ⟨subd9_0_458, List.forall_mem_cons.2 ⟨subd9_0_459, List.forall_mem_cons.2 ⟨subd9_0_460, List.forall_mem_cons.2 ⟨subd9_0_461, List.forall_mem_cons.2 ⟨subd9_0_462, List.forall_mem_cons.2 ⟨subd9_0_463, List.forall_mem_cons.2 ⟨subd9_0_464, List.forall_mem_cons.2 ⟨subd9_0_465, List.forall_mem_cons.2 ⟨subd9_0_466, List.forall_mem_cons.2 ⟨subd9_0_467, List.forall_mem_cons.2 ⟨subd9_0_468, List.forall_mem_cons.2 ⟨subd9_0_469, List.forall_mem_cons.2 ⟨subd9_0_470, List.forall_mem_cons.2 ⟨subd9_0_471, List.forall_mem_cons.2 ⟨subd9_0_472, List.forall_mem_cons.2 ⟨subd9_0_473, List.forall_mem_cons.2 ⟨subd9_0_474, List.forall_mem_cons.2 ⟨subd9_0_475, List.forall_mem_cons.2 ⟨subd9_0_476, List.forall_mem_cons.2 ⟨subd9_0_477, List.forall_mem_cons.2 ⟨subd9_0_478, List.forall_mem_cons.2 ⟨subd9_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_480 : subd9_0 [1, -2, -9] = true := by decide +kernel
theorem subd9_0_481 : subd9_0 [1, -2, -8] = true := by decide +kernel
theorem subd9_0_482 : subd9_0 [1, -2, -7] = true := by decide +kernel
theorem subd9_0_483 : subd9_0 [1, -2, -6] = true := by decide +kernel
theorem subd9_0_484 : subd9_0 [1, -2, -5] = true := by decide +kernel
theorem subd9_0_485 : subd9_0 [1, -2, -4] = true := by decide +kernel
theorem subd9_0_486 : subd9_0 [1, -2, -3] = true := by decide +kernel
theorem subd9_0_487 : subd9_0 [1, -2, -2] = true := by decide +kernel
theorem subd9_0_488 : subd9_0 [1, -2, -1] = true := by decide +kernel
theorem subd9_0_489 : subd9_0 [1, -2, 0] = true := by decide +kernel
theorem subd9_0_490 : subd9_0 [1, -2, 1] = true := by decide +kernel
theorem subd9_0_491 : subd9_0 [1, -2, 2] = true := by decide +kernel
theorem subd9_0_492 : subd9_0 [1, -2, 3] = true := by decide +kernel
theorem subd9_0_493 : subd9_0 [1, -2, 4] = true := by decide +kernel
theorem subd9_0_494 : subd9_0 [1, -2, 5] = true := by decide +kernel
theorem subd9_0_495 : subd9_0 [1, -2, 6] = true := by decide +kernel
theorem subd9_0_496 : subd9_0 [1, -2, 7] = true := by decide +kernel
theorem subd9_0_497 : subd9_0 [1, -2, 8] = true := by decide +kernel
theorem subd9_0_498 : subd9_0 [1, -1, -11] = true := by decide +kernel
theorem subd9_0_499 : subd9_0 [1, -1, -10] = true := by decide +kernel
theorem subd9_0_500 : subd9_0 [1, -1, -9] = true := by decide +kernel
theorem subd9_0_501 : subd9_0 [1, -1, -8] = true := by decide +kernel
theorem subd9_0_502 : subd9_0 [1, -1, -7] = true := by decide +kernel
theorem subd9_0_503 : subd9_0 [1, -1, -6] = true := by decide +kernel
theorem subd9_0_504 : subd9_0 [1, -1, -5] = true := by decide +kernel
theorem subd9_0_505 : subd9_0 [1, -1, -4] = true := by decide +kernel
theorem subd9_0_506 : subd9_0 [1, -1, -3] = true := by decide +kernel
theorem subd9_0_507 : subd9_0 [1, -1, -2] = true := by decide +kernel
theorem subd9_0_508 : subd9_0 [1, -1, -1] = true := by decide +kernel
theorem subd9_0_509 : subd9_0 [1, -1, 0] = true := by decide +kernel
theorem subd9_0_510 : subd9_0 [1, -1, 1] = true := by decide +kernel
theorem subd9_0_511 : subd9_0 [1, -1, 2] = true := by decide +kernel
theorem sbd9_0_15 : ∀ q ∈ blkd9_0_15, subd9_0 q = true := by
  unfold blkd9_0_15
  exact List.forall_mem_cons.2 ⟨subd9_0_480, List.forall_mem_cons.2 ⟨subd9_0_481, List.forall_mem_cons.2 ⟨subd9_0_482, List.forall_mem_cons.2 ⟨subd9_0_483, List.forall_mem_cons.2 ⟨subd9_0_484, List.forall_mem_cons.2 ⟨subd9_0_485, List.forall_mem_cons.2 ⟨subd9_0_486, List.forall_mem_cons.2 ⟨subd9_0_487, List.forall_mem_cons.2 ⟨subd9_0_488, List.forall_mem_cons.2 ⟨subd9_0_489, List.forall_mem_cons.2 ⟨subd9_0_490, List.forall_mem_cons.2 ⟨subd9_0_491, List.forall_mem_cons.2 ⟨subd9_0_492, List.forall_mem_cons.2 ⟨subd9_0_493, List.forall_mem_cons.2 ⟨subd9_0_494, List.forall_mem_cons.2 ⟨subd9_0_495, List.forall_mem_cons.2 ⟨subd9_0_496, List.forall_mem_cons.2 ⟨subd9_0_497, List.forall_mem_cons.2 ⟨subd9_0_498, List.forall_mem_cons.2 ⟨subd9_0_499, List.forall_mem_cons.2 ⟨subd9_0_500, List.forall_mem_cons.2 ⟨subd9_0_501, List.forall_mem_cons.2 ⟨subd9_0_502, List.forall_mem_cons.2 ⟨subd9_0_503, List.forall_mem_cons.2 ⟨subd9_0_504, List.forall_mem_cons.2 ⟨subd9_0_505, List.forall_mem_cons.2 ⟨subd9_0_506, List.forall_mem_cons.2 ⟨subd9_0_507, List.forall_mem_cons.2 ⟨subd9_0_508, List.forall_mem_cons.2 ⟨subd9_0_509, List.forall_mem_cons.2 ⟨subd9_0_510, List.forall_mem_cons.2 ⟨subd9_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_512 : subd9_0 [1, -1, 3] = true := by decide +kernel
theorem subd9_0_513 : subd9_0 [1, -1, 4] = true := by decide +kernel
theorem subd9_0_514 : subd9_0 [1, -1, 5] = true := by decide +kernel
theorem subd9_0_515 : subd9_0 [1, -1, 6] = true := by decide +kernel
theorem subd9_0_516 : subd9_0 [1, -1, 7] = true := by decide +kernel
theorem subd9_0_517 : subd9_0 [1, -1, 8] = true := by decide +kernel
theorem subd9_0_518 : subd9_0 [1, -1, 9] = true := by decide +kernel
theorem subd9_0_519 : subd9_0 [1, 0, -11] = true := by decide +kernel
theorem subd9_0_520 : subd9_0 [1, 0, -10] = true := by decide +kernel
theorem subd9_0_521 : subd9_0 [1, 0, -9] = true := by decide +kernel
theorem subd9_0_522 : subd9_0 [1, 0, -8] = true := by decide +kernel
theorem subd9_0_523 : subd9_0 [1, 0, -7] = true := by decide +kernel
theorem subd9_0_524 : subd9_0 [1, 0, -6] = true := by decide +kernel
theorem subd9_0_525 : subd9_0 [1, 0, -5] = true := by decide +kernel
theorem subd9_0_526 : subd9_0 [1, 0, -4] = true := by decide +kernel
theorem subd9_0_527 : subd9_0 [1, 0, -3] = true := by decide +kernel
theorem subd9_0_528 : subd9_0 [1, 0, -2] = true := by decide +kernel
theorem subd9_0_529 : subd9_0 [1, 0, -1] = true := by decide +kernel
theorem subd9_0_530 : subd9_0 [1, 0, 0] = true := by decide +kernel
theorem subd9_0_531 : subd9_0 [1, 0, 1] = true := by decide +kernel
theorem subd9_0_532 : subd9_0 [1, 0, 2] = true := by decide +kernel
theorem subd9_0_533 : subd9_0 [1, 0, 3] = true := by decide +kernel
theorem subd9_0_534 : subd9_0 [1, 0, 4] = true := by decide +kernel
theorem subd9_0_535 : subd9_0 [1, 0, 5] = true := by decide +kernel
theorem subd9_0_536 : subd9_0 [1, 0, 6] = true := by decide +kernel
theorem subd9_0_537 : subd9_0 [1, 0, 7] = true := by decide +kernel
theorem subd9_0_538 : subd9_0 [1, 0, 8] = true := by decide +kernel
theorem subd9_0_539 : subd9_0 [1, 0, 9] = true := by decide +kernel
theorem subd9_0_540 : subd9_0 [1, 1, -11] = true := by decide +kernel
theorem subd9_0_541 : subd9_0 [1, 1, -10] = true := by decide +kernel
theorem subd9_0_542 : subd9_0 [1, 1, -9] = true := by decide +kernel
theorem subd9_0_543 : subd9_0 [1, 1, -8] = true := by decide +kernel
theorem sbd9_0_16 : ∀ q ∈ blkd9_0_16, subd9_0 q = true := by
  unfold blkd9_0_16
  exact List.forall_mem_cons.2 ⟨subd9_0_512, List.forall_mem_cons.2 ⟨subd9_0_513, List.forall_mem_cons.2 ⟨subd9_0_514, List.forall_mem_cons.2 ⟨subd9_0_515, List.forall_mem_cons.2 ⟨subd9_0_516, List.forall_mem_cons.2 ⟨subd9_0_517, List.forall_mem_cons.2 ⟨subd9_0_518, List.forall_mem_cons.2 ⟨subd9_0_519, List.forall_mem_cons.2 ⟨subd9_0_520, List.forall_mem_cons.2 ⟨subd9_0_521, List.forall_mem_cons.2 ⟨subd9_0_522, List.forall_mem_cons.2 ⟨subd9_0_523, List.forall_mem_cons.2 ⟨subd9_0_524, List.forall_mem_cons.2 ⟨subd9_0_525, List.forall_mem_cons.2 ⟨subd9_0_526, List.forall_mem_cons.2 ⟨subd9_0_527, List.forall_mem_cons.2 ⟨subd9_0_528, List.forall_mem_cons.2 ⟨subd9_0_529, List.forall_mem_cons.2 ⟨subd9_0_530, List.forall_mem_cons.2 ⟨subd9_0_531, List.forall_mem_cons.2 ⟨subd9_0_532, List.forall_mem_cons.2 ⟨subd9_0_533, List.forall_mem_cons.2 ⟨subd9_0_534, List.forall_mem_cons.2 ⟨subd9_0_535, List.forall_mem_cons.2 ⟨subd9_0_536, List.forall_mem_cons.2 ⟨subd9_0_537, List.forall_mem_cons.2 ⟨subd9_0_538, List.forall_mem_cons.2 ⟨subd9_0_539, List.forall_mem_cons.2 ⟨subd9_0_540, List.forall_mem_cons.2 ⟨subd9_0_541, List.forall_mem_cons.2 ⟨subd9_0_542, List.forall_mem_cons.2 ⟨subd9_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_544 : subd9_0 [1, 1, -7] = true := by decide +kernel
theorem subd9_0_545 : subd9_0 [1, 1, -6] = true := by decide +kernel
theorem subd9_0_546 : subd9_0 [1, 1, -5] = true := by decide +kernel
theorem subd9_0_547 : subd9_0 [1, 1, -4] = true := by decide +kernel
theorem subd9_0_548 : subd9_0 [1, 1, -3] = true := by decide +kernel
theorem subd9_0_549 : subd9_0 [1, 1, -2] = true := by decide +kernel
theorem subd9_0_550 : subd9_0 [1, 1, -1] = true := by decide +kernel
theorem subd9_0_551 : subd9_0 [1, 1, 0] = true := by decide +kernel
theorem subd9_0_552 : subd9_0 [1, 1, 1] = true := by decide +kernel
theorem subd9_0_553 : subd9_0 [1, 1, 2] = true := by decide +kernel
theorem subd9_0_554 : subd9_0 [1, 1, 3] = true := by decide +kernel
theorem subd9_0_555 : subd9_0 [1, 1, 4] = true := by decide +kernel
theorem subd9_0_556 : subd9_0 [1, 1, 5] = true := by decide +kernel
theorem subd9_0_557 : subd9_0 [1, 1, 6] = true := by decide +kernel
theorem subd9_0_558 : subd9_0 [1, 1, 7] = true := by decide +kernel
theorem subd9_0_559 : subd9_0 [1, 1, 8] = true := by decide +kernel
theorem subd9_0_560 : subd9_0 [1, 1, 9] = true := by decide +kernel
theorem subd9_0_561 : subd9_0 [1, 2, -10] = true := by decide +kernel
theorem subd9_0_562 : subd9_0 [1, 2, -9] = true := by decide +kernel
theorem subd9_0_563 : subd9_0 [1, 2, -8] = true := by decide +kernel
theorem subd9_0_564 : subd9_0 [1, 2, -7] = true := by decide +kernel
theorem subd9_0_565 : subd9_0 [1, 2, -6] = true := by decide +kernel
theorem subd9_0_566 : subd9_0 [1, 2, -5] = true := by decide +kernel
theorem subd9_0_567 : subd9_0 [1, 2, -4] = true := by decide +kernel
theorem subd9_0_568 : subd9_0 [1, 2, -3] = true := by decide +kernel
theorem subd9_0_569 : subd9_0 [1, 2, -2] = true := by decide +kernel
theorem subd9_0_570 : subd9_0 [1, 2, -1] = true := by decide +kernel
theorem subd9_0_571 : subd9_0 [1, 2, 0] = true := by decide +kernel
theorem subd9_0_572 : subd9_0 [1, 2, 1] = true := by decide +kernel
theorem subd9_0_573 : subd9_0 [1, 2, 2] = true := by decide +kernel
theorem subd9_0_574 : subd9_0 [1, 2, 3] = true := by decide +kernel
theorem subd9_0_575 : subd9_0 [1, 2, 4] = true := by decide +kernel
theorem sbd9_0_17 : ∀ q ∈ blkd9_0_17, subd9_0 q = true := by
  unfold blkd9_0_17
  exact List.forall_mem_cons.2 ⟨subd9_0_544, List.forall_mem_cons.2 ⟨subd9_0_545, List.forall_mem_cons.2 ⟨subd9_0_546, List.forall_mem_cons.2 ⟨subd9_0_547, List.forall_mem_cons.2 ⟨subd9_0_548, List.forall_mem_cons.2 ⟨subd9_0_549, List.forall_mem_cons.2 ⟨subd9_0_550, List.forall_mem_cons.2 ⟨subd9_0_551, List.forall_mem_cons.2 ⟨subd9_0_552, List.forall_mem_cons.2 ⟨subd9_0_553, List.forall_mem_cons.2 ⟨subd9_0_554, List.forall_mem_cons.2 ⟨subd9_0_555, List.forall_mem_cons.2 ⟨subd9_0_556, List.forall_mem_cons.2 ⟨subd9_0_557, List.forall_mem_cons.2 ⟨subd9_0_558, List.forall_mem_cons.2 ⟨subd9_0_559, List.forall_mem_cons.2 ⟨subd9_0_560, List.forall_mem_cons.2 ⟨subd9_0_561, List.forall_mem_cons.2 ⟨subd9_0_562, List.forall_mem_cons.2 ⟨subd9_0_563, List.forall_mem_cons.2 ⟨subd9_0_564, List.forall_mem_cons.2 ⟨subd9_0_565, List.forall_mem_cons.2 ⟨subd9_0_566, List.forall_mem_cons.2 ⟨subd9_0_567, List.forall_mem_cons.2 ⟨subd9_0_568, List.forall_mem_cons.2 ⟨subd9_0_569, List.forall_mem_cons.2 ⟨subd9_0_570, List.forall_mem_cons.2 ⟨subd9_0_571, List.forall_mem_cons.2 ⟨subd9_0_572, List.forall_mem_cons.2 ⟨subd9_0_573, List.forall_mem_cons.2 ⟨subd9_0_574, List.forall_mem_cons.2 ⟨subd9_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_576 : subd9_0 [1, 2, 5] = true := by decide +kernel
theorem subd9_0_577 : subd9_0 [1, 2, 6] = true := by decide +kernel
theorem subd9_0_578 : subd9_0 [1, 2, 7] = true := by decide +kernel
theorem subd9_0_579 : subd9_0 [1, 2, 8] = true := by decide +kernel
theorem subd9_0_580 : subd9_0 [1, 3, -9] = true := by decide +kernel
theorem subd9_0_581 : subd9_0 [1, 3, -8] = true := by decide +kernel
theorem subd9_0_582 : subd9_0 [1, 3, -7] = true := by decide +kernel
theorem subd9_0_583 : subd9_0 [1, 3, -6] = true := by decide +kernel
theorem subd9_0_584 : subd9_0 [1, 3, -5] = true := by decide +kernel
theorem subd9_0_585 : subd9_0 [1, 3, -4] = true := by decide +kernel
theorem subd9_0_586 : subd9_0 [1, 3, -3] = true := by decide +kernel
theorem subd9_0_587 : subd9_0 [1, 3, -2] = true := by decide +kernel
theorem subd9_0_588 : subd9_0 [1, 3, -1] = true := by decide +kernel
theorem subd9_0_589 : subd9_0 [1, 3, 0] = true := by decide +kernel
theorem subd9_0_590 : subd9_0 [1, 3, 1] = true := by decide +kernel
theorem subd9_0_591 : subd9_0 [1, 3, 2] = true := by decide +kernel
theorem subd9_0_592 : subd9_0 [1, 3, 3] = true := by decide +kernel
theorem subd9_0_593 : subd9_0 [1, 3, 4] = true := by decide +kernel
theorem subd9_0_594 : subd9_0 [1, 3, 5] = true := by decide +kernel
theorem subd9_0_595 : subd9_0 [1, 3, 6] = true := by decide +kernel
theorem subd9_0_596 : subd9_0 [1, 3, 7] = true := by decide +kernel
theorem subd9_0_597 : subd9_0 [1, 4] = true := by decide +kernel
theorem subd9_0_598 : subd9_0 [2, -5] = true := by decide +kernel
theorem subd9_0_599 : subd9_0 [2, -4] = true := by decide +kernel
theorem subd9_0_600 : subd9_0 [2, -3] = true := by decide +kernel
theorem subd9_0_601 : subd9_0 [2, -2, -10] = true := by decide +kernel
theorem subd9_0_602 : subd9_0 [2, -2, -9] = true := by decide +kernel
theorem subd9_0_603 : subd9_0 [2, -2, -8] = true := by decide +kernel
theorem subd9_0_604 : subd9_0 [2, -2, -7] = true := by decide +kernel
theorem subd9_0_605 : subd9_0 [2, -2, -6] = true := by decide +kernel
theorem subd9_0_606 : subd9_0 [2, -2, -5] = true := by decide +kernel
theorem subd9_0_607 : subd9_0 [2, -2, -4] = true := by decide +kernel
theorem sbd9_0_18 : ∀ q ∈ blkd9_0_18, subd9_0 q = true := by
  unfold blkd9_0_18
  exact List.forall_mem_cons.2 ⟨subd9_0_576, List.forall_mem_cons.2 ⟨subd9_0_577, List.forall_mem_cons.2 ⟨subd9_0_578, List.forall_mem_cons.2 ⟨subd9_0_579, List.forall_mem_cons.2 ⟨subd9_0_580, List.forall_mem_cons.2 ⟨subd9_0_581, List.forall_mem_cons.2 ⟨subd9_0_582, List.forall_mem_cons.2 ⟨subd9_0_583, List.forall_mem_cons.2 ⟨subd9_0_584, List.forall_mem_cons.2 ⟨subd9_0_585, List.forall_mem_cons.2 ⟨subd9_0_586, List.forall_mem_cons.2 ⟨subd9_0_587, List.forall_mem_cons.2 ⟨subd9_0_588, List.forall_mem_cons.2 ⟨subd9_0_589, List.forall_mem_cons.2 ⟨subd9_0_590, List.forall_mem_cons.2 ⟨subd9_0_591, List.forall_mem_cons.2 ⟨subd9_0_592, List.forall_mem_cons.2 ⟨subd9_0_593, List.forall_mem_cons.2 ⟨subd9_0_594, List.forall_mem_cons.2 ⟨subd9_0_595, List.forall_mem_cons.2 ⟨subd9_0_596, List.forall_mem_cons.2 ⟨subd9_0_597, List.forall_mem_cons.2 ⟨subd9_0_598, List.forall_mem_cons.2 ⟨subd9_0_599, List.forall_mem_cons.2 ⟨subd9_0_600, List.forall_mem_cons.2 ⟨subd9_0_601, List.forall_mem_cons.2 ⟨subd9_0_602, List.forall_mem_cons.2 ⟨subd9_0_603, List.forall_mem_cons.2 ⟨subd9_0_604, List.forall_mem_cons.2 ⟨subd9_0_605, List.forall_mem_cons.2 ⟨subd9_0_606, List.forall_mem_cons.2 ⟨subd9_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_608 : subd9_0 [2, -2, -3] = true := by decide +kernel
theorem subd9_0_609 : subd9_0 [2, -2, -2] = true := by decide +kernel
theorem subd9_0_610 : subd9_0 [2, -2, -1] = true := by decide +kernel
theorem subd9_0_611 : subd9_0 [2, -2, 0] = true := by decide +kernel
theorem subd9_0_612 : subd9_0 [2, -2, 1] = true := by decide +kernel
theorem subd9_0_613 : subd9_0 [2, -2, 2] = true := by decide +kernel
theorem subd9_0_614 : subd9_0 [2, -2, 3] = true := by decide +kernel
theorem subd9_0_615 : subd9_0 [2, -2, 4] = true := by decide +kernel
theorem subd9_0_616 : subd9_0 [2, -2, 5] = true := by decide +kernel
theorem subd9_0_617 : subd9_0 [2, -2, 6] = true := by decide +kernel
theorem subd9_0_618 : subd9_0 [2, -2, 7] = true := by decide +kernel
theorem subd9_0_619 : subd9_0 [2, -1, -10] = true := by decide +kernel
theorem subd9_0_620 : subd9_0 [2, -1, -9] = true := by decide +kernel
theorem subd9_0_621 : subd9_0 [2, -1, -8] = true := by decide +kernel
theorem subd9_0_622 : subd9_0 [2, -1, -7] = true := by decide +kernel
theorem subd9_0_623 : subd9_0 [2, -1, -6] = true := by decide +kernel
theorem subd9_0_624 : subd9_0 [2, -1, -5] = true := by decide +kernel
theorem subd9_0_625 : subd9_0 [2, -1, -4] = true := by decide +kernel
theorem subd9_0_626 : subd9_0 [2, -1, -3] = true := by decide +kernel
theorem subd9_0_627 : subd9_0 [2, -1, -2] = true := by decide +kernel
theorem subd9_0_628 : subd9_0 [2, -1, -1] = true := by decide +kernel
theorem subd9_0_629 : subd9_0 [2, -1, 0] = true := by decide +kernel
theorem subd9_0_630 : subd9_0 [2, -1, 1] = true := by decide +kernel
theorem subd9_0_631 : subd9_0 [2, -1, 2] = true := by decide +kernel
theorem subd9_0_632 : subd9_0 [2, -1, 3] = true := by decide +kernel
theorem subd9_0_633 : subd9_0 [2, -1, 4] = true := by decide +kernel
theorem subd9_0_634 : subd9_0 [2, -1, 5] = true := by decide +kernel
theorem subd9_0_635 : subd9_0 [2, -1, 6] = true := by decide +kernel
theorem subd9_0_636 : subd9_0 [2, -1, 7] = true := by decide +kernel
theorem subd9_0_637 : subd9_0 [2, -1, 8] = true := by decide +kernel
theorem subd9_0_638 : subd9_0 [2, 0, -11] = true := by decide +kernel
theorem subd9_0_639 : subd9_0 [2, 0, -10] = true := by decide +kernel
theorem sbd9_0_19 : ∀ q ∈ blkd9_0_19, subd9_0 q = true := by
  unfold blkd9_0_19
  exact List.forall_mem_cons.2 ⟨subd9_0_608, List.forall_mem_cons.2 ⟨subd9_0_609, List.forall_mem_cons.2 ⟨subd9_0_610, List.forall_mem_cons.2 ⟨subd9_0_611, List.forall_mem_cons.2 ⟨subd9_0_612, List.forall_mem_cons.2 ⟨subd9_0_613, List.forall_mem_cons.2 ⟨subd9_0_614, List.forall_mem_cons.2 ⟨subd9_0_615, List.forall_mem_cons.2 ⟨subd9_0_616, List.forall_mem_cons.2 ⟨subd9_0_617, List.forall_mem_cons.2 ⟨subd9_0_618, List.forall_mem_cons.2 ⟨subd9_0_619, List.forall_mem_cons.2 ⟨subd9_0_620, List.forall_mem_cons.2 ⟨subd9_0_621, List.forall_mem_cons.2 ⟨subd9_0_622, List.forall_mem_cons.2 ⟨subd9_0_623, List.forall_mem_cons.2 ⟨subd9_0_624, List.forall_mem_cons.2 ⟨subd9_0_625, List.forall_mem_cons.2 ⟨subd9_0_626, List.forall_mem_cons.2 ⟨subd9_0_627, List.forall_mem_cons.2 ⟨subd9_0_628, List.forall_mem_cons.2 ⟨subd9_0_629, List.forall_mem_cons.2 ⟨subd9_0_630, List.forall_mem_cons.2 ⟨subd9_0_631, List.forall_mem_cons.2 ⟨subd9_0_632, List.forall_mem_cons.2 ⟨subd9_0_633, List.forall_mem_cons.2 ⟨subd9_0_634, List.forall_mem_cons.2 ⟨subd9_0_635, List.forall_mem_cons.2 ⟨subd9_0_636, List.forall_mem_cons.2 ⟨subd9_0_637, List.forall_mem_cons.2 ⟨subd9_0_638, List.forall_mem_cons.2 ⟨subd9_0_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_640 : subd9_0 [2, 0, -9] = true := by decide +kernel
theorem subd9_0_641 : subd9_0 [2, 0, -8] = true := by decide +kernel
theorem subd9_0_642 : subd9_0 [2, 0, -7] = true := by decide +kernel
theorem subd9_0_643 : subd9_0 [2, 0, -6] = true := by decide +kernel
theorem subd9_0_644 : subd9_0 [2, 0, -5] = true := by decide +kernel
theorem subd9_0_645 : subd9_0 [2, 0, -4] = true := by decide +kernel
theorem subd9_0_646 : subd9_0 [2, 0, -3] = true := by decide +kernel
theorem subd9_0_647 : subd9_0 [2, 0, -2] = true := by decide +kernel
theorem subd9_0_648 : subd9_0 [2, 0, -1] = true := by decide +kernel
theorem subd9_0_649 : subd9_0 [2, 0, 0] = true := by decide +kernel
theorem subd9_0_650 : subd9_0 [2, 0, 1] = true := by decide +kernel
theorem subd9_0_651 : subd9_0 [2, 0, 2] = true := by decide +kernel
theorem subd9_0_652 : subd9_0 [2, 0, 3] = true := by decide +kernel
theorem subd9_0_653 : subd9_0 [2, 0, 4] = true := by decide +kernel
theorem subd9_0_654 : subd9_0 [2, 0, 5] = true := by decide +kernel
theorem subd9_0_655 : subd9_0 [2, 0, 6] = true := by decide +kernel
theorem subd9_0_656 : subd9_0 [2, 0, 7] = true := by decide +kernel
theorem subd9_0_657 : subd9_0 [2, 0, 8] = true := by decide +kernel
theorem subd9_0_658 : subd9_0 [2, 1, -10] = true := by decide +kernel
theorem subd9_0_659 : subd9_0 [2, 1, -9] = true := by decide +kernel
theorem subd9_0_660 : subd9_0 [2, 1, -8] = true := by decide +kernel
theorem subd9_0_661 : subd9_0 [2, 1, -7] = true := by decide +kernel
theorem subd9_0_662 : subd9_0 [2, 1, -6] = true := by decide +kernel
theorem subd9_0_663 : subd9_0 [2, 1, -5] = true := by decide +kernel
theorem subd9_0_664 : subd9_0 [2, 1, -4] = true := by decide +kernel
theorem subd9_0_665 : subd9_0 [2, 1, -3] = true := by decide +kernel
theorem subd9_0_666 : subd9_0 [2, 1, -2] = true := by decide +kernel
theorem subd9_0_667 : subd9_0 [2, 1, -1] = true := by decide +kernel
theorem subd9_0_668 : subd9_0 [2, 1, 0] = true := by decide +kernel
theorem subd9_0_669 : subd9_0 [2, 1, 1] = true := by decide +kernel
theorem subd9_0_670 : subd9_0 [2, 1, 2] = true := by decide +kernel
theorem subd9_0_671 : subd9_0 [2, 1, 3] = true := by decide +kernel
theorem sbd9_0_20 : ∀ q ∈ blkd9_0_20, subd9_0 q = true := by
  unfold blkd9_0_20
  exact List.forall_mem_cons.2 ⟨subd9_0_640, List.forall_mem_cons.2 ⟨subd9_0_641, List.forall_mem_cons.2 ⟨subd9_0_642, List.forall_mem_cons.2 ⟨subd9_0_643, List.forall_mem_cons.2 ⟨subd9_0_644, List.forall_mem_cons.2 ⟨subd9_0_645, List.forall_mem_cons.2 ⟨subd9_0_646, List.forall_mem_cons.2 ⟨subd9_0_647, List.forall_mem_cons.2 ⟨subd9_0_648, List.forall_mem_cons.2 ⟨subd9_0_649, List.forall_mem_cons.2 ⟨subd9_0_650, List.forall_mem_cons.2 ⟨subd9_0_651, List.forall_mem_cons.2 ⟨subd9_0_652, List.forall_mem_cons.2 ⟨subd9_0_653, List.forall_mem_cons.2 ⟨subd9_0_654, List.forall_mem_cons.2 ⟨subd9_0_655, List.forall_mem_cons.2 ⟨subd9_0_656, List.forall_mem_cons.2 ⟨subd9_0_657, List.forall_mem_cons.2 ⟨subd9_0_658, List.forall_mem_cons.2 ⟨subd9_0_659, List.forall_mem_cons.2 ⟨subd9_0_660, List.forall_mem_cons.2 ⟨subd9_0_661, List.forall_mem_cons.2 ⟨subd9_0_662, List.forall_mem_cons.2 ⟨subd9_0_663, List.forall_mem_cons.2 ⟨subd9_0_664, List.forall_mem_cons.2 ⟨subd9_0_665, List.forall_mem_cons.2 ⟨subd9_0_666, List.forall_mem_cons.2 ⟨subd9_0_667, List.forall_mem_cons.2 ⟨subd9_0_668, List.forall_mem_cons.2 ⟨subd9_0_669, List.forall_mem_cons.2 ⟨subd9_0_670, List.forall_mem_cons.2 ⟨subd9_0_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_672 : subd9_0 [2, 1, 4] = true := by decide +kernel
theorem subd9_0_673 : subd9_0 [2, 1, 5] = true := by decide +kernel
theorem subd9_0_674 : subd9_0 [2, 1, 6] = true := by decide +kernel
theorem subd9_0_675 : subd9_0 [2, 1, 7] = true := by decide +kernel
theorem subd9_0_676 : subd9_0 [2, 1, 8] = true := by decide +kernel
theorem subd9_0_677 : subd9_0 [2, 2, -10] = true := by decide +kernel
theorem subd9_0_678 : subd9_0 [2, 2, -9] = true := by decide +kernel
theorem subd9_0_679 : subd9_0 [2, 2, -8] = true := by decide +kernel
theorem subd9_0_680 : subd9_0 [2, 2, -7] = true := by decide +kernel
theorem subd9_0_681 : subd9_0 [2, 2, -6] = true := by decide +kernel
theorem subd9_0_682 : subd9_0 [2, 2, -5] = true := by decide +kernel
theorem subd9_0_683 : subd9_0 [2, 2, -4] = true := by decide +kernel
theorem subd9_0_684 : subd9_0 [2, 2, -3] = true := by decide +kernel
theorem subd9_0_685 : subd9_0 [2, 2, -2] = true := by decide +kernel
theorem subd9_0_686 : subd9_0 [2, 2, -1] = true := by decide +kernel
theorem subd9_0_687 : subd9_0 [2, 2, 0] = true := by decide +kernel
theorem subd9_0_688 : subd9_0 [2, 2, 1] = true := by decide +kernel
theorem subd9_0_689 : subd9_0 [2, 2, 2] = true := by decide +kernel
theorem subd9_0_690 : subd9_0 [2, 2, 3] = true := by decide +kernel
theorem subd9_0_691 : subd9_0 [2, 2, 4] = true := by decide +kernel
theorem subd9_0_692 : subd9_0 [2, 2, 5] = true := by decide +kernel
theorem subd9_0_693 : subd9_0 [2, 2, 6] = true := by decide +kernel
theorem subd9_0_694 : subd9_0 [2, 2, 7] = true := by decide +kernel
theorem subd9_0_695 : subd9_0 [2, 3, -8] = true := by decide +kernel
theorem subd9_0_696 : subd9_0 [2, 3, -7] = true := by decide +kernel
theorem subd9_0_697 : subd9_0 [2, 3, -6] = true := by decide +kernel
theorem subd9_0_698 : subd9_0 [2, 3, -5] = true := by decide +kernel
theorem subd9_0_699 : subd9_0 [2, 3, -4] = true := by decide +kernel
theorem subd9_0_700 : subd9_0 [2, 3, -3] = true := by decide +kernel
theorem subd9_0_701 : subd9_0 [2, 3, -2] = true := by decide +kernel
theorem subd9_0_702 : subd9_0 [2, 3, -1] = true := by decide +kernel
theorem subd9_0_703 : subd9_0 [2, 3, 0] = true := by decide +kernel
theorem sbd9_0_21 : ∀ q ∈ blkd9_0_21, subd9_0 q = true := by
  unfold blkd9_0_21
  exact List.forall_mem_cons.2 ⟨subd9_0_672, List.forall_mem_cons.2 ⟨subd9_0_673, List.forall_mem_cons.2 ⟨subd9_0_674, List.forall_mem_cons.2 ⟨subd9_0_675, List.forall_mem_cons.2 ⟨subd9_0_676, List.forall_mem_cons.2 ⟨subd9_0_677, List.forall_mem_cons.2 ⟨subd9_0_678, List.forall_mem_cons.2 ⟨subd9_0_679, List.forall_mem_cons.2 ⟨subd9_0_680, List.forall_mem_cons.2 ⟨subd9_0_681, List.forall_mem_cons.2 ⟨subd9_0_682, List.forall_mem_cons.2 ⟨subd9_0_683, List.forall_mem_cons.2 ⟨subd9_0_684, List.forall_mem_cons.2 ⟨subd9_0_685, List.forall_mem_cons.2 ⟨subd9_0_686, List.forall_mem_cons.2 ⟨subd9_0_687, List.forall_mem_cons.2 ⟨subd9_0_688, List.forall_mem_cons.2 ⟨subd9_0_689, List.forall_mem_cons.2 ⟨subd9_0_690, List.forall_mem_cons.2 ⟨subd9_0_691, List.forall_mem_cons.2 ⟨subd9_0_692, List.forall_mem_cons.2 ⟨subd9_0_693, List.forall_mem_cons.2 ⟨subd9_0_694, List.forall_mem_cons.2 ⟨subd9_0_695, List.forall_mem_cons.2 ⟨subd9_0_696, List.forall_mem_cons.2 ⟨subd9_0_697, List.forall_mem_cons.2 ⟨subd9_0_698, List.forall_mem_cons.2 ⟨subd9_0_699, List.forall_mem_cons.2 ⟨subd9_0_700, List.forall_mem_cons.2 ⟨subd9_0_701, List.forall_mem_cons.2 ⟨subd9_0_702, List.forall_mem_cons.2 ⟨subd9_0_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_704 : subd9_0 [2, 3, 1] = true := by decide +kernel
theorem subd9_0_705 : subd9_0 [2, 3, 2] = true := by decide +kernel
theorem subd9_0_706 : subd9_0 [2, 3, 3] = true := by decide +kernel
theorem subd9_0_707 : subd9_0 [2, 3, 4] = true := by decide +kernel
theorem subd9_0_708 : subd9_0 [2, 3, 5] = true := by decide +kernel
theorem subd9_0_709 : subd9_0 [2, 4] = true := by decide +kernel
theorem subd9_0_710 : subd9_0 [3, -4] = true := by decide +kernel
theorem subd9_0_711 : subd9_0 [3, -3] = true := by decide +kernel
theorem subd9_0_712 : subd9_0 [3, -2] = true := by decide +kernel
theorem subd9_0_713 : subd9_0 [3, -1, -9] = true := by decide +kernel
theorem subd9_0_714 : subd9_0 [3, -1, -8] = true := by decide +kernel
theorem subd9_0_715 : subd9_0 [3, -1, -7] = true := by decide +kernel
theorem subd9_0_716 : subd9_0 [3, -1, -6] = true := by decide +kernel
theorem subd9_0_717 : subd9_0 [3, -1, -5] = true := by decide +kernel
theorem subd9_0_718 : subd9_0 [3, -1, -4] = true := by decide +kernel
theorem subd9_0_719 : subd9_0 [3, -1, -3] = true := by decide +kernel
theorem subd9_0_720 : subd9_0 [3, -1, -2] = true := by decide +kernel
theorem subd9_0_721 : subd9_0 [3, -1, -1] = true := by decide +kernel
theorem subd9_0_722 : subd9_0 [3, -1, 0] = true := by decide +kernel
theorem subd9_0_723 : subd9_0 [3, -1, 1] = true := by decide +kernel
theorem subd9_0_724 : subd9_0 [3, -1, 2] = true := by decide +kernel
theorem subd9_0_725 : subd9_0 [3, -1, 3] = true := by decide +kernel
theorem subd9_0_726 : subd9_0 [3, -1, 4] = true := by decide +kernel
theorem subd9_0_727 : subd9_0 [3, -1, 5] = true := by decide +kernel
theorem subd9_0_728 : subd9_0 [3, -1, 6] = true := by decide +kernel
theorem subd9_0_729 : subd9_0 [3, 0, -10] = true := by decide +kernel
theorem subd9_0_730 : subd9_0 [3, 0, -9] = true := by decide +kernel
theorem subd9_0_731 : subd9_0 [3, 0, -8] = true := by decide +kernel
theorem subd9_0_732 : subd9_0 [3, 0, -7] = true := by decide +kernel
theorem subd9_0_733 : subd9_0 [3, 0, -6] = true := by decide +kernel
theorem subd9_0_734 : subd9_0 [3, 0, -5] = true := by decide +kernel
theorem subd9_0_735 : subd9_0 [3, 0, -4] = true := by decide +kernel
theorem sbd9_0_22 : ∀ q ∈ blkd9_0_22, subd9_0 q = true := by
  unfold blkd9_0_22
  exact List.forall_mem_cons.2 ⟨subd9_0_704, List.forall_mem_cons.2 ⟨subd9_0_705, List.forall_mem_cons.2 ⟨subd9_0_706, List.forall_mem_cons.2 ⟨subd9_0_707, List.forall_mem_cons.2 ⟨subd9_0_708, List.forall_mem_cons.2 ⟨subd9_0_709, List.forall_mem_cons.2 ⟨subd9_0_710, List.forall_mem_cons.2 ⟨subd9_0_711, List.forall_mem_cons.2 ⟨subd9_0_712, List.forall_mem_cons.2 ⟨subd9_0_713, List.forall_mem_cons.2 ⟨subd9_0_714, List.forall_mem_cons.2 ⟨subd9_0_715, List.forall_mem_cons.2 ⟨subd9_0_716, List.forall_mem_cons.2 ⟨subd9_0_717, List.forall_mem_cons.2 ⟨subd9_0_718, List.forall_mem_cons.2 ⟨subd9_0_719, List.forall_mem_cons.2 ⟨subd9_0_720, List.forall_mem_cons.2 ⟨subd9_0_721, List.forall_mem_cons.2 ⟨subd9_0_722, List.forall_mem_cons.2 ⟨subd9_0_723, List.forall_mem_cons.2 ⟨subd9_0_724, List.forall_mem_cons.2 ⟨subd9_0_725, List.forall_mem_cons.2 ⟨subd9_0_726, List.forall_mem_cons.2 ⟨subd9_0_727, List.forall_mem_cons.2 ⟨subd9_0_728, List.forall_mem_cons.2 ⟨subd9_0_729, List.forall_mem_cons.2 ⟨subd9_0_730, List.forall_mem_cons.2 ⟨subd9_0_731, List.forall_mem_cons.2 ⟨subd9_0_732, List.forall_mem_cons.2 ⟨subd9_0_733, List.forall_mem_cons.2 ⟨subd9_0_734, List.forall_mem_cons.2 ⟨subd9_0_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_736 : subd9_0 [3, 0, -3] = true := by decide +kernel
theorem subd9_0_737 : subd9_0 [3, 0, -2] = true := by decide +kernel
theorem subd9_0_738 : subd9_0 [3, 0, -1] = true := by decide +kernel
theorem subd9_0_739 : subd9_0 [3, 0, 0] = true := by decide +kernel
theorem subd9_0_740 : subd9_0 [3, 0, 1] = true := by decide +kernel
theorem subd9_0_741 : subd9_0 [3, 0, 2] = true := by decide +kernel
theorem subd9_0_742 : subd9_0 [3, 0, 3] = true := by decide +kernel
theorem subd9_0_743 : subd9_0 [3, 0, 4] = true := by decide +kernel
theorem subd9_0_744 : subd9_0 [3, 0, 5] = true := by decide +kernel
theorem subd9_0_745 : subd9_0 [3, 0, 6] = true := by decide +kernel
theorem subd9_0_746 : subd9_0 [3, 1, -10] = true := by decide +kernel
theorem subd9_0_747 : subd9_0 [3, 1, -9] = true := by decide +kernel
theorem subd9_0_748 : subd9_0 [3, 1, -8] = true := by decide +kernel
theorem subd9_0_749 : subd9_0 [3, 1, -7] = true := by decide +kernel
theorem subd9_0_750 : subd9_0 [3, 1, -6] = true := by decide +kernel
theorem subd9_0_751 : subd9_0 [3, 1, -5] = true := by decide +kernel
theorem subd9_0_752 : subd9_0 [3, 1, -4] = true := by decide +kernel
theorem subd9_0_753 : subd9_0 [3, 1, -3] = true := by decide +kernel
theorem subd9_0_754 : subd9_0 [3, 1, -2] = true := by decide +kernel
theorem subd9_0_755 : subd9_0 [3, 1, -1] = true := by decide +kernel
theorem subd9_0_756 : subd9_0 [3, 1, 0] = true := by decide +kernel
theorem subd9_0_757 : subd9_0 [3, 1, 1] = true := by decide +kernel
theorem subd9_0_758 : subd9_0 [3, 1, 2] = true := by decide +kernel
theorem subd9_0_759 : subd9_0 [3, 1, 3] = true := by decide +kernel
theorem subd9_0_760 : subd9_0 [3, 1, 4] = true := by decide +kernel
theorem subd9_0_761 : subd9_0 [3, 1, 5] = true := by decide +kernel
theorem subd9_0_762 : subd9_0 [3, 1, 6] = true := by decide +kernel
theorem subd9_0_763 : subd9_0 [3, 2, -9] = true := by decide +kernel
theorem subd9_0_764 : subd9_0 [3, 2, -8] = true := by decide +kernel
theorem subd9_0_765 : subd9_0 [3, 2, -7] = true := by decide +kernel
theorem subd9_0_766 : subd9_0 [3, 2, -6] = true := by decide +kernel
theorem subd9_0_767 : subd9_0 [3, 2, -5] = true := by decide +kernel
theorem sbd9_0_23 : ∀ q ∈ blkd9_0_23, subd9_0 q = true := by
  unfold blkd9_0_23
  exact List.forall_mem_cons.2 ⟨subd9_0_736, List.forall_mem_cons.2 ⟨subd9_0_737, List.forall_mem_cons.2 ⟨subd9_0_738, List.forall_mem_cons.2 ⟨subd9_0_739, List.forall_mem_cons.2 ⟨subd9_0_740, List.forall_mem_cons.2 ⟨subd9_0_741, List.forall_mem_cons.2 ⟨subd9_0_742, List.forall_mem_cons.2 ⟨subd9_0_743, List.forall_mem_cons.2 ⟨subd9_0_744, List.forall_mem_cons.2 ⟨subd9_0_745, List.forall_mem_cons.2 ⟨subd9_0_746, List.forall_mem_cons.2 ⟨subd9_0_747, List.forall_mem_cons.2 ⟨subd9_0_748, List.forall_mem_cons.2 ⟨subd9_0_749, List.forall_mem_cons.2 ⟨subd9_0_750, List.forall_mem_cons.2 ⟨subd9_0_751, List.forall_mem_cons.2 ⟨subd9_0_752, List.forall_mem_cons.2 ⟨subd9_0_753, List.forall_mem_cons.2 ⟨subd9_0_754, List.forall_mem_cons.2 ⟨subd9_0_755, List.forall_mem_cons.2 ⟨subd9_0_756, List.forall_mem_cons.2 ⟨subd9_0_757, List.forall_mem_cons.2 ⟨subd9_0_758, List.forall_mem_cons.2 ⟨subd9_0_759, List.forall_mem_cons.2 ⟨subd9_0_760, List.forall_mem_cons.2 ⟨subd9_0_761, List.forall_mem_cons.2 ⟨subd9_0_762, List.forall_mem_cons.2 ⟨subd9_0_763, List.forall_mem_cons.2 ⟨subd9_0_764, List.forall_mem_cons.2 ⟨subd9_0_765, List.forall_mem_cons.2 ⟨subd9_0_766, List.forall_mem_cons.2 ⟨subd9_0_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_768 : subd9_0 [3, 2, -4] = true := by decide +kernel
theorem subd9_0_769 : subd9_0 [3, 2, -3] = true := by decide +kernel
theorem subd9_0_770 : subd9_0 [3, 2, -2] = true := by decide +kernel
theorem subd9_0_771 : subd9_0 [3, 2, -1] = true := by decide +kernel
theorem subd9_0_772 : subd9_0 [3, 2, 0] = true := by decide +kernel
theorem subd9_0_773 : subd9_0 [3, 2, 1] = true := by decide +kernel
theorem subd9_0_774 : subd9_0 [3, 2, 2] = true := by decide +kernel
theorem subd9_0_775 : subd9_0 [3, 2, 3] = true := by decide +kernel
theorem subd9_0_776 : subd9_0 [3, 2, 4] = true := by decide +kernel
theorem subd9_0_777 : subd9_0 [3, 2, 5] = true := by decide +kernel
theorem subd9_0_778 : subd9_0 [3, 3] = true := by decide +kernel
theorem subd9_0_779 : subd9_0 [4, -3] = true := by decide +kernel
theorem subd9_0_780 : subd9_0 [4, -2] = true := by decide +kernel
theorem subd9_0_781 : subd9_0 [4, -1] = true := by decide +kernel
theorem subd9_0_782 : subd9_0 [4, 0] = true := by decide +kernel
theorem subd9_0_783 : subd9_0 [4, 1] = true := by decide +kernel
theorem subd9_0_784 : subd9_0 [4, 2] = true := by decide +kernel
theorem sbd9_0_24 : ∀ q ∈ blkd9_0_24, subd9_0 q = true := by
  unfold blkd9_0_24
  exact List.forall_mem_cons.2 ⟨subd9_0_768, List.forall_mem_cons.2 ⟨subd9_0_769, List.forall_mem_cons.2 ⟨subd9_0_770, List.forall_mem_cons.2 ⟨subd9_0_771, List.forall_mem_cons.2 ⟨subd9_0_772, List.forall_mem_cons.2 ⟨subd9_0_773, List.forall_mem_cons.2 ⟨subd9_0_774, List.forall_mem_cons.2 ⟨subd9_0_775, List.forall_mem_cons.2 ⟨subd9_0_776, List.forall_mem_cons.2 ⟨subd9_0_777, List.forall_mem_cons.2 ⟨subd9_0_778, List.forall_mem_cons.2 ⟨subd9_0_779, List.forall_mem_cons.2 ⟨subd9_0_780, List.forall_mem_cons.2 ⟨subd9_0_781, List.forall_mem_cons.2 ⟨subd9_0_782, List.forall_mem_cons.2 ⟨subd9_0_783, List.forall_mem_cons.2 ⟨subd9_0_784, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C141
