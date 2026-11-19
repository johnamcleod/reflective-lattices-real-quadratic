import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_1_416 : subd6_1 [1, 1, 6] = true := by decide +kernel
theorem subd6_1_417 : subd6_1 [1, 1, 7] = true := by decide +kernel
theorem subd6_1_418 : subd6_1 [1, 1, 8] = true := by decide +kernel
theorem subd6_1_419 : subd6_1 [1, 2, -8] = true := by decide +kernel
theorem subd6_1_420 : subd6_1 [1, 2, -7] = true := by decide +kernel
theorem subd6_1_421 : subd6_1 [1, 2, -6] = true := by decide +kernel
theorem subd6_1_422 : subd6_1 [1, 2, -5] = true := by decide +kernel
theorem subd6_1_423 : subd6_1 [1, 2, -4] = true := by decide +kernel
theorem subd6_1_424 : subd6_1 [1, 2, -3] = true := by decide +kernel
theorem subd6_1_425 : subd6_1 [1, 2, -2] = true := by decide +kernel
theorem subd6_1_426 : subd6_1 [1, 2, -1] = true := by decide +kernel
theorem subd6_1_427 : subd6_1 [1, 2, 0] = true := by decide +kernel
theorem subd6_1_428 : subd6_1 [1, 2, 1] = true := by decide +kernel
theorem subd6_1_429 : subd6_1 [1, 2, 2] = true := by decide +kernel
theorem subd6_1_430 : subd6_1 [1, 2, 3] = true := by decide +kernel
theorem subd6_1_431 : subd6_1 [1, 2, 4] = true := by decide +kernel
theorem subd6_1_432 : subd6_1 [1, 2, 5] = true := by decide +kernel
theorem subd6_1_433 : subd6_1 [1, 2, 6] = true := by decide +kernel
theorem subd6_1_434 : subd6_1 [1, 2, 7] = true := by decide +kernel
theorem subd6_1_435 : subd6_1 [1, 3] = true := by decide +kernel
theorem subd6_1_436 : subd6_1 [1, 4] = true := by decide +kernel
theorem subd6_1_437 : subd6_1 [1, 5] = true := by decide +kernel
theorem subd6_1_438 : subd6_1 [2, -7] = true := by decide +kernel
theorem subd6_1_439 : subd6_1 [2, -6] = true := by decide +kernel
theorem subd6_1_440 : subd6_1 [2, -5] = true := by decide +kernel
theorem subd6_1_441 : subd6_1 [2, -4] = true := by decide +kernel
theorem subd6_1_442 : subd6_1 [2, -3, -7] = true := by decide +kernel
theorem subd6_1_443 : subd6_1 [2, -3, -6] = true := by decide +kernel
theorem subd6_1_444 : subd6_1 [2, -3, -5] = true := by decide +kernel
theorem subd6_1_445 : subd6_1 [2, -3, -4] = true := by decide +kernel
theorem subd6_1_446 : subd6_1 [2, -3, -3] = true := by decide +kernel
theorem subd6_1_447 : subd6_1 [2, -3, -2] = true := by decide +kernel
theorem sbd6_1_13 : ∀ q ∈ blkd6_1_13, subd6_1 q = true := by
  unfold blkd6_1_13
  exact List.forall_mem_cons.2 ⟨subd6_1_416, List.forall_mem_cons.2 ⟨subd6_1_417, List.forall_mem_cons.2 ⟨subd6_1_418, List.forall_mem_cons.2 ⟨subd6_1_419, List.forall_mem_cons.2 ⟨subd6_1_420, List.forall_mem_cons.2 ⟨subd6_1_421, List.forall_mem_cons.2 ⟨subd6_1_422, List.forall_mem_cons.2 ⟨subd6_1_423, List.forall_mem_cons.2 ⟨subd6_1_424, List.forall_mem_cons.2 ⟨subd6_1_425, List.forall_mem_cons.2 ⟨subd6_1_426, List.forall_mem_cons.2 ⟨subd6_1_427, List.forall_mem_cons.2 ⟨subd6_1_428, List.forall_mem_cons.2 ⟨subd6_1_429, List.forall_mem_cons.2 ⟨subd6_1_430, List.forall_mem_cons.2 ⟨subd6_1_431, List.forall_mem_cons.2 ⟨subd6_1_432, List.forall_mem_cons.2 ⟨subd6_1_433, List.forall_mem_cons.2 ⟨subd6_1_434, List.forall_mem_cons.2 ⟨subd6_1_435, List.forall_mem_cons.2 ⟨subd6_1_436, List.forall_mem_cons.2 ⟨subd6_1_437, List.forall_mem_cons.2 ⟨subd6_1_438, List.forall_mem_cons.2 ⟨subd6_1_439, List.forall_mem_cons.2 ⟨subd6_1_440, List.forall_mem_cons.2 ⟨subd6_1_441, List.forall_mem_cons.2 ⟨subd6_1_442, List.forall_mem_cons.2 ⟨subd6_1_443, List.forall_mem_cons.2 ⟨subd6_1_444, List.forall_mem_cons.2 ⟨subd6_1_445, List.forall_mem_cons.2 ⟨subd6_1_446, List.forall_mem_cons.2 ⟨subd6_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_448 : subd6_1 [2, -3, -1] = true := by decide +kernel
theorem subd6_1_449 : subd6_1 [2, -3, 0] = true := by decide +kernel
theorem subd6_1_450 : subd6_1 [2, -3, 1] = true := by decide +kernel
theorem subd6_1_451 : subd6_1 [2, -3, 2] = true := by decide +kernel
theorem subd6_1_452 : subd6_1 [2, -3, 3] = true := by decide +kernel
theorem subd6_1_453 : subd6_1 [2, -3, 4] = true := by decide +kernel
theorem subd6_1_454 : subd6_1 [2, -3, 5] = true := by decide +kernel
theorem subd6_1_455 : subd6_1 [2, -3, 6] = true := by decide +kernel
theorem subd6_1_456 : subd6_1 [2, -3, 7] = true := by decide +kernel
theorem subd6_1_457 : subd6_1 [2, -2, -7] = true := by decide +kernel
theorem subd6_1_458 : subd6_1 [2, -2, -6] = true := by decide +kernel
theorem subd6_1_459 : subd6_1 [2, -2, -5] = true := by decide +kernel
theorem subd6_1_460 : subd6_1 [2, -2, -4] = true := by decide +kernel
theorem subd6_1_461 : subd6_1 [2, -2, -3] = true := by decide +kernel
theorem subd6_1_462 : subd6_1 [2, -2, -2] = true := by decide +kernel
theorem subd6_1_463 : subd6_1 [2, -2, -1] = true := by decide +kernel
theorem subd6_1_464 : subd6_1 [2, -2, 0] = true := by decide +kernel
theorem subd6_1_465 : subd6_1 [2, -2, 1] = true := by decide +kernel
theorem subd6_1_466 : subd6_1 [2, -2, 2] = true := by decide +kernel
theorem subd6_1_467 : subd6_1 [2, -2, 3] = true := by decide +kernel
theorem subd6_1_468 : subd6_1 [2, -2, 4] = true := by decide +kernel
theorem subd6_1_469 : subd6_1 [2, -2, 5] = true := by decide +kernel
theorem subd6_1_470 : subd6_1 [2, -2, 6] = true := by decide +kernel
theorem subd6_1_471 : subd6_1 [2, -2, 7] = true := by decide +kernel
theorem subd6_1_472 : subd6_1 [2, -2, 8] = true := by decide +kernel
theorem subd6_1_473 : subd6_1 [2, -1, -7] = true := by decide +kernel
theorem subd6_1_474 : subd6_1 [2, -1, -6] = true := by decide +kernel
theorem subd6_1_475 : subd6_1 [2, -1, -5] = true := by decide +kernel
theorem subd6_1_476 : subd6_1 [2, -1, -4] = true := by decide +kernel
theorem subd6_1_477 : subd6_1 [2, -1, -3] = true := by decide +kernel
theorem subd6_1_478 : subd6_1 [2, -1, -2] = true := by decide +kernel
theorem subd6_1_479 : subd6_1 [2, -1, -1] = true := by decide +kernel
theorem sbd6_1_14 : ∀ q ∈ blkd6_1_14, subd6_1 q = true := by
  unfold blkd6_1_14
  exact List.forall_mem_cons.2 ⟨subd6_1_448, List.forall_mem_cons.2 ⟨subd6_1_449, List.forall_mem_cons.2 ⟨subd6_1_450, List.forall_mem_cons.2 ⟨subd6_1_451, List.forall_mem_cons.2 ⟨subd6_1_452, List.forall_mem_cons.2 ⟨subd6_1_453, List.forall_mem_cons.2 ⟨subd6_1_454, List.forall_mem_cons.2 ⟨subd6_1_455, List.forall_mem_cons.2 ⟨subd6_1_456, List.forall_mem_cons.2 ⟨subd6_1_457, List.forall_mem_cons.2 ⟨subd6_1_458, List.forall_mem_cons.2 ⟨subd6_1_459, List.forall_mem_cons.2 ⟨subd6_1_460, List.forall_mem_cons.2 ⟨subd6_1_461, List.forall_mem_cons.2 ⟨subd6_1_462, List.forall_mem_cons.2 ⟨subd6_1_463, List.forall_mem_cons.2 ⟨subd6_1_464, List.forall_mem_cons.2 ⟨subd6_1_465, List.forall_mem_cons.2 ⟨subd6_1_466, List.forall_mem_cons.2 ⟨subd6_1_467, List.forall_mem_cons.2 ⟨subd6_1_468, List.forall_mem_cons.2 ⟨subd6_1_469, List.forall_mem_cons.2 ⟨subd6_1_470, List.forall_mem_cons.2 ⟨subd6_1_471, List.forall_mem_cons.2 ⟨subd6_1_472, List.forall_mem_cons.2 ⟨subd6_1_473, List.forall_mem_cons.2 ⟨subd6_1_474, List.forall_mem_cons.2 ⟨subd6_1_475, List.forall_mem_cons.2 ⟨subd6_1_476, List.forall_mem_cons.2 ⟨subd6_1_477, List.forall_mem_cons.2 ⟨subd6_1_478, List.forall_mem_cons.2 ⟨subd6_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_480 : subd6_1 [2, -1, 0] = true := by decide +kernel
theorem subd6_1_481 : subd6_1 [2, -1, 1] = true := by decide +kernel
theorem subd6_1_482 : subd6_1 [2, -1, 2] = true := by decide +kernel
theorem subd6_1_483 : subd6_1 [2, -1, 3] = true := by decide +kernel
theorem subd6_1_484 : subd6_1 [2, -1, 4] = true := by decide +kernel
theorem subd6_1_485 : subd6_1 [2, -1, 5] = true := by decide +kernel
theorem subd6_1_486 : subd6_1 [2, -1, 6] = true := by decide +kernel
theorem subd6_1_487 : subd6_1 [2, -1, 7] = true := by decide +kernel
theorem subd6_1_488 : subd6_1 [2, -1, 8] = true := by decide +kernel
theorem subd6_1_489 : subd6_1 [2, 0, -7] = true := by decide +kernel
theorem subd6_1_490 : subd6_1 [2, 0, -6] = true := by decide +kernel
theorem subd6_1_491 : subd6_1 [2, 0, -5] = true := by decide +kernel
theorem subd6_1_492 : subd6_1 [2, 0, -4] = true := by decide +kernel
theorem subd6_1_493 : subd6_1 [2, 0, -3] = true := by decide +kernel
theorem subd6_1_494 : subd6_1 [2, 0, -2] = true := by decide +kernel
theorem subd6_1_495 : subd6_1 [2, 0, -1] = true := by decide +kernel
theorem subd6_1_496 : subd6_1 [2, 0, 0] = true := by decide +kernel
theorem subd6_1_497 : subd6_1 [2, 0, 1] = true := by decide +kernel
theorem subd6_1_498 : subd6_1 [2, 0, 2] = true := by decide +kernel
theorem subd6_1_499 : subd6_1 [2, 0, 3] = true := by decide +kernel
theorem subd6_1_500 : subd6_1 [2, 0, 4] = true := by decide +kernel
theorem subd6_1_501 : subd6_1 [2, 0, 5] = true := by decide +kernel
theorem subd6_1_502 : subd6_1 [2, 0, 6] = true := by decide +kernel
theorem subd6_1_503 : subd6_1 [2, 0, 7] = true := by decide +kernel
theorem subd6_1_504 : subd6_1 [2, 0, 8] = true := by decide +kernel
theorem subd6_1_505 : subd6_1 [2, 1, -7] = true := by decide +kernel
theorem subd6_1_506 : subd6_1 [2, 1, -6] = true := by decide +kernel
theorem subd6_1_507 : subd6_1 [2, 1, -5] = true := by decide +kernel
theorem subd6_1_508 : subd6_1 [2, 1, -4] = true := by decide +kernel
theorem subd6_1_509 : subd6_1 [2, 1, -3] = true := by decide +kernel
theorem subd6_1_510 : subd6_1 [2, 1, -2] = true := by decide +kernel
theorem subd6_1_511 : subd6_1 [2, 1, -1] = true := by decide +kernel
theorem sbd6_1_15 : ∀ q ∈ blkd6_1_15, subd6_1 q = true := by
  unfold blkd6_1_15
  exact List.forall_mem_cons.2 ⟨subd6_1_480, List.forall_mem_cons.2 ⟨subd6_1_481, List.forall_mem_cons.2 ⟨subd6_1_482, List.forall_mem_cons.2 ⟨subd6_1_483, List.forall_mem_cons.2 ⟨subd6_1_484, List.forall_mem_cons.2 ⟨subd6_1_485, List.forall_mem_cons.2 ⟨subd6_1_486, List.forall_mem_cons.2 ⟨subd6_1_487, List.forall_mem_cons.2 ⟨subd6_1_488, List.forall_mem_cons.2 ⟨subd6_1_489, List.forall_mem_cons.2 ⟨subd6_1_490, List.forall_mem_cons.2 ⟨subd6_1_491, List.forall_mem_cons.2 ⟨subd6_1_492, List.forall_mem_cons.2 ⟨subd6_1_493, List.forall_mem_cons.2 ⟨subd6_1_494, List.forall_mem_cons.2 ⟨subd6_1_495, List.forall_mem_cons.2 ⟨subd6_1_496, List.forall_mem_cons.2 ⟨subd6_1_497, List.forall_mem_cons.2 ⟨subd6_1_498, List.forall_mem_cons.2 ⟨subd6_1_499, List.forall_mem_cons.2 ⟨subd6_1_500, List.forall_mem_cons.2 ⟨subd6_1_501, List.forall_mem_cons.2 ⟨subd6_1_502, List.forall_mem_cons.2 ⟨subd6_1_503, List.forall_mem_cons.2 ⟨subd6_1_504, List.forall_mem_cons.2 ⟨subd6_1_505, List.forall_mem_cons.2 ⟨subd6_1_506, List.forall_mem_cons.2 ⟨subd6_1_507, List.forall_mem_cons.2 ⟨subd6_1_508, List.forall_mem_cons.2 ⟨subd6_1_509, List.forall_mem_cons.2 ⟨subd6_1_510, List.forall_mem_cons.2 ⟨subd6_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_512 : subd6_1 [2, 1, 0] = true := by decide +kernel
theorem subd6_1_513 : subd6_1 [2, 1, 1] = true := by decide +kernel
theorem subd6_1_514 : subd6_1 [2, 1, 2] = true := by decide +kernel
theorem subd6_1_515 : subd6_1 [2, 1, 3] = true := by decide +kernel
theorem subd6_1_516 : subd6_1 [2, 1, 4] = true := by decide +kernel
theorem subd6_1_517 : subd6_1 [2, 1, 5] = true := by decide +kernel
theorem subd6_1_518 : subd6_1 [2, 1, 6] = true := by decide +kernel
theorem subd6_1_519 : subd6_1 [2, 1, 7] = true := by decide +kernel
theorem subd6_1_520 : subd6_1 [2, 2] = true := by decide +kernel
theorem subd6_1_521 : subd6_1 [2, 3] = true := by decide +kernel
theorem subd6_1_522 : subd6_1 [2, 4] = true := by decide +kernel
theorem subd6_1_523 : subd6_1 [3, -6] = true := by decide +kernel
theorem subd6_1_524 : subd6_1 [3, -5] = true := by decide +kernel
theorem subd6_1_525 : subd6_1 [3, -4] = true := by decide +kernel
theorem subd6_1_526 : subd6_1 [3, -3] = true := by decide +kernel
theorem subd6_1_527 : subd6_1 [3, -2] = true := by decide +kernel
theorem subd6_1_528 : subd6_1 [3, -1] = true := by decide +kernel
theorem subd6_1_529 : subd6_1 [3, 0] = true := by decide +kernel
theorem subd6_1_530 : subd6_1 [3, 1] = true := by decide +kernel
theorem subd6_1_531 : subd6_1 [3, 2] = true := by decide +kernel
theorem subd6_1_532 : subd6_1 [3, 3] = true := by decide +kernel
theorem subd6_1_533 : subd6_1 [4, -6] = true := by decide +kernel
theorem subd6_1_534 : subd6_1 [4, -5] = true := by decide +kernel
theorem subd6_1_535 : subd6_1 [4, -4] = true := by decide +kernel
theorem subd6_1_536 : subd6_1 [4, -3] = true := by decide +kernel
theorem subd6_1_537 : subd6_1 [4, -2] = true := by decide +kernel
theorem subd6_1_538 : subd6_1 [4, -1] = true := by decide +kernel
theorem subd6_1_539 : subd6_1 [4, 0] = true := by decide +kernel
theorem subd6_1_540 : subd6_1 [4, 1] = true := by decide +kernel
theorem subd6_1_541 : subd6_1 [4, 2] = true := by decide +kernel
theorem subd6_1_542 : subd6_1 [5] = true := by decide +kernel
theorem sbd6_1_16 : ∀ q ∈ blkd6_1_16, subd6_1 q = true := by
  unfold blkd6_1_16
  exact List.forall_mem_cons.2 ⟨subd6_1_512, List.forall_mem_cons.2 ⟨subd6_1_513, List.forall_mem_cons.2 ⟨subd6_1_514, List.forall_mem_cons.2 ⟨subd6_1_515, List.forall_mem_cons.2 ⟨subd6_1_516, List.forall_mem_cons.2 ⟨subd6_1_517, List.forall_mem_cons.2 ⟨subd6_1_518, List.forall_mem_cons.2 ⟨subd6_1_519, List.forall_mem_cons.2 ⟨subd6_1_520, List.forall_mem_cons.2 ⟨subd6_1_521, List.forall_mem_cons.2 ⟨subd6_1_522, List.forall_mem_cons.2 ⟨subd6_1_523, List.forall_mem_cons.2 ⟨subd6_1_524, List.forall_mem_cons.2 ⟨subd6_1_525, List.forall_mem_cons.2 ⟨subd6_1_526, List.forall_mem_cons.2 ⟨subd6_1_527, List.forall_mem_cons.2 ⟨subd6_1_528, List.forall_mem_cons.2 ⟨subd6_1_529, List.forall_mem_cons.2 ⟨subd6_1_530, List.forall_mem_cons.2 ⟨subd6_1_531, List.forall_mem_cons.2 ⟨subd6_1_532, List.forall_mem_cons.2 ⟨subd6_1_533, List.forall_mem_cons.2 ⟨subd6_1_534, List.forall_mem_cons.2 ⟨subd6_1_535, List.forall_mem_cons.2 ⟨subd6_1_536, List.forall_mem_cons.2 ⟨subd6_1_537, List.forall_mem_cons.2 ⟨subd6_1_538, List.forall_mem_cons.2 ⟨subd6_1_539, List.forall_mem_cons.2 ⟨subd6_1_540, List.forall_mem_cons.2 ⟨subd6_1_541, List.forall_mem_cons.2 ⟨subd6_1_542, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-3] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-2, -2] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [-2, -1, -9] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [-2, -1, -8] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [-2, -1, -7] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [-2, -1, -6] = true := by decide +kernel
theorem subd6_2_6 : subd6_2 [-2, -1, -5] = true := by decide +kernel
theorem subd6_2_7 : subd6_2 [-2, -1, -4] = true := by decide +kernel
theorem subd6_2_8 : subd6_2 [-2, -1, -3] = true := by decide +kernel
theorem subd6_2_9 : subd6_2 [-2, -1, -2] = true := by decide +kernel
theorem subd6_2_10 : subd6_2 [-2, -1, -1] = true := by decide +kernel
theorem subd6_2_11 : subd6_2 [-2, -1, 0] = true := by decide +kernel
theorem subd6_2_12 : subd6_2 [-2, -1, 1] = true := by decide +kernel
theorem subd6_2_13 : subd6_2 [-2, -1, 2] = true := by decide +kernel
theorem subd6_2_14 : subd6_2 [-2, -1, 3] = true := by decide +kernel
theorem subd6_2_15 : subd6_2 [-2, -1, 4] = true := by decide +kernel
theorem subd6_2_16 : subd6_2 [-2, -1, 5] = true := by decide +kernel
theorem subd6_2_17 : subd6_2 [-2, -1, 6] = true := by decide +kernel
theorem subd6_2_18 : subd6_2 [-2, -1, 7] = true := by decide +kernel
theorem subd6_2_19 : subd6_2 [-2, -1, 8] = true := by decide +kernel
theorem subd6_2_20 : subd6_2 [-2, -1, 9] = true := by decide +kernel
theorem subd6_2_21 : subd6_2 [-2, 0, -11] = true := by decide +kernel
theorem subd6_2_22 : subd6_2 [-2, 0, -10] = true := by decide +kernel
theorem subd6_2_23 : subd6_2 [-2, 0, -9] = true := by decide +kernel
theorem subd6_2_24 : subd6_2 [-2, 0, -8] = true := by decide +kernel
theorem subd6_2_25 : subd6_2 [-2, 0, -7] = true := by decide +kernel
theorem subd6_2_26 : subd6_2 [-2, 0, -6] = true := by decide +kernel
theorem subd6_2_27 : subd6_2 [-2, 0, -5] = true := by decide +kernel
theorem subd6_2_28 : subd6_2 [-2, 0, -4] = true := by decide +kernel
theorem subd6_2_29 : subd6_2 [-2, 0, -3] = true := by decide +kernel
theorem subd6_2_30 : subd6_2 [-2, 0, -2] = true := by decide +kernel
theorem subd6_2_31 : subd6_2 [-2, 0, -1] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_cons.2 ⟨subd6_2_6, List.forall_mem_cons.2 ⟨subd6_2_7, List.forall_mem_cons.2 ⟨subd6_2_8, List.forall_mem_cons.2 ⟨subd6_2_9, List.forall_mem_cons.2 ⟨subd6_2_10, List.forall_mem_cons.2 ⟨subd6_2_11, List.forall_mem_cons.2 ⟨subd6_2_12, List.forall_mem_cons.2 ⟨subd6_2_13, List.forall_mem_cons.2 ⟨subd6_2_14, List.forall_mem_cons.2 ⟨subd6_2_15, List.forall_mem_cons.2 ⟨subd6_2_16, List.forall_mem_cons.2 ⟨subd6_2_17, List.forall_mem_cons.2 ⟨subd6_2_18, List.forall_mem_cons.2 ⟨subd6_2_19, List.forall_mem_cons.2 ⟨subd6_2_20, List.forall_mem_cons.2 ⟨subd6_2_21, List.forall_mem_cons.2 ⟨subd6_2_22, List.forall_mem_cons.2 ⟨subd6_2_23, List.forall_mem_cons.2 ⟨subd6_2_24, List.forall_mem_cons.2 ⟨subd6_2_25, List.forall_mem_cons.2 ⟨subd6_2_26, List.forall_mem_cons.2 ⟨subd6_2_27, List.forall_mem_cons.2 ⟨subd6_2_28, List.forall_mem_cons.2 ⟨subd6_2_29, List.forall_mem_cons.2 ⟨subd6_2_30, List.forall_mem_cons.2 ⟨subd6_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_32 : subd6_2 [-2, 0, 0] = true := by decide +kernel
theorem subd6_2_33 : subd6_2 [-2, 0, 1] = true := by decide +kernel
theorem subd6_2_34 : subd6_2 [-2, 0, 2] = true := by decide +kernel
theorem subd6_2_35 : subd6_2 [-2, 0, 3] = true := by decide +kernel
theorem subd6_2_36 : subd6_2 [-2, 0, 4] = true := by decide +kernel
theorem subd6_2_37 : subd6_2 [-2, 0, 5] = true := by decide +kernel
theorem subd6_2_38 : subd6_2 [-2, 0, 6] = true := by decide +kernel
theorem subd6_2_39 : subd6_2 [-2, 0, 7] = true := by decide +kernel
theorem subd6_2_40 : subd6_2 [-2, 0, 8] = true := by decide +kernel
theorem subd6_2_41 : subd6_2 [-2, 0, 9] = true := by decide +kernel
theorem subd6_2_42 : subd6_2 [-2, 0, 10] = true := by decide +kernel
theorem subd6_2_43 : subd6_2 [-2, 0, 11] = true := by decide +kernel
theorem subd6_2_44 : subd6_2 [-2, 1, -11] = true := by decide +kernel
theorem subd6_2_45 : subd6_2 [-2, 1, -10] = true := by decide +kernel
theorem subd6_2_46 : subd6_2 [-2, 1, -9] = true := by decide +kernel
theorem subd6_2_47 : subd6_2 [-2, 1, -8] = true := by decide +kernel
theorem subd6_2_48 : subd6_2 [-2, 1, -7] = true := by decide +kernel
theorem subd6_2_49 : subd6_2 [-2, 1, -6] = true := by decide +kernel
theorem subd6_2_50 : subd6_2 [-2, 1, -5] = true := by decide +kernel
theorem subd6_2_51 : subd6_2 [-2, 1, -4] = true := by decide +kernel
theorem subd6_2_52 : subd6_2 [-2, 1, -3] = true := by decide +kernel
theorem subd6_2_53 : subd6_2 [-2, 1, -2] = true := by decide +kernel
theorem subd6_2_54 : subd6_2 [-2, 1, -1] = true := by decide +kernel
theorem subd6_2_55 : subd6_2 [-2, 1, 0] = true := by decide +kernel
theorem subd6_2_56 : subd6_2 [-2, 1, 1] = true := by decide +kernel
theorem subd6_2_57 : subd6_2 [-2, 1, 2] = true := by decide +kernel
theorem subd6_2_58 : subd6_2 [-2, 1, 3] = true := by decide +kernel
theorem subd6_2_59 : subd6_2 [-2, 1, 4] = true := by decide +kernel
theorem subd6_2_60 : subd6_2 [-2, 1, 5] = true := by decide +kernel
theorem subd6_2_61 : subd6_2 [-2, 1, 6] = true := by decide +kernel
theorem subd6_2_62 : subd6_2 [-2, 1, 7] = true := by decide +kernel
theorem subd6_2_63 : subd6_2 [-2, 1, 8] = true := by decide +kernel
theorem sbd6_2_1 : ∀ q ∈ blkd6_2_1, subd6_2 q = true := by
  unfold blkd6_2_1
  exact List.forall_mem_cons.2 ⟨subd6_2_32, List.forall_mem_cons.2 ⟨subd6_2_33, List.forall_mem_cons.2 ⟨subd6_2_34, List.forall_mem_cons.2 ⟨subd6_2_35, List.forall_mem_cons.2 ⟨subd6_2_36, List.forall_mem_cons.2 ⟨subd6_2_37, List.forall_mem_cons.2 ⟨subd6_2_38, List.forall_mem_cons.2 ⟨subd6_2_39, List.forall_mem_cons.2 ⟨subd6_2_40, List.forall_mem_cons.2 ⟨subd6_2_41, List.forall_mem_cons.2 ⟨subd6_2_42, List.forall_mem_cons.2 ⟨subd6_2_43, List.forall_mem_cons.2 ⟨subd6_2_44, List.forall_mem_cons.2 ⟨subd6_2_45, List.forall_mem_cons.2 ⟨subd6_2_46, List.forall_mem_cons.2 ⟨subd6_2_47, List.forall_mem_cons.2 ⟨subd6_2_48, List.forall_mem_cons.2 ⟨subd6_2_49, List.forall_mem_cons.2 ⟨subd6_2_50, List.forall_mem_cons.2 ⟨subd6_2_51, List.forall_mem_cons.2 ⟨subd6_2_52, List.forall_mem_cons.2 ⟨subd6_2_53, List.forall_mem_cons.2 ⟨subd6_2_54, List.forall_mem_cons.2 ⟨subd6_2_55, List.forall_mem_cons.2 ⟨subd6_2_56, List.forall_mem_cons.2 ⟨subd6_2_57, List.forall_mem_cons.2 ⟨subd6_2_58, List.forall_mem_cons.2 ⟨subd6_2_59, List.forall_mem_cons.2 ⟨subd6_2_60, List.forall_mem_cons.2 ⟨subd6_2_61, List.forall_mem_cons.2 ⟨subd6_2_62, List.forall_mem_cons.2 ⟨subd6_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_64 : subd6_2 [-2, 1, 9] = true := by decide +kernel
theorem subd6_2_65 : subd6_2 [-2, 1, 10] = true := by decide +kernel
theorem subd6_2_66 : subd6_2 [-2, 2, -7] = true := by decide +kernel
theorem subd6_2_67 : subd6_2 [-2, 2, -6] = true := by decide +kernel
theorem subd6_2_68 : subd6_2 [-2, 2, -5] = true := by decide +kernel
theorem subd6_2_69 : subd6_2 [-2, 2, -4] = true := by decide +kernel
theorem subd6_2_70 : subd6_2 [-2, 2, -3] = true := by decide +kernel
theorem subd6_2_71 : subd6_2 [-2, 2, -2] = true := by decide +kernel
theorem subd6_2_72 : subd6_2 [-2, 2, -1] = true := by decide +kernel
theorem subd6_2_73 : subd6_2 [-2, 2, 0] = true := by decide +kernel
theorem subd6_2_74 : subd6_2 [-2, 2, 1] = true := by decide +kernel
theorem subd6_2_75 : subd6_2 [-2, 2, 2] = true := by decide +kernel
theorem subd6_2_76 : subd6_2 [-2, 2, 3] = true := by decide +kernel
theorem subd6_2_77 : subd6_2 [-2, 2, 4] = true := by decide +kernel
theorem subd6_2_78 : subd6_2 [-2, 2, 5] = true := by decide +kernel
theorem subd6_2_79 : subd6_2 [-2, 2, 6] = true := by decide +kernel
theorem subd6_2_80 : subd6_2 [-1, -3] = true := by decide +kernel
theorem subd6_2_81 : subd6_2 [-1, -2, -8] = true := by decide +kernel
theorem subd6_2_82 : subd6_2 [-1, -2, -7] = true := by decide +kernel
theorem subd6_2_83 : subd6_2 [-1, -2, -6] = true := by decide +kernel
theorem subd6_2_84 : subd6_2 [-1, -2, -5] = true := by decide +kernel
theorem subd6_2_85 : subd6_2 [-1, -2, -4] = true := by decide +kernel
theorem subd6_2_86 : subd6_2 [-1, -2, -3] = true := by decide +kernel
theorem subd6_2_87 : subd6_2 [-1, -2, -2] = true := by decide +kernel
theorem subd6_2_88 : subd6_2 [-1, -2, -1] = true := by decide +kernel
theorem subd6_2_89 : subd6_2 [-1, -2, 0] = true := by decide +kernel
theorem subd6_2_90 : subd6_2 [-1, -2, 1] = true := by decide +kernel
theorem subd6_2_91 : subd6_2 [-1, -2, 2] = true := by decide +kernel
theorem subd6_2_92 : subd6_2 [-1, -2, 3] = true := by decide +kernel
theorem subd6_2_93 : subd6_2 [-1, -2, 4] = true := by decide +kernel
theorem subd6_2_94 : subd6_2 [-1, -2, 5] = true := by decide +kernel
theorem subd6_2_95 : subd6_2 [-1, -2, 6] = true := by decide +kernel
theorem sbd6_2_2 : ∀ q ∈ blkd6_2_2, subd6_2 q = true := by
  unfold blkd6_2_2
  exact List.forall_mem_cons.2 ⟨subd6_2_64, List.forall_mem_cons.2 ⟨subd6_2_65, List.forall_mem_cons.2 ⟨subd6_2_66, List.forall_mem_cons.2 ⟨subd6_2_67, List.forall_mem_cons.2 ⟨subd6_2_68, List.forall_mem_cons.2 ⟨subd6_2_69, List.forall_mem_cons.2 ⟨subd6_2_70, List.forall_mem_cons.2 ⟨subd6_2_71, List.forall_mem_cons.2 ⟨subd6_2_72, List.forall_mem_cons.2 ⟨subd6_2_73, List.forall_mem_cons.2 ⟨subd6_2_74, List.forall_mem_cons.2 ⟨subd6_2_75, List.forall_mem_cons.2 ⟨subd6_2_76, List.forall_mem_cons.2 ⟨subd6_2_77, List.forall_mem_cons.2 ⟨subd6_2_78, List.forall_mem_cons.2 ⟨subd6_2_79, List.forall_mem_cons.2 ⟨subd6_2_80, List.forall_mem_cons.2 ⟨subd6_2_81, List.forall_mem_cons.2 ⟨subd6_2_82, List.forall_mem_cons.2 ⟨subd6_2_83, List.forall_mem_cons.2 ⟨subd6_2_84, List.forall_mem_cons.2 ⟨subd6_2_85, List.forall_mem_cons.2 ⟨subd6_2_86, List.forall_mem_cons.2 ⟨subd6_2_87, List.forall_mem_cons.2 ⟨subd6_2_88, List.forall_mem_cons.2 ⟨subd6_2_89, List.forall_mem_cons.2 ⟨subd6_2_90, List.forall_mem_cons.2 ⟨subd6_2_91, List.forall_mem_cons.2 ⟨subd6_2_92, List.forall_mem_cons.2 ⟨subd6_2_93, List.forall_mem_cons.2 ⟨subd6_2_94, List.forall_mem_cons.2 ⟨subd6_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_96 : subd6_2 [-1, -2, 7] = true := by decide +kernel
theorem subd6_2_97 : subd6_2 [-1, -2, 8] = true := by decide +kernel
theorem subd6_2_98 : subd6_2 [-1, -2, 9] = true := by decide +kernel
theorem subd6_2_99 : subd6_2 [-1, -1, -13] = true := by decide +kernel
theorem subd6_2_100 : subd6_2 [-1, -1, -12] = true := by decide +kernel
theorem subd6_2_101 : subd6_2 [-1, -1, -11] = true := by decide +kernel
theorem subd6_2_102 : subd6_2 [-1, -1, -10] = true := by decide +kernel
theorem subd6_2_103 : subd6_2 [-1, -1, -9] = true := by decide +kernel
theorem subd6_2_104 : subd6_2 [-1, -1, -8] = true := by decide +kernel
theorem subd6_2_105 : subd6_2 [-1, -1, -7] = true := by decide +kernel
theorem subd6_2_106 : subd6_2 [-1, -1, -6] = true := by decide +kernel
theorem subd6_2_107 : subd6_2 [-1, -1, -5] = true := by decide +kernel
theorem subd6_2_108 : subd6_2 [-1, -1, -4] = true := by decide +kernel
theorem subd6_2_109 : subd6_2 [-1, -1, -3] = true := by decide +kernel
theorem subd6_2_110 : subd6_2 [-1, -1, -2] = true := by decide +kernel
theorem subd6_2_111 : subd6_2 [-1, -1, -1] = true := by decide +kernel
theorem subd6_2_112 : subd6_2 [-1, -1, 0] = true := by decide +kernel
theorem subd6_2_113 : subd6_2 [-1, -1, 1] = true := by decide +kernel
theorem subd6_2_114 : subd6_2 [-1, -1, 2] = true := by decide +kernel
theorem subd6_2_115 : subd6_2 [-1, -1, 3] = true := by decide +kernel
theorem subd6_2_116 : subd6_2 [-1, -1, 4] = true := by decide +kernel
theorem subd6_2_117 : subd6_2 [-1, -1, 5] = true := by decide +kernel
theorem subd6_2_118 : subd6_2 [-1, -1, 6] = true := by decide +kernel
theorem subd6_2_119 : subd6_2 [-1, -1, 7] = true := by decide +kernel
theorem subd6_2_120 : subd6_2 [-1, -1, 8] = true := by decide +kernel
theorem subd6_2_121 : subd6_2 [-1, -1, 9] = true := by decide +kernel
theorem subd6_2_122 : subd6_2 [-1, -1, 10] = true := by decide +kernel
theorem subd6_2_123 : subd6_2 [-1, -1, 11] = true := by decide +kernel
theorem subd6_2_124 : subd6_2 [-1, -1, 12] = true := by decide +kernel
theorem subd6_2_125 : subd6_2 [-1, -1, 13] = true := by decide +kernel
theorem subd6_2_126 : subd6_2 [-1, 0, -14] = true := by decide +kernel
theorem subd6_2_127 : subd6_2 [-1, 0, -13] = true := by decide +kernel
theorem sbd6_2_3 : ∀ q ∈ blkd6_2_3, subd6_2 q = true := by
  unfold blkd6_2_3
  exact List.forall_mem_cons.2 ⟨subd6_2_96, List.forall_mem_cons.2 ⟨subd6_2_97, List.forall_mem_cons.2 ⟨subd6_2_98, List.forall_mem_cons.2 ⟨subd6_2_99, List.forall_mem_cons.2 ⟨subd6_2_100, List.forall_mem_cons.2 ⟨subd6_2_101, List.forall_mem_cons.2 ⟨subd6_2_102, List.forall_mem_cons.2 ⟨subd6_2_103, List.forall_mem_cons.2 ⟨subd6_2_104, List.forall_mem_cons.2 ⟨subd6_2_105, List.forall_mem_cons.2 ⟨subd6_2_106, List.forall_mem_cons.2 ⟨subd6_2_107, List.forall_mem_cons.2 ⟨subd6_2_108, List.forall_mem_cons.2 ⟨subd6_2_109, List.forall_mem_cons.2 ⟨subd6_2_110, List.forall_mem_cons.2 ⟨subd6_2_111, List.forall_mem_cons.2 ⟨subd6_2_112, List.forall_mem_cons.2 ⟨subd6_2_113, List.forall_mem_cons.2 ⟨subd6_2_114, List.forall_mem_cons.2 ⟨subd6_2_115, List.forall_mem_cons.2 ⟨subd6_2_116, List.forall_mem_cons.2 ⟨subd6_2_117, List.forall_mem_cons.2 ⟨subd6_2_118, List.forall_mem_cons.2 ⟨subd6_2_119, List.forall_mem_cons.2 ⟨subd6_2_120, List.forall_mem_cons.2 ⟨subd6_2_121, List.forall_mem_cons.2 ⟨subd6_2_122, List.forall_mem_cons.2 ⟨subd6_2_123, List.forall_mem_cons.2 ⟨subd6_2_124, List.forall_mem_cons.2 ⟨subd6_2_125, List.forall_mem_cons.2 ⟨subd6_2_126, List.forall_mem_cons.2 ⟨subd6_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_128 : subd6_2 [-1, 0, -12] = true := by decide +kernel
theorem subd6_2_129 : subd6_2 [-1, 0, -11] = true := by decide +kernel
theorem subd6_2_130 : subd6_2 [-1, 0, -10] = true := by decide +kernel
theorem subd6_2_131 : subd6_2 [-1, 0, -9] = true := by decide +kernel
theorem subd6_2_132 : subd6_2 [-1, 0, -8] = true := by decide +kernel
theorem subd6_2_133 : subd6_2 [-1, 0, -7] = true := by decide +kernel
theorem subd6_2_134 : subd6_2 [-1, 0, -6] = true := by decide +kernel
theorem subd6_2_135 : subd6_2 [-1, 0, -5] = true := by decide +kernel
theorem subd6_2_136 : subd6_2 [-1, 0, -4] = true := by decide +kernel
theorem subd6_2_137 : subd6_2 [-1, 0, -3] = true := by decide +kernel
theorem subd6_2_138 : subd6_2 [-1, 0, -2] = true := by decide +kernel
theorem subd6_2_139 : subd6_2 [-1, 0, -1] = true := by decide +kernel
theorem subd6_2_140 : subd6_2 [-1, 0, 0] = true := by decide +kernel
theorem subd6_2_141 : subd6_2 [-1, 0, 1] = true := by decide +kernel
theorem subd6_2_142 : subd6_2 [-1, 0, 2] = true := by decide +kernel
theorem subd6_2_143 : subd6_2 [-1, 0, 3] = true := by decide +kernel
theorem subd6_2_144 : subd6_2 [-1, 0, 4] = true := by decide +kernel
theorem subd6_2_145 : subd6_2 [-1, 0, 5] = true := by decide +kernel
theorem subd6_2_146 : subd6_2 [-1, 0, 6] = true := by decide +kernel
theorem subd6_2_147 : subd6_2 [-1, 0, 7] = true := by decide +kernel
theorem subd6_2_148 : subd6_2 [-1, 0, 8] = true := by decide +kernel
theorem subd6_2_149 : subd6_2 [-1, 0, 9] = true := by decide +kernel
theorem subd6_2_150 : subd6_2 [-1, 0, 10] = true := by decide +kernel
theorem subd6_2_151 : subd6_2 [-1, 0, 11] = true := by decide +kernel
theorem subd6_2_152 : subd6_2 [-1, 0, 12] = true := by decide +kernel
theorem subd6_2_153 : subd6_2 [-1, 0, 13] = true := by decide +kernel
theorem subd6_2_154 : subd6_2 [-1, 0, 14] = true := by decide +kernel
theorem subd6_2_155 : subd6_2 [-1, 1, -14] = true := by decide +kernel
theorem subd6_2_156 : subd6_2 [-1, 1, -13] = true := by decide +kernel
theorem subd6_2_157 : subd6_2 [-1, 1, -12] = true := by decide +kernel
theorem subd6_2_158 : subd6_2 [-1, 1, -11] = true := by decide +kernel
theorem subd6_2_159 : subd6_2 [-1, 1, -10] = true := by decide +kernel
theorem sbd6_2_4 : ∀ q ∈ blkd6_2_4, subd6_2 q = true := by
  unfold blkd6_2_4
  exact List.forall_mem_cons.2 ⟨subd6_2_128, List.forall_mem_cons.2 ⟨subd6_2_129, List.forall_mem_cons.2 ⟨subd6_2_130, List.forall_mem_cons.2 ⟨subd6_2_131, List.forall_mem_cons.2 ⟨subd6_2_132, List.forall_mem_cons.2 ⟨subd6_2_133, List.forall_mem_cons.2 ⟨subd6_2_134, List.forall_mem_cons.2 ⟨subd6_2_135, List.forall_mem_cons.2 ⟨subd6_2_136, List.forall_mem_cons.2 ⟨subd6_2_137, List.forall_mem_cons.2 ⟨subd6_2_138, List.forall_mem_cons.2 ⟨subd6_2_139, List.forall_mem_cons.2 ⟨subd6_2_140, List.forall_mem_cons.2 ⟨subd6_2_141, List.forall_mem_cons.2 ⟨subd6_2_142, List.forall_mem_cons.2 ⟨subd6_2_143, List.forall_mem_cons.2 ⟨subd6_2_144, List.forall_mem_cons.2 ⟨subd6_2_145, List.forall_mem_cons.2 ⟨subd6_2_146, List.forall_mem_cons.2 ⟨subd6_2_147, List.forall_mem_cons.2 ⟨subd6_2_148, List.forall_mem_cons.2 ⟨subd6_2_149, List.forall_mem_cons.2 ⟨subd6_2_150, List.forall_mem_cons.2 ⟨subd6_2_151, List.forall_mem_cons.2 ⟨subd6_2_152, List.forall_mem_cons.2 ⟨subd6_2_153, List.forall_mem_cons.2 ⟨subd6_2_154, List.forall_mem_cons.2 ⟨subd6_2_155, List.forall_mem_cons.2 ⟨subd6_2_156, List.forall_mem_cons.2 ⟨subd6_2_157, List.forall_mem_cons.2 ⟨subd6_2_158, List.forall_mem_cons.2 ⟨subd6_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
