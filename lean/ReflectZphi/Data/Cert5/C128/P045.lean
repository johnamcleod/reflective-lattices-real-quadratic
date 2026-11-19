import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_4_448 : subd7_4 [1, 2, 8] = true := by decide +kernel
theorem subd7_4_449 : subd7_4 [1, 2, 9] = true := by decide +kernel
theorem subd7_4_450 : subd7_4 [1, 3, -6] = true := by decide +kernel
theorem subd7_4_451 : subd7_4 [1, 3, -5] = true := by decide +kernel
theorem subd7_4_452 : subd7_4 [1, 3, -4] = true := by decide +kernel
theorem subd7_4_453 : subd7_4 [1, 3, -3] = true := by decide +kernel
theorem subd7_4_454 : subd7_4 [1, 3, -2] = true := by decide +kernel
theorem subd7_4_455 : subd7_4 [1, 3, -1] = true := by decide +kernel
theorem subd7_4_456 : subd7_4 [1, 3, 0] = true := by decide +kernel
theorem subd7_4_457 : subd7_4 [1, 3, 1] = true := by decide +kernel
theorem subd7_4_458 : subd7_4 [1, 3, 2] = true := by decide +kernel
theorem subd7_4_459 : subd7_4 [1, 3, 3] = true := by decide +kernel
theorem subd7_4_460 : subd7_4 [1, 3, 4] = true := by decide +kernel
theorem subd7_4_461 : subd7_4 [1, 3, 5] = true := by decide +kernel
theorem subd7_4_462 : subd7_4 [1, 3, 6] = true := by decide +kernel
theorem subd7_4_463 : subd7_4 [1, 3, 7] = true := by decide +kernel
theorem subd7_4_464 : subd7_4 [2, -4] = true := by decide +kernel
theorem subd7_4_465 : subd7_4 [2, -3] = true := by decide +kernel
theorem subd7_4_466 : subd7_4 [2, -2, -7] = true := by decide +kernel
theorem subd7_4_467 : subd7_4 [2, -2, -6] = true := by decide +kernel
theorem subd7_4_468 : subd7_4 [2, -2, -5] = true := by decide +kernel
theorem subd7_4_469 : subd7_4 [2, -2, -4] = true := by decide +kernel
theorem subd7_4_470 : subd7_4 [2, -2, -3] = true := by decide +kernel
theorem subd7_4_471 : subd7_4 [2, -2, -2] = true := by decide +kernel
theorem subd7_4_472 : subd7_4 [2, -2, -1] = true := by decide +kernel
theorem subd7_4_473 : subd7_4 [2, -2, 0] = true := by decide +kernel
theorem subd7_4_474 : subd7_4 [2, -2, 1] = true := by decide +kernel
theorem subd7_4_475 : subd7_4 [2, -2, 2] = true := by decide +kernel
theorem subd7_4_476 : subd7_4 [2, -2, 3] = true := by decide +kernel
theorem subd7_4_477 : subd7_4 [2, -2, 4] = true := by decide +kernel
theorem subd7_4_478 : subd7_4 [2, -2, 5] = true := by decide +kernel
theorem subd7_4_479 : subd7_4 [2, -2, 6] = true := by decide +kernel
theorem sbd7_4_14 : ∀ q ∈ blkd7_4_14, subd7_4 q = true := by
  unfold blkd7_4_14
  exact List.forall_mem_cons.2 ⟨subd7_4_448, List.forall_mem_cons.2 ⟨subd7_4_449, List.forall_mem_cons.2 ⟨subd7_4_450, List.forall_mem_cons.2 ⟨subd7_4_451, List.forall_mem_cons.2 ⟨subd7_4_452, List.forall_mem_cons.2 ⟨subd7_4_453, List.forall_mem_cons.2 ⟨subd7_4_454, List.forall_mem_cons.2 ⟨subd7_4_455, List.forall_mem_cons.2 ⟨subd7_4_456, List.forall_mem_cons.2 ⟨subd7_4_457, List.forall_mem_cons.2 ⟨subd7_4_458, List.forall_mem_cons.2 ⟨subd7_4_459, List.forall_mem_cons.2 ⟨subd7_4_460, List.forall_mem_cons.2 ⟨subd7_4_461, List.forall_mem_cons.2 ⟨subd7_4_462, List.forall_mem_cons.2 ⟨subd7_4_463, List.forall_mem_cons.2 ⟨subd7_4_464, List.forall_mem_cons.2 ⟨subd7_4_465, List.forall_mem_cons.2 ⟨subd7_4_466, List.forall_mem_cons.2 ⟨subd7_4_467, List.forall_mem_cons.2 ⟨subd7_4_468, List.forall_mem_cons.2 ⟨subd7_4_469, List.forall_mem_cons.2 ⟨subd7_4_470, List.forall_mem_cons.2 ⟨subd7_4_471, List.forall_mem_cons.2 ⟨subd7_4_472, List.forall_mem_cons.2 ⟨subd7_4_473, List.forall_mem_cons.2 ⟨subd7_4_474, List.forall_mem_cons.2 ⟨subd7_4_475, List.forall_mem_cons.2 ⟨subd7_4_476, List.forall_mem_cons.2 ⟨subd7_4_477, List.forall_mem_cons.2 ⟨subd7_4_478, List.forall_mem_cons.2 ⟨subd7_4_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_480 : subd7_4 [2, -1, -9] = true := by decide +kernel
theorem subd7_4_481 : subd7_4 [2, -1, -8] = true := by decide +kernel
theorem subd7_4_482 : subd7_4 [2, -1, -7] = true := by decide +kernel
theorem subd7_4_483 : subd7_4 [2, -1, -6] = true := by decide +kernel
theorem subd7_4_484 : subd7_4 [2, -1, -5] = true := by decide +kernel
theorem subd7_4_485 : subd7_4 [2, -1, -4] = true := by decide +kernel
theorem subd7_4_486 : subd7_4 [2, -1, -3] = true := by decide +kernel
theorem subd7_4_487 : subd7_4 [2, -1, -2] = true := by decide +kernel
theorem subd7_4_488 : subd7_4 [2, -1, -1] = true := by decide +kernel
theorem subd7_4_489 : subd7_4 [2, -1, 0] = true := by decide +kernel
theorem subd7_4_490 : subd7_4 [2, -1, 1] = true := by decide +kernel
theorem subd7_4_491 : subd7_4 [2, -1, 2] = true := by decide +kernel
theorem subd7_4_492 : subd7_4 [2, -1, 3] = true := by decide +kernel
theorem subd7_4_493 : subd7_4 [2, -1, 4] = true := by decide +kernel
theorem subd7_4_494 : subd7_4 [2, -1, 5] = true := by decide +kernel
theorem subd7_4_495 : subd7_4 [2, -1, 6] = true := by decide +kernel
theorem subd7_4_496 : subd7_4 [2, -1, 7] = true := by decide +kernel
theorem subd7_4_497 : subd7_4 [2, -1, 8] = true := by decide +kernel
theorem subd7_4_498 : subd7_4 [2, 0, -9] = true := by decide +kernel
theorem subd7_4_499 : subd7_4 [2, 0, -8] = true := by decide +kernel
theorem subd7_4_500 : subd7_4 [2, 0, -7] = true := by decide +kernel
theorem subd7_4_501 : subd7_4 [2, 0, -6] = true := by decide +kernel
theorem subd7_4_502 : subd7_4 [2, 0, -5] = true := by decide +kernel
theorem subd7_4_503 : subd7_4 [2, 0, -4] = true := by decide +kernel
theorem subd7_4_504 : subd7_4 [2, 0, -3] = true := by decide +kernel
theorem subd7_4_505 : subd7_4 [2, 0, -2] = true := by decide +kernel
theorem subd7_4_506 : subd7_4 [2, 0, -1] = true := by decide +kernel
theorem subd7_4_507 : subd7_4 [2, 0, 0] = true := by decide +kernel
theorem subd7_4_508 : subd7_4 [2, 0, 1] = true := by decide +kernel
theorem subd7_4_509 : subd7_4 [2, 0, 2] = true := by decide +kernel
theorem subd7_4_510 : subd7_4 [2, 0, 3] = true := by decide +kernel
theorem subd7_4_511 : subd7_4 [2, 0, 4] = true := by decide +kernel
theorem sbd7_4_15 : ∀ q ∈ blkd7_4_15, subd7_4 q = true := by
  unfold blkd7_4_15
  exact List.forall_mem_cons.2 ⟨subd7_4_480, List.forall_mem_cons.2 ⟨subd7_4_481, List.forall_mem_cons.2 ⟨subd7_4_482, List.forall_mem_cons.2 ⟨subd7_4_483, List.forall_mem_cons.2 ⟨subd7_4_484, List.forall_mem_cons.2 ⟨subd7_4_485, List.forall_mem_cons.2 ⟨subd7_4_486, List.forall_mem_cons.2 ⟨subd7_4_487, List.forall_mem_cons.2 ⟨subd7_4_488, List.forall_mem_cons.2 ⟨subd7_4_489, List.forall_mem_cons.2 ⟨subd7_4_490, List.forall_mem_cons.2 ⟨subd7_4_491, List.forall_mem_cons.2 ⟨subd7_4_492, List.forall_mem_cons.2 ⟨subd7_4_493, List.forall_mem_cons.2 ⟨subd7_4_494, List.forall_mem_cons.2 ⟨subd7_4_495, List.forall_mem_cons.2 ⟨subd7_4_496, List.forall_mem_cons.2 ⟨subd7_4_497, List.forall_mem_cons.2 ⟨subd7_4_498, List.forall_mem_cons.2 ⟨subd7_4_499, List.forall_mem_cons.2 ⟨subd7_4_500, List.forall_mem_cons.2 ⟨subd7_4_501, List.forall_mem_cons.2 ⟨subd7_4_502, List.forall_mem_cons.2 ⟨subd7_4_503, List.forall_mem_cons.2 ⟨subd7_4_504, List.forall_mem_cons.2 ⟨subd7_4_505, List.forall_mem_cons.2 ⟨subd7_4_506, List.forall_mem_cons.2 ⟨subd7_4_507, List.forall_mem_cons.2 ⟨subd7_4_508, List.forall_mem_cons.2 ⟨subd7_4_509, List.forall_mem_cons.2 ⟨subd7_4_510, List.forall_mem_cons.2 ⟨subd7_4_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_512 : subd7_4 [2, 0, 5] = true := by decide +kernel
theorem subd7_4_513 : subd7_4 [2, 0, 6] = true := by decide +kernel
theorem subd7_4_514 : subd7_4 [2, 0, 7] = true := by decide +kernel
theorem subd7_4_515 : subd7_4 [2, 0, 8] = true := by decide +kernel
theorem subd7_4_516 : subd7_4 [2, 0, 9] = true := by decide +kernel
theorem subd7_4_517 : subd7_4 [2, 1, -8] = true := by decide +kernel
theorem subd7_4_518 : subd7_4 [2, 1, -7] = true := by decide +kernel
theorem subd7_4_519 : subd7_4 [2, 1, -6] = true := by decide +kernel
theorem subd7_4_520 : subd7_4 [2, 1, -5] = true := by decide +kernel
theorem subd7_4_521 : subd7_4 [2, 1, -4] = true := by decide +kernel
theorem subd7_4_522 : subd7_4 [2, 1, -3] = true := by decide +kernel
theorem subd7_4_523 : subd7_4 [2, 1, -2] = true := by decide +kernel
theorem subd7_4_524 : subd7_4 [2, 1, -1] = true := by decide +kernel
theorem subd7_4_525 : subd7_4 [2, 1, 0] = true := by decide +kernel
theorem subd7_4_526 : subd7_4 [2, 1, 1] = true := by decide +kernel
theorem subd7_4_527 : subd7_4 [2, 1, 2] = true := by decide +kernel
theorem subd7_4_528 : subd7_4 [2, 1, 3] = true := by decide +kernel
theorem subd7_4_529 : subd7_4 [2, 1, 4] = true := by decide +kernel
theorem subd7_4_530 : subd7_4 [2, 1, 5] = true := by decide +kernel
theorem subd7_4_531 : subd7_4 [2, 1, 6] = true := by decide +kernel
theorem subd7_4_532 : subd7_4 [2, 1, 7] = true := by decide +kernel
theorem subd7_4_533 : subd7_4 [2, 1, 8] = true := by decide +kernel
theorem subd7_4_534 : subd7_4 [2, 1, 9] = true := by decide +kernel
theorem subd7_4_535 : subd7_4 [2, 2, -7] = true := by decide +kernel
theorem subd7_4_536 : subd7_4 [2, 2, -6] = true := by decide +kernel
theorem subd7_4_537 : subd7_4 [2, 2, -5] = true := by decide +kernel
theorem subd7_4_538 : subd7_4 [2, 2, -4] = true := by decide +kernel
theorem subd7_4_539 : subd7_4 [2, 2, -3] = true := by decide +kernel
theorem subd7_4_540 : subd7_4 [2, 2, -2] = true := by decide +kernel
theorem subd7_4_541 : subd7_4 [2, 2, -1] = true := by decide +kernel
theorem subd7_4_542 : subd7_4 [2, 2, 0] = true := by decide +kernel
theorem subd7_4_543 : subd7_4 [2, 2, 1] = true := by decide +kernel
theorem sbd7_4_16 : ∀ q ∈ blkd7_4_16, subd7_4 q = true := by
  unfold blkd7_4_16
  exact List.forall_mem_cons.2 ⟨subd7_4_512, List.forall_mem_cons.2 ⟨subd7_4_513, List.forall_mem_cons.2 ⟨subd7_4_514, List.forall_mem_cons.2 ⟨subd7_4_515, List.forall_mem_cons.2 ⟨subd7_4_516, List.forall_mem_cons.2 ⟨subd7_4_517, List.forall_mem_cons.2 ⟨subd7_4_518, List.forall_mem_cons.2 ⟨subd7_4_519, List.forall_mem_cons.2 ⟨subd7_4_520, List.forall_mem_cons.2 ⟨subd7_4_521, List.forall_mem_cons.2 ⟨subd7_4_522, List.forall_mem_cons.2 ⟨subd7_4_523, List.forall_mem_cons.2 ⟨subd7_4_524, List.forall_mem_cons.2 ⟨subd7_4_525, List.forall_mem_cons.2 ⟨subd7_4_526, List.forall_mem_cons.2 ⟨subd7_4_527, List.forall_mem_cons.2 ⟨subd7_4_528, List.forall_mem_cons.2 ⟨subd7_4_529, List.forall_mem_cons.2 ⟨subd7_4_530, List.forall_mem_cons.2 ⟨subd7_4_531, List.forall_mem_cons.2 ⟨subd7_4_532, List.forall_mem_cons.2 ⟨subd7_4_533, List.forall_mem_cons.2 ⟨subd7_4_534, List.forall_mem_cons.2 ⟨subd7_4_535, List.forall_mem_cons.2 ⟨subd7_4_536, List.forall_mem_cons.2 ⟨subd7_4_537, List.forall_mem_cons.2 ⟨subd7_4_538, List.forall_mem_cons.2 ⟨subd7_4_539, List.forall_mem_cons.2 ⟨subd7_4_540, List.forall_mem_cons.2 ⟨subd7_4_541, List.forall_mem_cons.2 ⟨subd7_4_542, List.forall_mem_cons.2 ⟨subd7_4_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_544 : subd7_4 [2, 2, 2] = true := by decide +kernel
theorem subd7_4_545 : subd7_4 [2, 2, 3] = true := by decide +kernel
theorem subd7_4_546 : subd7_4 [2, 2, 4] = true := by decide +kernel
theorem subd7_4_547 : subd7_4 [2, 2, 5] = true := by decide +kernel
theorem subd7_4_548 : subd7_4 [2, 2, 6] = true := by decide +kernel
theorem subd7_4_549 : subd7_4 [2, 2, 7] = true := by decide +kernel
theorem subd7_4_550 : subd7_4 [2, 3] = true := by decide +kernel
theorem subd7_4_551 : subd7_4 [3, -3] = true := by decide +kernel
theorem subd7_4_552 : subd7_4 [3, -2] = true := by decide +kernel
theorem subd7_4_553 : subd7_4 [3, -1] = true := by decide +kernel
theorem subd7_4_554 : subd7_4 [3, 0, -6] = true := by decide +kernel
theorem subd7_4_555 : subd7_4 [3, 0, -5] = true := by decide +kernel
theorem subd7_4_556 : subd7_4 [3, 0, -4] = true := by decide +kernel
theorem subd7_4_557 : subd7_4 [3, 0, -3] = true := by decide +kernel
theorem subd7_4_558 : subd7_4 [3, 0, -2] = true := by decide +kernel
theorem subd7_4_559 : subd7_4 [3, 0, -1] = true := by decide +kernel
theorem subd7_4_560 : subd7_4 [3, 0, 0] = true := by decide +kernel
theorem subd7_4_561 : subd7_4 [3, 0, 1] = true := by decide +kernel
theorem subd7_4_562 : subd7_4 [3, 0, 2] = true := by decide +kernel
theorem subd7_4_563 : subd7_4 [3, 0, 3] = true := by decide +kernel
theorem subd7_4_564 : subd7_4 [3, 0, 4] = true := by decide +kernel
theorem subd7_4_565 : subd7_4 [3, 0, 5] = true := by decide +kernel
theorem subd7_4_566 : subd7_4 [3, 0, 6] = true := by decide +kernel
theorem subd7_4_567 : subd7_4 [3, 1] = true := by decide +kernel
theorem subd7_4_568 : subd7_4 [3, 2] = true := by decide +kernel
theorem sbd7_4_17 : ∀ q ∈ blkd7_4_17, subd7_4 q = true := by
  unfold blkd7_4_17
  exact List.forall_mem_cons.2 ⟨subd7_4_544, List.forall_mem_cons.2 ⟨subd7_4_545, List.forall_mem_cons.2 ⟨subd7_4_546, List.forall_mem_cons.2 ⟨subd7_4_547, List.forall_mem_cons.2 ⟨subd7_4_548, List.forall_mem_cons.2 ⟨subd7_4_549, List.forall_mem_cons.2 ⟨subd7_4_550, List.forall_mem_cons.2 ⟨subd7_4_551, List.forall_mem_cons.2 ⟨subd7_4_552, List.forall_mem_cons.2 ⟨subd7_4_553, List.forall_mem_cons.2 ⟨subd7_4_554, List.forall_mem_cons.2 ⟨subd7_4_555, List.forall_mem_cons.2 ⟨subd7_4_556, List.forall_mem_cons.2 ⟨subd7_4_557, List.forall_mem_cons.2 ⟨subd7_4_558, List.forall_mem_cons.2 ⟨subd7_4_559, List.forall_mem_cons.2 ⟨subd7_4_560, List.forall_mem_cons.2 ⟨subd7_4_561, List.forall_mem_cons.2 ⟨subd7_4_562, List.forall_mem_cons.2 ⟨subd7_4_563, List.forall_mem_cons.2 ⟨subd7_4_564, List.forall_mem_cons.2 ⟨subd7_4_565, List.forall_mem_cons.2 ⟨subd7_4_566, List.forall_mem_cons.2 ⟨subd7_4_567, List.forall_mem_cons.2 ⟨subd7_4_568, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_5 : ldCheck G d7_5.U d7_5.ms ldd7_5 = true := by decide +kernel
theorem pre_okd7_5 : subPre G cell7 d7_5 = true := by decide +kernel
theorem subd7_5_0 : subd7_5 [-5, -4] = true := by decide +kernel
theorem subd7_5_1 : subd7_5 [-5, -3] = true := by decide +kernel
theorem subd7_5_2 : subd7_5 [-5, -2] = true := by decide +kernel
theorem subd7_5_3 : subd7_5 [-5, -1] = true := by decide +kernel
theorem subd7_5_4 : subd7_5 [-5, 0] = true := by decide +kernel
theorem subd7_5_5 : subd7_5 [-5, 1] = true := by decide +kernel
theorem subd7_5_6 : subd7_5 [-5, 2] = true := by decide +kernel
theorem subd7_5_7 : subd7_5 [-4, -5] = true := by decide +kernel
theorem subd7_5_8 : subd7_5 [-4, -4] = true := by decide +kernel
theorem subd7_5_9 : subd7_5 [-4, -3] = true := by decide +kernel
theorem subd7_5_10 : subd7_5 [-4, -2] = true := by decide +kernel
theorem subd7_5_11 : subd7_5 [-4, -1] = true := by decide +kernel
theorem subd7_5_12 : subd7_5 [-4, 0] = true := by decide +kernel
theorem subd7_5_13 : subd7_5 [-4, 1] = true := by decide +kernel
theorem subd7_5_14 : subd7_5 [-4, 2] = true := by decide +kernel
theorem subd7_5_15 : subd7_5 [-4, 3] = true := by decide +kernel
theorem subd7_5_16 : subd7_5 [-4, 4] = true := by decide +kernel
theorem subd7_5_17 : subd7_5 [-3, -6] = true := by decide +kernel
theorem subd7_5_18 : subd7_5 [-3, -5] = true := by decide +kernel
theorem subd7_5_19 : subd7_5 [-3, -4] = true := by decide +kernel
theorem subd7_5_20 : subd7_5 [-3, -3] = true := by decide +kernel
theorem subd7_5_21 : subd7_5 [-3, -2] = true := by decide +kernel
theorem subd7_5_22 : subd7_5 [-3, -1] = true := by decide +kernel
theorem subd7_5_23 : subd7_5 [-3, 0] = true := by decide +kernel
theorem subd7_5_24 : subd7_5 [-3, 1] = true := by decide +kernel
theorem subd7_5_25 : subd7_5 [-3, 2] = true := by decide +kernel
theorem subd7_5_26 : subd7_5 [-3, 3] = true := by decide +kernel
theorem subd7_5_27 : subd7_5 [-3, 4] = true := by decide +kernel
theorem subd7_5_28 : subd7_5 [-2, -6] = true := by decide +kernel
theorem subd7_5_29 : subd7_5 [-2, -5] = true := by decide +kernel
theorem subd7_5_30 : subd7_5 [-2, -4] = true := by decide +kernel
theorem subd7_5_31 : subd7_5 [-2, -3] = true := by decide +kernel
theorem sbd7_5_0 : ∀ q ∈ blkd7_5_0, subd7_5 q = true := by
  unfold blkd7_5_0
  exact List.forall_mem_cons.2 ⟨subd7_5_0, List.forall_mem_cons.2 ⟨subd7_5_1, List.forall_mem_cons.2 ⟨subd7_5_2, List.forall_mem_cons.2 ⟨subd7_5_3, List.forall_mem_cons.2 ⟨subd7_5_4, List.forall_mem_cons.2 ⟨subd7_5_5, List.forall_mem_cons.2 ⟨subd7_5_6, List.forall_mem_cons.2 ⟨subd7_5_7, List.forall_mem_cons.2 ⟨subd7_5_8, List.forall_mem_cons.2 ⟨subd7_5_9, List.forall_mem_cons.2 ⟨subd7_5_10, List.forall_mem_cons.2 ⟨subd7_5_11, List.forall_mem_cons.2 ⟨subd7_5_12, List.forall_mem_cons.2 ⟨subd7_5_13, List.forall_mem_cons.2 ⟨subd7_5_14, List.forall_mem_cons.2 ⟨subd7_5_15, List.forall_mem_cons.2 ⟨subd7_5_16, List.forall_mem_cons.2 ⟨subd7_5_17, List.forall_mem_cons.2 ⟨subd7_5_18, List.forall_mem_cons.2 ⟨subd7_5_19, List.forall_mem_cons.2 ⟨subd7_5_20, List.forall_mem_cons.2 ⟨subd7_5_21, List.forall_mem_cons.2 ⟨subd7_5_22, List.forall_mem_cons.2 ⟨subd7_5_23, List.forall_mem_cons.2 ⟨subd7_5_24, List.forall_mem_cons.2 ⟨subd7_5_25, List.forall_mem_cons.2 ⟨subd7_5_26, List.forall_mem_cons.2 ⟨subd7_5_27, List.forall_mem_cons.2 ⟨subd7_5_28, List.forall_mem_cons.2 ⟨subd7_5_29, List.forall_mem_cons.2 ⟨subd7_5_30, List.forall_mem_cons.2 ⟨subd7_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_32 : subd7_5 [-2, -2] = true := by decide +kernel
theorem subd7_5_33 : subd7_5 [-2, -1, -7] = true := by decide +kernel
theorem subd7_5_34 : subd7_5 [-2, -1, -6] = true := by decide +kernel
theorem subd7_5_35 : subd7_5 [-2, -1, -5] = true := by decide +kernel
theorem subd7_5_36 : subd7_5 [-2, -1, -4] = true := by decide +kernel
theorem subd7_5_37 : subd7_5 [-2, -1, -3] = true := by decide +kernel
theorem subd7_5_38 : subd7_5 [-2, -1, -2] = true := by decide +kernel
theorem subd7_5_39 : subd7_5 [-2, -1, -1] = true := by decide +kernel
theorem subd7_5_40 : subd7_5 [-2, -1, 0] = true := by decide +kernel
theorem subd7_5_41 : subd7_5 [-2, -1, 1] = true := by decide +kernel
theorem subd7_5_42 : subd7_5 [-2, -1, 2] = true := by decide +kernel
theorem subd7_5_43 : subd7_5 [-2, -1, 3] = true := by decide +kernel
theorem subd7_5_44 : subd7_5 [-2, -1, 4] = true := by decide +kernel
theorem subd7_5_45 : subd7_5 [-2, -1, 5] = true := by decide +kernel
theorem subd7_5_46 : subd7_5 [-2, 0, -7] = true := by decide +kernel
theorem subd7_5_47 : subd7_5 [-2, 0, -6] = true := by decide +kernel
theorem subd7_5_48 : subd7_5 [-2, 0, -5] = true := by decide +kernel
theorem subd7_5_49 : subd7_5 [-2, 0, -4] = true := by decide +kernel
theorem subd7_5_50 : subd7_5 [-2, 0, -3] = true := by decide +kernel
theorem subd7_5_51 : subd7_5 [-2, 0, -2] = true := by decide +kernel
theorem subd7_5_52 : subd7_5 [-2, 0, -1] = true := by decide +kernel
theorem subd7_5_53 : subd7_5 [-2, 0, 0] = true := by decide +kernel
theorem subd7_5_54 : subd7_5 [-2, 0, 1] = true := by decide +kernel
theorem subd7_5_55 : subd7_5 [-2, 0, 2] = true := by decide +kernel
theorem subd7_5_56 : subd7_5 [-2, 0, 3] = true := by decide +kernel
theorem subd7_5_57 : subd7_5 [-2, 0, 4] = true := by decide +kernel
theorem subd7_5_58 : subd7_5 [-2, 0, 5] = true := by decide +kernel
theorem subd7_5_59 : subd7_5 [-2, 0, 6] = true := by decide +kernel
theorem subd7_5_60 : subd7_5 [-2, 1, -7] = true := by decide +kernel
theorem subd7_5_61 : subd7_5 [-2, 1, -6] = true := by decide +kernel
theorem subd7_5_62 : subd7_5 [-2, 1, -5] = true := by decide +kernel
theorem subd7_5_63 : subd7_5 [-2, 1, -4] = true := by decide +kernel
theorem sbd7_5_1 : ∀ q ∈ blkd7_5_1, subd7_5 q = true := by
  unfold blkd7_5_1
  exact List.forall_mem_cons.2 ⟨subd7_5_32, List.forall_mem_cons.2 ⟨subd7_5_33, List.forall_mem_cons.2 ⟨subd7_5_34, List.forall_mem_cons.2 ⟨subd7_5_35, List.forall_mem_cons.2 ⟨subd7_5_36, List.forall_mem_cons.2 ⟨subd7_5_37, List.forall_mem_cons.2 ⟨subd7_5_38, List.forall_mem_cons.2 ⟨subd7_5_39, List.forall_mem_cons.2 ⟨subd7_5_40, List.forall_mem_cons.2 ⟨subd7_5_41, List.forall_mem_cons.2 ⟨subd7_5_42, List.forall_mem_cons.2 ⟨subd7_5_43, List.forall_mem_cons.2 ⟨subd7_5_44, List.forall_mem_cons.2 ⟨subd7_5_45, List.forall_mem_cons.2 ⟨subd7_5_46, List.forall_mem_cons.2 ⟨subd7_5_47, List.forall_mem_cons.2 ⟨subd7_5_48, List.forall_mem_cons.2 ⟨subd7_5_49, List.forall_mem_cons.2 ⟨subd7_5_50, List.forall_mem_cons.2 ⟨subd7_5_51, List.forall_mem_cons.2 ⟨subd7_5_52, List.forall_mem_cons.2 ⟨subd7_5_53, List.forall_mem_cons.2 ⟨subd7_5_54, List.forall_mem_cons.2 ⟨subd7_5_55, List.forall_mem_cons.2 ⟨subd7_5_56, List.forall_mem_cons.2 ⟨subd7_5_57, List.forall_mem_cons.2 ⟨subd7_5_58, List.forall_mem_cons.2 ⟨subd7_5_59, List.forall_mem_cons.2 ⟨subd7_5_60, List.forall_mem_cons.2 ⟨subd7_5_61, List.forall_mem_cons.2 ⟨subd7_5_62, List.forall_mem_cons.2 ⟨subd7_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_64 : subd7_5 [-2, 1, -3] = true := by decide +kernel
theorem subd7_5_65 : subd7_5 [-2, 1, -2] = true := by decide +kernel
theorem subd7_5_66 : subd7_5 [-2, 1, -1] = true := by decide +kernel
theorem subd7_5_67 : subd7_5 [-2, 1, 0] = true := by decide +kernel
theorem subd7_5_68 : subd7_5 [-2, 1, 1] = true := by decide +kernel
theorem subd7_5_69 : subd7_5 [-2, 1, 2] = true := by decide +kernel
theorem subd7_5_70 : subd7_5 [-2, 1, 3] = true := by decide +kernel
theorem subd7_5_71 : subd7_5 [-2, 1, 4] = true := by decide +kernel
theorem subd7_5_72 : subd7_5 [-2, 1, 5] = true := by decide +kernel
theorem subd7_5_73 : subd7_5 [-2, 1, 6] = true := by decide +kernel
theorem subd7_5_74 : subd7_5 [-2, 2] = true := by decide +kernel
theorem subd7_5_75 : subd7_5 [-2, 3] = true := by decide +kernel
theorem subd7_5_76 : subd7_5 [-2, 4] = true := by decide +kernel
theorem subd7_5_77 : subd7_5 [-2, 5] = true := by decide +kernel
theorem subd7_5_78 : subd7_5 [-1, -6] = true := by decide +kernel
theorem subd7_5_79 : subd7_5 [-1, -5] = true := by decide +kernel
theorem subd7_5_80 : subd7_5 [-1, -4] = true := by decide +kernel
theorem subd7_5_81 : subd7_5 [-1, -3] = true := by decide +kernel
theorem subd7_5_82 : subd7_5 [-1, -2, -7] = true := by decide +kernel
theorem subd7_5_83 : subd7_5 [-1, -2, -6] = true := by decide +kernel
theorem subd7_5_84 : subd7_5 [-1, -2, -5] = true := by decide +kernel
theorem subd7_5_85 : subd7_5 [-1, -2, -4] = true := by decide +kernel
theorem subd7_5_86 : subd7_5 [-1, -2, -3] = true := by decide +kernel
theorem subd7_5_87 : subd7_5 [-1, -2, -2] = true := by decide +kernel
theorem subd7_5_88 : subd7_5 [-1, -2, -1] = true := by decide +kernel
theorem subd7_5_89 : subd7_5 [-1, -2, 0] = true := by decide +kernel
theorem subd7_5_90 : subd7_5 [-1, -2, 1] = true := by decide +kernel
theorem subd7_5_91 : subd7_5 [-1, -2, 2] = true := by decide +kernel
theorem subd7_5_92 : subd7_5 [-1, -2, 3] = true := by decide +kernel
theorem subd7_5_93 : subd7_5 [-1, -2, 4] = true := by decide +kernel
theorem subd7_5_94 : subd7_5 [-1, -2, 5] = true := by decide +kernel
theorem subd7_5_95 : subd7_5 [-1, -1, -8] = true := by decide +kernel
theorem sbd7_5_2 : ∀ q ∈ blkd7_5_2, subd7_5 q = true := by
  unfold blkd7_5_2
  exact List.forall_mem_cons.2 ⟨subd7_5_64, List.forall_mem_cons.2 ⟨subd7_5_65, List.forall_mem_cons.2 ⟨subd7_5_66, List.forall_mem_cons.2 ⟨subd7_5_67, List.forall_mem_cons.2 ⟨subd7_5_68, List.forall_mem_cons.2 ⟨subd7_5_69, List.forall_mem_cons.2 ⟨subd7_5_70, List.forall_mem_cons.2 ⟨subd7_5_71, List.forall_mem_cons.2 ⟨subd7_5_72, List.forall_mem_cons.2 ⟨subd7_5_73, List.forall_mem_cons.2 ⟨subd7_5_74, List.forall_mem_cons.2 ⟨subd7_5_75, List.forall_mem_cons.2 ⟨subd7_5_76, List.forall_mem_cons.2 ⟨subd7_5_77, List.forall_mem_cons.2 ⟨subd7_5_78, List.forall_mem_cons.2 ⟨subd7_5_79, List.forall_mem_cons.2 ⟨subd7_5_80, List.forall_mem_cons.2 ⟨subd7_5_81, List.forall_mem_cons.2 ⟨subd7_5_82, List.forall_mem_cons.2 ⟨subd7_5_83, List.forall_mem_cons.2 ⟨subd7_5_84, List.forall_mem_cons.2 ⟨subd7_5_85, List.forall_mem_cons.2 ⟨subd7_5_86, List.forall_mem_cons.2 ⟨subd7_5_87, List.forall_mem_cons.2 ⟨subd7_5_88, List.forall_mem_cons.2 ⟨subd7_5_89, List.forall_mem_cons.2 ⟨subd7_5_90, List.forall_mem_cons.2 ⟨subd7_5_91, List.forall_mem_cons.2 ⟨subd7_5_92, List.forall_mem_cons.2 ⟨subd7_5_93, List.forall_mem_cons.2 ⟨subd7_5_94, List.forall_mem_cons.2 ⟨subd7_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_96 : subd7_5 [-1, -1, -7] = true := by decide +kernel
theorem subd7_5_97 : subd7_5 [-1, -1, -6] = true := by decide +kernel
theorem subd7_5_98 : subd7_5 [-1, -1, -5] = true := by decide +kernel
theorem subd7_5_99 : subd7_5 [-1, -1, -4] = true := by decide +kernel
theorem subd7_5_100 : subd7_5 [-1, -1, -3] = true := by decide +kernel
theorem subd7_5_101 : subd7_5 [-1, -1, -2] = true := by decide +kernel
theorem subd7_5_102 : subd7_5 [-1, -1, -1] = true := by decide +kernel
theorem subd7_5_103 : subd7_5 [-1, -1, 0] = true := by decide +kernel
theorem subd7_5_104 : subd7_5 [-1, -1, 1] = true := by decide +kernel
theorem subd7_5_105 : subd7_5 [-1, -1, 2] = true := by decide +kernel
theorem subd7_5_106 : subd7_5 [-1, -1, 3] = true := by decide +kernel
theorem subd7_5_107 : subd7_5 [-1, -1, 4] = true := by decide +kernel
theorem subd7_5_108 : subd7_5 [-1, -1, 5] = true := by decide +kernel
theorem subd7_5_109 : subd7_5 [-1, -1, 6] = true := by decide +kernel
theorem subd7_5_110 : subd7_5 [-1, 0, -8] = true := by decide +kernel
theorem subd7_5_111 : subd7_5 [-1, 0, -7] = true := by decide +kernel
theorem subd7_5_112 : subd7_5 [-1, 0, -6] = true := by decide +kernel
theorem subd7_5_113 : subd7_5 [-1, 0, -5] = true := by decide +kernel
theorem subd7_5_114 : subd7_5 [-1, 0, -4] = true := by decide +kernel
theorem subd7_5_115 : subd7_5 [-1, 0, -3] = true := by decide +kernel
theorem subd7_5_116 : subd7_5 [-1, 0, -2] = true := by decide +kernel
theorem subd7_5_117 : subd7_5 [-1, 0, -1] = true := by decide +kernel
theorem subd7_5_118 : subd7_5 [-1, 0, 0] = true := by decide +kernel
theorem subd7_5_119 : subd7_5 [-1, 0, 1] = true := by decide +kernel
theorem subd7_5_120 : subd7_5 [-1, 0, 2] = true := by decide +kernel
theorem subd7_5_121 : subd7_5 [-1, 0, 3] = true := by decide +kernel
theorem subd7_5_122 : subd7_5 [-1, 0, 4] = true := by decide +kernel
theorem subd7_5_123 : subd7_5 [-1, 0, 5] = true := by decide +kernel
theorem subd7_5_124 : subd7_5 [-1, 0, 6] = true := by decide +kernel
theorem subd7_5_125 : subd7_5 [-1, 1, -7] = true := by decide +kernel
theorem subd7_5_126 : subd7_5 [-1, 1, -6] = true := by decide +kernel
theorem subd7_5_127 : subd7_5 [-1, 1, -5] = true := by decide +kernel
theorem sbd7_5_3 : ∀ q ∈ blkd7_5_3, subd7_5 q = true := by
  unfold blkd7_5_3
  exact List.forall_mem_cons.2 ⟨subd7_5_96, List.forall_mem_cons.2 ⟨subd7_5_97, List.forall_mem_cons.2 ⟨subd7_5_98, List.forall_mem_cons.2 ⟨subd7_5_99, List.forall_mem_cons.2 ⟨subd7_5_100, List.forall_mem_cons.2 ⟨subd7_5_101, List.forall_mem_cons.2 ⟨subd7_5_102, List.forall_mem_cons.2 ⟨subd7_5_103, List.forall_mem_cons.2 ⟨subd7_5_104, List.forall_mem_cons.2 ⟨subd7_5_105, List.forall_mem_cons.2 ⟨subd7_5_106, List.forall_mem_cons.2 ⟨subd7_5_107, List.forall_mem_cons.2 ⟨subd7_5_108, List.forall_mem_cons.2 ⟨subd7_5_109, List.forall_mem_cons.2 ⟨subd7_5_110, List.forall_mem_cons.2 ⟨subd7_5_111, List.forall_mem_cons.2 ⟨subd7_5_112, List.forall_mem_cons.2 ⟨subd7_5_113, List.forall_mem_cons.2 ⟨subd7_5_114, List.forall_mem_cons.2 ⟨subd7_5_115, List.forall_mem_cons.2 ⟨subd7_5_116, List.forall_mem_cons.2 ⟨subd7_5_117, List.forall_mem_cons.2 ⟨subd7_5_118, List.forall_mem_cons.2 ⟨subd7_5_119, List.forall_mem_cons.2 ⟨subd7_5_120, List.forall_mem_cons.2 ⟨subd7_5_121, List.forall_mem_cons.2 ⟨subd7_5_122, List.forall_mem_cons.2 ⟨subd7_5_123, List.forall_mem_cons.2 ⟨subd7_5_124, List.forall_mem_cons.2 ⟨subd7_5_125, List.forall_mem_cons.2 ⟨subd7_5_126, List.forall_mem_cons.2 ⟨subd7_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_128 : subd7_5 [-1, 1, -4] = true := by decide +kernel
theorem subd7_5_129 : subd7_5 [-1, 1, -3] = true := by decide +kernel
theorem subd7_5_130 : subd7_5 [-1, 1, -2] = true := by decide +kernel
theorem subd7_5_131 : subd7_5 [-1, 1, -1] = true := by decide +kernel
theorem subd7_5_132 : subd7_5 [-1, 1, 0] = true := by decide +kernel
theorem subd7_5_133 : subd7_5 [-1, 1, 1] = true := by decide +kernel
theorem subd7_5_134 : subd7_5 [-1, 1, 2] = true := by decide +kernel
theorem subd7_5_135 : subd7_5 [-1, 1, 3] = true := by decide +kernel
theorem subd7_5_136 : subd7_5 [-1, 1, 4] = true := by decide +kernel
theorem subd7_5_137 : subd7_5 [-1, 1, 5] = true := by decide +kernel
theorem subd7_5_138 : subd7_5 [-1, 1, 6] = true := by decide +kernel
theorem subd7_5_139 : subd7_5 [-1, 2, -7] = true := by decide +kernel
theorem subd7_5_140 : subd7_5 [-1, 2, -6] = true := by decide +kernel
theorem subd7_5_141 : subd7_5 [-1, 2, -5] = true := by decide +kernel
theorem subd7_5_142 : subd7_5 [-1, 2, -4] = true := by decide +kernel
theorem subd7_5_143 : subd7_5 [-1, 2, -3] = true := by decide +kernel
theorem subd7_5_144 : subd7_5 [-1, 2, -2] = true := by decide +kernel
theorem subd7_5_145 : subd7_5 [-1, 2, -1] = true := by decide +kernel
theorem subd7_5_146 : subd7_5 [-1, 2, 0] = true := by decide +kernel
theorem subd7_5_147 : subd7_5 [-1, 2, 1] = true := by decide +kernel
theorem subd7_5_148 : subd7_5 [-1, 2, 2] = true := by decide +kernel
theorem subd7_5_149 : subd7_5 [-1, 2, 3] = true := by decide +kernel
theorem subd7_5_150 : subd7_5 [-1, 2, 4] = true := by decide +kernel
theorem subd7_5_151 : subd7_5 [-1, 2, 5] = true := by decide +kernel
theorem subd7_5_152 : subd7_5 [-1, 2, 6] = true := by decide +kernel
theorem subd7_5_153 : subd7_5 [-1, 3] = true := by decide +kernel
theorem subd7_5_154 : subd7_5 [-1, 4] = true := by decide +kernel
theorem subd7_5_155 : subd7_5 [-1, 5] = true := by decide +kernel
theorem subd7_5_156 : subd7_5 [0, -6] = true := by decide +kernel
theorem subd7_5_157 : subd7_5 [0, -5] = true := by decide +kernel
theorem subd7_5_158 : subd7_5 [0, -4] = true := by decide +kernel
theorem subd7_5_159 : subd7_5 [0, -3] = true := by decide +kernel
theorem sbd7_5_4 : ∀ q ∈ blkd7_5_4, subd7_5 q = true := by
  unfold blkd7_5_4
  exact List.forall_mem_cons.2 ⟨subd7_5_128, List.forall_mem_cons.2 ⟨subd7_5_129, List.forall_mem_cons.2 ⟨subd7_5_130, List.forall_mem_cons.2 ⟨subd7_5_131, List.forall_mem_cons.2 ⟨subd7_5_132, List.forall_mem_cons.2 ⟨subd7_5_133, List.forall_mem_cons.2 ⟨subd7_5_134, List.forall_mem_cons.2 ⟨subd7_5_135, List.forall_mem_cons.2 ⟨subd7_5_136, List.forall_mem_cons.2 ⟨subd7_5_137, List.forall_mem_cons.2 ⟨subd7_5_138, List.forall_mem_cons.2 ⟨subd7_5_139, List.forall_mem_cons.2 ⟨subd7_5_140, List.forall_mem_cons.2 ⟨subd7_5_141, List.forall_mem_cons.2 ⟨subd7_5_142, List.forall_mem_cons.2 ⟨subd7_5_143, List.forall_mem_cons.2 ⟨subd7_5_144, List.forall_mem_cons.2 ⟨subd7_5_145, List.forall_mem_cons.2 ⟨subd7_5_146, List.forall_mem_cons.2 ⟨subd7_5_147, List.forall_mem_cons.2 ⟨subd7_5_148, List.forall_mem_cons.2 ⟨subd7_5_149, List.forall_mem_cons.2 ⟨subd7_5_150, List.forall_mem_cons.2 ⟨subd7_5_151, List.forall_mem_cons.2 ⟨subd7_5_152, List.forall_mem_cons.2 ⟨subd7_5_153, List.forall_mem_cons.2 ⟨subd7_5_154, List.forall_mem_cons.2 ⟨subd7_5_155, List.forall_mem_cons.2 ⟨subd7_5_156, List.forall_mem_cons.2 ⟨subd7_5_157, List.forall_mem_cons.2 ⟨subd7_5_158, List.forall_mem_cons.2 ⟨subd7_5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
