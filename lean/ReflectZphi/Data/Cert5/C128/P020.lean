import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_1_480 : subd5_1 [2, -1, -3] = true := by decide +kernel
theorem subd5_1_481 : subd5_1 [2, -1, -2] = true := by decide +kernel
theorem subd5_1_482 : subd5_1 [2, -1, -1] = true := by decide +kernel
theorem subd5_1_483 : subd5_1 [2, -1, 0] = true := by decide +kernel
theorem subd5_1_484 : subd5_1 [2, -1, 1] = true := by decide +kernel
theorem subd5_1_485 : subd5_1 [2, -1, 2] = true := by decide +kernel
theorem subd5_1_486 : subd5_1 [2, -1, 3] = true := by decide +kernel
theorem subd5_1_487 : subd5_1 [2, -1, 4] = true := by decide +kernel
theorem subd5_1_488 : subd5_1 [2, -1, 5] = true := by decide +kernel
theorem subd5_1_489 : subd5_1 [2, -1, 6] = true := by decide +kernel
theorem subd5_1_490 : subd5_1 [2, -1, 7] = true := by decide +kernel
theorem subd5_1_491 : subd5_1 [2, -1, 8] = true := by decide +kernel
theorem subd5_1_492 : subd5_1 [2, 0, -6] = true := by decide +kernel
theorem subd5_1_493 : subd5_1 [2, 0, -5] = true := by decide +kernel
theorem subd5_1_494 : subd5_1 [2, 0, -4] = true := by decide +kernel
theorem subd5_1_495 : subd5_1 [2, 0, -3] = true := by decide +kernel
theorem subd5_1_496 : subd5_1 [2, 0, -2] = true := by decide +kernel
theorem subd5_1_497 : subd5_1 [2, 0, -1] = true := by decide +kernel
theorem subd5_1_498 : subd5_1 [2, 0, 0] = true := by decide +kernel
theorem subd5_1_499 : subd5_1 [2, 0, 1] = true := by decide +kernel
theorem subd5_1_500 : subd5_1 [2, 0, 2] = true := by decide +kernel
theorem subd5_1_501 : subd5_1 [2, 0, 3] = true := by decide +kernel
theorem subd5_1_502 : subd5_1 [2, 0, 4] = true := by decide +kernel
theorem subd5_1_503 : subd5_1 [2, 0, 5] = true := by decide +kernel
theorem subd5_1_504 : subd5_1 [2, 0, 6] = true := by decide +kernel
theorem subd5_1_505 : subd5_1 [2, 0, 7] = true := by decide +kernel
theorem subd5_1_506 : subd5_1 [2, 1, -7] = true := by decide +kernel
theorem subd5_1_507 : subd5_1 [2, 1, -6] = true := by decide +kernel
theorem subd5_1_508 : subd5_1 [2, 1, -5] = true := by decide +kernel
theorem subd5_1_509 : subd5_1 [2, 1, -4] = true := by decide +kernel
theorem subd5_1_510 : subd5_1 [2, 1, -3] = true := by decide +kernel
theorem subd5_1_511 : subd5_1 [2, 1, -2] = true := by decide +kernel
theorem sbd5_1_15 : ∀ q ∈ blkd5_1_15, subd5_1 q = true := by
  unfold blkd5_1_15
  exact List.forall_mem_cons.2 ⟨subd5_1_480, List.forall_mem_cons.2 ⟨subd5_1_481, List.forall_mem_cons.2 ⟨subd5_1_482, List.forall_mem_cons.2 ⟨subd5_1_483, List.forall_mem_cons.2 ⟨subd5_1_484, List.forall_mem_cons.2 ⟨subd5_1_485, List.forall_mem_cons.2 ⟨subd5_1_486, List.forall_mem_cons.2 ⟨subd5_1_487, List.forall_mem_cons.2 ⟨subd5_1_488, List.forall_mem_cons.2 ⟨subd5_1_489, List.forall_mem_cons.2 ⟨subd5_1_490, List.forall_mem_cons.2 ⟨subd5_1_491, List.forall_mem_cons.2 ⟨subd5_1_492, List.forall_mem_cons.2 ⟨subd5_1_493, List.forall_mem_cons.2 ⟨subd5_1_494, List.forall_mem_cons.2 ⟨subd5_1_495, List.forall_mem_cons.2 ⟨subd5_1_496, List.forall_mem_cons.2 ⟨subd5_1_497, List.forall_mem_cons.2 ⟨subd5_1_498, List.forall_mem_cons.2 ⟨subd5_1_499, List.forall_mem_cons.2 ⟨subd5_1_500, List.forall_mem_cons.2 ⟨subd5_1_501, List.forall_mem_cons.2 ⟨subd5_1_502, List.forall_mem_cons.2 ⟨subd5_1_503, List.forall_mem_cons.2 ⟨subd5_1_504, List.forall_mem_cons.2 ⟨subd5_1_505, List.forall_mem_cons.2 ⟨subd5_1_506, List.forall_mem_cons.2 ⟨subd5_1_507, List.forall_mem_cons.2 ⟨subd5_1_508, List.forall_mem_cons.2 ⟨subd5_1_509, List.forall_mem_cons.2 ⟨subd5_1_510, List.forall_mem_cons.2 ⟨subd5_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_512 : subd5_1 [2, 1, -1] = true := by decide +kernel
theorem subd5_1_513 : subd5_1 [2, 1, 0] = true := by decide +kernel
theorem subd5_1_514 : subd5_1 [2, 1, 1] = true := by decide +kernel
theorem subd5_1_515 : subd5_1 [2, 1, 2] = true := by decide +kernel
theorem subd5_1_516 : subd5_1 [2, 1, 3] = true := by decide +kernel
theorem subd5_1_517 : subd5_1 [2, 1, 4] = true := by decide +kernel
theorem subd5_1_518 : subd5_1 [2, 1, 5] = true := by decide +kernel
theorem subd5_1_519 : subd5_1 [2, 1, 6] = true := by decide +kernel
theorem subd5_1_520 : subd5_1 [2, 1, 7] = true := by decide +kernel
theorem subd5_1_521 : subd5_1 [2, 2, -7] = true := by decide +kernel
theorem subd5_1_522 : subd5_1 [2, 2, -6] = true := by decide +kernel
theorem subd5_1_523 : subd5_1 [2, 2, -5] = true := by decide +kernel
theorem subd5_1_524 : subd5_1 [2, 2, -4] = true := by decide +kernel
theorem subd5_1_525 : subd5_1 [2, 2, -3] = true := by decide +kernel
theorem subd5_1_526 : subd5_1 [2, 2, -2] = true := by decide +kernel
theorem subd5_1_527 : subd5_1 [2, 2, -1] = true := by decide +kernel
theorem subd5_1_528 : subd5_1 [2, 2, 0] = true := by decide +kernel
theorem subd5_1_529 : subd5_1 [2, 2, 1] = true := by decide +kernel
theorem subd5_1_530 : subd5_1 [2, 2, 2] = true := by decide +kernel
theorem subd5_1_531 : subd5_1 [2, 2, 3] = true := by decide +kernel
theorem subd5_1_532 : subd5_1 [2, 2, 4] = true := by decide +kernel
theorem subd5_1_533 : subd5_1 [2, 2, 5] = true := by decide +kernel
theorem subd5_1_534 : subd5_1 [2, 2, 6] = true := by decide +kernel
theorem subd5_1_535 : subd5_1 [2, 3] = true := by decide +kernel
theorem subd5_1_536 : subd5_1 [2, 4] = true := by decide +kernel
theorem subd5_1_537 : subd5_1 [2, 5] = true := by decide +kernel
theorem subd5_1_538 : subd5_1 [3, -5] = true := by decide +kernel
theorem subd5_1_539 : subd5_1 [3, -4] = true := by decide +kernel
theorem subd5_1_540 : subd5_1 [3, -3] = true := by decide +kernel
theorem subd5_1_541 : subd5_1 [3, -2] = true := by decide +kernel
theorem subd5_1_542 : subd5_1 [3, -1] = true := by decide +kernel
theorem subd5_1_543 : subd5_1 [3, 0, -5] = true := by decide +kernel
theorem sbd5_1_16 : ∀ q ∈ blkd5_1_16, subd5_1 q = true := by
  unfold blkd5_1_16
  exact List.forall_mem_cons.2 ⟨subd5_1_512, List.forall_mem_cons.2 ⟨subd5_1_513, List.forall_mem_cons.2 ⟨subd5_1_514, List.forall_mem_cons.2 ⟨subd5_1_515, List.forall_mem_cons.2 ⟨subd5_1_516, List.forall_mem_cons.2 ⟨subd5_1_517, List.forall_mem_cons.2 ⟨subd5_1_518, List.forall_mem_cons.2 ⟨subd5_1_519, List.forall_mem_cons.2 ⟨subd5_1_520, List.forall_mem_cons.2 ⟨subd5_1_521, List.forall_mem_cons.2 ⟨subd5_1_522, List.forall_mem_cons.2 ⟨subd5_1_523, List.forall_mem_cons.2 ⟨subd5_1_524, List.forall_mem_cons.2 ⟨subd5_1_525, List.forall_mem_cons.2 ⟨subd5_1_526, List.forall_mem_cons.2 ⟨subd5_1_527, List.forall_mem_cons.2 ⟨subd5_1_528, List.forall_mem_cons.2 ⟨subd5_1_529, List.forall_mem_cons.2 ⟨subd5_1_530, List.forall_mem_cons.2 ⟨subd5_1_531, List.forall_mem_cons.2 ⟨subd5_1_532, List.forall_mem_cons.2 ⟨subd5_1_533, List.forall_mem_cons.2 ⟨subd5_1_534, List.forall_mem_cons.2 ⟨subd5_1_535, List.forall_mem_cons.2 ⟨subd5_1_536, List.forall_mem_cons.2 ⟨subd5_1_537, List.forall_mem_cons.2 ⟨subd5_1_538, List.forall_mem_cons.2 ⟨subd5_1_539, List.forall_mem_cons.2 ⟨subd5_1_540, List.forall_mem_cons.2 ⟨subd5_1_541, List.forall_mem_cons.2 ⟨subd5_1_542, List.forall_mem_cons.2 ⟨subd5_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_544 : subd5_1 [3, 0, -4] = true := by decide +kernel
theorem subd5_1_545 : subd5_1 [3, 0, -3] = true := by decide +kernel
theorem subd5_1_546 : subd5_1 [3, 0, -2] = true := by decide +kernel
theorem subd5_1_547 : subd5_1 [3, 0, -1] = true := by decide +kernel
theorem subd5_1_548 : subd5_1 [3, 0, 0] = true := by decide +kernel
theorem subd5_1_549 : subd5_1 [3, 0, 1] = true := by decide +kernel
theorem subd5_1_550 : subd5_1 [3, 0, 2] = true := by decide +kernel
theorem subd5_1_551 : subd5_1 [3, 0, 3] = true := by decide +kernel
theorem subd5_1_552 : subd5_1 [3, 0, 4] = true := by decide +kernel
theorem subd5_1_553 : subd5_1 [3, 0, 5] = true := by decide +kernel
theorem subd5_1_554 : subd5_1 [3, 0, 6] = true := by decide +kernel
theorem subd5_1_555 : subd5_1 [3, 0, 7] = true := by decide +kernel
theorem subd5_1_556 : subd5_1 [3, 1, -6] = true := by decide +kernel
theorem subd5_1_557 : subd5_1 [3, 1, -5] = true := by decide +kernel
theorem subd5_1_558 : subd5_1 [3, 1, -4] = true := by decide +kernel
theorem subd5_1_559 : subd5_1 [3, 1, -3] = true := by decide +kernel
theorem subd5_1_560 : subd5_1 [3, 1, -2] = true := by decide +kernel
theorem subd5_1_561 : subd5_1 [3, 1, -1] = true := by decide +kernel
theorem subd5_1_562 : subd5_1 [3, 1, 0] = true := by decide +kernel
theorem subd5_1_563 : subd5_1 [3, 1, 1] = true := by decide +kernel
theorem subd5_1_564 : subd5_1 [3, 1, 2] = true := by decide +kernel
theorem subd5_1_565 : subd5_1 [3, 1, 3] = true := by decide +kernel
theorem subd5_1_566 : subd5_1 [3, 1, 4] = true := by decide +kernel
theorem subd5_1_567 : subd5_1 [3, 1, 5] = true := by decide +kernel
theorem subd5_1_568 : subd5_1 [3, 1, 6] = true := by decide +kernel
theorem subd5_1_569 : subd5_1 [3, 1, 7] = true := by decide +kernel
theorem subd5_1_570 : subd5_1 [3, 2] = true := by decide +kernel
theorem subd5_1_571 : subd5_1 [3, 3] = true := by decide +kernel
theorem subd5_1_572 : subd5_1 [3, 4] = true := by decide +kernel
theorem subd5_1_573 : subd5_1 [3, 5] = true := by decide +kernel
theorem subd5_1_574 : subd5_1 [4, -5] = true := by decide +kernel
theorem subd5_1_575 : subd5_1 [4, -4] = true := by decide +kernel
theorem sbd5_1_17 : ∀ q ∈ blkd5_1_17, subd5_1 q = true := by
  unfold blkd5_1_17
  exact List.forall_mem_cons.2 ⟨subd5_1_544, List.forall_mem_cons.2 ⟨subd5_1_545, List.forall_mem_cons.2 ⟨subd5_1_546, List.forall_mem_cons.2 ⟨subd5_1_547, List.forall_mem_cons.2 ⟨subd5_1_548, List.forall_mem_cons.2 ⟨subd5_1_549, List.forall_mem_cons.2 ⟨subd5_1_550, List.forall_mem_cons.2 ⟨subd5_1_551, List.forall_mem_cons.2 ⟨subd5_1_552, List.forall_mem_cons.2 ⟨subd5_1_553, List.forall_mem_cons.2 ⟨subd5_1_554, List.forall_mem_cons.2 ⟨subd5_1_555, List.forall_mem_cons.2 ⟨subd5_1_556, List.forall_mem_cons.2 ⟨subd5_1_557, List.forall_mem_cons.2 ⟨subd5_1_558, List.forall_mem_cons.2 ⟨subd5_1_559, List.forall_mem_cons.2 ⟨subd5_1_560, List.forall_mem_cons.2 ⟨subd5_1_561, List.forall_mem_cons.2 ⟨subd5_1_562, List.forall_mem_cons.2 ⟨subd5_1_563, List.forall_mem_cons.2 ⟨subd5_1_564, List.forall_mem_cons.2 ⟨subd5_1_565, List.forall_mem_cons.2 ⟨subd5_1_566, List.forall_mem_cons.2 ⟨subd5_1_567, List.forall_mem_cons.2 ⟨subd5_1_568, List.forall_mem_cons.2 ⟨subd5_1_569, List.forall_mem_cons.2 ⟨subd5_1_570, List.forall_mem_cons.2 ⟨subd5_1_571, List.forall_mem_cons.2 ⟨subd5_1_572, List.forall_mem_cons.2 ⟨subd5_1_573, List.forall_mem_cons.2 ⟨subd5_1_574, List.forall_mem_cons.2 ⟨subd5_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_576 : subd5_1 [4, -3] = true := by decide +kernel
theorem subd5_1_577 : subd5_1 [4, -2] = true := by decide +kernel
theorem subd5_1_578 : subd5_1 [4, -1] = true := by decide +kernel
theorem subd5_1_579 : subd5_1 [4, 0] = true := by decide +kernel
theorem subd5_1_580 : subd5_1 [4, 1] = true := by decide +kernel
theorem subd5_1_581 : subd5_1 [4, 2] = true := by decide +kernel
theorem subd5_1_582 : subd5_1 [4, 3] = true := by decide +kernel
theorem subd5_1_583 : subd5_1 [4, 4] = true := by decide +kernel
theorem subd5_1_584 : subd5_1 [5, -3] = true := by decide +kernel
theorem subd5_1_585 : subd5_1 [5, -2] = true := by decide +kernel
theorem subd5_1_586 : subd5_1 [5, -1] = true := by decide +kernel
theorem subd5_1_587 : subd5_1 [5, 0] = true := by decide +kernel
theorem subd5_1_588 : subd5_1 [5, 1] = true := by decide +kernel
theorem subd5_1_589 : subd5_1 [5, 2] = true := by decide +kernel
theorem subd5_1_590 : subd5_1 [5, 3] = true := by decide +kernel
theorem sbd5_1_18 : ∀ q ∈ blkd5_1_18, subd5_1 q = true := by
  unfold blkd5_1_18
  exact List.forall_mem_cons.2 ⟨subd5_1_576, List.forall_mem_cons.2 ⟨subd5_1_577, List.forall_mem_cons.2 ⟨subd5_1_578, List.forall_mem_cons.2 ⟨subd5_1_579, List.forall_mem_cons.2 ⟨subd5_1_580, List.forall_mem_cons.2 ⟨subd5_1_581, List.forall_mem_cons.2 ⟨subd5_1_582, List.forall_mem_cons.2 ⟨subd5_1_583, List.forall_mem_cons.2 ⟨subd5_1_584, List.forall_mem_cons.2 ⟨subd5_1_585, List.forall_mem_cons.2 ⟨subd5_1_586, List.forall_mem_cons.2 ⟨subd5_1_587, List.forall_mem_cons.2 ⟨subd5_1_588, List.forall_mem_cons.2 ⟨subd5_1_589, List.forall_mem_cons.2 ⟨subd5_1_590, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [-5] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-4, -4] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [-4, -3] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [-4, -2] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [-4, -1] = true := by decide +kernel
theorem subd5_2_5 : subd5_2 [-4, 0] = true := by decide +kernel
theorem subd5_2_6 : subd5_2 [-4, 1] = true := by decide +kernel
theorem subd5_2_7 : subd5_2 [-4, 2] = true := by decide +kernel
theorem subd5_2_8 : subd5_2 [-4, 3] = true := by decide +kernel
theorem subd5_2_9 : subd5_2 [-4, 4] = true := by decide +kernel
theorem subd5_2_10 : subd5_2 [-3, -5] = true := by decide +kernel
theorem subd5_2_11 : subd5_2 [-3, -4] = true := by decide +kernel
theorem subd5_2_12 : subd5_2 [-3, -3] = true := by decide +kernel
theorem subd5_2_13 : subd5_2 [-3, -2] = true := by decide +kernel
theorem subd5_2_14 : subd5_2 [-3, -1] = true := by decide +kernel
theorem subd5_2_15 : subd5_2 [-3, 0] = true := by decide +kernel
theorem subd5_2_16 : subd5_2 [-3, 1] = true := by decide +kernel
theorem subd5_2_17 : subd5_2 [-3, 2] = true := by decide +kernel
theorem subd5_2_18 : subd5_2 [-3, 3] = true := by decide +kernel
theorem subd5_2_19 : subd5_2 [-3, 4] = true := by decide +kernel
theorem subd5_2_20 : subd5_2 [-2, -5] = true := by decide +kernel
theorem subd5_2_21 : subd5_2 [-2, -4] = true := by decide +kernel
theorem subd5_2_22 : subd5_2 [-2, -3] = true := by decide +kernel
theorem subd5_2_23 : subd5_2 [-2, -2] = true := by decide +kernel
theorem subd5_2_24 : subd5_2 [-2, -1, -6] = true := by decide +kernel
theorem subd5_2_25 : subd5_2 [-2, -1, -5] = true := by decide +kernel
theorem subd5_2_26 : subd5_2 [-2, -1, -4] = true := by decide +kernel
theorem subd5_2_27 : subd5_2 [-2, -1, -3] = true := by decide +kernel
theorem subd5_2_28 : subd5_2 [-2, -1, -2] = true := by decide +kernel
theorem subd5_2_29 : subd5_2 [-2, -1, -1] = true := by decide +kernel
theorem subd5_2_30 : subd5_2 [-2, -1, 0] = true := by decide +kernel
theorem subd5_2_31 : subd5_2 [-2, -1, 1] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_cons.2 ⟨subd5_2_5, List.forall_mem_cons.2 ⟨subd5_2_6, List.forall_mem_cons.2 ⟨subd5_2_7, List.forall_mem_cons.2 ⟨subd5_2_8, List.forall_mem_cons.2 ⟨subd5_2_9, List.forall_mem_cons.2 ⟨subd5_2_10, List.forall_mem_cons.2 ⟨subd5_2_11, List.forall_mem_cons.2 ⟨subd5_2_12, List.forall_mem_cons.2 ⟨subd5_2_13, List.forall_mem_cons.2 ⟨subd5_2_14, List.forall_mem_cons.2 ⟨subd5_2_15, List.forall_mem_cons.2 ⟨subd5_2_16, List.forall_mem_cons.2 ⟨subd5_2_17, List.forall_mem_cons.2 ⟨subd5_2_18, List.forall_mem_cons.2 ⟨subd5_2_19, List.forall_mem_cons.2 ⟨subd5_2_20, List.forall_mem_cons.2 ⟨subd5_2_21, List.forall_mem_cons.2 ⟨subd5_2_22, List.forall_mem_cons.2 ⟨subd5_2_23, List.forall_mem_cons.2 ⟨subd5_2_24, List.forall_mem_cons.2 ⟨subd5_2_25, List.forall_mem_cons.2 ⟨subd5_2_26, List.forall_mem_cons.2 ⟨subd5_2_27, List.forall_mem_cons.2 ⟨subd5_2_28, List.forall_mem_cons.2 ⟨subd5_2_29, List.forall_mem_cons.2 ⟨subd5_2_30, List.forall_mem_cons.2 ⟨subd5_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_32 : subd5_2 [-2, -1, 2] = true := by decide +kernel
theorem subd5_2_33 : subd5_2 [-2, -1, 3] = true := by decide +kernel
theorem subd5_2_34 : subd5_2 [-2, -1, 4] = true := by decide +kernel
theorem subd5_2_35 : subd5_2 [-2, -1, 5] = true := by decide +kernel
theorem subd5_2_36 : subd5_2 [-2, -1, 6] = true := by decide +kernel
theorem subd5_2_37 : subd5_2 [-2, 0, -7] = true := by decide +kernel
theorem subd5_2_38 : subd5_2 [-2, 0, -6] = true := by decide +kernel
theorem subd5_2_39 : subd5_2 [-2, 0, -5] = true := by decide +kernel
theorem subd5_2_40 : subd5_2 [-2, 0, -4] = true := by decide +kernel
theorem subd5_2_41 : subd5_2 [-2, 0, -3] = true := by decide +kernel
theorem subd5_2_42 : subd5_2 [-2, 0, -2] = true := by decide +kernel
theorem subd5_2_43 : subd5_2 [-2, 0, -1] = true := by decide +kernel
theorem subd5_2_44 : subd5_2 [-2, 0, 0] = true := by decide +kernel
theorem subd5_2_45 : subd5_2 [-2, 0, 1] = true := by decide +kernel
theorem subd5_2_46 : subd5_2 [-2, 0, 2] = true := by decide +kernel
theorem subd5_2_47 : subd5_2 [-2, 0, 3] = true := by decide +kernel
theorem subd5_2_48 : subd5_2 [-2, 0, 4] = true := by decide +kernel
theorem subd5_2_49 : subd5_2 [-2, 0, 5] = true := by decide +kernel
theorem subd5_2_50 : subd5_2 [-2, 0, 6] = true := by decide +kernel
theorem subd5_2_51 : subd5_2 [-2, 1, -7] = true := by decide +kernel
theorem subd5_2_52 : subd5_2 [-2, 1, -6] = true := by decide +kernel
theorem subd5_2_53 : subd5_2 [-2, 1, -5] = true := by decide +kernel
theorem subd5_2_54 : subd5_2 [-2, 1, -4] = true := by decide +kernel
theorem subd5_2_55 : subd5_2 [-2, 1, -3] = true := by decide +kernel
theorem subd5_2_56 : subd5_2 [-2, 1, -2] = true := by decide +kernel
theorem subd5_2_57 : subd5_2 [-2, 1, -1] = true := by decide +kernel
theorem subd5_2_58 : subd5_2 [-2, 1, 0] = true := by decide +kernel
theorem subd5_2_59 : subd5_2 [-2, 1, 1] = true := by decide +kernel
theorem subd5_2_60 : subd5_2 [-2, 1, 2] = true := by decide +kernel
theorem subd5_2_61 : subd5_2 [-2, 1, 3] = true := by decide +kernel
theorem subd5_2_62 : subd5_2 [-2, 1, 4] = true := by decide +kernel
theorem subd5_2_63 : subd5_2 [-2, 1, 5] = true := by decide +kernel
theorem sbd5_2_1 : ∀ q ∈ blkd5_2_1, subd5_2 q = true := by
  unfold blkd5_2_1
  exact List.forall_mem_cons.2 ⟨subd5_2_32, List.forall_mem_cons.2 ⟨subd5_2_33, List.forall_mem_cons.2 ⟨subd5_2_34, List.forall_mem_cons.2 ⟨subd5_2_35, List.forall_mem_cons.2 ⟨subd5_2_36, List.forall_mem_cons.2 ⟨subd5_2_37, List.forall_mem_cons.2 ⟨subd5_2_38, List.forall_mem_cons.2 ⟨subd5_2_39, List.forall_mem_cons.2 ⟨subd5_2_40, List.forall_mem_cons.2 ⟨subd5_2_41, List.forall_mem_cons.2 ⟨subd5_2_42, List.forall_mem_cons.2 ⟨subd5_2_43, List.forall_mem_cons.2 ⟨subd5_2_44, List.forall_mem_cons.2 ⟨subd5_2_45, List.forall_mem_cons.2 ⟨subd5_2_46, List.forall_mem_cons.2 ⟨subd5_2_47, List.forall_mem_cons.2 ⟨subd5_2_48, List.forall_mem_cons.2 ⟨subd5_2_49, List.forall_mem_cons.2 ⟨subd5_2_50, List.forall_mem_cons.2 ⟨subd5_2_51, List.forall_mem_cons.2 ⟨subd5_2_52, List.forall_mem_cons.2 ⟨subd5_2_53, List.forall_mem_cons.2 ⟨subd5_2_54, List.forall_mem_cons.2 ⟨subd5_2_55, List.forall_mem_cons.2 ⟨subd5_2_56, List.forall_mem_cons.2 ⟨subd5_2_57, List.forall_mem_cons.2 ⟨subd5_2_58, List.forall_mem_cons.2 ⟨subd5_2_59, List.forall_mem_cons.2 ⟨subd5_2_60, List.forall_mem_cons.2 ⟨subd5_2_61, List.forall_mem_cons.2 ⟨subd5_2_62, List.forall_mem_cons.2 ⟨subd5_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_64 : subd5_2 [-2, 1, 6] = true := by decide +kernel
theorem subd5_2_65 : subd5_2 [-2, 2] = true := by decide +kernel
theorem subd5_2_66 : subd5_2 [-2, 3] = true := by decide +kernel
theorem subd5_2_67 : subd5_2 [-2, 4] = true := by decide +kernel
theorem subd5_2_68 : subd5_2 [-2, 5] = true := by decide +kernel
theorem subd5_2_69 : subd5_2 [-1, -6] = true := by decide +kernel
theorem subd5_2_70 : subd5_2 [-1, -5] = true := by decide +kernel
theorem subd5_2_71 : subd5_2 [-1, -4] = true := by decide +kernel
theorem subd5_2_72 : subd5_2 [-1, -3] = true := by decide +kernel
theorem subd5_2_73 : subd5_2 [-1, -2, -6] = true := by decide +kernel
theorem subd5_2_74 : subd5_2 [-1, -2, -5] = true := by decide +kernel
theorem subd5_2_75 : subd5_2 [-1, -2, -4] = true := by decide +kernel
theorem subd5_2_76 : subd5_2 [-1, -2, -3] = true := by decide +kernel
theorem subd5_2_77 : subd5_2 [-1, -2, -2] = true := by decide +kernel
theorem subd5_2_78 : subd5_2 [-1, -2, -1] = true := by decide +kernel
theorem subd5_2_79 : subd5_2 [-1, -2, 0] = true := by decide +kernel
theorem subd5_2_80 : subd5_2 [-1, -2, 1] = true := by decide +kernel
theorem subd5_2_81 : subd5_2 [-1, -2, 2] = true := by decide +kernel
theorem subd5_2_82 : subd5_2 [-1, -2, 3] = true := by decide +kernel
theorem subd5_2_83 : subd5_2 [-1, -2, 4] = true := by decide +kernel
theorem subd5_2_84 : subd5_2 [-1, -2, 5] = true := by decide +kernel
theorem subd5_2_85 : subd5_2 [-1, -2, 6] = true := by decide +kernel
theorem subd5_2_86 : subd5_2 [-1, -2, 7] = true := by decide +kernel
theorem subd5_2_87 : subd5_2 [-1, -1, -7] = true := by decide +kernel
theorem subd5_2_88 : subd5_2 [-1, -1, -6] = true := by decide +kernel
theorem subd5_2_89 : subd5_2 [-1, -1, -5] = true := by decide +kernel
theorem subd5_2_90 : subd5_2 [-1, -1, -4] = true := by decide +kernel
theorem subd5_2_91 : subd5_2 [-1, -1, -3] = true := by decide +kernel
theorem subd5_2_92 : subd5_2 [-1, -1, -2] = true := by decide +kernel
theorem subd5_2_93 : subd5_2 [-1, -1, -1] = true := by decide +kernel
theorem subd5_2_94 : subd5_2 [-1, -1, 0] = true := by decide +kernel
theorem subd5_2_95 : subd5_2 [-1, -1, 1] = true := by decide +kernel
theorem sbd5_2_2 : ∀ q ∈ blkd5_2_2, subd5_2 q = true := by
  unfold blkd5_2_2
  exact List.forall_mem_cons.2 ⟨subd5_2_64, List.forall_mem_cons.2 ⟨subd5_2_65, List.forall_mem_cons.2 ⟨subd5_2_66, List.forall_mem_cons.2 ⟨subd5_2_67, List.forall_mem_cons.2 ⟨subd5_2_68, List.forall_mem_cons.2 ⟨subd5_2_69, List.forall_mem_cons.2 ⟨subd5_2_70, List.forall_mem_cons.2 ⟨subd5_2_71, List.forall_mem_cons.2 ⟨subd5_2_72, List.forall_mem_cons.2 ⟨subd5_2_73, List.forall_mem_cons.2 ⟨subd5_2_74, List.forall_mem_cons.2 ⟨subd5_2_75, List.forall_mem_cons.2 ⟨subd5_2_76, List.forall_mem_cons.2 ⟨subd5_2_77, List.forall_mem_cons.2 ⟨subd5_2_78, List.forall_mem_cons.2 ⟨subd5_2_79, List.forall_mem_cons.2 ⟨subd5_2_80, List.forall_mem_cons.2 ⟨subd5_2_81, List.forall_mem_cons.2 ⟨subd5_2_82, List.forall_mem_cons.2 ⟨subd5_2_83, List.forall_mem_cons.2 ⟨subd5_2_84, List.forall_mem_cons.2 ⟨subd5_2_85, List.forall_mem_cons.2 ⟨subd5_2_86, List.forall_mem_cons.2 ⟨subd5_2_87, List.forall_mem_cons.2 ⟨subd5_2_88, List.forall_mem_cons.2 ⟨subd5_2_89, List.forall_mem_cons.2 ⟨subd5_2_90, List.forall_mem_cons.2 ⟨subd5_2_91, List.forall_mem_cons.2 ⟨subd5_2_92, List.forall_mem_cons.2 ⟨subd5_2_93, List.forall_mem_cons.2 ⟨subd5_2_94, List.forall_mem_cons.2 ⟨subd5_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_96 : subd5_2 [-1, -1, 2] = true := by decide +kernel
theorem subd5_2_97 : subd5_2 [-1, -1, 3] = true := by decide +kernel
theorem subd5_2_98 : subd5_2 [-1, -1, 4] = true := by decide +kernel
theorem subd5_2_99 : subd5_2 [-1, -1, 5] = true := by decide +kernel
theorem subd5_2_100 : subd5_2 [-1, -1, 6] = true := by decide +kernel
theorem subd5_2_101 : subd5_2 [-1, -1, 7] = true := by decide +kernel
theorem subd5_2_102 : subd5_2 [-1, 0, -7] = true := by decide +kernel
theorem subd5_2_103 : subd5_2 [-1, 0, -6] = true := by decide +kernel
theorem subd5_2_104 : subd5_2 [-1, 0, -5] = true := by decide +kernel
theorem subd5_2_105 : subd5_2 [-1, 0, -4] = true := by decide +kernel
theorem subd5_2_106 : subd5_2 [-1, 0, -3] = true := by decide +kernel
theorem subd5_2_107 : subd5_2 [-1, 0, -2] = true := by decide +kernel
theorem subd5_2_108 : subd5_2 [-1, 0, -1] = true := by decide +kernel
theorem subd5_2_109 : subd5_2 [-1, 0, 0] = true := by decide +kernel
theorem subd5_2_110 : subd5_2 [-1, 0, 1] = true := by decide +kernel
theorem subd5_2_111 : subd5_2 [-1, 0, 2] = true := by decide +kernel
theorem subd5_2_112 : subd5_2 [-1, 0, 3] = true := by decide +kernel
theorem subd5_2_113 : subd5_2 [-1, 0, 4] = true := by decide +kernel
theorem subd5_2_114 : subd5_2 [-1, 0, 5] = true := by decide +kernel
theorem subd5_2_115 : subd5_2 [-1, 0, 6] = true := by decide +kernel
theorem subd5_2_116 : subd5_2 [-1, 1, -8] = true := by decide +kernel
theorem subd5_2_117 : subd5_2 [-1, 1, -7] = true := by decide +kernel
theorem subd5_2_118 : subd5_2 [-1, 1, -6] = true := by decide +kernel
theorem subd5_2_119 : subd5_2 [-1, 1, -5] = true := by decide +kernel
theorem subd5_2_120 : subd5_2 [-1, 1, -4] = true := by decide +kernel
theorem subd5_2_121 : subd5_2 [-1, 1, -3] = true := by decide +kernel
theorem subd5_2_122 : subd5_2 [-1, 1, -2] = true := by decide +kernel
theorem subd5_2_123 : subd5_2 [-1, 1, -1] = true := by decide +kernel
theorem subd5_2_124 : subd5_2 [-1, 1, 0] = true := by decide +kernel
theorem subd5_2_125 : subd5_2 [-1, 1, 1] = true := by decide +kernel
theorem subd5_2_126 : subd5_2 [-1, 1, 2] = true := by decide +kernel
theorem subd5_2_127 : subd5_2 [-1, 1, 3] = true := by decide +kernel
theorem sbd5_2_3 : ∀ q ∈ blkd5_2_3, subd5_2 q = true := by
  unfold blkd5_2_3
  exact List.forall_mem_cons.2 ⟨subd5_2_96, List.forall_mem_cons.2 ⟨subd5_2_97, List.forall_mem_cons.2 ⟨subd5_2_98, List.forall_mem_cons.2 ⟨subd5_2_99, List.forall_mem_cons.2 ⟨subd5_2_100, List.forall_mem_cons.2 ⟨subd5_2_101, List.forall_mem_cons.2 ⟨subd5_2_102, List.forall_mem_cons.2 ⟨subd5_2_103, List.forall_mem_cons.2 ⟨subd5_2_104, List.forall_mem_cons.2 ⟨subd5_2_105, List.forall_mem_cons.2 ⟨subd5_2_106, List.forall_mem_cons.2 ⟨subd5_2_107, List.forall_mem_cons.2 ⟨subd5_2_108, List.forall_mem_cons.2 ⟨subd5_2_109, List.forall_mem_cons.2 ⟨subd5_2_110, List.forall_mem_cons.2 ⟨subd5_2_111, List.forall_mem_cons.2 ⟨subd5_2_112, List.forall_mem_cons.2 ⟨subd5_2_113, List.forall_mem_cons.2 ⟨subd5_2_114, List.forall_mem_cons.2 ⟨subd5_2_115, List.forall_mem_cons.2 ⟨subd5_2_116, List.forall_mem_cons.2 ⟨subd5_2_117, List.forall_mem_cons.2 ⟨subd5_2_118, List.forall_mem_cons.2 ⟨subd5_2_119, List.forall_mem_cons.2 ⟨subd5_2_120, List.forall_mem_cons.2 ⟨subd5_2_121, List.forall_mem_cons.2 ⟨subd5_2_122, List.forall_mem_cons.2 ⟨subd5_2_123, List.forall_mem_cons.2 ⟨subd5_2_124, List.forall_mem_cons.2 ⟨subd5_2_125, List.forall_mem_cons.2 ⟨subd5_2_126, List.forall_mem_cons.2 ⟨subd5_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
