import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_3_480 : subd6_3 [1, 2, -2] = true := by decide +kernel
theorem subd6_3_481 : subd6_3 [1, 2, -1] = true := by decide +kernel
theorem subd6_3_482 : subd6_3 [1, 2, 0] = true := by decide +kernel
theorem subd6_3_483 : subd6_3 [1, 2, 1] = true := by decide +kernel
theorem subd6_3_484 : subd6_3 [1, 2, 2] = true := by decide +kernel
theorem subd6_3_485 : subd6_3 [1, 2, 3] = true := by decide +kernel
theorem subd6_3_486 : subd6_3 [1, 2, 4] = true := by decide +kernel
theorem subd6_3_487 : subd6_3 [1, 2, 5] = true := by decide +kernel
theorem subd6_3_488 : subd6_3 [1, 2, 6] = true := by decide +kernel
theorem subd6_3_489 : subd6_3 [1, 2, 7] = true := by decide +kernel
theorem subd6_3_490 : subd6_3 [1, 2, 8] = true := by decide +kernel
theorem subd6_3_491 : subd6_3 [2, -4] = true := by decide +kernel
theorem subd6_3_492 : subd6_3 [2, -3] = true := by decide +kernel
theorem subd6_3_493 : subd6_3 [2, -2, -10] = true := by decide +kernel
theorem subd6_3_494 : subd6_3 [2, -2, -9] = true := by decide +kernel
theorem subd6_3_495 : subd6_3 [2, -2, -8] = true := by decide +kernel
theorem subd6_3_496 : subd6_3 [2, -2, -7] = true := by decide +kernel
theorem subd6_3_497 : subd6_3 [2, -2, -6] = true := by decide +kernel
theorem subd6_3_498 : subd6_3 [2, -2, -5] = true := by decide +kernel
theorem subd6_3_499 : subd6_3 [2, -2, -4] = true := by decide +kernel
theorem subd6_3_500 : subd6_3 [2, -2, -3] = true := by decide +kernel
theorem subd6_3_501 : subd6_3 [2, -2, -2] = true := by decide +kernel
theorem subd6_3_502 : subd6_3 [2, -2, -1] = true := by decide +kernel
theorem subd6_3_503 : subd6_3 [2, -2, 0] = true := by decide +kernel
theorem subd6_3_504 : subd6_3 [2, -2, 1] = true := by decide +kernel
theorem subd6_3_505 : subd6_3 [2, -2, 2] = true := by decide +kernel
theorem subd6_3_506 : subd6_3 [2, -2, 3] = true := by decide +kernel
theorem subd6_3_507 : subd6_3 [2, -2, 4] = true := by decide +kernel
theorem subd6_3_508 : subd6_3 [2, -2, 5] = true := by decide +kernel
theorem subd6_3_509 : subd6_3 [2, -2, 6] = true := by decide +kernel
theorem subd6_3_510 : subd6_3 [2, -2, 7] = true := by decide +kernel
theorem subd6_3_511 : subd6_3 [2, -2, 8] = true := by decide +kernel
theorem sbd6_3_15 : ∀ q ∈ blkd6_3_15, subd6_3 q = true := by
  unfold blkd6_3_15
  exact List.forall_mem_cons.2 ⟨subd6_3_480, List.forall_mem_cons.2 ⟨subd6_3_481, List.forall_mem_cons.2 ⟨subd6_3_482, List.forall_mem_cons.2 ⟨subd6_3_483, List.forall_mem_cons.2 ⟨subd6_3_484, List.forall_mem_cons.2 ⟨subd6_3_485, List.forall_mem_cons.2 ⟨subd6_3_486, List.forall_mem_cons.2 ⟨subd6_3_487, List.forall_mem_cons.2 ⟨subd6_3_488, List.forall_mem_cons.2 ⟨subd6_3_489, List.forall_mem_cons.2 ⟨subd6_3_490, List.forall_mem_cons.2 ⟨subd6_3_491, List.forall_mem_cons.2 ⟨subd6_3_492, List.forall_mem_cons.2 ⟨subd6_3_493, List.forall_mem_cons.2 ⟨subd6_3_494, List.forall_mem_cons.2 ⟨subd6_3_495, List.forall_mem_cons.2 ⟨subd6_3_496, List.forall_mem_cons.2 ⟨subd6_3_497, List.forall_mem_cons.2 ⟨subd6_3_498, List.forall_mem_cons.2 ⟨subd6_3_499, List.forall_mem_cons.2 ⟨subd6_3_500, List.forall_mem_cons.2 ⟨subd6_3_501, List.forall_mem_cons.2 ⟨subd6_3_502, List.forall_mem_cons.2 ⟨subd6_3_503, List.forall_mem_cons.2 ⟨subd6_3_504, List.forall_mem_cons.2 ⟨subd6_3_505, List.forall_mem_cons.2 ⟨subd6_3_506, List.forall_mem_cons.2 ⟨subd6_3_507, List.forall_mem_cons.2 ⟨subd6_3_508, List.forall_mem_cons.2 ⟨subd6_3_509, List.forall_mem_cons.2 ⟨subd6_3_510, List.forall_mem_cons.2 ⟨subd6_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_512 : subd6_3 [2, -1, -11] = true := by decide +kernel
theorem subd6_3_513 : subd6_3 [2, -1, -10] = true := by decide +kernel
theorem subd6_3_514 : subd6_3 [2, -1, -9] = true := by decide +kernel
theorem subd6_3_515 : subd6_3 [2, -1, -8] = true := by decide +kernel
theorem subd6_3_516 : subd6_3 [2, -1, -7] = true := by decide +kernel
theorem subd6_3_517 : subd6_3 [2, -1, -6] = true := by decide +kernel
theorem subd6_3_518 : subd6_3 [2, -1, -5] = true := by decide +kernel
theorem subd6_3_519 : subd6_3 [2, -1, -4] = true := by decide +kernel
theorem subd6_3_520 : subd6_3 [2, -1, -3] = true := by decide +kernel
theorem subd6_3_521 : subd6_3 [2, -1, -2] = true := by decide +kernel
theorem subd6_3_522 : subd6_3 [2, -1, -1] = true := by decide +kernel
theorem subd6_3_523 : subd6_3 [2, -1, 0] = true := by decide +kernel
theorem subd6_3_524 : subd6_3 [2, -1, 1] = true := by decide +kernel
theorem subd6_3_525 : subd6_3 [2, -1, 2] = true := by decide +kernel
theorem subd6_3_526 : subd6_3 [2, -1, 3] = true := by decide +kernel
theorem subd6_3_527 : subd6_3 [2, -1, 4] = true := by decide +kernel
theorem subd6_3_528 : subd6_3 [2, -1, 5] = true := by decide +kernel
theorem subd6_3_529 : subd6_3 [2, -1, 6] = true := by decide +kernel
theorem subd6_3_530 : subd6_3 [2, -1, 7] = true := by decide +kernel
theorem subd6_3_531 : subd6_3 [2, -1, 8] = true := by decide +kernel
theorem subd6_3_532 : subd6_3 [2, -1, 9] = true := by decide +kernel
theorem subd6_3_533 : subd6_3 [2, -1, 10] = true := by decide +kernel
theorem subd6_3_534 : subd6_3 [2, 0, -11] = true := by decide +kernel
theorem subd6_3_535 : subd6_3 [2, 0, -10] = true := by decide +kernel
theorem subd6_3_536 : subd6_3 [2, 0, -9] = true := by decide +kernel
theorem subd6_3_537 : subd6_3 [2, 0, -8] = true := by decide +kernel
theorem subd6_3_538 : subd6_3 [2, 0, -7] = true := by decide +kernel
theorem subd6_3_539 : subd6_3 [2, 0, -6] = true := by decide +kernel
theorem subd6_3_540 : subd6_3 [2, 0, -5] = true := by decide +kernel
theorem subd6_3_541 : subd6_3 [2, 0, -4] = true := by decide +kernel
theorem subd6_3_542 : subd6_3 [2, 0, -3] = true := by decide +kernel
theorem subd6_3_543 : subd6_3 [2, 0, -2] = true := by decide +kernel
theorem sbd6_3_16 : ∀ q ∈ blkd6_3_16, subd6_3 q = true := by
  unfold blkd6_3_16
  exact List.forall_mem_cons.2 ⟨subd6_3_512, List.forall_mem_cons.2 ⟨subd6_3_513, List.forall_mem_cons.2 ⟨subd6_3_514, List.forall_mem_cons.2 ⟨subd6_3_515, List.forall_mem_cons.2 ⟨subd6_3_516, List.forall_mem_cons.2 ⟨subd6_3_517, List.forall_mem_cons.2 ⟨subd6_3_518, List.forall_mem_cons.2 ⟨subd6_3_519, List.forall_mem_cons.2 ⟨subd6_3_520, List.forall_mem_cons.2 ⟨subd6_3_521, List.forall_mem_cons.2 ⟨subd6_3_522, List.forall_mem_cons.2 ⟨subd6_3_523, List.forall_mem_cons.2 ⟨subd6_3_524, List.forall_mem_cons.2 ⟨subd6_3_525, List.forall_mem_cons.2 ⟨subd6_3_526, List.forall_mem_cons.2 ⟨subd6_3_527, List.forall_mem_cons.2 ⟨subd6_3_528, List.forall_mem_cons.2 ⟨subd6_3_529, List.forall_mem_cons.2 ⟨subd6_3_530, List.forall_mem_cons.2 ⟨subd6_3_531, List.forall_mem_cons.2 ⟨subd6_3_532, List.forall_mem_cons.2 ⟨subd6_3_533, List.forall_mem_cons.2 ⟨subd6_3_534, List.forall_mem_cons.2 ⟨subd6_3_535, List.forall_mem_cons.2 ⟨subd6_3_536, List.forall_mem_cons.2 ⟨subd6_3_537, List.forall_mem_cons.2 ⟨subd6_3_538, List.forall_mem_cons.2 ⟨subd6_3_539, List.forall_mem_cons.2 ⟨subd6_3_540, List.forall_mem_cons.2 ⟨subd6_3_541, List.forall_mem_cons.2 ⟨subd6_3_542, List.forall_mem_cons.2 ⟨subd6_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_544 : subd6_3 [2, 0, -1] = true := by decide +kernel
theorem subd6_3_545 : subd6_3 [2, 0, 0] = true := by decide +kernel
theorem subd6_3_546 : subd6_3 [2, 0, 1] = true := by decide +kernel
theorem subd6_3_547 : subd6_3 [2, 0, 2] = true := by decide +kernel
theorem subd6_3_548 : subd6_3 [2, 0, 3] = true := by decide +kernel
theorem subd6_3_549 : subd6_3 [2, 0, 4] = true := by decide +kernel
theorem subd6_3_550 : subd6_3 [2, 0, 5] = true := by decide +kernel
theorem subd6_3_551 : subd6_3 [2, 0, 6] = true := by decide +kernel
theorem subd6_3_552 : subd6_3 [2, 0, 7] = true := by decide +kernel
theorem subd6_3_553 : subd6_3 [2, 0, 8] = true := by decide +kernel
theorem subd6_3_554 : subd6_3 [2, 0, 9] = true := by decide +kernel
theorem subd6_3_555 : subd6_3 [2, 1, -7] = true := by decide +kernel
theorem subd6_3_556 : subd6_3 [2, 1, -6] = true := by decide +kernel
theorem subd6_3_557 : subd6_3 [2, 1, -5] = true := by decide +kernel
theorem subd6_3_558 : subd6_3 [2, 1, -4] = true := by decide +kernel
theorem subd6_3_559 : subd6_3 [2, 1, -3] = true := by decide +kernel
theorem subd6_3_560 : subd6_3 [2, 1, -2] = true := by decide +kernel
theorem subd6_3_561 : subd6_3 [2, 1, -1] = true := by decide +kernel
theorem subd6_3_562 : subd6_3 [2, 1, 0] = true := by decide +kernel
theorem subd6_3_563 : subd6_3 [2, 1, 1] = true := by decide +kernel
theorem subd6_3_564 : subd6_3 [2, 1, 2] = true := by decide +kernel
theorem subd6_3_565 : subd6_3 [2, 1, 3] = true := by decide +kernel
theorem subd6_3_566 : subd6_3 [2, 1, 4] = true := by decide +kernel
theorem subd6_3_567 : subd6_3 [2, 1, 5] = true := by decide +kernel
theorem subd6_3_568 : subd6_3 [2, 1, 6] = true := by decide +kernel
theorem sbd6_3_17 : ∀ q ∈ blkd6_3_17, subd6_3 q = true := by
  unfold blkd6_3_17
  exact List.forall_mem_cons.2 ⟨subd6_3_544, List.forall_mem_cons.2 ⟨subd6_3_545, List.forall_mem_cons.2 ⟨subd6_3_546, List.forall_mem_cons.2 ⟨subd6_3_547, List.forall_mem_cons.2 ⟨subd6_3_548, List.forall_mem_cons.2 ⟨subd6_3_549, List.forall_mem_cons.2 ⟨subd6_3_550, List.forall_mem_cons.2 ⟨subd6_3_551, List.forall_mem_cons.2 ⟨subd6_3_552, List.forall_mem_cons.2 ⟨subd6_3_553, List.forall_mem_cons.2 ⟨subd6_3_554, List.forall_mem_cons.2 ⟨subd6_3_555, List.forall_mem_cons.2 ⟨subd6_3_556, List.forall_mem_cons.2 ⟨subd6_3_557, List.forall_mem_cons.2 ⟨subd6_3_558, List.forall_mem_cons.2 ⟨subd6_3_559, List.forall_mem_cons.2 ⟨subd6_3_560, List.forall_mem_cons.2 ⟨subd6_3_561, List.forall_mem_cons.2 ⟨subd6_3_562, List.forall_mem_cons.2 ⟨subd6_3_563, List.forall_mem_cons.2 ⟨subd6_3_564, List.forall_mem_cons.2 ⟨subd6_3_565, List.forall_mem_cons.2 ⟨subd6_3_566, List.forall_mem_cons.2 ⟨subd6_3_567, List.forall_mem_cons.2 ⟨subd6_3_568, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel
theorem subd7_0_0 : subd7_0 [-6] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-5, -6] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [-5, -5] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [-5, -4] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [-5, -3] = true := by decide +kernel
theorem subd7_0_5 : subd7_0 [-5, -2] = true := by decide +kernel
theorem subd7_0_6 : subd7_0 [-5, -1] = true := by decide +kernel
theorem subd7_0_7 : subd7_0 [-5, 0] = true := by decide +kernel
theorem subd7_0_8 : subd7_0 [-5, 1] = true := by decide +kernel
theorem subd7_0_9 : subd7_0 [-5, 2] = true := by decide +kernel
theorem subd7_0_10 : subd7_0 [-4, -7] = true := by decide +kernel
theorem subd7_0_11 : subd7_0 [-4, -6] = true := by decide +kernel
theorem subd7_0_12 : subd7_0 [-4, -5] = true := by decide +kernel
theorem subd7_0_13 : subd7_0 [-4, -4] = true := by decide +kernel
theorem subd7_0_14 : subd7_0 [-4, -3] = true := by decide +kernel
theorem subd7_0_15 : subd7_0 [-4, -2] = true := by decide +kernel
theorem subd7_0_16 : subd7_0 [-4, -1] = true := by decide +kernel
theorem subd7_0_17 : subd7_0 [-4, 0] = true := by decide +kernel
theorem subd7_0_18 : subd7_0 [-4, 1] = true := by decide +kernel
theorem subd7_0_19 : subd7_0 [-4, 2] = true := by decide +kernel
theorem subd7_0_20 : subd7_0 [-4, 3] = true := by decide +kernel
theorem subd7_0_21 : subd7_0 [-4, 4] = true := by decide +kernel
theorem subd7_0_22 : subd7_0 [-3, -7] = true := by decide +kernel
theorem subd7_0_23 : subd7_0 [-3, -6] = true := by decide +kernel
theorem subd7_0_24 : subd7_0 [-3, -5] = true := by decide +kernel
theorem subd7_0_25 : subd7_0 [-3, -4] = true := by decide +kernel
theorem subd7_0_26 : subd7_0 [-3, -3] = true := by decide +kernel
theorem subd7_0_27 : subd7_0 [-3, -2] = true := by decide +kernel
theorem subd7_0_28 : subd7_0 [-3, -1] = true := by decide +kernel
theorem subd7_0_29 : subd7_0 [-3, 0] = true := by decide +kernel
theorem subd7_0_30 : subd7_0 [-3, 1] = true := by decide +kernel
theorem subd7_0_31 : subd7_0 [-3, 2] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_cons.2 ⟨subd7_0_5, List.forall_mem_cons.2 ⟨subd7_0_6, List.forall_mem_cons.2 ⟨subd7_0_7, List.forall_mem_cons.2 ⟨subd7_0_8, List.forall_mem_cons.2 ⟨subd7_0_9, List.forall_mem_cons.2 ⟨subd7_0_10, List.forall_mem_cons.2 ⟨subd7_0_11, List.forall_mem_cons.2 ⟨subd7_0_12, List.forall_mem_cons.2 ⟨subd7_0_13, List.forall_mem_cons.2 ⟨subd7_0_14, List.forall_mem_cons.2 ⟨subd7_0_15, List.forall_mem_cons.2 ⟨subd7_0_16, List.forall_mem_cons.2 ⟨subd7_0_17, List.forall_mem_cons.2 ⟨subd7_0_18, List.forall_mem_cons.2 ⟨subd7_0_19, List.forall_mem_cons.2 ⟨subd7_0_20, List.forall_mem_cons.2 ⟨subd7_0_21, List.forall_mem_cons.2 ⟨subd7_0_22, List.forall_mem_cons.2 ⟨subd7_0_23, List.forall_mem_cons.2 ⟨subd7_0_24, List.forall_mem_cons.2 ⟨subd7_0_25, List.forall_mem_cons.2 ⟨subd7_0_26, List.forall_mem_cons.2 ⟨subd7_0_27, List.forall_mem_cons.2 ⟨subd7_0_28, List.forall_mem_cons.2 ⟨subd7_0_29, List.forall_mem_cons.2 ⟨subd7_0_30, List.forall_mem_cons.2 ⟨subd7_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_32 : subd7_0 [-3, 3] = true := by decide +kernel
theorem subd7_0_33 : subd7_0 [-3, 4] = true := by decide +kernel
theorem subd7_0_34 : subd7_0 [-3, 5] = true := by decide +kernel
theorem subd7_0_35 : subd7_0 [-2, -8] = true := by decide +kernel
theorem subd7_0_36 : subd7_0 [-2, -7] = true := by decide +kernel
theorem subd7_0_37 : subd7_0 [-2, -6] = true := by decide +kernel
theorem subd7_0_38 : subd7_0 [-2, -5] = true := by decide +kernel
theorem subd7_0_39 : subd7_0 [-2, -4] = true := by decide +kernel
theorem subd7_0_40 : subd7_0 [-2, -3] = true := by decide +kernel
theorem subd7_0_41 : subd7_0 [-2, -2] = true := by decide +kernel
theorem subd7_0_42 : subd7_0 [-2, -1, -7] = true := by decide +kernel
theorem subd7_0_43 : subd7_0 [-2, -1, -6] = true := by decide +kernel
theorem subd7_0_44 : subd7_0 [-2, -1, -5] = true := by decide +kernel
theorem subd7_0_45 : subd7_0 [-2, -1, -4] = true := by decide +kernel
theorem subd7_0_46 : subd7_0 [-2, -1, -3] = true := by decide +kernel
theorem subd7_0_47 : subd7_0 [-2, -1, -2] = true := by decide +kernel
theorem subd7_0_48 : subd7_0 [-2, -1, -1] = true := by decide +kernel
theorem subd7_0_49 : subd7_0 [-2, -1, 0] = true := by decide +kernel
theorem subd7_0_50 : subd7_0 [-2, -1, 1] = true := by decide +kernel
theorem subd7_0_51 : subd7_0 [-2, -1, 2] = true := by decide +kernel
theorem subd7_0_52 : subd7_0 [-2, -1, 3] = true := by decide +kernel
theorem subd7_0_53 : subd7_0 [-2, -1, 4] = true := by decide +kernel
theorem subd7_0_54 : subd7_0 [-2, -1, 5] = true := by decide +kernel
theorem subd7_0_55 : subd7_0 [-2, 0, -7] = true := by decide +kernel
theorem subd7_0_56 : subd7_0 [-2, 0, -6] = true := by decide +kernel
theorem subd7_0_57 : subd7_0 [-2, 0, -5] = true := by decide +kernel
theorem subd7_0_58 : subd7_0 [-2, 0, -4] = true := by decide +kernel
theorem subd7_0_59 : subd7_0 [-2, 0, -3] = true := by decide +kernel
theorem subd7_0_60 : subd7_0 [-2, 0, -2] = true := by decide +kernel
theorem subd7_0_61 : subd7_0 [-2, 0, -1] = true := by decide +kernel
theorem subd7_0_62 : subd7_0 [-2, 0, 0] = true := by decide +kernel
theorem subd7_0_63 : subd7_0 [-2, 0, 1] = true := by decide +kernel
theorem sbd7_0_1 : ∀ q ∈ blkd7_0_1, subd7_0 q = true := by
  unfold blkd7_0_1
  exact List.forall_mem_cons.2 ⟨subd7_0_32, List.forall_mem_cons.2 ⟨subd7_0_33, List.forall_mem_cons.2 ⟨subd7_0_34, List.forall_mem_cons.2 ⟨subd7_0_35, List.forall_mem_cons.2 ⟨subd7_0_36, List.forall_mem_cons.2 ⟨subd7_0_37, List.forall_mem_cons.2 ⟨subd7_0_38, List.forall_mem_cons.2 ⟨subd7_0_39, List.forall_mem_cons.2 ⟨subd7_0_40, List.forall_mem_cons.2 ⟨subd7_0_41, List.forall_mem_cons.2 ⟨subd7_0_42, List.forall_mem_cons.2 ⟨subd7_0_43, List.forall_mem_cons.2 ⟨subd7_0_44, List.forall_mem_cons.2 ⟨subd7_0_45, List.forall_mem_cons.2 ⟨subd7_0_46, List.forall_mem_cons.2 ⟨subd7_0_47, List.forall_mem_cons.2 ⟨subd7_0_48, List.forall_mem_cons.2 ⟨subd7_0_49, List.forall_mem_cons.2 ⟨subd7_0_50, List.forall_mem_cons.2 ⟨subd7_0_51, List.forall_mem_cons.2 ⟨subd7_0_52, List.forall_mem_cons.2 ⟨subd7_0_53, List.forall_mem_cons.2 ⟨subd7_0_54, List.forall_mem_cons.2 ⟨subd7_0_55, List.forall_mem_cons.2 ⟨subd7_0_56, List.forall_mem_cons.2 ⟨subd7_0_57, List.forall_mem_cons.2 ⟨subd7_0_58, List.forall_mem_cons.2 ⟨subd7_0_59, List.forall_mem_cons.2 ⟨subd7_0_60, List.forall_mem_cons.2 ⟨subd7_0_61, List.forall_mem_cons.2 ⟨subd7_0_62, List.forall_mem_cons.2 ⟨subd7_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_64 : subd7_0 [-2, 0, 2] = true := by decide +kernel
theorem subd7_0_65 : subd7_0 [-2, 0, 3] = true := by decide +kernel
theorem subd7_0_66 : subd7_0 [-2, 0, 4] = true := by decide +kernel
theorem subd7_0_67 : subd7_0 [-2, 0, 5] = true := by decide +kernel
theorem subd7_0_68 : subd7_0 [-2, 1] = true := by decide +kernel
theorem subd7_0_69 : subd7_0 [-2, 2] = true := by decide +kernel
theorem subd7_0_70 : subd7_0 [-2, 3] = true := by decide +kernel
theorem subd7_0_71 : subd7_0 [-2, 4] = true := by decide +kernel
theorem subd7_0_72 : subd7_0 [-2, 5] = true := by decide +kernel
theorem subd7_0_73 : subd7_0 [-2, 6] = true := by decide +kernel
theorem subd7_0_74 : subd7_0 [-1, -8] = true := by decide +kernel
theorem subd7_0_75 : subd7_0 [-1, -7] = true := by decide +kernel
theorem subd7_0_76 : subd7_0 [-1, -6] = true := by decide +kernel
theorem subd7_0_77 : subd7_0 [-1, -5] = true := by decide +kernel
theorem subd7_0_78 : subd7_0 [-1, -4] = true := by decide +kernel
theorem subd7_0_79 : subd7_0 [-1, -3] = true := by decide +kernel
theorem subd7_0_80 : subd7_0 [-1, -2, -7] = true := by decide +kernel
theorem subd7_0_81 : subd7_0 [-1, -2, -6] = true := by decide +kernel
theorem subd7_0_82 : subd7_0 [-1, -2, -5] = true := by decide +kernel
theorem subd7_0_83 : subd7_0 [-1, -2, -4] = true := by decide +kernel
theorem subd7_0_84 : subd7_0 [-1, -2, -3] = true := by decide +kernel
theorem subd7_0_85 : subd7_0 [-1, -2, -2] = true := by decide +kernel
theorem subd7_0_86 : subd7_0 [-1, -2, -1] = true := by decide +kernel
theorem subd7_0_87 : subd7_0 [-1, -2, 0] = true := by decide +kernel
theorem subd7_0_88 : subd7_0 [-1, -2, 1] = true := by decide +kernel
theorem subd7_0_89 : subd7_0 [-1, -2, 2] = true := by decide +kernel
theorem subd7_0_90 : subd7_0 [-1, -2, 3] = true := by decide +kernel
theorem subd7_0_91 : subd7_0 [-1, -2, 4] = true := by decide +kernel
theorem subd7_0_92 : subd7_0 [-1, -2, 5] = true := by decide +kernel
theorem subd7_0_93 : subd7_0 [-1, -1, -7] = true := by decide +kernel
theorem subd7_0_94 : subd7_0 [-1, -1, -6] = true := by decide +kernel
theorem subd7_0_95 : subd7_0 [-1, -1, -5] = true := by decide +kernel
theorem sbd7_0_2 : ∀ q ∈ blkd7_0_2, subd7_0 q = true := by
  unfold blkd7_0_2
  exact List.forall_mem_cons.2 ⟨subd7_0_64, List.forall_mem_cons.2 ⟨subd7_0_65, List.forall_mem_cons.2 ⟨subd7_0_66, List.forall_mem_cons.2 ⟨subd7_0_67, List.forall_mem_cons.2 ⟨subd7_0_68, List.forall_mem_cons.2 ⟨subd7_0_69, List.forall_mem_cons.2 ⟨subd7_0_70, List.forall_mem_cons.2 ⟨subd7_0_71, List.forall_mem_cons.2 ⟨subd7_0_72, List.forall_mem_cons.2 ⟨subd7_0_73, List.forall_mem_cons.2 ⟨subd7_0_74, List.forall_mem_cons.2 ⟨subd7_0_75, List.forall_mem_cons.2 ⟨subd7_0_76, List.forall_mem_cons.2 ⟨subd7_0_77, List.forall_mem_cons.2 ⟨subd7_0_78, List.forall_mem_cons.2 ⟨subd7_0_79, List.forall_mem_cons.2 ⟨subd7_0_80, List.forall_mem_cons.2 ⟨subd7_0_81, List.forall_mem_cons.2 ⟨subd7_0_82, List.forall_mem_cons.2 ⟨subd7_0_83, List.forall_mem_cons.2 ⟨subd7_0_84, List.forall_mem_cons.2 ⟨subd7_0_85, List.forall_mem_cons.2 ⟨subd7_0_86, List.forall_mem_cons.2 ⟨subd7_0_87, List.forall_mem_cons.2 ⟨subd7_0_88, List.forall_mem_cons.2 ⟨subd7_0_89, List.forall_mem_cons.2 ⟨subd7_0_90, List.forall_mem_cons.2 ⟨subd7_0_91, List.forall_mem_cons.2 ⟨subd7_0_92, List.forall_mem_cons.2 ⟨subd7_0_93, List.forall_mem_cons.2 ⟨subd7_0_94, List.forall_mem_cons.2 ⟨subd7_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_96 : subd7_0 [-1, -1, -4] = true := by decide +kernel
theorem subd7_0_97 : subd7_0 [-1, -1, -3] = true := by decide +kernel
theorem subd7_0_98 : subd7_0 [-1, -1, -2] = true := by decide +kernel
theorem subd7_0_99 : subd7_0 [-1, -1, -1] = true := by decide +kernel
theorem subd7_0_100 : subd7_0 [-1, -1, 0] = true := by decide +kernel
theorem subd7_0_101 : subd7_0 [-1, -1, 1] = true := by decide +kernel
theorem subd7_0_102 : subd7_0 [-1, -1, 2] = true := by decide +kernel
theorem subd7_0_103 : subd7_0 [-1, -1, 3] = true := by decide +kernel
theorem subd7_0_104 : subd7_0 [-1, -1, 4] = true := by decide +kernel
theorem subd7_0_105 : subd7_0 [-1, -1, 5] = true := by decide +kernel
theorem subd7_0_106 : subd7_0 [-1, -1, 6] = true := by decide +kernel
theorem subd7_0_107 : subd7_0 [-1, 0, -7] = true := by decide +kernel
theorem subd7_0_108 : subd7_0 [-1, 0, -6] = true := by decide +kernel
theorem subd7_0_109 : subd7_0 [-1, 0, -5] = true := by decide +kernel
theorem subd7_0_110 : subd7_0 [-1, 0, -4] = true := by decide +kernel
theorem subd7_0_111 : subd7_0 [-1, 0, -3] = true := by decide +kernel
theorem subd7_0_112 : subd7_0 [-1, 0, -2] = true := by decide +kernel
theorem subd7_0_113 : subd7_0 [-1, 0, -1] = true := by decide +kernel
theorem subd7_0_114 : subd7_0 [-1, 0, 0] = true := by decide +kernel
theorem subd7_0_115 : subd7_0 [-1, 0, 1] = true := by decide +kernel
theorem subd7_0_116 : subd7_0 [-1, 0, 2] = true := by decide +kernel
theorem subd7_0_117 : subd7_0 [-1, 0, 3] = true := by decide +kernel
theorem subd7_0_118 : subd7_0 [-1, 0, 4] = true := by decide +kernel
theorem subd7_0_119 : subd7_0 [-1, 0, 5] = true := by decide +kernel
theorem subd7_0_120 : subd7_0 [-1, 0, 6] = true := by decide +kernel
theorem subd7_0_121 : subd7_0 [-1, 1, -7] = true := by decide +kernel
theorem subd7_0_122 : subd7_0 [-1, 1, -6] = true := by decide +kernel
theorem subd7_0_123 : subd7_0 [-1, 1, -5] = true := by decide +kernel
theorem subd7_0_124 : subd7_0 [-1, 1, -4] = true := by decide +kernel
theorem subd7_0_125 : subd7_0 [-1, 1, -3] = true := by decide +kernel
theorem subd7_0_126 : subd7_0 [-1, 1, -2] = true := by decide +kernel
theorem subd7_0_127 : subd7_0 [-1, 1, -1] = true := by decide +kernel
theorem sbd7_0_3 : ∀ q ∈ blkd7_0_3, subd7_0 q = true := by
  unfold blkd7_0_3
  exact List.forall_mem_cons.2 ⟨subd7_0_96, List.forall_mem_cons.2 ⟨subd7_0_97, List.forall_mem_cons.2 ⟨subd7_0_98, List.forall_mem_cons.2 ⟨subd7_0_99, List.forall_mem_cons.2 ⟨subd7_0_100, List.forall_mem_cons.2 ⟨subd7_0_101, List.forall_mem_cons.2 ⟨subd7_0_102, List.forall_mem_cons.2 ⟨subd7_0_103, List.forall_mem_cons.2 ⟨subd7_0_104, List.forall_mem_cons.2 ⟨subd7_0_105, List.forall_mem_cons.2 ⟨subd7_0_106, List.forall_mem_cons.2 ⟨subd7_0_107, List.forall_mem_cons.2 ⟨subd7_0_108, List.forall_mem_cons.2 ⟨subd7_0_109, List.forall_mem_cons.2 ⟨subd7_0_110, List.forall_mem_cons.2 ⟨subd7_0_111, List.forall_mem_cons.2 ⟨subd7_0_112, List.forall_mem_cons.2 ⟨subd7_0_113, List.forall_mem_cons.2 ⟨subd7_0_114, List.forall_mem_cons.2 ⟨subd7_0_115, List.forall_mem_cons.2 ⟨subd7_0_116, List.forall_mem_cons.2 ⟨subd7_0_117, List.forall_mem_cons.2 ⟨subd7_0_118, List.forall_mem_cons.2 ⟨subd7_0_119, List.forall_mem_cons.2 ⟨subd7_0_120, List.forall_mem_cons.2 ⟨subd7_0_121, List.forall_mem_cons.2 ⟨subd7_0_122, List.forall_mem_cons.2 ⟨subd7_0_123, List.forall_mem_cons.2 ⟨subd7_0_124, List.forall_mem_cons.2 ⟨subd7_0_125, List.forall_mem_cons.2 ⟨subd7_0_126, List.forall_mem_cons.2 ⟨subd7_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
