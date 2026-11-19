import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_3_512 : subd7_3 [1, 1, -2] = true := by decide +kernel
theorem subd7_3_513 : subd7_3 [1, 1, -1] = true := by decide +kernel
theorem subd7_3_514 : subd7_3 [1, 1, 0] = true := by decide +kernel
theorem subd7_3_515 : subd7_3 [1, 1, 1] = true := by decide +kernel
theorem subd7_3_516 : subd7_3 [1, 1, 2] = true := by decide +kernel
theorem subd7_3_517 : subd7_3 [1, 1, 3] = true := by decide +kernel
theorem subd7_3_518 : subd7_3 [1, 1, 4] = true := by decide +kernel
theorem subd7_3_519 : subd7_3 [1, 1, 5] = true := by decide +kernel
theorem subd7_3_520 : subd7_3 [1, 1, 6] = true := by decide +kernel
theorem subd7_3_521 : subd7_3 [1, 1, 7] = true := by decide +kernel
theorem subd7_3_522 : subd7_3 [1, 1, 8] = true := by decide +kernel
theorem subd7_3_523 : subd7_3 [1, 1, 9] = true := by decide +kernel
theorem subd7_3_524 : subd7_3 [1, 1, 10] = true := by decide +kernel
theorem subd7_3_525 : subd7_3 [1, 1, 11] = true := by decide +kernel
theorem subd7_3_526 : subd7_3 [1, 1, 12] = true := by decide +kernel
theorem subd7_3_527 : subd7_3 [1, 1, 13] = true := by decide +kernel
theorem subd7_3_528 : subd7_3 [1, 1, 14] = true := by decide +kernel
theorem subd7_3_529 : subd7_3 [1, 1, 15] = true := by decide +kernel
theorem subd7_3_530 : subd7_3 [1, 1, 16] = true := by decide +kernel
theorem subd7_3_531 : subd7_3 [1, 1, 17] = true := by decide +kernel
theorem subd7_3_532 : subd7_3 [1, 2, -11] = true := by decide +kernel
theorem subd7_3_533 : subd7_3 [1, 2, -10] = true := by decide +kernel
theorem subd7_3_534 : subd7_3 [1, 2, -9] = true := by decide +kernel
theorem subd7_3_535 : subd7_3 [1, 2, -8] = true := by decide +kernel
theorem subd7_3_536 : subd7_3 [1, 2, -7] = true := by decide +kernel
theorem subd7_3_537 : subd7_3 [1, 2, -6] = true := by decide +kernel
theorem subd7_3_538 : subd7_3 [1, 2, -5] = true := by decide +kernel
theorem subd7_3_539 : subd7_3 [1, 2, -4] = true := by decide +kernel
theorem subd7_3_540 : subd7_3 [1, 2, -3] = true := by decide +kernel
theorem subd7_3_541 : subd7_3 [1, 2, -2] = true := by decide +kernel
theorem subd7_3_542 : subd7_3 [1, 2, -1] = true := by decide +kernel
theorem subd7_3_543 : subd7_3 [1, 2, 0] = true := by decide +kernel
theorem sbd7_3_16 : ∀ q ∈ blkd7_3_16, subd7_3 q = true := by
  unfold blkd7_3_16
  exact List.forall_mem_cons.2 ⟨subd7_3_512, List.forall_mem_cons.2 ⟨subd7_3_513, List.forall_mem_cons.2 ⟨subd7_3_514, List.forall_mem_cons.2 ⟨subd7_3_515, List.forall_mem_cons.2 ⟨subd7_3_516, List.forall_mem_cons.2 ⟨subd7_3_517, List.forall_mem_cons.2 ⟨subd7_3_518, List.forall_mem_cons.2 ⟨subd7_3_519, List.forall_mem_cons.2 ⟨subd7_3_520, List.forall_mem_cons.2 ⟨subd7_3_521, List.forall_mem_cons.2 ⟨subd7_3_522, List.forall_mem_cons.2 ⟨subd7_3_523, List.forall_mem_cons.2 ⟨subd7_3_524, List.forall_mem_cons.2 ⟨subd7_3_525, List.forall_mem_cons.2 ⟨subd7_3_526, List.forall_mem_cons.2 ⟨subd7_3_527, List.forall_mem_cons.2 ⟨subd7_3_528, List.forall_mem_cons.2 ⟨subd7_3_529, List.forall_mem_cons.2 ⟨subd7_3_530, List.forall_mem_cons.2 ⟨subd7_3_531, List.forall_mem_cons.2 ⟨subd7_3_532, List.forall_mem_cons.2 ⟨subd7_3_533, List.forall_mem_cons.2 ⟨subd7_3_534, List.forall_mem_cons.2 ⟨subd7_3_535, List.forall_mem_cons.2 ⟨subd7_3_536, List.forall_mem_cons.2 ⟨subd7_3_537, List.forall_mem_cons.2 ⟨subd7_3_538, List.forall_mem_cons.2 ⟨subd7_3_539, List.forall_mem_cons.2 ⟨subd7_3_540, List.forall_mem_cons.2 ⟨subd7_3_541, List.forall_mem_cons.2 ⟨subd7_3_542, List.forall_mem_cons.2 ⟨subd7_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_544 : subd7_3 [1, 2, 1] = true := by decide +kernel
theorem subd7_3_545 : subd7_3 [1, 2, 2] = true := by decide +kernel
theorem subd7_3_546 : subd7_3 [1, 2, 3] = true := by decide +kernel
theorem subd7_3_547 : subd7_3 [1, 2, 4] = true := by decide +kernel
theorem subd7_3_548 : subd7_3 [1, 2, 5] = true := by decide +kernel
theorem subd7_3_549 : subd7_3 [1, 2, 6] = true := by decide +kernel
theorem subd7_3_550 : subd7_3 [1, 2, 7] = true := by decide +kernel
theorem subd7_3_551 : subd7_3 [1, 2, 8] = true := by decide +kernel
theorem subd7_3_552 : subd7_3 [1, 2, 9] = true := by decide +kernel
theorem subd7_3_553 : subd7_3 [2, -2] = true := by decide +kernel
theorem subd7_3_554 : subd7_3 [2, -1, -10] = true := by decide +kernel
theorem subd7_3_555 : subd7_3 [2, -1, -9] = true := by decide +kernel
theorem subd7_3_556 : subd7_3 [2, -1, -8] = true := by decide +kernel
theorem subd7_3_557 : subd7_3 [2, -1, -7] = true := by decide +kernel
theorem subd7_3_558 : subd7_3 [2, -1, -6] = true := by decide +kernel
theorem subd7_3_559 : subd7_3 [2, -1, -5] = true := by decide +kernel
theorem subd7_3_560 : subd7_3 [2, -1, -4] = true := by decide +kernel
theorem subd7_3_561 : subd7_3 [2, -1, -3] = true := by decide +kernel
theorem subd7_3_562 : subd7_3 [2, -1, -2] = true := by decide +kernel
theorem subd7_3_563 : subd7_3 [2, -1, -1] = true := by decide +kernel
theorem subd7_3_564 : subd7_3 [2, -1, 0] = true := by decide +kernel
theorem subd7_3_565 : subd7_3 [2, -1, 1] = true := by decide +kernel
theorem subd7_3_566 : subd7_3 [2, -1, 2] = true := by decide +kernel
theorem subd7_3_567 : subd7_3 [2, -1, 3] = true := by decide +kernel
theorem subd7_3_568 : subd7_3 [2, -1, 4] = true := by decide +kernel
theorem subd7_3_569 : subd7_3 [2, -1, 5] = true := by decide +kernel
theorem subd7_3_570 : subd7_3 [2, -1, 6] = true := by decide +kernel
theorem subd7_3_571 : subd7_3 [2, -1, 7] = true := by decide +kernel
theorem subd7_3_572 : subd7_3 [2, -1, 8] = true := by decide +kernel
theorem subd7_3_573 : subd7_3 [2, 0, -14] = true := by decide +kernel
theorem subd7_3_574 : subd7_3 [2, 0, -13] = true := by decide +kernel
theorem subd7_3_575 : subd7_3 [2, 0, -12] = true := by decide +kernel
theorem sbd7_3_17 : ∀ q ∈ blkd7_3_17, subd7_3 q = true := by
  unfold blkd7_3_17
  exact List.forall_mem_cons.2 ⟨subd7_3_544, List.forall_mem_cons.2 ⟨subd7_3_545, List.forall_mem_cons.2 ⟨subd7_3_546, List.forall_mem_cons.2 ⟨subd7_3_547, List.forall_mem_cons.2 ⟨subd7_3_548, List.forall_mem_cons.2 ⟨subd7_3_549, List.forall_mem_cons.2 ⟨subd7_3_550, List.forall_mem_cons.2 ⟨subd7_3_551, List.forall_mem_cons.2 ⟨subd7_3_552, List.forall_mem_cons.2 ⟨subd7_3_553, List.forall_mem_cons.2 ⟨subd7_3_554, List.forall_mem_cons.2 ⟨subd7_3_555, List.forall_mem_cons.2 ⟨subd7_3_556, List.forall_mem_cons.2 ⟨subd7_3_557, List.forall_mem_cons.2 ⟨subd7_3_558, List.forall_mem_cons.2 ⟨subd7_3_559, List.forall_mem_cons.2 ⟨subd7_3_560, List.forall_mem_cons.2 ⟨subd7_3_561, List.forall_mem_cons.2 ⟨subd7_3_562, List.forall_mem_cons.2 ⟨subd7_3_563, List.forall_mem_cons.2 ⟨subd7_3_564, List.forall_mem_cons.2 ⟨subd7_3_565, List.forall_mem_cons.2 ⟨subd7_3_566, List.forall_mem_cons.2 ⟨subd7_3_567, List.forall_mem_cons.2 ⟨subd7_3_568, List.forall_mem_cons.2 ⟨subd7_3_569, List.forall_mem_cons.2 ⟨subd7_3_570, List.forall_mem_cons.2 ⟨subd7_3_571, List.forall_mem_cons.2 ⟨subd7_3_572, List.forall_mem_cons.2 ⟨subd7_3_573, List.forall_mem_cons.2 ⟨subd7_3_574, List.forall_mem_cons.2 ⟨subd7_3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_576 : subd7_3 [2, 0, -11] = true := by decide +kernel
theorem subd7_3_577 : subd7_3 [2, 0, -10] = true := by decide +kernel
theorem subd7_3_578 : subd7_3 [2, 0, -9] = true := by decide +kernel
theorem subd7_3_579 : subd7_3 [2, 0, -8] = true := by decide +kernel
theorem subd7_3_580 : subd7_3 [2, 0, -7] = true := by decide +kernel
theorem subd7_3_581 : subd7_3 [2, 0, -6] = true := by decide +kernel
theorem subd7_3_582 : subd7_3 [2, 0, -5] = true := by decide +kernel
theorem subd7_3_583 : subd7_3 [2, 0, -4] = true := by decide +kernel
theorem subd7_3_584 : subd7_3 [2, 0, -3] = true := by decide +kernel
theorem subd7_3_585 : subd7_3 [2, 0, -2] = true := by decide +kernel
theorem subd7_3_586 : subd7_3 [2, 0, -1] = true := by decide +kernel
theorem subd7_3_587 : subd7_3 [2, 0, 0] = true := by decide +kernel
theorem subd7_3_588 : subd7_3 [2, 0, 1] = true := by decide +kernel
theorem subd7_3_589 : subd7_3 [2, 0, 2] = true := by decide +kernel
theorem subd7_3_590 : subd7_3 [2, 0, 3] = true := by decide +kernel
theorem subd7_3_591 : subd7_3 [2, 0, 4] = true := by decide +kernel
theorem subd7_3_592 : subd7_3 [2, 0, 5] = true := by decide +kernel
theorem subd7_3_593 : subd7_3 [2, 0, 6] = true := by decide +kernel
theorem subd7_3_594 : subd7_3 [2, 0, 7] = true := by decide +kernel
theorem subd7_3_595 : subd7_3 [2, 0, 8] = true := by decide +kernel
theorem subd7_3_596 : subd7_3 [2, 0, 9] = true := by decide +kernel
theorem subd7_3_597 : subd7_3 [2, 0, 10] = true := by decide +kernel
theorem subd7_3_598 : subd7_3 [2, 0, 11] = true := by decide +kernel
theorem subd7_3_599 : subd7_3 [2, 0, 12] = true := by decide +kernel
theorem subd7_3_600 : subd7_3 [2, 1, -11] = true := by decide +kernel
theorem subd7_3_601 : subd7_3 [2, 1, -10] = true := by decide +kernel
theorem subd7_3_602 : subd7_3 [2, 1, -9] = true := by decide +kernel
theorem subd7_3_603 : subd7_3 [2, 1, -8] = true := by decide +kernel
theorem subd7_3_604 : subd7_3 [2, 1, -7] = true := by decide +kernel
theorem subd7_3_605 : subd7_3 [2, 1, -6] = true := by decide +kernel
theorem subd7_3_606 : subd7_3 [2, 1, -5] = true := by decide +kernel
theorem subd7_3_607 : subd7_3 [2, 1, -4] = true := by decide +kernel
theorem sbd7_3_18 : ∀ q ∈ blkd7_3_18, subd7_3 q = true := by
  unfold blkd7_3_18
  exact List.forall_mem_cons.2 ⟨subd7_3_576, List.forall_mem_cons.2 ⟨subd7_3_577, List.forall_mem_cons.2 ⟨subd7_3_578, List.forall_mem_cons.2 ⟨subd7_3_579, List.forall_mem_cons.2 ⟨subd7_3_580, List.forall_mem_cons.2 ⟨subd7_3_581, List.forall_mem_cons.2 ⟨subd7_3_582, List.forall_mem_cons.2 ⟨subd7_3_583, List.forall_mem_cons.2 ⟨subd7_3_584, List.forall_mem_cons.2 ⟨subd7_3_585, List.forall_mem_cons.2 ⟨subd7_3_586, List.forall_mem_cons.2 ⟨subd7_3_587, List.forall_mem_cons.2 ⟨subd7_3_588, List.forall_mem_cons.2 ⟨subd7_3_589, List.forall_mem_cons.2 ⟨subd7_3_590, List.forall_mem_cons.2 ⟨subd7_3_591, List.forall_mem_cons.2 ⟨subd7_3_592, List.forall_mem_cons.2 ⟨subd7_3_593, List.forall_mem_cons.2 ⟨subd7_3_594, List.forall_mem_cons.2 ⟨subd7_3_595, List.forall_mem_cons.2 ⟨subd7_3_596, List.forall_mem_cons.2 ⟨subd7_3_597, List.forall_mem_cons.2 ⟨subd7_3_598, List.forall_mem_cons.2 ⟨subd7_3_599, List.forall_mem_cons.2 ⟨subd7_3_600, List.forall_mem_cons.2 ⟨subd7_3_601, List.forall_mem_cons.2 ⟨subd7_3_602, List.forall_mem_cons.2 ⟨subd7_3_603, List.forall_mem_cons.2 ⟨subd7_3_604, List.forall_mem_cons.2 ⟨subd7_3_605, List.forall_mem_cons.2 ⟨subd7_3_606, List.forall_mem_cons.2 ⟨subd7_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_608 : subd7_3 [2, 1, -3] = true := by decide +kernel
theorem subd7_3_609 : subd7_3 [2, 1, -2] = true := by decide +kernel
theorem subd7_3_610 : subd7_3 [2, 1, -1] = true := by decide +kernel
theorem subd7_3_611 : subd7_3 [2, 1, 0] = true := by decide +kernel
theorem subd7_3_612 : subd7_3 [2, 1, 1] = true := by decide +kernel
theorem subd7_3_613 : subd7_3 [2, 1, 2] = true := by decide +kernel
theorem subd7_3_614 : subd7_3 [2, 1, 3] = true := by decide +kernel
theorem subd7_3_615 : subd7_3 [2, 1, 4] = true := by decide +kernel
theorem subd7_3_616 : subd7_3 [2, 1, 5] = true := by decide +kernel
theorem subd7_3_617 : subd7_3 [2, 1, 6] = true := by decide +kernel
theorem subd7_3_618 : subd7_3 [2, 1, 7] = true := by decide +kernel
theorem subd7_3_619 : subd7_3 [2, 1, 8] = true := by decide +kernel
theorem subd7_3_620 : subd7_3 [2, 1, 9] = true := by decide +kernel
theorem sbd7_3_19 : ∀ q ∈ blkd7_3_19, subd7_3 q = true := by
  unfold blkd7_3_19
  exact List.forall_mem_cons.2 ⟨subd7_3_608, List.forall_mem_cons.2 ⟨subd7_3_609, List.forall_mem_cons.2 ⟨subd7_3_610, List.forall_mem_cons.2 ⟨subd7_3_611, List.forall_mem_cons.2 ⟨subd7_3_612, List.forall_mem_cons.2 ⟨subd7_3_613, List.forall_mem_cons.2 ⟨subd7_3_614, List.forall_mem_cons.2 ⟨subd7_3_615, List.forall_mem_cons.2 ⟨subd7_3_616, List.forall_mem_cons.2 ⟨subd7_3_617, List.forall_mem_cons.2 ⟨subd7_3_618, List.forall_mem_cons.2 ⟨subd7_3_619, List.forall_mem_cons.2 ⟨subd7_3_620, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-6, -4] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-6, -3] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [-6, -2] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [-6, -1] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [-6, 0] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [-6, 1] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [-6, 2] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [-5, -6] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [-5, -5] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [-5, -4] = true := by decide +kernel
theorem subd8_0_10 : subd8_0 [-5, -3] = true := by decide +kernel
theorem subd8_0_11 : subd8_0 [-5, -2] = true := by decide +kernel
theorem subd8_0_12 : subd8_0 [-5, -1] = true := by decide +kernel
theorem subd8_0_13 : subd8_0 [-5, 0] = true := by decide +kernel
theorem subd8_0_14 : subd8_0 [-5, 1] = true := by decide +kernel
theorem subd8_0_15 : subd8_0 [-5, 2] = true := by decide +kernel
theorem subd8_0_16 : subd8_0 [-5, 3] = true := by decide +kernel
theorem subd8_0_17 : subd8_0 [-5, 4] = true := by decide +kernel
theorem subd8_0_18 : subd8_0 [-4, -7] = true := by decide +kernel
theorem subd8_0_19 : subd8_0 [-4, -6] = true := by decide +kernel
theorem subd8_0_20 : subd8_0 [-4, -5] = true := by decide +kernel
theorem subd8_0_21 : subd8_0 [-4, -4] = true := by decide +kernel
theorem subd8_0_22 : subd8_0 [-4, -3] = true := by decide +kernel
theorem subd8_0_23 : subd8_0 [-4, -2] = true := by decide +kernel
theorem subd8_0_24 : subd8_0 [-4, -1] = true := by decide +kernel
theorem subd8_0_25 : subd8_0 [-4, 0] = true := by decide +kernel
theorem subd8_0_26 : subd8_0 [-4, 1] = true := by decide +kernel
theorem subd8_0_27 : subd8_0 [-4, 2] = true := by decide +kernel
theorem subd8_0_28 : subd8_0 [-4, 3] = true := by decide +kernel
theorem subd8_0_29 : subd8_0 [-4, 4] = true := by decide +kernel
theorem subd8_0_30 : subd8_0 [-4, 5] = true := by decide +kernel
theorem subd8_0_31 : subd8_0 [-3, -7] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_cons.2 ⟨subd8_0_10, List.forall_mem_cons.2 ⟨subd8_0_11, List.forall_mem_cons.2 ⟨subd8_0_12, List.forall_mem_cons.2 ⟨subd8_0_13, List.forall_mem_cons.2 ⟨subd8_0_14, List.forall_mem_cons.2 ⟨subd8_0_15, List.forall_mem_cons.2 ⟨subd8_0_16, List.forall_mem_cons.2 ⟨subd8_0_17, List.forall_mem_cons.2 ⟨subd8_0_18, List.forall_mem_cons.2 ⟨subd8_0_19, List.forall_mem_cons.2 ⟨subd8_0_20, List.forall_mem_cons.2 ⟨subd8_0_21, List.forall_mem_cons.2 ⟨subd8_0_22, List.forall_mem_cons.2 ⟨subd8_0_23, List.forall_mem_cons.2 ⟨subd8_0_24, List.forall_mem_cons.2 ⟨subd8_0_25, List.forall_mem_cons.2 ⟨subd8_0_26, List.forall_mem_cons.2 ⟨subd8_0_27, List.forall_mem_cons.2 ⟨subd8_0_28, List.forall_mem_cons.2 ⟨subd8_0_29, List.forall_mem_cons.2 ⟨subd8_0_30, List.forall_mem_cons.2 ⟨subd8_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_32 : subd8_0 [-3, -6] = true := by decide +kernel
theorem subd8_0_33 : subd8_0 [-3, -5] = true := by decide +kernel
theorem subd8_0_34 : subd8_0 [-3, -4] = true := by decide +kernel
theorem subd8_0_35 : subd8_0 [-3, -3] = true := by decide +kernel
theorem subd8_0_36 : subd8_0 [-3, -2, -9] = true := by decide +kernel
theorem subd8_0_37 : subd8_0 [-3, -2, -8] = true := by decide +kernel
theorem subd8_0_38 : subd8_0 [-3, -2, -7] = true := by decide +kernel
theorem subd8_0_39 : subd8_0 [-3, -2, -6] = true := by decide +kernel
theorem subd8_0_40 : subd8_0 [-3, -2, -5] = true := by decide +kernel
theorem subd8_0_41 : subd8_0 [-3, -2, -4] = true := by decide +kernel
theorem subd8_0_42 : subd8_0 [-3, -2, -3] = true := by decide +kernel
theorem subd8_0_43 : subd8_0 [-3, -2, -2] = true := by decide +kernel
theorem subd8_0_44 : subd8_0 [-3, -2, -1] = true := by decide +kernel
theorem subd8_0_45 : subd8_0 [-3, -2, 0] = true := by decide +kernel
theorem subd8_0_46 : subd8_0 [-3, -2, 1] = true := by decide +kernel
theorem subd8_0_47 : subd8_0 [-3, -2, 2] = true := by decide +kernel
theorem subd8_0_48 : subd8_0 [-3, -2, 3] = true := by decide +kernel
theorem subd8_0_49 : subd8_0 [-3, -2, 4] = true := by decide +kernel
theorem subd8_0_50 : subd8_0 [-3, -1, -9] = true := by decide +kernel
theorem subd8_0_51 : subd8_0 [-3, -1, -8] = true := by decide +kernel
theorem subd8_0_52 : subd8_0 [-3, -1, -7] = true := by decide +kernel
theorem subd8_0_53 : subd8_0 [-3, -1, -6] = true := by decide +kernel
theorem subd8_0_54 : subd8_0 [-3, -1, -5] = true := by decide +kernel
theorem subd8_0_55 : subd8_0 [-3, -1, -4] = true := by decide +kernel
theorem subd8_0_56 : subd8_0 [-3, -1, -3] = true := by decide +kernel
theorem subd8_0_57 : subd8_0 [-3, -1, -2] = true := by decide +kernel
theorem subd8_0_58 : subd8_0 [-3, -1, -1] = true := by decide +kernel
theorem subd8_0_59 : subd8_0 [-3, -1, 0] = true := by decide +kernel
theorem subd8_0_60 : subd8_0 [-3, -1, 1] = true := by decide +kernel
theorem subd8_0_61 : subd8_0 [-3, -1, 2] = true := by decide +kernel
theorem subd8_0_62 : subd8_0 [-3, -1, 3] = true := by decide +kernel
theorem subd8_0_63 : subd8_0 [-3, -1, 4] = true := by decide +kernel
theorem sbd8_0_1 : ∀ q ∈ blkd8_0_1, subd8_0 q = true := by
  unfold blkd8_0_1
  exact List.forall_mem_cons.2 ⟨subd8_0_32, List.forall_mem_cons.2 ⟨subd8_0_33, List.forall_mem_cons.2 ⟨subd8_0_34, List.forall_mem_cons.2 ⟨subd8_0_35, List.forall_mem_cons.2 ⟨subd8_0_36, List.forall_mem_cons.2 ⟨subd8_0_37, List.forall_mem_cons.2 ⟨subd8_0_38, List.forall_mem_cons.2 ⟨subd8_0_39, List.forall_mem_cons.2 ⟨subd8_0_40, List.forall_mem_cons.2 ⟨subd8_0_41, List.forall_mem_cons.2 ⟨subd8_0_42, List.forall_mem_cons.2 ⟨subd8_0_43, List.forall_mem_cons.2 ⟨subd8_0_44, List.forall_mem_cons.2 ⟨subd8_0_45, List.forall_mem_cons.2 ⟨subd8_0_46, List.forall_mem_cons.2 ⟨subd8_0_47, List.forall_mem_cons.2 ⟨subd8_0_48, List.forall_mem_cons.2 ⟨subd8_0_49, List.forall_mem_cons.2 ⟨subd8_0_50, List.forall_mem_cons.2 ⟨subd8_0_51, List.forall_mem_cons.2 ⟨subd8_0_52, List.forall_mem_cons.2 ⟨subd8_0_53, List.forall_mem_cons.2 ⟨subd8_0_54, List.forall_mem_cons.2 ⟨subd8_0_55, List.forall_mem_cons.2 ⟨subd8_0_56, List.forall_mem_cons.2 ⟨subd8_0_57, List.forall_mem_cons.2 ⟨subd8_0_58, List.forall_mem_cons.2 ⟨subd8_0_59, List.forall_mem_cons.2 ⟨subd8_0_60, List.forall_mem_cons.2 ⟨subd8_0_61, List.forall_mem_cons.2 ⟨subd8_0_62, List.forall_mem_cons.2 ⟨subd8_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_64 : subd8_0 [-3, -1, 5] = true := by decide +kernel
theorem subd8_0_65 : subd8_0 [-3, 0, -8] = true := by decide +kernel
theorem subd8_0_66 : subd8_0 [-3, 0, -7] = true := by decide +kernel
theorem subd8_0_67 : subd8_0 [-3, 0, -6] = true := by decide +kernel
theorem subd8_0_68 : subd8_0 [-3, 0, -5] = true := by decide +kernel
theorem subd8_0_69 : subd8_0 [-3, 0, -4] = true := by decide +kernel
theorem subd8_0_70 : subd8_0 [-3, 0, -3] = true := by decide +kernel
theorem subd8_0_71 : subd8_0 [-3, 0, -2] = true := by decide +kernel
theorem subd8_0_72 : subd8_0 [-3, 0, -1] = true := by decide +kernel
theorem subd8_0_73 : subd8_0 [-3, 0, 0] = true := by decide +kernel
theorem subd8_0_74 : subd8_0 [-3, 0, 1] = true := by decide +kernel
theorem subd8_0_75 : subd8_0 [-3, 0, 2] = true := by decide +kernel
theorem subd8_0_76 : subd8_0 [-3, 0, 3] = true := by decide +kernel
theorem subd8_0_77 : subd8_0 [-3, 0, 4] = true := by decide +kernel
theorem subd8_0_78 : subd8_0 [-3, 0, 5] = true := by decide +kernel
theorem subd8_0_79 : subd8_0 [-3, 1, -8] = true := by decide +kernel
theorem subd8_0_80 : subd8_0 [-3, 1, -7] = true := by decide +kernel
theorem subd8_0_81 : subd8_0 [-3, 1, -6] = true := by decide +kernel
theorem subd8_0_82 : subd8_0 [-3, 1, -5] = true := by decide +kernel
theorem subd8_0_83 : subd8_0 [-3, 1, -4] = true := by decide +kernel
theorem subd8_0_84 : subd8_0 [-3, 1, -3] = true := by decide +kernel
theorem subd8_0_85 : subd8_0 [-3, 1, -2] = true := by decide +kernel
theorem subd8_0_86 : subd8_0 [-3, 1, -1] = true := by decide +kernel
theorem subd8_0_87 : subd8_0 [-3, 1, 0] = true := by decide +kernel
theorem subd8_0_88 : subd8_0 [-3, 1, 1] = true := by decide +kernel
theorem subd8_0_89 : subd8_0 [-3, 1, 2] = true := by decide +kernel
theorem subd8_0_90 : subd8_0 [-3, 1, 3] = true := by decide +kernel
theorem subd8_0_91 : subd8_0 [-3, 1, 4] = true := by decide +kernel
theorem subd8_0_92 : subd8_0 [-3, 1, 5] = true := by decide +kernel
theorem subd8_0_93 : subd8_0 [-3, 1, 6] = true := by decide +kernel
theorem subd8_0_94 : subd8_0 [-3, 2] = true := by decide +kernel
theorem subd8_0_95 : subd8_0 [-3, 3] = true := by decide +kernel
theorem sbd8_0_2 : ∀ q ∈ blkd8_0_2, subd8_0 q = true := by
  unfold blkd8_0_2
  exact List.forall_mem_cons.2 ⟨subd8_0_64, List.forall_mem_cons.2 ⟨subd8_0_65, List.forall_mem_cons.2 ⟨subd8_0_66, List.forall_mem_cons.2 ⟨subd8_0_67, List.forall_mem_cons.2 ⟨subd8_0_68, List.forall_mem_cons.2 ⟨subd8_0_69, List.forall_mem_cons.2 ⟨subd8_0_70, List.forall_mem_cons.2 ⟨subd8_0_71, List.forall_mem_cons.2 ⟨subd8_0_72, List.forall_mem_cons.2 ⟨subd8_0_73, List.forall_mem_cons.2 ⟨subd8_0_74, List.forall_mem_cons.2 ⟨subd8_0_75, List.forall_mem_cons.2 ⟨subd8_0_76, List.forall_mem_cons.2 ⟨subd8_0_77, List.forall_mem_cons.2 ⟨subd8_0_78, List.forall_mem_cons.2 ⟨subd8_0_79, List.forall_mem_cons.2 ⟨subd8_0_80, List.forall_mem_cons.2 ⟨subd8_0_81, List.forall_mem_cons.2 ⟨subd8_0_82, List.forall_mem_cons.2 ⟨subd8_0_83, List.forall_mem_cons.2 ⟨subd8_0_84, List.forall_mem_cons.2 ⟨subd8_0_85, List.forall_mem_cons.2 ⟨subd8_0_86, List.forall_mem_cons.2 ⟨subd8_0_87, List.forall_mem_cons.2 ⟨subd8_0_88, List.forall_mem_cons.2 ⟨subd8_0_89, List.forall_mem_cons.2 ⟨subd8_0_90, List.forall_mem_cons.2 ⟨subd8_0_91, List.forall_mem_cons.2 ⟨subd8_0_92, List.forall_mem_cons.2 ⟨subd8_0_93, List.forall_mem_cons.2 ⟨subd8_0_94, List.forall_mem_cons.2 ⟨subd8_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_96 : subd8_0 [-3, 4] = true := by decide +kernel
theorem subd8_0_97 : subd8_0 [-3, 5] = true := by decide +kernel
theorem subd8_0_98 : subd8_0 [-2, -8] = true := by decide +kernel
theorem subd8_0_99 : subd8_0 [-2, -7] = true := by decide +kernel
theorem subd8_0_100 : subd8_0 [-2, -6] = true := by decide +kernel
theorem subd8_0_101 : subd8_0 [-2, -5] = true := by decide +kernel
theorem subd8_0_102 : subd8_0 [-2, -4] = true := by decide +kernel
theorem subd8_0_103 : subd8_0 [-2, -3, -9] = true := by decide +kernel
theorem subd8_0_104 : subd8_0 [-2, -3, -8] = true := by decide +kernel
theorem subd8_0_105 : subd8_0 [-2, -3, -7] = true := by decide +kernel
theorem subd8_0_106 : subd8_0 [-2, -3, -6] = true := by decide +kernel
theorem subd8_0_107 : subd8_0 [-2, -3, -5] = true := by decide +kernel
theorem subd8_0_108 : subd8_0 [-2, -3, -4] = true := by decide +kernel
theorem subd8_0_109 : subd8_0 [-2, -3, -3] = true := by decide +kernel
theorem subd8_0_110 : subd8_0 [-2, -3, -2] = true := by decide +kernel
theorem subd8_0_111 : subd8_0 [-2, -3, -1] = true := by decide +kernel
theorem subd8_0_112 : subd8_0 [-2, -3, 0] = true := by decide +kernel
theorem subd8_0_113 : subd8_0 [-2, -3, 1] = true := by decide +kernel
theorem subd8_0_114 : subd8_0 [-2, -3, 2] = true := by decide +kernel
theorem subd8_0_115 : subd8_0 [-2, -3, 3] = true := by decide +kernel
theorem subd8_0_116 : subd8_0 [-2, -3, 4] = true := by decide +kernel
theorem subd8_0_117 : subd8_0 [-2, -2, -9] = true := by decide +kernel
theorem subd8_0_118 : subd8_0 [-2, -2, -8] = true := by decide +kernel
theorem subd8_0_119 : subd8_0 [-2, -2, -7] = true := by decide +kernel
theorem subd8_0_120 : subd8_0 [-2, -2, -6] = true := by decide +kernel
theorem subd8_0_121 : subd8_0 [-2, -2, -5] = true := by decide +kernel
theorem subd8_0_122 : subd8_0 [-2, -2, -4] = true := by decide +kernel
theorem subd8_0_123 : subd8_0 [-2, -2, -3] = true := by decide +kernel
theorem subd8_0_124 : subd8_0 [-2, -2, -2] = true := by decide +kernel
theorem subd8_0_125 : subd8_0 [-2, -2, -1] = true := by decide +kernel
theorem subd8_0_126 : subd8_0 [-2, -2, 0] = true := by decide +kernel
theorem subd8_0_127 : subd8_0 [-2, -2, 1] = true := by decide +kernel
theorem sbd8_0_3 : ∀ q ∈ blkd8_0_3, subd8_0 q = true := by
  unfold blkd8_0_3
  exact List.forall_mem_cons.2 ⟨subd8_0_96, List.forall_mem_cons.2 ⟨subd8_0_97, List.forall_mem_cons.2 ⟨subd8_0_98, List.forall_mem_cons.2 ⟨subd8_0_99, List.forall_mem_cons.2 ⟨subd8_0_100, List.forall_mem_cons.2 ⟨subd8_0_101, List.forall_mem_cons.2 ⟨subd8_0_102, List.forall_mem_cons.2 ⟨subd8_0_103, List.forall_mem_cons.2 ⟨subd8_0_104, List.forall_mem_cons.2 ⟨subd8_0_105, List.forall_mem_cons.2 ⟨subd8_0_106, List.forall_mem_cons.2 ⟨subd8_0_107, List.forall_mem_cons.2 ⟨subd8_0_108, List.forall_mem_cons.2 ⟨subd8_0_109, List.forall_mem_cons.2 ⟨subd8_0_110, List.forall_mem_cons.2 ⟨subd8_0_111, List.forall_mem_cons.2 ⟨subd8_0_112, List.forall_mem_cons.2 ⟨subd8_0_113, List.forall_mem_cons.2 ⟨subd8_0_114, List.forall_mem_cons.2 ⟨subd8_0_115, List.forall_mem_cons.2 ⟨subd8_0_116, List.forall_mem_cons.2 ⟨subd8_0_117, List.forall_mem_cons.2 ⟨subd8_0_118, List.forall_mem_cons.2 ⟨subd8_0_119, List.forall_mem_cons.2 ⟨subd8_0_120, List.forall_mem_cons.2 ⟨subd8_0_121, List.forall_mem_cons.2 ⟨subd8_0_122, List.forall_mem_cons.2 ⟨subd8_0_123, List.forall_mem_cons.2 ⟨subd8_0_124, List.forall_mem_cons.2 ⟨subd8_0_125, List.forall_mem_cons.2 ⟨subd8_0_126, List.forall_mem_cons.2 ⟨subd8_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_128 : subd8_0 [-2, -2, 2] = true := by decide +kernel
theorem subd8_0_129 : subd8_0 [-2, -2, 3] = true := by decide +kernel
theorem subd8_0_130 : subd8_0 [-2, -2, 4] = true := by decide +kernel
theorem subd8_0_131 : subd8_0 [-2, -2, 5] = true := by decide +kernel
theorem subd8_0_132 : subd8_0 [-2, -1, -9] = true := by decide +kernel
theorem subd8_0_133 : subd8_0 [-2, -1, -8] = true := by decide +kernel
theorem subd8_0_134 : subd8_0 [-2, -1, -7] = true := by decide +kernel
theorem subd8_0_135 : subd8_0 [-2, -1, -6] = true := by decide +kernel
theorem subd8_0_136 : subd8_0 [-2, -1, -5] = true := by decide +kernel
theorem subd8_0_137 : subd8_0 [-2, -1, -4] = true := by decide +kernel
theorem subd8_0_138 : subd8_0 [-2, -1, -3] = true := by decide +kernel
theorem subd8_0_139 : subd8_0 [-2, -1, -2] = true := by decide +kernel
theorem subd8_0_140 : subd8_0 [-2, -1, -1] = true := by decide +kernel
theorem subd8_0_141 : subd8_0 [-2, -1, 0] = true := by decide +kernel
theorem subd8_0_142 : subd8_0 [-2, -1, 1] = true := by decide +kernel
theorem subd8_0_143 : subd8_0 [-2, -1, 2] = true := by decide +kernel
theorem subd8_0_144 : subd8_0 [-2, -1, 3] = true := by decide +kernel
theorem subd8_0_145 : subd8_0 [-2, -1, 4] = true := by decide +kernel
theorem subd8_0_146 : subd8_0 [-2, -1, 5] = true := by decide +kernel
theorem subd8_0_147 : subd8_0 [-2, -1, 6] = true := by decide +kernel
theorem subd8_0_148 : subd8_0 [-2, 0, -9] = true := by decide +kernel
theorem subd8_0_149 : subd8_0 [-2, 0, -8] = true := by decide +kernel
theorem subd8_0_150 : subd8_0 [-2, 0, -7] = true := by decide +kernel
theorem subd8_0_151 : subd8_0 [-2, 0, -6] = true := by decide +kernel
theorem subd8_0_152 : subd8_0 [-2, 0, -5] = true := by decide +kernel
theorem subd8_0_153 : subd8_0 [-2, 0, -4] = true := by decide +kernel
theorem subd8_0_154 : subd8_0 [-2, 0, -3] = true := by decide +kernel
theorem subd8_0_155 : subd8_0 [-2, 0, -2] = true := by decide +kernel
theorem subd8_0_156 : subd8_0 [-2, 0, -1] = true := by decide +kernel
theorem subd8_0_157 : subd8_0 [-2, 0, 0] = true := by decide +kernel
theorem subd8_0_158 : subd8_0 [-2, 0, 1] = true := by decide +kernel
theorem subd8_0_159 : subd8_0 [-2, 0, 2] = true := by decide +kernel
theorem sbd8_0_4 : ∀ q ∈ blkd8_0_4, subd8_0 q = true := by
  unfold blkd8_0_4
  exact List.forall_mem_cons.2 ⟨subd8_0_128, List.forall_mem_cons.2 ⟨subd8_0_129, List.forall_mem_cons.2 ⟨subd8_0_130, List.forall_mem_cons.2 ⟨subd8_0_131, List.forall_mem_cons.2 ⟨subd8_0_132, List.forall_mem_cons.2 ⟨subd8_0_133, List.forall_mem_cons.2 ⟨subd8_0_134, List.forall_mem_cons.2 ⟨subd8_0_135, List.forall_mem_cons.2 ⟨subd8_0_136, List.forall_mem_cons.2 ⟨subd8_0_137, List.forall_mem_cons.2 ⟨subd8_0_138, List.forall_mem_cons.2 ⟨subd8_0_139, List.forall_mem_cons.2 ⟨subd8_0_140, List.forall_mem_cons.2 ⟨subd8_0_141, List.forall_mem_cons.2 ⟨subd8_0_142, List.forall_mem_cons.2 ⟨subd8_0_143, List.forall_mem_cons.2 ⟨subd8_0_144, List.forall_mem_cons.2 ⟨subd8_0_145, List.forall_mem_cons.2 ⟨subd8_0_146, List.forall_mem_cons.2 ⟨subd8_0_147, List.forall_mem_cons.2 ⟨subd8_0_148, List.forall_mem_cons.2 ⟨subd8_0_149, List.forall_mem_cons.2 ⟨subd8_0_150, List.forall_mem_cons.2 ⟨subd8_0_151, List.forall_mem_cons.2 ⟨subd8_0_152, List.forall_mem_cons.2 ⟨subd8_0_153, List.forall_mem_cons.2 ⟨subd8_0_154, List.forall_mem_cons.2 ⟨subd8_0_155, List.forall_mem_cons.2 ⟨subd8_0_156, List.forall_mem_cons.2 ⟨subd8_0_157, List.forall_mem_cons.2 ⟨subd8_0_158, List.forall_mem_cons.2 ⟨subd8_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_160 : subd8_0 [-2, 0, 3] = true := by decide +kernel
theorem subd8_0_161 : subd8_0 [-2, 0, 4] = true := by decide +kernel
theorem subd8_0_162 : subd8_0 [-2, 0, 5] = true := by decide +kernel
theorem subd8_0_163 : subd8_0 [-2, 0, 6] = true := by decide +kernel
theorem subd8_0_164 : subd8_0 [-2, 1, -8] = true := by decide +kernel
theorem subd8_0_165 : subd8_0 [-2, 1, -7] = true := by decide +kernel
theorem subd8_0_166 : subd8_0 [-2, 1, -6] = true := by decide +kernel
theorem subd8_0_167 : subd8_0 [-2, 1, -5] = true := by decide +kernel
theorem subd8_0_168 : subd8_0 [-2, 1, -4] = true := by decide +kernel
theorem subd8_0_169 : subd8_0 [-2, 1, -3] = true := by decide +kernel
theorem subd8_0_170 : subd8_0 [-2, 1, -2] = true := by decide +kernel
theorem subd8_0_171 : subd8_0 [-2, 1, -1] = true := by decide +kernel
theorem subd8_0_172 : subd8_0 [-2, 1, 0] = true := by decide +kernel
theorem subd8_0_173 : subd8_0 [-2, 1, 1] = true := by decide +kernel
theorem subd8_0_174 : subd8_0 [-2, 1, 2] = true := by decide +kernel
theorem subd8_0_175 : subd8_0 [-2, 1, 3] = true := by decide +kernel
theorem subd8_0_176 : subd8_0 [-2, 1, 4] = true := by decide +kernel
theorem subd8_0_177 : subd8_0 [-2, 1, 5] = true := by decide +kernel
theorem subd8_0_178 : subd8_0 [-2, 1, 6] = true := by decide +kernel
theorem subd8_0_179 : subd8_0 [-2, 2, -7] = true := by decide +kernel
theorem subd8_0_180 : subd8_0 [-2, 2, -6] = true := by decide +kernel
theorem subd8_0_181 : subd8_0 [-2, 2, -5] = true := by decide +kernel
theorem subd8_0_182 : subd8_0 [-2, 2, -4] = true := by decide +kernel
theorem subd8_0_183 : subd8_0 [-2, 2, -3] = true := by decide +kernel
theorem subd8_0_184 : subd8_0 [-2, 2, -2] = true := by decide +kernel
theorem subd8_0_185 : subd8_0 [-2, 2, -1] = true := by decide +kernel
theorem subd8_0_186 : subd8_0 [-2, 2, 0] = true := by decide +kernel
theorem subd8_0_187 : subd8_0 [-2, 2, 1] = true := by decide +kernel
theorem subd8_0_188 : subd8_0 [-2, 2, 2] = true := by decide +kernel
theorem subd8_0_189 : subd8_0 [-2, 2, 3] = true := by decide +kernel
theorem subd8_0_190 : subd8_0 [-2, 2, 4] = true := by decide +kernel
theorem subd8_0_191 : subd8_0 [-2, 2, 5] = true := by decide +kernel
theorem sbd8_0_5 : ∀ q ∈ blkd8_0_5, subd8_0 q = true := by
  unfold blkd8_0_5
  exact List.forall_mem_cons.2 ⟨subd8_0_160, List.forall_mem_cons.2 ⟨subd8_0_161, List.forall_mem_cons.2 ⟨subd8_0_162, List.forall_mem_cons.2 ⟨subd8_0_163, List.forall_mem_cons.2 ⟨subd8_0_164, List.forall_mem_cons.2 ⟨subd8_0_165, List.forall_mem_cons.2 ⟨subd8_0_166, List.forall_mem_cons.2 ⟨subd8_0_167, List.forall_mem_cons.2 ⟨subd8_0_168, List.forall_mem_cons.2 ⟨subd8_0_169, List.forall_mem_cons.2 ⟨subd8_0_170, List.forall_mem_cons.2 ⟨subd8_0_171, List.forall_mem_cons.2 ⟨subd8_0_172, List.forall_mem_cons.2 ⟨subd8_0_173, List.forall_mem_cons.2 ⟨subd8_0_174, List.forall_mem_cons.2 ⟨subd8_0_175, List.forall_mem_cons.2 ⟨subd8_0_176, List.forall_mem_cons.2 ⟨subd8_0_177, List.forall_mem_cons.2 ⟨subd8_0_178, List.forall_mem_cons.2 ⟨subd8_0_179, List.forall_mem_cons.2 ⟨subd8_0_180, List.forall_mem_cons.2 ⟨subd8_0_181, List.forall_mem_cons.2 ⟨subd8_0_182, List.forall_mem_cons.2 ⟨subd8_0_183, List.forall_mem_cons.2 ⟨subd8_0_184, List.forall_mem_cons.2 ⟨subd8_0_185, List.forall_mem_cons.2 ⟨subd8_0_186, List.forall_mem_cons.2 ⟨subd8_0_187, List.forall_mem_cons.2 ⟨subd8_0_188, List.forall_mem_cons.2 ⟨subd8_0_189, List.forall_mem_cons.2 ⟨subd8_0_190, List.forall_mem_cons.2 ⟨subd8_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
