import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_2_544 : subd8_2 [2, 1, -8] = true := by decide +kernel
theorem subd8_2_545 : subd8_2 [2, 1, -7] = true := by decide +kernel
theorem subd8_2_546 : subd8_2 [2, 1, -6] = true := by decide +kernel
theorem subd8_2_547 : subd8_2 [2, 1, -5] = true := by decide +kernel
theorem subd8_2_548 : subd8_2 [2, 1, -4] = true := by decide +kernel
theorem subd8_2_549 : subd8_2 [2, 1, -3] = true := by decide +kernel
theorem subd8_2_550 : subd8_2 [2, 1, -2] = true := by decide +kernel
theorem subd8_2_551 : subd8_2 [2, 1, -1] = true := by decide +kernel
theorem subd8_2_552 : subd8_2 [2, 1, 0] = true := by decide +kernel
theorem subd8_2_553 : subd8_2 [2, 1, 1] = true := by decide +kernel
theorem subd8_2_554 : subd8_2 [2, 1, 2] = true := by decide +kernel
theorem subd8_2_555 : subd8_2 [2, 1, 3] = true := by decide +kernel
theorem subd8_2_556 : subd8_2 [2, 1, 4] = true := by decide +kernel
theorem subd8_2_557 : subd8_2 [2, 1, 5] = true := by decide +kernel
theorem subd8_2_558 : subd8_2 [2, 1, 6] = true := by decide +kernel
theorem subd8_2_559 : subd8_2 [2, 2] = true := by decide +kernel
theorem subd8_2_560 : subd8_2 [2, 3] = true := by decide +kernel
theorem subd8_2_561 : subd8_2 [2, 4] = true := by decide +kernel
theorem subd8_2_562 : subd8_2 [2, 5] = true := by decide +kernel
theorem subd8_2_563 : subd8_2 [3, -8] = true := by decide +kernel
theorem subd8_2_564 : subd8_2 [3, -7] = true := by decide +kernel
theorem subd8_2_565 : subd8_2 [3, -6] = true := by decide +kernel
theorem subd8_2_566 : subd8_2 [3, -5] = true := by decide +kernel
theorem subd8_2_567 : subd8_2 [3, -4] = true := by decide +kernel
theorem subd8_2_568 : subd8_2 [3, -3] = true := by decide +kernel
theorem subd8_2_569 : subd8_2 [3, -2, -8] = true := by decide +kernel
theorem subd8_2_570 : subd8_2 [3, -2, -7] = true := by decide +kernel
theorem subd8_2_571 : subd8_2 [3, -2, -6] = true := by decide +kernel
theorem subd8_2_572 : subd8_2 [3, -2, -5] = true := by decide +kernel
theorem subd8_2_573 : subd8_2 [3, -2, -4] = true := by decide +kernel
theorem subd8_2_574 : subd8_2 [3, -2, -3] = true := by decide +kernel
theorem subd8_2_575 : subd8_2 [3, -2, -2] = true := by decide +kernel
theorem sbd8_2_17 : ∀ q ∈ blkd8_2_17, subd8_2 q = true := by
  unfold blkd8_2_17
  exact List.forall_mem_cons.2 ⟨subd8_2_544, List.forall_mem_cons.2 ⟨subd8_2_545, List.forall_mem_cons.2 ⟨subd8_2_546, List.forall_mem_cons.2 ⟨subd8_2_547, List.forall_mem_cons.2 ⟨subd8_2_548, List.forall_mem_cons.2 ⟨subd8_2_549, List.forall_mem_cons.2 ⟨subd8_2_550, List.forall_mem_cons.2 ⟨subd8_2_551, List.forall_mem_cons.2 ⟨subd8_2_552, List.forall_mem_cons.2 ⟨subd8_2_553, List.forall_mem_cons.2 ⟨subd8_2_554, List.forall_mem_cons.2 ⟨subd8_2_555, List.forall_mem_cons.2 ⟨subd8_2_556, List.forall_mem_cons.2 ⟨subd8_2_557, List.forall_mem_cons.2 ⟨subd8_2_558, List.forall_mem_cons.2 ⟨subd8_2_559, List.forall_mem_cons.2 ⟨subd8_2_560, List.forall_mem_cons.2 ⟨subd8_2_561, List.forall_mem_cons.2 ⟨subd8_2_562, List.forall_mem_cons.2 ⟨subd8_2_563, List.forall_mem_cons.2 ⟨subd8_2_564, List.forall_mem_cons.2 ⟨subd8_2_565, List.forall_mem_cons.2 ⟨subd8_2_566, List.forall_mem_cons.2 ⟨subd8_2_567, List.forall_mem_cons.2 ⟨subd8_2_568, List.forall_mem_cons.2 ⟨subd8_2_569, List.forall_mem_cons.2 ⟨subd8_2_570, List.forall_mem_cons.2 ⟨subd8_2_571, List.forall_mem_cons.2 ⟨subd8_2_572, List.forall_mem_cons.2 ⟨subd8_2_573, List.forall_mem_cons.2 ⟨subd8_2_574, List.forall_mem_cons.2 ⟨subd8_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_576 : subd8_2 [3, -2, -1] = true := by decide +kernel
theorem subd8_2_577 : subd8_2 [3, -2, 0] = true := by decide +kernel
theorem subd8_2_578 : subd8_2 [3, -2, 1] = true := by decide +kernel
theorem subd8_2_579 : subd8_2 [3, -2, 2] = true := by decide +kernel
theorem subd8_2_580 : subd8_2 [3, -2, 3] = true := by decide +kernel
theorem subd8_2_581 : subd8_2 [3, -2, 4] = true := by decide +kernel
theorem subd8_2_582 : subd8_2 [3, -2, 5] = true := by decide +kernel
theorem subd8_2_583 : subd8_2 [3, -1, -8] = true := by decide +kernel
theorem subd8_2_584 : subd8_2 [3, -1, -7] = true := by decide +kernel
theorem subd8_2_585 : subd8_2 [3, -1, -6] = true := by decide +kernel
theorem subd8_2_586 : subd8_2 [3, -1, -5] = true := by decide +kernel
theorem subd8_2_587 : subd8_2 [3, -1, -4] = true := by decide +kernel
theorem subd8_2_588 : subd8_2 [3, -1, -3] = true := by decide +kernel
theorem subd8_2_589 : subd8_2 [3, -1, -2] = true := by decide +kernel
theorem subd8_2_590 : subd8_2 [3, -1, -1] = true := by decide +kernel
theorem subd8_2_591 : subd8_2 [3, -1, 0] = true := by decide +kernel
theorem subd8_2_592 : subd8_2 [3, -1, 1] = true := by decide +kernel
theorem subd8_2_593 : subd8_2 [3, -1, 2] = true := by decide +kernel
theorem subd8_2_594 : subd8_2 [3, -1, 3] = true := by decide +kernel
theorem subd8_2_595 : subd8_2 [3, -1, 4] = true := by decide +kernel
theorem subd8_2_596 : subd8_2 [3, -1, 5] = true := by decide +kernel
theorem subd8_2_597 : subd8_2 [3, 0, -8] = true := by decide +kernel
theorem subd8_2_598 : subd8_2 [3, 0, -7] = true := by decide +kernel
theorem subd8_2_599 : subd8_2 [3, 0, -6] = true := by decide +kernel
theorem subd8_2_600 : subd8_2 [3, 0, -5] = true := by decide +kernel
theorem subd8_2_601 : subd8_2 [3, 0, -4] = true := by decide +kernel
theorem subd8_2_602 : subd8_2 [3, 0, -3] = true := by decide +kernel
theorem subd8_2_603 : subd8_2 [3, 0, -2] = true := by decide +kernel
theorem subd8_2_604 : subd8_2 [3, 0, -1] = true := by decide +kernel
theorem subd8_2_605 : subd8_2 [3, 0, 0] = true := by decide +kernel
theorem subd8_2_606 : subd8_2 [3, 0, 1] = true := by decide +kernel
theorem subd8_2_607 : subd8_2 [3, 0, 2] = true := by decide +kernel
theorem sbd8_2_18 : ∀ q ∈ blkd8_2_18, subd8_2 q = true := by
  unfold blkd8_2_18
  exact List.forall_mem_cons.2 ⟨subd8_2_576, List.forall_mem_cons.2 ⟨subd8_2_577, List.forall_mem_cons.2 ⟨subd8_2_578, List.forall_mem_cons.2 ⟨subd8_2_579, List.forall_mem_cons.2 ⟨subd8_2_580, List.forall_mem_cons.2 ⟨subd8_2_581, List.forall_mem_cons.2 ⟨subd8_2_582, List.forall_mem_cons.2 ⟨subd8_2_583, List.forall_mem_cons.2 ⟨subd8_2_584, List.forall_mem_cons.2 ⟨subd8_2_585, List.forall_mem_cons.2 ⟨subd8_2_586, List.forall_mem_cons.2 ⟨subd8_2_587, List.forall_mem_cons.2 ⟨subd8_2_588, List.forall_mem_cons.2 ⟨subd8_2_589, List.forall_mem_cons.2 ⟨subd8_2_590, List.forall_mem_cons.2 ⟨subd8_2_591, List.forall_mem_cons.2 ⟨subd8_2_592, List.forall_mem_cons.2 ⟨subd8_2_593, List.forall_mem_cons.2 ⟨subd8_2_594, List.forall_mem_cons.2 ⟨subd8_2_595, List.forall_mem_cons.2 ⟨subd8_2_596, List.forall_mem_cons.2 ⟨subd8_2_597, List.forall_mem_cons.2 ⟨subd8_2_598, List.forall_mem_cons.2 ⟨subd8_2_599, List.forall_mem_cons.2 ⟨subd8_2_600, List.forall_mem_cons.2 ⟨subd8_2_601, List.forall_mem_cons.2 ⟨subd8_2_602, List.forall_mem_cons.2 ⟨subd8_2_603, List.forall_mem_cons.2 ⟨subd8_2_604, List.forall_mem_cons.2 ⟨subd8_2_605, List.forall_mem_cons.2 ⟨subd8_2_606, List.forall_mem_cons.2 ⟨subd8_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_608 : subd8_2 [3, 0, 3] = true := by decide +kernel
theorem subd8_2_609 : subd8_2 [3, 0, 4] = true := by decide +kernel
theorem subd8_2_610 : subd8_2 [3, 0, 5] = true := by decide +kernel
theorem subd8_2_611 : subd8_2 [3, 1] = true := by decide +kernel
theorem subd8_2_612 : subd8_2 [3, 2] = true := by decide +kernel
theorem subd8_2_613 : subd8_2 [3, 3] = true := by decide +kernel
theorem subd8_2_614 : subd8_2 [3, 4] = true := by decide +kernel
theorem subd8_2_615 : subd8_2 [3, 5] = true := by decide +kernel
theorem subd8_2_616 : subd8_2 [4, -7] = true := by decide +kernel
theorem subd8_2_617 : subd8_2 [4, -6] = true := by decide +kernel
theorem subd8_2_618 : subd8_2 [4, -5] = true := by decide +kernel
theorem subd8_2_619 : subd8_2 [4, -4] = true := by decide +kernel
theorem subd8_2_620 : subd8_2 [4, -3] = true := by decide +kernel
theorem subd8_2_621 : subd8_2 [4, -2] = true := by decide +kernel
theorem subd8_2_622 : subd8_2 [4, -1] = true := by decide +kernel
theorem subd8_2_623 : subd8_2 [4, 0] = true := by decide +kernel
theorem subd8_2_624 : subd8_2 [4, 1] = true := by decide +kernel
theorem subd8_2_625 : subd8_2 [4, 2] = true := by decide +kernel
theorem subd8_2_626 : subd8_2 [4, 3] = true := by decide +kernel
theorem subd8_2_627 : subd8_2 [4, 4] = true := by decide +kernel
theorem subd8_2_628 : subd8_2 [5, -7] = true := by decide +kernel
theorem subd8_2_629 : subd8_2 [5, -6] = true := by decide +kernel
theorem subd8_2_630 : subd8_2 [5, -5] = true := by decide +kernel
theorem subd8_2_631 : subd8_2 [5, -4] = true := by decide +kernel
theorem subd8_2_632 : subd8_2 [5, -3] = true := by decide +kernel
theorem subd8_2_633 : subd8_2 [5, -2] = true := by decide +kernel
theorem subd8_2_634 : subd8_2 [5, -1] = true := by decide +kernel
theorem subd8_2_635 : subd8_2 [5, 0] = true := by decide +kernel
theorem subd8_2_636 : subd8_2 [5, 1] = true := by decide +kernel
theorem subd8_2_637 : subd8_2 [5, 2] = true := by decide +kernel
theorem subd8_2_638 : subd8_2 [5, 3] = true := by decide +kernel
theorem subd8_2_639 : subd8_2 [6, -7] = true := by decide +kernel
theorem sbd8_2_19 : ∀ q ∈ blkd8_2_19, subd8_2 q = true := by
  unfold blkd8_2_19
  exact List.forall_mem_cons.2 ⟨subd8_2_608, List.forall_mem_cons.2 ⟨subd8_2_609, List.forall_mem_cons.2 ⟨subd8_2_610, List.forall_mem_cons.2 ⟨subd8_2_611, List.forall_mem_cons.2 ⟨subd8_2_612, List.forall_mem_cons.2 ⟨subd8_2_613, List.forall_mem_cons.2 ⟨subd8_2_614, List.forall_mem_cons.2 ⟨subd8_2_615, List.forall_mem_cons.2 ⟨subd8_2_616, List.forall_mem_cons.2 ⟨subd8_2_617, List.forall_mem_cons.2 ⟨subd8_2_618, List.forall_mem_cons.2 ⟨subd8_2_619, List.forall_mem_cons.2 ⟨subd8_2_620, List.forall_mem_cons.2 ⟨subd8_2_621, List.forall_mem_cons.2 ⟨subd8_2_622, List.forall_mem_cons.2 ⟨subd8_2_623, List.forall_mem_cons.2 ⟨subd8_2_624, List.forall_mem_cons.2 ⟨subd8_2_625, List.forall_mem_cons.2 ⟨subd8_2_626, List.forall_mem_cons.2 ⟨subd8_2_627, List.forall_mem_cons.2 ⟨subd8_2_628, List.forall_mem_cons.2 ⟨subd8_2_629, List.forall_mem_cons.2 ⟨subd8_2_630, List.forall_mem_cons.2 ⟨subd8_2_631, List.forall_mem_cons.2 ⟨subd8_2_632, List.forall_mem_cons.2 ⟨subd8_2_633, List.forall_mem_cons.2 ⟨subd8_2_634, List.forall_mem_cons.2 ⟨subd8_2_635, List.forall_mem_cons.2 ⟨subd8_2_636, List.forall_mem_cons.2 ⟨subd8_2_637, List.forall_mem_cons.2 ⟨subd8_2_638, List.forall_mem_cons.2 ⟨subd8_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_640 : subd8_2 [6, -6] = true := by decide +kernel
theorem subd8_2_641 : subd8_2 [6, -5] = true := by decide +kernel
theorem subd8_2_642 : subd8_2 [6, -4] = true := by decide +kernel
theorem subd8_2_643 : subd8_2 [6, -3] = true := by decide +kernel
theorem subd8_2_644 : subd8_2 [6, -2] = true := by decide +kernel
theorem subd8_2_645 : subd8_2 [6, -1] = true := by decide +kernel
theorem subd8_2_646 : subd8_2 [6, 0] = true := by decide +kernel
theorem subd8_2_647 : subd8_2 [6, 1] = true := by decide +kernel
theorem subd8_2_648 : subd8_2 [6, 2] = true := by decide +kernel
theorem subd8_2_649 : subd8_2 [7, -6] = true := by decide +kernel
theorem subd8_2_650 : subd8_2 [7, -5] = true := by decide +kernel
theorem subd8_2_651 : subd8_2 [7, -4] = true := by decide +kernel
theorem subd8_2_652 : subd8_2 [7, -3] = true := by decide +kernel
theorem subd8_2_653 : subd8_2 [7, -2] = true := by decide +kernel
theorem subd8_2_654 : subd8_2 [7, -1] = true := by decide +kernel
theorem subd8_2_655 : subd8_2 [7, 0] = true := by decide +kernel
theorem subd8_2_656 : subd8_2 [7, 1] = true := by decide +kernel
theorem sbd8_2_20 : ∀ q ∈ blkd8_2_20, subd8_2 q = true := by
  unfold blkd8_2_20
  exact List.forall_mem_cons.2 ⟨subd8_2_640, List.forall_mem_cons.2 ⟨subd8_2_641, List.forall_mem_cons.2 ⟨subd8_2_642, List.forall_mem_cons.2 ⟨subd8_2_643, List.forall_mem_cons.2 ⟨subd8_2_644, List.forall_mem_cons.2 ⟨subd8_2_645, List.forall_mem_cons.2 ⟨subd8_2_646, List.forall_mem_cons.2 ⟨subd8_2_647, List.forall_mem_cons.2 ⟨subd8_2_648, List.forall_mem_cons.2 ⟨subd8_2_649, List.forall_mem_cons.2 ⟨subd8_2_650, List.forall_mem_cons.2 ⟨subd8_2_651, List.forall_mem_cons.2 ⟨subd8_2_652, List.forall_mem_cons.2 ⟨subd8_2_653, List.forall_mem_cons.2 ⟨subd8_2_654, List.forall_mem_cons.2 ⟨subd8_2_655, List.forall_mem_cons.2 ⟨subd8_2_656, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-3, -3] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-3, -2, -7] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-3, -2, -6] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-3, -2, -5] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [-3, -2, -4] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [-3, -2, -3] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [-3, -2, -2] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [-3, -2, -1] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [-3, -2, 0] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [-3, -2, 1] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [-3, -2, 2] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [-3, -2, 3] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [-3, -2, 4] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [-3, -2, 5] = true := by decide +kernel
theorem subd8_3_14 : subd8_3 [-3, -2, 6] = true := by decide +kernel
theorem subd8_3_15 : subd8_3 [-3, -1, -10] = true := by decide +kernel
theorem subd8_3_16 : subd8_3 [-3, -1, -9] = true := by decide +kernel
theorem subd8_3_17 : subd8_3 [-3, -1, -8] = true := by decide +kernel
theorem subd8_3_18 : subd8_3 [-3, -1, -7] = true := by decide +kernel
theorem subd8_3_19 : subd8_3 [-3, -1, -6] = true := by decide +kernel
theorem subd8_3_20 : subd8_3 [-3, -1, -5] = true := by decide +kernel
theorem subd8_3_21 : subd8_3 [-3, -1, -4] = true := by decide +kernel
theorem subd8_3_22 : subd8_3 [-3, -1, -3] = true := by decide +kernel
theorem subd8_3_23 : subd8_3 [-3, -1, -2] = true := by decide +kernel
theorem subd8_3_24 : subd8_3 [-3, -1, -1] = true := by decide +kernel
theorem subd8_3_25 : subd8_3 [-3, -1, 0] = true := by decide +kernel
theorem subd8_3_26 : subd8_3 [-3, -1, 1] = true := by decide +kernel
theorem subd8_3_27 : subd8_3 [-3, -1, 2] = true := by decide +kernel
theorem subd8_3_28 : subd8_3 [-3, -1, 3] = true := by decide +kernel
theorem subd8_3_29 : subd8_3 [-3, -1, 4] = true := by decide +kernel
theorem subd8_3_30 : subd8_3 [-3, -1, 5] = true := by decide +kernel
theorem subd8_3_31 : subd8_3 [-3, -1, 6] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_cons.2 ⟨subd8_3_14, List.forall_mem_cons.2 ⟨subd8_3_15, List.forall_mem_cons.2 ⟨subd8_3_16, List.forall_mem_cons.2 ⟨subd8_3_17, List.forall_mem_cons.2 ⟨subd8_3_18, List.forall_mem_cons.2 ⟨subd8_3_19, List.forall_mem_cons.2 ⟨subd8_3_20, List.forall_mem_cons.2 ⟨subd8_3_21, List.forall_mem_cons.2 ⟨subd8_3_22, List.forall_mem_cons.2 ⟨subd8_3_23, List.forall_mem_cons.2 ⟨subd8_3_24, List.forall_mem_cons.2 ⟨subd8_3_25, List.forall_mem_cons.2 ⟨subd8_3_26, List.forall_mem_cons.2 ⟨subd8_3_27, List.forall_mem_cons.2 ⟨subd8_3_28, List.forall_mem_cons.2 ⟨subd8_3_29, List.forall_mem_cons.2 ⟨subd8_3_30, List.forall_mem_cons.2 ⟨subd8_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_32 : subd8_3 [-3, -1, 7] = true := by decide +kernel
theorem subd8_3_33 : subd8_3 [-3, 0, -11] = true := by decide +kernel
theorem subd8_3_34 : subd8_3 [-3, 0, -10] = true := by decide +kernel
theorem subd8_3_35 : subd8_3 [-3, 0, -9] = true := by decide +kernel
theorem subd8_3_36 : subd8_3 [-3, 0, -8] = true := by decide +kernel
theorem subd8_3_37 : subd8_3 [-3, 0, -7] = true := by decide +kernel
theorem subd8_3_38 : subd8_3 [-3, 0, -6] = true := by decide +kernel
theorem subd8_3_39 : subd8_3 [-3, 0, -5] = true := by decide +kernel
theorem subd8_3_40 : subd8_3 [-3, 0, -4] = true := by decide +kernel
theorem subd8_3_41 : subd8_3 [-3, 0, -3] = true := by decide +kernel
theorem subd8_3_42 : subd8_3 [-3, 0, -2] = true := by decide +kernel
theorem subd8_3_43 : subd8_3 [-3, 0, -1] = true := by decide +kernel
theorem subd8_3_44 : subd8_3 [-3, 0, 0] = true := by decide +kernel
theorem subd8_3_45 : subd8_3 [-3, 0, 1] = true := by decide +kernel
theorem subd8_3_46 : subd8_3 [-3, 0, 2] = true := by decide +kernel
theorem subd8_3_47 : subd8_3 [-3, 0, 3] = true := by decide +kernel
theorem subd8_3_48 : subd8_3 [-3, 0, 4] = true := by decide +kernel
theorem subd8_3_49 : subd8_3 [-3, 0, 5] = true := by decide +kernel
theorem subd8_3_50 : subd8_3 [-3, 0, 6] = true := by decide +kernel
theorem subd8_3_51 : subd8_3 [-3, 0, 7] = true := by decide +kernel
theorem subd8_3_52 : subd8_3 [-3, 0, 8] = true := by decide +kernel
theorem subd8_3_53 : subd8_3 [-3, 1, -11] = true := by decide +kernel
theorem subd8_3_54 : subd8_3 [-3, 1, -10] = true := by decide +kernel
theorem subd8_3_55 : subd8_3 [-3, 1, -9] = true := by decide +kernel
theorem subd8_3_56 : subd8_3 [-3, 1, -8] = true := by decide +kernel
theorem subd8_3_57 : subd8_3 [-3, 1, -7] = true := by decide +kernel
theorem subd8_3_58 : subd8_3 [-3, 1, -6] = true := by decide +kernel
theorem subd8_3_59 : subd8_3 [-3, 1, -5] = true := by decide +kernel
theorem subd8_3_60 : subd8_3 [-3, 1, -4] = true := by decide +kernel
theorem subd8_3_61 : subd8_3 [-3, 1, -3] = true := by decide +kernel
theorem subd8_3_62 : subd8_3 [-3, 1, -2] = true := by decide +kernel
theorem subd8_3_63 : subd8_3 [-3, 1, -1] = true := by decide +kernel
theorem sbd8_3_1 : ∀ q ∈ blkd8_3_1, subd8_3 q = true := by
  unfold blkd8_3_1
  exact List.forall_mem_cons.2 ⟨subd8_3_32, List.forall_mem_cons.2 ⟨subd8_3_33, List.forall_mem_cons.2 ⟨subd8_3_34, List.forall_mem_cons.2 ⟨subd8_3_35, List.forall_mem_cons.2 ⟨subd8_3_36, List.forall_mem_cons.2 ⟨subd8_3_37, List.forall_mem_cons.2 ⟨subd8_3_38, List.forall_mem_cons.2 ⟨subd8_3_39, List.forall_mem_cons.2 ⟨subd8_3_40, List.forall_mem_cons.2 ⟨subd8_3_41, List.forall_mem_cons.2 ⟨subd8_3_42, List.forall_mem_cons.2 ⟨subd8_3_43, List.forall_mem_cons.2 ⟨subd8_3_44, List.forall_mem_cons.2 ⟨subd8_3_45, List.forall_mem_cons.2 ⟨subd8_3_46, List.forall_mem_cons.2 ⟨subd8_3_47, List.forall_mem_cons.2 ⟨subd8_3_48, List.forall_mem_cons.2 ⟨subd8_3_49, List.forall_mem_cons.2 ⟨subd8_3_50, List.forall_mem_cons.2 ⟨subd8_3_51, List.forall_mem_cons.2 ⟨subd8_3_52, List.forall_mem_cons.2 ⟨subd8_3_53, List.forall_mem_cons.2 ⟨subd8_3_54, List.forall_mem_cons.2 ⟨subd8_3_55, List.forall_mem_cons.2 ⟨subd8_3_56, List.forall_mem_cons.2 ⟨subd8_3_57, List.forall_mem_cons.2 ⟨subd8_3_58, List.forall_mem_cons.2 ⟨subd8_3_59, List.forall_mem_cons.2 ⟨subd8_3_60, List.forall_mem_cons.2 ⟨subd8_3_61, List.forall_mem_cons.2 ⟨subd8_3_62, List.forall_mem_cons.2 ⟨subd8_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_64 : subd8_3 [-3, 1, 0] = true := by decide +kernel
theorem subd8_3_65 : subd8_3 [-3, 1, 1] = true := by decide +kernel
theorem subd8_3_66 : subd8_3 [-3, 1, 2] = true := by decide +kernel
theorem subd8_3_67 : subd8_3 [-3, 1, 3] = true := by decide +kernel
theorem subd8_3_68 : subd8_3 [-3, 1, 4] = true := by decide +kernel
theorem subd8_3_69 : subd8_3 [-3, 1, 5] = true := by decide +kernel
theorem subd8_3_70 : subd8_3 [-3, 1, 6] = true := by decide +kernel
theorem subd8_3_71 : subd8_3 [-3, 2] = true := by decide +kernel
theorem subd8_3_72 : subd8_3 [-2, -4] = true := by decide +kernel
theorem subd8_3_73 : subd8_3 [-2, -3, -7] = true := by decide +kernel
theorem subd8_3_74 : subd8_3 [-2, -3, -6] = true := by decide +kernel
theorem subd8_3_75 : subd8_3 [-2, -3, -5] = true := by decide +kernel
theorem subd8_3_76 : subd8_3 [-2, -3, -4] = true := by decide +kernel
theorem subd8_3_77 : subd8_3 [-2, -3, -3] = true := by decide +kernel
theorem subd8_3_78 : subd8_3 [-2, -3, -2] = true := by decide +kernel
theorem subd8_3_79 : subd8_3 [-2, -3, -1] = true := by decide +kernel
theorem subd8_3_80 : subd8_3 [-2, -3, 0] = true := by decide +kernel
theorem subd8_3_81 : subd8_3 [-2, -3, 1] = true := by decide +kernel
theorem subd8_3_82 : subd8_3 [-2, -3, 2] = true := by decide +kernel
theorem subd8_3_83 : subd8_3 [-2, -3, 3] = true := by decide +kernel
theorem subd8_3_84 : subd8_3 [-2, -3, 4] = true := by decide +kernel
theorem subd8_3_85 : subd8_3 [-2, -3, 5] = true := by decide +kernel
theorem subd8_3_86 : subd8_3 [-2, -3, 6] = true := by decide +kernel
theorem subd8_3_87 : subd8_3 [-2, -3, 7] = true := by decide +kernel
theorem subd8_3_88 : subd8_3 [-2, -2, -10] = true := by decide +kernel
theorem subd8_3_89 : subd8_3 [-2, -2, -9] = true := by decide +kernel
theorem subd8_3_90 : subd8_3 [-2, -2, -8] = true := by decide +kernel
theorem subd8_3_91 : subd8_3 [-2, -2, -7] = true := by decide +kernel
theorem subd8_3_92 : subd8_3 [-2, -2, -6] = true := by decide +kernel
theorem subd8_3_93 : subd8_3 [-2, -2, -5] = true := by decide +kernel
theorem subd8_3_94 : subd8_3 [-2, -2, -4] = true := by decide +kernel
theorem subd8_3_95 : subd8_3 [-2, -2, -3] = true := by decide +kernel
theorem sbd8_3_2 : ∀ q ∈ blkd8_3_2, subd8_3 q = true := by
  unfold blkd8_3_2
  exact List.forall_mem_cons.2 ⟨subd8_3_64, List.forall_mem_cons.2 ⟨subd8_3_65, List.forall_mem_cons.2 ⟨subd8_3_66, List.forall_mem_cons.2 ⟨subd8_3_67, List.forall_mem_cons.2 ⟨subd8_3_68, List.forall_mem_cons.2 ⟨subd8_3_69, List.forall_mem_cons.2 ⟨subd8_3_70, List.forall_mem_cons.2 ⟨subd8_3_71, List.forall_mem_cons.2 ⟨subd8_3_72, List.forall_mem_cons.2 ⟨subd8_3_73, List.forall_mem_cons.2 ⟨subd8_3_74, List.forall_mem_cons.2 ⟨subd8_3_75, List.forall_mem_cons.2 ⟨subd8_3_76, List.forall_mem_cons.2 ⟨subd8_3_77, List.forall_mem_cons.2 ⟨subd8_3_78, List.forall_mem_cons.2 ⟨subd8_3_79, List.forall_mem_cons.2 ⟨subd8_3_80, List.forall_mem_cons.2 ⟨subd8_3_81, List.forall_mem_cons.2 ⟨subd8_3_82, List.forall_mem_cons.2 ⟨subd8_3_83, List.forall_mem_cons.2 ⟨subd8_3_84, List.forall_mem_cons.2 ⟨subd8_3_85, List.forall_mem_cons.2 ⟨subd8_3_86, List.forall_mem_cons.2 ⟨subd8_3_87, List.forall_mem_cons.2 ⟨subd8_3_88, List.forall_mem_cons.2 ⟨subd8_3_89, List.forall_mem_cons.2 ⟨subd8_3_90, List.forall_mem_cons.2 ⟨subd8_3_91, List.forall_mem_cons.2 ⟨subd8_3_92, List.forall_mem_cons.2 ⟨subd8_3_93, List.forall_mem_cons.2 ⟨subd8_3_94, List.forall_mem_cons.2 ⟨subd8_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_96 : subd8_3 [-2, -2, -2] = true := by decide +kernel
theorem subd8_3_97 : subd8_3 [-2, -2, -1] = true := by decide +kernel
theorem subd8_3_98 : subd8_3 [-2, -2, 0] = true := by decide +kernel
theorem subd8_3_99 : subd8_3 [-2, -2, 1] = true := by decide +kernel
theorem subd8_3_100 : subd8_3 [-2, -2, 2] = true := by decide +kernel
theorem subd8_3_101 : subd8_3 [-2, -2, 3] = true := by decide +kernel
theorem subd8_3_102 : subd8_3 [-2, -2, 4] = true := by decide +kernel
theorem subd8_3_103 : subd8_3 [-2, -2, 5] = true := by decide +kernel
theorem subd8_3_104 : subd8_3 [-2, -2, 6] = true := by decide +kernel
theorem subd8_3_105 : subd8_3 [-2, -2, 7] = true := by decide +kernel
theorem subd8_3_106 : subd8_3 [-2, -2, 8] = true := by decide +kernel
theorem subd8_3_107 : subd8_3 [-2, -2, 9] = true := by decide +kernel
theorem subd8_3_108 : subd8_3 [-2, -2, 10] = true := by decide +kernel
theorem subd8_3_109 : subd8_3 [-2, -1, -13] = true := by decide +kernel
theorem subd8_3_110 : subd8_3 [-2, -1, -12] = true := by decide +kernel
theorem subd8_3_111 : subd8_3 [-2, -1, -11] = true := by decide +kernel
theorem subd8_3_112 : subd8_3 [-2, -1, -10] = true := by decide +kernel
theorem subd8_3_113 : subd8_3 [-2, -1, -9] = true := by decide +kernel
theorem subd8_3_114 : subd8_3 [-2, -1, -8] = true := by decide +kernel
theorem subd8_3_115 : subd8_3 [-2, -1, -7] = true := by decide +kernel
theorem subd8_3_116 : subd8_3 [-2, -1, -6] = true := by decide +kernel
theorem subd8_3_117 : subd8_3 [-2, -1, -5] = true := by decide +kernel
theorem subd8_3_118 : subd8_3 [-2, -1, -4] = true := by decide +kernel
theorem subd8_3_119 : subd8_3 [-2, -1, -3] = true := by decide +kernel
theorem subd8_3_120 : subd8_3 [-2, -1, -2] = true := by decide +kernel
theorem subd8_3_121 : subd8_3 [-2, -1, -1] = true := by decide +kernel
theorem subd8_3_122 : subd8_3 [-2, -1, 0] = true := by decide +kernel
theorem subd8_3_123 : subd8_3 [-2, -1, 1] = true := by decide +kernel
theorem subd8_3_124 : subd8_3 [-2, -1, 2] = true := by decide +kernel
theorem subd8_3_125 : subd8_3 [-2, -1, 3] = true := by decide +kernel
theorem subd8_3_126 : subd8_3 [-2, -1, 4] = true := by decide +kernel
theorem subd8_3_127 : subd8_3 [-2, -1, 5] = true := by decide +kernel
theorem sbd8_3_3 : ∀ q ∈ blkd8_3_3, subd8_3 q = true := by
  unfold blkd8_3_3
  exact List.forall_mem_cons.2 ⟨subd8_3_96, List.forall_mem_cons.2 ⟨subd8_3_97, List.forall_mem_cons.2 ⟨subd8_3_98, List.forall_mem_cons.2 ⟨subd8_3_99, List.forall_mem_cons.2 ⟨subd8_3_100, List.forall_mem_cons.2 ⟨subd8_3_101, List.forall_mem_cons.2 ⟨subd8_3_102, List.forall_mem_cons.2 ⟨subd8_3_103, List.forall_mem_cons.2 ⟨subd8_3_104, List.forall_mem_cons.2 ⟨subd8_3_105, List.forall_mem_cons.2 ⟨subd8_3_106, List.forall_mem_cons.2 ⟨subd8_3_107, List.forall_mem_cons.2 ⟨subd8_3_108, List.forall_mem_cons.2 ⟨subd8_3_109, List.forall_mem_cons.2 ⟨subd8_3_110, List.forall_mem_cons.2 ⟨subd8_3_111, List.forall_mem_cons.2 ⟨subd8_3_112, List.forall_mem_cons.2 ⟨subd8_3_113, List.forall_mem_cons.2 ⟨subd8_3_114, List.forall_mem_cons.2 ⟨subd8_3_115, List.forall_mem_cons.2 ⟨subd8_3_116, List.forall_mem_cons.2 ⟨subd8_3_117, List.forall_mem_cons.2 ⟨subd8_3_118, List.forall_mem_cons.2 ⟨subd8_3_119, List.forall_mem_cons.2 ⟨subd8_3_120, List.forall_mem_cons.2 ⟨subd8_3_121, List.forall_mem_cons.2 ⟨subd8_3_122, List.forall_mem_cons.2 ⟨subd8_3_123, List.forall_mem_cons.2 ⟨subd8_3_124, List.forall_mem_cons.2 ⟨subd8_3_125, List.forall_mem_cons.2 ⟨subd8_3_126, List.forall_mem_cons.2 ⟨subd8_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
