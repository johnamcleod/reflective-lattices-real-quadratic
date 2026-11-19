import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_0_544 : subd7_0 [2, 1, -4] = true := by decide +kernel
theorem subd7_0_545 : subd7_0 [2, 1, -3] = true := by decide +kernel
theorem subd7_0_546 : subd7_0 [2, 1, -2] = true := by decide +kernel
theorem subd7_0_547 : subd7_0 [2, 1, -1] = true := by decide +kernel
theorem subd7_0_548 : subd7_0 [2, 1, 0] = true := by decide +kernel
theorem subd7_0_549 : subd7_0 [2, 1, 1] = true := by decide +kernel
theorem subd7_0_550 : subd7_0 [2, 1, 2] = true := by decide +kernel
theorem subd7_0_551 : subd7_0 [2, 1, 3] = true := by decide +kernel
theorem subd7_0_552 : subd7_0 [2, 1, 4] = true := by decide +kernel
theorem subd7_0_553 : subd7_0 [2, 1, 5] = true := by decide +kernel
theorem subd7_0_554 : subd7_0 [2, 1, 6] = true := by decide +kernel
theorem subd7_0_555 : subd7_0 [2, 2, -7] = true := by decide +kernel
theorem subd7_0_556 : subd7_0 [2, 2, -6] = true := by decide +kernel
theorem subd7_0_557 : subd7_0 [2, 2, -5] = true := by decide +kernel
theorem subd7_0_558 : subd7_0 [2, 2, -4] = true := by decide +kernel
theorem subd7_0_559 : subd7_0 [2, 2, -3] = true := by decide +kernel
theorem subd7_0_560 : subd7_0 [2, 2, -2] = true := by decide +kernel
theorem subd7_0_561 : subd7_0 [2, 2, -1] = true := by decide +kernel
theorem subd7_0_562 : subd7_0 [2, 2, 0] = true := by decide +kernel
theorem subd7_0_563 : subd7_0 [2, 2, 1] = true := by decide +kernel
theorem subd7_0_564 : subd7_0 [2, 2, 2] = true := by decide +kernel
theorem subd7_0_565 : subd7_0 [2, 2, 3] = true := by decide +kernel
theorem subd7_0_566 : subd7_0 [2, 2, 4] = true := by decide +kernel
theorem subd7_0_567 : subd7_0 [2, 2, 5] = true := by decide +kernel
theorem subd7_0_568 : subd7_0 [2, 2, 6] = true := by decide +kernel
theorem subd7_0_569 : subd7_0 [2, 3, -7] = true := by decide +kernel
theorem subd7_0_570 : subd7_0 [2, 3, -6] = true := by decide +kernel
theorem subd7_0_571 : subd7_0 [2, 3, -5] = true := by decide +kernel
theorem subd7_0_572 : subd7_0 [2, 3, -4] = true := by decide +kernel
theorem subd7_0_573 : subd7_0 [2, 3, -3] = true := by decide +kernel
theorem subd7_0_574 : subd7_0 [2, 3, -2] = true := by decide +kernel
theorem subd7_0_575 : subd7_0 [2, 3, -1] = true := by decide +kernel
theorem sbd7_0_17 : ∀ q ∈ blkd7_0_17, subd7_0 q = true := by
  unfold blkd7_0_17
  exact List.forall_mem_cons.2 ⟨subd7_0_544, List.forall_mem_cons.2 ⟨subd7_0_545, List.forall_mem_cons.2 ⟨subd7_0_546, List.forall_mem_cons.2 ⟨subd7_0_547, List.forall_mem_cons.2 ⟨subd7_0_548, List.forall_mem_cons.2 ⟨subd7_0_549, List.forall_mem_cons.2 ⟨subd7_0_550, List.forall_mem_cons.2 ⟨subd7_0_551, List.forall_mem_cons.2 ⟨subd7_0_552, List.forall_mem_cons.2 ⟨subd7_0_553, List.forall_mem_cons.2 ⟨subd7_0_554, List.forall_mem_cons.2 ⟨subd7_0_555, List.forall_mem_cons.2 ⟨subd7_0_556, List.forall_mem_cons.2 ⟨subd7_0_557, List.forall_mem_cons.2 ⟨subd7_0_558, List.forall_mem_cons.2 ⟨subd7_0_559, List.forall_mem_cons.2 ⟨subd7_0_560, List.forall_mem_cons.2 ⟨subd7_0_561, List.forall_mem_cons.2 ⟨subd7_0_562, List.forall_mem_cons.2 ⟨subd7_0_563, List.forall_mem_cons.2 ⟨subd7_0_564, List.forall_mem_cons.2 ⟨subd7_0_565, List.forall_mem_cons.2 ⟨subd7_0_566, List.forall_mem_cons.2 ⟨subd7_0_567, List.forall_mem_cons.2 ⟨subd7_0_568, List.forall_mem_cons.2 ⟨subd7_0_569, List.forall_mem_cons.2 ⟨subd7_0_570, List.forall_mem_cons.2 ⟨subd7_0_571, List.forall_mem_cons.2 ⟨subd7_0_572, List.forall_mem_cons.2 ⟨subd7_0_573, List.forall_mem_cons.2 ⟨subd7_0_574, List.forall_mem_cons.2 ⟨subd7_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_576 : subd7_0 [2, 3, 0] = true := by decide +kernel
theorem subd7_0_577 : subd7_0 [2, 3, 1] = true := by decide +kernel
theorem subd7_0_578 : subd7_0 [2, 3, 2] = true := by decide +kernel
theorem subd7_0_579 : subd7_0 [2, 3, 3] = true := by decide +kernel
theorem subd7_0_580 : subd7_0 [2, 3, 4] = true := by decide +kernel
theorem subd7_0_581 : subd7_0 [2, 3, 5] = true := by decide +kernel
theorem subd7_0_582 : subd7_0 [2, 3, 6] = true := by decide +kernel
theorem subd7_0_583 : subd7_0 [2, 3, 7] = true := by decide +kernel
theorem subd7_0_584 : subd7_0 [2, 4] = true := by decide +kernel
theorem subd7_0_585 : subd7_0 [2, 5] = true := by decide +kernel
theorem subd7_0_586 : subd7_0 [2, 6] = true := by decide +kernel
theorem subd7_0_587 : subd7_0 [3, -5] = true := by decide +kernel
theorem subd7_0_588 : subd7_0 [3, -4] = true := by decide +kernel
theorem subd7_0_589 : subd7_0 [3, -3] = true := by decide +kernel
theorem subd7_0_590 : subd7_0 [3, -2] = true := by decide +kernel
theorem subd7_0_591 : subd7_0 [3, -1] = true := by decide +kernel
theorem subd7_0_592 : subd7_0 [3, 0, -8] = true := by decide +kernel
theorem subd7_0_593 : subd7_0 [3, 0, -7] = true := by decide +kernel
theorem subd7_0_594 : subd7_0 [3, 0, -6] = true := by decide +kernel
theorem subd7_0_595 : subd7_0 [3, 0, -5] = true := by decide +kernel
theorem subd7_0_596 : subd7_0 [3, 0, -4] = true := by decide +kernel
theorem subd7_0_597 : subd7_0 [3, 0, -3] = true := by decide +kernel
theorem subd7_0_598 : subd7_0 [3, 0, -2] = true := by decide +kernel
theorem subd7_0_599 : subd7_0 [3, 0, -1] = true := by decide +kernel
theorem subd7_0_600 : subd7_0 [3, 0, 0] = true := by decide +kernel
theorem subd7_0_601 : subd7_0 [3, 0, 1] = true := by decide +kernel
theorem subd7_0_602 : subd7_0 [3, 0, 2] = true := by decide +kernel
theorem subd7_0_603 : subd7_0 [3, 0, 3] = true := by decide +kernel
theorem subd7_0_604 : subd7_0 [3, 0, 4] = true := by decide +kernel
theorem subd7_0_605 : subd7_0 [3, 0, 5] = true := by decide +kernel
theorem subd7_0_606 : subd7_0 [3, 1, -8] = true := by decide +kernel
theorem subd7_0_607 : subd7_0 [3, 1, -7] = true := by decide +kernel
theorem sbd7_0_18 : ∀ q ∈ blkd7_0_18, subd7_0 q = true := by
  unfold blkd7_0_18
  exact List.forall_mem_cons.2 ⟨subd7_0_576, List.forall_mem_cons.2 ⟨subd7_0_577, List.forall_mem_cons.2 ⟨subd7_0_578, List.forall_mem_cons.2 ⟨subd7_0_579, List.forall_mem_cons.2 ⟨subd7_0_580, List.forall_mem_cons.2 ⟨subd7_0_581, List.forall_mem_cons.2 ⟨subd7_0_582, List.forall_mem_cons.2 ⟨subd7_0_583, List.forall_mem_cons.2 ⟨subd7_0_584, List.forall_mem_cons.2 ⟨subd7_0_585, List.forall_mem_cons.2 ⟨subd7_0_586, List.forall_mem_cons.2 ⟨subd7_0_587, List.forall_mem_cons.2 ⟨subd7_0_588, List.forall_mem_cons.2 ⟨subd7_0_589, List.forall_mem_cons.2 ⟨subd7_0_590, List.forall_mem_cons.2 ⟨subd7_0_591, List.forall_mem_cons.2 ⟨subd7_0_592, List.forall_mem_cons.2 ⟨subd7_0_593, List.forall_mem_cons.2 ⟨subd7_0_594, List.forall_mem_cons.2 ⟨subd7_0_595, List.forall_mem_cons.2 ⟨subd7_0_596, List.forall_mem_cons.2 ⟨subd7_0_597, List.forall_mem_cons.2 ⟨subd7_0_598, List.forall_mem_cons.2 ⟨subd7_0_599, List.forall_mem_cons.2 ⟨subd7_0_600, List.forall_mem_cons.2 ⟨subd7_0_601, List.forall_mem_cons.2 ⟨subd7_0_602, List.forall_mem_cons.2 ⟨subd7_0_603, List.forall_mem_cons.2 ⟨subd7_0_604, List.forall_mem_cons.2 ⟨subd7_0_605, List.forall_mem_cons.2 ⟨subd7_0_606, List.forall_mem_cons.2 ⟨subd7_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_608 : subd7_0 [3, 1, -6] = true := by decide +kernel
theorem subd7_0_609 : subd7_0 [3, 1, -5] = true := by decide +kernel
theorem subd7_0_610 : subd7_0 [3, 1, -4] = true := by decide +kernel
theorem subd7_0_611 : subd7_0 [3, 1, -3] = true := by decide +kernel
theorem subd7_0_612 : subd7_0 [3, 1, -2] = true := by decide +kernel
theorem subd7_0_613 : subd7_0 [3, 1, -1] = true := by decide +kernel
theorem subd7_0_614 : subd7_0 [3, 1, 0] = true := by decide +kernel
theorem subd7_0_615 : subd7_0 [3, 1, 1] = true := by decide +kernel
theorem subd7_0_616 : subd7_0 [3, 1, 2] = true := by decide +kernel
theorem subd7_0_617 : subd7_0 [3, 1, 3] = true := by decide +kernel
theorem subd7_0_618 : subd7_0 [3, 1, 4] = true := by decide +kernel
theorem subd7_0_619 : subd7_0 [3, 1, 5] = true := by decide +kernel
theorem subd7_0_620 : subd7_0 [3, 2, -7] = true := by decide +kernel
theorem subd7_0_621 : subd7_0 [3, 2, -6] = true := by decide +kernel
theorem subd7_0_622 : subd7_0 [3, 2, -5] = true := by decide +kernel
theorem subd7_0_623 : subd7_0 [3, 2, -4] = true := by decide +kernel
theorem subd7_0_624 : subd7_0 [3, 2, -3] = true := by decide +kernel
theorem subd7_0_625 : subd7_0 [3, 2, -2] = true := by decide +kernel
theorem subd7_0_626 : subd7_0 [3, 2, -1] = true := by decide +kernel
theorem subd7_0_627 : subd7_0 [3, 2, 0] = true := by decide +kernel
theorem subd7_0_628 : subd7_0 [3, 2, 1] = true := by decide +kernel
theorem subd7_0_629 : subd7_0 [3, 2, 2] = true := by decide +kernel
theorem subd7_0_630 : subd7_0 [3, 2, 3] = true := by decide +kernel
theorem subd7_0_631 : subd7_0 [3, 2, 4] = true := by decide +kernel
theorem subd7_0_632 : subd7_0 [3, 2, 5] = true := by decide +kernel
theorem subd7_0_633 : subd7_0 [3, 2, 6] = true := by decide +kernel
theorem subd7_0_634 : subd7_0 [3, 3] = true := by decide +kernel
theorem subd7_0_635 : subd7_0 [3, 4] = true := by decide +kernel
theorem subd7_0_636 : subd7_0 [3, 5] = true := by decide +kernel
theorem subd7_0_637 : subd7_0 [3, 6] = true := by decide +kernel
theorem subd7_0_638 : subd7_0 [4, -4] = true := by decide +kernel
theorem subd7_0_639 : subd7_0 [4, -3] = true := by decide +kernel
theorem sbd7_0_19 : ∀ q ∈ blkd7_0_19, subd7_0 q = true := by
  unfold blkd7_0_19
  exact List.forall_mem_cons.2 ⟨subd7_0_608, List.forall_mem_cons.2 ⟨subd7_0_609, List.forall_mem_cons.2 ⟨subd7_0_610, List.forall_mem_cons.2 ⟨subd7_0_611, List.forall_mem_cons.2 ⟨subd7_0_612, List.forall_mem_cons.2 ⟨subd7_0_613, List.forall_mem_cons.2 ⟨subd7_0_614, List.forall_mem_cons.2 ⟨subd7_0_615, List.forall_mem_cons.2 ⟨subd7_0_616, List.forall_mem_cons.2 ⟨subd7_0_617, List.forall_mem_cons.2 ⟨subd7_0_618, List.forall_mem_cons.2 ⟨subd7_0_619, List.forall_mem_cons.2 ⟨subd7_0_620, List.forall_mem_cons.2 ⟨subd7_0_621, List.forall_mem_cons.2 ⟨subd7_0_622, List.forall_mem_cons.2 ⟨subd7_0_623, List.forall_mem_cons.2 ⟨subd7_0_624, List.forall_mem_cons.2 ⟨subd7_0_625, List.forall_mem_cons.2 ⟨subd7_0_626, List.forall_mem_cons.2 ⟨subd7_0_627, List.forall_mem_cons.2 ⟨subd7_0_628, List.forall_mem_cons.2 ⟨subd7_0_629, List.forall_mem_cons.2 ⟨subd7_0_630, List.forall_mem_cons.2 ⟨subd7_0_631, List.forall_mem_cons.2 ⟨subd7_0_632, List.forall_mem_cons.2 ⟨subd7_0_633, List.forall_mem_cons.2 ⟨subd7_0_634, List.forall_mem_cons.2 ⟨subd7_0_635, List.forall_mem_cons.2 ⟨subd7_0_636, List.forall_mem_cons.2 ⟨subd7_0_637, List.forall_mem_cons.2 ⟨subd7_0_638, List.forall_mem_cons.2 ⟨subd7_0_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_640 : subd7_0 [4, -2] = true := by decide +kernel
theorem subd7_0_641 : subd7_0 [4, -1] = true := by decide +kernel
theorem subd7_0_642 : subd7_0 [4, 0] = true := by decide +kernel
theorem subd7_0_643 : subd7_0 [4, 1] = true := by decide +kernel
theorem subd7_0_644 : subd7_0 [4, 2] = true := by decide +kernel
theorem subd7_0_645 : subd7_0 [4, 3] = true := by decide +kernel
theorem subd7_0_646 : subd7_0 [4, 4] = true := by decide +kernel
theorem subd7_0_647 : subd7_0 [4, 5] = true := by decide +kernel
theorem subd7_0_648 : subd7_0 [4, 6] = true := by decide +kernel
theorem subd7_0_649 : subd7_0 [5, -2] = true := by decide +kernel
theorem subd7_0_650 : subd7_0 [5, -1] = true := by decide +kernel
theorem subd7_0_651 : subd7_0 [5, 0] = true := by decide +kernel
theorem subd7_0_652 : subd7_0 [5, 1] = true := by decide +kernel
theorem subd7_0_653 : subd7_0 [5, 2] = true := by decide +kernel
theorem subd7_0_654 : subd7_0 [5, 3] = true := by decide +kernel
theorem subd7_0_655 : subd7_0 [5, 4] = true := by decide +kernel
theorem subd7_0_656 : subd7_0 [5, 5] = true := by decide +kernel
theorem sbd7_0_20 : ∀ q ∈ blkd7_0_20, subd7_0 q = true := by
  unfold blkd7_0_20
  exact List.forall_mem_cons.2 ⟨subd7_0_640, List.forall_mem_cons.2 ⟨subd7_0_641, List.forall_mem_cons.2 ⟨subd7_0_642, List.forall_mem_cons.2 ⟨subd7_0_643, List.forall_mem_cons.2 ⟨subd7_0_644, List.forall_mem_cons.2 ⟨subd7_0_645, List.forall_mem_cons.2 ⟨subd7_0_646, List.forall_mem_cons.2 ⟨subd7_0_647, List.forall_mem_cons.2 ⟨subd7_0_648, List.forall_mem_cons.2 ⟨subd7_0_649, List.forall_mem_cons.2 ⟨subd7_0_650, List.forall_mem_cons.2 ⟨subd7_0_651, List.forall_mem_cons.2 ⟨subd7_0_652, List.forall_mem_cons.2 ⟨subd7_0_653, List.forall_mem_cons.2 ⟨subd7_0_654, List.forall_mem_cons.2 ⟨subd7_0_655, List.forall_mem_cons.2 ⟨subd7_0_656, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [-3, -2] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-3, -1] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [-3, 0] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [-3, 1] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [-3, 2] = true := by decide +kernel
theorem subd7_1_5 : subd7_1 [-3, 3] = true := by decide +kernel
theorem subd7_1_6 : subd7_1 [-2, -4] = true := by decide +kernel
theorem subd7_1_7 : subd7_1 [-2, -3] = true := by decide +kernel
theorem subd7_1_8 : subd7_1 [-2, -2] = true := by decide +kernel
theorem subd7_1_9 : subd7_1 [-2, -1] = true := by decide +kernel
theorem subd7_1_10 : subd7_1 [-2, 0] = true := by decide +kernel
theorem subd7_1_11 : subd7_1 [-2, 1] = true := by decide +kernel
theorem subd7_1_12 : subd7_1 [-2, 2] = true := by decide +kernel
theorem subd7_1_13 : subd7_1 [-2, 3] = true := by decide +kernel
theorem subd7_1_14 : subd7_1 [-2, 4] = true := by decide +kernel
theorem subd7_1_15 : subd7_1 [-1, -4] = true := by decide +kernel
theorem subd7_1_16 : subd7_1 [-1, -3] = true := by decide +kernel
theorem subd7_1_17 : subd7_1 [-1, -2] = true := by decide +kernel
theorem subd7_1_18 : subd7_1 [-1, -1] = true := by decide +kernel
theorem subd7_1_19 : subd7_1 [-1, 0] = true := by decide +kernel
theorem subd7_1_20 : subd7_1 [-1, 1] = true := by decide +kernel
theorem subd7_1_21 : subd7_1 [-1, 2] = true := by decide +kernel
theorem subd7_1_22 : subd7_1 [-1, 3] = true := by decide +kernel
theorem subd7_1_23 : subd7_1 [-1, 4] = true := by decide +kernel
theorem subd7_1_24 : subd7_1 [0, -5] = true := by decide +kernel
theorem subd7_1_25 : subd7_1 [0, -4] = true := by decide +kernel
theorem subd7_1_26 : subd7_1 [0, -3] = true := by decide +kernel
theorem subd7_1_27 : subd7_1 [0, -2] = true := by decide +kernel
theorem subd7_1_28 : subd7_1 [0, -1] = true := by decide +kernel
theorem subd7_1_29 : subd7_1 [0, 0] = true := by decide +kernel
theorem subd7_1_30 : subd7_1 [0, 1] = true := by decide +kernel
theorem subd7_1_31 : subd7_1 [0, 2] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_cons.2 ⟨subd7_1_5, List.forall_mem_cons.2 ⟨subd7_1_6, List.forall_mem_cons.2 ⟨subd7_1_7, List.forall_mem_cons.2 ⟨subd7_1_8, List.forall_mem_cons.2 ⟨subd7_1_9, List.forall_mem_cons.2 ⟨subd7_1_10, List.forall_mem_cons.2 ⟨subd7_1_11, List.forall_mem_cons.2 ⟨subd7_1_12, List.forall_mem_cons.2 ⟨subd7_1_13, List.forall_mem_cons.2 ⟨subd7_1_14, List.forall_mem_cons.2 ⟨subd7_1_15, List.forall_mem_cons.2 ⟨subd7_1_16, List.forall_mem_cons.2 ⟨subd7_1_17, List.forall_mem_cons.2 ⟨subd7_1_18, List.forall_mem_cons.2 ⟨subd7_1_19, List.forall_mem_cons.2 ⟨subd7_1_20, List.forall_mem_cons.2 ⟨subd7_1_21, List.forall_mem_cons.2 ⟨subd7_1_22, List.forall_mem_cons.2 ⟨subd7_1_23, List.forall_mem_cons.2 ⟨subd7_1_24, List.forall_mem_cons.2 ⟨subd7_1_25, List.forall_mem_cons.2 ⟨subd7_1_26, List.forall_mem_cons.2 ⟨subd7_1_27, List.forall_mem_cons.2 ⟨subd7_1_28, List.forall_mem_cons.2 ⟨subd7_1_29, List.forall_mem_cons.2 ⟨subd7_1_30, List.forall_mem_cons.2 ⟨subd7_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_32 : subd7_1 [0, 3] = true := by decide +kernel
theorem subd7_1_33 : subd7_1 [0, 4] = true := by decide +kernel
theorem subd7_1_34 : subd7_1 [1, -5] = true := by decide +kernel
theorem subd7_1_35 : subd7_1 [1, -4] = true := by decide +kernel
theorem subd7_1_36 : subd7_1 [1, -3] = true := by decide +kernel
theorem subd7_1_37 : subd7_1 [1, -2] = true := by decide +kernel
theorem subd7_1_38 : subd7_1 [1, -1] = true := by decide +kernel
theorem subd7_1_39 : subd7_1 [1, 0] = true := by decide +kernel
theorem subd7_1_40 : subd7_1 [1, 1] = true := by decide +kernel
theorem subd7_1_41 : subd7_1 [1, 2] = true := by decide +kernel
theorem subd7_1_42 : subd7_1 [1, 3] = true := by decide +kernel
theorem subd7_1_43 : subd7_1 [2, -5] = true := by decide +kernel
theorem subd7_1_44 : subd7_1 [2, -4] = true := by decide +kernel
theorem subd7_1_45 : subd7_1 [2, -3] = true := by decide +kernel
theorem subd7_1_46 : subd7_1 [2, -2] = true := by decide +kernel
theorem subd7_1_47 : subd7_1 [2, -1] = true := by decide +kernel
theorem subd7_1_48 : subd7_1 [2, 0] = true := by decide +kernel
theorem subd7_1_49 : subd7_1 [2, 1] = true := by decide +kernel
theorem subd7_1_50 : subd7_1 [2, 2] = true := by decide +kernel
theorem subd7_1_51 : subd7_1 [2, 3] = true := by decide +kernel
theorem subd7_1_52 : subd7_1 [3, -4] = true := by decide +kernel
theorem subd7_1_53 : subd7_1 [3, -3] = true := by decide +kernel
theorem subd7_1_54 : subd7_1 [3, -2] = true := by decide +kernel
theorem subd7_1_55 : subd7_1 [3, -1] = true := by decide +kernel
theorem subd7_1_56 : subd7_1 [3, 0] = true := by decide +kernel
theorem subd7_1_57 : subd7_1 [3, 1] = true := by decide +kernel
theorem sbd7_1_1 : ∀ q ∈ blkd7_1_1, subd7_1 q = true := by
  unfold blkd7_1_1
  exact List.forall_mem_cons.2 ⟨subd7_1_32, List.forall_mem_cons.2 ⟨subd7_1_33, List.forall_mem_cons.2 ⟨subd7_1_34, List.forall_mem_cons.2 ⟨subd7_1_35, List.forall_mem_cons.2 ⟨subd7_1_36, List.forall_mem_cons.2 ⟨subd7_1_37, List.forall_mem_cons.2 ⟨subd7_1_38, List.forall_mem_cons.2 ⟨subd7_1_39, List.forall_mem_cons.2 ⟨subd7_1_40, List.forall_mem_cons.2 ⟨subd7_1_41, List.forall_mem_cons.2 ⟨subd7_1_42, List.forall_mem_cons.2 ⟨subd7_1_43, List.forall_mem_cons.2 ⟨subd7_1_44, List.forall_mem_cons.2 ⟨subd7_1_45, List.forall_mem_cons.2 ⟨subd7_1_46, List.forall_mem_cons.2 ⟨subd7_1_47, List.forall_mem_cons.2 ⟨subd7_1_48, List.forall_mem_cons.2 ⟨subd7_1_49, List.forall_mem_cons.2 ⟨subd7_1_50, List.forall_mem_cons.2 ⟨subd7_1_51, List.forall_mem_cons.2 ⟨subd7_1_52, List.forall_mem_cons.2 ⟨subd7_1_53, List.forall_mem_cons.2 ⟨subd7_1_54, List.forall_mem_cons.2 ⟨subd7_1_55, List.forall_mem_cons.2 ⟨subd7_1_56, List.forall_mem_cons.2 ⟨subd7_1_57, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C141
