import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_0_576 : subd14_0 [2, 6] = true := by decide +kernel
theorem subd14_0_577 : subd14_0 [3, -6] = true := by decide +kernel
theorem subd14_0_578 : subd14_0 [3, -5] = true := by decide +kernel
theorem subd14_0_579 : subd14_0 [3, -4] = true := by decide +kernel
theorem subd14_0_580 : subd14_0 [3, -3] = true := by decide +kernel
theorem subd14_0_581 : subd14_0 [3, -2] = true := by decide +kernel
theorem subd14_0_582 : subd14_0 [3, -1, -8] = true := by decide +kernel
theorem subd14_0_583 : subd14_0 [3, -1, -7] = true := by decide +kernel
theorem subd14_0_584 : subd14_0 [3, -1, -6] = true := by decide +kernel
theorem subd14_0_585 : subd14_0 [3, -1, -5] = true := by decide +kernel
theorem subd14_0_586 : subd14_0 [3, -1, -4] = true := by decide +kernel
theorem subd14_0_587 : subd14_0 [3, -1, -3] = true := by decide +kernel
theorem subd14_0_588 : subd14_0 [3, -1, -2] = true := by decide +kernel
theorem subd14_0_589 : subd14_0 [3, -1, -1] = true := by decide +kernel
theorem subd14_0_590 : subd14_0 [3, -1, 0] = true := by decide +kernel
theorem subd14_0_591 : subd14_0 [3, -1, 1] = true := by decide +kernel
theorem subd14_0_592 : subd14_0 [3, -1, 2] = true := by decide +kernel
theorem subd14_0_593 : subd14_0 [3, -1, 3] = true := by decide +kernel
theorem subd14_0_594 : subd14_0 [3, -1, 4] = true := by decide +kernel
theorem subd14_0_595 : subd14_0 [3, -1, 5] = true := by decide +kernel
theorem subd14_0_596 : subd14_0 [3, 0, -8] = true := by decide +kernel
theorem subd14_0_597 : subd14_0 [3, 0, -7] = true := by decide +kernel
theorem subd14_0_598 : subd14_0 [3, 0, -6] = true := by decide +kernel
theorem subd14_0_599 : subd14_0 [3, 0, -5] = true := by decide +kernel
theorem subd14_0_600 : subd14_0 [3, 0, -4] = true := by decide +kernel
theorem subd14_0_601 : subd14_0 [3, 0, -3] = true := by decide +kernel
theorem subd14_0_602 : subd14_0 [3, 0, -2] = true := by decide +kernel
theorem subd14_0_603 : subd14_0 [3, 0, -1] = true := by decide +kernel
theorem subd14_0_604 : subd14_0 [3, 0, 0] = true := by decide +kernel
theorem subd14_0_605 : subd14_0 [3, 0, 1] = true := by decide +kernel
theorem subd14_0_606 : subd14_0 [3, 0, 2] = true := by decide +kernel
theorem subd14_0_607 : subd14_0 [3, 0, 3] = true := by decide +kernel
theorem sbd14_0_18 : ∀ q ∈ blkd14_0_18, subd14_0 q = true := by
  unfold blkd14_0_18
  exact List.forall_mem_cons.2 ⟨subd14_0_576, List.forall_mem_cons.2 ⟨subd14_0_577, List.forall_mem_cons.2 ⟨subd14_0_578, List.forall_mem_cons.2 ⟨subd14_0_579, List.forall_mem_cons.2 ⟨subd14_0_580, List.forall_mem_cons.2 ⟨subd14_0_581, List.forall_mem_cons.2 ⟨subd14_0_582, List.forall_mem_cons.2 ⟨subd14_0_583, List.forall_mem_cons.2 ⟨subd14_0_584, List.forall_mem_cons.2 ⟨subd14_0_585, List.forall_mem_cons.2 ⟨subd14_0_586, List.forall_mem_cons.2 ⟨subd14_0_587, List.forall_mem_cons.2 ⟨subd14_0_588, List.forall_mem_cons.2 ⟨subd14_0_589, List.forall_mem_cons.2 ⟨subd14_0_590, List.forall_mem_cons.2 ⟨subd14_0_591, List.forall_mem_cons.2 ⟨subd14_0_592, List.forall_mem_cons.2 ⟨subd14_0_593, List.forall_mem_cons.2 ⟨subd14_0_594, List.forall_mem_cons.2 ⟨subd14_0_595, List.forall_mem_cons.2 ⟨subd14_0_596, List.forall_mem_cons.2 ⟨subd14_0_597, List.forall_mem_cons.2 ⟨subd14_0_598, List.forall_mem_cons.2 ⟨subd14_0_599, List.forall_mem_cons.2 ⟨subd14_0_600, List.forall_mem_cons.2 ⟨subd14_0_601, List.forall_mem_cons.2 ⟨subd14_0_602, List.forall_mem_cons.2 ⟨subd14_0_603, List.forall_mem_cons.2 ⟨subd14_0_604, List.forall_mem_cons.2 ⟨subd14_0_605, List.forall_mem_cons.2 ⟨subd14_0_606, List.forall_mem_cons.2 ⟨subd14_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_608 : subd14_0 [3, 0, 4] = true := by decide +kernel
theorem subd14_0_609 : subd14_0 [3, 0, 5] = true := by decide +kernel
theorem subd14_0_610 : subd14_0 [3, 1, -8] = true := by decide +kernel
theorem subd14_0_611 : subd14_0 [3, 1, -7] = true := by decide +kernel
theorem subd14_0_612 : subd14_0 [3, 1, -6] = true := by decide +kernel
theorem subd14_0_613 : subd14_0 [3, 1, -5] = true := by decide +kernel
theorem subd14_0_614 : subd14_0 [3, 1, -4] = true := by decide +kernel
theorem subd14_0_615 : subd14_0 [3, 1, -3] = true := by decide +kernel
theorem subd14_0_616 : subd14_0 [3, 1, -2] = true := by decide +kernel
theorem subd14_0_617 : subd14_0 [3, 1, -1] = true := by decide +kernel
theorem subd14_0_618 : subd14_0 [3, 1, 0] = true := by decide +kernel
theorem subd14_0_619 : subd14_0 [3, 1, 1] = true := by decide +kernel
theorem subd14_0_620 : subd14_0 [3, 1, 2] = true := by decide +kernel
theorem subd14_0_621 : subd14_0 [3, 1, 3] = true := by decide +kernel
theorem subd14_0_622 : subd14_0 [3, 1, 4] = true := by decide +kernel
theorem subd14_0_623 : subd14_0 [3, 1, 5] = true := by decide +kernel
theorem subd14_0_624 : subd14_0 [3, 2] = true := by decide +kernel
theorem subd14_0_625 : subd14_0 [3, 3] = true := by decide +kernel
theorem subd14_0_626 : subd14_0 [3, 4] = true := by decide +kernel
theorem subd14_0_627 : subd14_0 [3, 5] = true := by decide +kernel
theorem subd14_0_628 : subd14_0 [4, -6] = true := by decide +kernel
theorem subd14_0_629 : subd14_0 [4, -5] = true := by decide +kernel
theorem subd14_0_630 : subd14_0 [4, -4] = true := by decide +kernel
theorem subd14_0_631 : subd14_0 [4, -3] = true := by decide +kernel
theorem subd14_0_632 : subd14_0 [4, -2] = true := by decide +kernel
theorem subd14_0_633 : subd14_0 [4, -1] = true := by decide +kernel
theorem subd14_0_634 : subd14_0 [4, 0] = true := by decide +kernel
theorem subd14_0_635 : subd14_0 [4, 1] = true := by decide +kernel
theorem subd14_0_636 : subd14_0 [4, 2] = true := by decide +kernel
theorem subd14_0_637 : subd14_0 [4, 3] = true := by decide +kernel
theorem subd14_0_638 : subd14_0 [4, 4] = true := by decide +kernel
theorem subd14_0_639 : subd14_0 [4, 5] = true := by decide +kernel
theorem sbd14_0_19 : ∀ q ∈ blkd14_0_19, subd14_0 q = true := by
  unfold blkd14_0_19
  exact List.forall_mem_cons.2 ⟨subd14_0_608, List.forall_mem_cons.2 ⟨subd14_0_609, List.forall_mem_cons.2 ⟨subd14_0_610, List.forall_mem_cons.2 ⟨subd14_0_611, List.forall_mem_cons.2 ⟨subd14_0_612, List.forall_mem_cons.2 ⟨subd14_0_613, List.forall_mem_cons.2 ⟨subd14_0_614, List.forall_mem_cons.2 ⟨subd14_0_615, List.forall_mem_cons.2 ⟨subd14_0_616, List.forall_mem_cons.2 ⟨subd14_0_617, List.forall_mem_cons.2 ⟨subd14_0_618, List.forall_mem_cons.2 ⟨subd14_0_619, List.forall_mem_cons.2 ⟨subd14_0_620, List.forall_mem_cons.2 ⟨subd14_0_621, List.forall_mem_cons.2 ⟨subd14_0_622, List.forall_mem_cons.2 ⟨subd14_0_623, List.forall_mem_cons.2 ⟨subd14_0_624, List.forall_mem_cons.2 ⟨subd14_0_625, List.forall_mem_cons.2 ⟨subd14_0_626, List.forall_mem_cons.2 ⟨subd14_0_627, List.forall_mem_cons.2 ⟨subd14_0_628, List.forall_mem_cons.2 ⟨subd14_0_629, List.forall_mem_cons.2 ⟨subd14_0_630, List.forall_mem_cons.2 ⟨subd14_0_631, List.forall_mem_cons.2 ⟨subd14_0_632, List.forall_mem_cons.2 ⟨subd14_0_633, List.forall_mem_cons.2 ⟨subd14_0_634, List.forall_mem_cons.2 ⟨subd14_0_635, List.forall_mem_cons.2 ⟨subd14_0_636, List.forall_mem_cons.2 ⟨subd14_0_637, List.forall_mem_cons.2 ⟨subd14_0_638, List.forall_mem_cons.2 ⟨subd14_0_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_640 : subd14_0 [5, -5] = true := by decide +kernel
theorem subd14_0_641 : subd14_0 [5, -4] = true := by decide +kernel
theorem subd14_0_642 : subd14_0 [5, -3] = true := by decide +kernel
theorem subd14_0_643 : subd14_0 [5, -2] = true := by decide +kernel
theorem subd14_0_644 : subd14_0 [5, -1] = true := by decide +kernel
theorem subd14_0_645 : subd14_0 [5, 0] = true := by decide +kernel
theorem subd14_0_646 : subd14_0 [5, 1] = true := by decide +kernel
theorem subd14_0_647 : subd14_0 [5, 2] = true := by decide +kernel
theorem subd14_0_648 : subd14_0 [5, 3] = true := by decide +kernel
theorem subd14_0_649 : subd14_0 [5, 4] = true := by decide +kernel
theorem subd14_0_650 : subd14_0 [6] = true := by decide +kernel
theorem sbd14_0_20 : ∀ q ∈ blkd14_0_20, subd14_0 q = true := by
  unfold blkd14_0_20
  exact List.forall_mem_cons.2 ⟨subd14_0_640, List.forall_mem_cons.2 ⟨subd14_0_641, List.forall_mem_cons.2 ⟨subd14_0_642, List.forall_mem_cons.2 ⟨subd14_0_643, List.forall_mem_cons.2 ⟨subd14_0_644, List.forall_mem_cons.2 ⟨subd14_0_645, List.forall_mem_cons.2 ⟨subd14_0_646, List.forall_mem_cons.2 ⟨subd14_0_647, List.forall_mem_cons.2 ⟨subd14_0_648, List.forall_mem_cons.2 ⟨subd14_0_649, List.forall_mem_cons.2 ⟨subd14_0_650, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [-8] = true := by decide +kernel
theorem subd14_1_1 : subd14_1 [-7, -5] = true := by decide +kernel
theorem subd14_1_2 : subd14_1 [-7, -4] = true := by decide +kernel
theorem subd14_1_3 : subd14_1 [-7, -3] = true := by decide +kernel
theorem subd14_1_4 : subd14_1 [-7, -2] = true := by decide +kernel
theorem subd14_1_5 : subd14_1 [-7, -1] = true := by decide +kernel
theorem subd14_1_6 : subd14_1 [-7, 0] = true := by decide +kernel
theorem subd14_1_7 : subd14_1 [-7, 1] = true := by decide +kernel
theorem subd14_1_8 : subd14_1 [-7, 2] = true := by decide +kernel
theorem subd14_1_9 : subd14_1 [-7, 3] = true := by decide +kernel
theorem subd14_1_10 : subd14_1 [-6, -6] = true := by decide +kernel
theorem subd14_1_11 : subd14_1 [-6, -5] = true := by decide +kernel
theorem subd14_1_12 : subd14_1 [-6, -4] = true := by decide +kernel
theorem subd14_1_13 : subd14_1 [-6, -3] = true := by decide +kernel
theorem subd14_1_14 : subd14_1 [-6, -2] = true := by decide +kernel
theorem subd14_1_15 : subd14_1 [-6, -1] = true := by decide +kernel
theorem subd14_1_16 : subd14_1 [-6, 0] = true := by decide +kernel
theorem subd14_1_17 : subd14_1 [-6, 1] = true := by decide +kernel
theorem subd14_1_18 : subd14_1 [-6, 2] = true := by decide +kernel
theorem subd14_1_19 : subd14_1 [-6, 3] = true := by decide +kernel
theorem subd14_1_20 : subd14_1 [-6, 4] = true := by decide +kernel
theorem subd14_1_21 : subd14_1 [-6, 5] = true := by decide +kernel
theorem subd14_1_22 : subd14_1 [-5, -7] = true := by decide +kernel
theorem subd14_1_23 : subd14_1 [-5, -6] = true := by decide +kernel
theorem subd14_1_24 : subd14_1 [-5, -5] = true := by decide +kernel
theorem subd14_1_25 : subd14_1 [-5, -4] = true := by decide +kernel
theorem subd14_1_26 : subd14_1 [-5, -3] = true := by decide +kernel
theorem subd14_1_27 : subd14_1 [-5, -2] = true := by decide +kernel
theorem subd14_1_28 : subd14_1 [-5, -1] = true := by decide +kernel
theorem subd14_1_29 : subd14_1 [-5, 0] = true := by decide +kernel
theorem subd14_1_30 : subd14_1 [-5, 1] = true := by decide +kernel
theorem subd14_1_31 : subd14_1 [-5, 2] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_cons.2 ⟨subd14_1_1, List.forall_mem_cons.2 ⟨subd14_1_2, List.forall_mem_cons.2 ⟨subd14_1_3, List.forall_mem_cons.2 ⟨subd14_1_4, List.forall_mem_cons.2 ⟨subd14_1_5, List.forall_mem_cons.2 ⟨subd14_1_6, List.forall_mem_cons.2 ⟨subd14_1_7, List.forall_mem_cons.2 ⟨subd14_1_8, List.forall_mem_cons.2 ⟨subd14_1_9, List.forall_mem_cons.2 ⟨subd14_1_10, List.forall_mem_cons.2 ⟨subd14_1_11, List.forall_mem_cons.2 ⟨subd14_1_12, List.forall_mem_cons.2 ⟨subd14_1_13, List.forall_mem_cons.2 ⟨subd14_1_14, List.forall_mem_cons.2 ⟨subd14_1_15, List.forall_mem_cons.2 ⟨subd14_1_16, List.forall_mem_cons.2 ⟨subd14_1_17, List.forall_mem_cons.2 ⟨subd14_1_18, List.forall_mem_cons.2 ⟨subd14_1_19, List.forall_mem_cons.2 ⟨subd14_1_20, List.forall_mem_cons.2 ⟨subd14_1_21, List.forall_mem_cons.2 ⟨subd14_1_22, List.forall_mem_cons.2 ⟨subd14_1_23, List.forall_mem_cons.2 ⟨subd14_1_24, List.forall_mem_cons.2 ⟨subd14_1_25, List.forall_mem_cons.2 ⟨subd14_1_26, List.forall_mem_cons.2 ⟨subd14_1_27, List.forall_mem_cons.2 ⟨subd14_1_28, List.forall_mem_cons.2 ⟨subd14_1_29, List.forall_mem_cons.2 ⟨subd14_1_30, List.forall_mem_cons.2 ⟨subd14_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
