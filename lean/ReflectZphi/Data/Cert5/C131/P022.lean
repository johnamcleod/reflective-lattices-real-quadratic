import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_1_576 : subd11_1 [2, 0, -9] = true := by decide +kernel
theorem subd11_1_577 : subd11_1 [2, 0, -8] = true := by decide +kernel
theorem subd11_1_578 : subd11_1 [2, 0, -7] = true := by decide +kernel
theorem subd11_1_579 : subd11_1 [2, 0, -6] = true := by decide +kernel
theorem subd11_1_580 : subd11_1 [2, 0, -5] = true := by decide +kernel
theorem subd11_1_581 : subd11_1 [2, 0, -4] = true := by decide +kernel
theorem subd11_1_582 : subd11_1 [2, 0, -3] = true := by decide +kernel
theorem subd11_1_583 : subd11_1 [2, 0, -2] = true := by decide +kernel
theorem subd11_1_584 : subd11_1 [2, 0, -1] = true := by decide +kernel
theorem subd11_1_585 : subd11_1 [2, 0, 0] = true := by decide +kernel
theorem subd11_1_586 : subd11_1 [2, 0, 1] = true := by decide +kernel
theorem subd11_1_587 : subd11_1 [2, 0, 2] = true := by decide +kernel
theorem subd11_1_588 : subd11_1 [2, 0, 3] = true := by decide +kernel
theorem subd11_1_589 : subd11_1 [2, 0, 4] = true := by decide +kernel
theorem subd11_1_590 : subd11_1 [2, 0, 5] = true := by decide +kernel
theorem subd11_1_591 : subd11_1 [2, 0, 6] = true := by decide +kernel
theorem subd11_1_592 : subd11_1 [2, 0, 7] = true := by decide +kernel
theorem subd11_1_593 : subd11_1 [2, 1, -8] = true := by decide +kernel
theorem subd11_1_594 : subd11_1 [2, 1, -7] = true := by decide +kernel
theorem subd11_1_595 : subd11_1 [2, 1, -6] = true := by decide +kernel
theorem subd11_1_596 : subd11_1 [2, 1, -5] = true := by decide +kernel
theorem subd11_1_597 : subd11_1 [2, 1, -4] = true := by decide +kernel
theorem subd11_1_598 : subd11_1 [2, 1, -3] = true := by decide +kernel
theorem subd11_1_599 : subd11_1 [2, 1, -2] = true := by decide +kernel
theorem subd11_1_600 : subd11_1 [2, 1, -1] = true := by decide +kernel
theorem subd11_1_601 : subd11_1 [2, 1, 0] = true := by decide +kernel
theorem subd11_1_602 : subd11_1 [2, 1, 1] = true := by decide +kernel
theorem subd11_1_603 : subd11_1 [2, 1, 2] = true := by decide +kernel
theorem subd11_1_604 : subd11_1 [2, 1, 3] = true := by decide +kernel
theorem subd11_1_605 : subd11_1 [2, 1, 4] = true := by decide +kernel
theorem subd11_1_606 : subd11_1 [2, 1, 5] = true := by decide +kernel
theorem subd11_1_607 : subd11_1 [2, 1, 6] = true := by decide +kernel
theorem sbd11_1_18 : ∀ q ∈ blkd11_1_18, subd11_1 q = true := by
  unfold blkd11_1_18
  exact List.forall_mem_cons.2 ⟨subd11_1_576, List.forall_mem_cons.2 ⟨subd11_1_577, List.forall_mem_cons.2 ⟨subd11_1_578, List.forall_mem_cons.2 ⟨subd11_1_579, List.forall_mem_cons.2 ⟨subd11_1_580, List.forall_mem_cons.2 ⟨subd11_1_581, List.forall_mem_cons.2 ⟨subd11_1_582, List.forall_mem_cons.2 ⟨subd11_1_583, List.forall_mem_cons.2 ⟨subd11_1_584, List.forall_mem_cons.2 ⟨subd11_1_585, List.forall_mem_cons.2 ⟨subd11_1_586, List.forall_mem_cons.2 ⟨subd11_1_587, List.forall_mem_cons.2 ⟨subd11_1_588, List.forall_mem_cons.2 ⟨subd11_1_589, List.forall_mem_cons.2 ⟨subd11_1_590, List.forall_mem_cons.2 ⟨subd11_1_591, List.forall_mem_cons.2 ⟨subd11_1_592, List.forall_mem_cons.2 ⟨subd11_1_593, List.forall_mem_cons.2 ⟨subd11_1_594, List.forall_mem_cons.2 ⟨subd11_1_595, List.forall_mem_cons.2 ⟨subd11_1_596, List.forall_mem_cons.2 ⟨subd11_1_597, List.forall_mem_cons.2 ⟨subd11_1_598, List.forall_mem_cons.2 ⟨subd11_1_599, List.forall_mem_cons.2 ⟨subd11_1_600, List.forall_mem_cons.2 ⟨subd11_1_601, List.forall_mem_cons.2 ⟨subd11_1_602, List.forall_mem_cons.2 ⟨subd11_1_603, List.forall_mem_cons.2 ⟨subd11_1_604, List.forall_mem_cons.2 ⟨subd11_1_605, List.forall_mem_cons.2 ⟨subd11_1_606, List.forall_mem_cons.2 ⟨subd11_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_608 : subd11_1 [2, 1, 7] = true := by decide +kernel
theorem subd11_1_609 : subd11_1 [2, 2, -7] = true := by decide +kernel
theorem subd11_1_610 : subd11_1 [2, 2, -6] = true := by decide +kernel
theorem subd11_1_611 : subd11_1 [2, 2, -5] = true := by decide +kernel
theorem subd11_1_612 : subd11_1 [2, 2, -4] = true := by decide +kernel
theorem subd11_1_613 : subd11_1 [2, 2, -3] = true := by decide +kernel
theorem subd11_1_614 : subd11_1 [2, 2, -2] = true := by decide +kernel
theorem subd11_1_615 : subd11_1 [2, 2, -1] = true := by decide +kernel
theorem subd11_1_616 : subd11_1 [2, 2, 0] = true := by decide +kernel
theorem subd11_1_617 : subd11_1 [2, 2, 1] = true := by decide +kernel
theorem subd11_1_618 : subd11_1 [2, 2, 2] = true := by decide +kernel
theorem subd11_1_619 : subd11_1 [2, 2, 3] = true := by decide +kernel
theorem subd11_1_620 : subd11_1 [2, 2, 4] = true := by decide +kernel
theorem subd11_1_621 : subd11_1 [2, 2, 5] = true := by decide +kernel
theorem subd11_1_622 : subd11_1 [2, 2, 6] = true := by decide +kernel
theorem subd11_1_623 : subd11_1 [2, 3] = true := by decide +kernel
theorem subd11_1_624 : subd11_1 [3, -5] = true := by decide +kernel
theorem subd11_1_625 : subd11_1 [3, -4] = true := by decide +kernel
theorem subd11_1_626 : subd11_1 [3, -3] = true := by decide +kernel
theorem subd11_1_627 : subd11_1 [3, -2, -8] = true := by decide +kernel
theorem subd11_1_628 : subd11_1 [3, -2, -7] = true := by decide +kernel
theorem subd11_1_629 : subd11_1 [3, -2, -6] = true := by decide +kernel
theorem subd11_1_630 : subd11_1 [3, -2, -5] = true := by decide +kernel
theorem subd11_1_631 : subd11_1 [3, -2, -4] = true := by decide +kernel
theorem subd11_1_632 : subd11_1 [3, -2, -3] = true := by decide +kernel
theorem subd11_1_633 : subd11_1 [3, -2, -2] = true := by decide +kernel
theorem subd11_1_634 : subd11_1 [3, -2, -1] = true := by decide +kernel
theorem subd11_1_635 : subd11_1 [3, -2, 0] = true := by decide +kernel
theorem subd11_1_636 : subd11_1 [3, -2, 1] = true := by decide +kernel
theorem subd11_1_637 : subd11_1 [3, -2, 2] = true := by decide +kernel
theorem subd11_1_638 : subd11_1 [3, -2, 3] = true := by decide +kernel
theorem subd11_1_639 : subd11_1 [3, -2, 4] = true := by decide +kernel
theorem sbd11_1_19 : ∀ q ∈ blkd11_1_19, subd11_1 q = true := by
  unfold blkd11_1_19
  exact List.forall_mem_cons.2 ⟨subd11_1_608, List.forall_mem_cons.2 ⟨subd11_1_609, List.forall_mem_cons.2 ⟨subd11_1_610, List.forall_mem_cons.2 ⟨subd11_1_611, List.forall_mem_cons.2 ⟨subd11_1_612, List.forall_mem_cons.2 ⟨subd11_1_613, List.forall_mem_cons.2 ⟨subd11_1_614, List.forall_mem_cons.2 ⟨subd11_1_615, List.forall_mem_cons.2 ⟨subd11_1_616, List.forall_mem_cons.2 ⟨subd11_1_617, List.forall_mem_cons.2 ⟨subd11_1_618, List.forall_mem_cons.2 ⟨subd11_1_619, List.forall_mem_cons.2 ⟨subd11_1_620, List.forall_mem_cons.2 ⟨subd11_1_621, List.forall_mem_cons.2 ⟨subd11_1_622, List.forall_mem_cons.2 ⟨subd11_1_623, List.forall_mem_cons.2 ⟨subd11_1_624, List.forall_mem_cons.2 ⟨subd11_1_625, List.forall_mem_cons.2 ⟨subd11_1_626, List.forall_mem_cons.2 ⟨subd11_1_627, List.forall_mem_cons.2 ⟨subd11_1_628, List.forall_mem_cons.2 ⟨subd11_1_629, List.forall_mem_cons.2 ⟨subd11_1_630, List.forall_mem_cons.2 ⟨subd11_1_631, List.forall_mem_cons.2 ⟨subd11_1_632, List.forall_mem_cons.2 ⟨subd11_1_633, List.forall_mem_cons.2 ⟨subd11_1_634, List.forall_mem_cons.2 ⟨subd11_1_635, List.forall_mem_cons.2 ⟨subd11_1_636, List.forall_mem_cons.2 ⟨subd11_1_637, List.forall_mem_cons.2 ⟨subd11_1_638, List.forall_mem_cons.2 ⟨subd11_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_640 : subd11_1 [3, -2, 5] = true := by decide +kernel
theorem subd11_1_641 : subd11_1 [3, -1, -8] = true := by decide +kernel
theorem subd11_1_642 : subd11_1 [3, -1, -7] = true := by decide +kernel
theorem subd11_1_643 : subd11_1 [3, -1, -6] = true := by decide +kernel
theorem subd11_1_644 : subd11_1 [3, -1, -5] = true := by decide +kernel
theorem subd11_1_645 : subd11_1 [3, -1, -4] = true := by decide +kernel
theorem subd11_1_646 : subd11_1 [3, -1, -3] = true := by decide +kernel
theorem subd11_1_647 : subd11_1 [3, -1, -2] = true := by decide +kernel
theorem subd11_1_648 : subd11_1 [3, -1, -1] = true := by decide +kernel
theorem subd11_1_649 : subd11_1 [3, -1, 0] = true := by decide +kernel
theorem subd11_1_650 : subd11_1 [3, -1, 1] = true := by decide +kernel
theorem subd11_1_651 : subd11_1 [3, -1, 2] = true := by decide +kernel
theorem subd11_1_652 : subd11_1 [3, -1, 3] = true := by decide +kernel
theorem subd11_1_653 : subd11_1 [3, -1, 4] = true := by decide +kernel
theorem subd11_1_654 : subd11_1 [3, -1, 5] = true := by decide +kernel
theorem subd11_1_655 : subd11_1 [3, 0, -8] = true := by decide +kernel
theorem subd11_1_656 : subd11_1 [3, 0, -7] = true := by decide +kernel
theorem subd11_1_657 : subd11_1 [3, 0, -6] = true := by decide +kernel
theorem subd11_1_658 : subd11_1 [3, 0, -5] = true := by decide +kernel
theorem subd11_1_659 : subd11_1 [3, 0, -4] = true := by decide +kernel
theorem subd11_1_660 : subd11_1 [3, 0, -3] = true := by decide +kernel
theorem subd11_1_661 : subd11_1 [3, 0, -2] = true := by decide +kernel
theorem subd11_1_662 : subd11_1 [3, 0, -1] = true := by decide +kernel
theorem subd11_1_663 : subd11_1 [3, 0, 0] = true := by decide +kernel
theorem subd11_1_664 : subd11_1 [3, 0, 1] = true := by decide +kernel
theorem subd11_1_665 : subd11_1 [3, 0, 2] = true := by decide +kernel
theorem subd11_1_666 : subd11_1 [3, 0, 3] = true := by decide +kernel
theorem subd11_1_667 : subd11_1 [3, 0, 4] = true := by decide +kernel
theorem subd11_1_668 : subd11_1 [3, 0, 5] = true := by decide +kernel
theorem subd11_1_669 : subd11_1 [3, 0, 6] = true := by decide +kernel
theorem subd11_1_670 : subd11_1 [3, 1] = true := by decide +kernel
theorem subd11_1_671 : subd11_1 [3, 2] = true := by decide +kernel
theorem sbd11_1_20 : ∀ q ∈ blkd11_1_20, subd11_1 q = true := by
  unfold blkd11_1_20
  exact List.forall_mem_cons.2 ⟨subd11_1_640, List.forall_mem_cons.2 ⟨subd11_1_641, List.forall_mem_cons.2 ⟨subd11_1_642, List.forall_mem_cons.2 ⟨subd11_1_643, List.forall_mem_cons.2 ⟨subd11_1_644, List.forall_mem_cons.2 ⟨subd11_1_645, List.forall_mem_cons.2 ⟨subd11_1_646, List.forall_mem_cons.2 ⟨subd11_1_647, List.forall_mem_cons.2 ⟨subd11_1_648, List.forall_mem_cons.2 ⟨subd11_1_649, List.forall_mem_cons.2 ⟨subd11_1_650, List.forall_mem_cons.2 ⟨subd11_1_651, List.forall_mem_cons.2 ⟨subd11_1_652, List.forall_mem_cons.2 ⟨subd11_1_653, List.forall_mem_cons.2 ⟨subd11_1_654, List.forall_mem_cons.2 ⟨subd11_1_655, List.forall_mem_cons.2 ⟨subd11_1_656, List.forall_mem_cons.2 ⟨subd11_1_657, List.forall_mem_cons.2 ⟨subd11_1_658, List.forall_mem_cons.2 ⟨subd11_1_659, List.forall_mem_cons.2 ⟨subd11_1_660, List.forall_mem_cons.2 ⟨subd11_1_661, List.forall_mem_cons.2 ⟨subd11_1_662, List.forall_mem_cons.2 ⟨subd11_1_663, List.forall_mem_cons.2 ⟨subd11_1_664, List.forall_mem_cons.2 ⟨subd11_1_665, List.forall_mem_cons.2 ⟨subd11_1_666, List.forall_mem_cons.2 ⟨subd11_1_667, List.forall_mem_cons.2 ⟨subd11_1_668, List.forall_mem_cons.2 ⟨subd11_1_669, List.forall_mem_cons.2 ⟨subd11_1_670, List.forall_mem_cons.2 ⟨subd11_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_672 : subd11_1 [4, -3] = true := by decide +kernel
theorem subd11_1_673 : subd11_1 [4, -2] = true := by decide +kernel
theorem subd11_1_674 : subd11_1 [4, -1] = true := by decide +kernel
theorem subd11_1_675 : subd11_1 [4, 0] = true := by decide +kernel
theorem subd11_1_676 : subd11_1 [4, 1] = true := by decide +kernel
theorem sbd11_1_21 : ∀ q ∈ blkd11_1_21, subd11_1 q = true := by
  unfold blkd11_1_21
  exact List.forall_mem_cons.2 ⟨subd11_1_672, List.forall_mem_cons.2 ⟨subd11_1_673, List.forall_mem_cons.2 ⟨subd11_1_674, List.forall_mem_cons.2 ⟨subd11_1_675, List.forall_mem_cons.2 ⟨subd11_1_676, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [-7, -3] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [-7, -2] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [-7, -1] = true := by decide +kernel
theorem subd12_0_3 : subd12_0 [-7, 0] = true := by decide +kernel
theorem subd12_0_4 : subd12_0 [-7, 1] = true := by decide +kernel
theorem subd12_0_5 : subd12_0 [-7, 2] = true := by decide +kernel
theorem subd12_0_6 : subd12_0 [-7, 3] = true := by decide +kernel
theorem subd12_0_7 : subd12_0 [-7, 4] = true := by decide +kernel
theorem subd12_0_8 : subd12_0 [-7, 5] = true := by decide +kernel
theorem subd12_0_9 : subd12_0 [-6, -5] = true := by decide +kernel
theorem subd12_0_10 : subd12_0 [-6, -4] = true := by decide +kernel
theorem subd12_0_11 : subd12_0 [-6, -3] = true := by decide +kernel
theorem subd12_0_12 : subd12_0 [-6, -2] = true := by decide +kernel
theorem subd12_0_13 : subd12_0 [-6, -1] = true := by decide +kernel
theorem subd12_0_14 : subd12_0 [-6, 0] = true := by decide +kernel
theorem subd12_0_15 : subd12_0 [-6, 1] = true := by decide +kernel
theorem subd12_0_16 : subd12_0 [-6, 2] = true := by decide +kernel
theorem subd12_0_17 : subd12_0 [-6, 3] = true := by decide +kernel
theorem subd12_0_18 : subd12_0 [-6, 4] = true := by decide +kernel
theorem subd12_0_19 : subd12_0 [-6, 5] = true := by decide +kernel
theorem subd12_0_20 : subd12_0 [-6, 6] = true := by decide +kernel
theorem subd12_0_21 : subd12_0 [-5, -6] = true := by decide +kernel
theorem subd12_0_22 : subd12_0 [-5, -5] = true := by decide +kernel
theorem subd12_0_23 : subd12_0 [-5, -4] = true := by decide +kernel
theorem subd12_0_24 : subd12_0 [-5, -3] = true := by decide +kernel
theorem subd12_0_25 : subd12_0 [-5, -2] = true := by decide +kernel
theorem subd12_0_26 : subd12_0 [-5, -1] = true := by decide +kernel
theorem subd12_0_27 : subd12_0 [-5, 0] = true := by decide +kernel
theorem subd12_0_28 : subd12_0 [-5, 1] = true := by decide +kernel
theorem subd12_0_29 : subd12_0 [-5, 2] = true := by decide +kernel
theorem subd12_0_30 : subd12_0 [-5, 3] = true := by decide +kernel
theorem subd12_0_31 : subd12_0 [-5, 4] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_cons.2 ⟨subd12_0_3, List.forall_mem_cons.2 ⟨subd12_0_4, List.forall_mem_cons.2 ⟨subd12_0_5, List.forall_mem_cons.2 ⟨subd12_0_6, List.forall_mem_cons.2 ⟨subd12_0_7, List.forall_mem_cons.2 ⟨subd12_0_8, List.forall_mem_cons.2 ⟨subd12_0_9, List.forall_mem_cons.2 ⟨subd12_0_10, List.forall_mem_cons.2 ⟨subd12_0_11, List.forall_mem_cons.2 ⟨subd12_0_12, List.forall_mem_cons.2 ⟨subd12_0_13, List.forall_mem_cons.2 ⟨subd12_0_14, List.forall_mem_cons.2 ⟨subd12_0_15, List.forall_mem_cons.2 ⟨subd12_0_16, List.forall_mem_cons.2 ⟨subd12_0_17, List.forall_mem_cons.2 ⟨subd12_0_18, List.forall_mem_cons.2 ⟨subd12_0_19, List.forall_mem_cons.2 ⟨subd12_0_20, List.forall_mem_cons.2 ⟨subd12_0_21, List.forall_mem_cons.2 ⟨subd12_0_22, List.forall_mem_cons.2 ⟨subd12_0_23, List.forall_mem_cons.2 ⟨subd12_0_24, List.forall_mem_cons.2 ⟨subd12_0_25, List.forall_mem_cons.2 ⟨subd12_0_26, List.forall_mem_cons.2 ⟨subd12_0_27, List.forall_mem_cons.2 ⟨subd12_0_28, List.forall_mem_cons.2 ⟨subd12_0_29, List.forall_mem_cons.2 ⟨subd12_0_30, List.forall_mem_cons.2 ⟨subd12_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_32 : subd12_0 [-5, 5] = true := by decide +kernel
theorem subd12_0_33 : subd12_0 [-5, 6] = true := by decide +kernel
theorem subd12_0_34 : subd12_0 [-5, 7] = true := by decide +kernel
theorem subd12_0_35 : subd12_0 [-4, -7] = true := by decide +kernel
theorem subd12_0_36 : subd12_0 [-4, -6] = true := by decide +kernel
theorem subd12_0_37 : subd12_0 [-4, -5] = true := by decide +kernel
theorem subd12_0_38 : subd12_0 [-4, -4] = true := by decide +kernel
theorem subd12_0_39 : subd12_0 [-4, -3] = true := by decide +kernel
theorem subd12_0_40 : subd12_0 [-4, -2, -8] = true := by decide +kernel
theorem subd12_0_41 : subd12_0 [-4, -2, -7] = true := by decide +kernel
theorem subd12_0_42 : subd12_0 [-4, -2, -6] = true := by decide +kernel
theorem subd12_0_43 : subd12_0 [-4, -2, -5] = true := by decide +kernel
theorem subd12_0_44 : subd12_0 [-4, -2, -4] = true := by decide +kernel
theorem subd12_0_45 : subd12_0 [-4, -2, -3] = true := by decide +kernel
theorem subd12_0_46 : subd12_0 [-4, -2, -2] = true := by decide +kernel
theorem subd12_0_47 : subd12_0 [-4, -2, -1] = true := by decide +kernel
theorem subd12_0_48 : subd12_0 [-4, -2, 0] = true := by decide +kernel
theorem subd12_0_49 : subd12_0 [-4, -2, 1] = true := by decide +kernel
theorem subd12_0_50 : subd12_0 [-4, -2, 2] = true := by decide +kernel
theorem subd12_0_51 : subd12_0 [-4, -2, 3] = true := by decide +kernel
theorem subd12_0_52 : subd12_0 [-4, -2, 4] = true := by decide +kernel
theorem subd12_0_53 : subd12_0 [-4, -2, 5] = true := by decide +kernel
theorem subd12_0_54 : subd12_0 [-4, -1, -8] = true := by decide +kernel
theorem subd12_0_55 : subd12_0 [-4, -1, -7] = true := by decide +kernel
theorem subd12_0_56 : subd12_0 [-4, -1, -6] = true := by decide +kernel
theorem subd12_0_57 : subd12_0 [-4, -1, -5] = true := by decide +kernel
theorem subd12_0_58 : subd12_0 [-4, -1, -4] = true := by decide +kernel
theorem subd12_0_59 : subd12_0 [-4, -1, -3] = true := by decide +kernel
theorem subd12_0_60 : subd12_0 [-4, -1, -2] = true := by decide +kernel
theorem subd12_0_61 : subd12_0 [-4, -1, -1] = true := by decide +kernel
theorem subd12_0_62 : subd12_0 [-4, -1, 0] = true := by decide +kernel
theorem subd12_0_63 : subd12_0 [-4, -1, 1] = true := by decide +kernel
theorem sbd12_0_1 : ∀ q ∈ blkd12_0_1, subd12_0 q = true := by
  unfold blkd12_0_1
  exact List.forall_mem_cons.2 ⟨subd12_0_32, List.forall_mem_cons.2 ⟨subd12_0_33, List.forall_mem_cons.2 ⟨subd12_0_34, List.forall_mem_cons.2 ⟨subd12_0_35, List.forall_mem_cons.2 ⟨subd12_0_36, List.forall_mem_cons.2 ⟨subd12_0_37, List.forall_mem_cons.2 ⟨subd12_0_38, List.forall_mem_cons.2 ⟨subd12_0_39, List.forall_mem_cons.2 ⟨subd12_0_40, List.forall_mem_cons.2 ⟨subd12_0_41, List.forall_mem_cons.2 ⟨subd12_0_42, List.forall_mem_cons.2 ⟨subd12_0_43, List.forall_mem_cons.2 ⟨subd12_0_44, List.forall_mem_cons.2 ⟨subd12_0_45, List.forall_mem_cons.2 ⟨subd12_0_46, List.forall_mem_cons.2 ⟨subd12_0_47, List.forall_mem_cons.2 ⟨subd12_0_48, List.forall_mem_cons.2 ⟨subd12_0_49, List.forall_mem_cons.2 ⟨subd12_0_50, List.forall_mem_cons.2 ⟨subd12_0_51, List.forall_mem_cons.2 ⟨subd12_0_52, List.forall_mem_cons.2 ⟨subd12_0_53, List.forall_mem_cons.2 ⟨subd12_0_54, List.forall_mem_cons.2 ⟨subd12_0_55, List.forall_mem_cons.2 ⟨subd12_0_56, List.forall_mem_cons.2 ⟨subd12_0_57, List.forall_mem_cons.2 ⟨subd12_0_58, List.forall_mem_cons.2 ⟨subd12_0_59, List.forall_mem_cons.2 ⟨subd12_0_60, List.forall_mem_cons.2 ⟨subd12_0_61, List.forall_mem_cons.2 ⟨subd12_0_62, List.forall_mem_cons.2 ⟨subd12_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_64 : subd12_0 [-4, -1, 2] = true := by decide +kernel
theorem subd12_0_65 : subd12_0 [-4, -1, 3] = true := by decide +kernel
theorem subd12_0_66 : subd12_0 [-4, -1, 4] = true := by decide +kernel
theorem subd12_0_67 : subd12_0 [-4, -1, 5] = true := by decide +kernel
theorem subd12_0_68 : subd12_0 [-4, -1, 6] = true := by decide +kernel
theorem subd12_0_69 : subd12_0 [-4, 0, -8] = true := by decide +kernel
theorem subd12_0_70 : subd12_0 [-4, 0, -7] = true := by decide +kernel
theorem subd12_0_71 : subd12_0 [-4, 0, -6] = true := by decide +kernel
theorem subd12_0_72 : subd12_0 [-4, 0, -5] = true := by decide +kernel
theorem subd12_0_73 : subd12_0 [-4, 0, -4] = true := by decide +kernel
theorem subd12_0_74 : subd12_0 [-4, 0, -3] = true := by decide +kernel
theorem subd12_0_75 : subd12_0 [-4, 0, -2] = true := by decide +kernel
theorem subd12_0_76 : subd12_0 [-4, 0, -1] = true := by decide +kernel
theorem subd12_0_77 : subd12_0 [-4, 0, 0] = true := by decide +kernel
theorem subd12_0_78 : subd12_0 [-4, 0, 1] = true := by decide +kernel
theorem subd12_0_79 : subd12_0 [-4, 0, 2] = true := by decide +kernel
theorem subd12_0_80 : subd12_0 [-4, 0, 3] = true := by decide +kernel
theorem subd12_0_81 : subd12_0 [-4, 0, 4] = true := by decide +kernel
theorem subd12_0_82 : subd12_0 [-4, 0, 5] = true := by decide +kernel
theorem subd12_0_83 : subd12_0 [-4, 0, 6] = true := by decide +kernel
theorem subd12_0_84 : subd12_0 [-4, 1, -7] = true := by decide +kernel
theorem subd12_0_85 : subd12_0 [-4, 1, -6] = true := by decide +kernel
theorem subd12_0_86 : subd12_0 [-4, 1, -5] = true := by decide +kernel
theorem subd12_0_87 : subd12_0 [-4, 1, -4] = true := by decide +kernel
theorem subd12_0_88 : subd12_0 [-4, 1, -3] = true := by decide +kernel
theorem subd12_0_89 : subd12_0 [-4, 1, -2] = true := by decide +kernel
theorem subd12_0_90 : subd12_0 [-4, 1, -1] = true := by decide +kernel
theorem subd12_0_91 : subd12_0 [-4, 1, 0] = true := by decide +kernel
theorem subd12_0_92 : subd12_0 [-4, 1, 1] = true := by decide +kernel
theorem subd12_0_93 : subd12_0 [-4, 1, 2] = true := by decide +kernel
theorem subd12_0_94 : subd12_0 [-4, 1, 3] = true := by decide +kernel
theorem subd12_0_95 : subd12_0 [-4, 1, 4] = true := by decide +kernel
theorem sbd12_0_2 : ∀ q ∈ blkd12_0_2, subd12_0 q = true := by
  unfold blkd12_0_2
  exact List.forall_mem_cons.2 ⟨subd12_0_64, List.forall_mem_cons.2 ⟨subd12_0_65, List.forall_mem_cons.2 ⟨subd12_0_66, List.forall_mem_cons.2 ⟨subd12_0_67, List.forall_mem_cons.2 ⟨subd12_0_68, List.forall_mem_cons.2 ⟨subd12_0_69, List.forall_mem_cons.2 ⟨subd12_0_70, List.forall_mem_cons.2 ⟨subd12_0_71, List.forall_mem_cons.2 ⟨subd12_0_72, List.forall_mem_cons.2 ⟨subd12_0_73, List.forall_mem_cons.2 ⟨subd12_0_74, List.forall_mem_cons.2 ⟨subd12_0_75, List.forall_mem_cons.2 ⟨subd12_0_76, List.forall_mem_cons.2 ⟨subd12_0_77, List.forall_mem_cons.2 ⟨subd12_0_78, List.forall_mem_cons.2 ⟨subd12_0_79, List.forall_mem_cons.2 ⟨subd12_0_80, List.forall_mem_cons.2 ⟨subd12_0_81, List.forall_mem_cons.2 ⟨subd12_0_82, List.forall_mem_cons.2 ⟨subd12_0_83, List.forall_mem_cons.2 ⟨subd12_0_84, List.forall_mem_cons.2 ⟨subd12_0_85, List.forall_mem_cons.2 ⟨subd12_0_86, List.forall_mem_cons.2 ⟨subd12_0_87, List.forall_mem_cons.2 ⟨subd12_0_88, List.forall_mem_cons.2 ⟨subd12_0_89, List.forall_mem_cons.2 ⟨subd12_0_90, List.forall_mem_cons.2 ⟨subd12_0_91, List.forall_mem_cons.2 ⟨subd12_0_92, List.forall_mem_cons.2 ⟨subd12_0_93, List.forall_mem_cons.2 ⟨subd12_0_94, List.forall_mem_cons.2 ⟨subd12_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_96 : subd12_0 [-4, 1, 5] = true := by decide +kernel
theorem subd12_0_97 : subd12_0 [-4, 1, 6] = true := by decide +kernel
theorem subd12_0_98 : subd12_0 [-4, 1, 7] = true := by decide +kernel
theorem subd12_0_99 : subd12_0 [-4, 2, -7] = true := by decide +kernel
theorem subd12_0_100 : subd12_0 [-4, 2, -6] = true := by decide +kernel
theorem subd12_0_101 : subd12_0 [-4, 2, -5] = true := by decide +kernel
theorem subd12_0_102 : subd12_0 [-4, 2, -4] = true := by decide +kernel
theorem subd12_0_103 : subd12_0 [-4, 2, -3] = true := by decide +kernel
theorem subd12_0_104 : subd12_0 [-4, 2, -2] = true := by decide +kernel
theorem subd12_0_105 : subd12_0 [-4, 2, -1] = true := by decide +kernel
theorem subd12_0_106 : subd12_0 [-4, 2, 0] = true := by decide +kernel
theorem subd12_0_107 : subd12_0 [-4, 2, 1] = true := by decide +kernel
theorem subd12_0_108 : subd12_0 [-4, 2, 2] = true := by decide +kernel
theorem subd12_0_109 : subd12_0 [-4, 2, 3] = true := by decide +kernel
theorem subd12_0_110 : subd12_0 [-4, 2, 4] = true := by decide +kernel
theorem subd12_0_111 : subd12_0 [-4, 2, 5] = true := by decide +kernel
theorem subd12_0_112 : subd12_0 [-4, 2, 6] = true := by decide +kernel
theorem subd12_0_113 : subd12_0 [-4, 2, 7] = true := by decide +kernel
theorem subd12_0_114 : subd12_0 [-4, 3, -6] = true := by decide +kernel
theorem subd12_0_115 : subd12_0 [-4, 3, -5] = true := by decide +kernel
theorem subd12_0_116 : subd12_0 [-4, 3, -4] = true := by decide +kernel
theorem subd12_0_117 : subd12_0 [-4, 3, -3] = true := by decide +kernel
theorem subd12_0_118 : subd12_0 [-4, 3, -2] = true := by decide +kernel
theorem subd12_0_119 : subd12_0 [-4, 3, -1] = true := by decide +kernel
theorem subd12_0_120 : subd12_0 [-4, 3, 0] = true := by decide +kernel
theorem subd12_0_121 : subd12_0 [-4, 3, 1] = true := by decide +kernel
theorem subd12_0_122 : subd12_0 [-4, 3, 2] = true := by decide +kernel
theorem subd12_0_123 : subd12_0 [-4, 3, 3] = true := by decide +kernel
theorem subd12_0_124 : subd12_0 [-4, 3, 4] = true := by decide +kernel
theorem subd12_0_125 : subd12_0 [-4, 3, 5] = true := by decide +kernel
theorem subd12_0_126 : subd12_0 [-4, 3, 6] = true := by decide +kernel
theorem subd12_0_127 : subd12_0 [-4, 3, 7] = true := by decide +kernel
theorem sbd12_0_3 : ∀ q ∈ blkd12_0_3, subd12_0 q = true := by
  unfold blkd12_0_3
  exact List.forall_mem_cons.2 ⟨subd12_0_96, List.forall_mem_cons.2 ⟨subd12_0_97, List.forall_mem_cons.2 ⟨subd12_0_98, List.forall_mem_cons.2 ⟨subd12_0_99, List.forall_mem_cons.2 ⟨subd12_0_100, List.forall_mem_cons.2 ⟨subd12_0_101, List.forall_mem_cons.2 ⟨subd12_0_102, List.forall_mem_cons.2 ⟨subd12_0_103, List.forall_mem_cons.2 ⟨subd12_0_104, List.forall_mem_cons.2 ⟨subd12_0_105, List.forall_mem_cons.2 ⟨subd12_0_106, List.forall_mem_cons.2 ⟨subd12_0_107, List.forall_mem_cons.2 ⟨subd12_0_108, List.forall_mem_cons.2 ⟨subd12_0_109, List.forall_mem_cons.2 ⟨subd12_0_110, List.forall_mem_cons.2 ⟨subd12_0_111, List.forall_mem_cons.2 ⟨subd12_0_112, List.forall_mem_cons.2 ⟨subd12_0_113, List.forall_mem_cons.2 ⟨subd12_0_114, List.forall_mem_cons.2 ⟨subd12_0_115, List.forall_mem_cons.2 ⟨subd12_0_116, List.forall_mem_cons.2 ⟨subd12_0_117, List.forall_mem_cons.2 ⟨subd12_0_118, List.forall_mem_cons.2 ⟨subd12_0_119, List.forall_mem_cons.2 ⟨subd12_0_120, List.forall_mem_cons.2 ⟨subd12_0_121, List.forall_mem_cons.2 ⟨subd12_0_122, List.forall_mem_cons.2 ⟨subd12_0_123, List.forall_mem_cons.2 ⟨subd12_0_124, List.forall_mem_cons.2 ⟨subd12_0_125, List.forall_mem_cons.2 ⟨subd12_0_126, List.forall_mem_cons.2 ⟨subd12_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_128 : subd12_0 [-4, 4] = true := by decide +kernel
theorem subd12_0_129 : subd12_0 [-4, 5] = true := by decide +kernel
theorem subd12_0_130 : subd12_0 [-4, 6] = true := by decide +kernel
theorem subd12_0_131 : subd12_0 [-4, 7] = true := by decide +kernel
theorem subd12_0_132 : subd12_0 [-3, -8] = true := by decide +kernel
theorem subd12_0_133 : subd12_0 [-3, -7] = true := by decide +kernel
theorem subd12_0_134 : subd12_0 [-3, -6] = true := by decide +kernel
theorem subd12_0_135 : subd12_0 [-3, -5] = true := by decide +kernel
theorem subd12_0_136 : subd12_0 [-3, -4] = true := by decide +kernel
theorem subd12_0_137 : subd12_0 [-3, -3, -9] = true := by decide +kernel
theorem subd12_0_138 : subd12_0 [-3, -3, -8] = true := by decide +kernel
theorem subd12_0_139 : subd12_0 [-3, -3, -7] = true := by decide +kernel
theorem subd12_0_140 : subd12_0 [-3, -3, -6] = true := by decide +kernel
theorem subd12_0_141 : subd12_0 [-3, -3, -5] = true := by decide +kernel
theorem subd12_0_142 : subd12_0 [-3, -3, -4] = true := by decide +kernel
theorem subd12_0_143 : subd12_0 [-3, -3, -3] = true := by decide +kernel
theorem subd12_0_144 : subd12_0 [-3, -3, -2] = true := by decide +kernel
theorem subd12_0_145 : subd12_0 [-3, -3, -1] = true := by decide +kernel
theorem subd12_0_146 : subd12_0 [-3, -3, 0] = true := by decide +kernel
theorem subd12_0_147 : subd12_0 [-3, -3, 1] = true := by decide +kernel
theorem subd12_0_148 : subd12_0 [-3, -3, 2] = true := by decide +kernel
theorem subd12_0_149 : subd12_0 [-3, -3, 3] = true := by decide +kernel
theorem subd12_0_150 : subd12_0 [-3, -3, 4] = true := by decide +kernel
theorem subd12_0_151 : subd12_0 [-3, -3, 5] = true := by decide +kernel
theorem subd12_0_152 : subd12_0 [-3, -2, -9] = true := by decide +kernel
theorem subd12_0_153 : subd12_0 [-3, -2, -8] = true := by decide +kernel
theorem subd12_0_154 : subd12_0 [-3, -2, -7] = true := by decide +kernel
theorem subd12_0_155 : subd12_0 [-3, -2, -6] = true := by decide +kernel
theorem subd12_0_156 : subd12_0 [-3, -2, -5] = true := by decide +kernel
theorem subd12_0_157 : subd12_0 [-3, -2, -4] = true := by decide +kernel
theorem subd12_0_158 : subd12_0 [-3, -2, -3] = true := by decide +kernel
theorem subd12_0_159 : subd12_0 [-3, -2, -2] = true := by decide +kernel
theorem sbd12_0_4 : ∀ q ∈ blkd12_0_4, subd12_0 q = true := by
  unfold blkd12_0_4
  exact List.forall_mem_cons.2 ⟨subd12_0_128, List.forall_mem_cons.2 ⟨subd12_0_129, List.forall_mem_cons.2 ⟨subd12_0_130, List.forall_mem_cons.2 ⟨subd12_0_131, List.forall_mem_cons.2 ⟨subd12_0_132, List.forall_mem_cons.2 ⟨subd12_0_133, List.forall_mem_cons.2 ⟨subd12_0_134, List.forall_mem_cons.2 ⟨subd12_0_135, List.forall_mem_cons.2 ⟨subd12_0_136, List.forall_mem_cons.2 ⟨subd12_0_137, List.forall_mem_cons.2 ⟨subd12_0_138, List.forall_mem_cons.2 ⟨subd12_0_139, List.forall_mem_cons.2 ⟨subd12_0_140, List.forall_mem_cons.2 ⟨subd12_0_141, List.forall_mem_cons.2 ⟨subd12_0_142, List.forall_mem_cons.2 ⟨subd12_0_143, List.forall_mem_cons.2 ⟨subd12_0_144, List.forall_mem_cons.2 ⟨subd12_0_145, List.forall_mem_cons.2 ⟨subd12_0_146, List.forall_mem_cons.2 ⟨subd12_0_147, List.forall_mem_cons.2 ⟨subd12_0_148, List.forall_mem_cons.2 ⟨subd12_0_149, List.forall_mem_cons.2 ⟨subd12_0_150, List.forall_mem_cons.2 ⟨subd12_0_151, List.forall_mem_cons.2 ⟨subd12_0_152, List.forall_mem_cons.2 ⟨subd12_0_153, List.forall_mem_cons.2 ⟨subd12_0_154, List.forall_mem_cons.2 ⟨subd12_0_155, List.forall_mem_cons.2 ⟨subd12_0_156, List.forall_mem_cons.2 ⟨subd12_0_157, List.forall_mem_cons.2 ⟨subd12_0_158, List.forall_mem_cons.2 ⟨subd12_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_160 : subd12_0 [-3, -2, -1] = true := by decide +kernel
theorem subd12_0_161 : subd12_0 [-3, -2, 0] = true := by decide +kernel
theorem subd12_0_162 : subd12_0 [-3, -2, 1] = true := by decide +kernel
theorem subd12_0_163 : subd12_0 [-3, -2, 2] = true := by decide +kernel
theorem subd12_0_164 : subd12_0 [-3, -2, 3] = true := by decide +kernel
theorem subd12_0_165 : subd12_0 [-3, -2, 4] = true := by decide +kernel
theorem subd12_0_166 : subd12_0 [-3, -2, 5] = true := by decide +kernel
theorem subd12_0_167 : subd12_0 [-3, -2, 6] = true := by decide +kernel
theorem subd12_0_168 : subd12_0 [-3, -1, -8] = true := by decide +kernel
theorem subd12_0_169 : subd12_0 [-3, -1, -7] = true := by decide +kernel
theorem subd12_0_170 : subd12_0 [-3, -1, -6] = true := by decide +kernel
theorem subd12_0_171 : subd12_0 [-3, -1, -5] = true := by decide +kernel
theorem subd12_0_172 : subd12_0 [-3, -1, -4] = true := by decide +kernel
theorem subd12_0_173 : subd12_0 [-3, -1, -3] = true := by decide +kernel
theorem subd12_0_174 : subd12_0 [-3, -1, -2] = true := by decide +kernel
theorem subd12_0_175 : subd12_0 [-3, -1, -1] = true := by decide +kernel
theorem subd12_0_176 : subd12_0 [-3, -1, 0] = true := by decide +kernel
theorem subd12_0_177 : subd12_0 [-3, -1, 1] = true := by decide +kernel
theorem subd12_0_178 : subd12_0 [-3, -1, 2] = true := by decide +kernel
theorem subd12_0_179 : subd12_0 [-3, -1, 3] = true := by decide +kernel
theorem subd12_0_180 : subd12_0 [-3, -1, 4] = true := by decide +kernel
theorem subd12_0_181 : subd12_0 [-3, -1, 5] = true := by decide +kernel
theorem subd12_0_182 : subd12_0 [-3, -1, 6] = true := by decide +kernel
theorem subd12_0_183 : subd12_0 [-3, 0, -8] = true := by decide +kernel
theorem subd12_0_184 : subd12_0 [-3, 0, -7] = true := by decide +kernel
theorem subd12_0_185 : subd12_0 [-3, 0, -6] = true := by decide +kernel
theorem subd12_0_186 : subd12_0 [-3, 0, -5] = true := by decide +kernel
theorem subd12_0_187 : subd12_0 [-3, 0, -4] = true := by decide +kernel
theorem subd12_0_188 : subd12_0 [-3, 0, -3] = true := by decide +kernel
theorem subd12_0_189 : subd12_0 [-3, 0, -2] = true := by decide +kernel
theorem subd12_0_190 : subd12_0 [-3, 0, -1] = true := by decide +kernel
theorem subd12_0_191 : subd12_0 [-3, 0, 0] = true := by decide +kernel
theorem sbd12_0_5 : ∀ q ∈ blkd12_0_5, subd12_0 q = true := by
  unfold blkd12_0_5
  exact List.forall_mem_cons.2 ⟨subd12_0_160, List.forall_mem_cons.2 ⟨subd12_0_161, List.forall_mem_cons.2 ⟨subd12_0_162, List.forall_mem_cons.2 ⟨subd12_0_163, List.forall_mem_cons.2 ⟨subd12_0_164, List.forall_mem_cons.2 ⟨subd12_0_165, List.forall_mem_cons.2 ⟨subd12_0_166, List.forall_mem_cons.2 ⟨subd12_0_167, List.forall_mem_cons.2 ⟨subd12_0_168, List.forall_mem_cons.2 ⟨subd12_0_169, List.forall_mem_cons.2 ⟨subd12_0_170, List.forall_mem_cons.2 ⟨subd12_0_171, List.forall_mem_cons.2 ⟨subd12_0_172, List.forall_mem_cons.2 ⟨subd12_0_173, List.forall_mem_cons.2 ⟨subd12_0_174, List.forall_mem_cons.2 ⟨subd12_0_175, List.forall_mem_cons.2 ⟨subd12_0_176, List.forall_mem_cons.2 ⟨subd12_0_177, List.forall_mem_cons.2 ⟨subd12_0_178, List.forall_mem_cons.2 ⟨subd12_0_179, List.forall_mem_cons.2 ⟨subd12_0_180, List.forall_mem_cons.2 ⟨subd12_0_181, List.forall_mem_cons.2 ⟨subd12_0_182, List.forall_mem_cons.2 ⟨subd12_0_183, List.forall_mem_cons.2 ⟨subd12_0_184, List.forall_mem_cons.2 ⟨subd12_0_185, List.forall_mem_cons.2 ⟨subd12_0_186, List.forall_mem_cons.2 ⟨subd12_0_187, List.forall_mem_cons.2 ⟨subd12_0_188, List.forall_mem_cons.2 ⟨subd12_0_189, List.forall_mem_cons.2 ⟨subd12_0_190, List.forall_mem_cons.2 ⟨subd12_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
