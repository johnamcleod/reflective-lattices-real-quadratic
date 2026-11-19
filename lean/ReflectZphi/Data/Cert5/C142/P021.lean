import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_2_608 : subd12_2 [2, 1, 0] = true := by decide +kernel
theorem subd12_2_609 : subd12_2 [2, 1, 1] = true := by decide +kernel
theorem subd12_2_610 : subd12_2 [2, 1, 2] = true := by decide +kernel
theorem subd12_2_611 : subd12_2 [2, 1, 3] = true := by decide +kernel
theorem subd12_2_612 : subd12_2 [2, 1, 4] = true := by decide +kernel
theorem subd12_2_613 : subd12_2 [2, 1, 5] = true := by decide +kernel
theorem subd12_2_614 : subd12_2 [2, 1, 6] = true := by decide +kernel
theorem subd12_2_615 : subd12_2 [2, 2, -9] = true := by decide +kernel
theorem subd12_2_616 : subd12_2 [2, 2, -8] = true := by decide +kernel
theorem subd12_2_617 : subd12_2 [2, 2, -7] = true := by decide +kernel
theorem subd12_2_618 : subd12_2 [2, 2, -6] = true := by decide +kernel
theorem subd12_2_619 : subd12_2 [2, 2, -5] = true := by decide +kernel
theorem subd12_2_620 : subd12_2 [2, 2, -4] = true := by decide +kernel
theorem subd12_2_621 : subd12_2 [2, 2, -3] = true := by decide +kernel
theorem subd12_2_622 : subd12_2 [2, 2, -2] = true := by decide +kernel
theorem subd12_2_623 : subd12_2 [2, 2, -1] = true := by decide +kernel
theorem subd12_2_624 : subd12_2 [2, 2, 0] = true := by decide +kernel
theorem subd12_2_625 : subd12_2 [2, 2, 1] = true := by decide +kernel
theorem subd12_2_626 : subd12_2 [2, 2, 2] = true := by decide +kernel
theorem subd12_2_627 : subd12_2 [2, 2, 3] = true := by decide +kernel
theorem subd12_2_628 : subd12_2 [2, 2, 4] = true := by decide +kernel
theorem subd12_2_629 : subd12_2 [2, 2, 5] = true := by decide +kernel
theorem subd12_2_630 : subd12_2 [2, 3] = true := by decide +kernel
theorem subd12_2_631 : subd12_2 [2, 4] = true := by decide +kernel
theorem subd12_2_632 : subd12_2 [3, -5] = true := by decide +kernel
theorem subd12_2_633 : subd12_2 [3, -4] = true := by decide +kernel
theorem subd12_2_634 : subd12_2 [3, -3] = true := by decide +kernel
theorem subd12_2_635 : subd12_2 [3, -2, -7] = true := by decide +kernel
theorem subd12_2_636 : subd12_2 [3, -2, -6] = true := by decide +kernel
theorem subd12_2_637 : subd12_2 [3, -2, -5] = true := by decide +kernel
theorem subd12_2_638 : subd12_2 [3, -2, -4] = true := by decide +kernel
theorem subd12_2_639 : subd12_2 [3, -2, -3] = true := by decide +kernel
theorem sbd12_2_19 : ∀ q ∈ blkd12_2_19, subd12_2 q = true := by
  unfold blkd12_2_19
  exact List.forall_mem_cons.2 ⟨subd12_2_608, List.forall_mem_cons.2 ⟨subd12_2_609, List.forall_mem_cons.2 ⟨subd12_2_610, List.forall_mem_cons.2 ⟨subd12_2_611, List.forall_mem_cons.2 ⟨subd12_2_612, List.forall_mem_cons.2 ⟨subd12_2_613, List.forall_mem_cons.2 ⟨subd12_2_614, List.forall_mem_cons.2 ⟨subd12_2_615, List.forall_mem_cons.2 ⟨subd12_2_616, List.forall_mem_cons.2 ⟨subd12_2_617, List.forall_mem_cons.2 ⟨subd12_2_618, List.forall_mem_cons.2 ⟨subd12_2_619, List.forall_mem_cons.2 ⟨subd12_2_620, List.forall_mem_cons.2 ⟨subd12_2_621, List.forall_mem_cons.2 ⟨subd12_2_622, List.forall_mem_cons.2 ⟨subd12_2_623, List.forall_mem_cons.2 ⟨subd12_2_624, List.forall_mem_cons.2 ⟨subd12_2_625, List.forall_mem_cons.2 ⟨subd12_2_626, List.forall_mem_cons.2 ⟨subd12_2_627, List.forall_mem_cons.2 ⟨subd12_2_628, List.forall_mem_cons.2 ⟨subd12_2_629, List.forall_mem_cons.2 ⟨subd12_2_630, List.forall_mem_cons.2 ⟨subd12_2_631, List.forall_mem_cons.2 ⟨subd12_2_632, List.forall_mem_cons.2 ⟨subd12_2_633, List.forall_mem_cons.2 ⟨subd12_2_634, List.forall_mem_cons.2 ⟨subd12_2_635, List.forall_mem_cons.2 ⟨subd12_2_636, List.forall_mem_cons.2 ⟨subd12_2_637, List.forall_mem_cons.2 ⟨subd12_2_638, List.forall_mem_cons.2 ⟨subd12_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_640 : subd12_2 [3, -2, -2] = true := by decide +kernel
theorem subd12_2_641 : subd12_2 [3, -2, -1] = true := by decide +kernel
theorem subd12_2_642 : subd12_2 [3, -2, 0] = true := by decide +kernel
theorem subd12_2_643 : subd12_2 [3, -2, 1] = true := by decide +kernel
theorem subd12_2_644 : subd12_2 [3, -2, 2] = true := by decide +kernel
theorem subd12_2_645 : subd12_2 [3, -2, 3] = true := by decide +kernel
theorem subd12_2_646 : subd12_2 [3, -2, 4] = true := by decide +kernel
theorem subd12_2_647 : subd12_2 [3, -2, 5] = true := by decide +kernel
theorem subd12_2_648 : subd12_2 [3, -2, 6] = true := by decide +kernel
theorem subd12_2_649 : subd12_2 [3, -1, -8] = true := by decide +kernel
theorem subd12_2_650 : subd12_2 [3, -1, -7] = true := by decide +kernel
theorem subd12_2_651 : subd12_2 [3, -1, -6] = true := by decide +kernel
theorem subd12_2_652 : subd12_2 [3, -1, -5] = true := by decide +kernel
theorem subd12_2_653 : subd12_2 [3, -1, -4] = true := by decide +kernel
theorem subd12_2_654 : subd12_2 [3, -1, -3] = true := by decide +kernel
theorem subd12_2_655 : subd12_2 [3, -1, -2] = true := by decide +kernel
theorem subd12_2_656 : subd12_2 [3, -1, -1] = true := by decide +kernel
theorem subd12_2_657 : subd12_2 [3, -1, 0] = true := by decide +kernel
theorem subd12_2_658 : subd12_2 [3, -1, 1] = true := by decide +kernel
theorem subd12_2_659 : subd12_2 [3, -1, 2] = true := by decide +kernel
theorem subd12_2_660 : subd12_2 [3, -1, 3] = true := by decide +kernel
theorem subd12_2_661 : subd12_2 [3, -1, 4] = true := by decide +kernel
theorem subd12_2_662 : subd12_2 [3, -1, 5] = true := by decide +kernel
theorem subd12_2_663 : subd12_2 [3, -1, 6] = true := by decide +kernel
theorem subd12_2_664 : subd12_2 [3, 0, -9] = true := by decide +kernel
theorem subd12_2_665 : subd12_2 [3, 0, -8] = true := by decide +kernel
theorem subd12_2_666 : subd12_2 [3, 0, -7] = true := by decide +kernel
theorem subd12_2_667 : subd12_2 [3, 0, -6] = true := by decide +kernel
theorem subd12_2_668 : subd12_2 [3, 0, -5] = true := by decide +kernel
theorem subd12_2_669 : subd12_2 [3, 0, -4] = true := by decide +kernel
theorem subd12_2_670 : subd12_2 [3, 0, -3] = true := by decide +kernel
theorem subd12_2_671 : subd12_2 [3, 0, -2] = true := by decide +kernel
theorem sbd12_2_20 : ∀ q ∈ blkd12_2_20, subd12_2 q = true := by
  unfold blkd12_2_20
  exact List.forall_mem_cons.2 ⟨subd12_2_640, List.forall_mem_cons.2 ⟨subd12_2_641, List.forall_mem_cons.2 ⟨subd12_2_642, List.forall_mem_cons.2 ⟨subd12_2_643, List.forall_mem_cons.2 ⟨subd12_2_644, List.forall_mem_cons.2 ⟨subd12_2_645, List.forall_mem_cons.2 ⟨subd12_2_646, List.forall_mem_cons.2 ⟨subd12_2_647, List.forall_mem_cons.2 ⟨subd12_2_648, List.forall_mem_cons.2 ⟨subd12_2_649, List.forall_mem_cons.2 ⟨subd12_2_650, List.forall_mem_cons.2 ⟨subd12_2_651, List.forall_mem_cons.2 ⟨subd12_2_652, List.forall_mem_cons.2 ⟨subd12_2_653, List.forall_mem_cons.2 ⟨subd12_2_654, List.forall_mem_cons.2 ⟨subd12_2_655, List.forall_mem_cons.2 ⟨subd12_2_656, List.forall_mem_cons.2 ⟨subd12_2_657, List.forall_mem_cons.2 ⟨subd12_2_658, List.forall_mem_cons.2 ⟨subd12_2_659, List.forall_mem_cons.2 ⟨subd12_2_660, List.forall_mem_cons.2 ⟨subd12_2_661, List.forall_mem_cons.2 ⟨subd12_2_662, List.forall_mem_cons.2 ⟨subd12_2_663, List.forall_mem_cons.2 ⟨subd12_2_664, List.forall_mem_cons.2 ⟨subd12_2_665, List.forall_mem_cons.2 ⟨subd12_2_666, List.forall_mem_cons.2 ⟨subd12_2_667, List.forall_mem_cons.2 ⟨subd12_2_668, List.forall_mem_cons.2 ⟨subd12_2_669, List.forall_mem_cons.2 ⟨subd12_2_670, List.forall_mem_cons.2 ⟨subd12_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_672 : subd12_2 [3, 0, -1] = true := by decide +kernel
theorem subd12_2_673 : subd12_2 [3, 0, 0] = true := by decide +kernel
theorem subd12_2_674 : subd12_2 [3, 0, 1] = true := by decide +kernel
theorem subd12_2_675 : subd12_2 [3, 0, 2] = true := by decide +kernel
theorem subd12_2_676 : subd12_2 [3, 0, 3] = true := by decide +kernel
theorem subd12_2_677 : subd12_2 [3, 0, 4] = true := by decide +kernel
theorem subd12_2_678 : subd12_2 [3, 0, 5] = true := by decide +kernel
theorem subd12_2_679 : subd12_2 [3, 0, 6] = true := by decide +kernel
theorem subd12_2_680 : subd12_2 [3, 1, -9] = true := by decide +kernel
theorem subd12_2_681 : subd12_2 [3, 1, -8] = true := by decide +kernel
theorem subd12_2_682 : subd12_2 [3, 1, -7] = true := by decide +kernel
theorem subd12_2_683 : subd12_2 [3, 1, -6] = true := by decide +kernel
theorem subd12_2_684 : subd12_2 [3, 1, -5] = true := by decide +kernel
theorem subd12_2_685 : subd12_2 [3, 1, -4] = true := by decide +kernel
theorem subd12_2_686 : subd12_2 [3, 1, -3] = true := by decide +kernel
theorem subd12_2_687 : subd12_2 [3, 1, -2] = true := by decide +kernel
theorem subd12_2_688 : subd12_2 [3, 1, -1] = true := by decide +kernel
theorem subd12_2_689 : subd12_2 [3, 1, 0] = true := by decide +kernel
theorem subd12_2_690 : subd12_2 [3, 1, 1] = true := by decide +kernel
theorem subd12_2_691 : subd12_2 [3, 1, 2] = true := by decide +kernel
theorem subd12_2_692 : subd12_2 [3, 1, 3] = true := by decide +kernel
theorem subd12_2_693 : subd12_2 [3, 1, 4] = true := by decide +kernel
theorem subd12_2_694 : subd12_2 [3, 1, 5] = true := by decide +kernel
theorem subd12_2_695 : subd12_2 [3, 2] = true := by decide +kernel
theorem subd12_2_696 : subd12_2 [3, 3] = true := by decide +kernel
theorem subd12_2_697 : subd12_2 [4, -4] = true := by decide +kernel
theorem subd12_2_698 : subd12_2 [4, -3] = true := by decide +kernel
theorem subd12_2_699 : subd12_2 [4, -2] = true := by decide +kernel
theorem subd12_2_700 : subd12_2 [4, -1] = true := by decide +kernel
theorem subd12_2_701 : subd12_2 [4, 0] = true := by decide +kernel
theorem subd12_2_702 : subd12_2 [4, 1] = true := by decide +kernel
theorem subd12_2_703 : subd12_2 [4, 2] = true := by decide +kernel
theorem sbd12_2_21 : ∀ q ∈ blkd12_2_21, subd12_2 q = true := by
  unfold blkd12_2_21
  exact List.forall_mem_cons.2 ⟨subd12_2_672, List.forall_mem_cons.2 ⟨subd12_2_673, List.forall_mem_cons.2 ⟨subd12_2_674, List.forall_mem_cons.2 ⟨subd12_2_675, List.forall_mem_cons.2 ⟨subd12_2_676, List.forall_mem_cons.2 ⟨subd12_2_677, List.forall_mem_cons.2 ⟨subd12_2_678, List.forall_mem_cons.2 ⟨subd12_2_679, List.forall_mem_cons.2 ⟨subd12_2_680, List.forall_mem_cons.2 ⟨subd12_2_681, List.forall_mem_cons.2 ⟨subd12_2_682, List.forall_mem_cons.2 ⟨subd12_2_683, List.forall_mem_cons.2 ⟨subd12_2_684, List.forall_mem_cons.2 ⟨subd12_2_685, List.forall_mem_cons.2 ⟨subd12_2_686, List.forall_mem_cons.2 ⟨subd12_2_687, List.forall_mem_cons.2 ⟨subd12_2_688, List.forall_mem_cons.2 ⟨subd12_2_689, List.forall_mem_cons.2 ⟨subd12_2_690, List.forall_mem_cons.2 ⟨subd12_2_691, List.forall_mem_cons.2 ⟨subd12_2_692, List.forall_mem_cons.2 ⟨subd12_2_693, List.forall_mem_cons.2 ⟨subd12_2_694, List.forall_mem_cons.2 ⟨subd12_2_695, List.forall_mem_cons.2 ⟨subd12_2_696, List.forall_mem_cons.2 ⟨subd12_2_697, List.forall_mem_cons.2 ⟨subd12_2_698, List.forall_mem_cons.2 ⟨subd12_2_699, List.forall_mem_cons.2 ⟨subd12_2_700, List.forall_mem_cons.2 ⟨subd12_2_701, List.forall_mem_cons.2 ⟨subd12_2_702, List.forall_mem_cons.2 ⟨subd12_2_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_704 : subd12_2 [5] = true := by decide +kernel
theorem sbd12_2_22 : ∀ q ∈ blkd12_2_22, subd12_2 q = true := by
  unfold blkd12_2_22
  exact List.forall_mem_cons.2 ⟨subd12_2_704, List.forall_mem_nil _⟩
theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel
theorem subd12_3_0 : subd12_3 [-2] = true := by decide +kernel
theorem subd12_3_1 : subd12_3 [-1, -3] = true := by decide +kernel
theorem subd12_3_2 : subd12_3 [-1, -2] = true := by decide +kernel
theorem subd12_3_3 : subd12_3 [-1, -1] = true := by decide +kernel
theorem subd12_3_4 : subd12_3 [-1, 0] = true := by decide +kernel
theorem subd12_3_5 : subd12_3 [-1, 1] = true := by decide +kernel
theorem subd12_3_6 : subd12_3 [-1, 2] = true := by decide +kernel
theorem subd12_3_7 : subd12_3 [0, -3] = true := by decide +kernel
theorem subd12_3_8 : subd12_3 [0, -2] = true := by decide +kernel
theorem subd12_3_9 : subd12_3 [0, -1] = true := by decide +kernel
theorem subd12_3_10 : subd12_3 [0, 0] = true := by decide +kernel
theorem subd12_3_11 : subd12_3 [0, 1] = true := by decide +kernel
theorem subd12_3_12 : subd12_3 [0, 2] = true := by decide +kernel
theorem subd12_3_13 : subd12_3 [1, -3] = true := by decide +kernel
theorem subd12_3_14 : subd12_3 [1, -2] = true := by decide +kernel
theorem subd12_3_15 : subd12_3 [1, -1] = true := by decide +kernel
theorem subd12_3_16 : subd12_3 [1, 0] = true := by decide +kernel
theorem subd12_3_17 : subd12_3 [1, 1] = true := by decide +kernel
theorem subd12_3_18 : subd12_3 [1, 2] = true := by decide +kernel
theorem subd12_3_19 : subd12_3 [2] = true := by decide +kernel
theorem sbd12_3_0 : ∀ q ∈ blkd12_3_0, subd12_3 q = true := by
  unfold blkd12_3_0
  exact List.forall_mem_cons.2 ⟨subd12_3_0, List.forall_mem_cons.2 ⟨subd12_3_1, List.forall_mem_cons.2 ⟨subd12_3_2, List.forall_mem_cons.2 ⟨subd12_3_3, List.forall_mem_cons.2 ⟨subd12_3_4, List.forall_mem_cons.2 ⟨subd12_3_5, List.forall_mem_cons.2 ⟨subd12_3_6, List.forall_mem_cons.2 ⟨subd12_3_7, List.forall_mem_cons.2 ⟨subd12_3_8, List.forall_mem_cons.2 ⟨subd12_3_9, List.forall_mem_cons.2 ⟨subd12_3_10, List.forall_mem_cons.2 ⟨subd12_3_11, List.forall_mem_cons.2 ⟨subd12_3_12, List.forall_mem_cons.2 ⟨subd12_3_13, List.forall_mem_cons.2 ⟨subd12_3_14, List.forall_mem_cons.2 ⟨subd12_3_15, List.forall_mem_cons.2 ⟨subd12_3_16, List.forall_mem_cons.2 ⟨subd12_3_17, List.forall_mem_cons.2 ⟨subd12_3_18, List.forall_mem_cons.2 ⟨subd12_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [-3] = true := by decide +kernel
theorem subd13_0_1 : subd13_0 [-2, -4] = true := by decide +kernel
theorem subd13_0_2 : subd13_0 [-2, -3] = true := by decide +kernel
theorem subd13_0_3 : subd13_0 [-2, -2] = true := by decide +kernel
theorem subd13_0_4 : subd13_0 [-2, -1] = true := by decide +kernel
theorem subd13_0_5 : subd13_0 [-2, 0] = true := by decide +kernel
theorem subd13_0_6 : subd13_0 [-2, 1] = true := by decide +kernel
theorem subd13_0_7 : subd13_0 [-2, 2] = true := by decide +kernel
theorem subd13_0_8 : subd13_0 [-1, -4] = true := by decide +kernel
theorem subd13_0_9 : subd13_0 [-1, -3] = true := by decide +kernel
theorem subd13_0_10 : subd13_0 [-1, -2] = true := by decide +kernel
theorem subd13_0_11 : subd13_0 [-1, -1] = true := by decide +kernel
theorem subd13_0_12 : subd13_0 [-1, 0] = true := by decide +kernel
theorem subd13_0_13 : subd13_0 [-1, 1] = true := by decide +kernel
theorem subd13_0_14 : subd13_0 [-1, 2] = true := by decide +kernel
theorem subd13_0_15 : subd13_0 [-1, 3] = true := by decide +kernel
theorem subd13_0_16 : subd13_0 [0, -4] = true := by decide +kernel
theorem subd13_0_17 : subd13_0 [0, -3] = true := by decide +kernel
theorem subd13_0_18 : subd13_0 [0, -2] = true := by decide +kernel
theorem subd13_0_19 : subd13_0 [0, -1] = true := by decide +kernel
theorem subd13_0_20 : subd13_0 [0, 0] = true := by decide +kernel
theorem subd13_0_21 : subd13_0 [0, 1] = true := by decide +kernel
theorem subd13_0_22 : subd13_0 [0, 2] = true := by decide +kernel
theorem subd13_0_23 : subd13_0 [0, 3] = true := by decide +kernel
theorem subd13_0_24 : subd13_0 [1, -4] = true := by decide +kernel
theorem subd13_0_25 : subd13_0 [1, -3] = true := by decide +kernel
theorem subd13_0_26 : subd13_0 [1, -2] = true := by decide +kernel
theorem subd13_0_27 : subd13_0 [1, -1] = true := by decide +kernel
theorem subd13_0_28 : subd13_0 [1, 0] = true := by decide +kernel
theorem subd13_0_29 : subd13_0 [1, 1] = true := by decide +kernel
theorem subd13_0_30 : subd13_0 [1, 2] = true := by decide +kernel
theorem subd13_0_31 : subd13_0 [1, 3] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_cons.2 ⟨subd13_0_1, List.forall_mem_cons.2 ⟨subd13_0_2, List.forall_mem_cons.2 ⟨subd13_0_3, List.forall_mem_cons.2 ⟨subd13_0_4, List.forall_mem_cons.2 ⟨subd13_0_5, List.forall_mem_cons.2 ⟨subd13_0_6, List.forall_mem_cons.2 ⟨subd13_0_7, List.forall_mem_cons.2 ⟨subd13_0_8, List.forall_mem_cons.2 ⟨subd13_0_9, List.forall_mem_cons.2 ⟨subd13_0_10, List.forall_mem_cons.2 ⟨subd13_0_11, List.forall_mem_cons.2 ⟨subd13_0_12, List.forall_mem_cons.2 ⟨subd13_0_13, List.forall_mem_cons.2 ⟨subd13_0_14, List.forall_mem_cons.2 ⟨subd13_0_15, List.forall_mem_cons.2 ⟨subd13_0_16, List.forall_mem_cons.2 ⟨subd13_0_17, List.forall_mem_cons.2 ⟨subd13_0_18, List.forall_mem_cons.2 ⟨subd13_0_19, List.forall_mem_cons.2 ⟨subd13_0_20, List.forall_mem_cons.2 ⟨subd13_0_21, List.forall_mem_cons.2 ⟨subd13_0_22, List.forall_mem_cons.2 ⟨subd13_0_23, List.forall_mem_cons.2 ⟨subd13_0_24, List.forall_mem_cons.2 ⟨subd13_0_25, List.forall_mem_cons.2 ⟨subd13_0_26, List.forall_mem_cons.2 ⟨subd13_0_27, List.forall_mem_cons.2 ⟨subd13_0_28, List.forall_mem_cons.2 ⟨subd13_0_29, List.forall_mem_cons.2 ⟨subd13_0_30, List.forall_mem_cons.2 ⟨subd13_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_32 : subd13_0 [2, -3] = true := by decide +kernel
theorem subd13_0_33 : subd13_0 [2, -2] = true := by decide +kernel
theorem subd13_0_34 : subd13_0 [2, -1] = true := by decide +kernel
theorem subd13_0_35 : subd13_0 [2, 0] = true := by decide +kernel
theorem subd13_0_36 : subd13_0 [2, 1] = true := by decide +kernel
theorem subd13_0_37 : subd13_0 [2, 2] = true := by decide +kernel
theorem subd13_0_38 : subd13_0 [2, 3] = true := by decide +kernel
theorem subd13_0_39 : subd13_0 [3] = true := by decide +kernel
theorem sbd13_0_1 : ∀ q ∈ blkd13_0_1, subd13_0 q = true := by
  unfold blkd13_0_1
  exact List.forall_mem_cons.2 ⟨subd13_0_32, List.forall_mem_cons.2 ⟨subd13_0_33, List.forall_mem_cons.2 ⟨subd13_0_34, List.forall_mem_cons.2 ⟨subd13_0_35, List.forall_mem_cons.2 ⟨subd13_0_36, List.forall_mem_cons.2 ⟨subd13_0_37, List.forall_mem_cons.2 ⟨subd13_0_38, List.forall_mem_cons.2 ⟨subd13_0_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C142
