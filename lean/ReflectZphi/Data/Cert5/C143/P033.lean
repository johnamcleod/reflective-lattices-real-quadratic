import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_1_608 : subd15_1 [2, -3, -3] = true := by decide +kernel
theorem subd15_1_609 : subd15_1 [2, -3, -2] = true := by decide +kernel
theorem subd15_1_610 : subd15_1 [2, -3, -1] = true := by decide +kernel
theorem subd15_1_611 : subd15_1 [2, -3, 0] = true := by decide +kernel
theorem subd15_1_612 : subd15_1 [2, -3, 1] = true := by decide +kernel
theorem subd15_1_613 : subd15_1 [2, -3, 2] = true := by decide +kernel
theorem subd15_1_614 : subd15_1 [2, -3, 3] = true := by decide +kernel
theorem subd15_1_615 : subd15_1 [2, -3, 4] = true := by decide +kernel
theorem subd15_1_616 : subd15_1 [2, -3, 5] = true := by decide +kernel
theorem subd15_1_617 : subd15_1 [2, -3, 6] = true := by decide +kernel
theorem subd15_1_618 : subd15_1 [2, -3, 7] = true := by decide +kernel
theorem subd15_1_619 : subd15_1 [2, -2, -8] = true := by decide +kernel
theorem subd15_1_620 : subd15_1 [2, -2, -7] = true := by decide +kernel
theorem subd15_1_621 : subd15_1 [2, -2, -6] = true := by decide +kernel
theorem subd15_1_622 : subd15_1 [2, -2, -5] = true := by decide +kernel
theorem subd15_1_623 : subd15_1 [2, -2, -4] = true := by decide +kernel
theorem subd15_1_624 : subd15_1 [2, -2, -3] = true := by decide +kernel
theorem subd15_1_625 : subd15_1 [2, -2, -2] = true := by decide +kernel
theorem subd15_1_626 : subd15_1 [2, -2, -1] = true := by decide +kernel
theorem subd15_1_627 : subd15_1 [2, -2, 0] = true := by decide +kernel
theorem subd15_1_628 : subd15_1 [2, -2, 1] = true := by decide +kernel
theorem subd15_1_629 : subd15_1 [2, -2, 2] = true := by decide +kernel
theorem subd15_1_630 : subd15_1 [2, -2, 3] = true := by decide +kernel
theorem subd15_1_631 : subd15_1 [2, -2, 4] = true := by decide +kernel
theorem subd15_1_632 : subd15_1 [2, -2, 5] = true := by decide +kernel
theorem subd15_1_633 : subd15_1 [2, -2, 6] = true := by decide +kernel
theorem subd15_1_634 : subd15_1 [2, -2, 7] = true := by decide +kernel
theorem subd15_1_635 : subd15_1 [2, -1, -9] = true := by decide +kernel
theorem subd15_1_636 : subd15_1 [2, -1, -8] = true := by decide +kernel
theorem subd15_1_637 : subd15_1 [2, -1, -7] = true := by decide +kernel
theorem subd15_1_638 : subd15_1 [2, -1, -6] = true := by decide +kernel
theorem subd15_1_639 : subd15_1 [2, -1, -5] = true := by decide +kernel
theorem sbd15_1_19 : ∀ q ∈ blkd15_1_19, subd15_1 q = true := by
  unfold blkd15_1_19
  exact List.forall_mem_cons.2 ⟨subd15_1_608, List.forall_mem_cons.2 ⟨subd15_1_609, List.forall_mem_cons.2 ⟨subd15_1_610, List.forall_mem_cons.2 ⟨subd15_1_611, List.forall_mem_cons.2 ⟨subd15_1_612, List.forall_mem_cons.2 ⟨subd15_1_613, List.forall_mem_cons.2 ⟨subd15_1_614, List.forall_mem_cons.2 ⟨subd15_1_615, List.forall_mem_cons.2 ⟨subd15_1_616, List.forall_mem_cons.2 ⟨subd15_1_617, List.forall_mem_cons.2 ⟨subd15_1_618, List.forall_mem_cons.2 ⟨subd15_1_619, List.forall_mem_cons.2 ⟨subd15_1_620, List.forall_mem_cons.2 ⟨subd15_1_621, List.forall_mem_cons.2 ⟨subd15_1_622, List.forall_mem_cons.2 ⟨subd15_1_623, List.forall_mem_cons.2 ⟨subd15_1_624, List.forall_mem_cons.2 ⟨subd15_1_625, List.forall_mem_cons.2 ⟨subd15_1_626, List.forall_mem_cons.2 ⟨subd15_1_627, List.forall_mem_cons.2 ⟨subd15_1_628, List.forall_mem_cons.2 ⟨subd15_1_629, List.forall_mem_cons.2 ⟨subd15_1_630, List.forall_mem_cons.2 ⟨subd15_1_631, List.forall_mem_cons.2 ⟨subd15_1_632, List.forall_mem_cons.2 ⟨subd15_1_633, List.forall_mem_cons.2 ⟨subd15_1_634, List.forall_mem_cons.2 ⟨subd15_1_635, List.forall_mem_cons.2 ⟨subd15_1_636, List.forall_mem_cons.2 ⟨subd15_1_637, List.forall_mem_cons.2 ⟨subd15_1_638, List.forall_mem_cons.2 ⟨subd15_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_640 : subd15_1 [2, -1, -4] = true := by decide +kernel
theorem subd15_1_641 : subd15_1 [2, -1, -3] = true := by decide +kernel
theorem subd15_1_642 : subd15_1 [2, -1, -2] = true := by decide +kernel
theorem subd15_1_643 : subd15_1 [2, -1, -1] = true := by decide +kernel
theorem subd15_1_644 : subd15_1 [2, -1, 0] = true := by decide +kernel
theorem subd15_1_645 : subd15_1 [2, -1, 1] = true := by decide +kernel
theorem subd15_1_646 : subd15_1 [2, -1, 2] = true := by decide +kernel
theorem subd15_1_647 : subd15_1 [2, -1, 3] = true := by decide +kernel
theorem subd15_1_648 : subd15_1 [2, -1, 4] = true := by decide +kernel
theorem subd15_1_649 : subd15_1 [2, -1, 5] = true := by decide +kernel
theorem subd15_1_650 : subd15_1 [2, -1, 6] = true := by decide +kernel
theorem subd15_1_651 : subd15_1 [2, -1, 7] = true := by decide +kernel
theorem subd15_1_652 : subd15_1 [2, 0, -9] = true := by decide +kernel
theorem subd15_1_653 : subd15_1 [2, 0, -8] = true := by decide +kernel
theorem subd15_1_654 : subd15_1 [2, 0, -7] = true := by decide +kernel
theorem subd15_1_655 : subd15_1 [2, 0, -6] = true := by decide +kernel
theorem subd15_1_656 : subd15_1 [2, 0, -5] = true := by decide +kernel
theorem subd15_1_657 : subd15_1 [2, 0, -4] = true := by decide +kernel
theorem subd15_1_658 : subd15_1 [2, 0, -3] = true := by decide +kernel
theorem subd15_1_659 : subd15_1 [2, 0, -2] = true := by decide +kernel
theorem subd15_1_660 : subd15_1 [2, 0, -1] = true := by decide +kernel
theorem subd15_1_661 : subd15_1 [2, 0, 0] = true := by decide +kernel
theorem subd15_1_662 : subd15_1 [2, 0, 1] = true := by decide +kernel
theorem subd15_1_663 : subd15_1 [2, 0, 2] = true := by decide +kernel
theorem subd15_1_664 : subd15_1 [2, 0, 3] = true := by decide +kernel
theorem subd15_1_665 : subd15_1 [2, 0, 4] = true := by decide +kernel
theorem subd15_1_666 : subd15_1 [2, 0, 5] = true := by decide +kernel
theorem subd15_1_667 : subd15_1 [2, 0, 6] = true := by decide +kernel
theorem subd15_1_668 : subd15_1 [2, 1, -9] = true := by decide +kernel
theorem subd15_1_669 : subd15_1 [2, 1, -8] = true := by decide +kernel
theorem subd15_1_670 : subd15_1 [2, 1, -7] = true := by decide +kernel
theorem subd15_1_671 : subd15_1 [2, 1, -6] = true := by decide +kernel
theorem sbd15_1_20 : ∀ q ∈ blkd15_1_20, subd15_1 q = true := by
  unfold blkd15_1_20
  exact List.forall_mem_cons.2 ⟨subd15_1_640, List.forall_mem_cons.2 ⟨subd15_1_641, List.forall_mem_cons.2 ⟨subd15_1_642, List.forall_mem_cons.2 ⟨subd15_1_643, List.forall_mem_cons.2 ⟨subd15_1_644, List.forall_mem_cons.2 ⟨subd15_1_645, List.forall_mem_cons.2 ⟨subd15_1_646, List.forall_mem_cons.2 ⟨subd15_1_647, List.forall_mem_cons.2 ⟨subd15_1_648, List.forall_mem_cons.2 ⟨subd15_1_649, List.forall_mem_cons.2 ⟨subd15_1_650, List.forall_mem_cons.2 ⟨subd15_1_651, List.forall_mem_cons.2 ⟨subd15_1_652, List.forall_mem_cons.2 ⟨subd15_1_653, List.forall_mem_cons.2 ⟨subd15_1_654, List.forall_mem_cons.2 ⟨subd15_1_655, List.forall_mem_cons.2 ⟨subd15_1_656, List.forall_mem_cons.2 ⟨subd15_1_657, List.forall_mem_cons.2 ⟨subd15_1_658, List.forall_mem_cons.2 ⟨subd15_1_659, List.forall_mem_cons.2 ⟨subd15_1_660, List.forall_mem_cons.2 ⟨subd15_1_661, List.forall_mem_cons.2 ⟨subd15_1_662, List.forall_mem_cons.2 ⟨subd15_1_663, List.forall_mem_cons.2 ⟨subd15_1_664, List.forall_mem_cons.2 ⟨subd15_1_665, List.forall_mem_cons.2 ⟨subd15_1_666, List.forall_mem_cons.2 ⟨subd15_1_667, List.forall_mem_cons.2 ⟨subd15_1_668, List.forall_mem_cons.2 ⟨subd15_1_669, List.forall_mem_cons.2 ⟨subd15_1_670, List.forall_mem_cons.2 ⟨subd15_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_672 : subd15_1 [2, 1, -5] = true := by decide +kernel
theorem subd15_1_673 : subd15_1 [2, 1, -4] = true := by decide +kernel
theorem subd15_1_674 : subd15_1 [2, 1, -3] = true := by decide +kernel
theorem subd15_1_675 : subd15_1 [2, 1, -2] = true := by decide +kernel
theorem subd15_1_676 : subd15_1 [2, 1, -1] = true := by decide +kernel
theorem subd15_1_677 : subd15_1 [2, 1, 0] = true := by decide +kernel
theorem subd15_1_678 : subd15_1 [2, 1, 1] = true := by decide +kernel
theorem subd15_1_679 : subd15_1 [2, 1, 2] = true := by decide +kernel
theorem subd15_1_680 : subd15_1 [2, 1, 3] = true := by decide +kernel
theorem subd15_1_681 : subd15_1 [2, 1, 4] = true := by decide +kernel
theorem subd15_1_682 : subd15_1 [2, 1, 5] = true := by decide +kernel
theorem subd15_1_683 : subd15_1 [2, 2, -9] = true := by decide +kernel
theorem subd15_1_684 : subd15_1 [2, 2, -8] = true := by decide +kernel
theorem subd15_1_685 : subd15_1 [2, 2, -7] = true := by decide +kernel
theorem subd15_1_686 : subd15_1 [2, 2, -6] = true := by decide +kernel
theorem subd15_1_687 : subd15_1 [2, 2, -5] = true := by decide +kernel
theorem subd15_1_688 : subd15_1 [2, 2, -4] = true := by decide +kernel
theorem subd15_1_689 : subd15_1 [2, 2, -3] = true := by decide +kernel
theorem subd15_1_690 : subd15_1 [2, 2, -2] = true := by decide +kernel
theorem subd15_1_691 : subd15_1 [2, 2, -1] = true := by decide +kernel
theorem subd15_1_692 : subd15_1 [2, 2, 0] = true := by decide +kernel
theorem subd15_1_693 : subd15_1 [2, 2, 1] = true := by decide +kernel
theorem subd15_1_694 : subd15_1 [2, 2, 2] = true := by decide +kernel
theorem subd15_1_695 : subd15_1 [2, 2, 3] = true := by decide +kernel
theorem subd15_1_696 : subd15_1 [2, 2, 4] = true := by decide +kernel
theorem subd15_1_697 : subd15_1 [2, 2, 5] = true := by decide +kernel
theorem subd15_1_698 : subd15_1 [2, 3] = true := by decide +kernel
theorem subd15_1_699 : subd15_1 [2, 4] = true := by decide +kernel
theorem subd15_1_700 : subd15_1 [3, -7] = true := by decide +kernel
theorem subd15_1_701 : subd15_1 [3, -6] = true := by decide +kernel
theorem subd15_1_702 : subd15_1 [3, -5] = true := by decide +kernel
theorem subd15_1_703 : subd15_1 [3, -4] = true := by decide +kernel
theorem sbd15_1_21 : ∀ q ∈ blkd15_1_21, subd15_1 q = true := by
  unfold blkd15_1_21
  exact List.forall_mem_cons.2 ⟨subd15_1_672, List.forall_mem_cons.2 ⟨subd15_1_673, List.forall_mem_cons.2 ⟨subd15_1_674, List.forall_mem_cons.2 ⟨subd15_1_675, List.forall_mem_cons.2 ⟨subd15_1_676, List.forall_mem_cons.2 ⟨subd15_1_677, List.forall_mem_cons.2 ⟨subd15_1_678, List.forall_mem_cons.2 ⟨subd15_1_679, List.forall_mem_cons.2 ⟨subd15_1_680, List.forall_mem_cons.2 ⟨subd15_1_681, List.forall_mem_cons.2 ⟨subd15_1_682, List.forall_mem_cons.2 ⟨subd15_1_683, List.forall_mem_cons.2 ⟨subd15_1_684, List.forall_mem_cons.2 ⟨subd15_1_685, List.forall_mem_cons.2 ⟨subd15_1_686, List.forall_mem_cons.2 ⟨subd15_1_687, List.forall_mem_cons.2 ⟨subd15_1_688, List.forall_mem_cons.2 ⟨subd15_1_689, List.forall_mem_cons.2 ⟨subd15_1_690, List.forall_mem_cons.2 ⟨subd15_1_691, List.forall_mem_cons.2 ⟨subd15_1_692, List.forall_mem_cons.2 ⟨subd15_1_693, List.forall_mem_cons.2 ⟨subd15_1_694, List.forall_mem_cons.2 ⟨subd15_1_695, List.forall_mem_cons.2 ⟨subd15_1_696, List.forall_mem_cons.2 ⟨subd15_1_697, List.forall_mem_cons.2 ⟨subd15_1_698, List.forall_mem_cons.2 ⟨subd15_1_699, List.forall_mem_cons.2 ⟨subd15_1_700, List.forall_mem_cons.2 ⟨subd15_1_701, List.forall_mem_cons.2 ⟨subd15_1_702, List.forall_mem_cons.2 ⟨subd15_1_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_704 : subd15_1 [3, -3, -7] = true := by decide +kernel
theorem subd15_1_705 : subd15_1 [3, -3, -6] = true := by decide +kernel
theorem subd15_1_706 : subd15_1 [3, -3, -5] = true := by decide +kernel
theorem subd15_1_707 : subd15_1 [3, -3, -4] = true := by decide +kernel
theorem subd15_1_708 : subd15_1 [3, -3, -3] = true := by decide +kernel
theorem subd15_1_709 : subd15_1 [3, -3, -2] = true := by decide +kernel
theorem subd15_1_710 : subd15_1 [3, -3, -1] = true := by decide +kernel
theorem subd15_1_711 : subd15_1 [3, -3, 0] = true := by decide +kernel
theorem subd15_1_712 : subd15_1 [3, -3, 1] = true := by decide +kernel
theorem subd15_1_713 : subd15_1 [3, -3, 2] = true := by decide +kernel
theorem subd15_1_714 : subd15_1 [3, -3, 3] = true := by decide +kernel
theorem subd15_1_715 : subd15_1 [3, -3, 4] = true := by decide +kernel
theorem subd15_1_716 : subd15_1 [3, -3, 5] = true := by decide +kernel
theorem subd15_1_717 : subd15_1 [3, -3, 6] = true := by decide +kernel
theorem subd15_1_718 : subd15_1 [3, -2, -8] = true := by decide +kernel
theorem subd15_1_719 : subd15_1 [3, -2, -7] = true := by decide +kernel
theorem subd15_1_720 : subd15_1 [3, -2, -6] = true := by decide +kernel
theorem subd15_1_721 : subd15_1 [3, -2, -5] = true := by decide +kernel
theorem subd15_1_722 : subd15_1 [3, -2, -4] = true := by decide +kernel
theorem subd15_1_723 : subd15_1 [3, -2, -3] = true := by decide +kernel
theorem subd15_1_724 : subd15_1 [3, -2, -2] = true := by decide +kernel
theorem subd15_1_725 : subd15_1 [3, -2, -1] = true := by decide +kernel
theorem subd15_1_726 : subd15_1 [3, -2, 0] = true := by decide +kernel
theorem subd15_1_727 : subd15_1 [3, -2, 1] = true := by decide +kernel
theorem subd15_1_728 : subd15_1 [3, -2, 2] = true := by decide +kernel
theorem subd15_1_729 : subd15_1 [3, -2, 3] = true := by decide +kernel
theorem subd15_1_730 : subd15_1 [3, -2, 4] = true := by decide +kernel
theorem subd15_1_731 : subd15_1 [3, -2, 5] = true := by decide +kernel
theorem subd15_1_732 : subd15_1 [3, -2, 6] = true := by decide +kernel
theorem subd15_1_733 : subd15_1 [3, -1, -8] = true := by decide +kernel
theorem subd15_1_734 : subd15_1 [3, -1, -7] = true := by decide +kernel
theorem subd15_1_735 : subd15_1 [3, -1, -6] = true := by decide +kernel
theorem sbd15_1_22 : ∀ q ∈ blkd15_1_22, subd15_1 q = true := by
  unfold blkd15_1_22
  exact List.forall_mem_cons.2 ⟨subd15_1_704, List.forall_mem_cons.2 ⟨subd15_1_705, List.forall_mem_cons.2 ⟨subd15_1_706, List.forall_mem_cons.2 ⟨subd15_1_707, List.forall_mem_cons.2 ⟨subd15_1_708, List.forall_mem_cons.2 ⟨subd15_1_709, List.forall_mem_cons.2 ⟨subd15_1_710, List.forall_mem_cons.2 ⟨subd15_1_711, List.forall_mem_cons.2 ⟨subd15_1_712, List.forall_mem_cons.2 ⟨subd15_1_713, List.forall_mem_cons.2 ⟨subd15_1_714, List.forall_mem_cons.2 ⟨subd15_1_715, List.forall_mem_cons.2 ⟨subd15_1_716, List.forall_mem_cons.2 ⟨subd15_1_717, List.forall_mem_cons.2 ⟨subd15_1_718, List.forall_mem_cons.2 ⟨subd15_1_719, List.forall_mem_cons.2 ⟨subd15_1_720, List.forall_mem_cons.2 ⟨subd15_1_721, List.forall_mem_cons.2 ⟨subd15_1_722, List.forall_mem_cons.2 ⟨subd15_1_723, List.forall_mem_cons.2 ⟨subd15_1_724, List.forall_mem_cons.2 ⟨subd15_1_725, List.forall_mem_cons.2 ⟨subd15_1_726, List.forall_mem_cons.2 ⟨subd15_1_727, List.forall_mem_cons.2 ⟨subd15_1_728, List.forall_mem_cons.2 ⟨subd15_1_729, List.forall_mem_cons.2 ⟨subd15_1_730, List.forall_mem_cons.2 ⟨subd15_1_731, List.forall_mem_cons.2 ⟨subd15_1_732, List.forall_mem_cons.2 ⟨subd15_1_733, List.forall_mem_cons.2 ⟨subd15_1_734, List.forall_mem_cons.2 ⟨subd15_1_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_736 : subd15_1 [3, -1, -5] = true := by decide +kernel
theorem subd15_1_737 : subd15_1 [3, -1, -4] = true := by decide +kernel
theorem subd15_1_738 : subd15_1 [3, -1, -3] = true := by decide +kernel
theorem subd15_1_739 : subd15_1 [3, -1, -2] = true := by decide +kernel
theorem subd15_1_740 : subd15_1 [3, -1, -1] = true := by decide +kernel
theorem subd15_1_741 : subd15_1 [3, -1, 0] = true := by decide +kernel
theorem subd15_1_742 : subd15_1 [3, -1, 1] = true := by decide +kernel
theorem subd15_1_743 : subd15_1 [3, -1, 2] = true := by decide +kernel
theorem subd15_1_744 : subd15_1 [3, -1, 3] = true := by decide +kernel
theorem subd15_1_745 : subd15_1 [3, -1, 4] = true := by decide +kernel
theorem subd15_1_746 : subd15_1 [3, -1, 5] = true := by decide +kernel
theorem subd15_1_747 : subd15_1 [3, 0, -9] = true := by decide +kernel
theorem subd15_1_748 : subd15_1 [3, 0, -8] = true := by decide +kernel
theorem subd15_1_749 : subd15_1 [3, 0, -7] = true := by decide +kernel
theorem subd15_1_750 : subd15_1 [3, 0, -6] = true := by decide +kernel
theorem subd15_1_751 : subd15_1 [3, 0, -5] = true := by decide +kernel
theorem subd15_1_752 : subd15_1 [3, 0, -4] = true := by decide +kernel
theorem subd15_1_753 : subd15_1 [3, 0, -3] = true := by decide +kernel
theorem subd15_1_754 : subd15_1 [3, 0, -2] = true := by decide +kernel
theorem subd15_1_755 : subd15_1 [3, 0, -1] = true := by decide +kernel
theorem subd15_1_756 : subd15_1 [3, 0, 0] = true := by decide +kernel
theorem subd15_1_757 : subd15_1 [3, 0, 1] = true := by decide +kernel
theorem subd15_1_758 : subd15_1 [3, 0, 2] = true := by decide +kernel
theorem subd15_1_759 : subd15_1 [3, 0, 3] = true := by decide +kernel
theorem subd15_1_760 : subd15_1 [3, 0, 4] = true := by decide +kernel
theorem subd15_1_761 : subd15_1 [3, 0, 5] = true := by decide +kernel
theorem subd15_1_762 : subd15_1 [3, 1, -8] = true := by decide +kernel
theorem subd15_1_763 : subd15_1 [3, 1, -7] = true := by decide +kernel
theorem subd15_1_764 : subd15_1 [3, 1, -6] = true := by decide +kernel
theorem subd15_1_765 : subd15_1 [3, 1, -5] = true := by decide +kernel
theorem subd15_1_766 : subd15_1 [3, 1, -4] = true := by decide +kernel
theorem subd15_1_767 : subd15_1 [3, 1, -3] = true := by decide +kernel
theorem sbd15_1_23 : ∀ q ∈ blkd15_1_23, subd15_1 q = true := by
  unfold blkd15_1_23
  exact List.forall_mem_cons.2 ⟨subd15_1_736, List.forall_mem_cons.2 ⟨subd15_1_737, List.forall_mem_cons.2 ⟨subd15_1_738, List.forall_mem_cons.2 ⟨subd15_1_739, List.forall_mem_cons.2 ⟨subd15_1_740, List.forall_mem_cons.2 ⟨subd15_1_741, List.forall_mem_cons.2 ⟨subd15_1_742, List.forall_mem_cons.2 ⟨subd15_1_743, List.forall_mem_cons.2 ⟨subd15_1_744, List.forall_mem_cons.2 ⟨subd15_1_745, List.forall_mem_cons.2 ⟨subd15_1_746, List.forall_mem_cons.2 ⟨subd15_1_747, List.forall_mem_cons.2 ⟨subd15_1_748, List.forall_mem_cons.2 ⟨subd15_1_749, List.forall_mem_cons.2 ⟨subd15_1_750, List.forall_mem_cons.2 ⟨subd15_1_751, List.forall_mem_cons.2 ⟨subd15_1_752, List.forall_mem_cons.2 ⟨subd15_1_753, List.forall_mem_cons.2 ⟨subd15_1_754, List.forall_mem_cons.2 ⟨subd15_1_755, List.forall_mem_cons.2 ⟨subd15_1_756, List.forall_mem_cons.2 ⟨subd15_1_757, List.forall_mem_cons.2 ⟨subd15_1_758, List.forall_mem_cons.2 ⟨subd15_1_759, List.forall_mem_cons.2 ⟨subd15_1_760, List.forall_mem_cons.2 ⟨subd15_1_761, List.forall_mem_cons.2 ⟨subd15_1_762, List.forall_mem_cons.2 ⟨subd15_1_763, List.forall_mem_cons.2 ⟨subd15_1_764, List.forall_mem_cons.2 ⟨subd15_1_765, List.forall_mem_cons.2 ⟨subd15_1_766, List.forall_mem_cons.2 ⟨subd15_1_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_768 : subd15_1 [3, 1, -2] = true := by decide +kernel
theorem subd15_1_769 : subd15_1 [3, 1, -1] = true := by decide +kernel
theorem subd15_1_770 : subd15_1 [3, 1, 0] = true := by decide +kernel
theorem subd15_1_771 : subd15_1 [3, 1, 1] = true := by decide +kernel
theorem subd15_1_772 : subd15_1 [3, 1, 2] = true := by decide +kernel
theorem subd15_1_773 : subd15_1 [3, 1, 3] = true := by decide +kernel
theorem subd15_1_774 : subd15_1 [3, 1, 4] = true := by decide +kernel
theorem subd15_1_775 : subd15_1 [3, 2] = true := by decide +kernel
theorem subd15_1_776 : subd15_1 [3, 3] = true := by decide +kernel
theorem subd15_1_777 : subd15_1 [3, 4] = true := by decide +kernel
theorem subd15_1_778 : subd15_1 [4, -6] = true := by decide +kernel
theorem subd15_1_779 : subd15_1 [4, -5] = true := by decide +kernel
theorem subd15_1_780 : subd15_1 [4, -4] = true := by decide +kernel
theorem subd15_1_781 : subd15_1 [4, -3] = true := by decide +kernel
theorem subd15_1_782 : subd15_1 [4, -2] = true := by decide +kernel
theorem subd15_1_783 : subd15_1 [4, -1] = true := by decide +kernel
theorem subd15_1_784 : subd15_1 [4, 0] = true := by decide +kernel
theorem subd15_1_785 : subd15_1 [4, 1] = true := by decide +kernel
theorem subd15_1_786 : subd15_1 [4, 2] = true := by decide +kernel
theorem subd15_1_787 : subd15_1 [5, -5] = true := by decide +kernel
theorem subd15_1_788 : subd15_1 [5, -4] = true := by decide +kernel
theorem subd15_1_789 : subd15_1 [5, -3] = true := by decide +kernel
theorem subd15_1_790 : subd15_1 [5, -2] = true := by decide +kernel
theorem subd15_1_791 : subd15_1 [5, -1] = true := by decide +kernel
theorem subd15_1_792 : subd15_1 [5, 0] = true := by decide +kernel
theorem sbd15_1_24 : ∀ q ∈ blkd15_1_24, subd15_1 q = true := by
  unfold blkd15_1_24
  exact List.forall_mem_cons.2 ⟨subd15_1_768, List.forall_mem_cons.2 ⟨subd15_1_769, List.forall_mem_cons.2 ⟨subd15_1_770, List.forall_mem_cons.2 ⟨subd15_1_771, List.forall_mem_cons.2 ⟨subd15_1_772, List.forall_mem_cons.2 ⟨subd15_1_773, List.forall_mem_cons.2 ⟨subd15_1_774, List.forall_mem_cons.2 ⟨subd15_1_775, List.forall_mem_cons.2 ⟨subd15_1_776, List.forall_mem_cons.2 ⟨subd15_1_777, List.forall_mem_cons.2 ⟨subd15_1_778, List.forall_mem_cons.2 ⟨subd15_1_779, List.forall_mem_cons.2 ⟨subd15_1_780, List.forall_mem_cons.2 ⟨subd15_1_781, List.forall_mem_cons.2 ⟨subd15_1_782, List.forall_mem_cons.2 ⟨subd15_1_783, List.forall_mem_cons.2 ⟨subd15_1_784, List.forall_mem_cons.2 ⟨subd15_1_785, List.forall_mem_cons.2 ⟨subd15_1_786, List.forall_mem_cons.2 ⟨subd15_1_787, List.forall_mem_cons.2 ⟨subd15_1_788, List.forall_mem_cons.2 ⟨subd15_1_789, List.forall_mem_cons.2 ⟨subd15_1_790, List.forall_mem_cons.2 ⟨subd15_1_791, List.forall_mem_cons.2 ⟨subd15_1_792, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_2 : ldCheck G d15_2.U d15_2.ms ldd15_2 = true := by decide +kernel
theorem pre_okd15_2 : subPre G cell15 d15_2 = true := by decide +kernel
theorem subd15_2_0 : subd15_2 [-4] = true := by decide +kernel
theorem subd15_2_1 : subd15_2 [-3, -4] = true := by decide +kernel
theorem subd15_2_2 : subd15_2 [-3, -3] = true := by decide +kernel
theorem subd15_2_3 : subd15_2 [-3, -2] = true := by decide +kernel
theorem subd15_2_4 : subd15_2 [-3, -1, -6] = true := by decide +kernel
theorem subd15_2_5 : subd15_2 [-3, -1, -5] = true := by decide +kernel
theorem subd15_2_6 : subd15_2 [-3, -1, -4] = true := by decide +kernel
theorem subd15_2_7 : subd15_2 [-3, -1, -3] = true := by decide +kernel
theorem subd15_2_8 : subd15_2 [-3, -1, -2] = true := by decide +kernel
theorem subd15_2_9 : subd15_2 [-3, -1, -1] = true := by decide +kernel
theorem subd15_2_10 : subd15_2 [-3, -1, 0] = true := by decide +kernel
theorem subd15_2_11 : subd15_2 [-3, -1, 1] = true := by decide +kernel
theorem subd15_2_12 : subd15_2 [-3, -1, 2] = true := by decide +kernel
theorem subd15_2_13 : subd15_2 [-3, -1, 3] = true := by decide +kernel
theorem subd15_2_14 : subd15_2 [-3, -1, 4] = true := by decide +kernel
theorem subd15_2_15 : subd15_2 [-3, -1, 5] = true := by decide +kernel
theorem subd15_2_16 : subd15_2 [-3, -1, 6] = true := by decide +kernel
theorem subd15_2_17 : subd15_2 [-3, -1, 7] = true := by decide +kernel
theorem subd15_2_18 : subd15_2 [-3, 0, -6] = true := by decide +kernel
theorem subd15_2_19 : subd15_2 [-3, 0, -5] = true := by decide +kernel
theorem subd15_2_20 : subd15_2 [-3, 0, -4] = true := by decide +kernel
theorem subd15_2_21 : subd15_2 [-3, 0, -3] = true := by decide +kernel
theorem subd15_2_22 : subd15_2 [-3, 0, -2] = true := by decide +kernel
theorem subd15_2_23 : subd15_2 [-3, 0, -1] = true := by decide +kernel
theorem subd15_2_24 : subd15_2 [-3, 0, 0] = true := by decide +kernel
theorem subd15_2_25 : subd15_2 [-3, 0, 1] = true := by decide +kernel
theorem subd15_2_26 : subd15_2 [-3, 0, 2] = true := by decide +kernel
theorem subd15_2_27 : subd15_2 [-3, 0, 3] = true := by decide +kernel
theorem subd15_2_28 : subd15_2 [-3, 0, 4] = true := by decide +kernel
theorem subd15_2_29 : subd15_2 [-3, 0, 5] = true := by decide +kernel
theorem subd15_2_30 : subd15_2 [-3, 0, 6] = true := by decide +kernel
theorem subd15_2_31 : subd15_2 [-3, 0, 7] = true := by decide +kernel
theorem sbd15_2_0 : ∀ q ∈ blkd15_2_0, subd15_2 q = true := by
  unfold blkd15_2_0
  exact List.forall_mem_cons.2 ⟨subd15_2_0, List.forall_mem_cons.2 ⟨subd15_2_1, List.forall_mem_cons.2 ⟨subd15_2_2, List.forall_mem_cons.2 ⟨subd15_2_3, List.forall_mem_cons.2 ⟨subd15_2_4, List.forall_mem_cons.2 ⟨subd15_2_5, List.forall_mem_cons.2 ⟨subd15_2_6, List.forall_mem_cons.2 ⟨subd15_2_7, List.forall_mem_cons.2 ⟨subd15_2_8, List.forall_mem_cons.2 ⟨subd15_2_9, List.forall_mem_cons.2 ⟨subd15_2_10, List.forall_mem_cons.2 ⟨subd15_2_11, List.forall_mem_cons.2 ⟨subd15_2_12, List.forall_mem_cons.2 ⟨subd15_2_13, List.forall_mem_cons.2 ⟨subd15_2_14, List.forall_mem_cons.2 ⟨subd15_2_15, List.forall_mem_cons.2 ⟨subd15_2_16, List.forall_mem_cons.2 ⟨subd15_2_17, List.forall_mem_cons.2 ⟨subd15_2_18, List.forall_mem_cons.2 ⟨subd15_2_19, List.forall_mem_cons.2 ⟨subd15_2_20, List.forall_mem_cons.2 ⟨subd15_2_21, List.forall_mem_cons.2 ⟨subd15_2_22, List.forall_mem_cons.2 ⟨subd15_2_23, List.forall_mem_cons.2 ⟨subd15_2_24, List.forall_mem_cons.2 ⟨subd15_2_25, List.forall_mem_cons.2 ⟨subd15_2_26, List.forall_mem_cons.2 ⟨subd15_2_27, List.forall_mem_cons.2 ⟨subd15_2_28, List.forall_mem_cons.2 ⟨subd15_2_29, List.forall_mem_cons.2 ⟨subd15_2_30, List.forall_mem_cons.2 ⟨subd15_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_32 : subd15_2 [-3, 1] = true := by decide +kernel
theorem subd15_2_33 : subd15_2 [-3, 2] = true := by decide +kernel
theorem subd15_2_34 : subd15_2 [-2, -5] = true := by decide +kernel
theorem subd15_2_35 : subd15_2 [-2, -4] = true := by decide +kernel
theorem subd15_2_36 : subd15_2 [-2, -3, -7] = true := by decide +kernel
theorem subd15_2_37 : subd15_2 [-2, -3, -6] = true := by decide +kernel
theorem subd15_2_38 : subd15_2 [-2, -3, -5] = true := by decide +kernel
theorem subd15_2_39 : subd15_2 [-2, -3, -4] = true := by decide +kernel
theorem subd15_2_40 : subd15_2 [-2, -3, -3] = true := by decide +kernel
theorem subd15_2_41 : subd15_2 [-2, -3, -2] = true := by decide +kernel
theorem subd15_2_42 : subd15_2 [-2, -3, -1] = true := by decide +kernel
theorem subd15_2_43 : subd15_2 [-2, -3, 0] = true := by decide +kernel
theorem subd15_2_44 : subd15_2 [-2, -3, 1] = true := by decide +kernel
theorem subd15_2_45 : subd15_2 [-2, -3, 2] = true := by decide +kernel
theorem subd15_2_46 : subd15_2 [-2, -3, 3] = true := by decide +kernel
theorem subd15_2_47 : subd15_2 [-2, -3, 4] = true := by decide +kernel
theorem subd15_2_48 : subd15_2 [-2, -3, 5] = true := by decide +kernel
theorem subd15_2_49 : subd15_2 [-2, -3, 6] = true := by decide +kernel
theorem subd15_2_50 : subd15_2 [-2, -2, -8] = true := by decide +kernel
theorem subd15_2_51 : subd15_2 [-2, -2, -7] = true := by decide +kernel
theorem subd15_2_52 : subd15_2 [-2, -2, -6] = true := by decide +kernel
theorem subd15_2_53 : subd15_2 [-2, -2, -5] = true := by decide +kernel
theorem subd15_2_54 : subd15_2 [-2, -2, -4] = true := by decide +kernel
theorem subd15_2_55 : subd15_2 [-2, -2, -3] = true := by decide +kernel
theorem subd15_2_56 : subd15_2 [-2, -2, -2] = true := by decide +kernel
theorem subd15_2_57 : subd15_2 [-2, -2, -1] = true := by decide +kernel
theorem subd15_2_58 : subd15_2 [-2, -2, 0] = true := by decide +kernel
theorem subd15_2_59 : subd15_2 [-2, -2, 1] = true := by decide +kernel
theorem subd15_2_60 : subd15_2 [-2, -2, 2] = true := by decide +kernel
theorem subd15_2_61 : subd15_2 [-2, -2, 3] = true := by decide +kernel
theorem subd15_2_62 : subd15_2 [-2, -2, 4] = true := by decide +kernel
theorem subd15_2_63 : subd15_2 [-2, -2, 5] = true := by decide +kernel
theorem sbd15_2_1 : ∀ q ∈ blkd15_2_1, subd15_2 q = true := by
  unfold blkd15_2_1
  exact List.forall_mem_cons.2 ⟨subd15_2_32, List.forall_mem_cons.2 ⟨subd15_2_33, List.forall_mem_cons.2 ⟨subd15_2_34, List.forall_mem_cons.2 ⟨subd15_2_35, List.forall_mem_cons.2 ⟨subd15_2_36, List.forall_mem_cons.2 ⟨subd15_2_37, List.forall_mem_cons.2 ⟨subd15_2_38, List.forall_mem_cons.2 ⟨subd15_2_39, List.forall_mem_cons.2 ⟨subd15_2_40, List.forall_mem_cons.2 ⟨subd15_2_41, List.forall_mem_cons.2 ⟨subd15_2_42, List.forall_mem_cons.2 ⟨subd15_2_43, List.forall_mem_cons.2 ⟨subd15_2_44, List.forall_mem_cons.2 ⟨subd15_2_45, List.forall_mem_cons.2 ⟨subd15_2_46, List.forall_mem_cons.2 ⟨subd15_2_47, List.forall_mem_cons.2 ⟨subd15_2_48, List.forall_mem_cons.2 ⟨subd15_2_49, List.forall_mem_cons.2 ⟨subd15_2_50, List.forall_mem_cons.2 ⟨subd15_2_51, List.forall_mem_cons.2 ⟨subd15_2_52, List.forall_mem_cons.2 ⟨subd15_2_53, List.forall_mem_cons.2 ⟨subd15_2_54, List.forall_mem_cons.2 ⟨subd15_2_55, List.forall_mem_cons.2 ⟨subd15_2_56, List.forall_mem_cons.2 ⟨subd15_2_57, List.forall_mem_cons.2 ⟨subd15_2_58, List.forall_mem_cons.2 ⟨subd15_2_59, List.forall_mem_cons.2 ⟨subd15_2_60, List.forall_mem_cons.2 ⟨subd15_2_61, List.forall_mem_cons.2 ⟨subd15_2_62, List.forall_mem_cons.2 ⟨subd15_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_64 : subd15_2 [-2, -2, 6] = true := by decide +kernel
theorem subd15_2_65 : subd15_2 [-2, -2, 7] = true := by decide +kernel
theorem subd15_2_66 : subd15_2 [-2, -2, 8] = true := by decide +kernel
theorem subd15_2_67 : subd15_2 [-2, -1, -9] = true := by decide +kernel
theorem subd15_2_68 : subd15_2 [-2, -1, -8] = true := by decide +kernel
theorem subd15_2_69 : subd15_2 [-2, -1, -7] = true := by decide +kernel
theorem subd15_2_70 : subd15_2 [-2, -1, -6] = true := by decide +kernel
theorem subd15_2_71 : subd15_2 [-2, -1, -5] = true := by decide +kernel
theorem subd15_2_72 : subd15_2 [-2, -1, -4] = true := by decide +kernel
theorem subd15_2_73 : subd15_2 [-2, -1, -3] = true := by decide +kernel
theorem subd15_2_74 : subd15_2 [-2, -1, -2] = true := by decide +kernel
theorem subd15_2_75 : subd15_2 [-2, -1, -1] = true := by decide +kernel
theorem subd15_2_76 : subd15_2 [-2, -1, 0] = true := by decide +kernel
theorem subd15_2_77 : subd15_2 [-2, -1, 1] = true := by decide +kernel
theorem subd15_2_78 : subd15_2 [-2, -1, 2] = true := by decide +kernel
theorem subd15_2_79 : subd15_2 [-2, -1, 3] = true := by decide +kernel
theorem subd15_2_80 : subd15_2 [-2, -1, 4] = true := by decide +kernel
theorem subd15_2_81 : subd15_2 [-2, -1, 5] = true := by decide +kernel
theorem subd15_2_82 : subd15_2 [-2, -1, 6] = true := by decide +kernel
theorem subd15_2_83 : subd15_2 [-2, -1, 7] = true := by decide +kernel
theorem subd15_2_84 : subd15_2 [-2, -1, 8] = true := by decide +kernel
theorem subd15_2_85 : subd15_2 [-2, -1, 9] = true := by decide +kernel
theorem subd15_2_86 : subd15_2 [-2, 0, -8] = true := by decide +kernel
theorem subd15_2_87 : subd15_2 [-2, 0, -7] = true := by decide +kernel
theorem subd15_2_88 : subd15_2 [-2, 0, -6] = true := by decide +kernel
theorem subd15_2_89 : subd15_2 [-2, 0, -5] = true := by decide +kernel
theorem subd15_2_90 : subd15_2 [-2, 0, -4] = true := by decide +kernel
theorem subd15_2_91 : subd15_2 [-2, 0, -3] = true := by decide +kernel
theorem subd15_2_92 : subd15_2 [-2, 0, -2] = true := by decide +kernel
theorem subd15_2_93 : subd15_2 [-2, 0, -1] = true := by decide +kernel
theorem subd15_2_94 : subd15_2 [-2, 0, 0] = true := by decide +kernel
theorem subd15_2_95 : subd15_2 [-2, 0, 1] = true := by decide +kernel
theorem sbd15_2_2 : ∀ q ∈ blkd15_2_2, subd15_2 q = true := by
  unfold blkd15_2_2
  exact List.forall_mem_cons.2 ⟨subd15_2_64, List.forall_mem_cons.2 ⟨subd15_2_65, List.forall_mem_cons.2 ⟨subd15_2_66, List.forall_mem_cons.2 ⟨subd15_2_67, List.forall_mem_cons.2 ⟨subd15_2_68, List.forall_mem_cons.2 ⟨subd15_2_69, List.forall_mem_cons.2 ⟨subd15_2_70, List.forall_mem_cons.2 ⟨subd15_2_71, List.forall_mem_cons.2 ⟨subd15_2_72, List.forall_mem_cons.2 ⟨subd15_2_73, List.forall_mem_cons.2 ⟨subd15_2_74, List.forall_mem_cons.2 ⟨subd15_2_75, List.forall_mem_cons.2 ⟨subd15_2_76, List.forall_mem_cons.2 ⟨subd15_2_77, List.forall_mem_cons.2 ⟨subd15_2_78, List.forall_mem_cons.2 ⟨subd15_2_79, List.forall_mem_cons.2 ⟨subd15_2_80, List.forall_mem_cons.2 ⟨subd15_2_81, List.forall_mem_cons.2 ⟨subd15_2_82, List.forall_mem_cons.2 ⟨subd15_2_83, List.forall_mem_cons.2 ⟨subd15_2_84, List.forall_mem_cons.2 ⟨subd15_2_85, List.forall_mem_cons.2 ⟨subd15_2_86, List.forall_mem_cons.2 ⟨subd15_2_87, List.forall_mem_cons.2 ⟨subd15_2_88, List.forall_mem_cons.2 ⟨subd15_2_89, List.forall_mem_cons.2 ⟨subd15_2_90, List.forall_mem_cons.2 ⟨subd15_2_91, List.forall_mem_cons.2 ⟨subd15_2_92, List.forall_mem_cons.2 ⟨subd15_2_93, List.forall_mem_cons.2 ⟨subd15_2_94, List.forall_mem_cons.2 ⟨subd15_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_96 : subd15_2 [-2, 0, 2] = true := by decide +kernel
theorem subd15_2_97 : subd15_2 [-2, 0, 3] = true := by decide +kernel
theorem subd15_2_98 : subd15_2 [-2, 0, 4] = true := by decide +kernel
theorem subd15_2_99 : subd15_2 [-2, 0, 5] = true := by decide +kernel
theorem subd15_2_100 : subd15_2 [-2, 0, 6] = true := by decide +kernel
theorem subd15_2_101 : subd15_2 [-2, 0, 7] = true := by decide +kernel
theorem subd15_2_102 : subd15_2 [-2, 0, 8] = true := by decide +kernel
theorem subd15_2_103 : subd15_2 [-2, 0, 9] = true := by decide +kernel
theorem subd15_2_104 : subd15_2 [-2, 1, -7] = true := by decide +kernel
theorem subd15_2_105 : subd15_2 [-2, 1, -6] = true := by decide +kernel
theorem subd15_2_106 : subd15_2 [-2, 1, -5] = true := by decide +kernel
theorem subd15_2_107 : subd15_2 [-2, 1, -4] = true := by decide +kernel
theorem subd15_2_108 : subd15_2 [-2, 1, -3] = true := by decide +kernel
theorem subd15_2_109 : subd15_2 [-2, 1, -2] = true := by decide +kernel
theorem subd15_2_110 : subd15_2 [-2, 1, -1] = true := by decide +kernel
theorem subd15_2_111 : subd15_2 [-2, 1, 0] = true := by decide +kernel
theorem subd15_2_112 : subd15_2 [-2, 1, 1] = true := by decide +kernel
theorem subd15_2_113 : subd15_2 [-2, 1, 2] = true := by decide +kernel
theorem subd15_2_114 : subd15_2 [-2, 1, 3] = true := by decide +kernel
theorem subd15_2_115 : subd15_2 [-2, 1, 4] = true := by decide +kernel
theorem subd15_2_116 : subd15_2 [-2, 1, 5] = true := by decide +kernel
theorem subd15_2_117 : subd15_2 [-2, 1, 6] = true := by decide +kernel
theorem subd15_2_118 : subd15_2 [-2, 1, 7] = true := by decide +kernel
theorem subd15_2_119 : subd15_2 [-2, 1, 8] = true := by decide +kernel
theorem subd15_2_120 : subd15_2 [-2, 1, 9] = true := by decide +kernel
theorem subd15_2_121 : subd15_2 [-2, 2, -6] = true := by decide +kernel
theorem subd15_2_122 : subd15_2 [-2, 2, -5] = true := by decide +kernel
theorem subd15_2_123 : subd15_2 [-2, 2, -4] = true := by decide +kernel
theorem subd15_2_124 : subd15_2 [-2, 2, -3] = true := by decide +kernel
theorem subd15_2_125 : subd15_2 [-2, 2, -2] = true := by decide +kernel
theorem subd15_2_126 : subd15_2 [-2, 2, -1] = true := by decide +kernel
theorem subd15_2_127 : subd15_2 [-2, 2, 0] = true := by decide +kernel
theorem sbd15_2_3 : ∀ q ∈ blkd15_2_3, subd15_2 q = true := by
  unfold blkd15_2_3
  exact List.forall_mem_cons.2 ⟨subd15_2_96, List.forall_mem_cons.2 ⟨subd15_2_97, List.forall_mem_cons.2 ⟨subd15_2_98, List.forall_mem_cons.2 ⟨subd15_2_99, List.forall_mem_cons.2 ⟨subd15_2_100, List.forall_mem_cons.2 ⟨subd15_2_101, List.forall_mem_cons.2 ⟨subd15_2_102, List.forall_mem_cons.2 ⟨subd15_2_103, List.forall_mem_cons.2 ⟨subd15_2_104, List.forall_mem_cons.2 ⟨subd15_2_105, List.forall_mem_cons.2 ⟨subd15_2_106, List.forall_mem_cons.2 ⟨subd15_2_107, List.forall_mem_cons.2 ⟨subd15_2_108, List.forall_mem_cons.2 ⟨subd15_2_109, List.forall_mem_cons.2 ⟨subd15_2_110, List.forall_mem_cons.2 ⟨subd15_2_111, List.forall_mem_cons.2 ⟨subd15_2_112, List.forall_mem_cons.2 ⟨subd15_2_113, List.forall_mem_cons.2 ⟨subd15_2_114, List.forall_mem_cons.2 ⟨subd15_2_115, List.forall_mem_cons.2 ⟨subd15_2_116, List.forall_mem_cons.2 ⟨subd15_2_117, List.forall_mem_cons.2 ⟨subd15_2_118, List.forall_mem_cons.2 ⟨subd15_2_119, List.forall_mem_cons.2 ⟨subd15_2_120, List.forall_mem_cons.2 ⟨subd15_2_121, List.forall_mem_cons.2 ⟨subd15_2_122, List.forall_mem_cons.2 ⟨subd15_2_123, List.forall_mem_cons.2 ⟨subd15_2_124, List.forall_mem_cons.2 ⟨subd15_2_125, List.forall_mem_cons.2 ⟨subd15_2_126, List.forall_mem_cons.2 ⟨subd15_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_128 : subd15_2 [-2, 2, 1] = true := by decide +kernel
theorem subd15_2_129 : subd15_2 [-2, 2, 2] = true := by decide +kernel
theorem subd15_2_130 : subd15_2 [-2, 2, 3] = true := by decide +kernel
theorem subd15_2_131 : subd15_2 [-2, 2, 4] = true := by decide +kernel
theorem subd15_2_132 : subd15_2 [-2, 2, 5] = true := by decide +kernel
theorem subd15_2_133 : subd15_2 [-2, 2, 6] = true := by decide +kernel
theorem subd15_2_134 : subd15_2 [-2, 2, 7] = true := by decide +kernel
theorem subd15_2_135 : subd15_2 [-2, 2, 8] = true := by decide +kernel
theorem subd15_2_136 : subd15_2 [-2, 3] = true := by decide +kernel
theorem subd15_2_137 : subd15_2 [-1, -5] = true := by decide +kernel
theorem subd15_2_138 : subd15_2 [-1, -4] = true := by decide +kernel
theorem subd15_2_139 : subd15_2 [-1, -3, -8] = true := by decide +kernel
theorem subd15_2_140 : subd15_2 [-1, -3, -7] = true := by decide +kernel
theorem subd15_2_141 : subd15_2 [-1, -3, -6] = true := by decide +kernel
theorem subd15_2_142 : subd15_2 [-1, -3, -5] = true := by decide +kernel
theorem subd15_2_143 : subd15_2 [-1, -3, -4] = true := by decide +kernel
theorem subd15_2_144 : subd15_2 [-1, -3, -3] = true := by decide +kernel
theorem subd15_2_145 : subd15_2 [-1, -3, -2] = true := by decide +kernel
theorem subd15_2_146 : subd15_2 [-1, -3, -1] = true := by decide +kernel
theorem subd15_2_147 : subd15_2 [-1, -3, 0] = true := by decide +kernel
theorem subd15_2_148 : subd15_2 [-1, -3, 1] = true := by decide +kernel
theorem subd15_2_149 : subd15_2 [-1, -3, 2] = true := by decide +kernel
theorem subd15_2_150 : subd15_2 [-1, -3, 3] = true := by decide +kernel
theorem subd15_2_151 : subd15_2 [-1, -3, 4] = true := by decide +kernel
theorem subd15_2_152 : subd15_2 [-1, -3, 5] = true := by decide +kernel
theorem subd15_2_153 : subd15_2 [-1, -3, 6] = true := by decide +kernel
theorem subd15_2_154 : subd15_2 [-1, -3, 7] = true := by decide +kernel
theorem subd15_2_155 : subd15_2 [-1, -2, -9] = true := by decide +kernel
theorem subd15_2_156 : subd15_2 [-1, -2, -8] = true := by decide +kernel
theorem subd15_2_157 : subd15_2 [-1, -2, -7] = true := by decide +kernel
theorem subd15_2_158 : subd15_2 [-1, -2, -6] = true := by decide +kernel
theorem subd15_2_159 : subd15_2 [-1, -2, -5] = true := by decide +kernel
theorem sbd15_2_4 : ∀ q ∈ blkd15_2_4, subd15_2 q = true := by
  unfold blkd15_2_4
  exact List.forall_mem_cons.2 ⟨subd15_2_128, List.forall_mem_cons.2 ⟨subd15_2_129, List.forall_mem_cons.2 ⟨subd15_2_130, List.forall_mem_cons.2 ⟨subd15_2_131, List.forall_mem_cons.2 ⟨subd15_2_132, List.forall_mem_cons.2 ⟨subd15_2_133, List.forall_mem_cons.2 ⟨subd15_2_134, List.forall_mem_cons.2 ⟨subd15_2_135, List.forall_mem_cons.2 ⟨subd15_2_136, List.forall_mem_cons.2 ⟨subd15_2_137, List.forall_mem_cons.2 ⟨subd15_2_138, List.forall_mem_cons.2 ⟨subd15_2_139, List.forall_mem_cons.2 ⟨subd15_2_140, List.forall_mem_cons.2 ⟨subd15_2_141, List.forall_mem_cons.2 ⟨subd15_2_142, List.forall_mem_cons.2 ⟨subd15_2_143, List.forall_mem_cons.2 ⟨subd15_2_144, List.forall_mem_cons.2 ⟨subd15_2_145, List.forall_mem_cons.2 ⟨subd15_2_146, List.forall_mem_cons.2 ⟨subd15_2_147, List.forall_mem_cons.2 ⟨subd15_2_148, List.forall_mem_cons.2 ⟨subd15_2_149, List.forall_mem_cons.2 ⟨subd15_2_150, List.forall_mem_cons.2 ⟨subd15_2_151, List.forall_mem_cons.2 ⟨subd15_2_152, List.forall_mem_cons.2 ⟨subd15_2_153, List.forall_mem_cons.2 ⟨subd15_2_154, List.forall_mem_cons.2 ⟨subd15_2_155, List.forall_mem_cons.2 ⟨subd15_2_156, List.forall_mem_cons.2 ⟨subd15_2_157, List.forall_mem_cons.2 ⟨subd15_2_158, List.forall_mem_cons.2 ⟨subd15_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_160 : subd15_2 [-1, -2, -4] = true := by decide +kernel
theorem subd15_2_161 : subd15_2 [-1, -2, -3] = true := by decide +kernel
theorem subd15_2_162 : subd15_2 [-1, -2, -2] = true := by decide +kernel
theorem subd15_2_163 : subd15_2 [-1, -2, -1] = true := by decide +kernel
theorem subd15_2_164 : subd15_2 [-1, -2, 0] = true := by decide +kernel
theorem subd15_2_165 : subd15_2 [-1, -2, 1] = true := by decide +kernel
theorem subd15_2_166 : subd15_2 [-1, -2, 2] = true := by decide +kernel
theorem subd15_2_167 : subd15_2 [-1, -2, 3] = true := by decide +kernel
theorem subd15_2_168 : subd15_2 [-1, -2, 4] = true := by decide +kernel
theorem subd15_2_169 : subd15_2 [-1, -2, 5] = true := by decide +kernel
theorem subd15_2_170 : subd15_2 [-1, -2, 6] = true := by decide +kernel
theorem subd15_2_171 : subd15_2 [-1, -2, 7] = true := by decide +kernel
theorem subd15_2_172 : subd15_2 [-1, -2, 8] = true := by decide +kernel
theorem subd15_2_173 : subd15_2 [-1, -2, 9] = true := by decide +kernel
theorem subd15_2_174 : subd15_2 [-1, -1, -10] = true := by decide +kernel
theorem subd15_2_175 : subd15_2 [-1, -1, -9] = true := by decide +kernel
theorem subd15_2_176 : subd15_2 [-1, -1, -8] = true := by decide +kernel
theorem subd15_2_177 : subd15_2 [-1, -1, -7] = true := by decide +kernel
theorem subd15_2_178 : subd15_2 [-1, -1, -6] = true := by decide +kernel
theorem subd15_2_179 : subd15_2 [-1, -1, -5] = true := by decide +kernel
theorem subd15_2_180 : subd15_2 [-1, -1, -4] = true := by decide +kernel
theorem subd15_2_181 : subd15_2 [-1, -1, -3] = true := by decide +kernel
theorem subd15_2_182 : subd15_2 [-1, -1, -2] = true := by decide +kernel
theorem subd15_2_183 : subd15_2 [-1, -1, -1] = true := by decide +kernel
theorem subd15_2_184 : subd15_2 [-1, -1, 0] = true := by decide +kernel
theorem subd15_2_185 : subd15_2 [-1, -1, 1] = true := by decide +kernel
theorem subd15_2_186 : subd15_2 [-1, -1, 2] = true := by decide +kernel
theorem subd15_2_187 : subd15_2 [-1, -1, 3] = true := by decide +kernel
theorem subd15_2_188 : subd15_2 [-1, -1, 4] = true := by decide +kernel
theorem subd15_2_189 : subd15_2 [-1, -1, 5] = true := by decide +kernel
theorem subd15_2_190 : subd15_2 [-1, -1, 6] = true := by decide +kernel
theorem subd15_2_191 : subd15_2 [-1, -1, 7] = true := by decide +kernel
theorem sbd15_2_5 : ∀ q ∈ blkd15_2_5, subd15_2 q = true := by
  unfold blkd15_2_5
  exact List.forall_mem_cons.2 ⟨subd15_2_160, List.forall_mem_cons.2 ⟨subd15_2_161, List.forall_mem_cons.2 ⟨subd15_2_162, List.forall_mem_cons.2 ⟨subd15_2_163, List.forall_mem_cons.2 ⟨subd15_2_164, List.forall_mem_cons.2 ⟨subd15_2_165, List.forall_mem_cons.2 ⟨subd15_2_166, List.forall_mem_cons.2 ⟨subd15_2_167, List.forall_mem_cons.2 ⟨subd15_2_168, List.forall_mem_cons.2 ⟨subd15_2_169, List.forall_mem_cons.2 ⟨subd15_2_170, List.forall_mem_cons.2 ⟨subd15_2_171, List.forall_mem_cons.2 ⟨subd15_2_172, List.forall_mem_cons.2 ⟨subd15_2_173, List.forall_mem_cons.2 ⟨subd15_2_174, List.forall_mem_cons.2 ⟨subd15_2_175, List.forall_mem_cons.2 ⟨subd15_2_176, List.forall_mem_cons.2 ⟨subd15_2_177, List.forall_mem_cons.2 ⟨subd15_2_178, List.forall_mem_cons.2 ⟨subd15_2_179, List.forall_mem_cons.2 ⟨subd15_2_180, List.forall_mem_cons.2 ⟨subd15_2_181, List.forall_mem_cons.2 ⟨subd15_2_182, List.forall_mem_cons.2 ⟨subd15_2_183, List.forall_mem_cons.2 ⟨subd15_2_184, List.forall_mem_cons.2 ⟨subd15_2_185, List.forall_mem_cons.2 ⟨subd15_2_186, List.forall_mem_cons.2 ⟨subd15_2_187, List.forall_mem_cons.2 ⟨subd15_2_188, List.forall_mem_cons.2 ⟨subd15_2_189, List.forall_mem_cons.2 ⟨subd15_2_190, List.forall_mem_cons.2 ⟨subd15_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
