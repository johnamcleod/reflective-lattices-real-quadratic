import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_2_608 : subd15_2 [0, 2, 6] = true := by decide +kernel
theorem subd15_2_609 : subd15_2 [0, 2, 7] = true := by decide +kernel
theorem subd15_2_610 : subd15_2 [0, 2, 8] = true := by decide +kernel
theorem subd15_2_611 : subd15_2 [0, 3, -8] = true := by decide +kernel
theorem subd15_2_612 : subd15_2 [0, 3, -7] = true := by decide +kernel
theorem subd15_2_613 : subd15_2 [0, 3, -6] = true := by decide +kernel
theorem subd15_2_614 : subd15_2 [0, 3, -5] = true := by decide +kernel
theorem subd15_2_615 : subd15_2 [0, 3, -4] = true := by decide +kernel
theorem subd15_2_616 : subd15_2 [0, 3, -3] = true := by decide +kernel
theorem subd15_2_617 : subd15_2 [0, 3, -2] = true := by decide +kernel
theorem subd15_2_618 : subd15_2 [0, 3, -1] = true := by decide +kernel
theorem subd15_2_619 : subd15_2 [0, 3, 0] = true := by decide +kernel
theorem subd15_2_620 : subd15_2 [0, 3, 1] = true := by decide +kernel
theorem subd15_2_621 : subd15_2 [0, 3, 2] = true := by decide +kernel
theorem subd15_2_622 : subd15_2 [0, 3, 3] = true := by decide +kernel
theorem subd15_2_623 : subd15_2 [0, 3, 4] = true := by decide +kernel
theorem subd15_2_624 : subd15_2 [0, 3, 5] = true := by decide +kernel
theorem subd15_2_625 : subd15_2 [0, 3, 6] = true := by decide +kernel
theorem subd15_2_626 : subd15_2 [0, 3, 7] = true := by decide +kernel
theorem subd15_2_627 : subd15_2 [0, 3, 8] = true := by decide +kernel
theorem subd15_2_628 : subd15_2 [0, 4, -8] = true := by decide +kernel
theorem subd15_2_629 : subd15_2 [0, 4, -7] = true := by decide +kernel
theorem subd15_2_630 : subd15_2 [0, 4, -6] = true := by decide +kernel
theorem subd15_2_631 : subd15_2 [0, 4, -5] = true := by decide +kernel
theorem subd15_2_632 : subd15_2 [0, 4, -4] = true := by decide +kernel
theorem subd15_2_633 : subd15_2 [0, 4, -3] = true := by decide +kernel
theorem subd15_2_634 : subd15_2 [0, 4, -2] = true := by decide +kernel
theorem subd15_2_635 : subd15_2 [0, 4, -1] = true := by decide +kernel
theorem subd15_2_636 : subd15_2 [0, 4, 0] = true := by decide +kernel
theorem subd15_2_637 : subd15_2 [0, 4, 1] = true := by decide +kernel
theorem subd15_2_638 : subd15_2 [0, 4, 2] = true := by decide +kernel
theorem subd15_2_639 : subd15_2 [0, 4, 3] = true := by decide +kernel
theorem sbd15_2_19 : ∀ q ∈ blkd15_2_19, subd15_2 q = true := by
  unfold blkd15_2_19
  exact List.forall_mem_cons.2 ⟨subd15_2_608, List.forall_mem_cons.2 ⟨subd15_2_609, List.forall_mem_cons.2 ⟨subd15_2_610, List.forall_mem_cons.2 ⟨subd15_2_611, List.forall_mem_cons.2 ⟨subd15_2_612, List.forall_mem_cons.2 ⟨subd15_2_613, List.forall_mem_cons.2 ⟨subd15_2_614, List.forall_mem_cons.2 ⟨subd15_2_615, List.forall_mem_cons.2 ⟨subd15_2_616, List.forall_mem_cons.2 ⟨subd15_2_617, List.forall_mem_cons.2 ⟨subd15_2_618, List.forall_mem_cons.2 ⟨subd15_2_619, List.forall_mem_cons.2 ⟨subd15_2_620, List.forall_mem_cons.2 ⟨subd15_2_621, List.forall_mem_cons.2 ⟨subd15_2_622, List.forall_mem_cons.2 ⟨subd15_2_623, List.forall_mem_cons.2 ⟨subd15_2_624, List.forall_mem_cons.2 ⟨subd15_2_625, List.forall_mem_cons.2 ⟨subd15_2_626, List.forall_mem_cons.2 ⟨subd15_2_627, List.forall_mem_cons.2 ⟨subd15_2_628, List.forall_mem_cons.2 ⟨subd15_2_629, List.forall_mem_cons.2 ⟨subd15_2_630, List.forall_mem_cons.2 ⟨subd15_2_631, List.forall_mem_cons.2 ⟨subd15_2_632, List.forall_mem_cons.2 ⟨subd15_2_633, List.forall_mem_cons.2 ⟨subd15_2_634, List.forall_mem_cons.2 ⟨subd15_2_635, List.forall_mem_cons.2 ⟨subd15_2_636, List.forall_mem_cons.2 ⟨subd15_2_637, List.forall_mem_cons.2 ⟨subd15_2_638, List.forall_mem_cons.2 ⟨subd15_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_640 : subd15_2 [0, 4, 4] = true := by decide +kernel
theorem subd15_2_641 : subd15_2 [0, 4, 5] = true := by decide +kernel
theorem subd15_2_642 : subd15_2 [0, 4, 6] = true := by decide +kernel
theorem subd15_2_643 : subd15_2 [0, 4, 7] = true := by decide +kernel
theorem subd15_2_644 : subd15_2 [0, 5] = true := by decide +kernel
theorem subd15_2_645 : subd15_2 [0, 6] = true := by decide +kernel
theorem subd15_2_646 : subd15_2 [1, -7] = true := by decide +kernel
theorem subd15_2_647 : subd15_2 [1, -6] = true := by decide +kernel
theorem subd15_2_648 : subd15_2 [1, -5] = true := by decide +kernel
theorem subd15_2_649 : subd15_2 [1, -4, -7] = true := by decide +kernel
theorem subd15_2_650 : subd15_2 [1, -4, -6] = true := by decide +kernel
theorem subd15_2_651 : subd15_2 [1, -4, -5] = true := by decide +kernel
theorem subd15_2_652 : subd15_2 [1, -4, -4] = true := by decide +kernel
theorem subd15_2_653 : subd15_2 [1, -4, -3] = true := by decide +kernel
theorem subd15_2_654 : subd15_2 [1, -4, -2] = true := by decide +kernel
theorem subd15_2_655 : subd15_2 [1, -4, -1] = true := by decide +kernel
theorem subd15_2_656 : subd15_2 [1, -4, 0] = true := by decide +kernel
theorem subd15_2_657 : subd15_2 [1, -4, 1] = true := by decide +kernel
theorem subd15_2_658 : subd15_2 [1, -4, 2] = true := by decide +kernel
theorem subd15_2_659 : subd15_2 [1, -4, 3] = true := by decide +kernel
theorem subd15_2_660 : subd15_2 [1, -4, 4] = true := by decide +kernel
theorem subd15_2_661 : subd15_2 [1, -4, 5] = true := by decide +kernel
theorem subd15_2_662 : subd15_2 [1, -4, 6] = true := by decide +kernel
theorem subd15_2_663 : subd15_2 [1, -3, -8] = true := by decide +kernel
theorem subd15_2_664 : subd15_2 [1, -3, -7] = true := by decide +kernel
theorem subd15_2_665 : subd15_2 [1, -3, -6] = true := by decide +kernel
theorem subd15_2_666 : subd15_2 [1, -3, -5] = true := by decide +kernel
theorem subd15_2_667 : subd15_2 [1, -3, -4] = true := by decide +kernel
theorem subd15_2_668 : subd15_2 [1, -3, -3] = true := by decide +kernel
theorem subd15_2_669 : subd15_2 [1, -3, -2] = true := by decide +kernel
theorem subd15_2_670 : subd15_2 [1, -3, -1] = true := by decide +kernel
theorem subd15_2_671 : subd15_2 [1, -3, 0] = true := by decide +kernel
theorem sbd15_2_20 : ∀ q ∈ blkd15_2_20, subd15_2 q = true := by
  unfold blkd15_2_20
  exact List.forall_mem_cons.2 ⟨subd15_2_640, List.forall_mem_cons.2 ⟨subd15_2_641, List.forall_mem_cons.2 ⟨subd15_2_642, List.forall_mem_cons.2 ⟨subd15_2_643, List.forall_mem_cons.2 ⟨subd15_2_644, List.forall_mem_cons.2 ⟨subd15_2_645, List.forall_mem_cons.2 ⟨subd15_2_646, List.forall_mem_cons.2 ⟨subd15_2_647, List.forall_mem_cons.2 ⟨subd15_2_648, List.forall_mem_cons.2 ⟨subd15_2_649, List.forall_mem_cons.2 ⟨subd15_2_650, List.forall_mem_cons.2 ⟨subd15_2_651, List.forall_mem_cons.2 ⟨subd15_2_652, List.forall_mem_cons.2 ⟨subd15_2_653, List.forall_mem_cons.2 ⟨subd15_2_654, List.forall_mem_cons.2 ⟨subd15_2_655, List.forall_mem_cons.2 ⟨subd15_2_656, List.forall_mem_cons.2 ⟨subd15_2_657, List.forall_mem_cons.2 ⟨subd15_2_658, List.forall_mem_cons.2 ⟨subd15_2_659, List.forall_mem_cons.2 ⟨subd15_2_660, List.forall_mem_cons.2 ⟨subd15_2_661, List.forall_mem_cons.2 ⟨subd15_2_662, List.forall_mem_cons.2 ⟨subd15_2_663, List.forall_mem_cons.2 ⟨subd15_2_664, List.forall_mem_cons.2 ⟨subd15_2_665, List.forall_mem_cons.2 ⟨subd15_2_666, List.forall_mem_cons.2 ⟨subd15_2_667, List.forall_mem_cons.2 ⟨subd15_2_668, List.forall_mem_cons.2 ⟨subd15_2_669, List.forall_mem_cons.2 ⟨subd15_2_670, List.forall_mem_cons.2 ⟨subd15_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_672 : subd15_2 [1, -3, 1] = true := by decide +kernel
theorem subd15_2_673 : subd15_2 [1, -3, 2] = true := by decide +kernel
theorem subd15_2_674 : subd15_2 [1, -3, 3] = true := by decide +kernel
theorem subd15_2_675 : subd15_2 [1, -3, 4] = true := by decide +kernel
theorem subd15_2_676 : subd15_2 [1, -3, 5] = true := by decide +kernel
theorem subd15_2_677 : subd15_2 [1, -3, 6] = true := by decide +kernel
theorem subd15_2_678 : subd15_2 [1, -3, 7] = true := by decide +kernel
theorem subd15_2_679 : subd15_2 [1, -2, -9] = true := by decide +kernel
theorem subd15_2_680 : subd15_2 [1, -2, -8] = true := by decide +kernel
theorem subd15_2_681 : subd15_2 [1, -2, -7] = true := by decide +kernel
theorem subd15_2_682 : subd15_2 [1, -2, -6] = true := by decide +kernel
theorem subd15_2_683 : subd15_2 [1, -2, -5] = true := by decide +kernel
theorem subd15_2_684 : subd15_2 [1, -2, -4] = true := by decide +kernel
theorem subd15_2_685 : subd15_2 [1, -2, -3] = true := by decide +kernel
theorem subd15_2_686 : subd15_2 [1, -2, -2] = true := by decide +kernel
theorem subd15_2_687 : subd15_2 [1, -2, -1] = true := by decide +kernel
theorem subd15_2_688 : subd15_2 [1, -2, 0] = true := by decide +kernel
theorem subd15_2_689 : subd15_2 [1, -2, 1] = true := by decide +kernel
theorem subd15_2_690 : subd15_2 [1, -2, 2] = true := by decide +kernel
theorem subd15_2_691 : subd15_2 [1, -2, 3] = true := by decide +kernel
theorem subd15_2_692 : subd15_2 [1, -2, 4] = true := by decide +kernel
theorem subd15_2_693 : subd15_2 [1, -2, 5] = true := by decide +kernel
theorem subd15_2_694 : subd15_2 [1, -2, 6] = true := by decide +kernel
theorem subd15_2_695 : subd15_2 [1, -2, 7] = true := by decide +kernel
theorem subd15_2_696 : subd15_2 [1, -2, 8] = true := by decide +kernel
theorem subd15_2_697 : subd15_2 [1, -1, -9] = true := by decide +kernel
theorem subd15_2_698 : subd15_2 [1, -1, -8] = true := by decide +kernel
theorem subd15_2_699 : subd15_2 [1, -1, -7] = true := by decide +kernel
theorem subd15_2_700 : subd15_2 [1, -1, -6] = true := by decide +kernel
theorem subd15_2_701 : subd15_2 [1, -1, -5] = true := by decide +kernel
theorem subd15_2_702 : subd15_2 [1, -1, -4] = true := by decide +kernel
theorem subd15_2_703 : subd15_2 [1, -1, -3] = true := by decide +kernel
theorem sbd15_2_21 : ∀ q ∈ blkd15_2_21, subd15_2 q = true := by
  unfold blkd15_2_21
  exact List.forall_mem_cons.2 ⟨subd15_2_672, List.forall_mem_cons.2 ⟨subd15_2_673, List.forall_mem_cons.2 ⟨subd15_2_674, List.forall_mem_cons.2 ⟨subd15_2_675, List.forall_mem_cons.2 ⟨subd15_2_676, List.forall_mem_cons.2 ⟨subd15_2_677, List.forall_mem_cons.2 ⟨subd15_2_678, List.forall_mem_cons.2 ⟨subd15_2_679, List.forall_mem_cons.2 ⟨subd15_2_680, List.forall_mem_cons.2 ⟨subd15_2_681, List.forall_mem_cons.2 ⟨subd15_2_682, List.forall_mem_cons.2 ⟨subd15_2_683, List.forall_mem_cons.2 ⟨subd15_2_684, List.forall_mem_cons.2 ⟨subd15_2_685, List.forall_mem_cons.2 ⟨subd15_2_686, List.forall_mem_cons.2 ⟨subd15_2_687, List.forall_mem_cons.2 ⟨subd15_2_688, List.forall_mem_cons.2 ⟨subd15_2_689, List.forall_mem_cons.2 ⟨subd15_2_690, List.forall_mem_cons.2 ⟨subd15_2_691, List.forall_mem_cons.2 ⟨subd15_2_692, List.forall_mem_cons.2 ⟨subd15_2_693, List.forall_mem_cons.2 ⟨subd15_2_694, List.forall_mem_cons.2 ⟨subd15_2_695, List.forall_mem_cons.2 ⟨subd15_2_696, List.forall_mem_cons.2 ⟨subd15_2_697, List.forall_mem_cons.2 ⟨subd15_2_698, List.forall_mem_cons.2 ⟨subd15_2_699, List.forall_mem_cons.2 ⟨subd15_2_700, List.forall_mem_cons.2 ⟨subd15_2_701, List.forall_mem_cons.2 ⟨subd15_2_702, List.forall_mem_cons.2 ⟨subd15_2_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_704 : subd15_2 [1, -1, -2] = true := by decide +kernel
theorem subd15_2_705 : subd15_2 [1, -1, -1] = true := by decide +kernel
theorem subd15_2_706 : subd15_2 [1, -1, 0] = true := by decide +kernel
theorem subd15_2_707 : subd15_2 [1, -1, 1] = true := by decide +kernel
theorem subd15_2_708 : subd15_2 [1, -1, 2] = true := by decide +kernel
theorem subd15_2_709 : subd15_2 [1, -1, 3] = true := by decide +kernel
theorem subd15_2_710 : subd15_2 [1, -1, 4] = true := by decide +kernel
theorem subd15_2_711 : subd15_2 [1, -1, 5] = true := by decide +kernel
theorem subd15_2_712 : subd15_2 [1, -1, 6] = true := by decide +kernel
theorem subd15_2_713 : subd15_2 [1, -1, 7] = true := by decide +kernel
theorem subd15_2_714 : subd15_2 [1, -1, 8] = true := by decide +kernel
theorem subd15_2_715 : subd15_2 [1, 0, -9] = true := by decide +kernel
theorem subd15_2_716 : subd15_2 [1, 0, -8] = true := by decide +kernel
theorem subd15_2_717 : subd15_2 [1, 0, -7] = true := by decide +kernel
theorem subd15_2_718 : subd15_2 [1, 0, -6] = true := by decide +kernel
theorem subd15_2_719 : subd15_2 [1, 0, -5] = true := by decide +kernel
theorem subd15_2_720 : subd15_2 [1, 0, -4] = true := by decide +kernel
theorem subd15_2_721 : subd15_2 [1, 0, -3] = true := by decide +kernel
theorem subd15_2_722 : subd15_2 [1, 0, -2] = true := by decide +kernel
theorem subd15_2_723 : subd15_2 [1, 0, -1] = true := by decide +kernel
theorem subd15_2_724 : subd15_2 [1, 0, 0] = true := by decide +kernel
theorem subd15_2_725 : subd15_2 [1, 0, 1] = true := by decide +kernel
theorem subd15_2_726 : subd15_2 [1, 0, 2] = true := by decide +kernel
theorem subd15_2_727 : subd15_2 [1, 0, 3] = true := by decide +kernel
theorem subd15_2_728 : subd15_2 [1, 0, 4] = true := by decide +kernel
theorem subd15_2_729 : subd15_2 [1, 0, 5] = true := by decide +kernel
theorem subd15_2_730 : subd15_2 [1, 0, 6] = true := by decide +kernel
theorem subd15_2_731 : subd15_2 [1, 0, 7] = true := by decide +kernel
theorem subd15_2_732 : subd15_2 [1, 0, 8] = true := by decide +kernel
theorem subd15_2_733 : subd15_2 [1, 0, 9] = true := by decide +kernel
theorem subd15_2_734 : subd15_2 [1, 1, -9] = true := by decide +kernel
theorem subd15_2_735 : subd15_2 [1, 1, -8] = true := by decide +kernel
theorem sbd15_2_22 : ∀ q ∈ blkd15_2_22, subd15_2 q = true := by
  unfold blkd15_2_22
  exact List.forall_mem_cons.2 ⟨subd15_2_704, List.forall_mem_cons.2 ⟨subd15_2_705, List.forall_mem_cons.2 ⟨subd15_2_706, List.forall_mem_cons.2 ⟨subd15_2_707, List.forall_mem_cons.2 ⟨subd15_2_708, List.forall_mem_cons.2 ⟨subd15_2_709, List.forall_mem_cons.2 ⟨subd15_2_710, List.forall_mem_cons.2 ⟨subd15_2_711, List.forall_mem_cons.2 ⟨subd15_2_712, List.forall_mem_cons.2 ⟨subd15_2_713, List.forall_mem_cons.2 ⟨subd15_2_714, List.forall_mem_cons.2 ⟨subd15_2_715, List.forall_mem_cons.2 ⟨subd15_2_716, List.forall_mem_cons.2 ⟨subd15_2_717, List.forall_mem_cons.2 ⟨subd15_2_718, List.forall_mem_cons.2 ⟨subd15_2_719, List.forall_mem_cons.2 ⟨subd15_2_720, List.forall_mem_cons.2 ⟨subd15_2_721, List.forall_mem_cons.2 ⟨subd15_2_722, List.forall_mem_cons.2 ⟨subd15_2_723, List.forall_mem_cons.2 ⟨subd15_2_724, List.forall_mem_cons.2 ⟨subd15_2_725, List.forall_mem_cons.2 ⟨subd15_2_726, List.forall_mem_cons.2 ⟨subd15_2_727, List.forall_mem_cons.2 ⟨subd15_2_728, List.forall_mem_cons.2 ⟨subd15_2_729, List.forall_mem_cons.2 ⟨subd15_2_730, List.forall_mem_cons.2 ⟨subd15_2_731, List.forall_mem_cons.2 ⟨subd15_2_732, List.forall_mem_cons.2 ⟨subd15_2_733, List.forall_mem_cons.2 ⟨subd15_2_734, List.forall_mem_cons.2 ⟨subd15_2_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_736 : subd15_2 [1, 1, -7] = true := by decide +kernel
theorem subd15_2_737 : subd15_2 [1, 1, -6] = true := by decide +kernel
theorem subd15_2_738 : subd15_2 [1, 1, -5] = true := by decide +kernel
theorem subd15_2_739 : subd15_2 [1, 1, -4] = true := by decide +kernel
theorem subd15_2_740 : subd15_2 [1, 1, -3] = true := by decide +kernel
theorem subd15_2_741 : subd15_2 [1, 1, -2] = true := by decide +kernel
theorem subd15_2_742 : subd15_2 [1, 1, -1] = true := by decide +kernel
theorem subd15_2_743 : subd15_2 [1, 1, 0] = true := by decide +kernel
theorem subd15_2_744 : subd15_2 [1, 1, 1] = true := by decide +kernel
theorem subd15_2_745 : subd15_2 [1, 1, 2] = true := by decide +kernel
theorem subd15_2_746 : subd15_2 [1, 1, 3] = true := by decide +kernel
theorem subd15_2_747 : subd15_2 [1, 1, 4] = true := by decide +kernel
theorem subd15_2_748 : subd15_2 [1, 1, 5] = true := by decide +kernel
theorem subd15_2_749 : subd15_2 [1, 1, 6] = true := by decide +kernel
theorem subd15_2_750 : subd15_2 [1, 1, 7] = true := by decide +kernel
theorem subd15_2_751 : subd15_2 [1, 1, 8] = true := by decide +kernel
theorem subd15_2_752 : subd15_2 [1, 1, 9] = true := by decide +kernel
theorem subd15_2_753 : subd15_2 [1, 2, -9] = true := by decide +kernel
theorem subd15_2_754 : subd15_2 [1, 2, -8] = true := by decide +kernel
theorem subd15_2_755 : subd15_2 [1, 2, -7] = true := by decide +kernel
theorem subd15_2_756 : subd15_2 [1, 2, -6] = true := by decide +kernel
theorem subd15_2_757 : subd15_2 [1, 2, -5] = true := by decide +kernel
theorem subd15_2_758 : subd15_2 [1, 2, -4] = true := by decide +kernel
theorem subd15_2_759 : subd15_2 [1, 2, -3] = true := by decide +kernel
theorem subd15_2_760 : subd15_2 [1, 2, -2] = true := by decide +kernel
theorem subd15_2_761 : subd15_2 [1, 2, -1] = true := by decide +kernel
theorem subd15_2_762 : subd15_2 [1, 2, 0] = true := by decide +kernel
theorem subd15_2_763 : subd15_2 [1, 2, 1] = true := by decide +kernel
theorem subd15_2_764 : subd15_2 [1, 2, 2] = true := by decide +kernel
theorem subd15_2_765 : subd15_2 [1, 2, 3] = true := by decide +kernel
theorem subd15_2_766 : subd15_2 [1, 2, 4] = true := by decide +kernel
theorem subd15_2_767 : subd15_2 [1, 2, 5] = true := by decide +kernel
theorem sbd15_2_23 : ∀ q ∈ blkd15_2_23, subd15_2 q = true := by
  unfold blkd15_2_23
  exact List.forall_mem_cons.2 ⟨subd15_2_736, List.forall_mem_cons.2 ⟨subd15_2_737, List.forall_mem_cons.2 ⟨subd15_2_738, List.forall_mem_cons.2 ⟨subd15_2_739, List.forall_mem_cons.2 ⟨subd15_2_740, List.forall_mem_cons.2 ⟨subd15_2_741, List.forall_mem_cons.2 ⟨subd15_2_742, List.forall_mem_cons.2 ⟨subd15_2_743, List.forall_mem_cons.2 ⟨subd15_2_744, List.forall_mem_cons.2 ⟨subd15_2_745, List.forall_mem_cons.2 ⟨subd15_2_746, List.forall_mem_cons.2 ⟨subd15_2_747, List.forall_mem_cons.2 ⟨subd15_2_748, List.forall_mem_cons.2 ⟨subd15_2_749, List.forall_mem_cons.2 ⟨subd15_2_750, List.forall_mem_cons.2 ⟨subd15_2_751, List.forall_mem_cons.2 ⟨subd15_2_752, List.forall_mem_cons.2 ⟨subd15_2_753, List.forall_mem_cons.2 ⟨subd15_2_754, List.forall_mem_cons.2 ⟨subd15_2_755, List.forall_mem_cons.2 ⟨subd15_2_756, List.forall_mem_cons.2 ⟨subd15_2_757, List.forall_mem_cons.2 ⟨subd15_2_758, List.forall_mem_cons.2 ⟨subd15_2_759, List.forall_mem_cons.2 ⟨subd15_2_760, List.forall_mem_cons.2 ⟨subd15_2_761, List.forall_mem_cons.2 ⟨subd15_2_762, List.forall_mem_cons.2 ⟨subd15_2_763, List.forall_mem_cons.2 ⟨subd15_2_764, List.forall_mem_cons.2 ⟨subd15_2_765, List.forall_mem_cons.2 ⟨subd15_2_766, List.forall_mem_cons.2 ⟨subd15_2_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_768 : subd15_2 [1, 2, 6] = true := by decide +kernel
theorem subd15_2_769 : subd15_2 [1, 2, 7] = true := by decide +kernel
theorem subd15_2_770 : subd15_2 [1, 2, 8] = true := by decide +kernel
theorem subd15_2_771 : subd15_2 [1, 3, -8] = true := by decide +kernel
theorem subd15_2_772 : subd15_2 [1, 3, -7] = true := by decide +kernel
theorem subd15_2_773 : subd15_2 [1, 3, -6] = true := by decide +kernel
theorem subd15_2_774 : subd15_2 [1, 3, -5] = true := by decide +kernel
theorem subd15_2_775 : subd15_2 [1, 3, -4] = true := by decide +kernel
theorem subd15_2_776 : subd15_2 [1, 3, -3] = true := by decide +kernel
theorem subd15_2_777 : subd15_2 [1, 3, -2] = true := by decide +kernel
theorem subd15_2_778 : subd15_2 [1, 3, -1] = true := by decide +kernel
theorem subd15_2_779 : subd15_2 [1, 3, 0] = true := by decide +kernel
theorem subd15_2_780 : subd15_2 [1, 3, 1] = true := by decide +kernel
theorem subd15_2_781 : subd15_2 [1, 3, 2] = true := by decide +kernel
theorem subd15_2_782 : subd15_2 [1, 3, 3] = true := by decide +kernel
theorem subd15_2_783 : subd15_2 [1, 3, 4] = true := by decide +kernel
theorem subd15_2_784 : subd15_2 [1, 3, 5] = true := by decide +kernel
theorem subd15_2_785 : subd15_2 [1, 3, 6] = true := by decide +kernel
theorem subd15_2_786 : subd15_2 [1, 3, 7] = true := by decide +kernel
theorem subd15_2_787 : subd15_2 [1, 3, 8] = true := by decide +kernel
theorem subd15_2_788 : subd15_2 [1, 4, -8] = true := by decide +kernel
theorem subd15_2_789 : subd15_2 [1, 4, -7] = true := by decide +kernel
theorem subd15_2_790 : subd15_2 [1, 4, -6] = true := by decide +kernel
theorem subd15_2_791 : subd15_2 [1, 4, -5] = true := by decide +kernel
theorem subd15_2_792 : subd15_2 [1, 4, -4] = true := by decide +kernel
theorem subd15_2_793 : subd15_2 [1, 4, -3] = true := by decide +kernel
theorem subd15_2_794 : subd15_2 [1, 4, -2] = true := by decide +kernel
theorem subd15_2_795 : subd15_2 [1, 4, -1] = true := by decide +kernel
theorem subd15_2_796 : subd15_2 [1, 4, 0] = true := by decide +kernel
theorem subd15_2_797 : subd15_2 [1, 4, 1] = true := by decide +kernel
theorem subd15_2_798 : subd15_2 [1, 4, 2] = true := by decide +kernel
theorem subd15_2_799 : subd15_2 [1, 4, 3] = true := by decide +kernel
theorem sbd15_2_24 : ∀ q ∈ blkd15_2_24, subd15_2 q = true := by
  unfold blkd15_2_24
  exact List.forall_mem_cons.2 ⟨subd15_2_768, List.forall_mem_cons.2 ⟨subd15_2_769, List.forall_mem_cons.2 ⟨subd15_2_770, List.forall_mem_cons.2 ⟨subd15_2_771, List.forall_mem_cons.2 ⟨subd15_2_772, List.forall_mem_cons.2 ⟨subd15_2_773, List.forall_mem_cons.2 ⟨subd15_2_774, List.forall_mem_cons.2 ⟨subd15_2_775, List.forall_mem_cons.2 ⟨subd15_2_776, List.forall_mem_cons.2 ⟨subd15_2_777, List.forall_mem_cons.2 ⟨subd15_2_778, List.forall_mem_cons.2 ⟨subd15_2_779, List.forall_mem_cons.2 ⟨subd15_2_780, List.forall_mem_cons.2 ⟨subd15_2_781, List.forall_mem_cons.2 ⟨subd15_2_782, List.forall_mem_cons.2 ⟨subd15_2_783, List.forall_mem_cons.2 ⟨subd15_2_784, List.forall_mem_cons.2 ⟨subd15_2_785, List.forall_mem_cons.2 ⟨subd15_2_786, List.forall_mem_cons.2 ⟨subd15_2_787, List.forall_mem_cons.2 ⟨subd15_2_788, List.forall_mem_cons.2 ⟨subd15_2_789, List.forall_mem_cons.2 ⟨subd15_2_790, List.forall_mem_cons.2 ⟨subd15_2_791, List.forall_mem_cons.2 ⟨subd15_2_792, List.forall_mem_cons.2 ⟨subd15_2_793, List.forall_mem_cons.2 ⟨subd15_2_794, List.forall_mem_cons.2 ⟨subd15_2_795, List.forall_mem_cons.2 ⟨subd15_2_796, List.forall_mem_cons.2 ⟨subd15_2_797, List.forall_mem_cons.2 ⟨subd15_2_798, List.forall_mem_cons.2 ⟨subd15_2_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_800 : subd15_2 [1, 4, 4] = true := by decide +kernel
theorem subd15_2_801 : subd15_2 [1, 4, 5] = true := by decide +kernel
theorem subd15_2_802 : subd15_2 [1, 4, 6] = true := by decide +kernel
theorem subd15_2_803 : subd15_2 [1, 4, 7] = true := by decide +kernel
theorem subd15_2_804 : subd15_2 [1, 5, -7] = true := by decide +kernel
theorem subd15_2_805 : subd15_2 [1, 5, -6] = true := by decide +kernel
theorem subd15_2_806 : subd15_2 [1, 5, -5] = true := by decide +kernel
theorem subd15_2_807 : subd15_2 [1, 5, -4] = true := by decide +kernel
theorem subd15_2_808 : subd15_2 [1, 5, -3] = true := by decide +kernel
theorem subd15_2_809 : subd15_2 [1, 5, -2] = true := by decide +kernel
theorem subd15_2_810 : subd15_2 [1, 5, -1] = true := by decide +kernel
theorem subd15_2_811 : subd15_2 [1, 5, 0] = true := by decide +kernel
theorem subd15_2_812 : subd15_2 [1, 5, 1] = true := by decide +kernel
theorem subd15_2_813 : subd15_2 [1, 5, 2] = true := by decide +kernel
theorem subd15_2_814 : subd15_2 [1, 5, 3] = true := by decide +kernel
theorem subd15_2_815 : subd15_2 [1, 5, 4] = true := by decide +kernel
theorem subd15_2_816 : subd15_2 [1, 5, 5] = true := by decide +kernel
theorem subd15_2_817 : subd15_2 [1, 5, 6] = true := by decide +kernel
theorem subd15_2_818 : subd15_2 [1, 6] = true := by decide +kernel
theorem subd15_2_819 : subd15_2 [1, 7] = true := by decide +kernel
theorem subd15_2_820 : subd15_2 [2, -6] = true := by decide +kernel
theorem subd15_2_821 : subd15_2 [2, -5] = true := by decide +kernel
theorem subd15_2_822 : subd15_2 [2, -4] = true := by decide +kernel
theorem subd15_2_823 : subd15_2 [2, -3, -7] = true := by decide +kernel
theorem subd15_2_824 : subd15_2 [2, -3, -6] = true := by decide +kernel
theorem subd15_2_825 : subd15_2 [2, -3, -5] = true := by decide +kernel
theorem subd15_2_826 : subd15_2 [2, -3, -4] = true := by decide +kernel
theorem subd15_2_827 : subd15_2 [2, -3, -3] = true := by decide +kernel
theorem subd15_2_828 : subd15_2 [2, -3, -2] = true := by decide +kernel
theorem subd15_2_829 : subd15_2 [2, -3, -1] = true := by decide +kernel
theorem subd15_2_830 : subd15_2 [2, -3, 0] = true := by decide +kernel
theorem subd15_2_831 : subd15_2 [2, -3, 1] = true := by decide +kernel
theorem sbd15_2_25 : ∀ q ∈ blkd15_2_25, subd15_2 q = true := by
  unfold blkd15_2_25
  exact List.forall_mem_cons.2 ⟨subd15_2_800, List.forall_mem_cons.2 ⟨subd15_2_801, List.forall_mem_cons.2 ⟨subd15_2_802, List.forall_mem_cons.2 ⟨subd15_2_803, List.forall_mem_cons.2 ⟨subd15_2_804, List.forall_mem_cons.2 ⟨subd15_2_805, List.forall_mem_cons.2 ⟨subd15_2_806, List.forall_mem_cons.2 ⟨subd15_2_807, List.forall_mem_cons.2 ⟨subd15_2_808, List.forall_mem_cons.2 ⟨subd15_2_809, List.forall_mem_cons.2 ⟨subd15_2_810, List.forall_mem_cons.2 ⟨subd15_2_811, List.forall_mem_cons.2 ⟨subd15_2_812, List.forall_mem_cons.2 ⟨subd15_2_813, List.forall_mem_cons.2 ⟨subd15_2_814, List.forall_mem_cons.2 ⟨subd15_2_815, List.forall_mem_cons.2 ⟨subd15_2_816, List.forall_mem_cons.2 ⟨subd15_2_817, List.forall_mem_cons.2 ⟨subd15_2_818, List.forall_mem_cons.2 ⟨subd15_2_819, List.forall_mem_cons.2 ⟨subd15_2_820, List.forall_mem_cons.2 ⟨subd15_2_821, List.forall_mem_cons.2 ⟨subd15_2_822, List.forall_mem_cons.2 ⟨subd15_2_823, List.forall_mem_cons.2 ⟨subd15_2_824, List.forall_mem_cons.2 ⟨subd15_2_825, List.forall_mem_cons.2 ⟨subd15_2_826, List.forall_mem_cons.2 ⟨subd15_2_827, List.forall_mem_cons.2 ⟨subd15_2_828, List.forall_mem_cons.2 ⟨subd15_2_829, List.forall_mem_cons.2 ⟨subd15_2_830, List.forall_mem_cons.2 ⟨subd15_2_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_832 : subd15_2 [2, -3, 2] = true := by decide +kernel
theorem subd15_2_833 : subd15_2 [2, -3, 3] = true := by decide +kernel
theorem subd15_2_834 : subd15_2 [2, -3, 4] = true := by decide +kernel
theorem subd15_2_835 : subd15_2 [2, -3, 5] = true := by decide +kernel
theorem subd15_2_836 : subd15_2 [2, -3, 6] = true := by decide +kernel
theorem subd15_2_837 : subd15_2 [2, -2, -8] = true := by decide +kernel
theorem subd15_2_838 : subd15_2 [2, -2, -7] = true := by decide +kernel
theorem subd15_2_839 : subd15_2 [2, -2, -6] = true := by decide +kernel
theorem subd15_2_840 : subd15_2 [2, -2, -5] = true := by decide +kernel
theorem subd15_2_841 : subd15_2 [2, -2, -4] = true := by decide +kernel
theorem subd15_2_842 : subd15_2 [2, -2, -3] = true := by decide +kernel
theorem subd15_2_843 : subd15_2 [2, -2, -2] = true := by decide +kernel
theorem subd15_2_844 : subd15_2 [2, -2, -1] = true := by decide +kernel
theorem subd15_2_845 : subd15_2 [2, -2, 0] = true := by decide +kernel
theorem subd15_2_846 : subd15_2 [2, -2, 1] = true := by decide +kernel
theorem subd15_2_847 : subd15_2 [2, -2, 2] = true := by decide +kernel
theorem subd15_2_848 : subd15_2 [2, -2, 3] = true := by decide +kernel
theorem subd15_2_849 : subd15_2 [2, -2, 4] = true := by decide +kernel
theorem subd15_2_850 : subd15_2 [2, -2, 5] = true := by decide +kernel
theorem subd15_2_851 : subd15_2 [2, -2, 6] = true := by decide +kernel
theorem subd15_2_852 : subd15_2 [2, -2, 7] = true := by decide +kernel
theorem subd15_2_853 : subd15_2 [2, -1, -8] = true := by decide +kernel
theorem subd15_2_854 : subd15_2 [2, -1, -7] = true := by decide +kernel
theorem subd15_2_855 : subd15_2 [2, -1, -6] = true := by decide +kernel
theorem subd15_2_856 : subd15_2 [2, -1, -5] = true := by decide +kernel
theorem subd15_2_857 : subd15_2 [2, -1, -4] = true := by decide +kernel
theorem subd15_2_858 : subd15_2 [2, -1, -3] = true := by decide +kernel
theorem subd15_2_859 : subd15_2 [2, -1, -2] = true := by decide +kernel
theorem subd15_2_860 : subd15_2 [2, -1, -1] = true := by decide +kernel
theorem subd15_2_861 : subd15_2 [2, -1, 0] = true := by decide +kernel
theorem subd15_2_862 : subd15_2 [2, -1, 1] = true := by decide +kernel
theorem subd15_2_863 : subd15_2 [2, -1, 2] = true := by decide +kernel
theorem sbd15_2_26 : ∀ q ∈ blkd15_2_26, subd15_2 q = true := by
  unfold blkd15_2_26
  exact List.forall_mem_cons.2 ⟨subd15_2_832, List.forall_mem_cons.2 ⟨subd15_2_833, List.forall_mem_cons.2 ⟨subd15_2_834, List.forall_mem_cons.2 ⟨subd15_2_835, List.forall_mem_cons.2 ⟨subd15_2_836, List.forall_mem_cons.2 ⟨subd15_2_837, List.forall_mem_cons.2 ⟨subd15_2_838, List.forall_mem_cons.2 ⟨subd15_2_839, List.forall_mem_cons.2 ⟨subd15_2_840, List.forall_mem_cons.2 ⟨subd15_2_841, List.forall_mem_cons.2 ⟨subd15_2_842, List.forall_mem_cons.2 ⟨subd15_2_843, List.forall_mem_cons.2 ⟨subd15_2_844, List.forall_mem_cons.2 ⟨subd15_2_845, List.forall_mem_cons.2 ⟨subd15_2_846, List.forall_mem_cons.2 ⟨subd15_2_847, List.forall_mem_cons.2 ⟨subd15_2_848, List.forall_mem_cons.2 ⟨subd15_2_849, List.forall_mem_cons.2 ⟨subd15_2_850, List.forall_mem_cons.2 ⟨subd15_2_851, List.forall_mem_cons.2 ⟨subd15_2_852, List.forall_mem_cons.2 ⟨subd15_2_853, List.forall_mem_cons.2 ⟨subd15_2_854, List.forall_mem_cons.2 ⟨subd15_2_855, List.forall_mem_cons.2 ⟨subd15_2_856, List.forall_mem_cons.2 ⟨subd15_2_857, List.forall_mem_cons.2 ⟨subd15_2_858, List.forall_mem_cons.2 ⟨subd15_2_859, List.forall_mem_cons.2 ⟨subd15_2_860, List.forall_mem_cons.2 ⟨subd15_2_861, List.forall_mem_cons.2 ⟨subd15_2_862, List.forall_mem_cons.2 ⟨subd15_2_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_864 : subd15_2 [2, -1, 3] = true := by decide +kernel
theorem subd15_2_865 : subd15_2 [2, -1, 4] = true := by decide +kernel
theorem subd15_2_866 : subd15_2 [2, -1, 5] = true := by decide +kernel
theorem subd15_2_867 : subd15_2 [2, -1, 6] = true := by decide +kernel
theorem subd15_2_868 : subd15_2 [2, -1, 7] = true := by decide +kernel
theorem subd15_2_869 : subd15_2 [2, -1, 8] = true := by decide +kernel
theorem subd15_2_870 : subd15_2 [2, 0, -8] = true := by decide +kernel
theorem subd15_2_871 : subd15_2 [2, 0, -7] = true := by decide +kernel
theorem subd15_2_872 : subd15_2 [2, 0, -6] = true := by decide +kernel
theorem subd15_2_873 : subd15_2 [2, 0, -5] = true := by decide +kernel
theorem subd15_2_874 : subd15_2 [2, 0, -4] = true := by decide +kernel
theorem subd15_2_875 : subd15_2 [2, 0, -3] = true := by decide +kernel
theorem subd15_2_876 : subd15_2 [2, 0, -2] = true := by decide +kernel
theorem subd15_2_877 : subd15_2 [2, 0, -1] = true := by decide +kernel
theorem subd15_2_878 : subd15_2 [2, 0, 0] = true := by decide +kernel
theorem subd15_2_879 : subd15_2 [2, 0, 1] = true := by decide +kernel
theorem subd15_2_880 : subd15_2 [2, 0, 2] = true := by decide +kernel
theorem subd15_2_881 : subd15_2 [2, 0, 3] = true := by decide +kernel
theorem subd15_2_882 : subd15_2 [2, 0, 4] = true := by decide +kernel
theorem subd15_2_883 : subd15_2 [2, 0, 5] = true := by decide +kernel
theorem subd15_2_884 : subd15_2 [2, 0, 6] = true := by decide +kernel
theorem subd15_2_885 : subd15_2 [2, 0, 7] = true := by decide +kernel
theorem subd15_2_886 : subd15_2 [2, 0, 8] = true := by decide +kernel
theorem subd15_2_887 : subd15_2 [2, 1, -8] = true := by decide +kernel
theorem subd15_2_888 : subd15_2 [2, 1, -7] = true := by decide +kernel
theorem subd15_2_889 : subd15_2 [2, 1, -6] = true := by decide +kernel
theorem subd15_2_890 : subd15_2 [2, 1, -5] = true := by decide +kernel
theorem subd15_2_891 : subd15_2 [2, 1, -4] = true := by decide +kernel
theorem subd15_2_892 : subd15_2 [2, 1, -3] = true := by decide +kernel
theorem subd15_2_893 : subd15_2 [2, 1, -2] = true := by decide +kernel
theorem subd15_2_894 : subd15_2 [2, 1, -1] = true := by decide +kernel
theorem subd15_2_895 : subd15_2 [2, 1, 0] = true := by decide +kernel
theorem sbd15_2_27 : ∀ q ∈ blkd15_2_27, subd15_2 q = true := by
  unfold blkd15_2_27
  exact List.forall_mem_cons.2 ⟨subd15_2_864, List.forall_mem_cons.2 ⟨subd15_2_865, List.forall_mem_cons.2 ⟨subd15_2_866, List.forall_mem_cons.2 ⟨subd15_2_867, List.forall_mem_cons.2 ⟨subd15_2_868, List.forall_mem_cons.2 ⟨subd15_2_869, List.forall_mem_cons.2 ⟨subd15_2_870, List.forall_mem_cons.2 ⟨subd15_2_871, List.forall_mem_cons.2 ⟨subd15_2_872, List.forall_mem_cons.2 ⟨subd15_2_873, List.forall_mem_cons.2 ⟨subd15_2_874, List.forall_mem_cons.2 ⟨subd15_2_875, List.forall_mem_cons.2 ⟨subd15_2_876, List.forall_mem_cons.2 ⟨subd15_2_877, List.forall_mem_cons.2 ⟨subd15_2_878, List.forall_mem_cons.2 ⟨subd15_2_879, List.forall_mem_cons.2 ⟨subd15_2_880, List.forall_mem_cons.2 ⟨subd15_2_881, List.forall_mem_cons.2 ⟨subd15_2_882, List.forall_mem_cons.2 ⟨subd15_2_883, List.forall_mem_cons.2 ⟨subd15_2_884, List.forall_mem_cons.2 ⟨subd15_2_885, List.forall_mem_cons.2 ⟨subd15_2_886, List.forall_mem_cons.2 ⟨subd15_2_887, List.forall_mem_cons.2 ⟨subd15_2_888, List.forall_mem_cons.2 ⟨subd15_2_889, List.forall_mem_cons.2 ⟨subd15_2_890, List.forall_mem_cons.2 ⟨subd15_2_891, List.forall_mem_cons.2 ⟨subd15_2_892, List.forall_mem_cons.2 ⟨subd15_2_893, List.forall_mem_cons.2 ⟨subd15_2_894, List.forall_mem_cons.2 ⟨subd15_2_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_896 : subd15_2 [2, 1, 1] = true := by decide +kernel
theorem subd15_2_897 : subd15_2 [2, 1, 2] = true := by decide +kernel
theorem subd15_2_898 : subd15_2 [2, 1, 3] = true := by decide +kernel
theorem subd15_2_899 : subd15_2 [2, 1, 4] = true := by decide +kernel
theorem subd15_2_900 : subd15_2 [2, 1, 5] = true := by decide +kernel
theorem subd15_2_901 : subd15_2 [2, 1, 6] = true := by decide +kernel
theorem subd15_2_902 : subd15_2 [2, 1, 7] = true := by decide +kernel
theorem subd15_2_903 : subd15_2 [2, 1, 8] = true := by decide +kernel
theorem subd15_2_904 : subd15_2 [2, 1, 9] = true := by decide +kernel
theorem subd15_2_905 : subd15_2 [2, 2, -8] = true := by decide +kernel
theorem subd15_2_906 : subd15_2 [2, 2, -7] = true := by decide +kernel
theorem subd15_2_907 : subd15_2 [2, 2, -6] = true := by decide +kernel
theorem subd15_2_908 : subd15_2 [2, 2, -5] = true := by decide +kernel
theorem subd15_2_909 : subd15_2 [2, 2, -4] = true := by decide +kernel
theorem subd15_2_910 : subd15_2 [2, 2, -3] = true := by decide +kernel
theorem subd15_2_911 : subd15_2 [2, 2, -2] = true := by decide +kernel
theorem subd15_2_912 : subd15_2 [2, 2, -1] = true := by decide +kernel
theorem subd15_2_913 : subd15_2 [2, 2, 0] = true := by decide +kernel
theorem subd15_2_914 : subd15_2 [2, 2, 1] = true := by decide +kernel
theorem subd15_2_915 : subd15_2 [2, 2, 2] = true := by decide +kernel
theorem subd15_2_916 : subd15_2 [2, 2, 3] = true := by decide +kernel
theorem subd15_2_917 : subd15_2 [2, 2, 4] = true := by decide +kernel
theorem subd15_2_918 : subd15_2 [2, 2, 5] = true := by decide +kernel
theorem subd15_2_919 : subd15_2 [2, 2, 6] = true := by decide +kernel
theorem subd15_2_920 : subd15_2 [2, 2, 7] = true := by decide +kernel
theorem subd15_2_921 : subd15_2 [2, 2, 8] = true := by decide +kernel
theorem subd15_2_922 : subd15_2 [2, 3, -8] = true := by decide +kernel
theorem subd15_2_923 : subd15_2 [2, 3, -7] = true := by decide +kernel
theorem subd15_2_924 : subd15_2 [2, 3, -6] = true := by decide +kernel
theorem subd15_2_925 : subd15_2 [2, 3, -5] = true := by decide +kernel
theorem subd15_2_926 : subd15_2 [2, 3, -4] = true := by decide +kernel
theorem subd15_2_927 : subd15_2 [2, 3, -3] = true := by decide +kernel
theorem sbd15_2_28 : ∀ q ∈ blkd15_2_28, subd15_2 q = true := by
  unfold blkd15_2_28
  exact List.forall_mem_cons.2 ⟨subd15_2_896, List.forall_mem_cons.2 ⟨subd15_2_897, List.forall_mem_cons.2 ⟨subd15_2_898, List.forall_mem_cons.2 ⟨subd15_2_899, List.forall_mem_cons.2 ⟨subd15_2_900, List.forall_mem_cons.2 ⟨subd15_2_901, List.forall_mem_cons.2 ⟨subd15_2_902, List.forall_mem_cons.2 ⟨subd15_2_903, List.forall_mem_cons.2 ⟨subd15_2_904, List.forall_mem_cons.2 ⟨subd15_2_905, List.forall_mem_cons.2 ⟨subd15_2_906, List.forall_mem_cons.2 ⟨subd15_2_907, List.forall_mem_cons.2 ⟨subd15_2_908, List.forall_mem_cons.2 ⟨subd15_2_909, List.forall_mem_cons.2 ⟨subd15_2_910, List.forall_mem_cons.2 ⟨subd15_2_911, List.forall_mem_cons.2 ⟨subd15_2_912, List.forall_mem_cons.2 ⟨subd15_2_913, List.forall_mem_cons.2 ⟨subd15_2_914, List.forall_mem_cons.2 ⟨subd15_2_915, List.forall_mem_cons.2 ⟨subd15_2_916, List.forall_mem_cons.2 ⟨subd15_2_917, List.forall_mem_cons.2 ⟨subd15_2_918, List.forall_mem_cons.2 ⟨subd15_2_919, List.forall_mem_cons.2 ⟨subd15_2_920, List.forall_mem_cons.2 ⟨subd15_2_921, List.forall_mem_cons.2 ⟨subd15_2_922, List.forall_mem_cons.2 ⟨subd15_2_923, List.forall_mem_cons.2 ⟨subd15_2_924, List.forall_mem_cons.2 ⟨subd15_2_925, List.forall_mem_cons.2 ⟨subd15_2_926, List.forall_mem_cons.2 ⟨subd15_2_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_928 : subd15_2 [2, 3, -2] = true := by decide +kernel
theorem subd15_2_929 : subd15_2 [2, 3, -1] = true := by decide +kernel
theorem subd15_2_930 : subd15_2 [2, 3, 0] = true := by decide +kernel
theorem subd15_2_931 : subd15_2 [2, 3, 1] = true := by decide +kernel
theorem subd15_2_932 : subd15_2 [2, 3, 2] = true := by decide +kernel
theorem subd15_2_933 : subd15_2 [2, 3, 3] = true := by decide +kernel
theorem subd15_2_934 : subd15_2 [2, 3, 4] = true := by decide +kernel
theorem subd15_2_935 : subd15_2 [2, 3, 5] = true := by decide +kernel
theorem subd15_2_936 : subd15_2 [2, 3, 6] = true := by decide +kernel
theorem subd15_2_937 : subd15_2 [2, 3, 7] = true := by decide +kernel
theorem subd15_2_938 : subd15_2 [2, 3, 8] = true := by decide +kernel
theorem subd15_2_939 : subd15_2 [2, 4, -7] = true := by decide +kernel
theorem subd15_2_940 : subd15_2 [2, 4, -6] = true := by decide +kernel
theorem subd15_2_941 : subd15_2 [2, 4, -5] = true := by decide +kernel
theorem subd15_2_942 : subd15_2 [2, 4, -4] = true := by decide +kernel
theorem subd15_2_943 : subd15_2 [2, 4, -3] = true := by decide +kernel
theorem subd15_2_944 : subd15_2 [2, 4, -2] = true := by decide +kernel
theorem subd15_2_945 : subd15_2 [2, 4, -1] = true := by decide +kernel
theorem subd15_2_946 : subd15_2 [2, 4, 0] = true := by decide +kernel
theorem subd15_2_947 : subd15_2 [2, 4, 1] = true := by decide +kernel
theorem subd15_2_948 : subd15_2 [2, 4, 2] = true := by decide +kernel
theorem subd15_2_949 : subd15_2 [2, 4, 3] = true := by decide +kernel
theorem subd15_2_950 : subd15_2 [2, 4, 4] = true := by decide +kernel
theorem subd15_2_951 : subd15_2 [2, 4, 5] = true := by decide +kernel
theorem subd15_2_952 : subd15_2 [2, 4, 6] = true := by decide +kernel
theorem subd15_2_953 : subd15_2 [2, 4, 7] = true := by decide +kernel
theorem subd15_2_954 : subd15_2 [2, 4, 8] = true := by decide +kernel
theorem subd15_2_955 : subd15_2 [2, 5, -6] = true := by decide +kernel
theorem subd15_2_956 : subd15_2 [2, 5, -5] = true := by decide +kernel
theorem subd15_2_957 : subd15_2 [2, 5, -4] = true := by decide +kernel
theorem subd15_2_958 : subd15_2 [2, 5, -3] = true := by decide +kernel
theorem subd15_2_959 : subd15_2 [2, 5, -2] = true := by decide +kernel
theorem sbd15_2_29 : ∀ q ∈ blkd15_2_29, subd15_2 q = true := by
  unfold blkd15_2_29
  exact List.forall_mem_cons.2 ⟨subd15_2_928, List.forall_mem_cons.2 ⟨subd15_2_929, List.forall_mem_cons.2 ⟨subd15_2_930, List.forall_mem_cons.2 ⟨subd15_2_931, List.forall_mem_cons.2 ⟨subd15_2_932, List.forall_mem_cons.2 ⟨subd15_2_933, List.forall_mem_cons.2 ⟨subd15_2_934, List.forall_mem_cons.2 ⟨subd15_2_935, List.forall_mem_cons.2 ⟨subd15_2_936, List.forall_mem_cons.2 ⟨subd15_2_937, List.forall_mem_cons.2 ⟨subd15_2_938, List.forall_mem_cons.2 ⟨subd15_2_939, List.forall_mem_cons.2 ⟨subd15_2_940, List.forall_mem_cons.2 ⟨subd15_2_941, List.forall_mem_cons.2 ⟨subd15_2_942, List.forall_mem_cons.2 ⟨subd15_2_943, List.forall_mem_cons.2 ⟨subd15_2_944, List.forall_mem_cons.2 ⟨subd15_2_945, List.forall_mem_cons.2 ⟨subd15_2_946, List.forall_mem_cons.2 ⟨subd15_2_947, List.forall_mem_cons.2 ⟨subd15_2_948, List.forall_mem_cons.2 ⟨subd15_2_949, List.forall_mem_cons.2 ⟨subd15_2_950, List.forall_mem_cons.2 ⟨subd15_2_951, List.forall_mem_cons.2 ⟨subd15_2_952, List.forall_mem_cons.2 ⟨subd15_2_953, List.forall_mem_cons.2 ⟨subd15_2_954, List.forall_mem_cons.2 ⟨subd15_2_955, List.forall_mem_cons.2 ⟨subd15_2_956, List.forall_mem_cons.2 ⟨subd15_2_957, List.forall_mem_cons.2 ⟨subd15_2_958, List.forall_mem_cons.2 ⟨subd15_2_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_960 : subd15_2 [2, 5, -1] = true := by decide +kernel
theorem subd15_2_961 : subd15_2 [2, 5, 0] = true := by decide +kernel
theorem subd15_2_962 : subd15_2 [2, 5, 1] = true := by decide +kernel
theorem subd15_2_963 : subd15_2 [2, 5, 2] = true := by decide +kernel
theorem subd15_2_964 : subd15_2 [2, 5, 3] = true := by decide +kernel
theorem subd15_2_965 : subd15_2 [2, 5, 4] = true := by decide +kernel
theorem subd15_2_966 : subd15_2 [2, 5, 5] = true := by decide +kernel
theorem subd15_2_967 : subd15_2 [2, 5, 6] = true := by decide +kernel
theorem subd15_2_968 : subd15_2 [2, 5, 7] = true := by decide +kernel
theorem subd15_2_969 : subd15_2 [2, 6] = true := by decide +kernel
theorem subd15_2_970 : subd15_2 [2, 7] = true := by decide +kernel
theorem subd15_2_971 : subd15_2 [3, -5] = true := by decide +kernel
theorem subd15_2_972 : subd15_2 [3, -4] = true := by decide +kernel
theorem subd15_2_973 : subd15_2 [3, -3] = true := by decide +kernel
theorem subd15_2_974 : subd15_2 [3, -2] = true := by decide +kernel
theorem subd15_2_975 : subd15_2 [3, -1, -7] = true := by decide +kernel
theorem subd15_2_976 : subd15_2 [3, -1, -6] = true := by decide +kernel
theorem subd15_2_977 : subd15_2 [3, -1, -5] = true := by decide +kernel
theorem subd15_2_978 : subd15_2 [3, -1, -4] = true := by decide +kernel
theorem subd15_2_979 : subd15_2 [3, -1, -3] = true := by decide +kernel
theorem subd15_2_980 : subd15_2 [3, -1, -2] = true := by decide +kernel
theorem subd15_2_981 : subd15_2 [3, -1, -1] = true := by decide +kernel
theorem subd15_2_982 : subd15_2 [3, -1, 0] = true := by decide +kernel
theorem subd15_2_983 : subd15_2 [3, -1, 1] = true := by decide +kernel
theorem subd15_2_984 : subd15_2 [3, -1, 2] = true := by decide +kernel
theorem subd15_2_985 : subd15_2 [3, -1, 3] = true := by decide +kernel
theorem subd15_2_986 : subd15_2 [3, -1, 4] = true := by decide +kernel
theorem subd15_2_987 : subd15_2 [3, -1, 5] = true := by decide +kernel
theorem subd15_2_988 : subd15_2 [3, -1, 6] = true := by decide +kernel
theorem subd15_2_989 : subd15_2 [3, -1, 7] = true := by decide +kernel
theorem subd15_2_990 : subd15_2 [3, 0, -7] = true := by decide +kernel
theorem subd15_2_991 : subd15_2 [3, 0, -6] = true := by decide +kernel
theorem sbd15_2_30 : ∀ q ∈ blkd15_2_30, subd15_2 q = true := by
  unfold blkd15_2_30
  exact List.forall_mem_cons.2 ⟨subd15_2_960, List.forall_mem_cons.2 ⟨subd15_2_961, List.forall_mem_cons.2 ⟨subd15_2_962, List.forall_mem_cons.2 ⟨subd15_2_963, List.forall_mem_cons.2 ⟨subd15_2_964, List.forall_mem_cons.2 ⟨subd15_2_965, List.forall_mem_cons.2 ⟨subd15_2_966, List.forall_mem_cons.2 ⟨subd15_2_967, List.forall_mem_cons.2 ⟨subd15_2_968, List.forall_mem_cons.2 ⟨subd15_2_969, List.forall_mem_cons.2 ⟨subd15_2_970, List.forall_mem_cons.2 ⟨subd15_2_971, List.forall_mem_cons.2 ⟨subd15_2_972, List.forall_mem_cons.2 ⟨subd15_2_973, List.forall_mem_cons.2 ⟨subd15_2_974, List.forall_mem_cons.2 ⟨subd15_2_975, List.forall_mem_cons.2 ⟨subd15_2_976, List.forall_mem_cons.2 ⟨subd15_2_977, List.forall_mem_cons.2 ⟨subd15_2_978, List.forall_mem_cons.2 ⟨subd15_2_979, List.forall_mem_cons.2 ⟨subd15_2_980, List.forall_mem_cons.2 ⟨subd15_2_981, List.forall_mem_cons.2 ⟨subd15_2_982, List.forall_mem_cons.2 ⟨subd15_2_983, List.forall_mem_cons.2 ⟨subd15_2_984, List.forall_mem_cons.2 ⟨subd15_2_985, List.forall_mem_cons.2 ⟨subd15_2_986, List.forall_mem_cons.2 ⟨subd15_2_987, List.forall_mem_cons.2 ⟨subd15_2_988, List.forall_mem_cons.2 ⟨subd15_2_989, List.forall_mem_cons.2 ⟨subd15_2_990, List.forall_mem_cons.2 ⟨subd15_2_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_992 : subd15_2 [3, 0, -5] = true := by decide +kernel
theorem subd15_2_993 : subd15_2 [3, 0, -4] = true := by decide +kernel
theorem subd15_2_994 : subd15_2 [3, 0, -3] = true := by decide +kernel
theorem subd15_2_995 : subd15_2 [3, 0, -2] = true := by decide +kernel
theorem subd15_2_996 : subd15_2 [3, 0, -1] = true := by decide +kernel
theorem subd15_2_997 : subd15_2 [3, 0, 0] = true := by decide +kernel
theorem subd15_2_998 : subd15_2 [3, 0, 1] = true := by decide +kernel
theorem subd15_2_999 : subd15_2 [3, 0, 2] = true := by decide +kernel
theorem subd15_2_1000 : subd15_2 [3, 0, 3] = true := by decide +kernel
theorem subd15_2_1001 : subd15_2 [3, 0, 4] = true := by decide +kernel
theorem subd15_2_1002 : subd15_2 [3, 0, 5] = true := by decide +kernel
theorem subd15_2_1003 : subd15_2 [3, 0, 6] = true := by decide +kernel
theorem subd15_2_1004 : subd15_2 [3, 0, 7] = true := by decide +kernel
theorem subd15_2_1005 : subd15_2 [3, 0, 8] = true := by decide +kernel
theorem subd15_2_1006 : subd15_2 [3, 1, -7] = true := by decide +kernel
theorem subd15_2_1007 : subd15_2 [3, 1, -6] = true := by decide +kernel
theorem subd15_2_1008 : subd15_2 [3, 1, -5] = true := by decide +kernel
theorem subd15_2_1009 : subd15_2 [3, 1, -4] = true := by decide +kernel
theorem subd15_2_1010 : subd15_2 [3, 1, -3] = true := by decide +kernel
theorem subd15_2_1011 : subd15_2 [3, 1, -2] = true := by decide +kernel
theorem subd15_2_1012 : subd15_2 [3, 1, -1] = true := by decide +kernel
theorem subd15_2_1013 : subd15_2 [3, 1, 0] = true := by decide +kernel
theorem subd15_2_1014 : subd15_2 [3, 1, 1] = true := by decide +kernel
theorem subd15_2_1015 : subd15_2 [3, 1, 2] = true := by decide +kernel
theorem subd15_2_1016 : subd15_2 [3, 1, 3] = true := by decide +kernel
theorem subd15_2_1017 : subd15_2 [3, 1, 4] = true := by decide +kernel
theorem subd15_2_1018 : subd15_2 [3, 1, 5] = true := by decide +kernel
theorem subd15_2_1019 : subd15_2 [3, 1, 6] = true := by decide +kernel
theorem subd15_2_1020 : subd15_2 [3, 1, 7] = true := by decide +kernel
theorem subd15_2_1021 : subd15_2 [3, 1, 8] = true := by decide +kernel
theorem subd15_2_1022 : subd15_2 [3, 2, -7] = true := by decide +kernel
theorem subd15_2_1023 : subd15_2 [3, 2, -6] = true := by decide +kernel
theorem sbd15_2_31 : ∀ q ∈ blkd15_2_31, subd15_2 q = true := by
  unfold blkd15_2_31
  exact List.forall_mem_cons.2 ⟨subd15_2_992, List.forall_mem_cons.2 ⟨subd15_2_993, List.forall_mem_cons.2 ⟨subd15_2_994, List.forall_mem_cons.2 ⟨subd15_2_995, List.forall_mem_cons.2 ⟨subd15_2_996, List.forall_mem_cons.2 ⟨subd15_2_997, List.forall_mem_cons.2 ⟨subd15_2_998, List.forall_mem_cons.2 ⟨subd15_2_999, List.forall_mem_cons.2 ⟨subd15_2_1000, List.forall_mem_cons.2 ⟨subd15_2_1001, List.forall_mem_cons.2 ⟨subd15_2_1002, List.forall_mem_cons.2 ⟨subd15_2_1003, List.forall_mem_cons.2 ⟨subd15_2_1004, List.forall_mem_cons.2 ⟨subd15_2_1005, List.forall_mem_cons.2 ⟨subd15_2_1006, List.forall_mem_cons.2 ⟨subd15_2_1007, List.forall_mem_cons.2 ⟨subd15_2_1008, List.forall_mem_cons.2 ⟨subd15_2_1009, List.forall_mem_cons.2 ⟨subd15_2_1010, List.forall_mem_cons.2 ⟨subd15_2_1011, List.forall_mem_cons.2 ⟨subd15_2_1012, List.forall_mem_cons.2 ⟨subd15_2_1013, List.forall_mem_cons.2 ⟨subd15_2_1014, List.forall_mem_cons.2 ⟨subd15_2_1015, List.forall_mem_cons.2 ⟨subd15_2_1016, List.forall_mem_cons.2 ⟨subd15_2_1017, List.forall_mem_cons.2 ⟨subd15_2_1018, List.forall_mem_cons.2 ⟨subd15_2_1019, List.forall_mem_cons.2 ⟨subd15_2_1020, List.forall_mem_cons.2 ⟨subd15_2_1021, List.forall_mem_cons.2 ⟨subd15_2_1022, List.forall_mem_cons.2 ⟨subd15_2_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_1024 : subd15_2 [3, 2, -5] = true := by decide +kernel
theorem subd15_2_1025 : subd15_2 [3, 2, -4] = true := by decide +kernel
theorem subd15_2_1026 : subd15_2 [3, 2, -3] = true := by decide +kernel
theorem subd15_2_1027 : subd15_2 [3, 2, -2] = true := by decide +kernel
theorem subd15_2_1028 : subd15_2 [3, 2, -1] = true := by decide +kernel
theorem subd15_2_1029 : subd15_2 [3, 2, 0] = true := by decide +kernel
theorem subd15_2_1030 : subd15_2 [3, 2, 1] = true := by decide +kernel
theorem subd15_2_1031 : subd15_2 [3, 2, 2] = true := by decide +kernel
theorem subd15_2_1032 : subd15_2 [3, 2, 3] = true := by decide +kernel
theorem subd15_2_1033 : subd15_2 [3, 2, 4] = true := by decide +kernel
theorem subd15_2_1034 : subd15_2 [3, 2, 5] = true := by decide +kernel
theorem subd15_2_1035 : subd15_2 [3, 2, 6] = true := by decide +kernel
theorem subd15_2_1036 : subd15_2 [3, 2, 7] = true := by decide +kernel
theorem subd15_2_1037 : subd15_2 [3, 2, 8] = true := by decide +kernel
theorem subd15_2_1038 : subd15_2 [3, 3, -7] = true := by decide +kernel
theorem subd15_2_1039 : subd15_2 [3, 3, -6] = true := by decide +kernel
theorem subd15_2_1040 : subd15_2 [3, 3, -5] = true := by decide +kernel
theorem subd15_2_1041 : subd15_2 [3, 3, -4] = true := by decide +kernel
theorem subd15_2_1042 : subd15_2 [3, 3, -3] = true := by decide +kernel
theorem subd15_2_1043 : subd15_2 [3, 3, -2] = true := by decide +kernel
theorem subd15_2_1044 : subd15_2 [3, 3, -1] = true := by decide +kernel
theorem subd15_2_1045 : subd15_2 [3, 3, 0] = true := by decide +kernel
theorem subd15_2_1046 : subd15_2 [3, 3, 1] = true := by decide +kernel
theorem subd15_2_1047 : subd15_2 [3, 3, 2] = true := by decide +kernel
theorem subd15_2_1048 : subd15_2 [3, 3, 3] = true := by decide +kernel
theorem subd15_2_1049 : subd15_2 [3, 3, 4] = true := by decide +kernel
theorem subd15_2_1050 : subd15_2 [3, 3, 5] = true := by decide +kernel
theorem subd15_2_1051 : subd15_2 [3, 3, 6] = true := by decide +kernel
theorem subd15_2_1052 : subd15_2 [3, 3, 7] = true := by decide +kernel
theorem subd15_2_1053 : subd15_2 [3, 3, 8] = true := by decide +kernel
theorem subd15_2_1054 : subd15_2 [3, 4, -7] = true := by decide +kernel
theorem subd15_2_1055 : subd15_2 [3, 4, -6] = true := by decide +kernel
theorem sbd15_2_32 : ∀ q ∈ blkd15_2_32, subd15_2 q = true := by
  unfold blkd15_2_32
  exact List.forall_mem_cons.2 ⟨subd15_2_1024, List.forall_mem_cons.2 ⟨subd15_2_1025, List.forall_mem_cons.2 ⟨subd15_2_1026, List.forall_mem_cons.2 ⟨subd15_2_1027, List.forall_mem_cons.2 ⟨subd15_2_1028, List.forall_mem_cons.2 ⟨subd15_2_1029, List.forall_mem_cons.2 ⟨subd15_2_1030, List.forall_mem_cons.2 ⟨subd15_2_1031, List.forall_mem_cons.2 ⟨subd15_2_1032, List.forall_mem_cons.2 ⟨subd15_2_1033, List.forall_mem_cons.2 ⟨subd15_2_1034, List.forall_mem_cons.2 ⟨subd15_2_1035, List.forall_mem_cons.2 ⟨subd15_2_1036, List.forall_mem_cons.2 ⟨subd15_2_1037, List.forall_mem_cons.2 ⟨subd15_2_1038, List.forall_mem_cons.2 ⟨subd15_2_1039, List.forall_mem_cons.2 ⟨subd15_2_1040, List.forall_mem_cons.2 ⟨subd15_2_1041, List.forall_mem_cons.2 ⟨subd15_2_1042, List.forall_mem_cons.2 ⟨subd15_2_1043, List.forall_mem_cons.2 ⟨subd15_2_1044, List.forall_mem_cons.2 ⟨subd15_2_1045, List.forall_mem_cons.2 ⟨subd15_2_1046, List.forall_mem_cons.2 ⟨subd15_2_1047, List.forall_mem_cons.2 ⟨subd15_2_1048, List.forall_mem_cons.2 ⟨subd15_2_1049, List.forall_mem_cons.2 ⟨subd15_2_1050, List.forall_mem_cons.2 ⟨subd15_2_1051, List.forall_mem_cons.2 ⟨subd15_2_1052, List.forall_mem_cons.2 ⟨subd15_2_1053, List.forall_mem_cons.2 ⟨subd15_2_1054, List.forall_mem_cons.2 ⟨subd15_2_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
