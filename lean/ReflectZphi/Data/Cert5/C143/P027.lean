import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_2_608 : subd14_2 [2, -3, -2] = true := by decide +kernel
theorem subd14_2_609 : subd14_2 [2, -3, -1] = true := by decide +kernel
theorem subd14_2_610 : subd14_2 [2, -3, 0] = true := by decide +kernel
theorem subd14_2_611 : subd14_2 [2, -3, 1] = true := by decide +kernel
theorem subd14_2_612 : subd14_2 [2, -3, 2] = true := by decide +kernel
theorem subd14_2_613 : subd14_2 [2, -3, 3] = true := by decide +kernel
theorem subd14_2_614 : subd14_2 [2, -3, 4] = true := by decide +kernel
theorem subd14_2_615 : subd14_2 [2, -3, 5] = true := by decide +kernel
theorem subd14_2_616 : subd14_2 [2, -3, 6] = true := by decide +kernel
theorem subd14_2_617 : subd14_2 [2, -3, 7] = true := by decide +kernel
theorem subd14_2_618 : subd14_2 [2, -3, 8] = true := by decide +kernel
theorem subd14_2_619 : subd14_2 [2, -2, -8] = true := by decide +kernel
theorem subd14_2_620 : subd14_2 [2, -2, -7] = true := by decide +kernel
theorem subd14_2_621 : subd14_2 [2, -2, -6] = true := by decide +kernel
theorem subd14_2_622 : subd14_2 [2, -2, -5] = true := by decide +kernel
theorem subd14_2_623 : subd14_2 [2, -2, -4] = true := by decide +kernel
theorem subd14_2_624 : subd14_2 [2, -2, -3] = true := by decide +kernel
theorem subd14_2_625 : subd14_2 [2, -2, -2] = true := by decide +kernel
theorem subd14_2_626 : subd14_2 [2, -2, -1] = true := by decide +kernel
theorem subd14_2_627 : subd14_2 [2, -2, 0] = true := by decide +kernel
theorem subd14_2_628 : subd14_2 [2, -2, 1] = true := by decide +kernel
theorem subd14_2_629 : subd14_2 [2, -2, 2] = true := by decide +kernel
theorem subd14_2_630 : subd14_2 [2, -2, 3] = true := by decide +kernel
theorem subd14_2_631 : subd14_2 [2, -2, 4] = true := by decide +kernel
theorem subd14_2_632 : subd14_2 [2, -2, 5] = true := by decide +kernel
theorem subd14_2_633 : subd14_2 [2, -2, 6] = true := by decide +kernel
theorem subd14_2_634 : subd14_2 [2, -2, 7] = true := by decide +kernel
theorem subd14_2_635 : subd14_2 [2, -2, 8] = true := by decide +kernel
theorem subd14_2_636 : subd14_2 [2, -2, 9] = true := by decide +kernel
theorem subd14_2_637 : subd14_2 [2, -1, -9] = true := by decide +kernel
theorem subd14_2_638 : subd14_2 [2, -1, -8] = true := by decide +kernel
theorem subd14_2_639 : subd14_2 [2, -1, -7] = true := by decide +kernel
theorem sbd14_2_19 : ∀ q ∈ blkd14_2_19, subd14_2 q = true := by
  unfold blkd14_2_19
  exact List.forall_mem_cons.2 ⟨subd14_2_608, List.forall_mem_cons.2 ⟨subd14_2_609, List.forall_mem_cons.2 ⟨subd14_2_610, List.forall_mem_cons.2 ⟨subd14_2_611, List.forall_mem_cons.2 ⟨subd14_2_612, List.forall_mem_cons.2 ⟨subd14_2_613, List.forall_mem_cons.2 ⟨subd14_2_614, List.forall_mem_cons.2 ⟨subd14_2_615, List.forall_mem_cons.2 ⟨subd14_2_616, List.forall_mem_cons.2 ⟨subd14_2_617, List.forall_mem_cons.2 ⟨subd14_2_618, List.forall_mem_cons.2 ⟨subd14_2_619, List.forall_mem_cons.2 ⟨subd14_2_620, List.forall_mem_cons.2 ⟨subd14_2_621, List.forall_mem_cons.2 ⟨subd14_2_622, List.forall_mem_cons.2 ⟨subd14_2_623, List.forall_mem_cons.2 ⟨subd14_2_624, List.forall_mem_cons.2 ⟨subd14_2_625, List.forall_mem_cons.2 ⟨subd14_2_626, List.forall_mem_cons.2 ⟨subd14_2_627, List.forall_mem_cons.2 ⟨subd14_2_628, List.forall_mem_cons.2 ⟨subd14_2_629, List.forall_mem_cons.2 ⟨subd14_2_630, List.forall_mem_cons.2 ⟨subd14_2_631, List.forall_mem_cons.2 ⟨subd14_2_632, List.forall_mem_cons.2 ⟨subd14_2_633, List.forall_mem_cons.2 ⟨subd14_2_634, List.forall_mem_cons.2 ⟨subd14_2_635, List.forall_mem_cons.2 ⟨subd14_2_636, List.forall_mem_cons.2 ⟨subd14_2_637, List.forall_mem_cons.2 ⟨subd14_2_638, List.forall_mem_cons.2 ⟨subd14_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_640 : subd14_2 [2, -1, -6] = true := by decide +kernel
theorem subd14_2_641 : subd14_2 [2, -1, -5] = true := by decide +kernel
theorem subd14_2_642 : subd14_2 [2, -1, -4] = true := by decide +kernel
theorem subd14_2_643 : subd14_2 [2, -1, -3] = true := by decide +kernel
theorem subd14_2_644 : subd14_2 [2, -1, -2] = true := by decide +kernel
theorem subd14_2_645 : subd14_2 [2, -1, -1] = true := by decide +kernel
theorem subd14_2_646 : subd14_2 [2, -1, 0] = true := by decide +kernel
theorem subd14_2_647 : subd14_2 [2, -1, 1] = true := by decide +kernel
theorem subd14_2_648 : subd14_2 [2, -1, 2] = true := by decide +kernel
theorem subd14_2_649 : subd14_2 [2, -1, 3] = true := by decide +kernel
theorem subd14_2_650 : subd14_2 [2, -1, 4] = true := by decide +kernel
theorem subd14_2_651 : subd14_2 [2, -1, 5] = true := by decide +kernel
theorem subd14_2_652 : subd14_2 [2, -1, 6] = true := by decide +kernel
theorem subd14_2_653 : subd14_2 [2, -1, 7] = true := by decide +kernel
theorem subd14_2_654 : subd14_2 [2, -1, 8] = true := by decide +kernel
theorem subd14_2_655 : subd14_2 [2, -1, 9] = true := by decide +kernel
theorem subd14_2_656 : subd14_2 [2, 0, -9] = true := by decide +kernel
theorem subd14_2_657 : subd14_2 [2, 0, -8] = true := by decide +kernel
theorem subd14_2_658 : subd14_2 [2, 0, -7] = true := by decide +kernel
theorem subd14_2_659 : subd14_2 [2, 0, -6] = true := by decide +kernel
theorem subd14_2_660 : subd14_2 [2, 0, -5] = true := by decide +kernel
theorem subd14_2_661 : subd14_2 [2, 0, -4] = true := by decide +kernel
theorem subd14_2_662 : subd14_2 [2, 0, -3] = true := by decide +kernel
theorem subd14_2_663 : subd14_2 [2, 0, -2] = true := by decide +kernel
theorem subd14_2_664 : subd14_2 [2, 0, -1] = true := by decide +kernel
theorem subd14_2_665 : subd14_2 [2, 0, 0] = true := by decide +kernel
theorem subd14_2_666 : subd14_2 [2, 0, 1] = true := by decide +kernel
theorem subd14_2_667 : subd14_2 [2, 0, 2] = true := by decide +kernel
theorem subd14_2_668 : subd14_2 [2, 0, 3] = true := by decide +kernel
theorem subd14_2_669 : subd14_2 [2, 0, 4] = true := by decide +kernel
theorem subd14_2_670 : subd14_2 [2, 0, 5] = true := by decide +kernel
theorem subd14_2_671 : subd14_2 [2, 0, 6] = true := by decide +kernel
theorem sbd14_2_20 : ∀ q ∈ blkd14_2_20, subd14_2 q = true := by
  unfold blkd14_2_20
  exact List.forall_mem_cons.2 ⟨subd14_2_640, List.forall_mem_cons.2 ⟨subd14_2_641, List.forall_mem_cons.2 ⟨subd14_2_642, List.forall_mem_cons.2 ⟨subd14_2_643, List.forall_mem_cons.2 ⟨subd14_2_644, List.forall_mem_cons.2 ⟨subd14_2_645, List.forall_mem_cons.2 ⟨subd14_2_646, List.forall_mem_cons.2 ⟨subd14_2_647, List.forall_mem_cons.2 ⟨subd14_2_648, List.forall_mem_cons.2 ⟨subd14_2_649, List.forall_mem_cons.2 ⟨subd14_2_650, List.forall_mem_cons.2 ⟨subd14_2_651, List.forall_mem_cons.2 ⟨subd14_2_652, List.forall_mem_cons.2 ⟨subd14_2_653, List.forall_mem_cons.2 ⟨subd14_2_654, List.forall_mem_cons.2 ⟨subd14_2_655, List.forall_mem_cons.2 ⟨subd14_2_656, List.forall_mem_cons.2 ⟨subd14_2_657, List.forall_mem_cons.2 ⟨subd14_2_658, List.forall_mem_cons.2 ⟨subd14_2_659, List.forall_mem_cons.2 ⟨subd14_2_660, List.forall_mem_cons.2 ⟨subd14_2_661, List.forall_mem_cons.2 ⟨subd14_2_662, List.forall_mem_cons.2 ⟨subd14_2_663, List.forall_mem_cons.2 ⟨subd14_2_664, List.forall_mem_cons.2 ⟨subd14_2_665, List.forall_mem_cons.2 ⟨subd14_2_666, List.forall_mem_cons.2 ⟨subd14_2_667, List.forall_mem_cons.2 ⟨subd14_2_668, List.forall_mem_cons.2 ⟨subd14_2_669, List.forall_mem_cons.2 ⟨subd14_2_670, List.forall_mem_cons.2 ⟨subd14_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_672 : subd14_2 [2, 0, 7] = true := by decide +kernel
theorem subd14_2_673 : subd14_2 [2, 0, 8] = true := by decide +kernel
theorem subd14_2_674 : subd14_2 [2, 0, 9] = true := by decide +kernel
theorem subd14_2_675 : subd14_2 [2, 1, -9] = true := by decide +kernel
theorem subd14_2_676 : subd14_2 [2, 1, -8] = true := by decide +kernel
theorem subd14_2_677 : subd14_2 [2, 1, -7] = true := by decide +kernel
theorem subd14_2_678 : subd14_2 [2, 1, -6] = true := by decide +kernel
theorem subd14_2_679 : subd14_2 [2, 1, -5] = true := by decide +kernel
theorem subd14_2_680 : subd14_2 [2, 1, -4] = true := by decide +kernel
theorem subd14_2_681 : subd14_2 [2, 1, -3] = true := by decide +kernel
theorem subd14_2_682 : subd14_2 [2, 1, -2] = true := by decide +kernel
theorem subd14_2_683 : subd14_2 [2, 1, -1] = true := by decide +kernel
theorem subd14_2_684 : subd14_2 [2, 1, 0] = true := by decide +kernel
theorem subd14_2_685 : subd14_2 [2, 1, 1] = true := by decide +kernel
theorem subd14_2_686 : subd14_2 [2, 1, 2] = true := by decide +kernel
theorem subd14_2_687 : subd14_2 [2, 1, 3] = true := by decide +kernel
theorem subd14_2_688 : subd14_2 [2, 1, 4] = true := by decide +kernel
theorem subd14_2_689 : subd14_2 [2, 1, 5] = true := by decide +kernel
theorem subd14_2_690 : subd14_2 [2, 1, 6] = true := by decide +kernel
theorem subd14_2_691 : subd14_2 [2, 1, 7] = true := by decide +kernel
theorem subd14_2_692 : subd14_2 [2, 1, 8] = true := by decide +kernel
theorem subd14_2_693 : subd14_2 [2, 1, 9] = true := by decide +kernel
theorem subd14_2_694 : subd14_2 [2, 2, -8] = true := by decide +kernel
theorem subd14_2_695 : subd14_2 [2, 2, -7] = true := by decide +kernel
theorem subd14_2_696 : subd14_2 [2, 2, -6] = true := by decide +kernel
theorem subd14_2_697 : subd14_2 [2, 2, -5] = true := by decide +kernel
theorem subd14_2_698 : subd14_2 [2, 2, -4] = true := by decide +kernel
theorem subd14_2_699 : subd14_2 [2, 2, -3] = true := by decide +kernel
theorem subd14_2_700 : subd14_2 [2, 2, -2] = true := by decide +kernel
theorem subd14_2_701 : subd14_2 [2, 2, -1] = true := by decide +kernel
theorem subd14_2_702 : subd14_2 [2, 2, 0] = true := by decide +kernel
theorem subd14_2_703 : subd14_2 [2, 2, 1] = true := by decide +kernel
theorem sbd14_2_21 : ∀ q ∈ blkd14_2_21, subd14_2 q = true := by
  unfold blkd14_2_21
  exact List.forall_mem_cons.2 ⟨subd14_2_672, List.forall_mem_cons.2 ⟨subd14_2_673, List.forall_mem_cons.2 ⟨subd14_2_674, List.forall_mem_cons.2 ⟨subd14_2_675, List.forall_mem_cons.2 ⟨subd14_2_676, List.forall_mem_cons.2 ⟨subd14_2_677, List.forall_mem_cons.2 ⟨subd14_2_678, List.forall_mem_cons.2 ⟨subd14_2_679, List.forall_mem_cons.2 ⟨subd14_2_680, List.forall_mem_cons.2 ⟨subd14_2_681, List.forall_mem_cons.2 ⟨subd14_2_682, List.forall_mem_cons.2 ⟨subd14_2_683, List.forall_mem_cons.2 ⟨subd14_2_684, List.forall_mem_cons.2 ⟨subd14_2_685, List.forall_mem_cons.2 ⟨subd14_2_686, List.forall_mem_cons.2 ⟨subd14_2_687, List.forall_mem_cons.2 ⟨subd14_2_688, List.forall_mem_cons.2 ⟨subd14_2_689, List.forall_mem_cons.2 ⟨subd14_2_690, List.forall_mem_cons.2 ⟨subd14_2_691, List.forall_mem_cons.2 ⟨subd14_2_692, List.forall_mem_cons.2 ⟨subd14_2_693, List.forall_mem_cons.2 ⟨subd14_2_694, List.forall_mem_cons.2 ⟨subd14_2_695, List.forall_mem_cons.2 ⟨subd14_2_696, List.forall_mem_cons.2 ⟨subd14_2_697, List.forall_mem_cons.2 ⟨subd14_2_698, List.forall_mem_cons.2 ⟨subd14_2_699, List.forall_mem_cons.2 ⟨subd14_2_700, List.forall_mem_cons.2 ⟨subd14_2_701, List.forall_mem_cons.2 ⟨subd14_2_702, List.forall_mem_cons.2 ⟨subd14_2_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_704 : subd14_2 [2, 2, 2] = true := by decide +kernel
theorem subd14_2_705 : subd14_2 [2, 2, 3] = true := by decide +kernel
theorem subd14_2_706 : subd14_2 [2, 2, 4] = true := by decide +kernel
theorem subd14_2_707 : subd14_2 [2, 2, 5] = true := by decide +kernel
theorem subd14_2_708 : subd14_2 [2, 2, 6] = true := by decide +kernel
theorem subd14_2_709 : subd14_2 [2, 2, 7] = true := by decide +kernel
theorem subd14_2_710 : subd14_2 [2, 2, 8] = true := by decide +kernel
theorem subd14_2_711 : subd14_2 [2, 3] = true := by decide +kernel
theorem subd14_2_712 : subd14_2 [2, 4] = true := by decide +kernel
theorem subd14_2_713 : subd14_2 [3, -5] = true := by decide +kernel
theorem subd14_2_714 : subd14_2 [3, -4] = true := by decide +kernel
theorem subd14_2_715 : subd14_2 [3, -3] = true := by decide +kernel
theorem subd14_2_716 : subd14_2 [3, -2, -7] = true := by decide +kernel
theorem subd14_2_717 : subd14_2 [3, -2, -6] = true := by decide +kernel
theorem subd14_2_718 : subd14_2 [3, -2, -5] = true := by decide +kernel
theorem subd14_2_719 : subd14_2 [3, -2, -4] = true := by decide +kernel
theorem subd14_2_720 : subd14_2 [3, -2, -3] = true := by decide +kernel
theorem subd14_2_721 : subd14_2 [3, -2, -2] = true := by decide +kernel
theorem subd14_2_722 : subd14_2 [3, -2, -1] = true := by decide +kernel
theorem subd14_2_723 : subd14_2 [3, -2, 0] = true := by decide +kernel
theorem subd14_2_724 : subd14_2 [3, -2, 1] = true := by decide +kernel
theorem subd14_2_725 : subd14_2 [3, -2, 2] = true := by decide +kernel
theorem subd14_2_726 : subd14_2 [3, -2, 3] = true := by decide +kernel
theorem subd14_2_727 : subd14_2 [3, -2, 4] = true := by decide +kernel
theorem subd14_2_728 : subd14_2 [3, -2, 5] = true := by decide +kernel
theorem subd14_2_729 : subd14_2 [3, -2, 6] = true := by decide +kernel
theorem subd14_2_730 : subd14_2 [3, -2, 7] = true := by decide +kernel
theorem subd14_2_731 : subd14_2 [3, -2, 8] = true := by decide +kernel
theorem subd14_2_732 : subd14_2 [3, -1, -7] = true := by decide +kernel
theorem subd14_2_733 : subd14_2 [3, -1, -6] = true := by decide +kernel
theorem subd14_2_734 : subd14_2 [3, -1, -5] = true := by decide +kernel
theorem subd14_2_735 : subd14_2 [3, -1, -4] = true := by decide +kernel
theorem sbd14_2_22 : ∀ q ∈ blkd14_2_22, subd14_2 q = true := by
  unfold blkd14_2_22
  exact List.forall_mem_cons.2 ⟨subd14_2_704, List.forall_mem_cons.2 ⟨subd14_2_705, List.forall_mem_cons.2 ⟨subd14_2_706, List.forall_mem_cons.2 ⟨subd14_2_707, List.forall_mem_cons.2 ⟨subd14_2_708, List.forall_mem_cons.2 ⟨subd14_2_709, List.forall_mem_cons.2 ⟨subd14_2_710, List.forall_mem_cons.2 ⟨subd14_2_711, List.forall_mem_cons.2 ⟨subd14_2_712, List.forall_mem_cons.2 ⟨subd14_2_713, List.forall_mem_cons.2 ⟨subd14_2_714, List.forall_mem_cons.2 ⟨subd14_2_715, List.forall_mem_cons.2 ⟨subd14_2_716, List.forall_mem_cons.2 ⟨subd14_2_717, List.forall_mem_cons.2 ⟨subd14_2_718, List.forall_mem_cons.2 ⟨subd14_2_719, List.forall_mem_cons.2 ⟨subd14_2_720, List.forall_mem_cons.2 ⟨subd14_2_721, List.forall_mem_cons.2 ⟨subd14_2_722, List.forall_mem_cons.2 ⟨subd14_2_723, List.forall_mem_cons.2 ⟨subd14_2_724, List.forall_mem_cons.2 ⟨subd14_2_725, List.forall_mem_cons.2 ⟨subd14_2_726, List.forall_mem_cons.2 ⟨subd14_2_727, List.forall_mem_cons.2 ⟨subd14_2_728, List.forall_mem_cons.2 ⟨subd14_2_729, List.forall_mem_cons.2 ⟨subd14_2_730, List.forall_mem_cons.2 ⟨subd14_2_731, List.forall_mem_cons.2 ⟨subd14_2_732, List.forall_mem_cons.2 ⟨subd14_2_733, List.forall_mem_cons.2 ⟨subd14_2_734, List.forall_mem_cons.2 ⟨subd14_2_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_736 : subd14_2 [3, -1, -3] = true := by decide +kernel
theorem subd14_2_737 : subd14_2 [3, -1, -2] = true := by decide +kernel
theorem subd14_2_738 : subd14_2 [3, -1, -1] = true := by decide +kernel
theorem subd14_2_739 : subd14_2 [3, -1, 0] = true := by decide +kernel
theorem subd14_2_740 : subd14_2 [3, -1, 1] = true := by decide +kernel
theorem subd14_2_741 : subd14_2 [3, -1, 2] = true := by decide +kernel
theorem subd14_2_742 : subd14_2 [3, -1, 3] = true := by decide +kernel
theorem subd14_2_743 : subd14_2 [3, -1, 4] = true := by decide +kernel
theorem subd14_2_744 : subd14_2 [3, -1, 5] = true := by decide +kernel
theorem subd14_2_745 : subd14_2 [3, -1, 6] = true := by decide +kernel
theorem subd14_2_746 : subd14_2 [3, -1, 7] = true := by decide +kernel
theorem subd14_2_747 : subd14_2 [3, -1, 8] = true := by decide +kernel
theorem subd14_2_748 : subd14_2 [3, 0, -7] = true := by decide +kernel
theorem subd14_2_749 : subd14_2 [3, 0, -6] = true := by decide +kernel
theorem subd14_2_750 : subd14_2 [3, 0, -5] = true := by decide +kernel
theorem subd14_2_751 : subd14_2 [3, 0, -4] = true := by decide +kernel
theorem subd14_2_752 : subd14_2 [3, 0, -3] = true := by decide +kernel
theorem subd14_2_753 : subd14_2 [3, 0, -2] = true := by decide +kernel
theorem subd14_2_754 : subd14_2 [3, 0, -1] = true := by decide +kernel
theorem subd14_2_755 : subd14_2 [3, 0, 0] = true := by decide +kernel
theorem subd14_2_756 : subd14_2 [3, 0, 1] = true := by decide +kernel
theorem subd14_2_757 : subd14_2 [3, 0, 2] = true := by decide +kernel
theorem subd14_2_758 : subd14_2 [3, 0, 3] = true := by decide +kernel
theorem subd14_2_759 : subd14_2 [3, 0, 4] = true := by decide +kernel
theorem subd14_2_760 : subd14_2 [3, 0, 5] = true := by decide +kernel
theorem subd14_2_761 : subd14_2 [3, 0, 6] = true := by decide +kernel
theorem subd14_2_762 : subd14_2 [3, 0, 7] = true := by decide +kernel
theorem subd14_2_763 : subd14_2 [3, 0, 8] = true := by decide +kernel
theorem subd14_2_764 : subd14_2 [3, 1, -7] = true := by decide +kernel
theorem subd14_2_765 : subd14_2 [3, 1, -6] = true := by decide +kernel
theorem subd14_2_766 : subd14_2 [3, 1, -5] = true := by decide +kernel
theorem subd14_2_767 : subd14_2 [3, 1, -4] = true := by decide +kernel
theorem sbd14_2_23 : ∀ q ∈ blkd14_2_23, subd14_2 q = true := by
  unfold blkd14_2_23
  exact List.forall_mem_cons.2 ⟨subd14_2_736, List.forall_mem_cons.2 ⟨subd14_2_737, List.forall_mem_cons.2 ⟨subd14_2_738, List.forall_mem_cons.2 ⟨subd14_2_739, List.forall_mem_cons.2 ⟨subd14_2_740, List.forall_mem_cons.2 ⟨subd14_2_741, List.forall_mem_cons.2 ⟨subd14_2_742, List.forall_mem_cons.2 ⟨subd14_2_743, List.forall_mem_cons.2 ⟨subd14_2_744, List.forall_mem_cons.2 ⟨subd14_2_745, List.forall_mem_cons.2 ⟨subd14_2_746, List.forall_mem_cons.2 ⟨subd14_2_747, List.forall_mem_cons.2 ⟨subd14_2_748, List.forall_mem_cons.2 ⟨subd14_2_749, List.forall_mem_cons.2 ⟨subd14_2_750, List.forall_mem_cons.2 ⟨subd14_2_751, List.forall_mem_cons.2 ⟨subd14_2_752, List.forall_mem_cons.2 ⟨subd14_2_753, List.forall_mem_cons.2 ⟨subd14_2_754, List.forall_mem_cons.2 ⟨subd14_2_755, List.forall_mem_cons.2 ⟨subd14_2_756, List.forall_mem_cons.2 ⟨subd14_2_757, List.forall_mem_cons.2 ⟨subd14_2_758, List.forall_mem_cons.2 ⟨subd14_2_759, List.forall_mem_cons.2 ⟨subd14_2_760, List.forall_mem_cons.2 ⟨subd14_2_761, List.forall_mem_cons.2 ⟨subd14_2_762, List.forall_mem_cons.2 ⟨subd14_2_763, List.forall_mem_cons.2 ⟨subd14_2_764, List.forall_mem_cons.2 ⟨subd14_2_765, List.forall_mem_cons.2 ⟨subd14_2_766, List.forall_mem_cons.2 ⟨subd14_2_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_768 : subd14_2 [3, 1, -3] = true := by decide +kernel
theorem subd14_2_769 : subd14_2 [3, 1, -2] = true := by decide +kernel
theorem subd14_2_770 : subd14_2 [3, 1, -1] = true := by decide +kernel
theorem subd14_2_771 : subd14_2 [3, 1, 0] = true := by decide +kernel
theorem subd14_2_772 : subd14_2 [3, 1, 1] = true := by decide +kernel
theorem subd14_2_773 : subd14_2 [3, 1, 2] = true := by decide +kernel
theorem subd14_2_774 : subd14_2 [3, 1, 3] = true := by decide +kernel
theorem subd14_2_775 : subd14_2 [3, 1, 4] = true := by decide +kernel
theorem subd14_2_776 : subd14_2 [3, 1, 5] = true := by decide +kernel
theorem subd14_2_777 : subd14_2 [3, 1, 6] = true := by decide +kernel
theorem subd14_2_778 : subd14_2 [3, 1, 7] = true := by decide +kernel
theorem subd14_2_779 : subd14_2 [3, 2] = true := by decide +kernel
theorem subd14_2_780 : subd14_2 [3, 3] = true := by decide +kernel
theorem subd14_2_781 : subd14_2 [4, -4] = true := by decide +kernel
theorem subd14_2_782 : subd14_2 [4, -3] = true := by decide +kernel
theorem subd14_2_783 : subd14_2 [4, -2] = true := by decide +kernel
theorem subd14_2_784 : subd14_2 [4, -1] = true := by decide +kernel
theorem subd14_2_785 : subd14_2 [4, 0] = true := by decide +kernel
theorem subd14_2_786 : subd14_2 [4, 1] = true := by decide +kernel
theorem sbd14_2_24 : ∀ q ∈ blkd14_2_24, subd14_2 q = true := by
  unfold blkd14_2_24
  exact List.forall_mem_cons.2 ⟨subd14_2_768, List.forall_mem_cons.2 ⟨subd14_2_769, List.forall_mem_cons.2 ⟨subd14_2_770, List.forall_mem_cons.2 ⟨subd14_2_771, List.forall_mem_cons.2 ⟨subd14_2_772, List.forall_mem_cons.2 ⟨subd14_2_773, List.forall_mem_cons.2 ⟨subd14_2_774, List.forall_mem_cons.2 ⟨subd14_2_775, List.forall_mem_cons.2 ⟨subd14_2_776, List.forall_mem_cons.2 ⟨subd14_2_777, List.forall_mem_cons.2 ⟨subd14_2_778, List.forall_mem_cons.2 ⟨subd14_2_779, List.forall_mem_cons.2 ⟨subd14_2_780, List.forall_mem_cons.2 ⟨subd14_2_781, List.forall_mem_cons.2 ⟨subd14_2_782, List.forall_mem_cons.2 ⟨subd14_2_783, List.forall_mem_cons.2 ⟨subd14_2_784, List.forall_mem_cons.2 ⟨subd14_2_785, List.forall_mem_cons.2 ⟨subd14_2_786, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_3 : ldCheck G d14_3.U d14_3.ms ldd14_3 = true := by decide +kernel
theorem pre_okd14_3 : subPre G cell14 d14_3 = true := by decide +kernel
theorem subd14_3_0 : subd14_3 [-5, -2] = true := by decide +kernel
theorem subd14_3_1 : subd14_3 [-5, -1] = true := by decide +kernel
theorem subd14_3_2 : subd14_3 [-5, 0] = true := by decide +kernel
theorem subd14_3_3 : subd14_3 [-5, 1] = true := by decide +kernel
theorem subd14_3_4 : subd14_3 [-5, 2] = true := by decide +kernel
theorem subd14_3_5 : subd14_3 [-4, -4] = true := by decide +kernel
theorem subd14_3_6 : subd14_3 [-4, -3] = true := by decide +kernel
theorem subd14_3_7 : subd14_3 [-4, -2] = true := by decide +kernel
theorem subd14_3_8 : subd14_3 [-4, -1, -6] = true := by decide +kernel
theorem subd14_3_9 : subd14_3 [-4, -1, -5] = true := by decide +kernel
theorem subd14_3_10 : subd14_3 [-4, -1, -4] = true := by decide +kernel
theorem subd14_3_11 : subd14_3 [-4, -1, -3] = true := by decide +kernel
theorem subd14_3_12 : subd14_3 [-4, -1, -2] = true := by decide +kernel
theorem subd14_3_13 : subd14_3 [-4, -1, -1] = true := by decide +kernel
theorem subd14_3_14 : subd14_3 [-4, -1, 0] = true := by decide +kernel
theorem subd14_3_15 : subd14_3 [-4, -1, 1] = true := by decide +kernel
theorem subd14_3_16 : subd14_3 [-4, -1, 2] = true := by decide +kernel
theorem subd14_3_17 : subd14_3 [-4, -1, 3] = true := by decide +kernel
theorem subd14_3_18 : subd14_3 [-4, -1, 4] = true := by decide +kernel
theorem subd14_3_19 : subd14_3 [-4, -1, 5] = true := by decide +kernel
theorem subd14_3_20 : subd14_3 [-4, -1, 6] = true := by decide +kernel
theorem subd14_3_21 : subd14_3 [-4, -1, 7] = true := by decide +kernel
theorem subd14_3_22 : subd14_3 [-4, 0, -7] = true := by decide +kernel
theorem subd14_3_23 : subd14_3 [-4, 0, -6] = true := by decide +kernel
theorem subd14_3_24 : subd14_3 [-4, 0, -5] = true := by decide +kernel
theorem subd14_3_25 : subd14_3 [-4, 0, -4] = true := by decide +kernel
theorem subd14_3_26 : subd14_3 [-4, 0, -3] = true := by decide +kernel
theorem subd14_3_27 : subd14_3 [-4, 0, -2] = true := by decide +kernel
theorem subd14_3_28 : subd14_3 [-4, 0, -1] = true := by decide +kernel
theorem subd14_3_29 : subd14_3 [-4, 0, 0] = true := by decide +kernel
theorem subd14_3_30 : subd14_3 [-4, 0, 1] = true := by decide +kernel
theorem subd14_3_31 : subd14_3 [-4, 0, 2] = true := by decide +kernel
theorem sbd14_3_0 : ∀ q ∈ blkd14_3_0, subd14_3 q = true := by
  unfold blkd14_3_0
  exact List.forall_mem_cons.2 ⟨subd14_3_0, List.forall_mem_cons.2 ⟨subd14_3_1, List.forall_mem_cons.2 ⟨subd14_3_2, List.forall_mem_cons.2 ⟨subd14_3_3, List.forall_mem_cons.2 ⟨subd14_3_4, List.forall_mem_cons.2 ⟨subd14_3_5, List.forall_mem_cons.2 ⟨subd14_3_6, List.forall_mem_cons.2 ⟨subd14_3_7, List.forall_mem_cons.2 ⟨subd14_3_8, List.forall_mem_cons.2 ⟨subd14_3_9, List.forall_mem_cons.2 ⟨subd14_3_10, List.forall_mem_cons.2 ⟨subd14_3_11, List.forall_mem_cons.2 ⟨subd14_3_12, List.forall_mem_cons.2 ⟨subd14_3_13, List.forall_mem_cons.2 ⟨subd14_3_14, List.forall_mem_cons.2 ⟨subd14_3_15, List.forall_mem_cons.2 ⟨subd14_3_16, List.forall_mem_cons.2 ⟨subd14_3_17, List.forall_mem_cons.2 ⟨subd14_3_18, List.forall_mem_cons.2 ⟨subd14_3_19, List.forall_mem_cons.2 ⟨subd14_3_20, List.forall_mem_cons.2 ⟨subd14_3_21, List.forall_mem_cons.2 ⟨subd14_3_22, List.forall_mem_cons.2 ⟨subd14_3_23, List.forall_mem_cons.2 ⟨subd14_3_24, List.forall_mem_cons.2 ⟨subd14_3_25, List.forall_mem_cons.2 ⟨subd14_3_26, List.forall_mem_cons.2 ⟨subd14_3_27, List.forall_mem_cons.2 ⟨subd14_3_28, List.forall_mem_cons.2 ⟨subd14_3_29, List.forall_mem_cons.2 ⟨subd14_3_30, List.forall_mem_cons.2 ⟨subd14_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_32 : subd14_3 [-4, 0, 3] = true := by decide +kernel
theorem subd14_3_33 : subd14_3 [-4, 0, 4] = true := by decide +kernel
theorem subd14_3_34 : subd14_3 [-4, 0, 5] = true := by decide +kernel
theorem subd14_3_35 : subd14_3 [-4, 0, 6] = true := by decide +kernel
theorem subd14_3_36 : subd14_3 [-4, 0, 7] = true := by decide +kernel
theorem subd14_3_37 : subd14_3 [-4, 1, -8] = true := by decide +kernel
theorem subd14_3_38 : subd14_3 [-4, 1, -7] = true := by decide +kernel
theorem subd14_3_39 : subd14_3 [-4, 1, -6] = true := by decide +kernel
theorem subd14_3_40 : subd14_3 [-4, 1, -5] = true := by decide +kernel
theorem subd14_3_41 : subd14_3 [-4, 1, -4] = true := by decide +kernel
theorem subd14_3_42 : subd14_3 [-4, 1, -3] = true := by decide +kernel
theorem subd14_3_43 : subd14_3 [-4, 1, -2] = true := by decide +kernel
theorem subd14_3_44 : subd14_3 [-4, 1, -1] = true := by decide +kernel
theorem subd14_3_45 : subd14_3 [-4, 1, 0] = true := by decide +kernel
theorem subd14_3_46 : subd14_3 [-4, 1, 1] = true := by decide +kernel
theorem subd14_3_47 : subd14_3 [-4, 1, 2] = true := by decide +kernel
theorem subd14_3_48 : subd14_3 [-4, 1, 3] = true := by decide +kernel
theorem subd14_3_49 : subd14_3 [-4, 1, 4] = true := by decide +kernel
theorem subd14_3_50 : subd14_3 [-4, 1, 5] = true := by decide +kernel
theorem subd14_3_51 : subd14_3 [-4, 1, 6] = true := by decide +kernel
theorem subd14_3_52 : subd14_3 [-4, 2] = true := by decide +kernel
theorem subd14_3_53 : subd14_3 [-4, 3] = true := by decide +kernel
theorem subd14_3_54 : subd14_3 [-3, -5] = true := by decide +kernel
theorem subd14_3_55 : subd14_3 [-3, -4] = true := by decide +kernel
theorem subd14_3_56 : subd14_3 [-3, -3] = true := by decide +kernel
theorem subd14_3_57 : subd14_3 [-3, -2, -7] = true := by decide +kernel
theorem subd14_3_58 : subd14_3 [-3, -2, -6] = true := by decide +kernel
theorem subd14_3_59 : subd14_3 [-3, -2, -5] = true := by decide +kernel
theorem subd14_3_60 : subd14_3 [-3, -2, -4] = true := by decide +kernel
theorem subd14_3_61 : subd14_3 [-3, -2, -3] = true := by decide +kernel
theorem subd14_3_62 : subd14_3 [-3, -2, -2] = true := by decide +kernel
theorem subd14_3_63 : subd14_3 [-3, -2, -1] = true := by decide +kernel
theorem sbd14_3_1 : ∀ q ∈ blkd14_3_1, subd14_3 q = true := by
  unfold blkd14_3_1
  exact List.forall_mem_cons.2 ⟨subd14_3_32, List.forall_mem_cons.2 ⟨subd14_3_33, List.forall_mem_cons.2 ⟨subd14_3_34, List.forall_mem_cons.2 ⟨subd14_3_35, List.forall_mem_cons.2 ⟨subd14_3_36, List.forall_mem_cons.2 ⟨subd14_3_37, List.forall_mem_cons.2 ⟨subd14_3_38, List.forall_mem_cons.2 ⟨subd14_3_39, List.forall_mem_cons.2 ⟨subd14_3_40, List.forall_mem_cons.2 ⟨subd14_3_41, List.forall_mem_cons.2 ⟨subd14_3_42, List.forall_mem_cons.2 ⟨subd14_3_43, List.forall_mem_cons.2 ⟨subd14_3_44, List.forall_mem_cons.2 ⟨subd14_3_45, List.forall_mem_cons.2 ⟨subd14_3_46, List.forall_mem_cons.2 ⟨subd14_3_47, List.forall_mem_cons.2 ⟨subd14_3_48, List.forall_mem_cons.2 ⟨subd14_3_49, List.forall_mem_cons.2 ⟨subd14_3_50, List.forall_mem_cons.2 ⟨subd14_3_51, List.forall_mem_cons.2 ⟨subd14_3_52, List.forall_mem_cons.2 ⟨subd14_3_53, List.forall_mem_cons.2 ⟨subd14_3_54, List.forall_mem_cons.2 ⟨subd14_3_55, List.forall_mem_cons.2 ⟨subd14_3_56, List.forall_mem_cons.2 ⟨subd14_3_57, List.forall_mem_cons.2 ⟨subd14_3_58, List.forall_mem_cons.2 ⟨subd14_3_59, List.forall_mem_cons.2 ⟨subd14_3_60, List.forall_mem_cons.2 ⟨subd14_3_61, List.forall_mem_cons.2 ⟨subd14_3_62, List.forall_mem_cons.2 ⟨subd14_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_64 : subd14_3 [-3, -2, 0] = true := by decide +kernel
theorem subd14_3_65 : subd14_3 [-3, -2, 1] = true := by decide +kernel
theorem subd14_3_66 : subd14_3 [-3, -2, 2] = true := by decide +kernel
theorem subd14_3_67 : subd14_3 [-3, -2, 3] = true := by decide +kernel
theorem subd14_3_68 : subd14_3 [-3, -2, 4] = true := by decide +kernel
theorem subd14_3_69 : subd14_3 [-3, -2, 5] = true := by decide +kernel
theorem subd14_3_70 : subd14_3 [-3, -2, 6] = true := by decide +kernel
theorem subd14_3_71 : subd14_3 [-3, -2, 7] = true := by decide +kernel
theorem subd14_3_72 : subd14_3 [-3, -2, 8] = true := by decide +kernel
theorem subd14_3_73 : subd14_3 [-3, -1, -8] = true := by decide +kernel
theorem subd14_3_74 : subd14_3 [-3, -1, -7] = true := by decide +kernel
theorem subd14_3_75 : subd14_3 [-3, -1, -6] = true := by decide +kernel
theorem subd14_3_76 : subd14_3 [-3, -1, -5] = true := by decide +kernel
theorem subd14_3_77 : subd14_3 [-3, -1, -4] = true := by decide +kernel
theorem subd14_3_78 : subd14_3 [-3, -1, -3] = true := by decide +kernel
theorem subd14_3_79 : subd14_3 [-3, -1, -2] = true := by decide +kernel
theorem subd14_3_80 : subd14_3 [-3, -1, -1] = true := by decide +kernel
theorem subd14_3_81 : subd14_3 [-3, -1, 0] = true := by decide +kernel
theorem subd14_3_82 : subd14_3 [-3, -1, 1] = true := by decide +kernel
theorem subd14_3_83 : subd14_3 [-3, -1, 2] = true := by decide +kernel
theorem subd14_3_84 : subd14_3 [-3, -1, 3] = true := by decide +kernel
theorem subd14_3_85 : subd14_3 [-3, -1, 4] = true := by decide +kernel
theorem subd14_3_86 : subd14_3 [-3, -1, 5] = true := by decide +kernel
theorem subd14_3_87 : subd14_3 [-3, -1, 6] = true := by decide +kernel
theorem subd14_3_88 : subd14_3 [-3, -1, 7] = true := by decide +kernel
theorem subd14_3_89 : subd14_3 [-3, -1, 8] = true := by decide +kernel
theorem subd14_3_90 : subd14_3 [-3, 0, -9] = true := by decide +kernel
theorem subd14_3_91 : subd14_3 [-3, 0, -8] = true := by decide +kernel
theorem subd14_3_92 : subd14_3 [-3, 0, -7] = true := by decide +kernel
theorem subd14_3_93 : subd14_3 [-3, 0, -6] = true := by decide +kernel
theorem subd14_3_94 : subd14_3 [-3, 0, -5] = true := by decide +kernel
theorem subd14_3_95 : subd14_3 [-3, 0, -4] = true := by decide +kernel
theorem sbd14_3_2 : ∀ q ∈ blkd14_3_2, subd14_3 q = true := by
  unfold blkd14_3_2
  exact List.forall_mem_cons.2 ⟨subd14_3_64, List.forall_mem_cons.2 ⟨subd14_3_65, List.forall_mem_cons.2 ⟨subd14_3_66, List.forall_mem_cons.2 ⟨subd14_3_67, List.forall_mem_cons.2 ⟨subd14_3_68, List.forall_mem_cons.2 ⟨subd14_3_69, List.forall_mem_cons.2 ⟨subd14_3_70, List.forall_mem_cons.2 ⟨subd14_3_71, List.forall_mem_cons.2 ⟨subd14_3_72, List.forall_mem_cons.2 ⟨subd14_3_73, List.forall_mem_cons.2 ⟨subd14_3_74, List.forall_mem_cons.2 ⟨subd14_3_75, List.forall_mem_cons.2 ⟨subd14_3_76, List.forall_mem_cons.2 ⟨subd14_3_77, List.forall_mem_cons.2 ⟨subd14_3_78, List.forall_mem_cons.2 ⟨subd14_3_79, List.forall_mem_cons.2 ⟨subd14_3_80, List.forall_mem_cons.2 ⟨subd14_3_81, List.forall_mem_cons.2 ⟨subd14_3_82, List.forall_mem_cons.2 ⟨subd14_3_83, List.forall_mem_cons.2 ⟨subd14_3_84, List.forall_mem_cons.2 ⟨subd14_3_85, List.forall_mem_cons.2 ⟨subd14_3_86, List.forall_mem_cons.2 ⟨subd14_3_87, List.forall_mem_cons.2 ⟨subd14_3_88, List.forall_mem_cons.2 ⟨subd14_3_89, List.forall_mem_cons.2 ⟨subd14_3_90, List.forall_mem_cons.2 ⟨subd14_3_91, List.forall_mem_cons.2 ⟨subd14_3_92, List.forall_mem_cons.2 ⟨subd14_3_93, List.forall_mem_cons.2 ⟨subd14_3_94, List.forall_mem_cons.2 ⟨subd14_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_96 : subd14_3 [-3, 0, -3] = true := by decide +kernel
theorem subd14_3_97 : subd14_3 [-3, 0, -2] = true := by decide +kernel
theorem subd14_3_98 : subd14_3 [-3, 0, -1] = true := by decide +kernel
theorem subd14_3_99 : subd14_3 [-3, 0, 0] = true := by decide +kernel
theorem subd14_3_100 : subd14_3 [-3, 0, 1] = true := by decide +kernel
theorem subd14_3_101 : subd14_3 [-3, 0, 2] = true := by decide +kernel
theorem subd14_3_102 : subd14_3 [-3, 0, 3] = true := by decide +kernel
theorem subd14_3_103 : subd14_3 [-3, 0, 4] = true := by decide +kernel
theorem subd14_3_104 : subd14_3 [-3, 0, 5] = true := by decide +kernel
theorem subd14_3_105 : subd14_3 [-3, 0, 6] = true := by decide +kernel
theorem subd14_3_106 : subd14_3 [-3, 0, 7] = true := by decide +kernel
theorem subd14_3_107 : subd14_3 [-3, 0, 8] = true := by decide +kernel
theorem subd14_3_108 : subd14_3 [-3, 1, -9] = true := by decide +kernel
theorem subd14_3_109 : subd14_3 [-3, 1, -8] = true := by decide +kernel
theorem subd14_3_110 : subd14_3 [-3, 1, -7] = true := by decide +kernel
theorem subd14_3_111 : subd14_3 [-3, 1, -6] = true := by decide +kernel
theorem subd14_3_112 : subd14_3 [-3, 1, -5] = true := by decide +kernel
theorem subd14_3_113 : subd14_3 [-3, 1, -4] = true := by decide +kernel
theorem subd14_3_114 : subd14_3 [-3, 1, -3] = true := by decide +kernel
theorem subd14_3_115 : subd14_3 [-3, 1, -2] = true := by decide +kernel
theorem subd14_3_116 : subd14_3 [-3, 1, -1] = true := by decide +kernel
theorem subd14_3_117 : subd14_3 [-3, 1, 0] = true := by decide +kernel
theorem subd14_3_118 : subd14_3 [-3, 1, 1] = true := by decide +kernel
theorem subd14_3_119 : subd14_3 [-3, 1, 2] = true := by decide +kernel
theorem subd14_3_120 : subd14_3 [-3, 1, 3] = true := by decide +kernel
theorem subd14_3_121 : subd14_3 [-3, 1, 4] = true := by decide +kernel
theorem subd14_3_122 : subd14_3 [-3, 1, 5] = true := by decide +kernel
theorem subd14_3_123 : subd14_3 [-3, 1, 6] = true := by decide +kernel
theorem subd14_3_124 : subd14_3 [-3, 1, 7] = true := by decide +kernel
theorem subd14_3_125 : subd14_3 [-3, 1, 8] = true := by decide +kernel
theorem subd14_3_126 : subd14_3 [-3, 2, -9] = true := by decide +kernel
theorem subd14_3_127 : subd14_3 [-3, 2, -8] = true := by decide +kernel
theorem sbd14_3_3 : ∀ q ∈ blkd14_3_3, subd14_3 q = true := by
  unfold blkd14_3_3
  exact List.forall_mem_cons.2 ⟨subd14_3_96, List.forall_mem_cons.2 ⟨subd14_3_97, List.forall_mem_cons.2 ⟨subd14_3_98, List.forall_mem_cons.2 ⟨subd14_3_99, List.forall_mem_cons.2 ⟨subd14_3_100, List.forall_mem_cons.2 ⟨subd14_3_101, List.forall_mem_cons.2 ⟨subd14_3_102, List.forall_mem_cons.2 ⟨subd14_3_103, List.forall_mem_cons.2 ⟨subd14_3_104, List.forall_mem_cons.2 ⟨subd14_3_105, List.forall_mem_cons.2 ⟨subd14_3_106, List.forall_mem_cons.2 ⟨subd14_3_107, List.forall_mem_cons.2 ⟨subd14_3_108, List.forall_mem_cons.2 ⟨subd14_3_109, List.forall_mem_cons.2 ⟨subd14_3_110, List.forall_mem_cons.2 ⟨subd14_3_111, List.forall_mem_cons.2 ⟨subd14_3_112, List.forall_mem_cons.2 ⟨subd14_3_113, List.forall_mem_cons.2 ⟨subd14_3_114, List.forall_mem_cons.2 ⟨subd14_3_115, List.forall_mem_cons.2 ⟨subd14_3_116, List.forall_mem_cons.2 ⟨subd14_3_117, List.forall_mem_cons.2 ⟨subd14_3_118, List.forall_mem_cons.2 ⟨subd14_3_119, List.forall_mem_cons.2 ⟨subd14_3_120, List.forall_mem_cons.2 ⟨subd14_3_121, List.forall_mem_cons.2 ⟨subd14_3_122, List.forall_mem_cons.2 ⟨subd14_3_123, List.forall_mem_cons.2 ⟨subd14_3_124, List.forall_mem_cons.2 ⟨subd14_3_125, List.forall_mem_cons.2 ⟨subd14_3_126, List.forall_mem_cons.2 ⟨subd14_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_128 : subd14_3 [-3, 2, -7] = true := by decide +kernel
theorem subd14_3_129 : subd14_3 [-3, 2, -6] = true := by decide +kernel
theorem subd14_3_130 : subd14_3 [-3, 2, -5] = true := by decide +kernel
theorem subd14_3_131 : subd14_3 [-3, 2, -4] = true := by decide +kernel
theorem subd14_3_132 : subd14_3 [-3, 2, -3] = true := by decide +kernel
theorem subd14_3_133 : subd14_3 [-3, 2, -2] = true := by decide +kernel
theorem subd14_3_134 : subd14_3 [-3, 2, -1] = true := by decide +kernel
theorem subd14_3_135 : subd14_3 [-3, 2, 0] = true := by decide +kernel
theorem subd14_3_136 : subd14_3 [-3, 2, 1] = true := by decide +kernel
theorem subd14_3_137 : subd14_3 [-3, 2, 2] = true := by decide +kernel
theorem subd14_3_138 : subd14_3 [-3, 2, 3] = true := by decide +kernel
theorem subd14_3_139 : subd14_3 [-3, 2, 4] = true := by decide +kernel
theorem subd14_3_140 : subd14_3 [-3, 2, 5] = true := by decide +kernel
theorem subd14_3_141 : subd14_3 [-3, 2, 6] = true := by decide +kernel
theorem subd14_3_142 : subd14_3 [-3, 2, 7] = true := by decide +kernel
theorem subd14_3_143 : subd14_3 [-3, 3, -8] = true := by decide +kernel
theorem subd14_3_144 : subd14_3 [-3, 3, -7] = true := by decide +kernel
theorem subd14_3_145 : subd14_3 [-3, 3, -6] = true := by decide +kernel
theorem subd14_3_146 : subd14_3 [-3, 3, -5] = true := by decide +kernel
theorem subd14_3_147 : subd14_3 [-3, 3, -4] = true := by decide +kernel
theorem subd14_3_148 : subd14_3 [-3, 3, -3] = true := by decide +kernel
theorem subd14_3_149 : subd14_3 [-3, 3, -2] = true := by decide +kernel
theorem subd14_3_150 : subd14_3 [-3, 3, -1] = true := by decide +kernel
theorem subd14_3_151 : subd14_3 [-3, 3, 0] = true := by decide +kernel
theorem subd14_3_152 : subd14_3 [-3, 3, 1] = true := by decide +kernel
theorem subd14_3_153 : subd14_3 [-3, 3, 2] = true := by decide +kernel
theorem subd14_3_154 : subd14_3 [-3, 3, 3] = true := by decide +kernel
theorem subd14_3_155 : subd14_3 [-3, 3, 4] = true := by decide +kernel
theorem subd14_3_156 : subd14_3 [-3, 3, 5] = true := by decide +kernel
theorem subd14_3_157 : subd14_3 [-3, 4] = true := by decide +kernel
theorem subd14_3_158 : subd14_3 [-2, -5] = true := by decide +kernel
theorem subd14_3_159 : subd14_3 [-2, -4] = true := by decide +kernel
theorem sbd14_3_4 : ∀ q ∈ blkd14_3_4, subd14_3 q = true := by
  unfold blkd14_3_4
  exact List.forall_mem_cons.2 ⟨subd14_3_128, List.forall_mem_cons.2 ⟨subd14_3_129, List.forall_mem_cons.2 ⟨subd14_3_130, List.forall_mem_cons.2 ⟨subd14_3_131, List.forall_mem_cons.2 ⟨subd14_3_132, List.forall_mem_cons.2 ⟨subd14_3_133, List.forall_mem_cons.2 ⟨subd14_3_134, List.forall_mem_cons.2 ⟨subd14_3_135, List.forall_mem_cons.2 ⟨subd14_3_136, List.forall_mem_cons.2 ⟨subd14_3_137, List.forall_mem_cons.2 ⟨subd14_3_138, List.forall_mem_cons.2 ⟨subd14_3_139, List.forall_mem_cons.2 ⟨subd14_3_140, List.forall_mem_cons.2 ⟨subd14_3_141, List.forall_mem_cons.2 ⟨subd14_3_142, List.forall_mem_cons.2 ⟨subd14_3_143, List.forall_mem_cons.2 ⟨subd14_3_144, List.forall_mem_cons.2 ⟨subd14_3_145, List.forall_mem_cons.2 ⟨subd14_3_146, List.forall_mem_cons.2 ⟨subd14_3_147, List.forall_mem_cons.2 ⟨subd14_3_148, List.forall_mem_cons.2 ⟨subd14_3_149, List.forall_mem_cons.2 ⟨subd14_3_150, List.forall_mem_cons.2 ⟨subd14_3_151, List.forall_mem_cons.2 ⟨subd14_3_152, List.forall_mem_cons.2 ⟨subd14_3_153, List.forall_mem_cons.2 ⟨subd14_3_154, List.forall_mem_cons.2 ⟨subd14_3_155, List.forall_mem_cons.2 ⟨subd14_3_156, List.forall_mem_cons.2 ⟨subd14_3_157, List.forall_mem_cons.2 ⟨subd14_3_158, List.forall_mem_cons.2 ⟨subd14_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_160 : subd14_3 [-2, -3, -7] = true := by decide +kernel
theorem subd14_3_161 : subd14_3 [-2, -3, -6] = true := by decide +kernel
theorem subd14_3_162 : subd14_3 [-2, -3, -5] = true := by decide +kernel
theorem subd14_3_163 : subd14_3 [-2, -3, -4] = true := by decide +kernel
theorem subd14_3_164 : subd14_3 [-2, -3, -3] = true := by decide +kernel
theorem subd14_3_165 : subd14_3 [-2, -3, -2] = true := by decide +kernel
theorem subd14_3_166 : subd14_3 [-2, -3, -1] = true := by decide +kernel
theorem subd14_3_167 : subd14_3 [-2, -3, 0] = true := by decide +kernel
theorem subd14_3_168 : subd14_3 [-2, -3, 1] = true := by decide +kernel
theorem subd14_3_169 : subd14_3 [-2, -3, 2] = true := by decide +kernel
theorem subd14_3_170 : subd14_3 [-2, -3, 3] = true := by decide +kernel
theorem subd14_3_171 : subd14_3 [-2, -3, 4] = true := by decide +kernel
theorem subd14_3_172 : subd14_3 [-2, -3, 5] = true := by decide +kernel
theorem subd14_3_173 : subd14_3 [-2, -3, 6] = true := by decide +kernel
theorem subd14_3_174 : subd14_3 [-2, -3, 7] = true := by decide +kernel
theorem subd14_3_175 : subd14_3 [-2, -3, 8] = true := by decide +kernel
theorem subd14_3_176 : subd14_3 [-2, -2, -8] = true := by decide +kernel
theorem subd14_3_177 : subd14_3 [-2, -2, -7] = true := by decide +kernel
theorem subd14_3_178 : subd14_3 [-2, -2, -6] = true := by decide +kernel
theorem subd14_3_179 : subd14_3 [-2, -2, -5] = true := by decide +kernel
theorem subd14_3_180 : subd14_3 [-2, -2, -4] = true := by decide +kernel
theorem subd14_3_181 : subd14_3 [-2, -2, -3] = true := by decide +kernel
theorem subd14_3_182 : subd14_3 [-2, -2, -2] = true := by decide +kernel
theorem subd14_3_183 : subd14_3 [-2, -2, -1] = true := by decide +kernel
theorem subd14_3_184 : subd14_3 [-2, -2, 0] = true := by decide +kernel
theorem subd14_3_185 : subd14_3 [-2, -2, 1] = true := by decide +kernel
theorem subd14_3_186 : subd14_3 [-2, -2, 2] = true := by decide +kernel
theorem subd14_3_187 : subd14_3 [-2, -2, 3] = true := by decide +kernel
theorem subd14_3_188 : subd14_3 [-2, -2, 4] = true := by decide +kernel
theorem subd14_3_189 : subd14_3 [-2, -2, 5] = true := by decide +kernel
theorem subd14_3_190 : subd14_3 [-2, -2, 6] = true := by decide +kernel
theorem subd14_3_191 : subd14_3 [-2, -2, 7] = true := by decide +kernel
theorem sbd14_3_5 : ∀ q ∈ blkd14_3_5, subd14_3 q = true := by
  unfold blkd14_3_5
  exact List.forall_mem_cons.2 ⟨subd14_3_160, List.forall_mem_cons.2 ⟨subd14_3_161, List.forall_mem_cons.2 ⟨subd14_3_162, List.forall_mem_cons.2 ⟨subd14_3_163, List.forall_mem_cons.2 ⟨subd14_3_164, List.forall_mem_cons.2 ⟨subd14_3_165, List.forall_mem_cons.2 ⟨subd14_3_166, List.forall_mem_cons.2 ⟨subd14_3_167, List.forall_mem_cons.2 ⟨subd14_3_168, List.forall_mem_cons.2 ⟨subd14_3_169, List.forall_mem_cons.2 ⟨subd14_3_170, List.forall_mem_cons.2 ⟨subd14_3_171, List.forall_mem_cons.2 ⟨subd14_3_172, List.forall_mem_cons.2 ⟨subd14_3_173, List.forall_mem_cons.2 ⟨subd14_3_174, List.forall_mem_cons.2 ⟨subd14_3_175, List.forall_mem_cons.2 ⟨subd14_3_176, List.forall_mem_cons.2 ⟨subd14_3_177, List.forall_mem_cons.2 ⟨subd14_3_178, List.forall_mem_cons.2 ⟨subd14_3_179, List.forall_mem_cons.2 ⟨subd14_3_180, List.forall_mem_cons.2 ⟨subd14_3_181, List.forall_mem_cons.2 ⟨subd14_3_182, List.forall_mem_cons.2 ⟨subd14_3_183, List.forall_mem_cons.2 ⟨subd14_3_184, List.forall_mem_cons.2 ⟨subd14_3_185, List.forall_mem_cons.2 ⟨subd14_3_186, List.forall_mem_cons.2 ⟨subd14_3_187, List.forall_mem_cons.2 ⟨subd14_3_188, List.forall_mem_cons.2 ⟨subd14_3_189, List.forall_mem_cons.2 ⟨subd14_3_190, List.forall_mem_cons.2 ⟨subd14_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
