import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_0_608 : subd8_0 [2, 1, 1] = true := by decide +kernel
theorem subd8_0_609 : subd8_0 [2, 1, 2] = true := by decide +kernel
theorem subd8_0_610 : subd8_0 [2, 1, 3] = true := by decide +kernel
theorem subd8_0_611 : subd8_0 [2, 1, 4] = true := by decide +kernel
theorem subd8_0_612 : subd8_0 [2, 1, 5] = true := by decide +kernel
theorem subd8_0_613 : subd8_0 [2, 1, 6] = true := by decide +kernel
theorem subd8_0_614 : subd8_0 [2, 1, 7] = true := by decide +kernel
theorem subd8_0_615 : subd8_0 [2, 1, 8] = true := by decide +kernel
theorem subd8_0_616 : subd8_0 [2, 2, -6] = true := by decide +kernel
theorem subd8_0_617 : subd8_0 [2, 2, -5] = true := by decide +kernel
theorem subd8_0_618 : subd8_0 [2, 2, -4] = true := by decide +kernel
theorem subd8_0_619 : subd8_0 [2, 2, -3] = true := by decide +kernel
theorem subd8_0_620 : subd8_0 [2, 2, -2] = true := by decide +kernel
theorem subd8_0_621 : subd8_0 [2, 2, -1] = true := by decide +kernel
theorem subd8_0_622 : subd8_0 [2, 2, 0] = true := by decide +kernel
theorem subd8_0_623 : subd8_0 [2, 2, 1] = true := by decide +kernel
theorem subd8_0_624 : subd8_0 [2, 2, 2] = true := by decide +kernel
theorem subd8_0_625 : subd8_0 [2, 2, 3] = true := by decide +kernel
theorem subd8_0_626 : subd8_0 [2, 2, 4] = true := by decide +kernel
theorem subd8_0_627 : subd8_0 [2, 2, 5] = true := by decide +kernel
theorem subd8_0_628 : subd8_0 [2, 2, 6] = true := by decide +kernel
theorem subd8_0_629 : subd8_0 [2, 2, 7] = true := by decide +kernel
theorem subd8_0_630 : subd8_0 [2, 2, 8] = true := by decide +kernel
theorem subd8_0_631 : subd8_0 [2, 3, -5] = true := by decide +kernel
theorem subd8_0_632 : subd8_0 [2, 3, -4] = true := by decide +kernel
theorem subd8_0_633 : subd8_0 [2, 3, -3] = true := by decide +kernel
theorem subd8_0_634 : subd8_0 [2, 3, -2] = true := by decide +kernel
theorem subd8_0_635 : subd8_0 [2, 3, -1] = true := by decide +kernel
theorem subd8_0_636 : subd8_0 [2, 3, 0] = true := by decide +kernel
theorem subd8_0_637 : subd8_0 [2, 3, 1] = true := by decide +kernel
theorem subd8_0_638 : subd8_0 [2, 3, 2] = true := by decide +kernel
theorem subd8_0_639 : subd8_0 [2, 3, 3] = true := by decide +kernel
theorem sbd8_0_19 : ∀ q ∈ blkd8_0_19, subd8_0 q = true := by
  unfold blkd8_0_19
  exact List.forall_mem_cons.2 ⟨subd8_0_608, List.forall_mem_cons.2 ⟨subd8_0_609, List.forall_mem_cons.2 ⟨subd8_0_610, List.forall_mem_cons.2 ⟨subd8_0_611, List.forall_mem_cons.2 ⟨subd8_0_612, List.forall_mem_cons.2 ⟨subd8_0_613, List.forall_mem_cons.2 ⟨subd8_0_614, List.forall_mem_cons.2 ⟨subd8_0_615, List.forall_mem_cons.2 ⟨subd8_0_616, List.forall_mem_cons.2 ⟨subd8_0_617, List.forall_mem_cons.2 ⟨subd8_0_618, List.forall_mem_cons.2 ⟨subd8_0_619, List.forall_mem_cons.2 ⟨subd8_0_620, List.forall_mem_cons.2 ⟨subd8_0_621, List.forall_mem_cons.2 ⟨subd8_0_622, List.forall_mem_cons.2 ⟨subd8_0_623, List.forall_mem_cons.2 ⟨subd8_0_624, List.forall_mem_cons.2 ⟨subd8_0_625, List.forall_mem_cons.2 ⟨subd8_0_626, List.forall_mem_cons.2 ⟨subd8_0_627, List.forall_mem_cons.2 ⟨subd8_0_628, List.forall_mem_cons.2 ⟨subd8_0_629, List.forall_mem_cons.2 ⟨subd8_0_630, List.forall_mem_cons.2 ⟨subd8_0_631, List.forall_mem_cons.2 ⟨subd8_0_632, List.forall_mem_cons.2 ⟨subd8_0_633, List.forall_mem_cons.2 ⟨subd8_0_634, List.forall_mem_cons.2 ⟨subd8_0_635, List.forall_mem_cons.2 ⟨subd8_0_636, List.forall_mem_cons.2 ⟨subd8_0_637, List.forall_mem_cons.2 ⟨subd8_0_638, List.forall_mem_cons.2 ⟨subd8_0_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_640 : subd8_0 [2, 3, 4] = true := by decide +kernel
theorem subd8_0_641 : subd8_0 [2, 3, 5] = true := by decide +kernel
theorem subd8_0_642 : subd8_0 [2, 3, 6] = true := by decide +kernel
theorem subd8_0_643 : subd8_0 [2, 3, 7] = true := by decide +kernel
theorem subd8_0_644 : subd8_0 [2, 3, 8] = true := by decide +kernel
theorem subd8_0_645 : subd8_0 [2, 4] = true := by decide +kernel
theorem subd8_0_646 : subd8_0 [2, 5] = true := by decide +kernel
theorem subd8_0_647 : subd8_0 [2, 6] = true := by decide +kernel
theorem subd8_0_648 : subd8_0 [2, 7] = true := by decide +kernel
theorem subd8_0_649 : subd8_0 [3, -6] = true := by decide +kernel
theorem subd8_0_650 : subd8_0 [3, -5] = true := by decide +kernel
theorem subd8_0_651 : subd8_0 [3, -4] = true := by decide +kernel
theorem subd8_0_652 : subd8_0 [3, -3] = true := by decide +kernel
theorem subd8_0_653 : subd8_0 [3, -2] = true := by decide +kernel
theorem subd8_0_654 : subd8_0 [3, -1, -7] = true := by decide +kernel
theorem subd8_0_655 : subd8_0 [3, -1, -6] = true := by decide +kernel
theorem subd8_0_656 : subd8_0 [3, -1, -5] = true := by decide +kernel
theorem subd8_0_657 : subd8_0 [3, -1, -4] = true := by decide +kernel
theorem subd8_0_658 : subd8_0 [3, -1, -3] = true := by decide +kernel
theorem subd8_0_659 : subd8_0 [3, -1, -2] = true := by decide +kernel
theorem subd8_0_660 : subd8_0 [3, -1, -1] = true := by decide +kernel
theorem subd8_0_661 : subd8_0 [3, -1, 0] = true := by decide +kernel
theorem subd8_0_662 : subd8_0 [3, -1, 1] = true := by decide +kernel
theorem subd8_0_663 : subd8_0 [3, -1, 2] = true := by decide +kernel
theorem subd8_0_664 : subd8_0 [3, -1, 3] = true := by decide +kernel
theorem subd8_0_665 : subd8_0 [3, -1, 4] = true := by decide +kernel
theorem subd8_0_666 : subd8_0 [3, -1, 5] = true := by decide +kernel
theorem subd8_0_667 : subd8_0 [3, -1, 6] = true := by decide +kernel
theorem subd8_0_668 : subd8_0 [3, -1, 7] = true := by decide +kernel
theorem subd8_0_669 : subd8_0 [3, 0, -6] = true := by decide +kernel
theorem subd8_0_670 : subd8_0 [3, 0, -5] = true := by decide +kernel
theorem subd8_0_671 : subd8_0 [3, 0, -4] = true := by decide +kernel
theorem sbd8_0_20 : ∀ q ∈ blkd8_0_20, subd8_0 q = true := by
  unfold blkd8_0_20
  exact List.forall_mem_cons.2 ⟨subd8_0_640, List.forall_mem_cons.2 ⟨subd8_0_641, List.forall_mem_cons.2 ⟨subd8_0_642, List.forall_mem_cons.2 ⟨subd8_0_643, List.forall_mem_cons.2 ⟨subd8_0_644, List.forall_mem_cons.2 ⟨subd8_0_645, List.forall_mem_cons.2 ⟨subd8_0_646, List.forall_mem_cons.2 ⟨subd8_0_647, List.forall_mem_cons.2 ⟨subd8_0_648, List.forall_mem_cons.2 ⟨subd8_0_649, List.forall_mem_cons.2 ⟨subd8_0_650, List.forall_mem_cons.2 ⟨subd8_0_651, List.forall_mem_cons.2 ⟨subd8_0_652, List.forall_mem_cons.2 ⟨subd8_0_653, List.forall_mem_cons.2 ⟨subd8_0_654, List.forall_mem_cons.2 ⟨subd8_0_655, List.forall_mem_cons.2 ⟨subd8_0_656, List.forall_mem_cons.2 ⟨subd8_0_657, List.forall_mem_cons.2 ⟨subd8_0_658, List.forall_mem_cons.2 ⟨subd8_0_659, List.forall_mem_cons.2 ⟨subd8_0_660, List.forall_mem_cons.2 ⟨subd8_0_661, List.forall_mem_cons.2 ⟨subd8_0_662, List.forall_mem_cons.2 ⟨subd8_0_663, List.forall_mem_cons.2 ⟨subd8_0_664, List.forall_mem_cons.2 ⟨subd8_0_665, List.forall_mem_cons.2 ⟨subd8_0_666, List.forall_mem_cons.2 ⟨subd8_0_667, List.forall_mem_cons.2 ⟨subd8_0_668, List.forall_mem_cons.2 ⟨subd8_0_669, List.forall_mem_cons.2 ⟨subd8_0_670, List.forall_mem_cons.2 ⟨subd8_0_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_672 : subd8_0 [3, 0, -3] = true := by decide +kernel
theorem subd8_0_673 : subd8_0 [3, 0, -2] = true := by decide +kernel
theorem subd8_0_674 : subd8_0 [3, 0, -1] = true := by decide +kernel
theorem subd8_0_675 : subd8_0 [3, 0, 0] = true := by decide +kernel
theorem subd8_0_676 : subd8_0 [3, 0, 1] = true := by decide +kernel
theorem subd8_0_677 : subd8_0 [3, 0, 2] = true := by decide +kernel
theorem subd8_0_678 : subd8_0 [3, 0, 3] = true := by decide +kernel
theorem subd8_0_679 : subd8_0 [3, 0, 4] = true := by decide +kernel
theorem subd8_0_680 : subd8_0 [3, 0, 5] = true := by decide +kernel
theorem subd8_0_681 : subd8_0 [3, 0, 6] = true := by decide +kernel
theorem subd8_0_682 : subd8_0 [3, 0, 7] = true := by decide +kernel
theorem subd8_0_683 : subd8_0 [3, 1, -6] = true := by decide +kernel
theorem subd8_0_684 : subd8_0 [3, 1, -5] = true := by decide +kernel
theorem subd8_0_685 : subd8_0 [3, 1, -4] = true := by decide +kernel
theorem subd8_0_686 : subd8_0 [3, 1, -3] = true := by decide +kernel
theorem subd8_0_687 : subd8_0 [3, 1, -2] = true := by decide +kernel
theorem subd8_0_688 : subd8_0 [3, 1, -1] = true := by decide +kernel
theorem subd8_0_689 : subd8_0 [3, 1, 0] = true := by decide +kernel
theorem subd8_0_690 : subd8_0 [3, 1, 1] = true := by decide +kernel
theorem subd8_0_691 : subd8_0 [3, 1, 2] = true := by decide +kernel
theorem subd8_0_692 : subd8_0 [3, 1, 3] = true := by decide +kernel
theorem subd8_0_693 : subd8_0 [3, 1, 4] = true := by decide +kernel
theorem subd8_0_694 : subd8_0 [3, 1, 5] = true := by decide +kernel
theorem subd8_0_695 : subd8_0 [3, 1, 6] = true := by decide +kernel
theorem subd8_0_696 : subd8_0 [3, 1, 7] = true := by decide +kernel
theorem subd8_0_697 : subd8_0 [3, 1, 8] = true := by decide +kernel
theorem subd8_0_698 : subd8_0 [3, 2, -5] = true := by decide +kernel
theorem subd8_0_699 : subd8_0 [3, 2, -4] = true := by decide +kernel
theorem subd8_0_700 : subd8_0 [3, 2, -3] = true := by decide +kernel
theorem subd8_0_701 : subd8_0 [3, 2, -2] = true := by decide +kernel
theorem subd8_0_702 : subd8_0 [3, 2, -1] = true := by decide +kernel
theorem subd8_0_703 : subd8_0 [3, 2, 0] = true := by decide +kernel
theorem sbd8_0_21 : ∀ q ∈ blkd8_0_21, subd8_0 q = true := by
  unfold blkd8_0_21
  exact List.forall_mem_cons.2 ⟨subd8_0_672, List.forall_mem_cons.2 ⟨subd8_0_673, List.forall_mem_cons.2 ⟨subd8_0_674, List.forall_mem_cons.2 ⟨subd8_0_675, List.forall_mem_cons.2 ⟨subd8_0_676, List.forall_mem_cons.2 ⟨subd8_0_677, List.forall_mem_cons.2 ⟨subd8_0_678, List.forall_mem_cons.2 ⟨subd8_0_679, List.forall_mem_cons.2 ⟨subd8_0_680, List.forall_mem_cons.2 ⟨subd8_0_681, List.forall_mem_cons.2 ⟨subd8_0_682, List.forall_mem_cons.2 ⟨subd8_0_683, List.forall_mem_cons.2 ⟨subd8_0_684, List.forall_mem_cons.2 ⟨subd8_0_685, List.forall_mem_cons.2 ⟨subd8_0_686, List.forall_mem_cons.2 ⟨subd8_0_687, List.forall_mem_cons.2 ⟨subd8_0_688, List.forall_mem_cons.2 ⟨subd8_0_689, List.forall_mem_cons.2 ⟨subd8_0_690, List.forall_mem_cons.2 ⟨subd8_0_691, List.forall_mem_cons.2 ⟨subd8_0_692, List.forall_mem_cons.2 ⟨subd8_0_693, List.forall_mem_cons.2 ⟨subd8_0_694, List.forall_mem_cons.2 ⟨subd8_0_695, List.forall_mem_cons.2 ⟨subd8_0_696, List.forall_mem_cons.2 ⟨subd8_0_697, List.forall_mem_cons.2 ⟨subd8_0_698, List.forall_mem_cons.2 ⟨subd8_0_699, List.forall_mem_cons.2 ⟨subd8_0_700, List.forall_mem_cons.2 ⟨subd8_0_701, List.forall_mem_cons.2 ⟨subd8_0_702, List.forall_mem_cons.2 ⟨subd8_0_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_704 : subd8_0 [3, 2, 1] = true := by decide +kernel
theorem subd8_0_705 : subd8_0 [3, 2, 2] = true := by decide +kernel
theorem subd8_0_706 : subd8_0 [3, 2, 3] = true := by decide +kernel
theorem subd8_0_707 : subd8_0 [3, 2, 4] = true := by decide +kernel
theorem subd8_0_708 : subd8_0 [3, 2, 5] = true := by decide +kernel
theorem subd8_0_709 : subd8_0 [3, 2, 6] = true := by decide +kernel
theorem subd8_0_710 : subd8_0 [3, 2, 7] = true := by decide +kernel
theorem subd8_0_711 : subd8_0 [3, 2, 8] = true := by decide +kernel
theorem subd8_0_712 : subd8_0 [3, 3] = true := by decide +kernel
theorem subd8_0_713 : subd8_0 [3, 4] = true := by decide +kernel
theorem subd8_0_714 : subd8_0 [3, 5] = true := by decide +kernel
theorem subd8_0_715 : subd8_0 [3, 6] = true := by decide +kernel
theorem subd8_0_716 : subd8_0 [4, -6] = true := by decide +kernel
theorem subd8_0_717 : subd8_0 [4, -5] = true := by decide +kernel
theorem subd8_0_718 : subd8_0 [4, -4] = true := by decide +kernel
theorem subd8_0_719 : subd8_0 [4, -3] = true := by decide +kernel
theorem subd8_0_720 : subd8_0 [4, -2] = true := by decide +kernel
theorem subd8_0_721 : subd8_0 [4, -1] = true := by decide +kernel
theorem subd8_0_722 : subd8_0 [4, 0] = true := by decide +kernel
theorem subd8_0_723 : subd8_0 [4, 1] = true := by decide +kernel
theorem subd8_0_724 : subd8_0 [4, 2] = true := by decide +kernel
theorem subd8_0_725 : subd8_0 [4, 3] = true := by decide +kernel
theorem subd8_0_726 : subd8_0 [4, 4] = true := by decide +kernel
theorem subd8_0_727 : subd8_0 [4, 5] = true := by decide +kernel
theorem subd8_0_728 : subd8_0 [4, 6] = true := by decide +kernel
theorem subd8_0_729 : subd8_0 [5, -5] = true := by decide +kernel
theorem subd8_0_730 : subd8_0 [5, -4] = true := by decide +kernel
theorem subd8_0_731 : subd8_0 [5, -3] = true := by decide +kernel
theorem subd8_0_732 : subd8_0 [5, -2] = true := by decide +kernel
theorem subd8_0_733 : subd8_0 [5, -1] = true := by decide +kernel
theorem subd8_0_734 : subd8_0 [5, 0] = true := by decide +kernel
theorem subd8_0_735 : subd8_0 [5, 1] = true := by decide +kernel
theorem sbd8_0_22 : ∀ q ∈ blkd8_0_22, subd8_0 q = true := by
  unfold blkd8_0_22
  exact List.forall_mem_cons.2 ⟨subd8_0_704, List.forall_mem_cons.2 ⟨subd8_0_705, List.forall_mem_cons.2 ⟨subd8_0_706, List.forall_mem_cons.2 ⟨subd8_0_707, List.forall_mem_cons.2 ⟨subd8_0_708, List.forall_mem_cons.2 ⟨subd8_0_709, List.forall_mem_cons.2 ⟨subd8_0_710, List.forall_mem_cons.2 ⟨subd8_0_711, List.forall_mem_cons.2 ⟨subd8_0_712, List.forall_mem_cons.2 ⟨subd8_0_713, List.forall_mem_cons.2 ⟨subd8_0_714, List.forall_mem_cons.2 ⟨subd8_0_715, List.forall_mem_cons.2 ⟨subd8_0_716, List.forall_mem_cons.2 ⟨subd8_0_717, List.forall_mem_cons.2 ⟨subd8_0_718, List.forall_mem_cons.2 ⟨subd8_0_719, List.forall_mem_cons.2 ⟨subd8_0_720, List.forall_mem_cons.2 ⟨subd8_0_721, List.forall_mem_cons.2 ⟨subd8_0_722, List.forall_mem_cons.2 ⟨subd8_0_723, List.forall_mem_cons.2 ⟨subd8_0_724, List.forall_mem_cons.2 ⟨subd8_0_725, List.forall_mem_cons.2 ⟨subd8_0_726, List.forall_mem_cons.2 ⟨subd8_0_727, List.forall_mem_cons.2 ⟨subd8_0_728, List.forall_mem_cons.2 ⟨subd8_0_729, List.forall_mem_cons.2 ⟨subd8_0_730, List.forall_mem_cons.2 ⟨subd8_0_731, List.forall_mem_cons.2 ⟨subd8_0_732, List.forall_mem_cons.2 ⟨subd8_0_733, List.forall_mem_cons.2 ⟨subd8_0_734, List.forall_mem_cons.2 ⟨subd8_0_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_736 : subd8_0 [5, 2] = true := by decide +kernel
theorem subd8_0_737 : subd8_0 [5, 3] = true := by decide +kernel
theorem subd8_0_738 : subd8_0 [5, 4] = true := by decide +kernel
theorem subd8_0_739 : subd8_0 [5, 5] = true := by decide +kernel
theorem subd8_0_740 : subd8_0 [6, -3] = true := by decide +kernel
theorem subd8_0_741 : subd8_0 [6, -2] = true := by decide +kernel
theorem subd8_0_742 : subd8_0 [6, -1] = true := by decide +kernel
theorem subd8_0_743 : subd8_0 [6, 0] = true := by decide +kernel
theorem subd8_0_744 : subd8_0 [6, 1] = true := by decide +kernel
theorem subd8_0_745 : subd8_0 [6, 2] = true := by decide +kernel
theorem subd8_0_746 : subd8_0 [6, 3] = true := by decide +kernel
theorem sbd8_0_23 : ∀ q ∈ blkd8_0_23, subd8_0 q = true := by
  unfold blkd8_0_23
  exact List.forall_mem_cons.2 ⟨subd8_0_736, List.forall_mem_cons.2 ⟨subd8_0_737, List.forall_mem_cons.2 ⟨subd8_0_738, List.forall_mem_cons.2 ⟨subd8_0_739, List.forall_mem_cons.2 ⟨subd8_0_740, List.forall_mem_cons.2 ⟨subd8_0_741, List.forall_mem_cons.2 ⟨subd8_0_742, List.forall_mem_cons.2 ⟨subd8_0_743, List.forall_mem_cons.2 ⟨subd8_0_744, List.forall_mem_cons.2 ⟨subd8_0_745, List.forall_mem_cons.2 ⟨subd8_0_746, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [-5, -6] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-5, -5] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-5, -4] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-5, -3] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-5, -2] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-5, -1] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-5, 0] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-5, 1] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [-4, -7] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [-4, -6] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [-4, -5] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [-4, -4] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [-4, -3] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [-4, -2] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [-4, -1] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [-4, 0] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [-4, 1] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [-4, 2] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [-3, -7] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [-3, -6] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [-3, -5] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [-3, -4] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [-3, -3] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [-3, -2] = true := by decide +kernel
theorem subd8_1_24 : subd8_1 [-3, -1] = true := by decide +kernel
theorem subd8_1_25 : subd8_1 [-3, 0] = true := by decide +kernel
theorem subd8_1_26 : subd8_1 [-3, 1] = true := by decide +kernel
theorem subd8_1_27 : subd8_1 [-3, 2] = true := by decide +kernel
theorem subd8_1_28 : subd8_1 [-3, 3] = true := by decide +kernel
theorem subd8_1_29 : subd8_1 [-3, 4] = true := by decide +kernel
theorem subd8_1_30 : subd8_1 [-2, -7] = true := by decide +kernel
theorem subd8_1_31 : subd8_1 [-2, -6] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_cons.2 ⟨subd8_1_24, List.forall_mem_cons.2 ⟨subd8_1_25, List.forall_mem_cons.2 ⟨subd8_1_26, List.forall_mem_cons.2 ⟨subd8_1_27, List.forall_mem_cons.2 ⟨subd8_1_28, List.forall_mem_cons.2 ⟨subd8_1_29, List.forall_mem_cons.2 ⟨subd8_1_30, List.forall_mem_cons.2 ⟨subd8_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_32 : subd8_1 [-2, -5] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [-2, -4] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [-2, -3] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [-2, -2, -7] = true := by decide +kernel
theorem subd8_1_36 : subd8_1 [-2, -2, -6] = true := by decide +kernel
theorem subd8_1_37 : subd8_1 [-2, -2, -5] = true := by decide +kernel
theorem subd8_1_38 : subd8_1 [-2, -2, -4] = true := by decide +kernel
theorem subd8_1_39 : subd8_1 [-2, -2, -3] = true := by decide +kernel
theorem subd8_1_40 : subd8_1 [-2, -2, -2] = true := by decide +kernel
theorem subd8_1_41 : subd8_1 [-2, -2, -1] = true := by decide +kernel
theorem subd8_1_42 : subd8_1 [-2, -2, 0] = true := by decide +kernel
theorem subd8_1_43 : subd8_1 [-2, -2, 1] = true := by decide +kernel
theorem subd8_1_44 : subd8_1 [-2, -2, 2] = true := by decide +kernel
theorem subd8_1_45 : subd8_1 [-2, -2, 3] = true := by decide +kernel
theorem subd8_1_46 : subd8_1 [-2, -2, 4] = true := by decide +kernel
theorem subd8_1_47 : subd8_1 [-2, -2, 5] = true := by decide +kernel
theorem subd8_1_48 : subd8_1 [-2, -2, 6] = true := by decide +kernel
theorem subd8_1_49 : subd8_1 [-2, -1, -7] = true := by decide +kernel
theorem subd8_1_50 : subd8_1 [-2, -1, -6] = true := by decide +kernel
theorem subd8_1_51 : subd8_1 [-2, -1, -5] = true := by decide +kernel
theorem subd8_1_52 : subd8_1 [-2, -1, -4] = true := by decide +kernel
theorem subd8_1_53 : subd8_1 [-2, -1, -3] = true := by decide +kernel
theorem subd8_1_54 : subd8_1 [-2, -1, -2] = true := by decide +kernel
theorem subd8_1_55 : subd8_1 [-2, -1, -1] = true := by decide +kernel
theorem subd8_1_56 : subd8_1 [-2, -1, 0] = true := by decide +kernel
theorem subd8_1_57 : subd8_1 [-2, -1, 1] = true := by decide +kernel
theorem subd8_1_58 : subd8_1 [-2, -1, 2] = true := by decide +kernel
theorem subd8_1_59 : subd8_1 [-2, -1, 3] = true := by decide +kernel
theorem subd8_1_60 : subd8_1 [-2, -1, 4] = true := by decide +kernel
theorem subd8_1_61 : subd8_1 [-2, -1, 5] = true := by decide +kernel
theorem subd8_1_62 : subd8_1 [-2, -1, 6] = true := by decide +kernel
theorem subd8_1_63 : subd8_1 [-2, 0, -7] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_cons.2 ⟨subd8_1_36, List.forall_mem_cons.2 ⟨subd8_1_37, List.forall_mem_cons.2 ⟨subd8_1_38, List.forall_mem_cons.2 ⟨subd8_1_39, List.forall_mem_cons.2 ⟨subd8_1_40, List.forall_mem_cons.2 ⟨subd8_1_41, List.forall_mem_cons.2 ⟨subd8_1_42, List.forall_mem_cons.2 ⟨subd8_1_43, List.forall_mem_cons.2 ⟨subd8_1_44, List.forall_mem_cons.2 ⟨subd8_1_45, List.forall_mem_cons.2 ⟨subd8_1_46, List.forall_mem_cons.2 ⟨subd8_1_47, List.forall_mem_cons.2 ⟨subd8_1_48, List.forall_mem_cons.2 ⟨subd8_1_49, List.forall_mem_cons.2 ⟨subd8_1_50, List.forall_mem_cons.2 ⟨subd8_1_51, List.forall_mem_cons.2 ⟨subd8_1_52, List.forall_mem_cons.2 ⟨subd8_1_53, List.forall_mem_cons.2 ⟨subd8_1_54, List.forall_mem_cons.2 ⟨subd8_1_55, List.forall_mem_cons.2 ⟨subd8_1_56, List.forall_mem_cons.2 ⟨subd8_1_57, List.forall_mem_cons.2 ⟨subd8_1_58, List.forall_mem_cons.2 ⟨subd8_1_59, List.forall_mem_cons.2 ⟨subd8_1_60, List.forall_mem_cons.2 ⟨subd8_1_61, List.forall_mem_cons.2 ⟨subd8_1_62, List.forall_mem_cons.2 ⟨subd8_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
