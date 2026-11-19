import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_3_640 : subd11_3 [1, 0, 8] = true := by decide +kernel
theorem subd11_3_641 : subd11_3 [1, 1, -9] = true := by decide +kernel
theorem subd11_3_642 : subd11_3 [1, 1, -8] = true := by decide +kernel
theorem subd11_3_643 : subd11_3 [1, 1, -7] = true := by decide +kernel
theorem subd11_3_644 : subd11_3 [1, 1, -6] = true := by decide +kernel
theorem subd11_3_645 : subd11_3 [1, 1, -5] = true := by decide +kernel
theorem subd11_3_646 : subd11_3 [1, 1, -4] = true := by decide +kernel
theorem subd11_3_647 : subd11_3 [1, 1, -3] = true := by decide +kernel
theorem subd11_3_648 : subd11_3 [1, 1, -2] = true := by decide +kernel
theorem subd11_3_649 : subd11_3 [1, 1, -1] = true := by decide +kernel
theorem subd11_3_650 : subd11_3 [1, 1, 0] = true := by decide +kernel
theorem subd11_3_651 : subd11_3 [1, 1, 1] = true := by decide +kernel
theorem subd11_3_652 : subd11_3 [1, 1, 2] = true := by decide +kernel
theorem subd11_3_653 : subd11_3 [1, 1, 3] = true := by decide +kernel
theorem subd11_3_654 : subd11_3 [1, 1, 4] = true := by decide +kernel
theorem subd11_3_655 : subd11_3 [1, 1, 5] = true := by decide +kernel
theorem subd11_3_656 : subd11_3 [1, 1, 6] = true := by decide +kernel
theorem subd11_3_657 : subd11_3 [1, 1, 7] = true := by decide +kernel
theorem subd11_3_658 : subd11_3 [1, 1, 8] = true := by decide +kernel
theorem subd11_3_659 : subd11_3 [1, 1, 9] = true := by decide +kernel
theorem subd11_3_660 : subd11_3 [1, 2, -8] = true := by decide +kernel
theorem subd11_3_661 : subd11_3 [1, 2, -7] = true := by decide +kernel
theorem subd11_3_662 : subd11_3 [1, 2, -6] = true := by decide +kernel
theorem subd11_3_663 : subd11_3 [1, 2, -5] = true := by decide +kernel
theorem subd11_3_664 : subd11_3 [1, 2, -4] = true := by decide +kernel
theorem subd11_3_665 : subd11_3 [1, 2, -3] = true := by decide +kernel
theorem subd11_3_666 : subd11_3 [1, 2, -2] = true := by decide +kernel
theorem subd11_3_667 : subd11_3 [1, 2, -1] = true := by decide +kernel
theorem subd11_3_668 : subd11_3 [1, 2, 0] = true := by decide +kernel
theorem subd11_3_669 : subd11_3 [1, 2, 1] = true := by decide +kernel
theorem subd11_3_670 : subd11_3 [1, 2, 2] = true := by decide +kernel
theorem subd11_3_671 : subd11_3 [1, 2, 3] = true := by decide +kernel
theorem sbd11_3_20 : ∀ q ∈ blkd11_3_20, subd11_3 q = true := by
  unfold blkd11_3_20
  exact List.forall_mem_cons.2 ⟨subd11_3_640, List.forall_mem_cons.2 ⟨subd11_3_641, List.forall_mem_cons.2 ⟨subd11_3_642, List.forall_mem_cons.2 ⟨subd11_3_643, List.forall_mem_cons.2 ⟨subd11_3_644, List.forall_mem_cons.2 ⟨subd11_3_645, List.forall_mem_cons.2 ⟨subd11_3_646, List.forall_mem_cons.2 ⟨subd11_3_647, List.forall_mem_cons.2 ⟨subd11_3_648, List.forall_mem_cons.2 ⟨subd11_3_649, List.forall_mem_cons.2 ⟨subd11_3_650, List.forall_mem_cons.2 ⟨subd11_3_651, List.forall_mem_cons.2 ⟨subd11_3_652, List.forall_mem_cons.2 ⟨subd11_3_653, List.forall_mem_cons.2 ⟨subd11_3_654, List.forall_mem_cons.2 ⟨subd11_3_655, List.forall_mem_cons.2 ⟨subd11_3_656, List.forall_mem_cons.2 ⟨subd11_3_657, List.forall_mem_cons.2 ⟨subd11_3_658, List.forall_mem_cons.2 ⟨subd11_3_659, List.forall_mem_cons.2 ⟨subd11_3_660, List.forall_mem_cons.2 ⟨subd11_3_661, List.forall_mem_cons.2 ⟨subd11_3_662, List.forall_mem_cons.2 ⟨subd11_3_663, List.forall_mem_cons.2 ⟨subd11_3_664, List.forall_mem_cons.2 ⟨subd11_3_665, List.forall_mem_cons.2 ⟨subd11_3_666, List.forall_mem_cons.2 ⟨subd11_3_667, List.forall_mem_cons.2 ⟨subd11_3_668, List.forall_mem_cons.2 ⟨subd11_3_669, List.forall_mem_cons.2 ⟨subd11_3_670, List.forall_mem_cons.2 ⟨subd11_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_672 : subd11_3 [1, 2, 4] = true := by decide +kernel
theorem subd11_3_673 : subd11_3 [1, 2, 5] = true := by decide +kernel
theorem subd11_3_674 : subd11_3 [1, 2, 6] = true := by decide +kernel
theorem subd11_3_675 : subd11_3 [1, 2, 7] = true := by decide +kernel
theorem subd11_3_676 : subd11_3 [1, 2, 8] = true := by decide +kernel
theorem subd11_3_677 : subd11_3 [1, 3, -7] = true := by decide +kernel
theorem subd11_3_678 : subd11_3 [1, 3, -6] = true := by decide +kernel
theorem subd11_3_679 : subd11_3 [1, 3, -5] = true := by decide +kernel
theorem subd11_3_680 : subd11_3 [1, 3, -4] = true := by decide +kernel
theorem subd11_3_681 : subd11_3 [1, 3, -3] = true := by decide +kernel
theorem subd11_3_682 : subd11_3 [1, 3, -2] = true := by decide +kernel
theorem subd11_3_683 : subd11_3 [1, 3, -1] = true := by decide +kernel
theorem subd11_3_684 : subd11_3 [1, 3, 0] = true := by decide +kernel
theorem subd11_3_685 : subd11_3 [1, 3, 1] = true := by decide +kernel
theorem subd11_3_686 : subd11_3 [1, 3, 2] = true := by decide +kernel
theorem subd11_3_687 : subd11_3 [1, 3, 3] = true := by decide +kernel
theorem subd11_3_688 : subd11_3 [1, 3, 4] = true := by decide +kernel
theorem subd11_3_689 : subd11_3 [1, 3, 5] = true := by decide +kernel
theorem subd11_3_690 : subd11_3 [1, 3, 6] = true := by decide +kernel
theorem subd11_3_691 : subd11_3 [1, 3, 7] = true := by decide +kernel
theorem subd11_3_692 : subd11_3 [1, 3, 8] = true := by decide +kernel
theorem subd11_3_693 : subd11_3 [1, 4] = true := by decide +kernel
theorem subd11_3_694 : subd11_3 [1, 5] = true := by decide +kernel
theorem subd11_3_695 : subd11_3 [2, -6] = true := by decide +kernel
theorem subd11_3_696 : subd11_3 [2, -5] = true := by decide +kernel
theorem subd11_3_697 : subd11_3 [2, -4, -9] = true := by decide +kernel
theorem subd11_3_698 : subd11_3 [2, -4, -8] = true := by decide +kernel
theorem subd11_3_699 : subd11_3 [2, -4, -7] = true := by decide +kernel
theorem subd11_3_700 : subd11_3 [2, -4, -6] = true := by decide +kernel
theorem subd11_3_701 : subd11_3 [2, -4, -5] = true := by decide +kernel
theorem subd11_3_702 : subd11_3 [2, -4, -4] = true := by decide +kernel
theorem subd11_3_703 : subd11_3 [2, -4, -3] = true := by decide +kernel
theorem sbd11_3_21 : ∀ q ∈ blkd11_3_21, subd11_3 q = true := by
  unfold blkd11_3_21
  exact List.forall_mem_cons.2 ⟨subd11_3_672, List.forall_mem_cons.2 ⟨subd11_3_673, List.forall_mem_cons.2 ⟨subd11_3_674, List.forall_mem_cons.2 ⟨subd11_3_675, List.forall_mem_cons.2 ⟨subd11_3_676, List.forall_mem_cons.2 ⟨subd11_3_677, List.forall_mem_cons.2 ⟨subd11_3_678, List.forall_mem_cons.2 ⟨subd11_3_679, List.forall_mem_cons.2 ⟨subd11_3_680, List.forall_mem_cons.2 ⟨subd11_3_681, List.forall_mem_cons.2 ⟨subd11_3_682, List.forall_mem_cons.2 ⟨subd11_3_683, List.forall_mem_cons.2 ⟨subd11_3_684, List.forall_mem_cons.2 ⟨subd11_3_685, List.forall_mem_cons.2 ⟨subd11_3_686, List.forall_mem_cons.2 ⟨subd11_3_687, List.forall_mem_cons.2 ⟨subd11_3_688, List.forall_mem_cons.2 ⟨subd11_3_689, List.forall_mem_cons.2 ⟨subd11_3_690, List.forall_mem_cons.2 ⟨subd11_3_691, List.forall_mem_cons.2 ⟨subd11_3_692, List.forall_mem_cons.2 ⟨subd11_3_693, List.forall_mem_cons.2 ⟨subd11_3_694, List.forall_mem_cons.2 ⟨subd11_3_695, List.forall_mem_cons.2 ⟨subd11_3_696, List.forall_mem_cons.2 ⟨subd11_3_697, List.forall_mem_cons.2 ⟨subd11_3_698, List.forall_mem_cons.2 ⟨subd11_3_699, List.forall_mem_cons.2 ⟨subd11_3_700, List.forall_mem_cons.2 ⟨subd11_3_701, List.forall_mem_cons.2 ⟨subd11_3_702, List.forall_mem_cons.2 ⟨subd11_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_704 : subd11_3 [2, -4, -2] = true := by decide +kernel
theorem subd11_3_705 : subd11_3 [2, -4, -1] = true := by decide +kernel
theorem subd11_3_706 : subd11_3 [2, -4, 0] = true := by decide +kernel
theorem subd11_3_707 : subd11_3 [2, -4, 1] = true := by decide +kernel
theorem subd11_3_708 : subd11_3 [2, -4, 2] = true := by decide +kernel
theorem subd11_3_709 : subd11_3 [2, -4, 3] = true := by decide +kernel
theorem subd11_3_710 : subd11_3 [2, -4, 4] = true := by decide +kernel
theorem subd11_3_711 : subd11_3 [2, -3, -10] = true := by decide +kernel
theorem subd11_3_712 : subd11_3 [2, -3, -9] = true := by decide +kernel
theorem subd11_3_713 : subd11_3 [2, -3, -8] = true := by decide +kernel
theorem subd11_3_714 : subd11_3 [2, -3, -7] = true := by decide +kernel
theorem subd11_3_715 : subd11_3 [2, -3, -6] = true := by decide +kernel
theorem subd11_3_716 : subd11_3 [2, -3, -5] = true := by decide +kernel
theorem subd11_3_717 : subd11_3 [2, -3, -4] = true := by decide +kernel
theorem subd11_3_718 : subd11_3 [2, -3, -3] = true := by decide +kernel
theorem subd11_3_719 : subd11_3 [2, -3, -2] = true := by decide +kernel
theorem subd11_3_720 : subd11_3 [2, -3, -1] = true := by decide +kernel
theorem subd11_3_721 : subd11_3 [2, -3, 0] = true := by decide +kernel
theorem subd11_3_722 : subd11_3 [2, -3, 1] = true := by decide +kernel
theorem subd11_3_723 : subd11_3 [2, -3, 2] = true := by decide +kernel
theorem subd11_3_724 : subd11_3 [2, -3, 3] = true := by decide +kernel
theorem subd11_3_725 : subd11_3 [2, -3, 4] = true := by decide +kernel
theorem subd11_3_726 : subd11_3 [2, -3, 5] = true := by decide +kernel
theorem subd11_3_727 : subd11_3 [2, -2, -10] = true := by decide +kernel
theorem subd11_3_728 : subd11_3 [2, -2, -9] = true := by decide +kernel
theorem subd11_3_729 : subd11_3 [2, -2, -8] = true := by decide +kernel
theorem subd11_3_730 : subd11_3 [2, -2, -7] = true := by decide +kernel
theorem subd11_3_731 : subd11_3 [2, -2, -6] = true := by decide +kernel
theorem subd11_3_732 : subd11_3 [2, -2, -5] = true := by decide +kernel
theorem subd11_3_733 : subd11_3 [2, -2, -4] = true := by decide +kernel
theorem subd11_3_734 : subd11_3 [2, -2, -3] = true := by decide +kernel
theorem subd11_3_735 : subd11_3 [2, -2, -2] = true := by decide +kernel
theorem sbd11_3_22 : ∀ q ∈ blkd11_3_22, subd11_3 q = true := by
  unfold blkd11_3_22
  exact List.forall_mem_cons.2 ⟨subd11_3_704, List.forall_mem_cons.2 ⟨subd11_3_705, List.forall_mem_cons.2 ⟨subd11_3_706, List.forall_mem_cons.2 ⟨subd11_3_707, List.forall_mem_cons.2 ⟨subd11_3_708, List.forall_mem_cons.2 ⟨subd11_3_709, List.forall_mem_cons.2 ⟨subd11_3_710, List.forall_mem_cons.2 ⟨subd11_3_711, List.forall_mem_cons.2 ⟨subd11_3_712, List.forall_mem_cons.2 ⟨subd11_3_713, List.forall_mem_cons.2 ⟨subd11_3_714, List.forall_mem_cons.2 ⟨subd11_3_715, List.forall_mem_cons.2 ⟨subd11_3_716, List.forall_mem_cons.2 ⟨subd11_3_717, List.forall_mem_cons.2 ⟨subd11_3_718, List.forall_mem_cons.2 ⟨subd11_3_719, List.forall_mem_cons.2 ⟨subd11_3_720, List.forall_mem_cons.2 ⟨subd11_3_721, List.forall_mem_cons.2 ⟨subd11_3_722, List.forall_mem_cons.2 ⟨subd11_3_723, List.forall_mem_cons.2 ⟨subd11_3_724, List.forall_mem_cons.2 ⟨subd11_3_725, List.forall_mem_cons.2 ⟨subd11_3_726, List.forall_mem_cons.2 ⟨subd11_3_727, List.forall_mem_cons.2 ⟨subd11_3_728, List.forall_mem_cons.2 ⟨subd11_3_729, List.forall_mem_cons.2 ⟨subd11_3_730, List.forall_mem_cons.2 ⟨subd11_3_731, List.forall_mem_cons.2 ⟨subd11_3_732, List.forall_mem_cons.2 ⟨subd11_3_733, List.forall_mem_cons.2 ⟨subd11_3_734, List.forall_mem_cons.2 ⟨subd11_3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_736 : subd11_3 [2, -2, -1] = true := by decide +kernel
theorem subd11_3_737 : subd11_3 [2, -2, 0] = true := by decide +kernel
theorem subd11_3_738 : subd11_3 [2, -2, 1] = true := by decide +kernel
theorem subd11_3_739 : subd11_3 [2, -2, 2] = true := by decide +kernel
theorem subd11_3_740 : subd11_3 [2, -2, 3] = true := by decide +kernel
theorem subd11_3_741 : subd11_3 [2, -2, 4] = true := by decide +kernel
theorem subd11_3_742 : subd11_3 [2, -2, 5] = true := by decide +kernel
theorem subd11_3_743 : subd11_3 [2, -2, 6] = true := by decide +kernel
theorem subd11_3_744 : subd11_3 [2, -1, -10] = true := by decide +kernel
theorem subd11_3_745 : subd11_3 [2, -1, -9] = true := by decide +kernel
theorem subd11_3_746 : subd11_3 [2, -1, -8] = true := by decide +kernel
theorem subd11_3_747 : subd11_3 [2, -1, -7] = true := by decide +kernel
theorem subd11_3_748 : subd11_3 [2, -1, -6] = true := by decide +kernel
theorem subd11_3_749 : subd11_3 [2, -1, -5] = true := by decide +kernel
theorem subd11_3_750 : subd11_3 [2, -1, -4] = true := by decide +kernel
theorem subd11_3_751 : subd11_3 [2, -1, -3] = true := by decide +kernel
theorem subd11_3_752 : subd11_3 [2, -1, -2] = true := by decide +kernel
theorem subd11_3_753 : subd11_3 [2, -1, -1] = true := by decide +kernel
theorem subd11_3_754 : subd11_3 [2, -1, 0] = true := by decide +kernel
theorem subd11_3_755 : subd11_3 [2, -1, 1] = true := by decide +kernel
theorem subd11_3_756 : subd11_3 [2, -1, 2] = true := by decide +kernel
theorem subd11_3_757 : subd11_3 [2, -1, 3] = true := by decide +kernel
theorem subd11_3_758 : subd11_3 [2, -1, 4] = true := by decide +kernel
theorem subd11_3_759 : subd11_3 [2, -1, 5] = true := by decide +kernel
theorem subd11_3_760 : subd11_3 [2, -1, 6] = true := by decide +kernel
theorem subd11_3_761 : subd11_3 [2, -1, 7] = true := by decide +kernel
theorem subd11_3_762 : subd11_3 [2, 0, -10] = true := by decide +kernel
theorem subd11_3_763 : subd11_3 [2, 0, -9] = true := by decide +kernel
theorem subd11_3_764 : subd11_3 [2, 0, -8] = true := by decide +kernel
theorem subd11_3_765 : subd11_3 [2, 0, -7] = true := by decide +kernel
theorem subd11_3_766 : subd11_3 [2, 0, -6] = true := by decide +kernel
theorem subd11_3_767 : subd11_3 [2, 0, -5] = true := by decide +kernel
theorem sbd11_3_23 : ∀ q ∈ blkd11_3_23, subd11_3 q = true := by
  unfold blkd11_3_23
  exact List.forall_mem_cons.2 ⟨subd11_3_736, List.forall_mem_cons.2 ⟨subd11_3_737, List.forall_mem_cons.2 ⟨subd11_3_738, List.forall_mem_cons.2 ⟨subd11_3_739, List.forall_mem_cons.2 ⟨subd11_3_740, List.forall_mem_cons.2 ⟨subd11_3_741, List.forall_mem_cons.2 ⟨subd11_3_742, List.forall_mem_cons.2 ⟨subd11_3_743, List.forall_mem_cons.2 ⟨subd11_3_744, List.forall_mem_cons.2 ⟨subd11_3_745, List.forall_mem_cons.2 ⟨subd11_3_746, List.forall_mem_cons.2 ⟨subd11_3_747, List.forall_mem_cons.2 ⟨subd11_3_748, List.forall_mem_cons.2 ⟨subd11_3_749, List.forall_mem_cons.2 ⟨subd11_3_750, List.forall_mem_cons.2 ⟨subd11_3_751, List.forall_mem_cons.2 ⟨subd11_3_752, List.forall_mem_cons.2 ⟨subd11_3_753, List.forall_mem_cons.2 ⟨subd11_3_754, List.forall_mem_cons.2 ⟨subd11_3_755, List.forall_mem_cons.2 ⟨subd11_3_756, List.forall_mem_cons.2 ⟨subd11_3_757, List.forall_mem_cons.2 ⟨subd11_3_758, List.forall_mem_cons.2 ⟨subd11_3_759, List.forall_mem_cons.2 ⟨subd11_3_760, List.forall_mem_cons.2 ⟨subd11_3_761, List.forall_mem_cons.2 ⟨subd11_3_762, List.forall_mem_cons.2 ⟨subd11_3_763, List.forall_mem_cons.2 ⟨subd11_3_764, List.forall_mem_cons.2 ⟨subd11_3_765, List.forall_mem_cons.2 ⟨subd11_3_766, List.forall_mem_cons.2 ⟨subd11_3_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_768 : subd11_3 [2, 0, -4] = true := by decide +kernel
theorem subd11_3_769 : subd11_3 [2, 0, -3] = true := by decide +kernel
theorem subd11_3_770 : subd11_3 [2, 0, -2] = true := by decide +kernel
theorem subd11_3_771 : subd11_3 [2, 0, -1] = true := by decide +kernel
theorem subd11_3_772 : subd11_3 [2, 0, 0] = true := by decide +kernel
theorem subd11_3_773 : subd11_3 [2, 0, 1] = true := by decide +kernel
theorem subd11_3_774 : subd11_3 [2, 0, 2] = true := by decide +kernel
theorem subd11_3_775 : subd11_3 [2, 0, 3] = true := by decide +kernel
theorem subd11_3_776 : subd11_3 [2, 0, 4] = true := by decide +kernel
theorem subd11_3_777 : subd11_3 [2, 0, 5] = true := by decide +kernel
theorem subd11_3_778 : subd11_3 [2, 0, 6] = true := by decide +kernel
theorem subd11_3_779 : subd11_3 [2, 0, 7] = true := by decide +kernel
theorem subd11_3_780 : subd11_3 [2, 0, 8] = true := by decide +kernel
theorem subd11_3_781 : subd11_3 [2, 1, -9] = true := by decide +kernel
theorem subd11_3_782 : subd11_3 [2, 1, -8] = true := by decide +kernel
theorem subd11_3_783 : subd11_3 [2, 1, -7] = true := by decide +kernel
theorem subd11_3_784 : subd11_3 [2, 1, -6] = true := by decide +kernel
theorem subd11_3_785 : subd11_3 [2, 1, -5] = true := by decide +kernel
theorem subd11_3_786 : subd11_3 [2, 1, -4] = true := by decide +kernel
theorem subd11_3_787 : subd11_3 [2, 1, -3] = true := by decide +kernel
theorem subd11_3_788 : subd11_3 [2, 1, -2] = true := by decide +kernel
theorem subd11_3_789 : subd11_3 [2, 1, -1] = true := by decide +kernel
theorem subd11_3_790 : subd11_3 [2, 1, 0] = true := by decide +kernel
theorem subd11_3_791 : subd11_3 [2, 1, 1] = true := by decide +kernel
theorem subd11_3_792 : subd11_3 [2, 1, 2] = true := by decide +kernel
theorem subd11_3_793 : subd11_3 [2, 1, 3] = true := by decide +kernel
theorem subd11_3_794 : subd11_3 [2, 1, 4] = true := by decide +kernel
theorem subd11_3_795 : subd11_3 [2, 1, 5] = true := by decide +kernel
theorem subd11_3_796 : subd11_3 [2, 1, 6] = true := by decide +kernel
theorem subd11_3_797 : subd11_3 [2, 1, 7] = true := by decide +kernel
theorem subd11_3_798 : subd11_3 [2, 1, 8] = true := by decide +kernel
theorem subd11_3_799 : subd11_3 [2, 2, -8] = true := by decide +kernel
theorem sbd11_3_24 : ∀ q ∈ blkd11_3_24, subd11_3 q = true := by
  unfold blkd11_3_24
  exact List.forall_mem_cons.2 ⟨subd11_3_768, List.forall_mem_cons.2 ⟨subd11_3_769, List.forall_mem_cons.2 ⟨subd11_3_770, List.forall_mem_cons.2 ⟨subd11_3_771, List.forall_mem_cons.2 ⟨subd11_3_772, List.forall_mem_cons.2 ⟨subd11_3_773, List.forall_mem_cons.2 ⟨subd11_3_774, List.forall_mem_cons.2 ⟨subd11_3_775, List.forall_mem_cons.2 ⟨subd11_3_776, List.forall_mem_cons.2 ⟨subd11_3_777, List.forall_mem_cons.2 ⟨subd11_3_778, List.forall_mem_cons.2 ⟨subd11_3_779, List.forall_mem_cons.2 ⟨subd11_3_780, List.forall_mem_cons.2 ⟨subd11_3_781, List.forall_mem_cons.2 ⟨subd11_3_782, List.forall_mem_cons.2 ⟨subd11_3_783, List.forall_mem_cons.2 ⟨subd11_3_784, List.forall_mem_cons.2 ⟨subd11_3_785, List.forall_mem_cons.2 ⟨subd11_3_786, List.forall_mem_cons.2 ⟨subd11_3_787, List.forall_mem_cons.2 ⟨subd11_3_788, List.forall_mem_cons.2 ⟨subd11_3_789, List.forall_mem_cons.2 ⟨subd11_3_790, List.forall_mem_cons.2 ⟨subd11_3_791, List.forall_mem_cons.2 ⟨subd11_3_792, List.forall_mem_cons.2 ⟨subd11_3_793, List.forall_mem_cons.2 ⟨subd11_3_794, List.forall_mem_cons.2 ⟨subd11_3_795, List.forall_mem_cons.2 ⟨subd11_3_796, List.forall_mem_cons.2 ⟨subd11_3_797, List.forall_mem_cons.2 ⟨subd11_3_798, List.forall_mem_cons.2 ⟨subd11_3_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_800 : subd11_3 [2, 2, -7] = true := by decide +kernel
theorem subd11_3_801 : subd11_3 [2, 2, -6] = true := by decide +kernel
theorem subd11_3_802 : subd11_3 [2, 2, -5] = true := by decide +kernel
theorem subd11_3_803 : subd11_3 [2, 2, -4] = true := by decide +kernel
theorem subd11_3_804 : subd11_3 [2, 2, -3] = true := by decide +kernel
theorem subd11_3_805 : subd11_3 [2, 2, -2] = true := by decide +kernel
theorem subd11_3_806 : subd11_3 [2, 2, -1] = true := by decide +kernel
theorem subd11_3_807 : subd11_3 [2, 2, 0] = true := by decide +kernel
theorem subd11_3_808 : subd11_3 [2, 2, 1] = true := by decide +kernel
theorem subd11_3_809 : subd11_3 [2, 2, 2] = true := by decide +kernel
theorem subd11_3_810 : subd11_3 [2, 2, 3] = true := by decide +kernel
theorem subd11_3_811 : subd11_3 [2, 2, 4] = true := by decide +kernel
theorem subd11_3_812 : subd11_3 [2, 2, 5] = true := by decide +kernel
theorem subd11_3_813 : subd11_3 [2, 2, 6] = true := by decide +kernel
theorem subd11_3_814 : subd11_3 [2, 2, 7] = true := by decide +kernel
theorem subd11_3_815 : subd11_3 [2, 3, -7] = true := by decide +kernel
theorem subd11_3_816 : subd11_3 [2, 3, -6] = true := by decide +kernel
theorem subd11_3_817 : subd11_3 [2, 3, -5] = true := by decide +kernel
theorem subd11_3_818 : subd11_3 [2, 3, -4] = true := by decide +kernel
theorem subd11_3_819 : subd11_3 [2, 3, -3] = true := by decide +kernel
theorem subd11_3_820 : subd11_3 [2, 3, -2] = true := by decide +kernel
theorem subd11_3_821 : subd11_3 [2, 3, -1] = true := by decide +kernel
theorem subd11_3_822 : subd11_3 [2, 3, 0] = true := by decide +kernel
theorem subd11_3_823 : subd11_3 [2, 3, 1] = true := by decide +kernel
theorem subd11_3_824 : subd11_3 [2, 3, 2] = true := by decide +kernel
theorem subd11_3_825 : subd11_3 [2, 3, 3] = true := by decide +kernel
theorem subd11_3_826 : subd11_3 [2, 3, 4] = true := by decide +kernel
theorem subd11_3_827 : subd11_3 [2, 3, 5] = true := by decide +kernel
theorem subd11_3_828 : subd11_3 [2, 3, 6] = true := by decide +kernel
theorem subd11_3_829 : subd11_3 [2, 3, 7] = true := by decide +kernel
theorem subd11_3_830 : subd11_3 [2, 4] = true := by decide +kernel
theorem subd11_3_831 : subd11_3 [3, -6] = true := by decide +kernel
theorem sbd11_3_25 : ∀ q ∈ blkd11_3_25, subd11_3 q = true := by
  unfold blkd11_3_25
  exact List.forall_mem_cons.2 ⟨subd11_3_800, List.forall_mem_cons.2 ⟨subd11_3_801, List.forall_mem_cons.2 ⟨subd11_3_802, List.forall_mem_cons.2 ⟨subd11_3_803, List.forall_mem_cons.2 ⟨subd11_3_804, List.forall_mem_cons.2 ⟨subd11_3_805, List.forall_mem_cons.2 ⟨subd11_3_806, List.forall_mem_cons.2 ⟨subd11_3_807, List.forall_mem_cons.2 ⟨subd11_3_808, List.forall_mem_cons.2 ⟨subd11_3_809, List.forall_mem_cons.2 ⟨subd11_3_810, List.forall_mem_cons.2 ⟨subd11_3_811, List.forall_mem_cons.2 ⟨subd11_3_812, List.forall_mem_cons.2 ⟨subd11_3_813, List.forall_mem_cons.2 ⟨subd11_3_814, List.forall_mem_cons.2 ⟨subd11_3_815, List.forall_mem_cons.2 ⟨subd11_3_816, List.forall_mem_cons.2 ⟨subd11_3_817, List.forall_mem_cons.2 ⟨subd11_3_818, List.forall_mem_cons.2 ⟨subd11_3_819, List.forall_mem_cons.2 ⟨subd11_3_820, List.forall_mem_cons.2 ⟨subd11_3_821, List.forall_mem_cons.2 ⟨subd11_3_822, List.forall_mem_cons.2 ⟨subd11_3_823, List.forall_mem_cons.2 ⟨subd11_3_824, List.forall_mem_cons.2 ⟨subd11_3_825, List.forall_mem_cons.2 ⟨subd11_3_826, List.forall_mem_cons.2 ⟨subd11_3_827, List.forall_mem_cons.2 ⟨subd11_3_828, List.forall_mem_cons.2 ⟨subd11_3_829, List.forall_mem_cons.2 ⟨subd11_3_830, List.forall_mem_cons.2 ⟨subd11_3_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_832 : subd11_3 [3, -5] = true := by decide +kernel
theorem subd11_3_833 : subd11_3 [3, -4] = true := by decide +kernel
theorem subd11_3_834 : subd11_3 [3, -3, -9] = true := by decide +kernel
theorem subd11_3_835 : subd11_3 [3, -3, -8] = true := by decide +kernel
theorem subd11_3_836 : subd11_3 [3, -3, -7] = true := by decide +kernel
theorem subd11_3_837 : subd11_3 [3, -3, -6] = true := by decide +kernel
theorem subd11_3_838 : subd11_3 [3, -3, -5] = true := by decide +kernel
theorem subd11_3_839 : subd11_3 [3, -3, -4] = true := by decide +kernel
theorem subd11_3_840 : subd11_3 [3, -3, -3] = true := by decide +kernel
theorem subd11_3_841 : subd11_3 [3, -3, -2] = true := by decide +kernel
theorem subd11_3_842 : subd11_3 [3, -3, -1] = true := by decide +kernel
theorem subd11_3_843 : subd11_3 [3, -3, 0] = true := by decide +kernel
theorem subd11_3_844 : subd11_3 [3, -3, 1] = true := by decide +kernel
theorem subd11_3_845 : subd11_3 [3, -3, 2] = true := by decide +kernel
theorem subd11_3_846 : subd11_3 [3, -3, 3] = true := by decide +kernel
theorem subd11_3_847 : subd11_3 [3, -3, 4] = true := by decide +kernel
theorem subd11_3_848 : subd11_3 [3, -2, -10] = true := by decide +kernel
theorem subd11_3_849 : subd11_3 [3, -2, -9] = true := by decide +kernel
theorem subd11_3_850 : subd11_3 [3, -2, -8] = true := by decide +kernel
theorem subd11_3_851 : subd11_3 [3, -2, -7] = true := by decide +kernel
theorem subd11_3_852 : subd11_3 [3, -2, -6] = true := by decide +kernel
theorem subd11_3_853 : subd11_3 [3, -2, -5] = true := by decide +kernel
theorem subd11_3_854 : subd11_3 [3, -2, -4] = true := by decide +kernel
theorem subd11_3_855 : subd11_3 [3, -2, -3] = true := by decide +kernel
theorem subd11_3_856 : subd11_3 [3, -2, -2] = true := by decide +kernel
theorem subd11_3_857 : subd11_3 [3, -2, -1] = true := by decide +kernel
theorem subd11_3_858 : subd11_3 [3, -2, 0] = true := by decide +kernel
theorem subd11_3_859 : subd11_3 [3, -2, 1] = true := by decide +kernel
theorem subd11_3_860 : subd11_3 [3, -2, 2] = true := by decide +kernel
theorem subd11_3_861 : subd11_3 [3, -2, 3] = true := by decide +kernel
theorem subd11_3_862 : subd11_3 [3, -2, 4] = true := by decide +kernel
theorem subd11_3_863 : subd11_3 [3, -2, 5] = true := by decide +kernel
theorem sbd11_3_26 : ∀ q ∈ blkd11_3_26, subd11_3 q = true := by
  unfold blkd11_3_26
  exact List.forall_mem_cons.2 ⟨subd11_3_832, List.forall_mem_cons.2 ⟨subd11_3_833, List.forall_mem_cons.2 ⟨subd11_3_834, List.forall_mem_cons.2 ⟨subd11_3_835, List.forall_mem_cons.2 ⟨subd11_3_836, List.forall_mem_cons.2 ⟨subd11_3_837, List.forall_mem_cons.2 ⟨subd11_3_838, List.forall_mem_cons.2 ⟨subd11_3_839, List.forall_mem_cons.2 ⟨subd11_3_840, List.forall_mem_cons.2 ⟨subd11_3_841, List.forall_mem_cons.2 ⟨subd11_3_842, List.forall_mem_cons.2 ⟨subd11_3_843, List.forall_mem_cons.2 ⟨subd11_3_844, List.forall_mem_cons.2 ⟨subd11_3_845, List.forall_mem_cons.2 ⟨subd11_3_846, List.forall_mem_cons.2 ⟨subd11_3_847, List.forall_mem_cons.2 ⟨subd11_3_848, List.forall_mem_cons.2 ⟨subd11_3_849, List.forall_mem_cons.2 ⟨subd11_3_850, List.forall_mem_cons.2 ⟨subd11_3_851, List.forall_mem_cons.2 ⟨subd11_3_852, List.forall_mem_cons.2 ⟨subd11_3_853, List.forall_mem_cons.2 ⟨subd11_3_854, List.forall_mem_cons.2 ⟨subd11_3_855, List.forall_mem_cons.2 ⟨subd11_3_856, List.forall_mem_cons.2 ⟨subd11_3_857, List.forall_mem_cons.2 ⟨subd11_3_858, List.forall_mem_cons.2 ⟨subd11_3_859, List.forall_mem_cons.2 ⟨subd11_3_860, List.forall_mem_cons.2 ⟨subd11_3_861, List.forall_mem_cons.2 ⟨subd11_3_862, List.forall_mem_cons.2 ⟨subd11_3_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_864 : subd11_3 [3, -1, -10] = true := by decide +kernel
theorem subd11_3_865 : subd11_3 [3, -1, -9] = true := by decide +kernel
theorem subd11_3_866 : subd11_3 [3, -1, -8] = true := by decide +kernel
theorem subd11_3_867 : subd11_3 [3, -1, -7] = true := by decide +kernel
theorem subd11_3_868 : subd11_3 [3, -1, -6] = true := by decide +kernel
theorem subd11_3_869 : subd11_3 [3, -1, -5] = true := by decide +kernel
theorem subd11_3_870 : subd11_3 [3, -1, -4] = true := by decide +kernel
theorem subd11_3_871 : subd11_3 [3, -1, -3] = true := by decide +kernel
theorem subd11_3_872 : subd11_3 [3, -1, -2] = true := by decide +kernel
theorem subd11_3_873 : subd11_3 [3, -1, -1] = true := by decide +kernel
theorem subd11_3_874 : subd11_3 [3, -1, 0] = true := by decide +kernel
theorem subd11_3_875 : subd11_3 [3, -1, 1] = true := by decide +kernel
theorem subd11_3_876 : subd11_3 [3, -1, 2] = true := by decide +kernel
theorem subd11_3_877 : subd11_3 [3, -1, 3] = true := by decide +kernel
theorem subd11_3_878 : subd11_3 [3, -1, 4] = true := by decide +kernel
theorem subd11_3_879 : subd11_3 [3, -1, 5] = true := by decide +kernel
theorem subd11_3_880 : subd11_3 [3, -1, 6] = true := by decide +kernel
theorem subd11_3_881 : subd11_3 [3, 0, -9] = true := by decide +kernel
theorem subd11_3_882 : subd11_3 [3, 0, -8] = true := by decide +kernel
theorem subd11_3_883 : subd11_3 [3, 0, -7] = true := by decide +kernel
theorem subd11_3_884 : subd11_3 [3, 0, -6] = true := by decide +kernel
theorem subd11_3_885 : subd11_3 [3, 0, -5] = true := by decide +kernel
theorem subd11_3_886 : subd11_3 [3, 0, -4] = true := by decide +kernel
theorem subd11_3_887 : subd11_3 [3, 0, -3] = true := by decide +kernel
theorem subd11_3_888 : subd11_3 [3, 0, -2] = true := by decide +kernel
theorem subd11_3_889 : subd11_3 [3, 0, -1] = true := by decide +kernel
theorem subd11_3_890 : subd11_3 [3, 0, 0] = true := by decide +kernel
theorem subd11_3_891 : subd11_3 [3, 0, 1] = true := by decide +kernel
theorem subd11_3_892 : subd11_3 [3, 0, 2] = true := by decide +kernel
theorem subd11_3_893 : subd11_3 [3, 0, 3] = true := by decide +kernel
theorem subd11_3_894 : subd11_3 [3, 0, 4] = true := by decide +kernel
theorem subd11_3_895 : subd11_3 [3, 0, 5] = true := by decide +kernel
theorem sbd11_3_27 : ∀ q ∈ blkd11_3_27, subd11_3 q = true := by
  unfold blkd11_3_27
  exact List.forall_mem_cons.2 ⟨subd11_3_864, List.forall_mem_cons.2 ⟨subd11_3_865, List.forall_mem_cons.2 ⟨subd11_3_866, List.forall_mem_cons.2 ⟨subd11_3_867, List.forall_mem_cons.2 ⟨subd11_3_868, List.forall_mem_cons.2 ⟨subd11_3_869, List.forall_mem_cons.2 ⟨subd11_3_870, List.forall_mem_cons.2 ⟨subd11_3_871, List.forall_mem_cons.2 ⟨subd11_3_872, List.forall_mem_cons.2 ⟨subd11_3_873, List.forall_mem_cons.2 ⟨subd11_3_874, List.forall_mem_cons.2 ⟨subd11_3_875, List.forall_mem_cons.2 ⟨subd11_3_876, List.forall_mem_cons.2 ⟨subd11_3_877, List.forall_mem_cons.2 ⟨subd11_3_878, List.forall_mem_cons.2 ⟨subd11_3_879, List.forall_mem_cons.2 ⟨subd11_3_880, List.forall_mem_cons.2 ⟨subd11_3_881, List.forall_mem_cons.2 ⟨subd11_3_882, List.forall_mem_cons.2 ⟨subd11_3_883, List.forall_mem_cons.2 ⟨subd11_3_884, List.forall_mem_cons.2 ⟨subd11_3_885, List.forall_mem_cons.2 ⟨subd11_3_886, List.forall_mem_cons.2 ⟨subd11_3_887, List.forall_mem_cons.2 ⟨subd11_3_888, List.forall_mem_cons.2 ⟨subd11_3_889, List.forall_mem_cons.2 ⟨subd11_3_890, List.forall_mem_cons.2 ⟨subd11_3_891, List.forall_mem_cons.2 ⟨subd11_3_892, List.forall_mem_cons.2 ⟨subd11_3_893, List.forall_mem_cons.2 ⟨subd11_3_894, List.forall_mem_cons.2 ⟨subd11_3_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_896 : subd11_3 [3, 0, 6] = true := by decide +kernel
theorem subd11_3_897 : subd11_3 [3, 1, -8] = true := by decide +kernel
theorem subd11_3_898 : subd11_3 [3, 1, -7] = true := by decide +kernel
theorem subd11_3_899 : subd11_3 [3, 1, -6] = true := by decide +kernel
theorem subd11_3_900 : subd11_3 [3, 1, -5] = true := by decide +kernel
theorem subd11_3_901 : subd11_3 [3, 1, -4] = true := by decide +kernel
theorem subd11_3_902 : subd11_3 [3, 1, -3] = true := by decide +kernel
theorem subd11_3_903 : subd11_3 [3, 1, -2] = true := by decide +kernel
theorem subd11_3_904 : subd11_3 [3, 1, -1] = true := by decide +kernel
theorem subd11_3_905 : subd11_3 [3, 1, 0] = true := by decide +kernel
theorem subd11_3_906 : subd11_3 [3, 1, 1] = true := by decide +kernel
theorem subd11_3_907 : subd11_3 [3, 1, 2] = true := by decide +kernel
theorem subd11_3_908 : subd11_3 [3, 1, 3] = true := by decide +kernel
theorem subd11_3_909 : subd11_3 [3, 1, 4] = true := by decide +kernel
theorem subd11_3_910 : subd11_3 [3, 1, 5] = true := by decide +kernel
theorem subd11_3_911 : subd11_3 [3, 1, 6] = true := by decide +kernel
theorem subd11_3_912 : subd11_3 [3, 2, -7] = true := by decide +kernel
theorem subd11_3_913 : subd11_3 [3, 2, -6] = true := by decide +kernel
theorem subd11_3_914 : subd11_3 [3, 2, -5] = true := by decide +kernel
theorem subd11_3_915 : subd11_3 [3, 2, -4] = true := by decide +kernel
theorem subd11_3_916 : subd11_3 [3, 2, -3] = true := by decide +kernel
theorem subd11_3_917 : subd11_3 [3, 2, -2] = true := by decide +kernel
theorem subd11_3_918 : subd11_3 [3, 2, -1] = true := by decide +kernel
theorem subd11_3_919 : subd11_3 [3, 2, 0] = true := by decide +kernel
theorem subd11_3_920 : subd11_3 [3, 2, 1] = true := by decide +kernel
theorem subd11_3_921 : subd11_3 [3, 2, 2] = true := by decide +kernel
theorem subd11_3_922 : subd11_3 [3, 2, 3] = true := by decide +kernel
theorem subd11_3_923 : subd11_3 [3, 2, 4] = true := by decide +kernel
theorem subd11_3_924 : subd11_3 [3, 2, 5] = true := by decide +kernel
theorem subd11_3_925 : subd11_3 [3, 2, 6] = true := by decide +kernel
theorem subd11_3_926 : subd11_3 [3, 3] = true := by decide +kernel
theorem subd11_3_927 : subd11_3 [3, 4] = true := by decide +kernel
theorem sbd11_3_28 : ∀ q ∈ blkd11_3_28, subd11_3 q = true := by
  unfold blkd11_3_28
  exact List.forall_mem_cons.2 ⟨subd11_3_896, List.forall_mem_cons.2 ⟨subd11_3_897, List.forall_mem_cons.2 ⟨subd11_3_898, List.forall_mem_cons.2 ⟨subd11_3_899, List.forall_mem_cons.2 ⟨subd11_3_900, List.forall_mem_cons.2 ⟨subd11_3_901, List.forall_mem_cons.2 ⟨subd11_3_902, List.forall_mem_cons.2 ⟨subd11_3_903, List.forall_mem_cons.2 ⟨subd11_3_904, List.forall_mem_cons.2 ⟨subd11_3_905, List.forall_mem_cons.2 ⟨subd11_3_906, List.forall_mem_cons.2 ⟨subd11_3_907, List.forall_mem_cons.2 ⟨subd11_3_908, List.forall_mem_cons.2 ⟨subd11_3_909, List.forall_mem_cons.2 ⟨subd11_3_910, List.forall_mem_cons.2 ⟨subd11_3_911, List.forall_mem_cons.2 ⟨subd11_3_912, List.forall_mem_cons.2 ⟨subd11_3_913, List.forall_mem_cons.2 ⟨subd11_3_914, List.forall_mem_cons.2 ⟨subd11_3_915, List.forall_mem_cons.2 ⟨subd11_3_916, List.forall_mem_cons.2 ⟨subd11_3_917, List.forall_mem_cons.2 ⟨subd11_3_918, List.forall_mem_cons.2 ⟨subd11_3_919, List.forall_mem_cons.2 ⟨subd11_3_920, List.forall_mem_cons.2 ⟨subd11_3_921, List.forall_mem_cons.2 ⟨subd11_3_922, List.forall_mem_cons.2 ⟨subd11_3_923, List.forall_mem_cons.2 ⟨subd11_3_924, List.forall_mem_cons.2 ⟨subd11_3_925, List.forall_mem_cons.2 ⟨subd11_3_926, List.forall_mem_cons.2 ⟨subd11_3_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_928 : subd11_3 [4, -5] = true := by decide +kernel
theorem subd11_3_929 : subd11_3 [4, -4] = true := by decide +kernel
theorem subd11_3_930 : subd11_3 [4, -3] = true := by decide +kernel
theorem subd11_3_931 : subd11_3 [4, -2] = true := by decide +kernel
theorem subd11_3_932 : subd11_3 [4, -1] = true := by decide +kernel
theorem subd11_3_933 : subd11_3 [4, 0] = true := by decide +kernel
theorem subd11_3_934 : subd11_3 [4, 1] = true := by decide +kernel
theorem subd11_3_935 : subd11_3 [4, 2] = true := by decide +kernel
theorem subd11_3_936 : subd11_3 [4, 3] = true := by decide +kernel
theorem subd11_3_937 : subd11_3 [5, -4] = true := by decide +kernel
theorem subd11_3_938 : subd11_3 [5, -3] = true := by decide +kernel
theorem subd11_3_939 : subd11_3 [5, -2] = true := by decide +kernel
theorem subd11_3_940 : subd11_3 [5, -1] = true := by decide +kernel
theorem subd11_3_941 : subd11_3 [5, 0] = true := by decide +kernel
theorem subd11_3_942 : subd11_3 [5, 1] = true := by decide +kernel
theorem sbd11_3_29 : ∀ q ∈ blkd11_3_29, subd11_3 q = true := by
  unfold blkd11_3_29
  exact List.forall_mem_cons.2 ⟨subd11_3_928, List.forall_mem_cons.2 ⟨subd11_3_929, List.forall_mem_cons.2 ⟨subd11_3_930, List.forall_mem_cons.2 ⟨subd11_3_931, List.forall_mem_cons.2 ⟨subd11_3_932, List.forall_mem_cons.2 ⟨subd11_3_933, List.forall_mem_cons.2 ⟨subd11_3_934, List.forall_mem_cons.2 ⟨subd11_3_935, List.forall_mem_cons.2 ⟨subd11_3_936, List.forall_mem_cons.2 ⟨subd11_3_937, List.forall_mem_cons.2 ⟨subd11_3_938, List.forall_mem_cons.2 ⟨subd11_3_939, List.forall_mem_cons.2 ⟨subd11_3_940, List.forall_mem_cons.2 ⟨subd11_3_941, List.forall_mem_cons.2 ⟨subd11_3_942, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [-4] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [-3, -3] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [-3, -2] = true := by decide +kernel
theorem subd12_0_3 : subd12_0 [-3, -1] = true := by decide +kernel
theorem subd12_0_4 : subd12_0 [-3, 0] = true := by decide +kernel
theorem subd12_0_5 : subd12_0 [-3, 1] = true := by decide +kernel
theorem subd12_0_6 : subd12_0 [-3, 2] = true := by decide +kernel
theorem subd12_0_7 : subd12_0 [-3, 3] = true := by decide +kernel
theorem subd12_0_8 : subd12_0 [-3, 4] = true := by decide +kernel
theorem subd12_0_9 : subd12_0 [-2, -4] = true := by decide +kernel
theorem subd12_0_10 : subd12_0 [-2, -3] = true := by decide +kernel
theorem subd12_0_11 : subd12_0 [-2, -2] = true := by decide +kernel
theorem subd12_0_12 : subd12_0 [-2, -1] = true := by decide +kernel
theorem subd12_0_13 : subd12_0 [-2, 0] = true := by decide +kernel
theorem subd12_0_14 : subd12_0 [-2, 1] = true := by decide +kernel
theorem subd12_0_15 : subd12_0 [-2, 2] = true := by decide +kernel
theorem subd12_0_16 : subd12_0 [-2, 3] = true := by decide +kernel
theorem subd12_0_17 : subd12_0 [-2, 4] = true := by decide +kernel
theorem subd12_0_18 : subd12_0 [-1, -5] = true := by decide +kernel
theorem subd12_0_19 : subd12_0 [-1, -4] = true := by decide +kernel
theorem subd12_0_20 : subd12_0 [-1, -3] = true := by decide +kernel
theorem subd12_0_21 : subd12_0 [-1, -2] = true := by decide +kernel
theorem subd12_0_22 : subd12_0 [-1, -1] = true := by decide +kernel
theorem subd12_0_23 : subd12_0 [-1, 0] = true := by decide +kernel
theorem subd12_0_24 : subd12_0 [-1, 1] = true := by decide +kernel
theorem subd12_0_25 : subd12_0 [-1, 2] = true := by decide +kernel
theorem subd12_0_26 : subd12_0 [-1, 3] = true := by decide +kernel
theorem subd12_0_27 : subd12_0 [-1, 4] = true := by decide +kernel
theorem subd12_0_28 : subd12_0 [0, -5] = true := by decide +kernel
theorem subd12_0_29 : subd12_0 [0, -4] = true := by decide +kernel
theorem subd12_0_30 : subd12_0 [0, -3] = true := by decide +kernel
theorem subd12_0_31 : subd12_0 [0, -2] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_cons.2 ⟨subd12_0_3, List.forall_mem_cons.2 ⟨subd12_0_4, List.forall_mem_cons.2 ⟨subd12_0_5, List.forall_mem_cons.2 ⟨subd12_0_6, List.forall_mem_cons.2 ⟨subd12_0_7, List.forall_mem_cons.2 ⟨subd12_0_8, List.forall_mem_cons.2 ⟨subd12_0_9, List.forall_mem_cons.2 ⟨subd12_0_10, List.forall_mem_cons.2 ⟨subd12_0_11, List.forall_mem_cons.2 ⟨subd12_0_12, List.forall_mem_cons.2 ⟨subd12_0_13, List.forall_mem_cons.2 ⟨subd12_0_14, List.forall_mem_cons.2 ⟨subd12_0_15, List.forall_mem_cons.2 ⟨subd12_0_16, List.forall_mem_cons.2 ⟨subd12_0_17, List.forall_mem_cons.2 ⟨subd12_0_18, List.forall_mem_cons.2 ⟨subd12_0_19, List.forall_mem_cons.2 ⟨subd12_0_20, List.forall_mem_cons.2 ⟨subd12_0_21, List.forall_mem_cons.2 ⟨subd12_0_22, List.forall_mem_cons.2 ⟨subd12_0_23, List.forall_mem_cons.2 ⟨subd12_0_24, List.forall_mem_cons.2 ⟨subd12_0_25, List.forall_mem_cons.2 ⟨subd12_0_26, List.forall_mem_cons.2 ⟨subd12_0_27, List.forall_mem_cons.2 ⟨subd12_0_28, List.forall_mem_cons.2 ⟨subd12_0_29, List.forall_mem_cons.2 ⟨subd12_0_30, List.forall_mem_cons.2 ⟨subd12_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
