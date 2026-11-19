import ReflectZphi.Data.Cert5.C104.Base

namespace ReflectZphi.Data.Cert5.C104
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_640 : sub5 [2, 1, -5] = true := by decide +kernel
theorem sub5_641 : sub5 [2, 1, -4] = true := by decide +kernel
theorem sub5_642 : sub5 [2, 1, -3] = true := by decide +kernel
theorem sub5_643 : sub5 [2, 1, -2] = true := by decide +kernel
theorem sub5_644 : sub5 [2, 1, -1] = true := by decide +kernel
theorem sub5_645 : sub5 [2, 1, 0] = true := by decide +kernel
theorem sub5_646 : sub5 [2, 1, 1] = true := by decide +kernel
theorem sub5_647 : sub5 [2, 1, 2] = true := by decide +kernel
theorem sub5_648 : sub5 [2, 1, 3] = true := by decide +kernel
theorem sub5_649 : sub5 [2, 1, 4] = true := by decide +kernel
theorem sub5_650 : sub5 [2, 1, 5] = true := by decide +kernel
theorem sub5_651 : sub5 [2, 1, 6] = true := by decide +kernel
theorem sub5_652 : sub5 [2, 1, 7] = true := by decide +kernel
theorem sub5_653 : sub5 [2, 1, 8] = true := by decide +kernel
theorem sub5_654 : sub5 [2, 2, -7] = true := by decide +kernel
theorem sub5_655 : sub5 [2, 2, -6] = true := by decide +kernel
theorem sub5_656 : sub5 [2, 2, -5] = true := by decide +kernel
theorem sub5_657 : sub5 [2, 2, -4] = true := by decide +kernel
theorem sub5_658 : sub5 [2, 2, -3] = true := by decide +kernel
theorem sub5_659 : sub5 [2, 2, -2] = true := by decide +kernel
theorem sub5_660 : sub5 [2, 2, -1] = true := by decide +kernel
theorem sub5_661 : sub5 [2, 2, 0] = true := by decide +kernel
theorem sub5_662 : sub5 [2, 2, 1] = true := by decide +kernel
theorem sub5_663 : sub5 [2, 2, 2] = true := by decide +kernel
theorem sub5_664 : sub5 [2, 2, 3] = true := by decide +kernel
theorem sub5_665 : sub5 [2, 2, 4] = true := by decide +kernel
theorem sub5_666 : sub5 [2, 2, 5] = true := by decide +kernel
theorem sub5_667 : sub5 [2, 2, 6] = true := by decide +kernel
theorem sub5_668 : sub5 [2, 2, 7] = true := by decide +kernel
theorem sub5_669 : sub5 [2, 2, 8] = true := by decide +kernel
theorem sub5_670 : sub5 [2, 3, -7] = true := by decide +kernel
theorem sub5_671 : sub5 [2, 3, -6] = true := by decide +kernel
theorem sb5_20 : ∀ q ∈ blk5_20, sub5 q = true := by
  unfold blk5_20
  exact List.forall_mem_cons.2 ⟨sub5_640, List.forall_mem_cons.2 ⟨sub5_641, List.forall_mem_cons.2 ⟨sub5_642, List.forall_mem_cons.2 ⟨sub5_643, List.forall_mem_cons.2 ⟨sub5_644, List.forall_mem_cons.2 ⟨sub5_645, List.forall_mem_cons.2 ⟨sub5_646, List.forall_mem_cons.2 ⟨sub5_647, List.forall_mem_cons.2 ⟨sub5_648, List.forall_mem_cons.2 ⟨sub5_649, List.forall_mem_cons.2 ⟨sub5_650, List.forall_mem_cons.2 ⟨sub5_651, List.forall_mem_cons.2 ⟨sub5_652, List.forall_mem_cons.2 ⟨sub5_653, List.forall_mem_cons.2 ⟨sub5_654, List.forall_mem_cons.2 ⟨sub5_655, List.forall_mem_cons.2 ⟨sub5_656, List.forall_mem_cons.2 ⟨sub5_657, List.forall_mem_cons.2 ⟨sub5_658, List.forall_mem_cons.2 ⟨sub5_659, List.forall_mem_cons.2 ⟨sub5_660, List.forall_mem_cons.2 ⟨sub5_661, List.forall_mem_cons.2 ⟨sub5_662, List.forall_mem_cons.2 ⟨sub5_663, List.forall_mem_cons.2 ⟨sub5_664, List.forall_mem_cons.2 ⟨sub5_665, List.forall_mem_cons.2 ⟨sub5_666, List.forall_mem_cons.2 ⟨sub5_667, List.forall_mem_cons.2 ⟨sub5_668, List.forall_mem_cons.2 ⟨sub5_669, List.forall_mem_cons.2 ⟨sub5_670, List.forall_mem_cons.2 ⟨sub5_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_672 : sub5 [2, 3, -5] = true := by decide +kernel
theorem sub5_673 : sub5 [2, 3, -4] = true := by decide +kernel
theorem sub5_674 : sub5 [2, 3, -3] = true := by decide +kernel
theorem sub5_675 : sub5 [2, 3, -2] = true := by decide +kernel
theorem sub5_676 : sub5 [2, 3, -1] = true := by decide +kernel
theorem sub5_677 : sub5 [2, 3, 0] = true := by decide +kernel
theorem sub5_678 : sub5 [2, 3, 1] = true := by decide +kernel
theorem sub5_679 : sub5 [2, 3, 2] = true := by decide +kernel
theorem sub5_680 : sub5 [2, 3, 3] = true := by decide +kernel
theorem sub5_681 : sub5 [2, 3, 4] = true := by decide +kernel
theorem sub5_682 : sub5 [2, 3, 5] = true := by decide +kernel
theorem sub5_683 : sub5 [2, 3, 6] = true := by decide +kernel
theorem sub5_684 : sub5 [2, 3, 7] = true := by decide +kernel
theorem sub5_685 : sub5 [2, 3, 8] = true := by decide +kernel
theorem sub5_686 : sub5 [2, 4] = true := by decide +kernel
theorem sub5_687 : sub5 [2, 5] = true := by decide +kernel
theorem sub5_688 : sub5 [3, -4] = true := by decide +kernel
theorem sub5_689 : sub5 [3, -3] = true := by decide +kernel
theorem sub5_690 : sub5 [3, -2] = true := by decide +kernel
theorem sub5_691 : sub5 [3, -1] = true := by decide +kernel
theorem sub5_692 : sub5 [3, 0, -7] = true := by decide +kernel
theorem sub5_693 : sub5 [3, 0, -6] = true := by decide +kernel
theorem sub5_694 : sub5 [3, 0, -5] = true := by decide +kernel
theorem sub5_695 : sub5 [3, 0, -4] = true := by decide +kernel
theorem sub5_696 : sub5 [3, 0, -3] = true := by decide +kernel
theorem sub5_697 : sub5 [3, 0, -2] = true := by decide +kernel
theorem sub5_698 : sub5 [3, 0, -1] = true := by decide +kernel
theorem sub5_699 : sub5 [3, 0, 0] = true := by decide +kernel
theorem sub5_700 : sub5 [3, 0, 1] = true := by decide +kernel
theorem sub5_701 : sub5 [3, 0, 2] = true := by decide +kernel
theorem sub5_702 : sub5 [3, 0, 3] = true := by decide +kernel
theorem sub5_703 : sub5 [3, 0, 4] = true := by decide +kernel
theorem sb5_21 : ∀ q ∈ blk5_21, sub5 q = true := by
  unfold blk5_21
  exact List.forall_mem_cons.2 ⟨sub5_672, List.forall_mem_cons.2 ⟨sub5_673, List.forall_mem_cons.2 ⟨sub5_674, List.forall_mem_cons.2 ⟨sub5_675, List.forall_mem_cons.2 ⟨sub5_676, List.forall_mem_cons.2 ⟨sub5_677, List.forall_mem_cons.2 ⟨sub5_678, List.forall_mem_cons.2 ⟨sub5_679, List.forall_mem_cons.2 ⟨sub5_680, List.forall_mem_cons.2 ⟨sub5_681, List.forall_mem_cons.2 ⟨sub5_682, List.forall_mem_cons.2 ⟨sub5_683, List.forall_mem_cons.2 ⟨sub5_684, List.forall_mem_cons.2 ⟨sub5_685, List.forall_mem_cons.2 ⟨sub5_686, List.forall_mem_cons.2 ⟨sub5_687, List.forall_mem_cons.2 ⟨sub5_688, List.forall_mem_cons.2 ⟨sub5_689, List.forall_mem_cons.2 ⟨sub5_690, List.forall_mem_cons.2 ⟨sub5_691, List.forall_mem_cons.2 ⟨sub5_692, List.forall_mem_cons.2 ⟨sub5_693, List.forall_mem_cons.2 ⟨sub5_694, List.forall_mem_cons.2 ⟨sub5_695, List.forall_mem_cons.2 ⟨sub5_696, List.forall_mem_cons.2 ⟨sub5_697, List.forall_mem_cons.2 ⟨sub5_698, List.forall_mem_cons.2 ⟨sub5_699, List.forall_mem_cons.2 ⟨sub5_700, List.forall_mem_cons.2 ⟨sub5_701, List.forall_mem_cons.2 ⟨sub5_702, List.forall_mem_cons.2 ⟨sub5_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_704 : sub5 [3, 0, 5] = true := by decide +kernel
theorem sub5_705 : sub5 [3, 0, 6] = true := by decide +kernel
theorem sub5_706 : sub5 [3, 0, 7] = true := by decide +kernel
theorem sub5_707 : sub5 [3, 1, -7] = true := by decide +kernel
theorem sub5_708 : sub5 [3, 1, -6] = true := by decide +kernel
theorem sub5_709 : sub5 [3, 1, -5] = true := by decide +kernel
theorem sub5_710 : sub5 [3, 1, -4] = true := by decide +kernel
theorem sub5_711 : sub5 [3, 1, -3] = true := by decide +kernel
theorem sub5_712 : sub5 [3, 1, -2] = true := by decide +kernel
theorem sub5_713 : sub5 [3, 1, -1] = true := by decide +kernel
theorem sub5_714 : sub5 [3, 1, 0] = true := by decide +kernel
theorem sub5_715 : sub5 [3, 1, 1] = true := by decide +kernel
theorem sub5_716 : sub5 [3, 1, 2] = true := by decide +kernel
theorem sub5_717 : sub5 [3, 1, 3] = true := by decide +kernel
theorem sub5_718 : sub5 [3, 1, 4] = true := by decide +kernel
theorem sub5_719 : sub5 [3, 1, 5] = true := by decide +kernel
theorem sub5_720 : sub5 [3, 1, 6] = true := by decide +kernel
theorem sub5_721 : sub5 [3, 1, 7] = true := by decide +kernel
theorem sub5_722 : sub5 [3, 1, 8] = true := by decide +kernel
theorem sub5_723 : sub5 [3, 2, -6] = true := by decide +kernel
theorem sub5_724 : sub5 [3, 2, -5] = true := by decide +kernel
theorem sub5_725 : sub5 [3, 2, -4] = true := by decide +kernel
theorem sub5_726 : sub5 [3, 2, -3] = true := by decide +kernel
theorem sub5_727 : sub5 [3, 2, -2] = true := by decide +kernel
theorem sub5_728 : sub5 [3, 2, -1] = true := by decide +kernel
theorem sub5_729 : sub5 [3, 2, 0] = true := by decide +kernel
theorem sub5_730 : sub5 [3, 2, 1] = true := by decide +kernel
theorem sub5_731 : sub5 [3, 2, 2] = true := by decide +kernel
theorem sub5_732 : sub5 [3, 2, 3] = true := by decide +kernel
theorem sub5_733 : sub5 [3, 2, 4] = true := by decide +kernel
theorem sub5_734 : sub5 [3, 2, 5] = true := by decide +kernel
theorem sub5_735 : sub5 [3, 2, 6] = true := by decide +kernel
theorem sb5_22 : ∀ q ∈ blk5_22, sub5 q = true := by
  unfold blk5_22
  exact List.forall_mem_cons.2 ⟨sub5_704, List.forall_mem_cons.2 ⟨sub5_705, List.forall_mem_cons.2 ⟨sub5_706, List.forall_mem_cons.2 ⟨sub5_707, List.forall_mem_cons.2 ⟨sub5_708, List.forall_mem_cons.2 ⟨sub5_709, List.forall_mem_cons.2 ⟨sub5_710, List.forall_mem_cons.2 ⟨sub5_711, List.forall_mem_cons.2 ⟨sub5_712, List.forall_mem_cons.2 ⟨sub5_713, List.forall_mem_cons.2 ⟨sub5_714, List.forall_mem_cons.2 ⟨sub5_715, List.forall_mem_cons.2 ⟨sub5_716, List.forall_mem_cons.2 ⟨sub5_717, List.forall_mem_cons.2 ⟨sub5_718, List.forall_mem_cons.2 ⟨sub5_719, List.forall_mem_cons.2 ⟨sub5_720, List.forall_mem_cons.2 ⟨sub5_721, List.forall_mem_cons.2 ⟨sub5_722, List.forall_mem_cons.2 ⟨sub5_723, List.forall_mem_cons.2 ⟨sub5_724, List.forall_mem_cons.2 ⟨sub5_725, List.forall_mem_cons.2 ⟨sub5_726, List.forall_mem_cons.2 ⟨sub5_727, List.forall_mem_cons.2 ⟨sub5_728, List.forall_mem_cons.2 ⟨sub5_729, List.forall_mem_cons.2 ⟨sub5_730, List.forall_mem_cons.2 ⟨sub5_731, List.forall_mem_cons.2 ⟨sub5_732, List.forall_mem_cons.2 ⟨sub5_733, List.forall_mem_cons.2 ⟨sub5_734, List.forall_mem_cons.2 ⟨sub5_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_736 : sub5 [3, 2, 7] = true := by decide +kernel
theorem sub5_737 : sub5 [3, 2, 8] = true := by decide +kernel
theorem sub5_738 : sub5 [3, 3, -6] = true := by decide +kernel
theorem sub5_739 : sub5 [3, 3, -5] = true := by decide +kernel
theorem sub5_740 : sub5 [3, 3, -4] = true := by decide +kernel
theorem sub5_741 : sub5 [3, 3, -3] = true := by decide +kernel
theorem sub5_742 : sub5 [3, 3, -2] = true := by decide +kernel
theorem sub5_743 : sub5 [3, 3, -1] = true := by decide +kernel
theorem sub5_744 : sub5 [3, 3, 0] = true := by decide +kernel
theorem sub5_745 : sub5 [3, 3, 1] = true := by decide +kernel
theorem sub5_746 : sub5 [3, 3, 2] = true := by decide +kernel
theorem sub5_747 : sub5 [3, 3, 3] = true := by decide +kernel
theorem sub5_748 : sub5 [3, 3, 4] = true := by decide +kernel
theorem sub5_749 : sub5 [3, 3, 5] = true := by decide +kernel
theorem sub5_750 : sub5 [3, 3, 6] = true := by decide +kernel
theorem sub5_751 : sub5 [3, 3, 7] = true := by decide +kernel
theorem sub5_752 : sub5 [3, 3, 8] = true := by decide +kernel
theorem sub5_753 : sub5 [3, 4] = true := by decide +kernel
theorem sub5_754 : sub5 [3, 5] = true := by decide +kernel
theorem sub5_755 : sub5 [4, -3] = true := by decide +kernel
theorem sub5_756 : sub5 [4, -2] = true := by decide +kernel
theorem sub5_757 : sub5 [4, -1] = true := by decide +kernel
theorem sub5_758 : sub5 [4, 0] = true := by decide +kernel
theorem sub5_759 : sub5 [4, 1] = true := by decide +kernel
theorem sub5_760 : sub5 [4, 2] = true := by decide +kernel
theorem sub5_761 : sub5 [4, 3] = true := by decide +kernel
theorem sub5_762 : sub5 [4, 4] = true := by decide +kernel
theorem sub5_763 : sub5 [4, 5] = true := by decide +kernel
theorem sub5_764 : sub5 [5] = true := by decide +kernel
theorem sb5_23 : ∀ q ∈ blk5_23, sub5 q = true := by
  unfold blk5_23
  exact List.forall_mem_cons.2 ⟨sub5_736, List.forall_mem_cons.2 ⟨sub5_737, List.forall_mem_cons.2 ⟨sub5_738, List.forall_mem_cons.2 ⟨sub5_739, List.forall_mem_cons.2 ⟨sub5_740, List.forall_mem_cons.2 ⟨sub5_741, List.forall_mem_cons.2 ⟨sub5_742, List.forall_mem_cons.2 ⟨sub5_743, List.forall_mem_cons.2 ⟨sub5_744, List.forall_mem_cons.2 ⟨sub5_745, List.forall_mem_cons.2 ⟨sub5_746, List.forall_mem_cons.2 ⟨sub5_747, List.forall_mem_cons.2 ⟨sub5_748, List.forall_mem_cons.2 ⟨sub5_749, List.forall_mem_cons.2 ⟨sub5_750, List.forall_mem_cons.2 ⟨sub5_751, List.forall_mem_cons.2 ⟨sub5_752, List.forall_mem_cons.2 ⟨sub5_753, List.forall_mem_cons.2 ⟨sub5_754, List.forall_mem_cons.2 ⟨sub5_755, List.forall_mem_cons.2 ⟨sub5_756, List.forall_mem_cons.2 ⟨sub5_757, List.forall_mem_cons.2 ⟨sub5_758, List.forall_mem_cons.2 ⟨sub5_759, List.forall_mem_cons.2 ⟨sub5_760, List.forall_mem_cons.2 ⟨sub5_761, List.forall_mem_cons.2 ⟨sub5_762, List.forall_mem_cons.2 ⟨sub5_763, List.forall_mem_cons.2 ⟨sub5_764, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-4, -2] = true := by decide +kernel
theorem sub6_1 : sub6 [-4, -1] = true := by decide +kernel
theorem sub6_2 : sub6 [-4, 0] = true := by decide +kernel
theorem sub6_3 : sub6 [-4, 1] = true := by decide +kernel
theorem sub6_4 : sub6 [-3, -4] = true := by decide +kernel
theorem sub6_5 : sub6 [-3, -3] = true := by decide +kernel
theorem sub6_6 : sub6 [-3, -2, -8] = true := by decide +kernel
theorem sub6_7 : sub6 [-3, -2, -7] = true := by decide +kernel
theorem sub6_8 : sub6 [-3, -2, -6] = true := by decide +kernel
theorem sub6_9 : sub6 [-3, -2, -5] = true := by decide +kernel
theorem sub6_10 : sub6 [-3, -2, -4] = true := by decide +kernel
theorem sub6_11 : sub6 [-3, -2, -3] = true := by decide +kernel
theorem sub6_12 : sub6 [-3, -2, -2] = true := by decide +kernel
theorem sub6_13 : sub6 [-3, -2, -1] = true := by decide +kernel
theorem sub6_14 : sub6 [-3, -2, 0] = true := by decide +kernel
theorem sub6_15 : sub6 [-3, -2, 1] = true := by decide +kernel
theorem sub6_16 : sub6 [-3, -2, 2] = true := by decide +kernel
theorem sub6_17 : sub6 [-3, -2, 3] = true := by decide +kernel
theorem sub6_18 : sub6 [-3, -2, 4] = true := by decide +kernel
theorem sub6_19 : sub6 [-3, -2, 5] = true := by decide +kernel
theorem sub6_20 : sub6 [-3, -2, 6] = true := by decide +kernel
theorem sub6_21 : sub6 [-3, -2, 7] = true := by decide +kernel
theorem sub6_22 : sub6 [-3, -1, -10] = true := by decide +kernel
theorem sub6_23 : sub6 [-3, -1, -9] = true := by decide +kernel
theorem sub6_24 : sub6 [-3, -1, -8] = true := by decide +kernel
theorem sub6_25 : sub6 [-3, -1, -7] = true := by decide +kernel
theorem sub6_26 : sub6 [-3, -1, -6] = true := by decide +kernel
theorem sub6_27 : sub6 [-3, -1, -5] = true := by decide +kernel
theorem sub6_28 : sub6 [-3, -1, -4] = true := by decide +kernel
theorem sub6_29 : sub6 [-3, -1, -3] = true := by decide +kernel
theorem sub6_30 : sub6 [-3, -1, -2] = true := by decide +kernel
theorem sub6_31 : sub6 [-3, -1, -1] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_32 : sub6 [-3, -1, 0] = true := by decide +kernel
theorem sub6_33 : sub6 [-3, -1, 1] = true := by decide +kernel
theorem sub6_34 : sub6 [-3, -1, 2] = true := by decide +kernel
theorem sub6_35 : sub6 [-3, -1, 3] = true := by decide +kernel
theorem sub6_36 : sub6 [-3, -1, 4] = true := by decide +kernel
theorem sub6_37 : sub6 [-3, -1, 5] = true := by decide +kernel
theorem sub6_38 : sub6 [-3, -1, 6] = true := by decide +kernel
theorem sub6_39 : sub6 [-3, -1, 7] = true := by decide +kernel
theorem sub6_40 : sub6 [-3, -1, 8] = true := by decide +kernel
theorem sub6_41 : sub6 [-3, -1, 9] = true := by decide +kernel
theorem sub6_42 : sub6 [-3, 0, -10] = true := by decide +kernel
theorem sub6_43 : sub6 [-3, 0, -9] = true := by decide +kernel
theorem sub6_44 : sub6 [-3, 0, -8] = true := by decide +kernel
theorem sub6_45 : sub6 [-3, 0, -7] = true := by decide +kernel
theorem sub6_46 : sub6 [-3, 0, -6] = true := by decide +kernel
theorem sub6_47 : sub6 [-3, 0, -5] = true := by decide +kernel
theorem sub6_48 : sub6 [-3, 0, -4] = true := by decide +kernel
theorem sub6_49 : sub6 [-3, 0, -3] = true := by decide +kernel
theorem sub6_50 : sub6 [-3, 0, -2] = true := by decide +kernel
theorem sub6_51 : sub6 [-3, 0, -1] = true := by decide +kernel
theorem sub6_52 : sub6 [-3, 0, 0] = true := by decide +kernel
theorem sub6_53 : sub6 [-3, 0, 1] = true := by decide +kernel
theorem sub6_54 : sub6 [-3, 0, 2] = true := by decide +kernel
theorem sub6_55 : sub6 [-3, 0, 3] = true := by decide +kernel
theorem sub6_56 : sub6 [-3, 0, 4] = true := by decide +kernel
theorem sub6_57 : sub6 [-3, 0, 5] = true := by decide +kernel
theorem sub6_58 : sub6 [-3, 0, 6] = true := by decide +kernel
theorem sub6_59 : sub6 [-3, 0, 7] = true := by decide +kernel
theorem sub6_60 : sub6 [-3, 0, 8] = true := by decide +kernel
theorem sub6_61 : sub6 [-3, 0, 9] = true := by decide +kernel
theorem sub6_62 : sub6 [-3, 0, 10] = true := by decide +kernel
theorem sub6_63 : sub6 [-3, 1, -9] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_cons.2 ⟨sub6_38, List.forall_mem_cons.2 ⟨sub6_39, List.forall_mem_cons.2 ⟨sub6_40, List.forall_mem_cons.2 ⟨sub6_41, List.forall_mem_cons.2 ⟨sub6_42, List.forall_mem_cons.2 ⟨sub6_43, List.forall_mem_cons.2 ⟨sub6_44, List.forall_mem_cons.2 ⟨sub6_45, List.forall_mem_cons.2 ⟨sub6_46, List.forall_mem_cons.2 ⟨sub6_47, List.forall_mem_cons.2 ⟨sub6_48, List.forall_mem_cons.2 ⟨sub6_49, List.forall_mem_cons.2 ⟨sub6_50, List.forall_mem_cons.2 ⟨sub6_51, List.forall_mem_cons.2 ⟨sub6_52, List.forall_mem_cons.2 ⟨sub6_53, List.forall_mem_cons.2 ⟨sub6_54, List.forall_mem_cons.2 ⟨sub6_55, List.forall_mem_cons.2 ⟨sub6_56, List.forall_mem_cons.2 ⟨sub6_57, List.forall_mem_cons.2 ⟨sub6_58, List.forall_mem_cons.2 ⟨sub6_59, List.forall_mem_cons.2 ⟨sub6_60, List.forall_mem_cons.2 ⟨sub6_61, List.forall_mem_cons.2 ⟨sub6_62, List.forall_mem_cons.2 ⟨sub6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_64 : sub6 [-3, 1, -8] = true := by decide +kernel
theorem sub6_65 : sub6 [-3, 1, -7] = true := by decide +kernel
theorem sub6_66 : sub6 [-3, 1, -6] = true := by decide +kernel
theorem sub6_67 : sub6 [-3, 1, -5] = true := by decide +kernel
theorem sub6_68 : sub6 [-3, 1, -4] = true := by decide +kernel
theorem sub6_69 : sub6 [-3, 1, -3] = true := by decide +kernel
theorem sub6_70 : sub6 [-3, 1, -2] = true := by decide +kernel
theorem sub6_71 : sub6 [-3, 1, -1] = true := by decide +kernel
theorem sub6_72 : sub6 [-3, 1, 0] = true := by decide +kernel
theorem sub6_73 : sub6 [-3, 1, 1] = true := by decide +kernel
theorem sub6_74 : sub6 [-3, 1, 2] = true := by decide +kernel
theorem sub6_75 : sub6 [-3, 1, 3] = true := by decide +kernel
theorem sub6_76 : sub6 [-3, 1, 4] = true := by decide +kernel
theorem sub6_77 : sub6 [-3, 1, 5] = true := by decide +kernel
theorem sub6_78 : sub6 [-3, 1, 6] = true := by decide +kernel
theorem sub6_79 : sub6 [-3, 1, 7] = true := by decide +kernel
theorem sub6_80 : sub6 [-3, 1, 8] = true := by decide +kernel
theorem sub6_81 : sub6 [-3, 1, 9] = true := by decide +kernel
theorem sub6_82 : sub6 [-3, 1, 10] = true := by decide +kernel
theorem sub6_83 : sub6 [-3, 2, -7] = true := by decide +kernel
theorem sub6_84 : sub6 [-3, 2, -6] = true := by decide +kernel
theorem sub6_85 : sub6 [-3, 2, -5] = true := by decide +kernel
theorem sub6_86 : sub6 [-3, 2, -4] = true := by decide +kernel
theorem sub6_87 : sub6 [-3, 2, -3] = true := by decide +kernel
theorem sub6_88 : sub6 [-3, 2, -2] = true := by decide +kernel
theorem sub6_89 : sub6 [-3, 2, -1] = true := by decide +kernel
theorem sub6_90 : sub6 [-3, 2, 0] = true := by decide +kernel
theorem sub6_91 : sub6 [-3, 2, 1] = true := by decide +kernel
theorem sub6_92 : sub6 [-3, 2, 2] = true := by decide +kernel
theorem sub6_93 : sub6 [-3, 2, 3] = true := by decide +kernel
theorem sub6_94 : sub6 [-3, 2, 4] = true := by decide +kernel
theorem sub6_95 : sub6 [-3, 2, 5] = true := by decide +kernel
theorem sb6_2 : ∀ q ∈ blk6_2, sub6 q = true := by
  unfold blk6_2
  exact List.forall_mem_cons.2 ⟨sub6_64, List.forall_mem_cons.2 ⟨sub6_65, List.forall_mem_cons.2 ⟨sub6_66, List.forall_mem_cons.2 ⟨sub6_67, List.forall_mem_cons.2 ⟨sub6_68, List.forall_mem_cons.2 ⟨sub6_69, List.forall_mem_cons.2 ⟨sub6_70, List.forall_mem_cons.2 ⟨sub6_71, List.forall_mem_cons.2 ⟨sub6_72, List.forall_mem_cons.2 ⟨sub6_73, List.forall_mem_cons.2 ⟨sub6_74, List.forall_mem_cons.2 ⟨sub6_75, List.forall_mem_cons.2 ⟨sub6_76, List.forall_mem_cons.2 ⟨sub6_77, List.forall_mem_cons.2 ⟨sub6_78, List.forall_mem_cons.2 ⟨sub6_79, List.forall_mem_cons.2 ⟨sub6_80, List.forall_mem_cons.2 ⟨sub6_81, List.forall_mem_cons.2 ⟨sub6_82, List.forall_mem_cons.2 ⟨sub6_83, List.forall_mem_cons.2 ⟨sub6_84, List.forall_mem_cons.2 ⟨sub6_85, List.forall_mem_cons.2 ⟨sub6_86, List.forall_mem_cons.2 ⟨sub6_87, List.forall_mem_cons.2 ⟨sub6_88, List.forall_mem_cons.2 ⟨sub6_89, List.forall_mem_cons.2 ⟨sub6_90, List.forall_mem_cons.2 ⟨sub6_91, List.forall_mem_cons.2 ⟨sub6_92, List.forall_mem_cons.2 ⟨sub6_93, List.forall_mem_cons.2 ⟨sub6_94, List.forall_mem_cons.2 ⟨sub6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_96 : sub6 [-3, 2, 6] = true := by decide +kernel
theorem sub6_97 : sub6 [-3, 2, 7] = true := by decide +kernel
theorem sub6_98 : sub6 [-3, 2, 8] = true := by decide +kernel
theorem sub6_99 : sub6 [-3, 2, 9] = true := by decide +kernel
theorem sub6_100 : sub6 [-3, 3] = true := by decide +kernel
theorem sub6_101 : sub6 [-2, -4] = true := by decide +kernel
theorem sub6_102 : sub6 [-2, -3, -9] = true := by decide +kernel
theorem sub6_103 : sub6 [-2, -3, -8] = true := by decide +kernel
theorem sub6_104 : sub6 [-2, -3, -7] = true := by decide +kernel
theorem sub6_105 : sub6 [-2, -3, -6] = true := by decide +kernel
theorem sub6_106 : sub6 [-2, -3, -5] = true := by decide +kernel
theorem sub6_107 : sub6 [-2, -3, -4] = true := by decide +kernel
theorem sub6_108 : sub6 [-2, -3, -3] = true := by decide +kernel
theorem sub6_109 : sub6 [-2, -3, -2] = true := by decide +kernel
theorem sub6_110 : sub6 [-2, -3, -1] = true := by decide +kernel
theorem sub6_111 : sub6 [-2, -3, 0] = true := by decide +kernel
theorem sub6_112 : sub6 [-2, -3, 1] = true := by decide +kernel
theorem sub6_113 : sub6 [-2, -3, 2] = true := by decide +kernel
theorem sub6_114 : sub6 [-2, -3, 3] = true := by decide +kernel
theorem sub6_115 : sub6 [-2, -3, 4] = true := by decide +kernel
theorem sub6_116 : sub6 [-2, -3, 5] = true := by decide +kernel
theorem sub6_117 : sub6 [-2, -3, 6] = true := by decide +kernel
theorem sub6_118 : sub6 [-2, -2, -11] = true := by decide +kernel
theorem sub6_119 : sub6 [-2, -2, -10] = true := by decide +kernel
theorem sub6_120 : sub6 [-2, -2, -9] = true := by decide +kernel
theorem sub6_121 : sub6 [-2, -2, -8] = true := by decide +kernel
theorem sub6_122 : sub6 [-2, -2, -7] = true := by decide +kernel
theorem sub6_123 : sub6 [-2, -2, -6] = true := by decide +kernel
theorem sub6_124 : sub6 [-2, -2, -5] = true := by decide +kernel
theorem sub6_125 : sub6 [-2, -2, -4] = true := by decide +kernel
theorem sub6_126 : sub6 [-2, -2, -3] = true := by decide +kernel
theorem sub6_127 : sub6 [-2, -2, -2] = true := by decide +kernel
theorem sb6_3 : ∀ q ∈ blk6_3, sub6 q = true := by
  unfold blk6_3
  exact List.forall_mem_cons.2 ⟨sub6_96, List.forall_mem_cons.2 ⟨sub6_97, List.forall_mem_cons.2 ⟨sub6_98, List.forall_mem_cons.2 ⟨sub6_99, List.forall_mem_cons.2 ⟨sub6_100, List.forall_mem_cons.2 ⟨sub6_101, List.forall_mem_cons.2 ⟨sub6_102, List.forall_mem_cons.2 ⟨sub6_103, List.forall_mem_cons.2 ⟨sub6_104, List.forall_mem_cons.2 ⟨sub6_105, List.forall_mem_cons.2 ⟨sub6_106, List.forall_mem_cons.2 ⟨sub6_107, List.forall_mem_cons.2 ⟨sub6_108, List.forall_mem_cons.2 ⟨sub6_109, List.forall_mem_cons.2 ⟨sub6_110, List.forall_mem_cons.2 ⟨sub6_111, List.forall_mem_cons.2 ⟨sub6_112, List.forall_mem_cons.2 ⟨sub6_113, List.forall_mem_cons.2 ⟨sub6_114, List.forall_mem_cons.2 ⟨sub6_115, List.forall_mem_cons.2 ⟨sub6_116, List.forall_mem_cons.2 ⟨sub6_117, List.forall_mem_cons.2 ⟨sub6_118, List.forall_mem_cons.2 ⟨sub6_119, List.forall_mem_cons.2 ⟨sub6_120, List.forall_mem_cons.2 ⟨sub6_121, List.forall_mem_cons.2 ⟨sub6_122, List.forall_mem_cons.2 ⟨sub6_123, List.forall_mem_cons.2 ⟨sub6_124, List.forall_mem_cons.2 ⟨sub6_125, List.forall_mem_cons.2 ⟨sub6_126, List.forall_mem_cons.2 ⟨sub6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_128 : sub6 [-2, -2, -1] = true := by decide +kernel
theorem sub6_129 : sub6 [-2, -2, 0] = true := by decide +kernel
theorem sub6_130 : sub6 [-2, -2, 1] = true := by decide +kernel
theorem sub6_131 : sub6 [-2, -2, 2] = true := by decide +kernel
theorem sub6_132 : sub6 [-2, -2, 3] = true := by decide +kernel
theorem sub6_133 : sub6 [-2, -2, 4] = true := by decide +kernel
theorem sub6_134 : sub6 [-2, -2, 5] = true := by decide +kernel
theorem sub6_135 : sub6 [-2, -2, 6] = true := by decide +kernel
theorem sub6_136 : sub6 [-2, -2, 7] = true := by decide +kernel
theorem sub6_137 : sub6 [-2, -2, 8] = true := by decide +kernel
theorem sub6_138 : sub6 [-2, -2, 9] = true := by decide +kernel
theorem sub6_139 : sub6 [-2, -1, -12] = true := by decide +kernel
theorem sub6_140 : sub6 [-2, -1, -11] = true := by decide +kernel
theorem sub6_141 : sub6 [-2, -1, -10] = true := by decide +kernel
theorem sub6_142 : sub6 [-2, -1, -9] = true := by decide +kernel
theorem sub6_143 : sub6 [-2, -1, -8] = true := by decide +kernel
theorem sub6_144 : sub6 [-2, -1, -7] = true := by decide +kernel
theorem sub6_145 : sub6 [-2, -1, -6] = true := by decide +kernel
theorem sub6_146 : sub6 [-2, -1, -5] = true := by decide +kernel
theorem sub6_147 : sub6 [-2, -1, -4] = true := by decide +kernel
theorem sub6_148 : sub6 [-2, -1, -3] = true := by decide +kernel
theorem sub6_149 : sub6 [-2, -1, -2] = true := by decide +kernel
theorem sub6_150 : sub6 [-2, -1, -1] = true := by decide +kernel
theorem sub6_151 : sub6 [-2, -1, 0] = true := by decide +kernel
theorem sub6_152 : sub6 [-2, -1, 1] = true := by decide +kernel
theorem sub6_153 : sub6 [-2, -1, 2] = true := by decide +kernel
theorem sub6_154 : sub6 [-2, -1, 3] = true := by decide +kernel
theorem sub6_155 : sub6 [-2, -1, 4] = true := by decide +kernel
theorem sub6_156 : sub6 [-2, -1, 5] = true := by decide +kernel
theorem sub6_157 : sub6 [-2, -1, 6] = true := by decide +kernel
theorem sub6_158 : sub6 [-2, -1, 7] = true := by decide +kernel
theorem sub6_159 : sub6 [-2, -1, 8] = true := by decide +kernel
theorem sb6_4 : ∀ q ∈ blk6_4, sub6 q = true := by
  unfold blk6_4
  exact List.forall_mem_cons.2 ⟨sub6_128, List.forall_mem_cons.2 ⟨sub6_129, List.forall_mem_cons.2 ⟨sub6_130, List.forall_mem_cons.2 ⟨sub6_131, List.forall_mem_cons.2 ⟨sub6_132, List.forall_mem_cons.2 ⟨sub6_133, List.forall_mem_cons.2 ⟨sub6_134, List.forall_mem_cons.2 ⟨sub6_135, List.forall_mem_cons.2 ⟨sub6_136, List.forall_mem_cons.2 ⟨sub6_137, List.forall_mem_cons.2 ⟨sub6_138, List.forall_mem_cons.2 ⟨sub6_139, List.forall_mem_cons.2 ⟨sub6_140, List.forall_mem_cons.2 ⟨sub6_141, List.forall_mem_cons.2 ⟨sub6_142, List.forall_mem_cons.2 ⟨sub6_143, List.forall_mem_cons.2 ⟨sub6_144, List.forall_mem_cons.2 ⟨sub6_145, List.forall_mem_cons.2 ⟨sub6_146, List.forall_mem_cons.2 ⟨sub6_147, List.forall_mem_cons.2 ⟨sub6_148, List.forall_mem_cons.2 ⟨sub6_149, List.forall_mem_cons.2 ⟨sub6_150, List.forall_mem_cons.2 ⟨sub6_151, List.forall_mem_cons.2 ⟨sub6_152, List.forall_mem_cons.2 ⟨sub6_153, List.forall_mem_cons.2 ⟨sub6_154, List.forall_mem_cons.2 ⟨sub6_155, List.forall_mem_cons.2 ⟨sub6_156, List.forall_mem_cons.2 ⟨sub6_157, List.forall_mem_cons.2 ⟨sub6_158, List.forall_mem_cons.2 ⟨sub6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_160 : sub6 [-2, -1, 9] = true := by decide +kernel
theorem sub6_161 : sub6 [-2, -1, 10] = true := by decide +kernel
theorem sub6_162 : sub6 [-2, -1, 11] = true := by decide +kernel
theorem sub6_163 : sub6 [-2, 0, -12] = true := by decide +kernel
theorem sub6_164 : sub6 [-2, 0, -11] = true := by decide +kernel
theorem sub6_165 : sub6 [-2, 0, -10] = true := by decide +kernel
theorem sub6_166 : sub6 [-2, 0, -9] = true := by decide +kernel
theorem sub6_167 : sub6 [-2, 0, -8] = true := by decide +kernel
theorem sub6_168 : sub6 [-2, 0, -7] = true := by decide +kernel
theorem sub6_169 : sub6 [-2, 0, -6] = true := by decide +kernel
theorem sub6_170 : sub6 [-2, 0, -5] = true := by decide +kernel
theorem sub6_171 : sub6 [-2, 0, -4] = true := by decide +kernel
theorem sub6_172 : sub6 [-2, 0, -3] = true := by decide +kernel
theorem sub6_173 : sub6 [-2, 0, -2] = true := by decide +kernel
theorem sub6_174 : sub6 [-2, 0, -1] = true := by decide +kernel
theorem sub6_175 : sub6 [-2, 0, 0] = true := by decide +kernel
theorem sub6_176 : sub6 [-2, 0, 1] = true := by decide +kernel
theorem sub6_177 : sub6 [-2, 0, 2] = true := by decide +kernel
theorem sub6_178 : sub6 [-2, 0, 3] = true := by decide +kernel
theorem sub6_179 : sub6 [-2, 0, 4] = true := by decide +kernel
theorem sub6_180 : sub6 [-2, 0, 5] = true := by decide +kernel
theorem sub6_181 : sub6 [-2, 0, 6] = true := by decide +kernel
theorem sub6_182 : sub6 [-2, 0, 7] = true := by decide +kernel
theorem sub6_183 : sub6 [-2, 0, 8] = true := by decide +kernel
theorem sub6_184 : sub6 [-2, 0, 9] = true := by decide +kernel
theorem sub6_185 : sub6 [-2, 0, 10] = true := by decide +kernel
theorem sub6_186 : sub6 [-2, 0, 11] = true := by decide +kernel
theorem sub6_187 : sub6 [-2, 0, 12] = true := by decide +kernel
theorem sub6_188 : sub6 [-2, 1, -12] = true := by decide +kernel
theorem sub6_189 : sub6 [-2, 1, -11] = true := by decide +kernel
theorem sub6_190 : sub6 [-2, 1, -10] = true := by decide +kernel
theorem sub6_191 : sub6 [-2, 1, -9] = true := by decide +kernel
theorem sb6_5 : ∀ q ∈ blk6_5, sub6 q = true := by
  unfold blk6_5
  exact List.forall_mem_cons.2 ⟨sub6_160, List.forall_mem_cons.2 ⟨sub6_161, List.forall_mem_cons.2 ⟨sub6_162, List.forall_mem_cons.2 ⟨sub6_163, List.forall_mem_cons.2 ⟨sub6_164, List.forall_mem_cons.2 ⟨sub6_165, List.forall_mem_cons.2 ⟨sub6_166, List.forall_mem_cons.2 ⟨sub6_167, List.forall_mem_cons.2 ⟨sub6_168, List.forall_mem_cons.2 ⟨sub6_169, List.forall_mem_cons.2 ⟨sub6_170, List.forall_mem_cons.2 ⟨sub6_171, List.forall_mem_cons.2 ⟨sub6_172, List.forall_mem_cons.2 ⟨sub6_173, List.forall_mem_cons.2 ⟨sub6_174, List.forall_mem_cons.2 ⟨sub6_175, List.forall_mem_cons.2 ⟨sub6_176, List.forall_mem_cons.2 ⟨sub6_177, List.forall_mem_cons.2 ⟨sub6_178, List.forall_mem_cons.2 ⟨sub6_179, List.forall_mem_cons.2 ⟨sub6_180, List.forall_mem_cons.2 ⟨sub6_181, List.forall_mem_cons.2 ⟨sub6_182, List.forall_mem_cons.2 ⟨sub6_183, List.forall_mem_cons.2 ⟨sub6_184, List.forall_mem_cons.2 ⟨sub6_185, List.forall_mem_cons.2 ⟨sub6_186, List.forall_mem_cons.2 ⟨sub6_187, List.forall_mem_cons.2 ⟨sub6_188, List.forall_mem_cons.2 ⟨sub6_189, List.forall_mem_cons.2 ⟨sub6_190, List.forall_mem_cons.2 ⟨sub6_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_192 : sub6 [-2, 1, -8] = true := by decide +kernel
theorem sub6_193 : sub6 [-2, 1, -7] = true := by decide +kernel
theorem sub6_194 : sub6 [-2, 1, -6] = true := by decide +kernel
theorem sub6_195 : sub6 [-2, 1, -5] = true := by decide +kernel
theorem sub6_196 : sub6 [-2, 1, -4] = true := by decide +kernel
theorem sub6_197 : sub6 [-2, 1, -3] = true := by decide +kernel
theorem sub6_198 : sub6 [-2, 1, -2] = true := by decide +kernel
theorem sub6_199 : sub6 [-2, 1, -1] = true := by decide +kernel
theorem sub6_200 : sub6 [-2, 1, 0] = true := by decide +kernel
theorem sub6_201 : sub6 [-2, 1, 1] = true := by decide +kernel
theorem sub6_202 : sub6 [-2, 1, 2] = true := by decide +kernel
theorem sub6_203 : sub6 [-2, 1, 3] = true := by decide +kernel
theorem sub6_204 : sub6 [-2, 1, 4] = true := by decide +kernel
theorem sub6_205 : sub6 [-2, 1, 5] = true := by decide +kernel
theorem sub6_206 : sub6 [-2, 1, 6] = true := by decide +kernel
theorem sub6_207 : sub6 [-2, 1, 7] = true := by decide +kernel
theorem sub6_208 : sub6 [-2, 1, 8] = true := by decide +kernel
theorem sub6_209 : sub6 [-2, 1, 9] = true := by decide +kernel
theorem sub6_210 : sub6 [-2, 1, 10] = true := by decide +kernel
theorem sub6_211 : sub6 [-2, 1, 11] = true := by decide +kernel
theorem sub6_212 : sub6 [-2, 1, 12] = true := by decide +kernel
theorem sub6_213 : sub6 [-2, 2, -10] = true := by decide +kernel
theorem sub6_214 : sub6 [-2, 2, -9] = true := by decide +kernel
theorem sub6_215 : sub6 [-2, 2, -8] = true := by decide +kernel
theorem sub6_216 : sub6 [-2, 2, -7] = true := by decide +kernel
theorem sub6_217 : sub6 [-2, 2, -6] = true := by decide +kernel
theorem sub6_218 : sub6 [-2, 2, -5] = true := by decide +kernel
theorem sub6_219 : sub6 [-2, 2, -4] = true := by decide +kernel
theorem sub6_220 : sub6 [-2, 2, -3] = true := by decide +kernel
theorem sub6_221 : sub6 [-2, 2, -2] = true := by decide +kernel
theorem sub6_222 : sub6 [-2, 2, -1] = true := by decide +kernel
theorem sub6_223 : sub6 [-2, 2, 0] = true := by decide +kernel
theorem sb6_6 : ∀ q ∈ blk6_6, sub6 q = true := by
  unfold blk6_6
  exact List.forall_mem_cons.2 ⟨sub6_192, List.forall_mem_cons.2 ⟨sub6_193, List.forall_mem_cons.2 ⟨sub6_194, List.forall_mem_cons.2 ⟨sub6_195, List.forall_mem_cons.2 ⟨sub6_196, List.forall_mem_cons.2 ⟨sub6_197, List.forall_mem_cons.2 ⟨sub6_198, List.forall_mem_cons.2 ⟨sub6_199, List.forall_mem_cons.2 ⟨sub6_200, List.forall_mem_cons.2 ⟨sub6_201, List.forall_mem_cons.2 ⟨sub6_202, List.forall_mem_cons.2 ⟨sub6_203, List.forall_mem_cons.2 ⟨sub6_204, List.forall_mem_cons.2 ⟨sub6_205, List.forall_mem_cons.2 ⟨sub6_206, List.forall_mem_cons.2 ⟨sub6_207, List.forall_mem_cons.2 ⟨sub6_208, List.forall_mem_cons.2 ⟨sub6_209, List.forall_mem_cons.2 ⟨sub6_210, List.forall_mem_cons.2 ⟨sub6_211, List.forall_mem_cons.2 ⟨sub6_212, List.forall_mem_cons.2 ⟨sub6_213, List.forall_mem_cons.2 ⟨sub6_214, List.forall_mem_cons.2 ⟨sub6_215, List.forall_mem_cons.2 ⟨sub6_216, List.forall_mem_cons.2 ⟨sub6_217, List.forall_mem_cons.2 ⟨sub6_218, List.forall_mem_cons.2 ⟨sub6_219, List.forall_mem_cons.2 ⟨sub6_220, List.forall_mem_cons.2 ⟨sub6_221, List.forall_mem_cons.2 ⟨sub6_222, List.forall_mem_cons.2 ⟨sub6_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_224 : sub6 [-2, 2, 1] = true := by decide +kernel
theorem sub6_225 : sub6 [-2, 2, 2] = true := by decide +kernel
theorem sub6_226 : sub6 [-2, 2, 3] = true := by decide +kernel
theorem sub6_227 : sub6 [-2, 2, 4] = true := by decide +kernel
theorem sub6_228 : sub6 [-2, 2, 5] = true := by decide +kernel
theorem sub6_229 : sub6 [-2, 2, 6] = true := by decide +kernel
theorem sub6_230 : sub6 [-2, 2, 7] = true := by decide +kernel
theorem sub6_231 : sub6 [-2, 2, 8] = true := by decide +kernel
theorem sub6_232 : sub6 [-2, 2, 9] = true := by decide +kernel
theorem sub6_233 : sub6 [-2, 2, 10] = true := by decide +kernel
theorem sub6_234 : sub6 [-2, 2, 11] = true := by decide +kernel
theorem sub6_235 : sub6 [-2, 2, 12] = true := by decide +kernel
theorem sub6_236 : sub6 [-2, 3, -7] = true := by decide +kernel
theorem sub6_237 : sub6 [-2, 3, -6] = true := by decide +kernel
theorem sub6_238 : sub6 [-2, 3, -5] = true := by decide +kernel
theorem sub6_239 : sub6 [-2, 3, -4] = true := by decide +kernel
theorem sub6_240 : sub6 [-2, 3, -3] = true := by decide +kernel
theorem sub6_241 : sub6 [-2, 3, -2] = true := by decide +kernel
theorem sub6_242 : sub6 [-2, 3, -1] = true := by decide +kernel
theorem sub6_243 : sub6 [-2, 3, 0] = true := by decide +kernel
theorem sub6_244 : sub6 [-2, 3, 1] = true := by decide +kernel
theorem sub6_245 : sub6 [-2, 3, 2] = true := by decide +kernel
theorem sub6_246 : sub6 [-2, 3, 3] = true := by decide +kernel
theorem sub6_247 : sub6 [-2, 3, 4] = true := by decide +kernel
theorem sub6_248 : sub6 [-2, 3, 5] = true := by decide +kernel
theorem sub6_249 : sub6 [-2, 3, 6] = true := by decide +kernel
theorem sub6_250 : sub6 [-2, 3, 7] = true := by decide +kernel
theorem sub6_251 : sub6 [-2, 3, 8] = true := by decide +kernel
theorem sub6_252 : sub6 [-2, 3, 9] = true := by decide +kernel
theorem sub6_253 : sub6 [-2, 3, 10] = true := by decide +kernel
theorem sub6_254 : sub6 [-2, 4] = true := by decide +kernel
theorem sub6_255 : sub6 [-1, -5] = true := by decide +kernel
theorem sb6_7 : ∀ q ∈ blk6_7, sub6 q = true := by
  unfold blk6_7
  exact List.forall_mem_cons.2 ⟨sub6_224, List.forall_mem_cons.2 ⟨sub6_225, List.forall_mem_cons.2 ⟨sub6_226, List.forall_mem_cons.2 ⟨sub6_227, List.forall_mem_cons.2 ⟨sub6_228, List.forall_mem_cons.2 ⟨sub6_229, List.forall_mem_cons.2 ⟨sub6_230, List.forall_mem_cons.2 ⟨sub6_231, List.forall_mem_cons.2 ⟨sub6_232, List.forall_mem_cons.2 ⟨sub6_233, List.forall_mem_cons.2 ⟨sub6_234, List.forall_mem_cons.2 ⟨sub6_235, List.forall_mem_cons.2 ⟨sub6_236, List.forall_mem_cons.2 ⟨sub6_237, List.forall_mem_cons.2 ⟨sub6_238, List.forall_mem_cons.2 ⟨sub6_239, List.forall_mem_cons.2 ⟨sub6_240, List.forall_mem_cons.2 ⟨sub6_241, List.forall_mem_cons.2 ⟨sub6_242, List.forall_mem_cons.2 ⟨sub6_243, List.forall_mem_cons.2 ⟨sub6_244, List.forall_mem_cons.2 ⟨sub6_245, List.forall_mem_cons.2 ⟨sub6_246, List.forall_mem_cons.2 ⟨sub6_247, List.forall_mem_cons.2 ⟨sub6_248, List.forall_mem_cons.2 ⟨sub6_249, List.forall_mem_cons.2 ⟨sub6_250, List.forall_mem_cons.2 ⟨sub6_251, List.forall_mem_cons.2 ⟨sub6_252, List.forall_mem_cons.2 ⟨sub6_253, List.forall_mem_cons.2 ⟨sub6_254, List.forall_mem_cons.2 ⟨sub6_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C104
