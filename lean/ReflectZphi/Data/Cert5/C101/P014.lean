import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_0_704 : subd11_0 [2, 1, 7] = true := by decide +kernel
theorem subd11_0_705 : subd11_0 [2, 2, -6] = true := by decide +kernel
theorem subd11_0_706 : subd11_0 [2, 2, -5] = true := by decide +kernel
theorem subd11_0_707 : subd11_0 [2, 2, -4] = true := by decide +kernel
theorem subd11_0_708 : subd11_0 [2, 2, -3] = true := by decide +kernel
theorem subd11_0_709 : subd11_0 [2, 2, -2] = true := by decide +kernel
theorem subd11_0_710 : subd11_0 [2, 2, -1] = true := by decide +kernel
theorem subd11_0_711 : subd11_0 [2, 2, 0] = true := by decide +kernel
theorem subd11_0_712 : subd11_0 [2, 2, 1] = true := by decide +kernel
theorem subd11_0_713 : subd11_0 [2, 2, 2] = true := by decide +kernel
theorem subd11_0_714 : subd11_0 [2, 2, 3] = true := by decide +kernel
theorem subd11_0_715 : subd11_0 [2, 2, 4] = true := by decide +kernel
theorem subd11_0_716 : subd11_0 [2, 2, 5] = true := by decide +kernel
theorem subd11_0_717 : subd11_0 [2, 2, 6] = true := by decide +kernel
theorem subd11_0_718 : subd11_0 [2, 2, 7] = true := by decide +kernel
theorem subd11_0_719 : subd11_0 [2, 3] = true := by decide +kernel
theorem subd11_0_720 : subd11_0 [2, 4] = true := by decide +kernel
theorem subd11_0_721 : subd11_0 [2, 5] = true := by decide +kernel
theorem subd11_0_722 : subd11_0 [3, -7] = true := by decide +kernel
theorem subd11_0_723 : subd11_0 [3, -6] = true := by decide +kernel
theorem subd11_0_724 : subd11_0 [3, -5] = true := by decide +kernel
theorem subd11_0_725 : subd11_0 [3, -4] = true := by decide +kernel
theorem subd11_0_726 : subd11_0 [3, -3, -8] = true := by decide +kernel
theorem subd11_0_727 : subd11_0 [3, -3, -7] = true := by decide +kernel
theorem subd11_0_728 : subd11_0 [3, -3, -6] = true := by decide +kernel
theorem subd11_0_729 : subd11_0 [3, -3, -5] = true := by decide +kernel
theorem subd11_0_730 : subd11_0 [3, -3, -4] = true := by decide +kernel
theorem subd11_0_731 : subd11_0 [3, -3, -3] = true := by decide +kernel
theorem subd11_0_732 : subd11_0 [3, -3, -2] = true := by decide +kernel
theorem subd11_0_733 : subd11_0 [3, -3, -1] = true := by decide +kernel
theorem subd11_0_734 : subd11_0 [3, -3, 0] = true := by decide +kernel
theorem subd11_0_735 : subd11_0 [3, -3, 1] = true := by decide +kernel
theorem sbd11_0_22 : ∀ q ∈ blkd11_0_22, subd11_0 q = true := by
  unfold blkd11_0_22
  exact List.forall_mem_cons.2 ⟨subd11_0_704, List.forall_mem_cons.2 ⟨subd11_0_705, List.forall_mem_cons.2 ⟨subd11_0_706, List.forall_mem_cons.2 ⟨subd11_0_707, List.forall_mem_cons.2 ⟨subd11_0_708, List.forall_mem_cons.2 ⟨subd11_0_709, List.forall_mem_cons.2 ⟨subd11_0_710, List.forall_mem_cons.2 ⟨subd11_0_711, List.forall_mem_cons.2 ⟨subd11_0_712, List.forall_mem_cons.2 ⟨subd11_0_713, List.forall_mem_cons.2 ⟨subd11_0_714, List.forall_mem_cons.2 ⟨subd11_0_715, List.forall_mem_cons.2 ⟨subd11_0_716, List.forall_mem_cons.2 ⟨subd11_0_717, List.forall_mem_cons.2 ⟨subd11_0_718, List.forall_mem_cons.2 ⟨subd11_0_719, List.forall_mem_cons.2 ⟨subd11_0_720, List.forall_mem_cons.2 ⟨subd11_0_721, List.forall_mem_cons.2 ⟨subd11_0_722, List.forall_mem_cons.2 ⟨subd11_0_723, List.forall_mem_cons.2 ⟨subd11_0_724, List.forall_mem_cons.2 ⟨subd11_0_725, List.forall_mem_cons.2 ⟨subd11_0_726, List.forall_mem_cons.2 ⟨subd11_0_727, List.forall_mem_cons.2 ⟨subd11_0_728, List.forall_mem_cons.2 ⟨subd11_0_729, List.forall_mem_cons.2 ⟨subd11_0_730, List.forall_mem_cons.2 ⟨subd11_0_731, List.forall_mem_cons.2 ⟨subd11_0_732, List.forall_mem_cons.2 ⟨subd11_0_733, List.forall_mem_cons.2 ⟨subd11_0_734, List.forall_mem_cons.2 ⟨subd11_0_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_736 : subd11_0 [3, -3, 2] = true := by decide +kernel
theorem subd11_0_737 : subd11_0 [3, -3, 3] = true := by decide +kernel
theorem subd11_0_738 : subd11_0 [3, -3, 4] = true := by decide +kernel
theorem subd11_0_739 : subd11_0 [3, -3, 5] = true := by decide +kernel
theorem subd11_0_740 : subd11_0 [3, -2, -8] = true := by decide +kernel
theorem subd11_0_741 : subd11_0 [3, -2, -7] = true := by decide +kernel
theorem subd11_0_742 : subd11_0 [3, -2, -6] = true := by decide +kernel
theorem subd11_0_743 : subd11_0 [3, -2, -5] = true := by decide +kernel
theorem subd11_0_744 : subd11_0 [3, -2, -4] = true := by decide +kernel
theorem subd11_0_745 : subd11_0 [3, -2, -3] = true := by decide +kernel
theorem subd11_0_746 : subd11_0 [3, -2, -2] = true := by decide +kernel
theorem subd11_0_747 : subd11_0 [3, -2, -1] = true := by decide +kernel
theorem subd11_0_748 : subd11_0 [3, -2, 0] = true := by decide +kernel
theorem subd11_0_749 : subd11_0 [3, -2, 1] = true := by decide +kernel
theorem subd11_0_750 : subd11_0 [3, -2, 2] = true := by decide +kernel
theorem subd11_0_751 : subd11_0 [3, -2, 3] = true := by decide +kernel
theorem subd11_0_752 : subd11_0 [3, -2, 4] = true := by decide +kernel
theorem subd11_0_753 : subd11_0 [3, -2, 5] = true := by decide +kernel
theorem subd11_0_754 : subd11_0 [3, -2, 6] = true := by decide +kernel
theorem subd11_0_755 : subd11_0 [3, -1, -7] = true := by decide +kernel
theorem subd11_0_756 : subd11_0 [3, -1, -6] = true := by decide +kernel
theorem subd11_0_757 : subd11_0 [3, -1, -5] = true := by decide +kernel
theorem subd11_0_758 : subd11_0 [3, -1, -4] = true := by decide +kernel
theorem subd11_0_759 : subd11_0 [3, -1, -3] = true := by decide +kernel
theorem subd11_0_760 : subd11_0 [3, -1, -2] = true := by decide +kernel
theorem subd11_0_761 : subd11_0 [3, -1, -1] = true := by decide +kernel
theorem subd11_0_762 : subd11_0 [3, -1, 0] = true := by decide +kernel
theorem subd11_0_763 : subd11_0 [3, -1, 1] = true := by decide +kernel
theorem subd11_0_764 : subd11_0 [3, -1, 2] = true := by decide +kernel
theorem subd11_0_765 : subd11_0 [3, -1, 3] = true := by decide +kernel
theorem subd11_0_766 : subd11_0 [3, -1, 4] = true := by decide +kernel
theorem subd11_0_767 : subd11_0 [3, -1, 5] = true := by decide +kernel
theorem sbd11_0_23 : ∀ q ∈ blkd11_0_23, subd11_0 q = true := by
  unfold blkd11_0_23
  exact List.forall_mem_cons.2 ⟨subd11_0_736, List.forall_mem_cons.2 ⟨subd11_0_737, List.forall_mem_cons.2 ⟨subd11_0_738, List.forall_mem_cons.2 ⟨subd11_0_739, List.forall_mem_cons.2 ⟨subd11_0_740, List.forall_mem_cons.2 ⟨subd11_0_741, List.forall_mem_cons.2 ⟨subd11_0_742, List.forall_mem_cons.2 ⟨subd11_0_743, List.forall_mem_cons.2 ⟨subd11_0_744, List.forall_mem_cons.2 ⟨subd11_0_745, List.forall_mem_cons.2 ⟨subd11_0_746, List.forall_mem_cons.2 ⟨subd11_0_747, List.forall_mem_cons.2 ⟨subd11_0_748, List.forall_mem_cons.2 ⟨subd11_0_749, List.forall_mem_cons.2 ⟨subd11_0_750, List.forall_mem_cons.2 ⟨subd11_0_751, List.forall_mem_cons.2 ⟨subd11_0_752, List.forall_mem_cons.2 ⟨subd11_0_753, List.forall_mem_cons.2 ⟨subd11_0_754, List.forall_mem_cons.2 ⟨subd11_0_755, List.forall_mem_cons.2 ⟨subd11_0_756, List.forall_mem_cons.2 ⟨subd11_0_757, List.forall_mem_cons.2 ⟨subd11_0_758, List.forall_mem_cons.2 ⟨subd11_0_759, List.forall_mem_cons.2 ⟨subd11_0_760, List.forall_mem_cons.2 ⟨subd11_0_761, List.forall_mem_cons.2 ⟨subd11_0_762, List.forall_mem_cons.2 ⟨subd11_0_763, List.forall_mem_cons.2 ⟨subd11_0_764, List.forall_mem_cons.2 ⟨subd11_0_765, List.forall_mem_cons.2 ⟨subd11_0_766, List.forall_mem_cons.2 ⟨subd11_0_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_768 : subd11_0 [3, -1, 6] = true := by decide +kernel
theorem subd11_0_769 : subd11_0 [3, 0, -7] = true := by decide +kernel
theorem subd11_0_770 : subd11_0 [3, 0, -6] = true := by decide +kernel
theorem subd11_0_771 : subd11_0 [3, 0, -5] = true := by decide +kernel
theorem subd11_0_772 : subd11_0 [3, 0, -4] = true := by decide +kernel
theorem subd11_0_773 : subd11_0 [3, 0, -3] = true := by decide +kernel
theorem subd11_0_774 : subd11_0 [3, 0, -2] = true := by decide +kernel
theorem subd11_0_775 : subd11_0 [3, 0, -1] = true := by decide +kernel
theorem subd11_0_776 : subd11_0 [3, 0, 0] = true := by decide +kernel
theorem subd11_0_777 : subd11_0 [3, 0, 1] = true := by decide +kernel
theorem subd11_0_778 : subd11_0 [3, 0, 2] = true := by decide +kernel
theorem subd11_0_779 : subd11_0 [3, 0, 3] = true := by decide +kernel
theorem subd11_0_780 : subd11_0 [3, 0, 4] = true := by decide +kernel
theorem subd11_0_781 : subd11_0 [3, 0, 5] = true := by decide +kernel
theorem subd11_0_782 : subd11_0 [3, 0, 6] = true := by decide +kernel
theorem subd11_0_783 : subd11_0 [3, 1, -6] = true := by decide +kernel
theorem subd11_0_784 : subd11_0 [3, 1, -5] = true := by decide +kernel
theorem subd11_0_785 : subd11_0 [3, 1, -4] = true := by decide +kernel
theorem subd11_0_786 : subd11_0 [3, 1, -3] = true := by decide +kernel
theorem subd11_0_787 : subd11_0 [3, 1, -2] = true := by decide +kernel
theorem subd11_0_788 : subd11_0 [3, 1, -1] = true := by decide +kernel
theorem subd11_0_789 : subd11_0 [3, 1, 0] = true := by decide +kernel
theorem subd11_0_790 : subd11_0 [3, 1, 1] = true := by decide +kernel
theorem subd11_0_791 : subd11_0 [3, 1, 2] = true := by decide +kernel
theorem subd11_0_792 : subd11_0 [3, 1, 3] = true := by decide +kernel
theorem subd11_0_793 : subd11_0 [3, 1, 4] = true := by decide +kernel
theorem subd11_0_794 : subd11_0 [3, 1, 5] = true := by decide +kernel
theorem subd11_0_795 : subd11_0 [3, 1, 6] = true := by decide +kernel
theorem subd11_0_796 : subd11_0 [3, 1, 7] = true := by decide +kernel
theorem subd11_0_797 : subd11_0 [3, 2] = true := by decide +kernel
theorem subd11_0_798 : subd11_0 [3, 3] = true := by decide +kernel
theorem subd11_0_799 : subd11_0 [3, 4] = true := by decide +kernel
theorem sbd11_0_24 : ∀ q ∈ blkd11_0_24, subd11_0 q = true := by
  unfold blkd11_0_24
  exact List.forall_mem_cons.2 ⟨subd11_0_768, List.forall_mem_cons.2 ⟨subd11_0_769, List.forall_mem_cons.2 ⟨subd11_0_770, List.forall_mem_cons.2 ⟨subd11_0_771, List.forall_mem_cons.2 ⟨subd11_0_772, List.forall_mem_cons.2 ⟨subd11_0_773, List.forall_mem_cons.2 ⟨subd11_0_774, List.forall_mem_cons.2 ⟨subd11_0_775, List.forall_mem_cons.2 ⟨subd11_0_776, List.forall_mem_cons.2 ⟨subd11_0_777, List.forall_mem_cons.2 ⟨subd11_0_778, List.forall_mem_cons.2 ⟨subd11_0_779, List.forall_mem_cons.2 ⟨subd11_0_780, List.forall_mem_cons.2 ⟨subd11_0_781, List.forall_mem_cons.2 ⟨subd11_0_782, List.forall_mem_cons.2 ⟨subd11_0_783, List.forall_mem_cons.2 ⟨subd11_0_784, List.forall_mem_cons.2 ⟨subd11_0_785, List.forall_mem_cons.2 ⟨subd11_0_786, List.forall_mem_cons.2 ⟨subd11_0_787, List.forall_mem_cons.2 ⟨subd11_0_788, List.forall_mem_cons.2 ⟨subd11_0_789, List.forall_mem_cons.2 ⟨subd11_0_790, List.forall_mem_cons.2 ⟨subd11_0_791, List.forall_mem_cons.2 ⟨subd11_0_792, List.forall_mem_cons.2 ⟨subd11_0_793, List.forall_mem_cons.2 ⟨subd11_0_794, List.forall_mem_cons.2 ⟨subd11_0_795, List.forall_mem_cons.2 ⟨subd11_0_796, List.forall_mem_cons.2 ⟨subd11_0_797, List.forall_mem_cons.2 ⟨subd11_0_798, List.forall_mem_cons.2 ⟨subd11_0_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_800 : subd11_0 [4, -7] = true := by decide +kernel
theorem subd11_0_801 : subd11_0 [4, -6] = true := by decide +kernel
theorem subd11_0_802 : subd11_0 [4, -5] = true := by decide +kernel
theorem subd11_0_803 : subd11_0 [4, -4] = true := by decide +kernel
theorem subd11_0_804 : subd11_0 [4, -3] = true := by decide +kernel
theorem subd11_0_805 : subd11_0 [4, -2] = true := by decide +kernel
theorem subd11_0_806 : subd11_0 [4, -1] = true := by decide +kernel
theorem subd11_0_807 : subd11_0 [4, 0] = true := by decide +kernel
theorem subd11_0_808 : subd11_0 [4, 1] = true := by decide +kernel
theorem subd11_0_809 : subd11_0 [4, 2] = true := by decide +kernel
theorem subd11_0_810 : subd11_0 [4, 3] = true := by decide +kernel
theorem subd11_0_811 : subd11_0 [5, -6] = true := by decide +kernel
theorem subd11_0_812 : subd11_0 [5, -5] = true := by decide +kernel
theorem subd11_0_813 : subd11_0 [5, -4] = true := by decide +kernel
theorem subd11_0_814 : subd11_0 [5, -3] = true := by decide +kernel
theorem subd11_0_815 : subd11_0 [5, -2] = true := by decide +kernel
theorem subd11_0_816 : subd11_0 [5, -1] = true := by decide +kernel
theorem subd11_0_817 : subd11_0 [5, 0] = true := by decide +kernel
theorem subd11_0_818 : subd11_0 [5, 1] = true := by decide +kernel
theorem sbd11_0_25 : ∀ q ∈ blkd11_0_25, subd11_0 q = true := by
  unfold blkd11_0_25
  exact List.forall_mem_cons.2 ⟨subd11_0_800, List.forall_mem_cons.2 ⟨subd11_0_801, List.forall_mem_cons.2 ⟨subd11_0_802, List.forall_mem_cons.2 ⟨subd11_0_803, List.forall_mem_cons.2 ⟨subd11_0_804, List.forall_mem_cons.2 ⟨subd11_0_805, List.forall_mem_cons.2 ⟨subd11_0_806, List.forall_mem_cons.2 ⟨subd11_0_807, List.forall_mem_cons.2 ⟨subd11_0_808, List.forall_mem_cons.2 ⟨subd11_0_809, List.forall_mem_cons.2 ⟨subd11_0_810, List.forall_mem_cons.2 ⟨subd11_0_811, List.forall_mem_cons.2 ⟨subd11_0_812, List.forall_mem_cons.2 ⟨subd11_0_813, List.forall_mem_cons.2 ⟨subd11_0_814, List.forall_mem_cons.2 ⟨subd11_0_815, List.forall_mem_cons.2 ⟨subd11_0_816, List.forall_mem_cons.2 ⟨subd11_0_817, List.forall_mem_cons.2 ⟨subd11_0_818, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-2] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-1, -2, -13] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-1, -2, -12] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-1, -2, -11] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-1, -2, -10] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-1, -2, -9] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-1, -2, -8] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-1, -2, -7] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [-1, -2, -6] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [-1, -2, -5] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [-1, -2, -4] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [-1, -2, -3] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [-1, -2, -2] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [-1, -2, -1] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [-1, -2, 0] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [-1, -2, 1] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [-1, -2, 2] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [-1, -2, 3] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [-1, -2, 4] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [-1, -2, 5] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [-1, -2, 6] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [-1, -2, 7] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [-1, -2, 8] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [-1, -2, 9] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [-1, -2, 10] = true := by decide +kernel
theorem subd11_1_26 : subd11_1 [-1, -2, 11] = true := by decide +kernel
theorem subd11_1_27 : subd11_1 [-1, -2, 12] = true := by decide +kernel
theorem subd11_1_28 : subd11_1 [-1, -1, -20] = true := by decide +kernel
theorem subd11_1_29 : subd11_1 [-1, -1, -19] = true := by decide +kernel
theorem subd11_1_30 : subd11_1 [-1, -1, -18] = true := by decide +kernel
theorem subd11_1_31 : subd11_1 [-1, -1, -17] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_cons.2 ⟨subd11_1_26, List.forall_mem_cons.2 ⟨subd11_1_27, List.forall_mem_cons.2 ⟨subd11_1_28, List.forall_mem_cons.2 ⟨subd11_1_29, List.forall_mem_cons.2 ⟨subd11_1_30, List.forall_mem_cons.2 ⟨subd11_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_32 : subd11_1 [-1, -1, -16] = true := by decide +kernel
theorem subd11_1_33 : subd11_1 [-1, -1, -15] = true := by decide +kernel
theorem subd11_1_34 : subd11_1 [-1, -1, -14] = true := by decide +kernel
theorem subd11_1_35 : subd11_1 [-1, -1, -13] = true := by decide +kernel
theorem subd11_1_36 : subd11_1 [-1, -1, -12] = true := by decide +kernel
theorem subd11_1_37 : subd11_1 [-1, -1, -11] = true := by decide +kernel
theorem subd11_1_38 : subd11_1 [-1, -1, -10] = true := by decide +kernel
theorem subd11_1_39 : subd11_1 [-1, -1, -9] = true := by decide +kernel
theorem subd11_1_40 : subd11_1 [-1, -1, -8] = true := by decide +kernel
theorem subd11_1_41 : subd11_1 [-1, -1, -7] = true := by decide +kernel
theorem subd11_1_42 : subd11_1 [-1, -1, -6] = true := by decide +kernel
theorem subd11_1_43 : subd11_1 [-1, -1, -5] = true := by decide +kernel
theorem subd11_1_44 : subd11_1 [-1, -1, -4] = true := by decide +kernel
theorem subd11_1_45 : subd11_1 [-1, -1, -3] = true := by decide +kernel
theorem subd11_1_46 : subd11_1 [-1, -1, -2] = true := by decide +kernel
theorem subd11_1_47 : subd11_1 [-1, -1, -1] = true := by decide +kernel
theorem subd11_1_48 : subd11_1 [-1, -1, 0] = true := by decide +kernel
theorem subd11_1_49 : subd11_1 [-1, -1, 1] = true := by decide +kernel
theorem subd11_1_50 : subd11_1 [-1, -1, 2] = true := by decide +kernel
theorem subd11_1_51 : subd11_1 [-1, -1, 3] = true := by decide +kernel
theorem subd11_1_52 : subd11_1 [-1, -1, 4] = true := by decide +kernel
theorem subd11_1_53 : subd11_1 [-1, -1, 5] = true := by decide +kernel
theorem subd11_1_54 : subd11_1 [-1, -1, 6] = true := by decide +kernel
theorem subd11_1_55 : subd11_1 [-1, -1, 7] = true := by decide +kernel
theorem subd11_1_56 : subd11_1 [-1, -1, 8] = true := by decide +kernel
theorem subd11_1_57 : subd11_1 [-1, -1, 9] = true := by decide +kernel
theorem subd11_1_58 : subd11_1 [-1, -1, 10] = true := by decide +kernel
theorem subd11_1_59 : subd11_1 [-1, -1, 11] = true := by decide +kernel
theorem subd11_1_60 : subd11_1 [-1, -1, 12] = true := by decide +kernel
theorem subd11_1_61 : subd11_1 [-1, -1, 13] = true := by decide +kernel
theorem subd11_1_62 : subd11_1 [-1, -1, 14] = true := by decide +kernel
theorem subd11_1_63 : subd11_1 [-1, -1, 15] = true := by decide +kernel
theorem sbd11_1_1 : ∀ q ∈ blkd11_1_1, subd11_1 q = true := by
  unfold blkd11_1_1
  exact List.forall_mem_cons.2 ⟨subd11_1_32, List.forall_mem_cons.2 ⟨subd11_1_33, List.forall_mem_cons.2 ⟨subd11_1_34, List.forall_mem_cons.2 ⟨subd11_1_35, List.forall_mem_cons.2 ⟨subd11_1_36, List.forall_mem_cons.2 ⟨subd11_1_37, List.forall_mem_cons.2 ⟨subd11_1_38, List.forall_mem_cons.2 ⟨subd11_1_39, List.forall_mem_cons.2 ⟨subd11_1_40, List.forall_mem_cons.2 ⟨subd11_1_41, List.forall_mem_cons.2 ⟨subd11_1_42, List.forall_mem_cons.2 ⟨subd11_1_43, List.forall_mem_cons.2 ⟨subd11_1_44, List.forall_mem_cons.2 ⟨subd11_1_45, List.forall_mem_cons.2 ⟨subd11_1_46, List.forall_mem_cons.2 ⟨subd11_1_47, List.forall_mem_cons.2 ⟨subd11_1_48, List.forall_mem_cons.2 ⟨subd11_1_49, List.forall_mem_cons.2 ⟨subd11_1_50, List.forall_mem_cons.2 ⟨subd11_1_51, List.forall_mem_cons.2 ⟨subd11_1_52, List.forall_mem_cons.2 ⟨subd11_1_53, List.forall_mem_cons.2 ⟨subd11_1_54, List.forall_mem_cons.2 ⟨subd11_1_55, List.forall_mem_cons.2 ⟨subd11_1_56, List.forall_mem_cons.2 ⟨subd11_1_57, List.forall_mem_cons.2 ⟨subd11_1_58, List.forall_mem_cons.2 ⟨subd11_1_59, List.forall_mem_cons.2 ⟨subd11_1_60, List.forall_mem_cons.2 ⟨subd11_1_61, List.forall_mem_cons.2 ⟨subd11_1_62, List.forall_mem_cons.2 ⟨subd11_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_64 : subd11_1 [-1, -1, 16] = true := by decide +kernel
theorem subd11_1_65 : subd11_1 [-1, -1, 17] = true := by decide +kernel
theorem subd11_1_66 : subd11_1 [-1, -1, 18] = true := by decide +kernel
theorem subd11_1_67 : subd11_1 [-1, -1, 19] = true := by decide +kernel
theorem subd11_1_68 : subd11_1 [-1, 0, -21] = true := by decide +kernel
theorem subd11_1_69 : subd11_1 [-1, 0, -20] = true := by decide +kernel
theorem subd11_1_70 : subd11_1 [-1, 0, -19] = true := by decide +kernel
theorem subd11_1_71 : subd11_1 [-1, 0, -18] = true := by decide +kernel
theorem subd11_1_72 : subd11_1 [-1, 0, -17] = true := by decide +kernel
theorem subd11_1_73 : subd11_1 [-1, 0, -16] = true := by decide +kernel
theorem subd11_1_74 : subd11_1 [-1, 0, -15] = true := by decide +kernel
theorem subd11_1_75 : subd11_1 [-1, 0, -14] = true := by decide +kernel
theorem subd11_1_76 : subd11_1 [-1, 0, -13] = true := by decide +kernel
theorem subd11_1_77 : subd11_1 [-1, 0, -12] = true := by decide +kernel
theorem subd11_1_78 : subd11_1 [-1, 0, -11] = true := by decide +kernel
theorem subd11_1_79 : subd11_1 [-1, 0, -10] = true := by decide +kernel
theorem subd11_1_80 : subd11_1 [-1, 0, -9] = true := by decide +kernel
theorem subd11_1_81 : subd11_1 [-1, 0, -8] = true := by decide +kernel
theorem subd11_1_82 : subd11_1 [-1, 0, -7] = true := by decide +kernel
theorem subd11_1_83 : subd11_1 [-1, 0, -6] = true := by decide +kernel
theorem subd11_1_84 : subd11_1 [-1, 0, -5] = true := by decide +kernel
theorem subd11_1_85 : subd11_1 [-1, 0, -4] = true := by decide +kernel
theorem subd11_1_86 : subd11_1 [-1, 0, -3] = true := by decide +kernel
theorem subd11_1_87 : subd11_1 [-1, 0, -2] = true := by decide +kernel
theorem subd11_1_88 : subd11_1 [-1, 0, -1] = true := by decide +kernel
theorem subd11_1_89 : subd11_1 [-1, 0, 0] = true := by decide +kernel
theorem subd11_1_90 : subd11_1 [-1, 0, 1] = true := by decide +kernel
theorem subd11_1_91 : subd11_1 [-1, 0, 2] = true := by decide +kernel
theorem subd11_1_92 : subd11_1 [-1, 0, 3] = true := by decide +kernel
theorem subd11_1_93 : subd11_1 [-1, 0, 4] = true := by decide +kernel
theorem subd11_1_94 : subd11_1 [-1, 0, 5] = true := by decide +kernel
theorem subd11_1_95 : subd11_1 [-1, 0, 6] = true := by decide +kernel
theorem sbd11_1_2 : ∀ q ∈ blkd11_1_2, subd11_1 q = true := by
  unfold blkd11_1_2
  exact List.forall_mem_cons.2 ⟨subd11_1_64, List.forall_mem_cons.2 ⟨subd11_1_65, List.forall_mem_cons.2 ⟨subd11_1_66, List.forall_mem_cons.2 ⟨subd11_1_67, List.forall_mem_cons.2 ⟨subd11_1_68, List.forall_mem_cons.2 ⟨subd11_1_69, List.forall_mem_cons.2 ⟨subd11_1_70, List.forall_mem_cons.2 ⟨subd11_1_71, List.forall_mem_cons.2 ⟨subd11_1_72, List.forall_mem_cons.2 ⟨subd11_1_73, List.forall_mem_cons.2 ⟨subd11_1_74, List.forall_mem_cons.2 ⟨subd11_1_75, List.forall_mem_cons.2 ⟨subd11_1_76, List.forall_mem_cons.2 ⟨subd11_1_77, List.forall_mem_cons.2 ⟨subd11_1_78, List.forall_mem_cons.2 ⟨subd11_1_79, List.forall_mem_cons.2 ⟨subd11_1_80, List.forall_mem_cons.2 ⟨subd11_1_81, List.forall_mem_cons.2 ⟨subd11_1_82, List.forall_mem_cons.2 ⟨subd11_1_83, List.forall_mem_cons.2 ⟨subd11_1_84, List.forall_mem_cons.2 ⟨subd11_1_85, List.forall_mem_cons.2 ⟨subd11_1_86, List.forall_mem_cons.2 ⟨subd11_1_87, List.forall_mem_cons.2 ⟨subd11_1_88, List.forall_mem_cons.2 ⟨subd11_1_89, List.forall_mem_cons.2 ⟨subd11_1_90, List.forall_mem_cons.2 ⟨subd11_1_91, List.forall_mem_cons.2 ⟨subd11_1_92, List.forall_mem_cons.2 ⟨subd11_1_93, List.forall_mem_cons.2 ⟨subd11_1_94, List.forall_mem_cons.2 ⟨subd11_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
