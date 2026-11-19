import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_1_736 : subd19_1 [0, 2, 7] = true := by decide +kernel
theorem subd19_1_737 : subd19_1 [0, 2, 8] = true := by decide +kernel
theorem subd19_1_738 : subd19_1 [0, 3, -7] = true := by decide +kernel
theorem subd19_1_739 : subd19_1 [0, 3, -6] = true := by decide +kernel
theorem subd19_1_740 : subd19_1 [0, 3, -5] = true := by decide +kernel
theorem subd19_1_741 : subd19_1 [0, 3, -4] = true := by decide +kernel
theorem subd19_1_742 : subd19_1 [0, 3, -3] = true := by decide +kernel
theorem subd19_1_743 : subd19_1 [0, 3, -2] = true := by decide +kernel
theorem subd19_1_744 : subd19_1 [0, 3, -1] = true := by decide +kernel
theorem subd19_1_745 : subd19_1 [0, 3, 0] = true := by decide +kernel
theorem subd19_1_746 : subd19_1 [0, 3, 1] = true := by decide +kernel
theorem subd19_1_747 : subd19_1 [0, 3, 2] = true := by decide +kernel
theorem subd19_1_748 : subd19_1 [0, 3, 3] = true := by decide +kernel
theorem subd19_1_749 : subd19_1 [0, 3, 4] = true := by decide +kernel
theorem subd19_1_750 : subd19_1 [0, 3, 5] = true := by decide +kernel
theorem subd19_1_751 : subd19_1 [0, 3, 6] = true := by decide +kernel
theorem subd19_1_752 : subd19_1 [0, 3, 7] = true := by decide +kernel
theorem subd19_1_753 : subd19_1 [0, 3, 8] = true := by decide +kernel
theorem subd19_1_754 : subd19_1 [0, 4, -6] = true := by decide +kernel
theorem subd19_1_755 : subd19_1 [0, 4, -5] = true := by decide +kernel
theorem subd19_1_756 : subd19_1 [0, 4, -4] = true := by decide +kernel
theorem subd19_1_757 : subd19_1 [0, 4, -3] = true := by decide +kernel
theorem subd19_1_758 : subd19_1 [0, 4, -2] = true := by decide +kernel
theorem subd19_1_759 : subd19_1 [0, 4, -1] = true := by decide +kernel
theorem subd19_1_760 : subd19_1 [0, 4, 0] = true := by decide +kernel
theorem subd19_1_761 : subd19_1 [0, 4, 1] = true := by decide +kernel
theorem subd19_1_762 : subd19_1 [0, 4, 2] = true := by decide +kernel
theorem subd19_1_763 : subd19_1 [0, 4, 3] = true := by decide +kernel
theorem subd19_1_764 : subd19_1 [0, 4, 4] = true := by decide +kernel
theorem subd19_1_765 : subd19_1 [0, 4, 5] = true := by decide +kernel
theorem subd19_1_766 : subd19_1 [0, 4, 6] = true := by decide +kernel
theorem subd19_1_767 : subd19_1 [0, 4, 7] = true := by decide +kernel
theorem sbd19_1_23 : ∀ q ∈ blkd19_1_23, subd19_1 q = true := by
  unfold blkd19_1_23
  exact List.forall_mem_cons.2 ⟨subd19_1_736, List.forall_mem_cons.2 ⟨subd19_1_737, List.forall_mem_cons.2 ⟨subd19_1_738, List.forall_mem_cons.2 ⟨subd19_1_739, List.forall_mem_cons.2 ⟨subd19_1_740, List.forall_mem_cons.2 ⟨subd19_1_741, List.forall_mem_cons.2 ⟨subd19_1_742, List.forall_mem_cons.2 ⟨subd19_1_743, List.forall_mem_cons.2 ⟨subd19_1_744, List.forall_mem_cons.2 ⟨subd19_1_745, List.forall_mem_cons.2 ⟨subd19_1_746, List.forall_mem_cons.2 ⟨subd19_1_747, List.forall_mem_cons.2 ⟨subd19_1_748, List.forall_mem_cons.2 ⟨subd19_1_749, List.forall_mem_cons.2 ⟨subd19_1_750, List.forall_mem_cons.2 ⟨subd19_1_751, List.forall_mem_cons.2 ⟨subd19_1_752, List.forall_mem_cons.2 ⟨subd19_1_753, List.forall_mem_cons.2 ⟨subd19_1_754, List.forall_mem_cons.2 ⟨subd19_1_755, List.forall_mem_cons.2 ⟨subd19_1_756, List.forall_mem_cons.2 ⟨subd19_1_757, List.forall_mem_cons.2 ⟨subd19_1_758, List.forall_mem_cons.2 ⟨subd19_1_759, List.forall_mem_cons.2 ⟨subd19_1_760, List.forall_mem_cons.2 ⟨subd19_1_761, List.forall_mem_cons.2 ⟨subd19_1_762, List.forall_mem_cons.2 ⟨subd19_1_763, List.forall_mem_cons.2 ⟨subd19_1_764, List.forall_mem_cons.2 ⟨subd19_1_765, List.forall_mem_cons.2 ⟨subd19_1_766, List.forall_mem_cons.2 ⟨subd19_1_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_768 : subd19_1 [0, 4, 8] = true := by decide +kernel
theorem subd19_1_769 : subd19_1 [0, 5] = true := by decide +kernel
theorem subd19_1_770 : subd19_1 [0, 6] = true := by decide +kernel
theorem subd19_1_771 : subd19_1 [0, 7] = true := by decide +kernel
theorem subd19_1_772 : subd19_1 [0, 8] = true := by decide +kernel
theorem subd19_1_773 : subd19_1 [0, 9] = true := by decide +kernel
theorem subd19_1_774 : subd19_1 [1, -10] = true := by decide +kernel
theorem subd19_1_775 : subd19_1 [1, -9] = true := by decide +kernel
theorem subd19_1_776 : subd19_1 [1, -8] = true := by decide +kernel
theorem subd19_1_777 : subd19_1 [1, -7] = true := by decide +kernel
theorem subd19_1_778 : subd19_1 [1, -6] = true := by decide +kernel
theorem subd19_1_779 : subd19_1 [1, -5, -9] = true := by decide +kernel
theorem subd19_1_780 : subd19_1 [1, -5, -8] = true := by decide +kernel
theorem subd19_1_781 : subd19_1 [1, -5, -7] = true := by decide +kernel
theorem subd19_1_782 : subd19_1 [1, -5, -6] = true := by decide +kernel
theorem subd19_1_783 : subd19_1 [1, -5, -5] = true := by decide +kernel
theorem subd19_1_784 : subd19_1 [1, -5, -4] = true := by decide +kernel
theorem subd19_1_785 : subd19_1 [1, -5, -3] = true := by decide +kernel
theorem subd19_1_786 : subd19_1 [1, -5, -2] = true := by decide +kernel
theorem subd19_1_787 : subd19_1 [1, -5, -1] = true := by decide +kernel
theorem subd19_1_788 : subd19_1 [1, -5, 0] = true := by decide +kernel
theorem subd19_1_789 : subd19_1 [1, -5, 1] = true := by decide +kernel
theorem subd19_1_790 : subd19_1 [1, -5, 2] = true := by decide +kernel
theorem subd19_1_791 : subd19_1 [1, -5, 3] = true := by decide +kernel
theorem subd19_1_792 : subd19_1 [1, -5, 4] = true := by decide +kernel
theorem subd19_1_793 : subd19_1 [1, -4, -9] = true := by decide +kernel
theorem subd19_1_794 : subd19_1 [1, -4, -8] = true := by decide +kernel
theorem subd19_1_795 : subd19_1 [1, -4, -7] = true := by decide +kernel
theorem subd19_1_796 : subd19_1 [1, -4, -6] = true := by decide +kernel
theorem subd19_1_797 : subd19_1 [1, -4, -5] = true := by decide +kernel
theorem subd19_1_798 : subd19_1 [1, -4, -4] = true := by decide +kernel
theorem subd19_1_799 : subd19_1 [1, -4, -3] = true := by decide +kernel
theorem sbd19_1_24 : ∀ q ∈ blkd19_1_24, subd19_1 q = true := by
  unfold blkd19_1_24
  exact List.forall_mem_cons.2 ⟨subd19_1_768, List.forall_mem_cons.2 ⟨subd19_1_769, List.forall_mem_cons.2 ⟨subd19_1_770, List.forall_mem_cons.2 ⟨subd19_1_771, List.forall_mem_cons.2 ⟨subd19_1_772, List.forall_mem_cons.2 ⟨subd19_1_773, List.forall_mem_cons.2 ⟨subd19_1_774, List.forall_mem_cons.2 ⟨subd19_1_775, List.forall_mem_cons.2 ⟨subd19_1_776, List.forall_mem_cons.2 ⟨subd19_1_777, List.forall_mem_cons.2 ⟨subd19_1_778, List.forall_mem_cons.2 ⟨subd19_1_779, List.forall_mem_cons.2 ⟨subd19_1_780, List.forall_mem_cons.2 ⟨subd19_1_781, List.forall_mem_cons.2 ⟨subd19_1_782, List.forall_mem_cons.2 ⟨subd19_1_783, List.forall_mem_cons.2 ⟨subd19_1_784, List.forall_mem_cons.2 ⟨subd19_1_785, List.forall_mem_cons.2 ⟨subd19_1_786, List.forall_mem_cons.2 ⟨subd19_1_787, List.forall_mem_cons.2 ⟨subd19_1_788, List.forall_mem_cons.2 ⟨subd19_1_789, List.forall_mem_cons.2 ⟨subd19_1_790, List.forall_mem_cons.2 ⟨subd19_1_791, List.forall_mem_cons.2 ⟨subd19_1_792, List.forall_mem_cons.2 ⟨subd19_1_793, List.forall_mem_cons.2 ⟨subd19_1_794, List.forall_mem_cons.2 ⟨subd19_1_795, List.forall_mem_cons.2 ⟨subd19_1_796, List.forall_mem_cons.2 ⟨subd19_1_797, List.forall_mem_cons.2 ⟨subd19_1_798, List.forall_mem_cons.2 ⟨subd19_1_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_800 : subd19_1 [1, -4, -2] = true := by decide +kernel
theorem subd19_1_801 : subd19_1 [1, -4, -1] = true := by decide +kernel
theorem subd19_1_802 : subd19_1 [1, -4, 0] = true := by decide +kernel
theorem subd19_1_803 : subd19_1 [1, -4, 1] = true := by decide +kernel
theorem subd19_1_804 : subd19_1 [1, -4, 2] = true := by decide +kernel
theorem subd19_1_805 : subd19_1 [1, -4, 3] = true := by decide +kernel
theorem subd19_1_806 : subd19_1 [1, -4, 4] = true := by decide +kernel
theorem subd19_1_807 : subd19_1 [1, -4, 5] = true := by decide +kernel
theorem subd19_1_808 : subd19_1 [1, -3, -9] = true := by decide +kernel
theorem subd19_1_809 : subd19_1 [1, -3, -8] = true := by decide +kernel
theorem subd19_1_810 : subd19_1 [1, -3, -7] = true := by decide +kernel
theorem subd19_1_811 : subd19_1 [1, -3, -6] = true := by decide +kernel
theorem subd19_1_812 : subd19_1 [1, -3, -5] = true := by decide +kernel
theorem subd19_1_813 : subd19_1 [1, -3, -4] = true := by decide +kernel
theorem subd19_1_814 : subd19_1 [1, -3, -3] = true := by decide +kernel
theorem subd19_1_815 : subd19_1 [1, -3, -2] = true := by decide +kernel
theorem subd19_1_816 : subd19_1 [1, -3, -1] = true := by decide +kernel
theorem subd19_1_817 : subd19_1 [1, -3, 0] = true := by decide +kernel
theorem subd19_1_818 : subd19_1 [1, -3, 1] = true := by decide +kernel
theorem subd19_1_819 : subd19_1 [1, -3, 2] = true := by decide +kernel
theorem subd19_1_820 : subd19_1 [1, -3, 3] = true := by decide +kernel
theorem subd19_1_821 : subd19_1 [1, -3, 4] = true := by decide +kernel
theorem subd19_1_822 : subd19_1 [1, -3, 5] = true := by decide +kernel
theorem subd19_1_823 : subd19_1 [1, -2, -9] = true := by decide +kernel
theorem subd19_1_824 : subd19_1 [1, -2, -8] = true := by decide +kernel
theorem subd19_1_825 : subd19_1 [1, -2, -7] = true := by decide +kernel
theorem subd19_1_826 : subd19_1 [1, -2, -6] = true := by decide +kernel
theorem subd19_1_827 : subd19_1 [1, -2, -5] = true := by decide +kernel
theorem subd19_1_828 : subd19_1 [1, -2, -4] = true := by decide +kernel
theorem subd19_1_829 : subd19_1 [1, -2, -3] = true := by decide +kernel
theorem subd19_1_830 : subd19_1 [1, -2, -2] = true := by decide +kernel
theorem subd19_1_831 : subd19_1 [1, -2, -1] = true := by decide +kernel
theorem sbd19_1_25 : ∀ q ∈ blkd19_1_25, subd19_1 q = true := by
  unfold blkd19_1_25
  exact List.forall_mem_cons.2 ⟨subd19_1_800, List.forall_mem_cons.2 ⟨subd19_1_801, List.forall_mem_cons.2 ⟨subd19_1_802, List.forall_mem_cons.2 ⟨subd19_1_803, List.forall_mem_cons.2 ⟨subd19_1_804, List.forall_mem_cons.2 ⟨subd19_1_805, List.forall_mem_cons.2 ⟨subd19_1_806, List.forall_mem_cons.2 ⟨subd19_1_807, List.forall_mem_cons.2 ⟨subd19_1_808, List.forall_mem_cons.2 ⟨subd19_1_809, List.forall_mem_cons.2 ⟨subd19_1_810, List.forall_mem_cons.2 ⟨subd19_1_811, List.forall_mem_cons.2 ⟨subd19_1_812, List.forall_mem_cons.2 ⟨subd19_1_813, List.forall_mem_cons.2 ⟨subd19_1_814, List.forall_mem_cons.2 ⟨subd19_1_815, List.forall_mem_cons.2 ⟨subd19_1_816, List.forall_mem_cons.2 ⟨subd19_1_817, List.forall_mem_cons.2 ⟨subd19_1_818, List.forall_mem_cons.2 ⟨subd19_1_819, List.forall_mem_cons.2 ⟨subd19_1_820, List.forall_mem_cons.2 ⟨subd19_1_821, List.forall_mem_cons.2 ⟨subd19_1_822, List.forall_mem_cons.2 ⟨subd19_1_823, List.forall_mem_cons.2 ⟨subd19_1_824, List.forall_mem_cons.2 ⟨subd19_1_825, List.forall_mem_cons.2 ⟨subd19_1_826, List.forall_mem_cons.2 ⟨subd19_1_827, List.forall_mem_cons.2 ⟨subd19_1_828, List.forall_mem_cons.2 ⟨subd19_1_829, List.forall_mem_cons.2 ⟨subd19_1_830, List.forall_mem_cons.2 ⟨subd19_1_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_832 : subd19_1 [1, -2, 0] = true := by decide +kernel
theorem subd19_1_833 : subd19_1 [1, -2, 1] = true := by decide +kernel
theorem subd19_1_834 : subd19_1 [1, -2, 2] = true := by decide +kernel
theorem subd19_1_835 : subd19_1 [1, -2, 3] = true := by decide +kernel
theorem subd19_1_836 : subd19_1 [1, -2, 4] = true := by decide +kernel
theorem subd19_1_837 : subd19_1 [1, -2, 5] = true := by decide +kernel
theorem subd19_1_838 : subd19_1 [1, -2, 6] = true := by decide +kernel
theorem subd19_1_839 : subd19_1 [1, -1, -9] = true := by decide +kernel
theorem subd19_1_840 : subd19_1 [1, -1, -8] = true := by decide +kernel
theorem subd19_1_841 : subd19_1 [1, -1, -7] = true := by decide +kernel
theorem subd19_1_842 : subd19_1 [1, -1, -6] = true := by decide +kernel
theorem subd19_1_843 : subd19_1 [1, -1, -5] = true := by decide +kernel
theorem subd19_1_844 : subd19_1 [1, -1, -4] = true := by decide +kernel
theorem subd19_1_845 : subd19_1 [1, -1, -3] = true := by decide +kernel
theorem subd19_1_846 : subd19_1 [1, -1, -2] = true := by decide +kernel
theorem subd19_1_847 : subd19_1 [1, -1, -1] = true := by decide +kernel
theorem subd19_1_848 : subd19_1 [1, -1, 0] = true := by decide +kernel
theorem subd19_1_849 : subd19_1 [1, -1, 1] = true := by decide +kernel
theorem subd19_1_850 : subd19_1 [1, -1, 2] = true := by decide +kernel
theorem subd19_1_851 : subd19_1 [1, -1, 3] = true := by decide +kernel
theorem subd19_1_852 : subd19_1 [1, -1, 4] = true := by decide +kernel
theorem subd19_1_853 : subd19_1 [1, -1, 5] = true := by decide +kernel
theorem subd19_1_854 : subd19_1 [1, -1, 6] = true := by decide +kernel
theorem subd19_1_855 : subd19_1 [1, 0, -9] = true := by decide +kernel
theorem subd19_1_856 : subd19_1 [1, 0, -8] = true := by decide +kernel
theorem subd19_1_857 : subd19_1 [1, 0, -7] = true := by decide +kernel
theorem subd19_1_858 : subd19_1 [1, 0, -6] = true := by decide +kernel
theorem subd19_1_859 : subd19_1 [1, 0, -5] = true := by decide +kernel
theorem subd19_1_860 : subd19_1 [1, 0, -4] = true := by decide +kernel
theorem subd19_1_861 : subd19_1 [1, 0, -3] = true := by decide +kernel
theorem subd19_1_862 : subd19_1 [1, 0, -2] = true := by decide +kernel
theorem subd19_1_863 : subd19_1 [1, 0, -1] = true := by decide +kernel
theorem sbd19_1_26 : ∀ q ∈ blkd19_1_26, subd19_1 q = true := by
  unfold blkd19_1_26
  exact List.forall_mem_cons.2 ⟨subd19_1_832, List.forall_mem_cons.2 ⟨subd19_1_833, List.forall_mem_cons.2 ⟨subd19_1_834, List.forall_mem_cons.2 ⟨subd19_1_835, List.forall_mem_cons.2 ⟨subd19_1_836, List.forall_mem_cons.2 ⟨subd19_1_837, List.forall_mem_cons.2 ⟨subd19_1_838, List.forall_mem_cons.2 ⟨subd19_1_839, List.forall_mem_cons.2 ⟨subd19_1_840, List.forall_mem_cons.2 ⟨subd19_1_841, List.forall_mem_cons.2 ⟨subd19_1_842, List.forall_mem_cons.2 ⟨subd19_1_843, List.forall_mem_cons.2 ⟨subd19_1_844, List.forall_mem_cons.2 ⟨subd19_1_845, List.forall_mem_cons.2 ⟨subd19_1_846, List.forall_mem_cons.2 ⟨subd19_1_847, List.forall_mem_cons.2 ⟨subd19_1_848, List.forall_mem_cons.2 ⟨subd19_1_849, List.forall_mem_cons.2 ⟨subd19_1_850, List.forall_mem_cons.2 ⟨subd19_1_851, List.forall_mem_cons.2 ⟨subd19_1_852, List.forall_mem_cons.2 ⟨subd19_1_853, List.forall_mem_cons.2 ⟨subd19_1_854, List.forall_mem_cons.2 ⟨subd19_1_855, List.forall_mem_cons.2 ⟨subd19_1_856, List.forall_mem_cons.2 ⟨subd19_1_857, List.forall_mem_cons.2 ⟨subd19_1_858, List.forall_mem_cons.2 ⟨subd19_1_859, List.forall_mem_cons.2 ⟨subd19_1_860, List.forall_mem_cons.2 ⟨subd19_1_861, List.forall_mem_cons.2 ⟨subd19_1_862, List.forall_mem_cons.2 ⟨subd19_1_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_864 : subd19_1 [1, 0, 0] = true := by decide +kernel
theorem subd19_1_865 : subd19_1 [1, 0, 1] = true := by decide +kernel
theorem subd19_1_866 : subd19_1 [1, 0, 2] = true := by decide +kernel
theorem subd19_1_867 : subd19_1 [1, 0, 3] = true := by decide +kernel
theorem subd19_1_868 : subd19_1 [1, 0, 4] = true := by decide +kernel
theorem subd19_1_869 : subd19_1 [1, 0, 5] = true := by decide +kernel
theorem subd19_1_870 : subd19_1 [1, 0, 6] = true := by decide +kernel
theorem subd19_1_871 : subd19_1 [1, 0, 7] = true := by decide +kernel
theorem subd19_1_872 : subd19_1 [1, 1, -8] = true := by decide +kernel
theorem subd19_1_873 : subd19_1 [1, 1, -7] = true := by decide +kernel
theorem subd19_1_874 : subd19_1 [1, 1, -6] = true := by decide +kernel
theorem subd19_1_875 : subd19_1 [1, 1, -5] = true := by decide +kernel
theorem subd19_1_876 : subd19_1 [1, 1, -4] = true := by decide +kernel
theorem subd19_1_877 : subd19_1 [1, 1, -3] = true := by decide +kernel
theorem subd19_1_878 : subd19_1 [1, 1, -2] = true := by decide +kernel
theorem subd19_1_879 : subd19_1 [1, 1, -1] = true := by decide +kernel
theorem subd19_1_880 : subd19_1 [1, 1, 0] = true := by decide +kernel
theorem subd19_1_881 : subd19_1 [1, 1, 1] = true := by decide +kernel
theorem subd19_1_882 : subd19_1 [1, 1, 2] = true := by decide +kernel
theorem subd19_1_883 : subd19_1 [1, 1, 3] = true := by decide +kernel
theorem subd19_1_884 : subd19_1 [1, 1, 4] = true := by decide +kernel
theorem subd19_1_885 : subd19_1 [1, 1, 5] = true := by decide +kernel
theorem subd19_1_886 : subd19_1 [1, 1, 6] = true := by decide +kernel
theorem subd19_1_887 : subd19_1 [1, 1, 7] = true := by decide +kernel
theorem subd19_1_888 : subd19_1 [1, 2, -8] = true := by decide +kernel
theorem subd19_1_889 : subd19_1 [1, 2, -7] = true := by decide +kernel
theorem subd19_1_890 : subd19_1 [1, 2, -6] = true := by decide +kernel
theorem subd19_1_891 : subd19_1 [1, 2, -5] = true := by decide +kernel
theorem subd19_1_892 : subd19_1 [1, 2, -4] = true := by decide +kernel
theorem subd19_1_893 : subd19_1 [1, 2, -3] = true := by decide +kernel
theorem subd19_1_894 : subd19_1 [1, 2, -2] = true := by decide +kernel
theorem subd19_1_895 : subd19_1 [1, 2, -1] = true := by decide +kernel
theorem sbd19_1_27 : ∀ q ∈ blkd19_1_27, subd19_1 q = true := by
  unfold blkd19_1_27
  exact List.forall_mem_cons.2 ⟨subd19_1_864, List.forall_mem_cons.2 ⟨subd19_1_865, List.forall_mem_cons.2 ⟨subd19_1_866, List.forall_mem_cons.2 ⟨subd19_1_867, List.forall_mem_cons.2 ⟨subd19_1_868, List.forall_mem_cons.2 ⟨subd19_1_869, List.forall_mem_cons.2 ⟨subd19_1_870, List.forall_mem_cons.2 ⟨subd19_1_871, List.forall_mem_cons.2 ⟨subd19_1_872, List.forall_mem_cons.2 ⟨subd19_1_873, List.forall_mem_cons.2 ⟨subd19_1_874, List.forall_mem_cons.2 ⟨subd19_1_875, List.forall_mem_cons.2 ⟨subd19_1_876, List.forall_mem_cons.2 ⟨subd19_1_877, List.forall_mem_cons.2 ⟨subd19_1_878, List.forall_mem_cons.2 ⟨subd19_1_879, List.forall_mem_cons.2 ⟨subd19_1_880, List.forall_mem_cons.2 ⟨subd19_1_881, List.forall_mem_cons.2 ⟨subd19_1_882, List.forall_mem_cons.2 ⟨subd19_1_883, List.forall_mem_cons.2 ⟨subd19_1_884, List.forall_mem_cons.2 ⟨subd19_1_885, List.forall_mem_cons.2 ⟨subd19_1_886, List.forall_mem_cons.2 ⟨subd19_1_887, List.forall_mem_cons.2 ⟨subd19_1_888, List.forall_mem_cons.2 ⟨subd19_1_889, List.forall_mem_cons.2 ⟨subd19_1_890, List.forall_mem_cons.2 ⟨subd19_1_891, List.forall_mem_cons.2 ⟨subd19_1_892, List.forall_mem_cons.2 ⟨subd19_1_893, List.forall_mem_cons.2 ⟨subd19_1_894, List.forall_mem_cons.2 ⟨subd19_1_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_896 : subd19_1 [1, 2, 0] = true := by decide +kernel
theorem subd19_1_897 : subd19_1 [1, 2, 1] = true := by decide +kernel
theorem subd19_1_898 : subd19_1 [1, 2, 2] = true := by decide +kernel
theorem subd19_1_899 : subd19_1 [1, 2, 3] = true := by decide +kernel
theorem subd19_1_900 : subd19_1 [1, 2, 4] = true := by decide +kernel
theorem subd19_1_901 : subd19_1 [1, 2, 5] = true := by decide +kernel
theorem subd19_1_902 : subd19_1 [1, 2, 6] = true := by decide +kernel
theorem subd19_1_903 : subd19_1 [1, 2, 7] = true := by decide +kernel
theorem subd19_1_904 : subd19_1 [1, 3, -7] = true := by decide +kernel
theorem subd19_1_905 : subd19_1 [1, 3, -6] = true := by decide +kernel
theorem subd19_1_906 : subd19_1 [1, 3, -5] = true := by decide +kernel
theorem subd19_1_907 : subd19_1 [1, 3, -4] = true := by decide +kernel
theorem subd19_1_908 : subd19_1 [1, 3, -3] = true := by decide +kernel
theorem subd19_1_909 : subd19_1 [1, 3, -2] = true := by decide +kernel
theorem subd19_1_910 : subd19_1 [1, 3, -1] = true := by decide +kernel
theorem subd19_1_911 : subd19_1 [1, 3, 0] = true := by decide +kernel
theorem subd19_1_912 : subd19_1 [1, 3, 1] = true := by decide +kernel
theorem subd19_1_913 : subd19_1 [1, 3, 2] = true := by decide +kernel
theorem subd19_1_914 : subd19_1 [1, 3, 3] = true := by decide +kernel
theorem subd19_1_915 : subd19_1 [1, 3, 4] = true := by decide +kernel
theorem subd19_1_916 : subd19_1 [1, 3, 5] = true := by decide +kernel
theorem subd19_1_917 : subd19_1 [1, 3, 6] = true := by decide +kernel
theorem subd19_1_918 : subd19_1 [1, 3, 7] = true := by decide +kernel
theorem subd19_1_919 : subd19_1 [1, 4, -6] = true := by decide +kernel
theorem subd19_1_920 : subd19_1 [1, 4, -5] = true := by decide +kernel
theorem subd19_1_921 : subd19_1 [1, 4, -4] = true := by decide +kernel
theorem subd19_1_922 : subd19_1 [1, 4, -3] = true := by decide +kernel
theorem subd19_1_923 : subd19_1 [1, 4, -2] = true := by decide +kernel
theorem subd19_1_924 : subd19_1 [1, 4, -1] = true := by decide +kernel
theorem subd19_1_925 : subd19_1 [1, 4, 0] = true := by decide +kernel
theorem subd19_1_926 : subd19_1 [1, 4, 1] = true := by decide +kernel
theorem subd19_1_927 : subd19_1 [1, 4, 2] = true := by decide +kernel
theorem sbd19_1_28 : ∀ q ∈ blkd19_1_28, subd19_1 q = true := by
  unfold blkd19_1_28
  exact List.forall_mem_cons.2 ⟨subd19_1_896, List.forall_mem_cons.2 ⟨subd19_1_897, List.forall_mem_cons.2 ⟨subd19_1_898, List.forall_mem_cons.2 ⟨subd19_1_899, List.forall_mem_cons.2 ⟨subd19_1_900, List.forall_mem_cons.2 ⟨subd19_1_901, List.forall_mem_cons.2 ⟨subd19_1_902, List.forall_mem_cons.2 ⟨subd19_1_903, List.forall_mem_cons.2 ⟨subd19_1_904, List.forall_mem_cons.2 ⟨subd19_1_905, List.forall_mem_cons.2 ⟨subd19_1_906, List.forall_mem_cons.2 ⟨subd19_1_907, List.forall_mem_cons.2 ⟨subd19_1_908, List.forall_mem_cons.2 ⟨subd19_1_909, List.forall_mem_cons.2 ⟨subd19_1_910, List.forall_mem_cons.2 ⟨subd19_1_911, List.forall_mem_cons.2 ⟨subd19_1_912, List.forall_mem_cons.2 ⟨subd19_1_913, List.forall_mem_cons.2 ⟨subd19_1_914, List.forall_mem_cons.2 ⟨subd19_1_915, List.forall_mem_cons.2 ⟨subd19_1_916, List.forall_mem_cons.2 ⟨subd19_1_917, List.forall_mem_cons.2 ⟨subd19_1_918, List.forall_mem_cons.2 ⟨subd19_1_919, List.forall_mem_cons.2 ⟨subd19_1_920, List.forall_mem_cons.2 ⟨subd19_1_921, List.forall_mem_cons.2 ⟨subd19_1_922, List.forall_mem_cons.2 ⟨subd19_1_923, List.forall_mem_cons.2 ⟨subd19_1_924, List.forall_mem_cons.2 ⟨subd19_1_925, List.forall_mem_cons.2 ⟨subd19_1_926, List.forall_mem_cons.2 ⟨subd19_1_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_928 : subd19_1 [1, 4, 3] = true := by decide +kernel
theorem subd19_1_929 : subd19_1 [1, 4, 4] = true := by decide +kernel
theorem subd19_1_930 : subd19_1 [1, 4, 5] = true := by decide +kernel
theorem subd19_1_931 : subd19_1 [1, 4, 6] = true := by decide +kernel
theorem subd19_1_932 : subd19_1 [1, 4, 7] = true := by decide +kernel
theorem subd19_1_933 : subd19_1 [1, 5] = true := by decide +kernel
theorem subd19_1_934 : subd19_1 [1, 6] = true := by decide +kernel
theorem subd19_1_935 : subd19_1 [1, 7] = true := by decide +kernel
theorem subd19_1_936 : subd19_1 [1, 8] = true := by decide +kernel
theorem subd19_1_937 : subd19_1 [1, 9] = true := by decide +kernel
theorem subd19_1_938 : subd19_1 [2, -10] = true := by decide +kernel
theorem subd19_1_939 : subd19_1 [2, -9] = true := by decide +kernel
theorem subd19_1_940 : subd19_1 [2, -8] = true := by decide +kernel
theorem subd19_1_941 : subd19_1 [2, -7] = true := by decide +kernel
theorem subd19_1_942 : subd19_1 [2, -6] = true := by decide +kernel
theorem subd19_1_943 : subd19_1 [2, -5] = true := by decide +kernel
theorem subd19_1_944 : subd19_1 [2, -4, -9] = true := by decide +kernel
theorem subd19_1_945 : subd19_1 [2, -4, -8] = true := by decide +kernel
theorem subd19_1_946 : subd19_1 [2, -4, -7] = true := by decide +kernel
theorem subd19_1_947 : subd19_1 [2, -4, -6] = true := by decide +kernel
theorem subd19_1_948 : subd19_1 [2, -4, -5] = true := by decide +kernel
theorem subd19_1_949 : subd19_1 [2, -4, -4] = true := by decide +kernel
theorem subd19_1_950 : subd19_1 [2, -4, -3] = true := by decide +kernel
theorem subd19_1_951 : subd19_1 [2, -4, -2] = true := by decide +kernel
theorem subd19_1_952 : subd19_1 [2, -4, -1] = true := by decide +kernel
theorem subd19_1_953 : subd19_1 [2, -4, 0] = true := by decide +kernel
theorem subd19_1_954 : subd19_1 [2, -4, 1] = true := by decide +kernel
theorem subd19_1_955 : subd19_1 [2, -4, 2] = true := by decide +kernel
theorem subd19_1_956 : subd19_1 [2, -4, 3] = true := by decide +kernel
theorem subd19_1_957 : subd19_1 [2, -4, 4] = true := by decide +kernel
theorem subd19_1_958 : subd19_1 [2, -3, -9] = true := by decide +kernel
theorem subd19_1_959 : subd19_1 [2, -3, -8] = true := by decide +kernel
theorem sbd19_1_29 : ∀ q ∈ blkd19_1_29, subd19_1 q = true := by
  unfold blkd19_1_29
  exact List.forall_mem_cons.2 ⟨subd19_1_928, List.forall_mem_cons.2 ⟨subd19_1_929, List.forall_mem_cons.2 ⟨subd19_1_930, List.forall_mem_cons.2 ⟨subd19_1_931, List.forall_mem_cons.2 ⟨subd19_1_932, List.forall_mem_cons.2 ⟨subd19_1_933, List.forall_mem_cons.2 ⟨subd19_1_934, List.forall_mem_cons.2 ⟨subd19_1_935, List.forall_mem_cons.2 ⟨subd19_1_936, List.forall_mem_cons.2 ⟨subd19_1_937, List.forall_mem_cons.2 ⟨subd19_1_938, List.forall_mem_cons.2 ⟨subd19_1_939, List.forall_mem_cons.2 ⟨subd19_1_940, List.forall_mem_cons.2 ⟨subd19_1_941, List.forall_mem_cons.2 ⟨subd19_1_942, List.forall_mem_cons.2 ⟨subd19_1_943, List.forall_mem_cons.2 ⟨subd19_1_944, List.forall_mem_cons.2 ⟨subd19_1_945, List.forall_mem_cons.2 ⟨subd19_1_946, List.forall_mem_cons.2 ⟨subd19_1_947, List.forall_mem_cons.2 ⟨subd19_1_948, List.forall_mem_cons.2 ⟨subd19_1_949, List.forall_mem_cons.2 ⟨subd19_1_950, List.forall_mem_cons.2 ⟨subd19_1_951, List.forall_mem_cons.2 ⟨subd19_1_952, List.forall_mem_cons.2 ⟨subd19_1_953, List.forall_mem_cons.2 ⟨subd19_1_954, List.forall_mem_cons.2 ⟨subd19_1_955, List.forall_mem_cons.2 ⟨subd19_1_956, List.forall_mem_cons.2 ⟨subd19_1_957, List.forall_mem_cons.2 ⟨subd19_1_958, List.forall_mem_cons.2 ⟨subd19_1_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_960 : subd19_1 [2, -3, -7] = true := by decide +kernel
theorem subd19_1_961 : subd19_1 [2, -3, -6] = true := by decide +kernel
theorem subd19_1_962 : subd19_1 [2, -3, -5] = true := by decide +kernel
theorem subd19_1_963 : subd19_1 [2, -3, -4] = true := by decide +kernel
theorem subd19_1_964 : subd19_1 [2, -3, -3] = true := by decide +kernel
theorem subd19_1_965 : subd19_1 [2, -3, -2] = true := by decide +kernel
theorem subd19_1_966 : subd19_1 [2, -3, -1] = true := by decide +kernel
theorem subd19_1_967 : subd19_1 [2, -3, 0] = true := by decide +kernel
theorem subd19_1_968 : subd19_1 [2, -3, 1] = true := by decide +kernel
theorem subd19_1_969 : subd19_1 [2, -3, 2] = true := by decide +kernel
theorem subd19_1_970 : subd19_1 [2, -3, 3] = true := by decide +kernel
theorem subd19_1_971 : subd19_1 [2, -3, 4] = true := by decide +kernel
theorem subd19_1_972 : subd19_1 [2, -3, 5] = true := by decide +kernel
theorem subd19_1_973 : subd19_1 [2, -2, -9] = true := by decide +kernel
theorem subd19_1_974 : subd19_1 [2, -2, -8] = true := by decide +kernel
theorem subd19_1_975 : subd19_1 [2, -2, -7] = true := by decide +kernel
theorem subd19_1_976 : subd19_1 [2, -2, -6] = true := by decide +kernel
theorem subd19_1_977 : subd19_1 [2, -2, -5] = true := by decide +kernel
theorem subd19_1_978 : subd19_1 [2, -2, -4] = true := by decide +kernel
theorem subd19_1_979 : subd19_1 [2, -2, -3] = true := by decide +kernel
theorem subd19_1_980 : subd19_1 [2, -2, -2] = true := by decide +kernel
theorem subd19_1_981 : subd19_1 [2, -2, -1] = true := by decide +kernel
theorem subd19_1_982 : subd19_1 [2, -2, 0] = true := by decide +kernel
theorem subd19_1_983 : subd19_1 [2, -2, 1] = true := by decide +kernel
theorem subd19_1_984 : subd19_1 [2, -2, 2] = true := by decide +kernel
theorem subd19_1_985 : subd19_1 [2, -2, 3] = true := by decide +kernel
theorem subd19_1_986 : subd19_1 [2, -2, 4] = true := by decide +kernel
theorem subd19_1_987 : subd19_1 [2, -2, 5] = true := by decide +kernel
theorem subd19_1_988 : subd19_1 [2, -1, -9] = true := by decide +kernel
theorem subd19_1_989 : subd19_1 [2, -1, -8] = true := by decide +kernel
theorem subd19_1_990 : subd19_1 [2, -1, -7] = true := by decide +kernel
theorem subd19_1_991 : subd19_1 [2, -1, -6] = true := by decide +kernel
theorem sbd19_1_30 : ∀ q ∈ blkd19_1_30, subd19_1 q = true := by
  unfold blkd19_1_30
  exact List.forall_mem_cons.2 ⟨subd19_1_960, List.forall_mem_cons.2 ⟨subd19_1_961, List.forall_mem_cons.2 ⟨subd19_1_962, List.forall_mem_cons.2 ⟨subd19_1_963, List.forall_mem_cons.2 ⟨subd19_1_964, List.forall_mem_cons.2 ⟨subd19_1_965, List.forall_mem_cons.2 ⟨subd19_1_966, List.forall_mem_cons.2 ⟨subd19_1_967, List.forall_mem_cons.2 ⟨subd19_1_968, List.forall_mem_cons.2 ⟨subd19_1_969, List.forall_mem_cons.2 ⟨subd19_1_970, List.forall_mem_cons.2 ⟨subd19_1_971, List.forall_mem_cons.2 ⟨subd19_1_972, List.forall_mem_cons.2 ⟨subd19_1_973, List.forall_mem_cons.2 ⟨subd19_1_974, List.forall_mem_cons.2 ⟨subd19_1_975, List.forall_mem_cons.2 ⟨subd19_1_976, List.forall_mem_cons.2 ⟨subd19_1_977, List.forall_mem_cons.2 ⟨subd19_1_978, List.forall_mem_cons.2 ⟨subd19_1_979, List.forall_mem_cons.2 ⟨subd19_1_980, List.forall_mem_cons.2 ⟨subd19_1_981, List.forall_mem_cons.2 ⟨subd19_1_982, List.forall_mem_cons.2 ⟨subd19_1_983, List.forall_mem_cons.2 ⟨subd19_1_984, List.forall_mem_cons.2 ⟨subd19_1_985, List.forall_mem_cons.2 ⟨subd19_1_986, List.forall_mem_cons.2 ⟨subd19_1_987, List.forall_mem_cons.2 ⟨subd19_1_988, List.forall_mem_cons.2 ⟨subd19_1_989, List.forall_mem_cons.2 ⟨subd19_1_990, List.forall_mem_cons.2 ⟨subd19_1_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_992 : subd19_1 [2, -1, -5] = true := by decide +kernel
theorem subd19_1_993 : subd19_1 [2, -1, -4] = true := by decide +kernel
theorem subd19_1_994 : subd19_1 [2, -1, -3] = true := by decide +kernel
theorem subd19_1_995 : subd19_1 [2, -1, -2] = true := by decide +kernel
theorem subd19_1_996 : subd19_1 [2, -1, -1] = true := by decide +kernel
theorem subd19_1_997 : subd19_1 [2, -1, 0] = true := by decide +kernel
theorem subd19_1_998 : subd19_1 [2, -1, 1] = true := by decide +kernel
theorem subd19_1_999 : subd19_1 [2, -1, 2] = true := by decide +kernel
theorem subd19_1_1000 : subd19_1 [2, -1, 3] = true := by decide +kernel
theorem subd19_1_1001 : subd19_1 [2, -1, 4] = true := by decide +kernel
theorem subd19_1_1002 : subd19_1 [2, -1, 5] = true := by decide +kernel
theorem subd19_1_1003 : subd19_1 [2, -1, 6] = true := by decide +kernel
theorem subd19_1_1004 : subd19_1 [2, 0, -9] = true := by decide +kernel
theorem subd19_1_1005 : subd19_1 [2, 0, -8] = true := by decide +kernel
theorem subd19_1_1006 : subd19_1 [2, 0, -7] = true := by decide +kernel
theorem subd19_1_1007 : subd19_1 [2, 0, -6] = true := by decide +kernel
theorem subd19_1_1008 : subd19_1 [2, 0, -5] = true := by decide +kernel
theorem subd19_1_1009 : subd19_1 [2, 0, -4] = true := by decide +kernel
theorem subd19_1_1010 : subd19_1 [2, 0, -3] = true := by decide +kernel
theorem subd19_1_1011 : subd19_1 [2, 0, -2] = true := by decide +kernel
theorem subd19_1_1012 : subd19_1 [2, 0, -1] = true := by decide +kernel
theorem subd19_1_1013 : subd19_1 [2, 0, 0] = true := by decide +kernel
theorem subd19_1_1014 : subd19_1 [2, 0, 1] = true := by decide +kernel
theorem subd19_1_1015 : subd19_1 [2, 0, 2] = true := by decide +kernel
theorem subd19_1_1016 : subd19_1 [2, 0, 3] = true := by decide +kernel
theorem subd19_1_1017 : subd19_1 [2, 0, 4] = true := by decide +kernel
theorem subd19_1_1018 : subd19_1 [2, 0, 5] = true := by decide +kernel
theorem subd19_1_1019 : subd19_1 [2, 0, 6] = true := by decide +kernel
theorem subd19_1_1020 : subd19_1 [2, 1, -8] = true := by decide +kernel
theorem subd19_1_1021 : subd19_1 [2, 1, -7] = true := by decide +kernel
theorem subd19_1_1022 : subd19_1 [2, 1, -6] = true := by decide +kernel
theorem subd19_1_1023 : subd19_1 [2, 1, -5] = true := by decide +kernel
theorem sbd19_1_31 : ∀ q ∈ blkd19_1_31, subd19_1 q = true := by
  unfold blkd19_1_31
  exact List.forall_mem_cons.2 ⟨subd19_1_992, List.forall_mem_cons.2 ⟨subd19_1_993, List.forall_mem_cons.2 ⟨subd19_1_994, List.forall_mem_cons.2 ⟨subd19_1_995, List.forall_mem_cons.2 ⟨subd19_1_996, List.forall_mem_cons.2 ⟨subd19_1_997, List.forall_mem_cons.2 ⟨subd19_1_998, List.forall_mem_cons.2 ⟨subd19_1_999, List.forall_mem_cons.2 ⟨subd19_1_1000, List.forall_mem_cons.2 ⟨subd19_1_1001, List.forall_mem_cons.2 ⟨subd19_1_1002, List.forall_mem_cons.2 ⟨subd19_1_1003, List.forall_mem_cons.2 ⟨subd19_1_1004, List.forall_mem_cons.2 ⟨subd19_1_1005, List.forall_mem_cons.2 ⟨subd19_1_1006, List.forall_mem_cons.2 ⟨subd19_1_1007, List.forall_mem_cons.2 ⟨subd19_1_1008, List.forall_mem_cons.2 ⟨subd19_1_1009, List.forall_mem_cons.2 ⟨subd19_1_1010, List.forall_mem_cons.2 ⟨subd19_1_1011, List.forall_mem_cons.2 ⟨subd19_1_1012, List.forall_mem_cons.2 ⟨subd19_1_1013, List.forall_mem_cons.2 ⟨subd19_1_1014, List.forall_mem_cons.2 ⟨subd19_1_1015, List.forall_mem_cons.2 ⟨subd19_1_1016, List.forall_mem_cons.2 ⟨subd19_1_1017, List.forall_mem_cons.2 ⟨subd19_1_1018, List.forall_mem_cons.2 ⟨subd19_1_1019, List.forall_mem_cons.2 ⟨subd19_1_1020, List.forall_mem_cons.2 ⟨subd19_1_1021, List.forall_mem_cons.2 ⟨subd19_1_1022, List.forall_mem_cons.2 ⟨subd19_1_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_1024 : subd19_1 [2, 1, -4] = true := by decide +kernel
theorem subd19_1_1025 : subd19_1 [2, 1, -3] = true := by decide +kernel
theorem subd19_1_1026 : subd19_1 [2, 1, -2] = true := by decide +kernel
theorem subd19_1_1027 : subd19_1 [2, 1, -1] = true := by decide +kernel
theorem subd19_1_1028 : subd19_1 [2, 1, 0] = true := by decide +kernel
theorem subd19_1_1029 : subd19_1 [2, 1, 1] = true := by decide +kernel
theorem subd19_1_1030 : subd19_1 [2, 1, 2] = true := by decide +kernel
theorem subd19_1_1031 : subd19_1 [2, 1, 3] = true := by decide +kernel
theorem subd19_1_1032 : subd19_1 [2, 1, 4] = true := by decide +kernel
theorem subd19_1_1033 : subd19_1 [2, 1, 5] = true := by decide +kernel
theorem subd19_1_1034 : subd19_1 [2, 1, 6] = true := by decide +kernel
theorem subd19_1_1035 : subd19_1 [2, 2, -8] = true := by decide +kernel
theorem subd19_1_1036 : subd19_1 [2, 2, -7] = true := by decide +kernel
theorem subd19_1_1037 : subd19_1 [2, 2, -6] = true := by decide +kernel
theorem subd19_1_1038 : subd19_1 [2, 2, -5] = true := by decide +kernel
theorem subd19_1_1039 : subd19_1 [2, 2, -4] = true := by decide +kernel
theorem subd19_1_1040 : subd19_1 [2, 2, -3] = true := by decide +kernel
theorem subd19_1_1041 : subd19_1 [2, 2, -2] = true := by decide +kernel
theorem subd19_1_1042 : subd19_1 [2, 2, -1] = true := by decide +kernel
theorem subd19_1_1043 : subd19_1 [2, 2, 0] = true := by decide +kernel
theorem subd19_1_1044 : subd19_1 [2, 2, 1] = true := by decide +kernel
theorem subd19_1_1045 : subd19_1 [2, 2, 2] = true := by decide +kernel
theorem subd19_1_1046 : subd19_1 [2, 2, 3] = true := by decide +kernel
theorem subd19_1_1047 : subd19_1 [2, 2, 4] = true := by decide +kernel
theorem subd19_1_1048 : subd19_1 [2, 2, 5] = true := by decide +kernel
theorem subd19_1_1049 : subd19_1 [2, 2, 6] = true := by decide +kernel
theorem subd19_1_1050 : subd19_1 [2, 3, -7] = true := by decide +kernel
theorem subd19_1_1051 : subd19_1 [2, 3, -6] = true := by decide +kernel
theorem subd19_1_1052 : subd19_1 [2, 3, -5] = true := by decide +kernel
theorem subd19_1_1053 : subd19_1 [2, 3, -4] = true := by decide +kernel
theorem subd19_1_1054 : subd19_1 [2, 3, -3] = true := by decide +kernel
theorem subd19_1_1055 : subd19_1 [2, 3, -2] = true := by decide +kernel
theorem sbd19_1_32 : ∀ q ∈ blkd19_1_32, subd19_1 q = true := by
  unfold blkd19_1_32
  exact List.forall_mem_cons.2 ⟨subd19_1_1024, List.forall_mem_cons.2 ⟨subd19_1_1025, List.forall_mem_cons.2 ⟨subd19_1_1026, List.forall_mem_cons.2 ⟨subd19_1_1027, List.forall_mem_cons.2 ⟨subd19_1_1028, List.forall_mem_cons.2 ⟨subd19_1_1029, List.forall_mem_cons.2 ⟨subd19_1_1030, List.forall_mem_cons.2 ⟨subd19_1_1031, List.forall_mem_cons.2 ⟨subd19_1_1032, List.forall_mem_cons.2 ⟨subd19_1_1033, List.forall_mem_cons.2 ⟨subd19_1_1034, List.forall_mem_cons.2 ⟨subd19_1_1035, List.forall_mem_cons.2 ⟨subd19_1_1036, List.forall_mem_cons.2 ⟨subd19_1_1037, List.forall_mem_cons.2 ⟨subd19_1_1038, List.forall_mem_cons.2 ⟨subd19_1_1039, List.forall_mem_cons.2 ⟨subd19_1_1040, List.forall_mem_cons.2 ⟨subd19_1_1041, List.forall_mem_cons.2 ⟨subd19_1_1042, List.forall_mem_cons.2 ⟨subd19_1_1043, List.forall_mem_cons.2 ⟨subd19_1_1044, List.forall_mem_cons.2 ⟨subd19_1_1045, List.forall_mem_cons.2 ⟨subd19_1_1046, List.forall_mem_cons.2 ⟨subd19_1_1047, List.forall_mem_cons.2 ⟨subd19_1_1048, List.forall_mem_cons.2 ⟨subd19_1_1049, List.forall_mem_cons.2 ⟨subd19_1_1050, List.forall_mem_cons.2 ⟨subd19_1_1051, List.forall_mem_cons.2 ⟨subd19_1_1052, List.forall_mem_cons.2 ⟨subd19_1_1053, List.forall_mem_cons.2 ⟨subd19_1_1054, List.forall_mem_cons.2 ⟨subd19_1_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_1056 : subd19_1 [2, 3, -1] = true := by decide +kernel
theorem subd19_1_1057 : subd19_1 [2, 3, 0] = true := by decide +kernel
theorem subd19_1_1058 : subd19_1 [2, 3, 1] = true := by decide +kernel
theorem subd19_1_1059 : subd19_1 [2, 3, 2] = true := by decide +kernel
theorem subd19_1_1060 : subd19_1 [2, 3, 3] = true := by decide +kernel
theorem subd19_1_1061 : subd19_1 [2, 3, 4] = true := by decide +kernel
theorem subd19_1_1062 : subd19_1 [2, 3, 5] = true := by decide +kernel
theorem subd19_1_1063 : subd19_1 [2, 3, 6] = true := by decide +kernel
theorem subd19_1_1064 : subd19_1 [2, 3, 7] = true := by decide +kernel
theorem subd19_1_1065 : subd19_1 [2, 4, -7] = true := by decide +kernel
theorem subd19_1_1066 : subd19_1 [2, 4, -6] = true := by decide +kernel
theorem subd19_1_1067 : subd19_1 [2, 4, -5] = true := by decide +kernel
theorem subd19_1_1068 : subd19_1 [2, 4, -4] = true := by decide +kernel
theorem subd19_1_1069 : subd19_1 [2, 4, -3] = true := by decide +kernel
theorem subd19_1_1070 : subd19_1 [2, 4, -2] = true := by decide +kernel
theorem subd19_1_1071 : subd19_1 [2, 4, -1] = true := by decide +kernel
theorem subd19_1_1072 : subd19_1 [2, 4, 0] = true := by decide +kernel
theorem subd19_1_1073 : subd19_1 [2, 4, 1] = true := by decide +kernel
theorem subd19_1_1074 : subd19_1 [2, 4, 2] = true := by decide +kernel
theorem subd19_1_1075 : subd19_1 [2, 4, 3] = true := by decide +kernel
theorem subd19_1_1076 : subd19_1 [2, 4, 4] = true := by decide +kernel
theorem subd19_1_1077 : subd19_1 [2, 4, 5] = true := by decide +kernel
theorem subd19_1_1078 : subd19_1 [2, 4, 6] = true := by decide +kernel
theorem subd19_1_1079 : subd19_1 [2, 4, 7] = true := by decide +kernel
theorem subd19_1_1080 : subd19_1 [2, 5] = true := by decide +kernel
theorem subd19_1_1081 : subd19_1 [2, 6] = true := by decide +kernel
theorem subd19_1_1082 : subd19_1 [2, 7] = true := by decide +kernel
theorem subd19_1_1083 : subd19_1 [2, 8] = true := by decide +kernel
theorem subd19_1_1084 : subd19_1 [2, 9] = true := by decide +kernel
theorem subd19_1_1085 : subd19_1 [3, -9] = true := by decide +kernel
theorem subd19_1_1086 : subd19_1 [3, -8] = true := by decide +kernel
theorem subd19_1_1087 : subd19_1 [3, -7] = true := by decide +kernel
theorem sbd19_1_33 : ∀ q ∈ blkd19_1_33, subd19_1 q = true := by
  unfold blkd19_1_33
  exact List.forall_mem_cons.2 ⟨subd19_1_1056, List.forall_mem_cons.2 ⟨subd19_1_1057, List.forall_mem_cons.2 ⟨subd19_1_1058, List.forall_mem_cons.2 ⟨subd19_1_1059, List.forall_mem_cons.2 ⟨subd19_1_1060, List.forall_mem_cons.2 ⟨subd19_1_1061, List.forall_mem_cons.2 ⟨subd19_1_1062, List.forall_mem_cons.2 ⟨subd19_1_1063, List.forall_mem_cons.2 ⟨subd19_1_1064, List.forall_mem_cons.2 ⟨subd19_1_1065, List.forall_mem_cons.2 ⟨subd19_1_1066, List.forall_mem_cons.2 ⟨subd19_1_1067, List.forall_mem_cons.2 ⟨subd19_1_1068, List.forall_mem_cons.2 ⟨subd19_1_1069, List.forall_mem_cons.2 ⟨subd19_1_1070, List.forall_mem_cons.2 ⟨subd19_1_1071, List.forall_mem_cons.2 ⟨subd19_1_1072, List.forall_mem_cons.2 ⟨subd19_1_1073, List.forall_mem_cons.2 ⟨subd19_1_1074, List.forall_mem_cons.2 ⟨subd19_1_1075, List.forall_mem_cons.2 ⟨subd19_1_1076, List.forall_mem_cons.2 ⟨subd19_1_1077, List.forall_mem_cons.2 ⟨subd19_1_1078, List.forall_mem_cons.2 ⟨subd19_1_1079, List.forall_mem_cons.2 ⟨subd19_1_1080, List.forall_mem_cons.2 ⟨subd19_1_1081, List.forall_mem_cons.2 ⟨subd19_1_1082, List.forall_mem_cons.2 ⟨subd19_1_1083, List.forall_mem_cons.2 ⟨subd19_1_1084, List.forall_mem_cons.2 ⟨subd19_1_1085, List.forall_mem_cons.2 ⟨subd19_1_1086, List.forall_mem_cons.2 ⟨subd19_1_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_1088 : subd19_1 [3, -6] = true := by decide +kernel
theorem subd19_1_1089 : subd19_1 [3, -5] = true := by decide +kernel
theorem subd19_1_1090 : subd19_1 [3, -4, -10] = true := by decide +kernel
theorem subd19_1_1091 : subd19_1 [3, -4, -9] = true := by decide +kernel
theorem subd19_1_1092 : subd19_1 [3, -4, -8] = true := by decide +kernel
theorem subd19_1_1093 : subd19_1 [3, -4, -7] = true := by decide +kernel
theorem subd19_1_1094 : subd19_1 [3, -4, -6] = true := by decide +kernel
theorem subd19_1_1095 : subd19_1 [3, -4, -5] = true := by decide +kernel
theorem subd19_1_1096 : subd19_1 [3, -4, -4] = true := by decide +kernel
theorem subd19_1_1097 : subd19_1 [3, -4, -3] = true := by decide +kernel
theorem subd19_1_1098 : subd19_1 [3, -4, -2] = true := by decide +kernel
theorem subd19_1_1099 : subd19_1 [3, -4, -1] = true := by decide +kernel
theorem subd19_1_1100 : subd19_1 [3, -4, 0] = true := by decide +kernel
theorem subd19_1_1101 : subd19_1 [3, -4, 1] = true := by decide +kernel
theorem subd19_1_1102 : subd19_1 [3, -4, 2] = true := by decide +kernel
theorem subd19_1_1103 : subd19_1 [3, -4, 3] = true := by decide +kernel
theorem subd19_1_1104 : subd19_1 [3, -3, -10] = true := by decide +kernel
theorem subd19_1_1105 : subd19_1 [3, -3, -9] = true := by decide +kernel
theorem subd19_1_1106 : subd19_1 [3, -3, -8] = true := by decide +kernel
theorem subd19_1_1107 : subd19_1 [3, -3, -7] = true := by decide +kernel
theorem subd19_1_1108 : subd19_1 [3, -3, -6] = true := by decide +kernel
theorem subd19_1_1109 : subd19_1 [3, -3, -5] = true := by decide +kernel
theorem subd19_1_1110 : subd19_1 [3, -3, -4] = true := by decide +kernel
theorem subd19_1_1111 : subd19_1 [3, -3, -3] = true := by decide +kernel
theorem subd19_1_1112 : subd19_1 [3, -3, -2] = true := by decide +kernel
theorem subd19_1_1113 : subd19_1 [3, -3, -1] = true := by decide +kernel
theorem subd19_1_1114 : subd19_1 [3, -3, 0] = true := by decide +kernel
theorem subd19_1_1115 : subd19_1 [3, -3, 1] = true := by decide +kernel
theorem subd19_1_1116 : subd19_1 [3, -3, 2] = true := by decide +kernel
theorem subd19_1_1117 : subd19_1 [3, -3, 3] = true := by decide +kernel
theorem subd19_1_1118 : subd19_1 [3, -3, 4] = true := by decide +kernel
theorem subd19_1_1119 : subd19_1 [3, -2, -10] = true := by decide +kernel
theorem sbd19_1_34 : ∀ q ∈ blkd19_1_34, subd19_1 q = true := by
  unfold blkd19_1_34
  exact List.forall_mem_cons.2 ⟨subd19_1_1088, List.forall_mem_cons.2 ⟨subd19_1_1089, List.forall_mem_cons.2 ⟨subd19_1_1090, List.forall_mem_cons.2 ⟨subd19_1_1091, List.forall_mem_cons.2 ⟨subd19_1_1092, List.forall_mem_cons.2 ⟨subd19_1_1093, List.forall_mem_cons.2 ⟨subd19_1_1094, List.forall_mem_cons.2 ⟨subd19_1_1095, List.forall_mem_cons.2 ⟨subd19_1_1096, List.forall_mem_cons.2 ⟨subd19_1_1097, List.forall_mem_cons.2 ⟨subd19_1_1098, List.forall_mem_cons.2 ⟨subd19_1_1099, List.forall_mem_cons.2 ⟨subd19_1_1100, List.forall_mem_cons.2 ⟨subd19_1_1101, List.forall_mem_cons.2 ⟨subd19_1_1102, List.forall_mem_cons.2 ⟨subd19_1_1103, List.forall_mem_cons.2 ⟨subd19_1_1104, List.forall_mem_cons.2 ⟨subd19_1_1105, List.forall_mem_cons.2 ⟨subd19_1_1106, List.forall_mem_cons.2 ⟨subd19_1_1107, List.forall_mem_cons.2 ⟨subd19_1_1108, List.forall_mem_cons.2 ⟨subd19_1_1109, List.forall_mem_cons.2 ⟨subd19_1_1110, List.forall_mem_cons.2 ⟨subd19_1_1111, List.forall_mem_cons.2 ⟨subd19_1_1112, List.forall_mem_cons.2 ⟨subd19_1_1113, List.forall_mem_cons.2 ⟨subd19_1_1114, List.forall_mem_cons.2 ⟨subd19_1_1115, List.forall_mem_cons.2 ⟨subd19_1_1116, List.forall_mem_cons.2 ⟨subd19_1_1117, List.forall_mem_cons.2 ⟨subd19_1_1118, List.forall_mem_cons.2 ⟨subd19_1_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_1120 : subd19_1 [3, -2, -9] = true := by decide +kernel
theorem subd19_1_1121 : subd19_1 [3, -2, -8] = true := by decide +kernel
theorem subd19_1_1122 : subd19_1 [3, -2, -7] = true := by decide +kernel
theorem subd19_1_1123 : subd19_1 [3, -2, -6] = true := by decide +kernel
theorem subd19_1_1124 : subd19_1 [3, -2, -5] = true := by decide +kernel
theorem subd19_1_1125 : subd19_1 [3, -2, -4] = true := by decide +kernel
theorem subd19_1_1126 : subd19_1 [3, -2, -3] = true := by decide +kernel
theorem subd19_1_1127 : subd19_1 [3, -2, -2] = true := by decide +kernel
theorem subd19_1_1128 : subd19_1 [3, -2, -1] = true := by decide +kernel
theorem subd19_1_1129 : subd19_1 [3, -2, 0] = true := by decide +kernel
theorem subd19_1_1130 : subd19_1 [3, -2, 1] = true := by decide +kernel
theorem subd19_1_1131 : subd19_1 [3, -2, 2] = true := by decide +kernel
theorem subd19_1_1132 : subd19_1 [3, -2, 3] = true := by decide +kernel
theorem subd19_1_1133 : subd19_1 [3, -2, 4] = true := by decide +kernel
theorem subd19_1_1134 : subd19_1 [3, -1, -9] = true := by decide +kernel
theorem subd19_1_1135 : subd19_1 [3, -1, -8] = true := by decide +kernel
theorem subd19_1_1136 : subd19_1 [3, -1, -7] = true := by decide +kernel
theorem subd19_1_1137 : subd19_1 [3, -1, -6] = true := by decide +kernel
theorem subd19_1_1138 : subd19_1 [3, -1, -5] = true := by decide +kernel
theorem subd19_1_1139 : subd19_1 [3, -1, -4] = true := by decide +kernel
theorem subd19_1_1140 : subd19_1 [3, -1, -3] = true := by decide +kernel
theorem subd19_1_1141 : subd19_1 [3, -1, -2] = true := by decide +kernel
theorem subd19_1_1142 : subd19_1 [3, -1, -1] = true := by decide +kernel
theorem subd19_1_1143 : subd19_1 [3, -1, 0] = true := by decide +kernel
theorem subd19_1_1144 : subd19_1 [3, -1, 1] = true := by decide +kernel
theorem subd19_1_1145 : subd19_1 [3, -1, 2] = true := by decide +kernel
theorem subd19_1_1146 : subd19_1 [3, -1, 3] = true := by decide +kernel
theorem subd19_1_1147 : subd19_1 [3, -1, 4] = true := by decide +kernel
theorem subd19_1_1148 : subd19_1 [3, -1, 5] = true := by decide +kernel
theorem subd19_1_1149 : subd19_1 [3, 0, -9] = true := by decide +kernel
theorem subd19_1_1150 : subd19_1 [3, 0, -8] = true := by decide +kernel
theorem subd19_1_1151 : subd19_1 [3, 0, -7] = true := by decide +kernel
theorem sbd19_1_35 : ∀ q ∈ blkd19_1_35, subd19_1 q = true := by
  unfold blkd19_1_35
  exact List.forall_mem_cons.2 ⟨subd19_1_1120, List.forall_mem_cons.2 ⟨subd19_1_1121, List.forall_mem_cons.2 ⟨subd19_1_1122, List.forall_mem_cons.2 ⟨subd19_1_1123, List.forall_mem_cons.2 ⟨subd19_1_1124, List.forall_mem_cons.2 ⟨subd19_1_1125, List.forall_mem_cons.2 ⟨subd19_1_1126, List.forall_mem_cons.2 ⟨subd19_1_1127, List.forall_mem_cons.2 ⟨subd19_1_1128, List.forall_mem_cons.2 ⟨subd19_1_1129, List.forall_mem_cons.2 ⟨subd19_1_1130, List.forall_mem_cons.2 ⟨subd19_1_1131, List.forall_mem_cons.2 ⟨subd19_1_1132, List.forall_mem_cons.2 ⟨subd19_1_1133, List.forall_mem_cons.2 ⟨subd19_1_1134, List.forall_mem_cons.2 ⟨subd19_1_1135, List.forall_mem_cons.2 ⟨subd19_1_1136, List.forall_mem_cons.2 ⟨subd19_1_1137, List.forall_mem_cons.2 ⟨subd19_1_1138, List.forall_mem_cons.2 ⟨subd19_1_1139, List.forall_mem_cons.2 ⟨subd19_1_1140, List.forall_mem_cons.2 ⟨subd19_1_1141, List.forall_mem_cons.2 ⟨subd19_1_1142, List.forall_mem_cons.2 ⟨subd19_1_1143, List.forall_mem_cons.2 ⟨subd19_1_1144, List.forall_mem_cons.2 ⟨subd19_1_1145, List.forall_mem_cons.2 ⟨subd19_1_1146, List.forall_mem_cons.2 ⟨subd19_1_1147, List.forall_mem_cons.2 ⟨subd19_1_1148, List.forall_mem_cons.2 ⟨subd19_1_1149, List.forall_mem_cons.2 ⟨subd19_1_1150, List.forall_mem_cons.2 ⟨subd19_1_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_1152 : subd19_1 [3, 0, -6] = true := by decide +kernel
theorem subd19_1_1153 : subd19_1 [3, 0, -5] = true := by decide +kernel
theorem subd19_1_1154 : subd19_1 [3, 0, -4] = true := by decide +kernel
theorem subd19_1_1155 : subd19_1 [3, 0, -3] = true := by decide +kernel
theorem subd19_1_1156 : subd19_1 [3, 0, -2] = true := by decide +kernel
theorem subd19_1_1157 : subd19_1 [3, 0, -1] = true := by decide +kernel
theorem subd19_1_1158 : subd19_1 [3, 0, 0] = true := by decide +kernel
theorem subd19_1_1159 : subd19_1 [3, 0, 1] = true := by decide +kernel
theorem subd19_1_1160 : subd19_1 [3, 0, 2] = true := by decide +kernel
theorem subd19_1_1161 : subd19_1 [3, 0, 3] = true := by decide +kernel
theorem subd19_1_1162 : subd19_1 [3, 0, 4] = true := by decide +kernel
theorem subd19_1_1163 : subd19_1 [3, 0, 5] = true := by decide +kernel
theorem subd19_1_1164 : subd19_1 [3, 1, -9] = true := by decide +kernel
theorem subd19_1_1165 : subd19_1 [3, 1, -8] = true := by decide +kernel
theorem subd19_1_1166 : subd19_1 [3, 1, -7] = true := by decide +kernel
theorem subd19_1_1167 : subd19_1 [3, 1, -6] = true := by decide +kernel
theorem subd19_1_1168 : subd19_1 [3, 1, -5] = true := by decide +kernel
theorem subd19_1_1169 : subd19_1 [3, 1, -4] = true := by decide +kernel
theorem subd19_1_1170 : subd19_1 [3, 1, -3] = true := by decide +kernel
theorem subd19_1_1171 : subd19_1 [3, 1, -2] = true := by decide +kernel
theorem subd19_1_1172 : subd19_1 [3, 1, -1] = true := by decide +kernel
theorem subd19_1_1173 : subd19_1 [3, 1, 0] = true := by decide +kernel
theorem subd19_1_1174 : subd19_1 [3, 1, 1] = true := by decide +kernel
theorem subd19_1_1175 : subd19_1 [3, 1, 2] = true := by decide +kernel
theorem subd19_1_1176 : subd19_1 [3, 1, 3] = true := by decide +kernel
theorem subd19_1_1177 : subd19_1 [3, 1, 4] = true := by decide +kernel
theorem subd19_1_1178 : subd19_1 [3, 1, 5] = true := by decide +kernel
theorem subd19_1_1179 : subd19_1 [3, 1, 6] = true := by decide +kernel
theorem subd19_1_1180 : subd19_1 [3, 2, -8] = true := by decide +kernel
theorem subd19_1_1181 : subd19_1 [3, 2, -7] = true := by decide +kernel
theorem subd19_1_1182 : subd19_1 [3, 2, -6] = true := by decide +kernel
theorem subd19_1_1183 : subd19_1 [3, 2, -5] = true := by decide +kernel
theorem sbd19_1_36 : ∀ q ∈ blkd19_1_36, subd19_1 q = true := by
  unfold blkd19_1_36
  exact List.forall_mem_cons.2 ⟨subd19_1_1152, List.forall_mem_cons.2 ⟨subd19_1_1153, List.forall_mem_cons.2 ⟨subd19_1_1154, List.forall_mem_cons.2 ⟨subd19_1_1155, List.forall_mem_cons.2 ⟨subd19_1_1156, List.forall_mem_cons.2 ⟨subd19_1_1157, List.forall_mem_cons.2 ⟨subd19_1_1158, List.forall_mem_cons.2 ⟨subd19_1_1159, List.forall_mem_cons.2 ⟨subd19_1_1160, List.forall_mem_cons.2 ⟨subd19_1_1161, List.forall_mem_cons.2 ⟨subd19_1_1162, List.forall_mem_cons.2 ⟨subd19_1_1163, List.forall_mem_cons.2 ⟨subd19_1_1164, List.forall_mem_cons.2 ⟨subd19_1_1165, List.forall_mem_cons.2 ⟨subd19_1_1166, List.forall_mem_cons.2 ⟨subd19_1_1167, List.forall_mem_cons.2 ⟨subd19_1_1168, List.forall_mem_cons.2 ⟨subd19_1_1169, List.forall_mem_cons.2 ⟨subd19_1_1170, List.forall_mem_cons.2 ⟨subd19_1_1171, List.forall_mem_cons.2 ⟨subd19_1_1172, List.forall_mem_cons.2 ⟨subd19_1_1173, List.forall_mem_cons.2 ⟨subd19_1_1174, List.forall_mem_cons.2 ⟨subd19_1_1175, List.forall_mem_cons.2 ⟨subd19_1_1176, List.forall_mem_cons.2 ⟨subd19_1_1177, List.forall_mem_cons.2 ⟨subd19_1_1178, List.forall_mem_cons.2 ⟨subd19_1_1179, List.forall_mem_cons.2 ⟨subd19_1_1180, List.forall_mem_cons.2 ⟨subd19_1_1181, List.forall_mem_cons.2 ⟨subd19_1_1182, List.forall_mem_cons.2 ⟨subd19_1_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
