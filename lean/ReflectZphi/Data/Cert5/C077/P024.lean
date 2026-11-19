import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_1_736 : subd11_1 [2, 1, -2] = true := by decide +kernel
theorem subd11_1_737 : subd11_1 [2, 1, -1] = true := by decide +kernel
theorem subd11_1_738 : subd11_1 [2, 1, 0] = true := by decide +kernel
theorem subd11_1_739 : subd11_1 [2, 1, 1] = true := by decide +kernel
theorem subd11_1_740 : subd11_1 [2, 1, 2] = true := by decide +kernel
theorem subd11_1_741 : subd11_1 [2, 1, 3] = true := by decide +kernel
theorem subd11_1_742 : subd11_1 [2, 1, 4] = true := by decide +kernel
theorem subd11_1_743 : subd11_1 [2, 1, 5] = true := by decide +kernel
theorem subd11_1_744 : subd11_1 [2, 1, 6] = true := by decide +kernel
theorem subd11_1_745 : subd11_1 [2, 1, 7] = true := by decide +kernel
theorem subd11_1_746 : subd11_1 [2, 2, -7] = true := by decide +kernel
theorem subd11_1_747 : subd11_1 [2, 2, -6] = true := by decide +kernel
theorem subd11_1_748 : subd11_1 [2, 2, -5] = true := by decide +kernel
theorem subd11_1_749 : subd11_1 [2, 2, -4] = true := by decide +kernel
theorem subd11_1_750 : subd11_1 [2, 2, -3] = true := by decide +kernel
theorem subd11_1_751 : subd11_1 [2, 2, -2] = true := by decide +kernel
theorem subd11_1_752 : subd11_1 [2, 2, -1] = true := by decide +kernel
theorem subd11_1_753 : subd11_1 [2, 2, 0] = true := by decide +kernel
theorem subd11_1_754 : subd11_1 [2, 2, 1] = true := by decide +kernel
theorem subd11_1_755 : subd11_1 [2, 2, 2] = true := by decide +kernel
theorem subd11_1_756 : subd11_1 [2, 2, 3] = true := by decide +kernel
theorem subd11_1_757 : subd11_1 [2, 2, 4] = true := by decide +kernel
theorem subd11_1_758 : subd11_1 [2, 2, 5] = true := by decide +kernel
theorem subd11_1_759 : subd11_1 [2, 2, 6] = true := by decide +kernel
theorem subd11_1_760 : subd11_1 [2, 3] = true := by decide +kernel
theorem subd11_1_761 : subd11_1 [2, 4] = true := by decide +kernel
theorem subd11_1_762 : subd11_1 [2, 5] = true := by decide +kernel
theorem subd11_1_763 : subd11_1 [2, 6] = true := by decide +kernel
theorem subd11_1_764 : subd11_1 [2, 7] = true := by decide +kernel
theorem subd11_1_765 : subd11_1 [3, -9] = true := by decide +kernel
theorem subd11_1_766 : subd11_1 [3, -8] = true := by decide +kernel
theorem subd11_1_767 : subd11_1 [3, -7] = true := by decide +kernel
theorem sbd11_1_23 : ∀ q ∈ blkd11_1_23, subd11_1 q = true := by
  unfold blkd11_1_23
  exact List.forall_mem_cons.2 ⟨subd11_1_736, List.forall_mem_cons.2 ⟨subd11_1_737, List.forall_mem_cons.2 ⟨subd11_1_738, List.forall_mem_cons.2 ⟨subd11_1_739, List.forall_mem_cons.2 ⟨subd11_1_740, List.forall_mem_cons.2 ⟨subd11_1_741, List.forall_mem_cons.2 ⟨subd11_1_742, List.forall_mem_cons.2 ⟨subd11_1_743, List.forall_mem_cons.2 ⟨subd11_1_744, List.forall_mem_cons.2 ⟨subd11_1_745, List.forall_mem_cons.2 ⟨subd11_1_746, List.forall_mem_cons.2 ⟨subd11_1_747, List.forall_mem_cons.2 ⟨subd11_1_748, List.forall_mem_cons.2 ⟨subd11_1_749, List.forall_mem_cons.2 ⟨subd11_1_750, List.forall_mem_cons.2 ⟨subd11_1_751, List.forall_mem_cons.2 ⟨subd11_1_752, List.forall_mem_cons.2 ⟨subd11_1_753, List.forall_mem_cons.2 ⟨subd11_1_754, List.forall_mem_cons.2 ⟨subd11_1_755, List.forall_mem_cons.2 ⟨subd11_1_756, List.forall_mem_cons.2 ⟨subd11_1_757, List.forall_mem_cons.2 ⟨subd11_1_758, List.forall_mem_cons.2 ⟨subd11_1_759, List.forall_mem_cons.2 ⟨subd11_1_760, List.forall_mem_cons.2 ⟨subd11_1_761, List.forall_mem_cons.2 ⟨subd11_1_762, List.forall_mem_cons.2 ⟨subd11_1_763, List.forall_mem_cons.2 ⟨subd11_1_764, List.forall_mem_cons.2 ⟨subd11_1_765, List.forall_mem_cons.2 ⟨subd11_1_766, List.forall_mem_cons.2 ⟨subd11_1_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_768 : subd11_1 [3, -6] = true := by decide +kernel
theorem subd11_1_769 : subd11_1 [3, -5] = true := by decide +kernel
theorem subd11_1_770 : subd11_1 [3, -4] = true := by decide +kernel
theorem subd11_1_771 : subd11_1 [3, -3, -7] = true := by decide +kernel
theorem subd11_1_772 : subd11_1 [3, -3, -6] = true := by decide +kernel
theorem subd11_1_773 : subd11_1 [3, -3, -5] = true := by decide +kernel
theorem subd11_1_774 : subd11_1 [3, -3, -4] = true := by decide +kernel
theorem subd11_1_775 : subd11_1 [3, -3, -3] = true := by decide +kernel
theorem subd11_1_776 : subd11_1 [3, -3, -2] = true := by decide +kernel
theorem subd11_1_777 : subd11_1 [3, -3, -1] = true := by decide +kernel
theorem subd11_1_778 : subd11_1 [3, -3, 0] = true := by decide +kernel
theorem subd11_1_779 : subd11_1 [3, -3, 1] = true := by decide +kernel
theorem subd11_1_780 : subd11_1 [3, -3, 2] = true := by decide +kernel
theorem subd11_1_781 : subd11_1 [3, -3, 3] = true := by decide +kernel
theorem subd11_1_782 : subd11_1 [3, -3, 4] = true := by decide +kernel
theorem subd11_1_783 : subd11_1 [3, -3, 5] = true := by decide +kernel
theorem subd11_1_784 : subd11_1 [3, -3, 6] = true := by decide +kernel
theorem subd11_1_785 : subd11_1 [3, -3, 7] = true := by decide +kernel
theorem subd11_1_786 : subd11_1 [3, -2, -7] = true := by decide +kernel
theorem subd11_1_787 : subd11_1 [3, -2, -6] = true := by decide +kernel
theorem subd11_1_788 : subd11_1 [3, -2, -5] = true := by decide +kernel
theorem subd11_1_789 : subd11_1 [3, -2, -4] = true := by decide +kernel
theorem subd11_1_790 : subd11_1 [3, -2, -3] = true := by decide +kernel
theorem subd11_1_791 : subd11_1 [3, -2, -2] = true := by decide +kernel
theorem subd11_1_792 : subd11_1 [3, -2, -1] = true := by decide +kernel
theorem subd11_1_793 : subd11_1 [3, -2, 0] = true := by decide +kernel
theorem subd11_1_794 : subd11_1 [3, -2, 1] = true := by decide +kernel
theorem subd11_1_795 : subd11_1 [3, -2, 2] = true := by decide +kernel
theorem subd11_1_796 : subd11_1 [3, -2, 3] = true := by decide +kernel
theorem subd11_1_797 : subd11_1 [3, -2, 4] = true := by decide +kernel
theorem subd11_1_798 : subd11_1 [3, -2, 5] = true := by decide +kernel
theorem subd11_1_799 : subd11_1 [3, -2, 6] = true := by decide +kernel
theorem sbd11_1_24 : ∀ q ∈ blkd11_1_24, subd11_1 q = true := by
  unfold blkd11_1_24
  exact List.forall_mem_cons.2 ⟨subd11_1_768, List.forall_mem_cons.2 ⟨subd11_1_769, List.forall_mem_cons.2 ⟨subd11_1_770, List.forall_mem_cons.2 ⟨subd11_1_771, List.forall_mem_cons.2 ⟨subd11_1_772, List.forall_mem_cons.2 ⟨subd11_1_773, List.forall_mem_cons.2 ⟨subd11_1_774, List.forall_mem_cons.2 ⟨subd11_1_775, List.forall_mem_cons.2 ⟨subd11_1_776, List.forall_mem_cons.2 ⟨subd11_1_777, List.forall_mem_cons.2 ⟨subd11_1_778, List.forall_mem_cons.2 ⟨subd11_1_779, List.forall_mem_cons.2 ⟨subd11_1_780, List.forall_mem_cons.2 ⟨subd11_1_781, List.forall_mem_cons.2 ⟨subd11_1_782, List.forall_mem_cons.2 ⟨subd11_1_783, List.forall_mem_cons.2 ⟨subd11_1_784, List.forall_mem_cons.2 ⟨subd11_1_785, List.forall_mem_cons.2 ⟨subd11_1_786, List.forall_mem_cons.2 ⟨subd11_1_787, List.forall_mem_cons.2 ⟨subd11_1_788, List.forall_mem_cons.2 ⟨subd11_1_789, List.forall_mem_cons.2 ⟨subd11_1_790, List.forall_mem_cons.2 ⟨subd11_1_791, List.forall_mem_cons.2 ⟨subd11_1_792, List.forall_mem_cons.2 ⟨subd11_1_793, List.forall_mem_cons.2 ⟨subd11_1_794, List.forall_mem_cons.2 ⟨subd11_1_795, List.forall_mem_cons.2 ⟨subd11_1_796, List.forall_mem_cons.2 ⟨subd11_1_797, List.forall_mem_cons.2 ⟨subd11_1_798, List.forall_mem_cons.2 ⟨subd11_1_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_800 : subd11_1 [3, -2, 7] = true := by decide +kernel
theorem subd11_1_801 : subd11_1 [3, -1, -7] = true := by decide +kernel
theorem subd11_1_802 : subd11_1 [3, -1, -6] = true := by decide +kernel
theorem subd11_1_803 : subd11_1 [3, -1, -5] = true := by decide +kernel
theorem subd11_1_804 : subd11_1 [3, -1, -4] = true := by decide +kernel
theorem subd11_1_805 : subd11_1 [3, -1, -3] = true := by decide +kernel
theorem subd11_1_806 : subd11_1 [3, -1, -2] = true := by decide +kernel
theorem subd11_1_807 : subd11_1 [3, -1, -1] = true := by decide +kernel
theorem subd11_1_808 : subd11_1 [3, -1, 0] = true := by decide +kernel
theorem subd11_1_809 : subd11_1 [3, -1, 1] = true := by decide +kernel
theorem subd11_1_810 : subd11_1 [3, -1, 2] = true := by decide +kernel
theorem subd11_1_811 : subd11_1 [3, -1, 3] = true := by decide +kernel
theorem subd11_1_812 : subd11_1 [3, -1, 4] = true := by decide +kernel
theorem subd11_1_813 : subd11_1 [3, -1, 5] = true := by decide +kernel
theorem subd11_1_814 : subd11_1 [3, -1, 6] = true := by decide +kernel
theorem subd11_1_815 : subd11_1 [3, -1, 7] = true := by decide +kernel
theorem subd11_1_816 : subd11_1 [3, 0, -7] = true := by decide +kernel
theorem subd11_1_817 : subd11_1 [3, 0, -6] = true := by decide +kernel
theorem subd11_1_818 : subd11_1 [3, 0, -5] = true := by decide +kernel
theorem subd11_1_819 : subd11_1 [3, 0, -4] = true := by decide +kernel
theorem subd11_1_820 : subd11_1 [3, 0, -3] = true := by decide +kernel
theorem subd11_1_821 : subd11_1 [3, 0, -2] = true := by decide +kernel
theorem subd11_1_822 : subd11_1 [3, 0, -1] = true := by decide +kernel
theorem subd11_1_823 : subd11_1 [3, 0, 0] = true := by decide +kernel
theorem subd11_1_824 : subd11_1 [3, 0, 1] = true := by decide +kernel
theorem subd11_1_825 : subd11_1 [3, 0, 2] = true := by decide +kernel
theorem subd11_1_826 : subd11_1 [3, 0, 3] = true := by decide +kernel
theorem subd11_1_827 : subd11_1 [3, 0, 4] = true := by decide +kernel
theorem subd11_1_828 : subd11_1 [3, 0, 5] = true := by decide +kernel
theorem subd11_1_829 : subd11_1 [3, 0, 6] = true := by decide +kernel
theorem subd11_1_830 : subd11_1 [3, 0, 7] = true := by decide +kernel
theorem subd11_1_831 : subd11_1 [3, 1, -7] = true := by decide +kernel
theorem sbd11_1_25 : ∀ q ∈ blkd11_1_25, subd11_1 q = true := by
  unfold blkd11_1_25
  exact List.forall_mem_cons.2 ⟨subd11_1_800, List.forall_mem_cons.2 ⟨subd11_1_801, List.forall_mem_cons.2 ⟨subd11_1_802, List.forall_mem_cons.2 ⟨subd11_1_803, List.forall_mem_cons.2 ⟨subd11_1_804, List.forall_mem_cons.2 ⟨subd11_1_805, List.forall_mem_cons.2 ⟨subd11_1_806, List.forall_mem_cons.2 ⟨subd11_1_807, List.forall_mem_cons.2 ⟨subd11_1_808, List.forall_mem_cons.2 ⟨subd11_1_809, List.forall_mem_cons.2 ⟨subd11_1_810, List.forall_mem_cons.2 ⟨subd11_1_811, List.forall_mem_cons.2 ⟨subd11_1_812, List.forall_mem_cons.2 ⟨subd11_1_813, List.forall_mem_cons.2 ⟨subd11_1_814, List.forall_mem_cons.2 ⟨subd11_1_815, List.forall_mem_cons.2 ⟨subd11_1_816, List.forall_mem_cons.2 ⟨subd11_1_817, List.forall_mem_cons.2 ⟨subd11_1_818, List.forall_mem_cons.2 ⟨subd11_1_819, List.forall_mem_cons.2 ⟨subd11_1_820, List.forall_mem_cons.2 ⟨subd11_1_821, List.forall_mem_cons.2 ⟨subd11_1_822, List.forall_mem_cons.2 ⟨subd11_1_823, List.forall_mem_cons.2 ⟨subd11_1_824, List.forall_mem_cons.2 ⟨subd11_1_825, List.forall_mem_cons.2 ⟨subd11_1_826, List.forall_mem_cons.2 ⟨subd11_1_827, List.forall_mem_cons.2 ⟨subd11_1_828, List.forall_mem_cons.2 ⟨subd11_1_829, List.forall_mem_cons.2 ⟨subd11_1_830, List.forall_mem_cons.2 ⟨subd11_1_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_832 : subd11_1 [3, 1, -6] = true := by decide +kernel
theorem subd11_1_833 : subd11_1 [3, 1, -5] = true := by decide +kernel
theorem subd11_1_834 : subd11_1 [3, 1, -4] = true := by decide +kernel
theorem subd11_1_835 : subd11_1 [3, 1, -3] = true := by decide +kernel
theorem subd11_1_836 : subd11_1 [3, 1, -2] = true := by decide +kernel
theorem subd11_1_837 : subd11_1 [3, 1, -1] = true := by decide +kernel
theorem subd11_1_838 : subd11_1 [3, 1, 0] = true := by decide +kernel
theorem subd11_1_839 : subd11_1 [3, 1, 1] = true := by decide +kernel
theorem subd11_1_840 : subd11_1 [3, 1, 2] = true := by decide +kernel
theorem subd11_1_841 : subd11_1 [3, 1, 3] = true := by decide +kernel
theorem subd11_1_842 : subd11_1 [3, 1, 4] = true := by decide +kernel
theorem subd11_1_843 : subd11_1 [3, 1, 5] = true := by decide +kernel
theorem subd11_1_844 : subd11_1 [3, 1, 6] = true := by decide +kernel
theorem subd11_1_845 : subd11_1 [3, 1, 7] = true := by decide +kernel
theorem subd11_1_846 : subd11_1 [3, 2] = true := by decide +kernel
theorem subd11_1_847 : subd11_1 [3, 3] = true := by decide +kernel
theorem subd11_1_848 : subd11_1 [3, 4] = true := by decide +kernel
theorem subd11_1_849 : subd11_1 [3, 5] = true := by decide +kernel
theorem subd11_1_850 : subd11_1 [3, 6] = true := by decide +kernel
theorem subd11_1_851 : subd11_1 [4, -9] = true := by decide +kernel
theorem subd11_1_852 : subd11_1 [4, -8] = true := by decide +kernel
theorem subd11_1_853 : subd11_1 [4, -7] = true := by decide +kernel
theorem subd11_1_854 : subd11_1 [4, -6] = true := by decide +kernel
theorem subd11_1_855 : subd11_1 [4, -5] = true := by decide +kernel
theorem subd11_1_856 : subd11_1 [4, -4] = true := by decide +kernel
theorem subd11_1_857 : subd11_1 [4, -3] = true := by decide +kernel
theorem subd11_1_858 : subd11_1 [4, -2] = true := by decide +kernel
theorem subd11_1_859 : subd11_1 [4, -1] = true := by decide +kernel
theorem subd11_1_860 : subd11_1 [4, 0] = true := by decide +kernel
theorem subd11_1_861 : subd11_1 [4, 1] = true := by decide +kernel
theorem subd11_1_862 : subd11_1 [4, 2] = true := by decide +kernel
theorem subd11_1_863 : subd11_1 [4, 3] = true := by decide +kernel
theorem sbd11_1_26 : ∀ q ∈ blkd11_1_26, subd11_1 q = true := by
  unfold blkd11_1_26
  exact List.forall_mem_cons.2 ⟨subd11_1_832, List.forall_mem_cons.2 ⟨subd11_1_833, List.forall_mem_cons.2 ⟨subd11_1_834, List.forall_mem_cons.2 ⟨subd11_1_835, List.forall_mem_cons.2 ⟨subd11_1_836, List.forall_mem_cons.2 ⟨subd11_1_837, List.forall_mem_cons.2 ⟨subd11_1_838, List.forall_mem_cons.2 ⟨subd11_1_839, List.forall_mem_cons.2 ⟨subd11_1_840, List.forall_mem_cons.2 ⟨subd11_1_841, List.forall_mem_cons.2 ⟨subd11_1_842, List.forall_mem_cons.2 ⟨subd11_1_843, List.forall_mem_cons.2 ⟨subd11_1_844, List.forall_mem_cons.2 ⟨subd11_1_845, List.forall_mem_cons.2 ⟨subd11_1_846, List.forall_mem_cons.2 ⟨subd11_1_847, List.forall_mem_cons.2 ⟨subd11_1_848, List.forall_mem_cons.2 ⟨subd11_1_849, List.forall_mem_cons.2 ⟨subd11_1_850, List.forall_mem_cons.2 ⟨subd11_1_851, List.forall_mem_cons.2 ⟨subd11_1_852, List.forall_mem_cons.2 ⟨subd11_1_853, List.forall_mem_cons.2 ⟨subd11_1_854, List.forall_mem_cons.2 ⟨subd11_1_855, List.forall_mem_cons.2 ⟨subd11_1_856, List.forall_mem_cons.2 ⟨subd11_1_857, List.forall_mem_cons.2 ⟨subd11_1_858, List.forall_mem_cons.2 ⟨subd11_1_859, List.forall_mem_cons.2 ⟨subd11_1_860, List.forall_mem_cons.2 ⟨subd11_1_861, List.forall_mem_cons.2 ⟨subd11_1_862, List.forall_mem_cons.2 ⟨subd11_1_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_864 : subd11_1 [4, 4] = true := by decide +kernel
theorem subd11_1_865 : subd11_1 [4, 5] = true := by decide +kernel
theorem subd11_1_866 : subd11_1 [5, -8] = true := by decide +kernel
theorem subd11_1_867 : subd11_1 [5, -7] = true := by decide +kernel
theorem subd11_1_868 : subd11_1 [5, -6] = true := by decide +kernel
theorem subd11_1_869 : subd11_1 [5, -5] = true := by decide +kernel
theorem subd11_1_870 : subd11_1 [5, -4] = true := by decide +kernel
theorem subd11_1_871 : subd11_1 [5, -3] = true := by decide +kernel
theorem subd11_1_872 : subd11_1 [5, -2] = true := by decide +kernel
theorem subd11_1_873 : subd11_1 [5, -1] = true := by decide +kernel
theorem subd11_1_874 : subd11_1 [5, 0] = true := by decide +kernel
theorem subd11_1_875 : subd11_1 [5, 1] = true := by decide +kernel
theorem subd11_1_876 : subd11_1 [5, 2] = true := by decide +kernel
theorem subd11_1_877 : subd11_1 [5, 3] = true := by decide +kernel
theorem subd11_1_878 : subd11_1 [5, 4] = true := by decide +kernel
theorem subd11_1_879 : subd11_1 [6, -8] = true := by decide +kernel
theorem subd11_1_880 : subd11_1 [6, -7] = true := by decide +kernel
theorem subd11_1_881 : subd11_1 [6, -6] = true := by decide +kernel
theorem subd11_1_882 : subd11_1 [6, -5] = true := by decide +kernel
theorem subd11_1_883 : subd11_1 [6, -4] = true := by decide +kernel
theorem subd11_1_884 : subd11_1 [6, -3] = true := by decide +kernel
theorem subd11_1_885 : subd11_1 [6, -2] = true := by decide +kernel
theorem subd11_1_886 : subd11_1 [6, -1] = true := by decide +kernel
theorem subd11_1_887 : subd11_1 [6, 0] = true := by decide +kernel
theorem subd11_1_888 : subd11_1 [6, 1] = true := by decide +kernel
theorem subd11_1_889 : subd11_1 [6, 2] = true := by decide +kernel
theorem subd11_1_890 : subd11_1 [6, 3] = true := by decide +kernel
theorem subd11_1_891 : subd11_1 [7, -7] = true := by decide +kernel
theorem subd11_1_892 : subd11_1 [7, -6] = true := by decide +kernel
theorem subd11_1_893 : subd11_1 [7, -5] = true := by decide +kernel
theorem subd11_1_894 : subd11_1 [7, -4] = true := by decide +kernel
theorem subd11_1_895 : subd11_1 [7, -3] = true := by decide +kernel
theorem sbd11_1_27 : ∀ q ∈ blkd11_1_27, subd11_1 q = true := by
  unfold blkd11_1_27
  exact List.forall_mem_cons.2 ⟨subd11_1_864, List.forall_mem_cons.2 ⟨subd11_1_865, List.forall_mem_cons.2 ⟨subd11_1_866, List.forall_mem_cons.2 ⟨subd11_1_867, List.forall_mem_cons.2 ⟨subd11_1_868, List.forall_mem_cons.2 ⟨subd11_1_869, List.forall_mem_cons.2 ⟨subd11_1_870, List.forall_mem_cons.2 ⟨subd11_1_871, List.forall_mem_cons.2 ⟨subd11_1_872, List.forall_mem_cons.2 ⟨subd11_1_873, List.forall_mem_cons.2 ⟨subd11_1_874, List.forall_mem_cons.2 ⟨subd11_1_875, List.forall_mem_cons.2 ⟨subd11_1_876, List.forall_mem_cons.2 ⟨subd11_1_877, List.forall_mem_cons.2 ⟨subd11_1_878, List.forall_mem_cons.2 ⟨subd11_1_879, List.forall_mem_cons.2 ⟨subd11_1_880, List.forall_mem_cons.2 ⟨subd11_1_881, List.forall_mem_cons.2 ⟨subd11_1_882, List.forall_mem_cons.2 ⟨subd11_1_883, List.forall_mem_cons.2 ⟨subd11_1_884, List.forall_mem_cons.2 ⟨subd11_1_885, List.forall_mem_cons.2 ⟨subd11_1_886, List.forall_mem_cons.2 ⟨subd11_1_887, List.forall_mem_cons.2 ⟨subd11_1_888, List.forall_mem_cons.2 ⟨subd11_1_889, List.forall_mem_cons.2 ⟨subd11_1_890, List.forall_mem_cons.2 ⟨subd11_1_891, List.forall_mem_cons.2 ⟨subd11_1_892, List.forall_mem_cons.2 ⟨subd11_1_893, List.forall_mem_cons.2 ⟨subd11_1_894, List.forall_mem_cons.2 ⟨subd11_1_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_896 : subd11_1 [7, -2] = true := by decide +kernel
theorem subd11_1_897 : subd11_1 [7, -1] = true := by decide +kernel
theorem subd11_1_898 : subd11_1 [7, 0] = true := by decide +kernel
theorem subd11_1_899 : subd11_1 [7, 1] = true := by decide +kernel
theorem subd11_1_900 : subd11_1 [8] = true := by decide +kernel
theorem sbd11_1_28 : ∀ q ∈ blkd11_1_28, subd11_1 q = true := by
  unfold blkd11_1_28
  exact List.forall_mem_cons.2 ⟨subd11_1_896, List.forall_mem_cons.2 ⟨subd11_1_897, List.forall_mem_cons.2 ⟨subd11_1_898, List.forall_mem_cons.2 ⟨subd11_1_899, List.forall_mem_cons.2 ⟨subd11_1_900, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C077
