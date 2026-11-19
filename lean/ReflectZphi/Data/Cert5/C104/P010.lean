import ReflectZphi.Data.Cert5.C104.Base

namespace ReflectZphi.Data.Cert5.C104
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_800 : sub7 [3, -3, -10] = true := by decide +kernel
theorem sub7_801 : sub7 [3, -3, -9] = true := by decide +kernel
theorem sub7_802 : sub7 [3, -3, -8] = true := by decide +kernel
theorem sub7_803 : sub7 [3, -3, -7] = true := by decide +kernel
theorem sub7_804 : sub7 [3, -3, -6] = true := by decide +kernel
theorem sub7_805 : sub7 [3, -3, -5] = true := by decide +kernel
theorem sub7_806 : sub7 [3, -3, -4] = true := by decide +kernel
theorem sub7_807 : sub7 [3, -3, -3] = true := by decide +kernel
theorem sub7_808 : sub7 [3, -3, -2] = true := by decide +kernel
theorem sub7_809 : sub7 [3, -3, -1] = true := by decide +kernel
theorem sub7_810 : sub7 [3, -3, 0] = true := by decide +kernel
theorem sub7_811 : sub7 [3, -3, 1] = true := by decide +kernel
theorem sub7_812 : sub7 [3, -3, 2] = true := by decide +kernel
theorem sub7_813 : sub7 [3, -3, 3] = true := by decide +kernel
theorem sub7_814 : sub7 [3, -3, 4] = true := by decide +kernel
theorem sub7_815 : sub7 [3, -2, -10] = true := by decide +kernel
theorem sub7_816 : sub7 [3, -2, -9] = true := by decide +kernel
theorem sub7_817 : sub7 [3, -2, -8] = true := by decide +kernel
theorem sub7_818 : sub7 [3, -2, -7] = true := by decide +kernel
theorem sub7_819 : sub7 [3, -2, -6] = true := by decide +kernel
theorem sub7_820 : sub7 [3, -2, -5] = true := by decide +kernel
theorem sub7_821 : sub7 [3, -2, -4] = true := by decide +kernel
theorem sub7_822 : sub7 [3, -2, -3] = true := by decide +kernel
theorem sub7_823 : sub7 [3, -2, -2] = true := by decide +kernel
theorem sub7_824 : sub7 [3, -2, -1] = true := by decide +kernel
theorem sub7_825 : sub7 [3, -2, 0] = true := by decide +kernel
theorem sub7_826 : sub7 [3, -2, 1] = true := by decide +kernel
theorem sub7_827 : sub7 [3, -2, 2] = true := by decide +kernel
theorem sub7_828 : sub7 [3, -2, 3] = true := by decide +kernel
theorem sub7_829 : sub7 [3, -2, 4] = true := by decide +kernel
theorem sub7_830 : sub7 [3, -2, 5] = true := by decide +kernel
theorem sub7_831 : sub7 [3, -1, -10] = true := by decide +kernel
theorem sb7_25 : ∀ q ∈ blk7_25, sub7 q = true := by
  unfold blk7_25
  exact List.forall_mem_cons.2 ⟨sub7_800, List.forall_mem_cons.2 ⟨sub7_801, List.forall_mem_cons.2 ⟨sub7_802, List.forall_mem_cons.2 ⟨sub7_803, List.forall_mem_cons.2 ⟨sub7_804, List.forall_mem_cons.2 ⟨sub7_805, List.forall_mem_cons.2 ⟨sub7_806, List.forall_mem_cons.2 ⟨sub7_807, List.forall_mem_cons.2 ⟨sub7_808, List.forall_mem_cons.2 ⟨sub7_809, List.forall_mem_cons.2 ⟨sub7_810, List.forall_mem_cons.2 ⟨sub7_811, List.forall_mem_cons.2 ⟨sub7_812, List.forall_mem_cons.2 ⟨sub7_813, List.forall_mem_cons.2 ⟨sub7_814, List.forall_mem_cons.2 ⟨sub7_815, List.forall_mem_cons.2 ⟨sub7_816, List.forall_mem_cons.2 ⟨sub7_817, List.forall_mem_cons.2 ⟨sub7_818, List.forall_mem_cons.2 ⟨sub7_819, List.forall_mem_cons.2 ⟨sub7_820, List.forall_mem_cons.2 ⟨sub7_821, List.forall_mem_cons.2 ⟨sub7_822, List.forall_mem_cons.2 ⟨sub7_823, List.forall_mem_cons.2 ⟨sub7_824, List.forall_mem_cons.2 ⟨sub7_825, List.forall_mem_cons.2 ⟨sub7_826, List.forall_mem_cons.2 ⟨sub7_827, List.forall_mem_cons.2 ⟨sub7_828, List.forall_mem_cons.2 ⟨sub7_829, List.forall_mem_cons.2 ⟨sub7_830, List.forall_mem_cons.2 ⟨sub7_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_832 : sub7 [3, -1, -9] = true := by decide +kernel
theorem sub7_833 : sub7 [3, -1, -8] = true := by decide +kernel
theorem sub7_834 : sub7 [3, -1, -7] = true := by decide +kernel
theorem sub7_835 : sub7 [3, -1, -6] = true := by decide +kernel
theorem sub7_836 : sub7 [3, -1, -5] = true := by decide +kernel
theorem sub7_837 : sub7 [3, -1, -4] = true := by decide +kernel
theorem sub7_838 : sub7 [3, -1, -3] = true := by decide +kernel
theorem sub7_839 : sub7 [3, -1, -2] = true := by decide +kernel
theorem sub7_840 : sub7 [3, -1, -1] = true := by decide +kernel
theorem sub7_841 : sub7 [3, -1, 0] = true := by decide +kernel
theorem sub7_842 : sub7 [3, -1, 1] = true := by decide +kernel
theorem sub7_843 : sub7 [3, -1, 2] = true := by decide +kernel
theorem sub7_844 : sub7 [3, -1, 3] = true := by decide +kernel
theorem sub7_845 : sub7 [3, -1, 4] = true := by decide +kernel
theorem sub7_846 : sub7 [3, -1, 5] = true := by decide +kernel
theorem sub7_847 : sub7 [3, -1, 6] = true := by decide +kernel
theorem sub7_848 : sub7 [3, 0, -9] = true := by decide +kernel
theorem sub7_849 : sub7 [3, 0, -8] = true := by decide +kernel
theorem sub7_850 : sub7 [3, 0, -7] = true := by decide +kernel
theorem sub7_851 : sub7 [3, 0, -6] = true := by decide +kernel
theorem sub7_852 : sub7 [3, 0, -5] = true := by decide +kernel
theorem sub7_853 : sub7 [3, 0, -4] = true := by decide +kernel
theorem sub7_854 : sub7 [3, 0, -3] = true := by decide +kernel
theorem sub7_855 : sub7 [3, 0, -2] = true := by decide +kernel
theorem sub7_856 : sub7 [3, 0, -1] = true := by decide +kernel
theorem sub7_857 : sub7 [3, 0, 0] = true := by decide +kernel
theorem sub7_858 : sub7 [3, 0, 1] = true := by decide +kernel
theorem sub7_859 : sub7 [3, 0, 2] = true := by decide +kernel
theorem sub7_860 : sub7 [3, 0, 3] = true := by decide +kernel
theorem sub7_861 : sub7 [3, 0, 4] = true := by decide +kernel
theorem sub7_862 : sub7 [3, 0, 5] = true := by decide +kernel
theorem sub7_863 : sub7 [3, 0, 6] = true := by decide +kernel
theorem sb7_26 : ∀ q ∈ blk7_26, sub7 q = true := by
  unfold blk7_26
  exact List.forall_mem_cons.2 ⟨sub7_832, List.forall_mem_cons.2 ⟨sub7_833, List.forall_mem_cons.2 ⟨sub7_834, List.forall_mem_cons.2 ⟨sub7_835, List.forall_mem_cons.2 ⟨sub7_836, List.forall_mem_cons.2 ⟨sub7_837, List.forall_mem_cons.2 ⟨sub7_838, List.forall_mem_cons.2 ⟨sub7_839, List.forall_mem_cons.2 ⟨sub7_840, List.forall_mem_cons.2 ⟨sub7_841, List.forall_mem_cons.2 ⟨sub7_842, List.forall_mem_cons.2 ⟨sub7_843, List.forall_mem_cons.2 ⟨sub7_844, List.forall_mem_cons.2 ⟨sub7_845, List.forall_mem_cons.2 ⟨sub7_846, List.forall_mem_cons.2 ⟨sub7_847, List.forall_mem_cons.2 ⟨sub7_848, List.forall_mem_cons.2 ⟨sub7_849, List.forall_mem_cons.2 ⟨sub7_850, List.forall_mem_cons.2 ⟨sub7_851, List.forall_mem_cons.2 ⟨sub7_852, List.forall_mem_cons.2 ⟨sub7_853, List.forall_mem_cons.2 ⟨sub7_854, List.forall_mem_cons.2 ⟨sub7_855, List.forall_mem_cons.2 ⟨sub7_856, List.forall_mem_cons.2 ⟨sub7_857, List.forall_mem_cons.2 ⟨sub7_858, List.forall_mem_cons.2 ⟨sub7_859, List.forall_mem_cons.2 ⟨sub7_860, List.forall_mem_cons.2 ⟨sub7_861, List.forall_mem_cons.2 ⟨sub7_862, List.forall_mem_cons.2 ⟨sub7_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_864 : sub7 [3, 1, -8] = true := by decide +kernel
theorem sub7_865 : sub7 [3, 1, -7] = true := by decide +kernel
theorem sub7_866 : sub7 [3, 1, -6] = true := by decide +kernel
theorem sub7_867 : sub7 [3, 1, -5] = true := by decide +kernel
theorem sub7_868 : sub7 [3, 1, -4] = true := by decide +kernel
theorem sub7_869 : sub7 [3, 1, -3] = true := by decide +kernel
theorem sub7_870 : sub7 [3, 1, -2] = true := by decide +kernel
theorem sub7_871 : sub7 [3, 1, -1] = true := by decide +kernel
theorem sub7_872 : sub7 [3, 1, 0] = true := by decide +kernel
theorem sub7_873 : sub7 [3, 1, 1] = true := by decide +kernel
theorem sub7_874 : sub7 [3, 1, 2] = true := by decide +kernel
theorem sub7_875 : sub7 [3, 1, 3] = true := by decide +kernel
theorem sub7_876 : sub7 [3, 1, 4] = true := by decide +kernel
theorem sub7_877 : sub7 [3, 1, 5] = true := by decide +kernel
theorem sub7_878 : sub7 [3, 1, 6] = true := by decide +kernel
theorem sub7_879 : sub7 [3, 2] = true := by decide +kernel
theorem sub7_880 : sub7 [3, 3] = true := by decide +kernel
theorem sub7_881 : sub7 [4, -6] = true := by decide +kernel
theorem sub7_882 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_883 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_884 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_885 : sub7 [4, -2] = true := by decide +kernel
theorem sub7_886 : sub7 [4, -1] = true := by decide +kernel
theorem sub7_887 : sub7 [4, 0] = true := by decide +kernel
theorem sub7_888 : sub7 [4, 1] = true := by decide +kernel
theorem sub7_889 : sub7 [4, 2] = true := by decide +kernel
theorem sub7_890 : sub7 [5] = true := by decide +kernel
theorem sb7_27 : ∀ q ∈ blk7_27, sub7 q = true := by
  unfold blk7_27
  exact List.forall_mem_cons.2 ⟨sub7_864, List.forall_mem_cons.2 ⟨sub7_865, List.forall_mem_cons.2 ⟨sub7_866, List.forall_mem_cons.2 ⟨sub7_867, List.forall_mem_cons.2 ⟨sub7_868, List.forall_mem_cons.2 ⟨sub7_869, List.forall_mem_cons.2 ⟨sub7_870, List.forall_mem_cons.2 ⟨sub7_871, List.forall_mem_cons.2 ⟨sub7_872, List.forall_mem_cons.2 ⟨sub7_873, List.forall_mem_cons.2 ⟨sub7_874, List.forall_mem_cons.2 ⟨sub7_875, List.forall_mem_cons.2 ⟨sub7_876, List.forall_mem_cons.2 ⟨sub7_877, List.forall_mem_cons.2 ⟨sub7_878, List.forall_mem_cons.2 ⟨sub7_879, List.forall_mem_cons.2 ⟨sub7_880, List.forall_mem_cons.2 ⟨sub7_881, List.forall_mem_cons.2 ⟨sub7_882, List.forall_mem_cons.2 ⟨sub7_883, List.forall_mem_cons.2 ⟨sub7_884, List.forall_mem_cons.2 ⟨sub7_885, List.forall_mem_cons.2 ⟨sub7_886, List.forall_mem_cons.2 ⟨sub7_887, List.forall_mem_cons.2 ⟨sub7_888, List.forall_mem_cons.2 ⟨sub7_889, List.forall_mem_cons.2 ⟨sub7_890, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_0 : sub8 [-6] = true := by decide +kernel
theorem sub8_1 : sub8 [-5, -5] = true := by decide +kernel
theorem sub8_2 : sub8 [-5, -4] = true := by decide +kernel
theorem sub8_3 : sub8 [-5, -3] = true := by decide +kernel
theorem sub8_4 : sub8 [-5, -2] = true := by decide +kernel
theorem sub8_5 : sub8 [-5, -1] = true := by decide +kernel
theorem sub8_6 : sub8 [-5, 0] = true := by decide +kernel
theorem sub8_7 : sub8 [-5, 1] = true := by decide +kernel
theorem sub8_8 : sub8 [-5, 2] = true := by decide +kernel
theorem sub8_9 : sub8 [-4, -6] = true := by decide +kernel
theorem sub8_10 : sub8 [-4, -5] = true := by decide +kernel
theorem sub8_11 : sub8 [-4, -4] = true := by decide +kernel
theorem sub8_12 : sub8 [-4, -3] = true := by decide +kernel
theorem sub8_13 : sub8 [-4, -2] = true := by decide +kernel
theorem sub8_14 : sub8 [-4, -1] = true := by decide +kernel
theorem sub8_15 : sub8 [-4, 0] = true := by decide +kernel
theorem sub8_16 : sub8 [-4, 1] = true := by decide +kernel
theorem sub8_17 : sub8 [-4, 2] = true := by decide +kernel
theorem sub8_18 : sub8 [-4, 3] = true := by decide +kernel
theorem sub8_19 : sub8 [-4, 4] = true := by decide +kernel
theorem sub8_20 : sub8 [-3, -7] = true := by decide +kernel
theorem sub8_21 : sub8 [-3, -6] = true := by decide +kernel
theorem sub8_22 : sub8 [-3, -5] = true := by decide +kernel
theorem sub8_23 : sub8 [-3, -4] = true := by decide +kernel
theorem sub8_24 : sub8 [-3, -3] = true := by decide +kernel
theorem sub8_25 : sub8 [-3, -2, -7] = true := by decide +kernel
theorem sub8_26 : sub8 [-3, -2, -6] = true := by decide +kernel
theorem sub8_27 : sub8 [-3, -2, -5] = true := by decide +kernel
theorem sub8_28 : sub8 [-3, -2, -4] = true := by decide +kernel
theorem sub8_29 : sub8 [-3, -2, -3] = true := by decide +kernel
theorem sub8_30 : sub8 [-3, -2, -2] = true := by decide +kernel
theorem sub8_31 : sub8 [-3, -2, -1] = true := by decide +kernel
theorem sb8_0 : ∀ q ∈ blk8_0, sub8 q = true := by
  unfold blk8_0
  exact List.forall_mem_cons.2 ⟨sub8_0, List.forall_mem_cons.2 ⟨sub8_1, List.forall_mem_cons.2 ⟨sub8_2, List.forall_mem_cons.2 ⟨sub8_3, List.forall_mem_cons.2 ⟨sub8_4, List.forall_mem_cons.2 ⟨sub8_5, List.forall_mem_cons.2 ⟨sub8_6, List.forall_mem_cons.2 ⟨sub8_7, List.forall_mem_cons.2 ⟨sub8_8, List.forall_mem_cons.2 ⟨sub8_9, List.forall_mem_cons.2 ⟨sub8_10, List.forall_mem_cons.2 ⟨sub8_11, List.forall_mem_cons.2 ⟨sub8_12, List.forall_mem_cons.2 ⟨sub8_13, List.forall_mem_cons.2 ⟨sub8_14, List.forall_mem_cons.2 ⟨sub8_15, List.forall_mem_cons.2 ⟨sub8_16, List.forall_mem_cons.2 ⟨sub8_17, List.forall_mem_cons.2 ⟨sub8_18, List.forall_mem_cons.2 ⟨sub8_19, List.forall_mem_cons.2 ⟨sub8_20, List.forall_mem_cons.2 ⟨sub8_21, List.forall_mem_cons.2 ⟨sub8_22, List.forall_mem_cons.2 ⟨sub8_23, List.forall_mem_cons.2 ⟨sub8_24, List.forall_mem_cons.2 ⟨sub8_25, List.forall_mem_cons.2 ⟨sub8_26, List.forall_mem_cons.2 ⟨sub8_27, List.forall_mem_cons.2 ⟨sub8_28, List.forall_mem_cons.2 ⟨sub8_29, List.forall_mem_cons.2 ⟨sub8_30, List.forall_mem_cons.2 ⟨sub8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_32 : sub8 [-3, -2, 0] = true := by decide +kernel
theorem sub8_33 : sub8 [-3, -2, 1] = true := by decide +kernel
theorem sub8_34 : sub8 [-3, -2, 2] = true := by decide +kernel
theorem sub8_35 : sub8 [-3, -2, 3] = true := by decide +kernel
theorem sub8_36 : sub8 [-3, -2, 4] = true := by decide +kernel
theorem sub8_37 : sub8 [-3, -2, 5] = true := by decide +kernel
theorem sub8_38 : sub8 [-3, -2, 6] = true := by decide +kernel
theorem sub8_39 : sub8 [-3, -1, -7] = true := by decide +kernel
theorem sub8_40 : sub8 [-3, -1, -6] = true := by decide +kernel
theorem sub8_41 : sub8 [-3, -1, -5] = true := by decide +kernel
theorem sub8_42 : sub8 [-3, -1, -4] = true := by decide +kernel
theorem sub8_43 : sub8 [-3, -1, -3] = true := by decide +kernel
theorem sub8_44 : sub8 [-3, -1, -2] = true := by decide +kernel
theorem sub8_45 : sub8 [-3, -1, -1] = true := by decide +kernel
theorem sub8_46 : sub8 [-3, -1, 0] = true := by decide +kernel
theorem sub8_47 : sub8 [-3, -1, 1] = true := by decide +kernel
theorem sub8_48 : sub8 [-3, -1, 2] = true := by decide +kernel
theorem sub8_49 : sub8 [-3, -1, 3] = true := by decide +kernel
theorem sub8_50 : sub8 [-3, -1, 4] = true := by decide +kernel
theorem sub8_51 : sub8 [-3, -1, 5] = true := by decide +kernel
theorem sub8_52 : sub8 [-3, -1, 6] = true := by decide +kernel
theorem sub8_53 : sub8 [-3, 0, -8] = true := by decide +kernel
theorem sub8_54 : sub8 [-3, 0, -7] = true := by decide +kernel
theorem sub8_55 : sub8 [-3, 0, -6] = true := by decide +kernel
theorem sub8_56 : sub8 [-3, 0, -5] = true := by decide +kernel
theorem sub8_57 : sub8 [-3, 0, -4] = true := by decide +kernel
theorem sub8_58 : sub8 [-3, 0, -3] = true := by decide +kernel
theorem sub8_59 : sub8 [-3, 0, -2] = true := by decide +kernel
theorem sub8_60 : sub8 [-3, 0, -1] = true := by decide +kernel
theorem sub8_61 : sub8 [-3, 0, 0] = true := by decide +kernel
theorem sub8_62 : sub8 [-3, 0, 1] = true := by decide +kernel
theorem sub8_63 : sub8 [-3, 0, 2] = true := by decide +kernel
theorem sb8_1 : ∀ q ∈ blk8_1, sub8 q = true := by
  unfold blk8_1
  exact List.forall_mem_cons.2 ⟨sub8_32, List.forall_mem_cons.2 ⟨sub8_33, List.forall_mem_cons.2 ⟨sub8_34, List.forall_mem_cons.2 ⟨sub8_35, List.forall_mem_cons.2 ⟨sub8_36, List.forall_mem_cons.2 ⟨sub8_37, List.forall_mem_cons.2 ⟨sub8_38, List.forall_mem_cons.2 ⟨sub8_39, List.forall_mem_cons.2 ⟨sub8_40, List.forall_mem_cons.2 ⟨sub8_41, List.forall_mem_cons.2 ⟨sub8_42, List.forall_mem_cons.2 ⟨sub8_43, List.forall_mem_cons.2 ⟨sub8_44, List.forall_mem_cons.2 ⟨sub8_45, List.forall_mem_cons.2 ⟨sub8_46, List.forall_mem_cons.2 ⟨sub8_47, List.forall_mem_cons.2 ⟨sub8_48, List.forall_mem_cons.2 ⟨sub8_49, List.forall_mem_cons.2 ⟨sub8_50, List.forall_mem_cons.2 ⟨sub8_51, List.forall_mem_cons.2 ⟨sub8_52, List.forall_mem_cons.2 ⟨sub8_53, List.forall_mem_cons.2 ⟨sub8_54, List.forall_mem_cons.2 ⟨sub8_55, List.forall_mem_cons.2 ⟨sub8_56, List.forall_mem_cons.2 ⟨sub8_57, List.forall_mem_cons.2 ⟨sub8_58, List.forall_mem_cons.2 ⟨sub8_59, List.forall_mem_cons.2 ⟨sub8_60, List.forall_mem_cons.2 ⟨sub8_61, List.forall_mem_cons.2 ⟨sub8_62, List.forall_mem_cons.2 ⟨sub8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_64 : sub8 [-3, 0, 3] = true := by decide +kernel
theorem sub8_65 : sub8 [-3, 0, 4] = true := by decide +kernel
theorem sub8_66 : sub8 [-3, 0, 5] = true := by decide +kernel
theorem sub8_67 : sub8 [-3, 0, 6] = true := by decide +kernel
theorem sub8_68 : sub8 [-3, 1, -8] = true := by decide +kernel
theorem sub8_69 : sub8 [-3, 1, -7] = true := by decide +kernel
theorem sub8_70 : sub8 [-3, 1, -6] = true := by decide +kernel
theorem sub8_71 : sub8 [-3, 1, -5] = true := by decide +kernel
theorem sub8_72 : sub8 [-3, 1, -4] = true := by decide +kernel
theorem sub8_73 : sub8 [-3, 1, -3] = true := by decide +kernel
theorem sub8_74 : sub8 [-3, 1, -2] = true := by decide +kernel
theorem sub8_75 : sub8 [-3, 1, -1] = true := by decide +kernel
theorem sub8_76 : sub8 [-3, 1, 0] = true := by decide +kernel
theorem sub8_77 : sub8 [-3, 1, 1] = true := by decide +kernel
theorem sub8_78 : sub8 [-3, 1, 2] = true := by decide +kernel
theorem sub8_79 : sub8 [-3, 1, 3] = true := by decide +kernel
theorem sub8_80 : sub8 [-3, 1, 4] = true := by decide +kernel
theorem sub8_81 : sub8 [-3, 1, 5] = true := by decide +kernel
theorem sub8_82 : sub8 [-3, 2] = true := by decide +kernel
theorem sub8_83 : sub8 [-3, 3] = true := by decide +kernel
theorem sub8_84 : sub8 [-3, 4] = true := by decide +kernel
theorem sub8_85 : sub8 [-3, 5] = true := by decide +kernel
theorem sub8_86 : sub8 [-2, -7] = true := by decide +kernel
theorem sub8_87 : sub8 [-2, -6] = true := by decide +kernel
theorem sub8_88 : sub8 [-2, -5] = true := by decide +kernel
theorem sub8_89 : sub8 [-2, -4] = true := by decide +kernel
theorem sub8_90 : sub8 [-2, -3, -7] = true := by decide +kernel
theorem sub8_91 : sub8 [-2, -3, -6] = true := by decide +kernel
theorem sub8_92 : sub8 [-2, -3, -5] = true := by decide +kernel
theorem sub8_93 : sub8 [-2, -3, -4] = true := by decide +kernel
theorem sub8_94 : sub8 [-2, -3, -3] = true := by decide +kernel
theorem sub8_95 : sub8 [-2, -3, -2] = true := by decide +kernel
theorem sb8_2 : ∀ q ∈ blk8_2, sub8 q = true := by
  unfold blk8_2
  exact List.forall_mem_cons.2 ⟨sub8_64, List.forall_mem_cons.2 ⟨sub8_65, List.forall_mem_cons.2 ⟨sub8_66, List.forall_mem_cons.2 ⟨sub8_67, List.forall_mem_cons.2 ⟨sub8_68, List.forall_mem_cons.2 ⟨sub8_69, List.forall_mem_cons.2 ⟨sub8_70, List.forall_mem_cons.2 ⟨sub8_71, List.forall_mem_cons.2 ⟨sub8_72, List.forall_mem_cons.2 ⟨sub8_73, List.forall_mem_cons.2 ⟨sub8_74, List.forall_mem_cons.2 ⟨sub8_75, List.forall_mem_cons.2 ⟨sub8_76, List.forall_mem_cons.2 ⟨sub8_77, List.forall_mem_cons.2 ⟨sub8_78, List.forall_mem_cons.2 ⟨sub8_79, List.forall_mem_cons.2 ⟨sub8_80, List.forall_mem_cons.2 ⟨sub8_81, List.forall_mem_cons.2 ⟨sub8_82, List.forall_mem_cons.2 ⟨sub8_83, List.forall_mem_cons.2 ⟨sub8_84, List.forall_mem_cons.2 ⟨sub8_85, List.forall_mem_cons.2 ⟨sub8_86, List.forall_mem_cons.2 ⟨sub8_87, List.forall_mem_cons.2 ⟨sub8_88, List.forall_mem_cons.2 ⟨sub8_89, List.forall_mem_cons.2 ⟨sub8_90, List.forall_mem_cons.2 ⟨sub8_91, List.forall_mem_cons.2 ⟨sub8_92, List.forall_mem_cons.2 ⟨sub8_93, List.forall_mem_cons.2 ⟨sub8_94, List.forall_mem_cons.2 ⟨sub8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_96 : sub8 [-2, -3, -1] = true := by decide +kernel
theorem sub8_97 : sub8 [-2, -3, 0] = true := by decide +kernel
theorem sub8_98 : sub8 [-2, -3, 1] = true := by decide +kernel
theorem sub8_99 : sub8 [-2, -3, 2] = true := by decide +kernel
theorem sub8_100 : sub8 [-2, -3, 3] = true := by decide +kernel
theorem sub8_101 : sub8 [-2, -3, 4] = true := by decide +kernel
theorem sub8_102 : sub8 [-2, -3, 5] = true := by decide +kernel
theorem sub8_103 : sub8 [-2, -3, 6] = true := by decide +kernel
theorem sub8_104 : sub8 [-2, -2, -7] = true := by decide +kernel
theorem sub8_105 : sub8 [-2, -2, -6] = true := by decide +kernel
theorem sub8_106 : sub8 [-2, -2, -5] = true := by decide +kernel
theorem sub8_107 : sub8 [-2, -2, -4] = true := by decide +kernel
theorem sub8_108 : sub8 [-2, -2, -3] = true := by decide +kernel
theorem sub8_109 : sub8 [-2, -2, -2] = true := by decide +kernel
theorem sub8_110 : sub8 [-2, -2, -1] = true := by decide +kernel
theorem sub8_111 : sub8 [-2, -2, 0] = true := by decide +kernel
theorem sub8_112 : sub8 [-2, -2, 1] = true := by decide +kernel
theorem sub8_113 : sub8 [-2, -2, 2] = true := by decide +kernel
theorem sub8_114 : sub8 [-2, -2, 3] = true := by decide +kernel
theorem sub8_115 : sub8 [-2, -2, 4] = true := by decide +kernel
theorem sub8_116 : sub8 [-2, -2, 5] = true := by decide +kernel
theorem sub8_117 : sub8 [-2, -2, 6] = true := by decide +kernel
theorem sub8_118 : sub8 [-2, -2, 7] = true := by decide +kernel
theorem sub8_119 : sub8 [-2, -1, -8] = true := by decide +kernel
theorem sub8_120 : sub8 [-2, -1, -7] = true := by decide +kernel
theorem sub8_121 : sub8 [-2, -1, -6] = true := by decide +kernel
theorem sub8_122 : sub8 [-2, -1, -5] = true := by decide +kernel
theorem sub8_123 : sub8 [-2, -1, -4] = true := by decide +kernel
theorem sub8_124 : sub8 [-2, -1, -3] = true := by decide +kernel
theorem sub8_125 : sub8 [-2, -1, -2] = true := by decide +kernel
theorem sub8_126 : sub8 [-2, -1, -1] = true := by decide +kernel
theorem sub8_127 : sub8 [-2, -1, 0] = true := by decide +kernel
theorem sb8_3 : ∀ q ∈ blk8_3, sub8 q = true := by
  unfold blk8_3
  exact List.forall_mem_cons.2 ⟨sub8_96, List.forall_mem_cons.2 ⟨sub8_97, List.forall_mem_cons.2 ⟨sub8_98, List.forall_mem_cons.2 ⟨sub8_99, List.forall_mem_cons.2 ⟨sub8_100, List.forall_mem_cons.2 ⟨sub8_101, List.forall_mem_cons.2 ⟨sub8_102, List.forall_mem_cons.2 ⟨sub8_103, List.forall_mem_cons.2 ⟨sub8_104, List.forall_mem_cons.2 ⟨sub8_105, List.forall_mem_cons.2 ⟨sub8_106, List.forall_mem_cons.2 ⟨sub8_107, List.forall_mem_cons.2 ⟨sub8_108, List.forall_mem_cons.2 ⟨sub8_109, List.forall_mem_cons.2 ⟨sub8_110, List.forall_mem_cons.2 ⟨sub8_111, List.forall_mem_cons.2 ⟨sub8_112, List.forall_mem_cons.2 ⟨sub8_113, List.forall_mem_cons.2 ⟨sub8_114, List.forall_mem_cons.2 ⟨sub8_115, List.forall_mem_cons.2 ⟨sub8_116, List.forall_mem_cons.2 ⟨sub8_117, List.forall_mem_cons.2 ⟨sub8_118, List.forall_mem_cons.2 ⟨sub8_119, List.forall_mem_cons.2 ⟨sub8_120, List.forall_mem_cons.2 ⟨sub8_121, List.forall_mem_cons.2 ⟨sub8_122, List.forall_mem_cons.2 ⟨sub8_123, List.forall_mem_cons.2 ⟨sub8_124, List.forall_mem_cons.2 ⟨sub8_125, List.forall_mem_cons.2 ⟨sub8_126, List.forall_mem_cons.2 ⟨sub8_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_128 : sub8 [-2, -1, 1] = true := by decide +kernel
theorem sub8_129 : sub8 [-2, -1, 2] = true := by decide +kernel
theorem sub8_130 : sub8 [-2, -1, 3] = true := by decide +kernel
theorem sub8_131 : sub8 [-2, -1, 4] = true := by decide +kernel
theorem sub8_132 : sub8 [-2, -1, 5] = true := by decide +kernel
theorem sub8_133 : sub8 [-2, -1, 6] = true := by decide +kernel
theorem sub8_134 : sub8 [-2, -1, 7] = true := by decide +kernel
theorem sub8_135 : sub8 [-2, 0, -8] = true := by decide +kernel
theorem sub8_136 : sub8 [-2, 0, -7] = true := by decide +kernel
theorem sub8_137 : sub8 [-2, 0, -6] = true := by decide +kernel
theorem sub8_138 : sub8 [-2, 0, -5] = true := by decide +kernel
theorem sub8_139 : sub8 [-2, 0, -4] = true := by decide +kernel
theorem sub8_140 : sub8 [-2, 0, -3] = true := by decide +kernel
theorem sub8_141 : sub8 [-2, 0, -2] = true := by decide +kernel
theorem sub8_142 : sub8 [-2, 0, -1] = true := by decide +kernel
theorem sub8_143 : sub8 [-2, 0, 0] = true := by decide +kernel
theorem sub8_144 : sub8 [-2, 0, 1] = true := by decide +kernel
theorem sub8_145 : sub8 [-2, 0, 2] = true := by decide +kernel
theorem sub8_146 : sub8 [-2, 0, 3] = true := by decide +kernel
theorem sub8_147 : sub8 [-2, 0, 4] = true := by decide +kernel
theorem sub8_148 : sub8 [-2, 0, 5] = true := by decide +kernel
theorem sub8_149 : sub8 [-2, 0, 6] = true := by decide +kernel
theorem sub8_150 : sub8 [-2, 1, -8] = true := by decide +kernel
theorem sub8_151 : sub8 [-2, 1, -7] = true := by decide +kernel
theorem sub8_152 : sub8 [-2, 1, -6] = true := by decide +kernel
theorem sub8_153 : sub8 [-2, 1, -5] = true := by decide +kernel
theorem sub8_154 : sub8 [-2, 1, -4] = true := by decide +kernel
theorem sub8_155 : sub8 [-2, 1, -3] = true := by decide +kernel
theorem sub8_156 : sub8 [-2, 1, -2] = true := by decide +kernel
theorem sub8_157 : sub8 [-2, 1, -1] = true := by decide +kernel
theorem sub8_158 : sub8 [-2, 1, 0] = true := by decide +kernel
theorem sub8_159 : sub8 [-2, 1, 1] = true := by decide +kernel
theorem sb8_4 : ∀ q ∈ blk8_4, sub8 q = true := by
  unfold blk8_4
  exact List.forall_mem_cons.2 ⟨sub8_128, List.forall_mem_cons.2 ⟨sub8_129, List.forall_mem_cons.2 ⟨sub8_130, List.forall_mem_cons.2 ⟨sub8_131, List.forall_mem_cons.2 ⟨sub8_132, List.forall_mem_cons.2 ⟨sub8_133, List.forall_mem_cons.2 ⟨sub8_134, List.forall_mem_cons.2 ⟨sub8_135, List.forall_mem_cons.2 ⟨sub8_136, List.forall_mem_cons.2 ⟨sub8_137, List.forall_mem_cons.2 ⟨sub8_138, List.forall_mem_cons.2 ⟨sub8_139, List.forall_mem_cons.2 ⟨sub8_140, List.forall_mem_cons.2 ⟨sub8_141, List.forall_mem_cons.2 ⟨sub8_142, List.forall_mem_cons.2 ⟨sub8_143, List.forall_mem_cons.2 ⟨sub8_144, List.forall_mem_cons.2 ⟨sub8_145, List.forall_mem_cons.2 ⟨sub8_146, List.forall_mem_cons.2 ⟨sub8_147, List.forall_mem_cons.2 ⟨sub8_148, List.forall_mem_cons.2 ⟨sub8_149, List.forall_mem_cons.2 ⟨sub8_150, List.forall_mem_cons.2 ⟨sub8_151, List.forall_mem_cons.2 ⟨sub8_152, List.forall_mem_cons.2 ⟨sub8_153, List.forall_mem_cons.2 ⟨sub8_154, List.forall_mem_cons.2 ⟨sub8_155, List.forall_mem_cons.2 ⟨sub8_156, List.forall_mem_cons.2 ⟨sub8_157, List.forall_mem_cons.2 ⟨sub8_158, List.forall_mem_cons.2 ⟨sub8_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_160 : sub8 [-2, 1, 2] = true := by decide +kernel
theorem sub8_161 : sub8 [-2, 1, 3] = true := by decide +kernel
theorem sub8_162 : sub8 [-2, 1, 4] = true := by decide +kernel
theorem sub8_163 : sub8 [-2, 1, 5] = true := by decide +kernel
theorem sub8_164 : sub8 [-2, 1, 6] = true := by decide +kernel
theorem sub8_165 : sub8 [-2, 2, -8] = true := by decide +kernel
theorem sub8_166 : sub8 [-2, 2, -7] = true := by decide +kernel
theorem sub8_167 : sub8 [-2, 2, -6] = true := by decide +kernel
theorem sub8_168 : sub8 [-2, 2, -5] = true := by decide +kernel
theorem sub8_169 : sub8 [-2, 2, -4] = true := by decide +kernel
theorem sub8_170 : sub8 [-2, 2, -3] = true := by decide +kernel
theorem sub8_171 : sub8 [-2, 2, -2] = true := by decide +kernel
theorem sub8_172 : sub8 [-2, 2, -1] = true := by decide +kernel
theorem sub8_173 : sub8 [-2, 2, 0] = true := by decide +kernel
theorem sub8_174 : sub8 [-2, 2, 1] = true := by decide +kernel
theorem sub8_175 : sub8 [-2, 2, 2] = true := by decide +kernel
theorem sub8_176 : sub8 [-2, 2, 3] = true := by decide +kernel
theorem sub8_177 : sub8 [-2, 2, 4] = true := by decide +kernel
theorem sub8_178 : sub8 [-2, 2, 5] = true := by decide +kernel
theorem sub8_179 : sub8 [-2, 2, 6] = true := by decide +kernel
theorem sub8_180 : sub8 [-2, 3] = true := by decide +kernel
theorem sub8_181 : sub8 [-2, 4] = true := by decide +kernel
theorem sub8_182 : sub8 [-2, 5] = true := by decide +kernel
theorem sub8_183 : sub8 [-1, -7] = true := by decide +kernel
theorem sub8_184 : sub8 [-1, -6] = true := by decide +kernel
theorem sub8_185 : sub8 [-1, -5] = true := by decide +kernel
theorem sub8_186 : sub8 [-1, -4] = true := by decide +kernel
theorem sub8_187 : sub8 [-1, -3, -7] = true := by decide +kernel
theorem sub8_188 : sub8 [-1, -3, -6] = true := by decide +kernel
theorem sub8_189 : sub8 [-1, -3, -5] = true := by decide +kernel
theorem sub8_190 : sub8 [-1, -3, -4] = true := by decide +kernel
theorem sub8_191 : sub8 [-1, -3, -3] = true := by decide +kernel
theorem sb8_5 : ∀ q ∈ blk8_5, sub8 q = true := by
  unfold blk8_5
  exact List.forall_mem_cons.2 ⟨sub8_160, List.forall_mem_cons.2 ⟨sub8_161, List.forall_mem_cons.2 ⟨sub8_162, List.forall_mem_cons.2 ⟨sub8_163, List.forall_mem_cons.2 ⟨sub8_164, List.forall_mem_cons.2 ⟨sub8_165, List.forall_mem_cons.2 ⟨sub8_166, List.forall_mem_cons.2 ⟨sub8_167, List.forall_mem_cons.2 ⟨sub8_168, List.forall_mem_cons.2 ⟨sub8_169, List.forall_mem_cons.2 ⟨sub8_170, List.forall_mem_cons.2 ⟨sub8_171, List.forall_mem_cons.2 ⟨sub8_172, List.forall_mem_cons.2 ⟨sub8_173, List.forall_mem_cons.2 ⟨sub8_174, List.forall_mem_cons.2 ⟨sub8_175, List.forall_mem_cons.2 ⟨sub8_176, List.forall_mem_cons.2 ⟨sub8_177, List.forall_mem_cons.2 ⟨sub8_178, List.forall_mem_cons.2 ⟨sub8_179, List.forall_mem_cons.2 ⟨sub8_180, List.forall_mem_cons.2 ⟨sub8_181, List.forall_mem_cons.2 ⟨sub8_182, List.forall_mem_cons.2 ⟨sub8_183, List.forall_mem_cons.2 ⟨sub8_184, List.forall_mem_cons.2 ⟨sub8_185, List.forall_mem_cons.2 ⟨sub8_186, List.forall_mem_cons.2 ⟨sub8_187, List.forall_mem_cons.2 ⟨sub8_188, List.forall_mem_cons.2 ⟨sub8_189, List.forall_mem_cons.2 ⟨sub8_190, List.forall_mem_cons.2 ⟨sub8_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_192 : sub8 [-1, -3, -2] = true := by decide +kernel
theorem sub8_193 : sub8 [-1, -3, -1] = true := by decide +kernel
theorem sub8_194 : sub8 [-1, -3, 0] = true := by decide +kernel
theorem sub8_195 : sub8 [-1, -3, 1] = true := by decide +kernel
theorem sub8_196 : sub8 [-1, -3, 2] = true := by decide +kernel
theorem sub8_197 : sub8 [-1, -3, 3] = true := by decide +kernel
theorem sub8_198 : sub8 [-1, -3, 4] = true := by decide +kernel
theorem sub8_199 : sub8 [-1, -3, 5] = true := by decide +kernel
theorem sub8_200 : sub8 [-1, -3, 6] = true := by decide +kernel
theorem sub8_201 : sub8 [-1, -3, 7] = true := by decide +kernel
theorem sub8_202 : sub8 [-1, -2, -8] = true := by decide +kernel
theorem sub8_203 : sub8 [-1, -2, -7] = true := by decide +kernel
theorem sub8_204 : sub8 [-1, -2, -6] = true := by decide +kernel
theorem sub8_205 : sub8 [-1, -2, -5] = true := by decide +kernel
theorem sub8_206 : sub8 [-1, -2, -4] = true := by decide +kernel
theorem sub8_207 : sub8 [-1, -2, -3] = true := by decide +kernel
theorem sub8_208 : sub8 [-1, -2, -2] = true := by decide +kernel
theorem sub8_209 : sub8 [-1, -2, -1] = true := by decide +kernel
theorem sub8_210 : sub8 [-1, -2, 0] = true := by decide +kernel
theorem sub8_211 : sub8 [-1, -2, 1] = true := by decide +kernel
theorem sub8_212 : sub8 [-1, -2, 2] = true := by decide +kernel
theorem sub8_213 : sub8 [-1, -2, 3] = true := by decide +kernel
theorem sub8_214 : sub8 [-1, -2, 4] = true := by decide +kernel
theorem sub8_215 : sub8 [-1, -2, 5] = true := by decide +kernel
theorem sub8_216 : sub8 [-1, -2, 6] = true := by decide +kernel
theorem sub8_217 : sub8 [-1, -2, 7] = true := by decide +kernel
theorem sub8_218 : sub8 [-1, -1, -8] = true := by decide +kernel
theorem sub8_219 : sub8 [-1, -1, -7] = true := by decide +kernel
theorem sub8_220 : sub8 [-1, -1, -6] = true := by decide +kernel
theorem sub8_221 : sub8 [-1, -1, -5] = true := by decide +kernel
theorem sub8_222 : sub8 [-1, -1, -4] = true := by decide +kernel
theorem sub8_223 : sub8 [-1, -1, -3] = true := by decide +kernel
theorem sb8_6 : ∀ q ∈ blk8_6, sub8 q = true := by
  unfold blk8_6
  exact List.forall_mem_cons.2 ⟨sub8_192, List.forall_mem_cons.2 ⟨sub8_193, List.forall_mem_cons.2 ⟨sub8_194, List.forall_mem_cons.2 ⟨sub8_195, List.forall_mem_cons.2 ⟨sub8_196, List.forall_mem_cons.2 ⟨sub8_197, List.forall_mem_cons.2 ⟨sub8_198, List.forall_mem_cons.2 ⟨sub8_199, List.forall_mem_cons.2 ⟨sub8_200, List.forall_mem_cons.2 ⟨sub8_201, List.forall_mem_cons.2 ⟨sub8_202, List.forall_mem_cons.2 ⟨sub8_203, List.forall_mem_cons.2 ⟨sub8_204, List.forall_mem_cons.2 ⟨sub8_205, List.forall_mem_cons.2 ⟨sub8_206, List.forall_mem_cons.2 ⟨sub8_207, List.forall_mem_cons.2 ⟨sub8_208, List.forall_mem_cons.2 ⟨sub8_209, List.forall_mem_cons.2 ⟨sub8_210, List.forall_mem_cons.2 ⟨sub8_211, List.forall_mem_cons.2 ⟨sub8_212, List.forall_mem_cons.2 ⟨sub8_213, List.forall_mem_cons.2 ⟨sub8_214, List.forall_mem_cons.2 ⟨sub8_215, List.forall_mem_cons.2 ⟨sub8_216, List.forall_mem_cons.2 ⟨sub8_217, List.forall_mem_cons.2 ⟨sub8_218, List.forall_mem_cons.2 ⟨sub8_219, List.forall_mem_cons.2 ⟨sub8_220, List.forall_mem_cons.2 ⟨sub8_221, List.forall_mem_cons.2 ⟨sub8_222, List.forall_mem_cons.2 ⟨sub8_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_224 : sub8 [-1, -1, -2] = true := by decide +kernel
theorem sub8_225 : sub8 [-1, -1, -1] = true := by decide +kernel
theorem sub8_226 : sub8 [-1, -1, 0] = true := by decide +kernel
theorem sub8_227 : sub8 [-1, -1, 1] = true := by decide +kernel
theorem sub8_228 : sub8 [-1, -1, 2] = true := by decide +kernel
theorem sub8_229 : sub8 [-1, -1, 3] = true := by decide +kernel
theorem sub8_230 : sub8 [-1, -1, 4] = true := by decide +kernel
theorem sub8_231 : sub8 [-1, -1, 5] = true := by decide +kernel
theorem sub8_232 : sub8 [-1, -1, 6] = true := by decide +kernel
theorem sub8_233 : sub8 [-1, -1, 7] = true := by decide +kernel
theorem sub8_234 : sub8 [-1, 0, -8] = true := by decide +kernel
theorem sub8_235 : sub8 [-1, 0, -7] = true := by decide +kernel
theorem sub8_236 : sub8 [-1, 0, -6] = true := by decide +kernel
theorem sub8_237 : sub8 [-1, 0, -5] = true := by decide +kernel
theorem sub8_238 : sub8 [-1, 0, -4] = true := by decide +kernel
theorem sub8_239 : sub8 [-1, 0, -3] = true := by decide +kernel
theorem sub8_240 : sub8 [-1, 0, -2] = true := by decide +kernel
theorem sub8_241 : sub8 [-1, 0, -1] = true := by decide +kernel
theorem sub8_242 : sub8 [-1, 0, 0] = true := by decide +kernel
theorem sub8_243 : sub8 [-1, 0, 1] = true := by decide +kernel
theorem sub8_244 : sub8 [-1, 0, 2] = true := by decide +kernel
theorem sub8_245 : sub8 [-1, 0, 3] = true := by decide +kernel
theorem sub8_246 : sub8 [-1, 0, 4] = true := by decide +kernel
theorem sub8_247 : sub8 [-1, 0, 5] = true := by decide +kernel
theorem sub8_248 : sub8 [-1, 0, 6] = true := by decide +kernel
theorem sub8_249 : sub8 [-1, 0, 7] = true := by decide +kernel
theorem sub8_250 : sub8 [-1, 1, -8] = true := by decide +kernel
theorem sub8_251 : sub8 [-1, 1, -7] = true := by decide +kernel
theorem sub8_252 : sub8 [-1, 1, -6] = true := by decide +kernel
theorem sub8_253 : sub8 [-1, 1, -5] = true := by decide +kernel
theorem sub8_254 : sub8 [-1, 1, -4] = true := by decide +kernel
theorem sub8_255 : sub8 [-1, 1, -3] = true := by decide +kernel
theorem sb8_7 : ∀ q ∈ blk8_7, sub8 q = true := by
  unfold blk8_7
  exact List.forall_mem_cons.2 ⟨sub8_224, List.forall_mem_cons.2 ⟨sub8_225, List.forall_mem_cons.2 ⟨sub8_226, List.forall_mem_cons.2 ⟨sub8_227, List.forall_mem_cons.2 ⟨sub8_228, List.forall_mem_cons.2 ⟨sub8_229, List.forall_mem_cons.2 ⟨sub8_230, List.forall_mem_cons.2 ⟨sub8_231, List.forall_mem_cons.2 ⟨sub8_232, List.forall_mem_cons.2 ⟨sub8_233, List.forall_mem_cons.2 ⟨sub8_234, List.forall_mem_cons.2 ⟨sub8_235, List.forall_mem_cons.2 ⟨sub8_236, List.forall_mem_cons.2 ⟨sub8_237, List.forall_mem_cons.2 ⟨sub8_238, List.forall_mem_cons.2 ⟨sub8_239, List.forall_mem_cons.2 ⟨sub8_240, List.forall_mem_cons.2 ⟨sub8_241, List.forall_mem_cons.2 ⟨sub8_242, List.forall_mem_cons.2 ⟨sub8_243, List.forall_mem_cons.2 ⟨sub8_244, List.forall_mem_cons.2 ⟨sub8_245, List.forall_mem_cons.2 ⟨sub8_246, List.forall_mem_cons.2 ⟨sub8_247, List.forall_mem_cons.2 ⟨sub8_248, List.forall_mem_cons.2 ⟨sub8_249, List.forall_mem_cons.2 ⟨sub8_250, List.forall_mem_cons.2 ⟨sub8_251, List.forall_mem_cons.2 ⟨sub8_252, List.forall_mem_cons.2 ⟨sub8_253, List.forall_mem_cons.2 ⟨sub8_254, List.forall_mem_cons.2 ⟨sub8_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C104
