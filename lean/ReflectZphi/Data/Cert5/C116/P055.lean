import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_1_832 : subd11_1 [3, 0, 0] = true := by decide +kernel
theorem subd11_1_833 : subd11_1 [3, 0, 1] = true := by decide +kernel
theorem subd11_1_834 : subd11_1 [3, 0, 2] = true := by decide +kernel
theorem subd11_1_835 : subd11_1 [3, 0, 3] = true := by decide +kernel
theorem subd11_1_836 : subd11_1 [3, 0, 4] = true := by decide +kernel
theorem subd11_1_837 : subd11_1 [3, 0, 5] = true := by decide +kernel
theorem subd11_1_838 : subd11_1 [3, 0, 6] = true := by decide +kernel
theorem subd11_1_839 : subd11_1 [3, 0, 7] = true := by decide +kernel
theorem subd11_1_840 : subd11_1 [3, 0, 8] = true := by decide +kernel
theorem subd11_1_841 : subd11_1 [3, 1] = true := by decide +kernel
theorem subd11_1_842 : subd11_1 [3, 2] = true := by decide +kernel
theorem subd11_1_843 : subd11_1 [4, -6] = true := by decide +kernel
theorem subd11_1_844 : subd11_1 [4, -5] = true := by decide +kernel
theorem subd11_1_845 : subd11_1 [4, -4] = true := by decide +kernel
theorem subd11_1_846 : subd11_1 [4, -3] = true := by decide +kernel
theorem subd11_1_847 : subd11_1 [4, -2] = true := by decide +kernel
theorem subd11_1_848 : subd11_1 [4, -1] = true := by decide +kernel
theorem subd11_1_849 : subd11_1 [4, 0] = true := by decide +kernel
theorem subd11_1_850 : subd11_1 [4, 1] = true := by decide +kernel
theorem sbd11_1_26 : ∀ q ∈ blkd11_1_26, subd11_1 q = true := by
  unfold blkd11_1_26
  exact List.forall_mem_cons.2 ⟨subd11_1_832, List.forall_mem_cons.2 ⟨subd11_1_833, List.forall_mem_cons.2 ⟨subd11_1_834, List.forall_mem_cons.2 ⟨subd11_1_835, List.forall_mem_cons.2 ⟨subd11_1_836, List.forall_mem_cons.2 ⟨subd11_1_837, List.forall_mem_cons.2 ⟨subd11_1_838, List.forall_mem_cons.2 ⟨subd11_1_839, List.forall_mem_cons.2 ⟨subd11_1_840, List.forall_mem_cons.2 ⟨subd11_1_841, List.forall_mem_cons.2 ⟨subd11_1_842, List.forall_mem_cons.2 ⟨subd11_1_843, List.forall_mem_cons.2 ⟨subd11_1_844, List.forall_mem_cons.2 ⟨subd11_1_845, List.forall_mem_cons.2 ⟨subd11_1_846, List.forall_mem_cons.2 ⟨subd11_1_847, List.forall_mem_cons.2 ⟨subd11_1_848, List.forall_mem_cons.2 ⟨subd11_1_849, List.forall_mem_cons.2 ⟨subd11_1_850, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [-1] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [0] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [1] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [-3] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [-2, -2] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [-2, -1] = true := by decide +kernel
theorem subd12_1_3 : subd12_1 [-2, 0] = true := by decide +kernel
theorem subd12_1_4 : subd12_1 [-2, 1] = true := by decide +kernel
theorem subd12_1_5 : subd12_1 [-2, 2] = true := by decide +kernel
theorem subd12_1_6 : subd12_1 [-2, 3] = true := by decide +kernel
theorem subd12_1_7 : subd12_1 [-1, -3] = true := by decide +kernel
theorem subd12_1_8 : subd12_1 [-1, -2] = true := by decide +kernel
theorem subd12_1_9 : subd12_1 [-1, -1] = true := by decide +kernel
theorem subd12_1_10 : subd12_1 [-1, 0, -7] = true := by decide +kernel
theorem subd12_1_11 : subd12_1 [-1, 0, -6] = true := by decide +kernel
theorem subd12_1_12 : subd12_1 [-1, 0, -5] = true := by decide +kernel
theorem subd12_1_13 : subd12_1 [-1, 0, -4] = true := by decide +kernel
theorem subd12_1_14 : subd12_1 [-1, 0, -3] = true := by decide +kernel
theorem subd12_1_15 : subd12_1 [-1, 0, -2] = true := by decide +kernel
theorem subd12_1_16 : subd12_1 [-1, 0, -1] = true := by decide +kernel
theorem subd12_1_17 : subd12_1 [-1, 0, 0] = true := by decide +kernel
theorem subd12_1_18 : subd12_1 [-1, 0, 1] = true := by decide +kernel
theorem subd12_1_19 : subd12_1 [-1, 0, 2] = true := by decide +kernel
theorem subd12_1_20 : subd12_1 [-1, 0, 3] = true := by decide +kernel
theorem subd12_1_21 : subd12_1 [-1, 0, 4] = true := by decide +kernel
theorem subd12_1_22 : subd12_1 [-1, 0, 5] = true := by decide +kernel
theorem subd12_1_23 : subd12_1 [-1, 0, 6] = true := by decide +kernel
theorem subd12_1_24 : subd12_1 [-1, 1, -6] = true := by decide +kernel
theorem subd12_1_25 : subd12_1 [-1, 1, -5] = true := by decide +kernel
theorem subd12_1_26 : subd12_1 [-1, 1, -4] = true := by decide +kernel
theorem subd12_1_27 : subd12_1 [-1, 1, -3] = true := by decide +kernel
theorem subd12_1_28 : subd12_1 [-1, 1, -2] = true := by decide +kernel
theorem subd12_1_29 : subd12_1 [-1, 1, -1] = true := by decide +kernel
theorem subd12_1_30 : subd12_1 [-1, 1, 0] = true := by decide +kernel
theorem subd12_1_31 : subd12_1 [-1, 1, 1] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_cons.2 ⟨subd12_1_3, List.forall_mem_cons.2 ⟨subd12_1_4, List.forall_mem_cons.2 ⟨subd12_1_5, List.forall_mem_cons.2 ⟨subd12_1_6, List.forall_mem_cons.2 ⟨subd12_1_7, List.forall_mem_cons.2 ⟨subd12_1_8, List.forall_mem_cons.2 ⟨subd12_1_9, List.forall_mem_cons.2 ⟨subd12_1_10, List.forall_mem_cons.2 ⟨subd12_1_11, List.forall_mem_cons.2 ⟨subd12_1_12, List.forall_mem_cons.2 ⟨subd12_1_13, List.forall_mem_cons.2 ⟨subd12_1_14, List.forall_mem_cons.2 ⟨subd12_1_15, List.forall_mem_cons.2 ⟨subd12_1_16, List.forall_mem_cons.2 ⟨subd12_1_17, List.forall_mem_cons.2 ⟨subd12_1_18, List.forall_mem_cons.2 ⟨subd12_1_19, List.forall_mem_cons.2 ⟨subd12_1_20, List.forall_mem_cons.2 ⟨subd12_1_21, List.forall_mem_cons.2 ⟨subd12_1_22, List.forall_mem_cons.2 ⟨subd12_1_23, List.forall_mem_cons.2 ⟨subd12_1_24, List.forall_mem_cons.2 ⟨subd12_1_25, List.forall_mem_cons.2 ⟨subd12_1_26, List.forall_mem_cons.2 ⟨subd12_1_27, List.forall_mem_cons.2 ⟨subd12_1_28, List.forall_mem_cons.2 ⟨subd12_1_29, List.forall_mem_cons.2 ⟨subd12_1_30, List.forall_mem_cons.2 ⟨subd12_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_32 : subd12_1 [-1, 1, 2] = true := by decide +kernel
theorem subd12_1_33 : subd12_1 [-1, 1, 3] = true := by decide +kernel
theorem subd12_1_34 : subd12_1 [-1, 1, 4] = true := by decide +kernel
theorem subd12_1_35 : subd12_1 [-1, 1, 5] = true := by decide +kernel
theorem subd12_1_36 : subd12_1 [-1, 1, 6] = true := by decide +kernel
theorem subd12_1_37 : subd12_1 [-1, 2] = true := by decide +kernel
theorem subd12_1_38 : subd12_1 [-1, 3] = true := by decide +kernel
theorem subd12_1_39 : subd12_1 [0, -4] = true := by decide +kernel
theorem subd12_1_40 : subd12_1 [0, -3] = true := by decide +kernel
theorem subd12_1_41 : subd12_1 [0, -2] = true := by decide +kernel
theorem subd12_1_42 : subd12_1 [0, -1, -7] = true := by decide +kernel
theorem subd12_1_43 : subd12_1 [0, -1, -6] = true := by decide +kernel
theorem subd12_1_44 : subd12_1 [0, -1, -5] = true := by decide +kernel
theorem subd12_1_45 : subd12_1 [0, -1, -4] = true := by decide +kernel
theorem subd12_1_46 : subd12_1 [0, -1, -3] = true := by decide +kernel
theorem subd12_1_47 : subd12_1 [0, -1, -2] = true := by decide +kernel
theorem subd12_1_48 : subd12_1 [0, -1, -1] = true := by decide +kernel
theorem subd12_1_49 : subd12_1 [0, -1, 0] = true := by decide +kernel
theorem subd12_1_50 : subd12_1 [0, -1, 1] = true := by decide +kernel
theorem subd12_1_51 : subd12_1 [0, -1, 2] = true := by decide +kernel
theorem subd12_1_52 : subd12_1 [0, -1, 3] = true := by decide +kernel
theorem subd12_1_53 : subd12_1 [0, -1, 4] = true := by decide +kernel
theorem subd12_1_54 : subd12_1 [0, -1, 5] = true := by decide +kernel
theorem subd12_1_55 : subd12_1 [0, -1, 6] = true := by decide +kernel
theorem subd12_1_56 : subd12_1 [0, 0, -7] = true := by decide +kernel
theorem subd12_1_57 : subd12_1 [0, 0, -6] = true := by decide +kernel
theorem subd12_1_58 : subd12_1 [0, 0, -5] = true := by decide +kernel
theorem subd12_1_59 : subd12_1 [0, 0, -4] = true := by decide +kernel
theorem subd12_1_60 : subd12_1 [0, 0, -3] = true := by decide +kernel
theorem subd12_1_61 : subd12_1 [0, 0, -2] = true := by decide +kernel
theorem subd12_1_62 : subd12_1 [0, 0, -1] = true := by decide +kernel
theorem subd12_1_63 : subd12_1 [0, 0, 0] = true := by decide +kernel
theorem sbd12_1_1 : ∀ q ∈ blkd12_1_1, subd12_1 q = true := by
  unfold blkd12_1_1
  exact List.forall_mem_cons.2 ⟨subd12_1_32, List.forall_mem_cons.2 ⟨subd12_1_33, List.forall_mem_cons.2 ⟨subd12_1_34, List.forall_mem_cons.2 ⟨subd12_1_35, List.forall_mem_cons.2 ⟨subd12_1_36, List.forall_mem_cons.2 ⟨subd12_1_37, List.forall_mem_cons.2 ⟨subd12_1_38, List.forall_mem_cons.2 ⟨subd12_1_39, List.forall_mem_cons.2 ⟨subd12_1_40, List.forall_mem_cons.2 ⟨subd12_1_41, List.forall_mem_cons.2 ⟨subd12_1_42, List.forall_mem_cons.2 ⟨subd12_1_43, List.forall_mem_cons.2 ⟨subd12_1_44, List.forall_mem_cons.2 ⟨subd12_1_45, List.forall_mem_cons.2 ⟨subd12_1_46, List.forall_mem_cons.2 ⟨subd12_1_47, List.forall_mem_cons.2 ⟨subd12_1_48, List.forall_mem_cons.2 ⟨subd12_1_49, List.forall_mem_cons.2 ⟨subd12_1_50, List.forall_mem_cons.2 ⟨subd12_1_51, List.forall_mem_cons.2 ⟨subd12_1_52, List.forall_mem_cons.2 ⟨subd12_1_53, List.forall_mem_cons.2 ⟨subd12_1_54, List.forall_mem_cons.2 ⟨subd12_1_55, List.forall_mem_cons.2 ⟨subd12_1_56, List.forall_mem_cons.2 ⟨subd12_1_57, List.forall_mem_cons.2 ⟨subd12_1_58, List.forall_mem_cons.2 ⟨subd12_1_59, List.forall_mem_cons.2 ⟨subd12_1_60, List.forall_mem_cons.2 ⟨subd12_1_61, List.forall_mem_cons.2 ⟨subd12_1_62, List.forall_mem_cons.2 ⟨subd12_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_64 : subd12_1 [0, 0, 1] = true := by decide +kernel
theorem subd12_1_65 : subd12_1 [0, 0, 2] = true := by decide +kernel
theorem subd12_1_66 : subd12_1 [0, 0, 3] = true := by decide +kernel
theorem subd12_1_67 : subd12_1 [0, 0, 4] = true := by decide +kernel
theorem subd12_1_68 : subd12_1 [0, 0, 5] = true := by decide +kernel
theorem subd12_1_69 : subd12_1 [0, 0, 6] = true := by decide +kernel
theorem subd12_1_70 : subd12_1 [0, 1, -7] = true := by decide +kernel
theorem subd12_1_71 : subd12_1 [0, 1, -6] = true := by decide +kernel
theorem subd12_1_72 : subd12_1 [0, 1, -5] = true := by decide +kernel
theorem subd12_1_73 : subd12_1 [0, 1, -4] = true := by decide +kernel
theorem subd12_1_74 : subd12_1 [0, 1, -3] = true := by decide +kernel
theorem subd12_1_75 : subd12_1 [0, 1, -2] = true := by decide +kernel
theorem subd12_1_76 : subd12_1 [0, 1, -1] = true := by decide +kernel
theorem subd12_1_77 : subd12_1 [0, 1, 0] = true := by decide +kernel
theorem subd12_1_78 : subd12_1 [0, 1, 1] = true := by decide +kernel
theorem subd12_1_79 : subd12_1 [0, 1, 2] = true := by decide +kernel
theorem subd12_1_80 : subd12_1 [0, 1, 3] = true := by decide +kernel
theorem subd12_1_81 : subd12_1 [0, 1, 4] = true := by decide +kernel
theorem subd12_1_82 : subd12_1 [0, 1, 5] = true := by decide +kernel
theorem subd12_1_83 : subd12_1 [0, 1, 6] = true := by decide +kernel
theorem subd12_1_84 : subd12_1 [0, 2] = true := by decide +kernel
theorem subd12_1_85 : subd12_1 [0, 3] = true := by decide +kernel
theorem subd12_1_86 : subd12_1 [1, -4] = true := by decide +kernel
theorem subd12_1_87 : subd12_1 [1, -3] = true := by decide +kernel
theorem subd12_1_88 : subd12_1 [1, -2] = true := by decide +kernel
theorem subd12_1_89 : subd12_1 [1, -1, -7] = true := by decide +kernel
theorem subd12_1_90 : subd12_1 [1, -1, -6] = true := by decide +kernel
theorem subd12_1_91 : subd12_1 [1, -1, -5] = true := by decide +kernel
theorem subd12_1_92 : subd12_1 [1, -1, -4] = true := by decide +kernel
theorem subd12_1_93 : subd12_1 [1, -1, -3] = true := by decide +kernel
theorem subd12_1_94 : subd12_1 [1, -1, -2] = true := by decide +kernel
theorem subd12_1_95 : subd12_1 [1, -1, -1] = true := by decide +kernel
theorem sbd12_1_2 : ∀ q ∈ blkd12_1_2, subd12_1 q = true := by
  unfold blkd12_1_2
  exact List.forall_mem_cons.2 ⟨subd12_1_64, List.forall_mem_cons.2 ⟨subd12_1_65, List.forall_mem_cons.2 ⟨subd12_1_66, List.forall_mem_cons.2 ⟨subd12_1_67, List.forall_mem_cons.2 ⟨subd12_1_68, List.forall_mem_cons.2 ⟨subd12_1_69, List.forall_mem_cons.2 ⟨subd12_1_70, List.forall_mem_cons.2 ⟨subd12_1_71, List.forall_mem_cons.2 ⟨subd12_1_72, List.forall_mem_cons.2 ⟨subd12_1_73, List.forall_mem_cons.2 ⟨subd12_1_74, List.forall_mem_cons.2 ⟨subd12_1_75, List.forall_mem_cons.2 ⟨subd12_1_76, List.forall_mem_cons.2 ⟨subd12_1_77, List.forall_mem_cons.2 ⟨subd12_1_78, List.forall_mem_cons.2 ⟨subd12_1_79, List.forall_mem_cons.2 ⟨subd12_1_80, List.forall_mem_cons.2 ⟨subd12_1_81, List.forall_mem_cons.2 ⟨subd12_1_82, List.forall_mem_cons.2 ⟨subd12_1_83, List.forall_mem_cons.2 ⟨subd12_1_84, List.forall_mem_cons.2 ⟨subd12_1_85, List.forall_mem_cons.2 ⟨subd12_1_86, List.forall_mem_cons.2 ⟨subd12_1_87, List.forall_mem_cons.2 ⟨subd12_1_88, List.forall_mem_cons.2 ⟨subd12_1_89, List.forall_mem_cons.2 ⟨subd12_1_90, List.forall_mem_cons.2 ⟨subd12_1_91, List.forall_mem_cons.2 ⟨subd12_1_92, List.forall_mem_cons.2 ⟨subd12_1_93, List.forall_mem_cons.2 ⟨subd12_1_94, List.forall_mem_cons.2 ⟨subd12_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_96 : subd12_1 [1, -1, 0] = true := by decide +kernel
theorem subd12_1_97 : subd12_1 [1, -1, 1] = true := by decide +kernel
theorem subd12_1_98 : subd12_1 [1, -1, 2] = true := by decide +kernel
theorem subd12_1_99 : subd12_1 [1, -1, 3] = true := by decide +kernel
theorem subd12_1_100 : subd12_1 [1, -1, 4] = true := by decide +kernel
theorem subd12_1_101 : subd12_1 [1, -1, 5] = true := by decide +kernel
theorem subd12_1_102 : subd12_1 [1, 0, -7] = true := by decide +kernel
theorem subd12_1_103 : subd12_1 [1, 0, -6] = true := by decide +kernel
theorem subd12_1_104 : subd12_1 [1, 0, -5] = true := by decide +kernel
theorem subd12_1_105 : subd12_1 [1, 0, -4] = true := by decide +kernel
theorem subd12_1_106 : subd12_1 [1, 0, -3] = true := by decide +kernel
theorem subd12_1_107 : subd12_1 [1, 0, -2] = true := by decide +kernel
theorem subd12_1_108 : subd12_1 [1, 0, -1] = true := by decide +kernel
theorem subd12_1_109 : subd12_1 [1, 0, 0] = true := by decide +kernel
theorem subd12_1_110 : subd12_1 [1, 0, 1] = true := by decide +kernel
theorem subd12_1_111 : subd12_1 [1, 0, 2] = true := by decide +kernel
theorem subd12_1_112 : subd12_1 [1, 0, 3] = true := by decide +kernel
theorem subd12_1_113 : subd12_1 [1, 0, 4] = true := by decide +kernel
theorem subd12_1_114 : subd12_1 [1, 0, 5] = true := by decide +kernel
theorem subd12_1_115 : subd12_1 [1, 0, 6] = true := by decide +kernel
theorem subd12_1_116 : subd12_1 [1, 1] = true := by decide +kernel
theorem subd12_1_117 : subd12_1 [1, 2] = true := by decide +kernel
theorem subd12_1_118 : subd12_1 [2, -4] = true := by decide +kernel
theorem subd12_1_119 : subd12_1 [2, -3] = true := by decide +kernel
theorem subd12_1_120 : subd12_1 [2, -2] = true := by decide +kernel
theorem subd12_1_121 : subd12_1 [2, -1] = true := by decide +kernel
theorem subd12_1_122 : subd12_1 [2, 0] = true := by decide +kernel
theorem subd12_1_123 : subd12_1 [2, 1] = true := by decide +kernel
theorem subd12_1_124 : subd12_1 [3] = true := by decide +kernel
theorem sbd12_1_3 : ∀ q ∈ blkd12_1_3, subd12_1 q = true := by
  unfold blkd12_1_3
  exact List.forall_mem_cons.2 ⟨subd12_1_96, List.forall_mem_cons.2 ⟨subd12_1_97, List.forall_mem_cons.2 ⟨subd12_1_98, List.forall_mem_cons.2 ⟨subd12_1_99, List.forall_mem_cons.2 ⟨subd12_1_100, List.forall_mem_cons.2 ⟨subd12_1_101, List.forall_mem_cons.2 ⟨subd12_1_102, List.forall_mem_cons.2 ⟨subd12_1_103, List.forall_mem_cons.2 ⟨subd12_1_104, List.forall_mem_cons.2 ⟨subd12_1_105, List.forall_mem_cons.2 ⟨subd12_1_106, List.forall_mem_cons.2 ⟨subd12_1_107, List.forall_mem_cons.2 ⟨subd12_1_108, List.forall_mem_cons.2 ⟨subd12_1_109, List.forall_mem_cons.2 ⟨subd12_1_110, List.forall_mem_cons.2 ⟨subd12_1_111, List.forall_mem_cons.2 ⟨subd12_1_112, List.forall_mem_cons.2 ⟨subd12_1_113, List.forall_mem_cons.2 ⟨subd12_1_114, List.forall_mem_cons.2 ⟨subd12_1_115, List.forall_mem_cons.2 ⟨subd12_1_116, List.forall_mem_cons.2 ⟨subd12_1_117, List.forall_mem_cons.2 ⟨subd12_1_118, List.forall_mem_cons.2 ⟨subd12_1_119, List.forall_mem_cons.2 ⟨subd12_1_120, List.forall_mem_cons.2 ⟨subd12_1_121, List.forall_mem_cons.2 ⟨subd12_1_122, List.forall_mem_cons.2 ⟨subd12_1_123, List.forall_mem_cons.2 ⟨subd12_1_124, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [-1] = true := by decide +kernel
theorem subd13_0_1 : subd13_0 [0] = true := by decide +kernel
theorem subd13_0_2 : subd13_0 [1] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_cons.2 ⟨subd13_0_1, List.forall_mem_cons.2 ⟨subd13_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C116
