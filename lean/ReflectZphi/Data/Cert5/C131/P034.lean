import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd17_1 : ldCheck G d17_1.U d17_1.ms ldd17_1 = true := by decide +kernel
theorem pre_okd17_1 : subPre G cell17 d17_1 = true := by decide +kernel
theorem subd17_1_0 : subd17_1 [-2] = true := by decide +kernel
theorem subd17_1_1 : subd17_1 [-1, -3] = true := by decide +kernel
theorem subd17_1_2 : subd17_1 [-1, -2] = true := by decide +kernel
theorem subd17_1_3 : subd17_1 [-1, -1] = true := by decide +kernel
theorem subd17_1_4 : subd17_1 [-1, 0] = true := by decide +kernel
theorem subd17_1_5 : subd17_1 [-1, 1] = true := by decide +kernel
theorem subd17_1_6 : subd17_1 [-1, 2] = true := by decide +kernel
theorem subd17_1_7 : subd17_1 [0, -3] = true := by decide +kernel
theorem subd17_1_8 : subd17_1 [0, -2] = true := by decide +kernel
theorem subd17_1_9 : subd17_1 [0, -1] = true := by decide +kernel
theorem subd17_1_10 : subd17_1 [0, 0] = true := by decide +kernel
theorem subd17_1_11 : subd17_1 [0, 1] = true := by decide +kernel
theorem subd17_1_12 : subd17_1 [0, 2] = true := by decide +kernel
theorem subd17_1_13 : subd17_1 [1, -3] = true := by decide +kernel
theorem subd17_1_14 : subd17_1 [1, -2] = true := by decide +kernel
theorem subd17_1_15 : subd17_1 [1, -1] = true := by decide +kernel
theorem subd17_1_16 : subd17_1 [1, 0] = true := by decide +kernel
theorem subd17_1_17 : subd17_1 [1, 1] = true := by decide +kernel
theorem subd17_1_18 : subd17_1 [1, 2] = true := by decide +kernel
theorem subd17_1_19 : subd17_1 [2] = true := by decide +kernel
theorem sbd17_1_0 : ∀ q ∈ blkd17_1_0, subd17_1 q = true := by
  unfold blkd17_1_0
  exact List.forall_mem_cons.2 ⟨subd17_1_0, List.forall_mem_cons.2 ⟨subd17_1_1, List.forall_mem_cons.2 ⟨subd17_1_2, List.forall_mem_cons.2 ⟨subd17_1_3, List.forall_mem_cons.2 ⟨subd17_1_4, List.forall_mem_cons.2 ⟨subd17_1_5, List.forall_mem_cons.2 ⟨subd17_1_6, List.forall_mem_cons.2 ⟨subd17_1_7, List.forall_mem_cons.2 ⟨subd17_1_8, List.forall_mem_cons.2 ⟨subd17_1_9, List.forall_mem_cons.2 ⟨subd17_1_10, List.forall_mem_cons.2 ⟨subd17_1_11, List.forall_mem_cons.2 ⟨subd17_1_12, List.forall_mem_cons.2 ⟨subd17_1_13, List.forall_mem_cons.2 ⟨subd17_1_14, List.forall_mem_cons.2 ⟨subd17_1_15, List.forall_mem_cons.2 ⟨subd17_1_16, List.forall_mem_cons.2 ⟨subd17_1_17, List.forall_mem_cons.2 ⟨subd17_1_18, List.forall_mem_cons.2 ⟨subd17_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd18_0 : ldCheck G d18_0.U d18_0.ms ldd18_0 = true := by decide +kernel
theorem pre_okd18_0 : subPre G cell18 d18_0 = true := by decide +kernel
theorem subd18_0_0 : subd18_0 [-2, -2] = true := by decide +kernel
theorem subd18_0_1 : subd18_0 [-2, -1] = true := by decide +kernel
theorem subd18_0_2 : subd18_0 [-2, 0, -6] = true := by decide +kernel
theorem subd18_0_3 : subd18_0 [-2, 0, -5] = true := by decide +kernel
theorem subd18_0_4 : subd18_0 [-2, 0, -4] = true := by decide +kernel
theorem subd18_0_5 : subd18_0 [-2, 0, -3] = true := by decide +kernel
theorem subd18_0_6 : subd18_0 [-2, 0, -2] = true := by decide +kernel
theorem subd18_0_7 : subd18_0 [-2, 0, -1] = true := by decide +kernel
theorem subd18_0_8 : subd18_0 [-2, 0, 0] = true := by decide +kernel
theorem subd18_0_9 : subd18_0 [-2, 0, 1] = true := by decide +kernel
theorem subd18_0_10 : subd18_0 [-2, 0, 2] = true := by decide +kernel
theorem subd18_0_11 : subd18_0 [-2, 0, 3] = true := by decide +kernel
theorem subd18_0_12 : subd18_0 [-2, 0, 4] = true := by decide +kernel
theorem subd18_0_13 : subd18_0 [-2, 0, 5] = true := by decide +kernel
theorem subd18_0_14 : subd18_0 [-2, 0, 6] = true := by decide +kernel
theorem subd18_0_15 : subd18_0 [-2, 0, 7] = true := by decide +kernel
theorem subd18_0_16 : subd18_0 [-2, 1] = true := by decide +kernel
theorem subd18_0_17 : subd18_0 [-2, 2] = true := by decide +kernel
theorem subd18_0_18 : subd18_0 [-1, -3] = true := by decide +kernel
theorem subd18_0_19 : subd18_0 [-1, -2] = true := by decide +kernel
theorem subd18_0_20 : subd18_0 [-1, -1, -8] = true := by decide +kernel
theorem subd18_0_21 : subd18_0 [-1, -1, -7] = true := by decide +kernel
theorem subd18_0_22 : subd18_0 [-1, -1, -6] = true := by decide +kernel
theorem subd18_0_23 : subd18_0 [-1, -1, -5] = true := by decide +kernel
theorem subd18_0_24 : subd18_0 [-1, -1, -4] = true := by decide +kernel
theorem subd18_0_25 : subd18_0 [-1, -1, -3] = true := by decide +kernel
theorem subd18_0_26 : subd18_0 [-1, -1, -2] = true := by decide +kernel
theorem subd18_0_27 : subd18_0 [-1, -1, -1] = true := by decide +kernel
theorem subd18_0_28 : subd18_0 [-1, -1, 0] = true := by decide +kernel
theorem subd18_0_29 : subd18_0 [-1, -1, 1] = true := by decide +kernel
theorem subd18_0_30 : subd18_0 [-1, -1, 2] = true := by decide +kernel
theorem subd18_0_31 : subd18_0 [-1, -1, 3] = true := by decide +kernel
theorem sbd18_0_0 : ∀ q ∈ blkd18_0_0, subd18_0 q = true := by
  unfold blkd18_0_0
  exact List.forall_mem_cons.2 ⟨subd18_0_0, List.forall_mem_cons.2 ⟨subd18_0_1, List.forall_mem_cons.2 ⟨subd18_0_2, List.forall_mem_cons.2 ⟨subd18_0_3, List.forall_mem_cons.2 ⟨subd18_0_4, List.forall_mem_cons.2 ⟨subd18_0_5, List.forall_mem_cons.2 ⟨subd18_0_6, List.forall_mem_cons.2 ⟨subd18_0_7, List.forall_mem_cons.2 ⟨subd18_0_8, List.forall_mem_cons.2 ⟨subd18_0_9, List.forall_mem_cons.2 ⟨subd18_0_10, List.forall_mem_cons.2 ⟨subd18_0_11, List.forall_mem_cons.2 ⟨subd18_0_12, List.forall_mem_cons.2 ⟨subd18_0_13, List.forall_mem_cons.2 ⟨subd18_0_14, List.forall_mem_cons.2 ⟨subd18_0_15, List.forall_mem_cons.2 ⟨subd18_0_16, List.forall_mem_cons.2 ⟨subd18_0_17, List.forall_mem_cons.2 ⟨subd18_0_18, List.forall_mem_cons.2 ⟨subd18_0_19, List.forall_mem_cons.2 ⟨subd18_0_20, List.forall_mem_cons.2 ⟨subd18_0_21, List.forall_mem_cons.2 ⟨subd18_0_22, List.forall_mem_cons.2 ⟨subd18_0_23, List.forall_mem_cons.2 ⟨subd18_0_24, List.forall_mem_cons.2 ⟨subd18_0_25, List.forall_mem_cons.2 ⟨subd18_0_26, List.forall_mem_cons.2 ⟨subd18_0_27, List.forall_mem_cons.2 ⟨subd18_0_28, List.forall_mem_cons.2 ⟨subd18_0_29, List.forall_mem_cons.2 ⟨subd18_0_30, List.forall_mem_cons.2 ⟨subd18_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_32 : subd18_0 [-1, -1, 4] = true := by decide +kernel
theorem subd18_0_33 : subd18_0 [-1, -1, 5] = true := by decide +kernel
theorem subd18_0_34 : subd18_0 [-1, -1, 6] = true := by decide +kernel
theorem subd18_0_35 : subd18_0 [-1, -1, 7] = true := by decide +kernel
theorem subd18_0_36 : subd18_0 [-1, 0, -8] = true := by decide +kernel
theorem subd18_0_37 : subd18_0 [-1, 0, -7] = true := by decide +kernel
theorem subd18_0_38 : subd18_0 [-1, 0, -6] = true := by decide +kernel
theorem subd18_0_39 : subd18_0 [-1, 0, -5] = true := by decide +kernel
theorem subd18_0_40 : subd18_0 [-1, 0, -4] = true := by decide +kernel
theorem subd18_0_41 : subd18_0 [-1, 0, -3] = true := by decide +kernel
theorem subd18_0_42 : subd18_0 [-1, 0, -2] = true := by decide +kernel
theorem subd18_0_43 : subd18_0 [-1, 0, -1] = true := by decide +kernel
theorem subd18_0_44 : subd18_0 [-1, 0, 0] = true := by decide +kernel
theorem subd18_0_45 : subd18_0 [-1, 0, 1] = true := by decide +kernel
theorem subd18_0_46 : subd18_0 [-1, 0, 2] = true := by decide +kernel
theorem subd18_0_47 : subd18_0 [-1, 0, 3] = true := by decide +kernel
theorem subd18_0_48 : subd18_0 [-1, 0, 4] = true := by decide +kernel
theorem subd18_0_49 : subd18_0 [-1, 0, 5] = true := by decide +kernel
theorem subd18_0_50 : subd18_0 [-1, 0, 6] = true := by decide +kernel
theorem subd18_0_51 : subd18_0 [-1, 0, 7] = true := by decide +kernel
theorem subd18_0_52 : subd18_0 [-1, 0, 8] = true := by decide +kernel
theorem subd18_0_53 : subd18_0 [-1, 1, -8] = true := by decide +kernel
theorem subd18_0_54 : subd18_0 [-1, 1, -7] = true := by decide +kernel
theorem subd18_0_55 : subd18_0 [-1, 1, -6] = true := by decide +kernel
theorem subd18_0_56 : subd18_0 [-1, 1, -5] = true := by decide +kernel
theorem subd18_0_57 : subd18_0 [-1, 1, -4] = true := by decide +kernel
theorem subd18_0_58 : subd18_0 [-1, 1, -3] = true := by decide +kernel
theorem subd18_0_59 : subd18_0 [-1, 1, -2] = true := by decide +kernel
theorem subd18_0_60 : subd18_0 [-1, 1, -1] = true := by decide +kernel
theorem subd18_0_61 : subd18_0 [-1, 1, 0] = true := by decide +kernel
theorem subd18_0_62 : subd18_0 [-1, 1, 1] = true := by decide +kernel
theorem subd18_0_63 : subd18_0 [-1, 1, 2] = true := by decide +kernel
theorem sbd18_0_1 : ∀ q ∈ blkd18_0_1, subd18_0 q = true := by
  unfold blkd18_0_1
  exact List.forall_mem_cons.2 ⟨subd18_0_32, List.forall_mem_cons.2 ⟨subd18_0_33, List.forall_mem_cons.2 ⟨subd18_0_34, List.forall_mem_cons.2 ⟨subd18_0_35, List.forall_mem_cons.2 ⟨subd18_0_36, List.forall_mem_cons.2 ⟨subd18_0_37, List.forall_mem_cons.2 ⟨subd18_0_38, List.forall_mem_cons.2 ⟨subd18_0_39, List.forall_mem_cons.2 ⟨subd18_0_40, List.forall_mem_cons.2 ⟨subd18_0_41, List.forall_mem_cons.2 ⟨subd18_0_42, List.forall_mem_cons.2 ⟨subd18_0_43, List.forall_mem_cons.2 ⟨subd18_0_44, List.forall_mem_cons.2 ⟨subd18_0_45, List.forall_mem_cons.2 ⟨subd18_0_46, List.forall_mem_cons.2 ⟨subd18_0_47, List.forall_mem_cons.2 ⟨subd18_0_48, List.forall_mem_cons.2 ⟨subd18_0_49, List.forall_mem_cons.2 ⟨subd18_0_50, List.forall_mem_cons.2 ⟨subd18_0_51, List.forall_mem_cons.2 ⟨subd18_0_52, List.forall_mem_cons.2 ⟨subd18_0_53, List.forall_mem_cons.2 ⟨subd18_0_54, List.forall_mem_cons.2 ⟨subd18_0_55, List.forall_mem_cons.2 ⟨subd18_0_56, List.forall_mem_cons.2 ⟨subd18_0_57, List.forall_mem_cons.2 ⟨subd18_0_58, List.forall_mem_cons.2 ⟨subd18_0_59, List.forall_mem_cons.2 ⟨subd18_0_60, List.forall_mem_cons.2 ⟨subd18_0_61, List.forall_mem_cons.2 ⟨subd18_0_62, List.forall_mem_cons.2 ⟨subd18_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_64 : subd18_0 [-1, 1, 3] = true := by decide +kernel
theorem subd18_0_65 : subd18_0 [-1, 1, 4] = true := by decide +kernel
theorem subd18_0_66 : subd18_0 [-1, 1, 5] = true := by decide +kernel
theorem subd18_0_67 : subd18_0 [-1, 1, 6] = true := by decide +kernel
theorem subd18_0_68 : subd18_0 [-1, 1, 7] = true := by decide +kernel
theorem subd18_0_69 : subd18_0 [-1, 1, 8] = true := by decide +kernel
theorem subd18_0_70 : subd18_0 [-1, 2] = true := by decide +kernel
theorem subd18_0_71 : subd18_0 [0, -3] = true := by decide +kernel
theorem subd18_0_72 : subd18_0 [0, -2, -7] = true := by decide +kernel
theorem subd18_0_73 : subd18_0 [0, -2, -6] = true := by decide +kernel
theorem subd18_0_74 : subd18_0 [0, -2, -5] = true := by decide +kernel
theorem subd18_0_75 : subd18_0 [0, -2, -4] = true := by decide +kernel
theorem subd18_0_76 : subd18_0 [0, -2, -3] = true := by decide +kernel
theorem subd18_0_77 : subd18_0 [0, -2, -2] = true := by decide +kernel
theorem subd18_0_78 : subd18_0 [0, -2, -1] = true := by decide +kernel
theorem subd18_0_79 : subd18_0 [0, -2, 0] = true := by decide +kernel
theorem subd18_0_80 : subd18_0 [0, -2, 1] = true := by decide +kernel
theorem subd18_0_81 : subd18_0 [0, -2, 2] = true := by decide +kernel
theorem subd18_0_82 : subd18_0 [0, -2, 3] = true := by decide +kernel
theorem subd18_0_83 : subd18_0 [0, -2, 4] = true := by decide +kernel
theorem subd18_0_84 : subd18_0 [0, -2, 5] = true := by decide +kernel
theorem subd18_0_85 : subd18_0 [0, -2, 6] = true := by decide +kernel
theorem subd18_0_86 : subd18_0 [0, -1, -9] = true := by decide +kernel
theorem subd18_0_87 : subd18_0 [0, -1, -8] = true := by decide +kernel
theorem subd18_0_88 : subd18_0 [0, -1, -7] = true := by decide +kernel
theorem subd18_0_89 : subd18_0 [0, -1, -6] = true := by decide +kernel
theorem subd18_0_90 : subd18_0 [0, -1, -5] = true := by decide +kernel
theorem subd18_0_91 : subd18_0 [0, -1, -4] = true := by decide +kernel
theorem subd18_0_92 : subd18_0 [0, -1, -3] = true := by decide +kernel
theorem subd18_0_93 : subd18_0 [0, -1, -2] = true := by decide +kernel
theorem subd18_0_94 : subd18_0 [0, -1, -1] = true := by decide +kernel
theorem subd18_0_95 : subd18_0 [0, -1, 0] = true := by decide +kernel
theorem sbd18_0_2 : ∀ q ∈ blkd18_0_2, subd18_0 q = true := by
  unfold blkd18_0_2
  exact List.forall_mem_cons.2 ⟨subd18_0_64, List.forall_mem_cons.2 ⟨subd18_0_65, List.forall_mem_cons.2 ⟨subd18_0_66, List.forall_mem_cons.2 ⟨subd18_0_67, List.forall_mem_cons.2 ⟨subd18_0_68, List.forall_mem_cons.2 ⟨subd18_0_69, List.forall_mem_cons.2 ⟨subd18_0_70, List.forall_mem_cons.2 ⟨subd18_0_71, List.forall_mem_cons.2 ⟨subd18_0_72, List.forall_mem_cons.2 ⟨subd18_0_73, List.forall_mem_cons.2 ⟨subd18_0_74, List.forall_mem_cons.2 ⟨subd18_0_75, List.forall_mem_cons.2 ⟨subd18_0_76, List.forall_mem_cons.2 ⟨subd18_0_77, List.forall_mem_cons.2 ⟨subd18_0_78, List.forall_mem_cons.2 ⟨subd18_0_79, List.forall_mem_cons.2 ⟨subd18_0_80, List.forall_mem_cons.2 ⟨subd18_0_81, List.forall_mem_cons.2 ⟨subd18_0_82, List.forall_mem_cons.2 ⟨subd18_0_83, List.forall_mem_cons.2 ⟨subd18_0_84, List.forall_mem_cons.2 ⟨subd18_0_85, List.forall_mem_cons.2 ⟨subd18_0_86, List.forall_mem_cons.2 ⟨subd18_0_87, List.forall_mem_cons.2 ⟨subd18_0_88, List.forall_mem_cons.2 ⟨subd18_0_89, List.forall_mem_cons.2 ⟨subd18_0_90, List.forall_mem_cons.2 ⟨subd18_0_91, List.forall_mem_cons.2 ⟨subd18_0_92, List.forall_mem_cons.2 ⟨subd18_0_93, List.forall_mem_cons.2 ⟨subd18_0_94, List.forall_mem_cons.2 ⟨subd18_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_96 : subd18_0 [0, -1, 1] = true := by decide +kernel
theorem subd18_0_97 : subd18_0 [0, -1, 2] = true := by decide +kernel
theorem subd18_0_98 : subd18_0 [0, -1, 3] = true := by decide +kernel
theorem subd18_0_99 : subd18_0 [0, -1, 4] = true := by decide +kernel
theorem subd18_0_100 : subd18_0 [0, -1, 5] = true := by decide +kernel
theorem subd18_0_101 : subd18_0 [0, -1, 6] = true := by decide +kernel
theorem subd18_0_102 : subd18_0 [0, -1, 7] = true := by decide +kernel
theorem subd18_0_103 : subd18_0 [0, -1, 8] = true := by decide +kernel
theorem subd18_0_104 : subd18_0 [0, 0, -9] = true := by decide +kernel
theorem subd18_0_105 : subd18_0 [0, 0, -8] = true := by decide +kernel
theorem subd18_0_106 : subd18_0 [0, 0, -7] = true := by decide +kernel
theorem subd18_0_107 : subd18_0 [0, 0, -6] = true := by decide +kernel
theorem subd18_0_108 : subd18_0 [0, 0, -5] = true := by decide +kernel
theorem subd18_0_109 : subd18_0 [0, 0, -4] = true := by decide +kernel
theorem subd18_0_110 : subd18_0 [0, 0, -3] = true := by decide +kernel
theorem subd18_0_111 : subd18_0 [0, 0, -2] = true := by decide +kernel
theorem subd18_0_112 : subd18_0 [0, 0, -1] = true := by decide +kernel
theorem subd18_0_113 : subd18_0 [0, 0, 0] = true := by decide +kernel
theorem subd18_0_114 : subd18_0 [0, 0, 1] = true := by decide +kernel
theorem subd18_0_115 : subd18_0 [0, 0, 2] = true := by decide +kernel
theorem subd18_0_116 : subd18_0 [0, 0, 3] = true := by decide +kernel
theorem subd18_0_117 : subd18_0 [0, 0, 4] = true := by decide +kernel
theorem subd18_0_118 : subd18_0 [0, 0, 5] = true := by decide +kernel
theorem subd18_0_119 : subd18_0 [0, 0, 6] = true := by decide +kernel
theorem subd18_0_120 : subd18_0 [0, 0, 7] = true := by decide +kernel
theorem subd18_0_121 : subd18_0 [0, 0, 8] = true := by decide +kernel
theorem subd18_0_122 : subd18_0 [0, 1, -9] = true := by decide +kernel
theorem subd18_0_123 : subd18_0 [0, 1, -8] = true := by decide +kernel
theorem subd18_0_124 : subd18_0 [0, 1, -7] = true := by decide +kernel
theorem subd18_0_125 : subd18_0 [0, 1, -6] = true := by decide +kernel
theorem subd18_0_126 : subd18_0 [0, 1, -5] = true := by decide +kernel
theorem subd18_0_127 : subd18_0 [0, 1, -4] = true := by decide +kernel
theorem sbd18_0_3 : ∀ q ∈ blkd18_0_3, subd18_0 q = true := by
  unfold blkd18_0_3
  exact List.forall_mem_cons.2 ⟨subd18_0_96, List.forall_mem_cons.2 ⟨subd18_0_97, List.forall_mem_cons.2 ⟨subd18_0_98, List.forall_mem_cons.2 ⟨subd18_0_99, List.forall_mem_cons.2 ⟨subd18_0_100, List.forall_mem_cons.2 ⟨subd18_0_101, List.forall_mem_cons.2 ⟨subd18_0_102, List.forall_mem_cons.2 ⟨subd18_0_103, List.forall_mem_cons.2 ⟨subd18_0_104, List.forall_mem_cons.2 ⟨subd18_0_105, List.forall_mem_cons.2 ⟨subd18_0_106, List.forall_mem_cons.2 ⟨subd18_0_107, List.forall_mem_cons.2 ⟨subd18_0_108, List.forall_mem_cons.2 ⟨subd18_0_109, List.forall_mem_cons.2 ⟨subd18_0_110, List.forall_mem_cons.2 ⟨subd18_0_111, List.forall_mem_cons.2 ⟨subd18_0_112, List.forall_mem_cons.2 ⟨subd18_0_113, List.forall_mem_cons.2 ⟨subd18_0_114, List.forall_mem_cons.2 ⟨subd18_0_115, List.forall_mem_cons.2 ⟨subd18_0_116, List.forall_mem_cons.2 ⟨subd18_0_117, List.forall_mem_cons.2 ⟨subd18_0_118, List.forall_mem_cons.2 ⟨subd18_0_119, List.forall_mem_cons.2 ⟨subd18_0_120, List.forall_mem_cons.2 ⟨subd18_0_121, List.forall_mem_cons.2 ⟨subd18_0_122, List.forall_mem_cons.2 ⟨subd18_0_123, List.forall_mem_cons.2 ⟨subd18_0_124, List.forall_mem_cons.2 ⟨subd18_0_125, List.forall_mem_cons.2 ⟨subd18_0_126, List.forall_mem_cons.2 ⟨subd18_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_128 : subd18_0 [0, 1, -3] = true := by decide +kernel
theorem subd18_0_129 : subd18_0 [0, 1, -2] = true := by decide +kernel
theorem subd18_0_130 : subd18_0 [0, 1, -1] = true := by decide +kernel
theorem subd18_0_131 : subd18_0 [0, 1, 0] = true := by decide +kernel
theorem subd18_0_132 : subd18_0 [0, 1, 1] = true := by decide +kernel
theorem subd18_0_133 : subd18_0 [0, 1, 2] = true := by decide +kernel
theorem subd18_0_134 : subd18_0 [0, 1, 3] = true := by decide +kernel
theorem subd18_0_135 : subd18_0 [0, 1, 4] = true := by decide +kernel
theorem subd18_0_136 : subd18_0 [0, 1, 5] = true := by decide +kernel
theorem subd18_0_137 : subd18_0 [0, 1, 6] = true := by decide +kernel
theorem subd18_0_138 : subd18_0 [0, 1, 7] = true := by decide +kernel
theorem subd18_0_139 : subd18_0 [0, 1, 8] = true := by decide +kernel
theorem subd18_0_140 : subd18_0 [0, 2, -7] = true := by decide +kernel
theorem subd18_0_141 : subd18_0 [0, 2, -6] = true := by decide +kernel
theorem subd18_0_142 : subd18_0 [0, 2, -5] = true := by decide +kernel
theorem subd18_0_143 : subd18_0 [0, 2, -4] = true := by decide +kernel
theorem subd18_0_144 : subd18_0 [0, 2, -3] = true := by decide +kernel
theorem subd18_0_145 : subd18_0 [0, 2, -2] = true := by decide +kernel
theorem subd18_0_146 : subd18_0 [0, 2, -1] = true := by decide +kernel
theorem subd18_0_147 : subd18_0 [0, 2, 0] = true := by decide +kernel
theorem subd18_0_148 : subd18_0 [0, 2, 1] = true := by decide +kernel
theorem subd18_0_149 : subd18_0 [0, 2, 2] = true := by decide +kernel
theorem subd18_0_150 : subd18_0 [0, 2, 3] = true := by decide +kernel
theorem subd18_0_151 : subd18_0 [0, 2, 4] = true := by decide +kernel
theorem subd18_0_152 : subd18_0 [0, 2, 5] = true := by decide +kernel
theorem subd18_0_153 : subd18_0 [0, 2, 6] = true := by decide +kernel
theorem subd18_0_154 : subd18_0 [1, -3] = true := by decide +kernel
theorem subd18_0_155 : subd18_0 [1, -2] = true := by decide +kernel
theorem subd18_0_156 : subd18_0 [1, -1, -9] = true := by decide +kernel
theorem subd18_0_157 : subd18_0 [1, -1, -8] = true := by decide +kernel
theorem subd18_0_158 : subd18_0 [1, -1, -7] = true := by decide +kernel
theorem subd18_0_159 : subd18_0 [1, -1, -6] = true := by decide +kernel
theorem sbd18_0_4 : ∀ q ∈ blkd18_0_4, subd18_0 q = true := by
  unfold blkd18_0_4
  exact List.forall_mem_cons.2 ⟨subd18_0_128, List.forall_mem_cons.2 ⟨subd18_0_129, List.forall_mem_cons.2 ⟨subd18_0_130, List.forall_mem_cons.2 ⟨subd18_0_131, List.forall_mem_cons.2 ⟨subd18_0_132, List.forall_mem_cons.2 ⟨subd18_0_133, List.forall_mem_cons.2 ⟨subd18_0_134, List.forall_mem_cons.2 ⟨subd18_0_135, List.forall_mem_cons.2 ⟨subd18_0_136, List.forall_mem_cons.2 ⟨subd18_0_137, List.forall_mem_cons.2 ⟨subd18_0_138, List.forall_mem_cons.2 ⟨subd18_0_139, List.forall_mem_cons.2 ⟨subd18_0_140, List.forall_mem_cons.2 ⟨subd18_0_141, List.forall_mem_cons.2 ⟨subd18_0_142, List.forall_mem_cons.2 ⟨subd18_0_143, List.forall_mem_cons.2 ⟨subd18_0_144, List.forall_mem_cons.2 ⟨subd18_0_145, List.forall_mem_cons.2 ⟨subd18_0_146, List.forall_mem_cons.2 ⟨subd18_0_147, List.forall_mem_cons.2 ⟨subd18_0_148, List.forall_mem_cons.2 ⟨subd18_0_149, List.forall_mem_cons.2 ⟨subd18_0_150, List.forall_mem_cons.2 ⟨subd18_0_151, List.forall_mem_cons.2 ⟨subd18_0_152, List.forall_mem_cons.2 ⟨subd18_0_153, List.forall_mem_cons.2 ⟨subd18_0_154, List.forall_mem_cons.2 ⟨subd18_0_155, List.forall_mem_cons.2 ⟨subd18_0_156, List.forall_mem_cons.2 ⟨subd18_0_157, List.forall_mem_cons.2 ⟨subd18_0_158, List.forall_mem_cons.2 ⟨subd18_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_160 : subd18_0 [1, -1, -5] = true := by decide +kernel
theorem subd18_0_161 : subd18_0 [1, -1, -4] = true := by decide +kernel
theorem subd18_0_162 : subd18_0 [1, -1, -3] = true := by decide +kernel
theorem subd18_0_163 : subd18_0 [1, -1, -2] = true := by decide +kernel
theorem subd18_0_164 : subd18_0 [1, -1, -1] = true := by decide +kernel
theorem subd18_0_165 : subd18_0 [1, -1, 0] = true := by decide +kernel
theorem subd18_0_166 : subd18_0 [1, -1, 1] = true := by decide +kernel
theorem subd18_0_167 : subd18_0 [1, -1, 2] = true := by decide +kernel
theorem subd18_0_168 : subd18_0 [1, -1, 3] = true := by decide +kernel
theorem subd18_0_169 : subd18_0 [1, -1, 4] = true := by decide +kernel
theorem subd18_0_170 : subd18_0 [1, -1, 5] = true := by decide +kernel
theorem subd18_0_171 : subd18_0 [1, -1, 6] = true := by decide +kernel
theorem subd18_0_172 : subd18_0 [1, -1, 7] = true := by decide +kernel
theorem subd18_0_173 : subd18_0 [1, 0, -9] = true := by decide +kernel
theorem subd18_0_174 : subd18_0 [1, 0, -8] = true := by decide +kernel
theorem subd18_0_175 : subd18_0 [1, 0, -7] = true := by decide +kernel
theorem subd18_0_176 : subd18_0 [1, 0, -6] = true := by decide +kernel
theorem subd18_0_177 : subd18_0 [1, 0, -5] = true := by decide +kernel
theorem subd18_0_178 : subd18_0 [1, 0, -4] = true := by decide +kernel
theorem subd18_0_179 : subd18_0 [1, 0, -3] = true := by decide +kernel
theorem subd18_0_180 : subd18_0 [1, 0, -2] = true := by decide +kernel
theorem subd18_0_181 : subd18_0 [1, 0, -1] = true := by decide +kernel
theorem subd18_0_182 : subd18_0 [1, 0, 0] = true := by decide +kernel
theorem subd18_0_183 : subd18_0 [1, 0, 1] = true := by decide +kernel
theorem subd18_0_184 : subd18_0 [1, 0, 2] = true := by decide +kernel
theorem subd18_0_185 : subd18_0 [1, 0, 3] = true := by decide +kernel
theorem subd18_0_186 : subd18_0 [1, 0, 4] = true := by decide +kernel
theorem subd18_0_187 : subd18_0 [1, 0, 5] = true := by decide +kernel
theorem subd18_0_188 : subd18_0 [1, 0, 6] = true := by decide +kernel
theorem subd18_0_189 : subd18_0 [1, 0, 7] = true := by decide +kernel
theorem subd18_0_190 : subd18_0 [1, 1, -8] = true := by decide +kernel
theorem subd18_0_191 : subd18_0 [1, 1, -7] = true := by decide +kernel
theorem sbd18_0_5 : ∀ q ∈ blkd18_0_5, subd18_0 q = true := by
  unfold blkd18_0_5
  exact List.forall_mem_cons.2 ⟨subd18_0_160, List.forall_mem_cons.2 ⟨subd18_0_161, List.forall_mem_cons.2 ⟨subd18_0_162, List.forall_mem_cons.2 ⟨subd18_0_163, List.forall_mem_cons.2 ⟨subd18_0_164, List.forall_mem_cons.2 ⟨subd18_0_165, List.forall_mem_cons.2 ⟨subd18_0_166, List.forall_mem_cons.2 ⟨subd18_0_167, List.forall_mem_cons.2 ⟨subd18_0_168, List.forall_mem_cons.2 ⟨subd18_0_169, List.forall_mem_cons.2 ⟨subd18_0_170, List.forall_mem_cons.2 ⟨subd18_0_171, List.forall_mem_cons.2 ⟨subd18_0_172, List.forall_mem_cons.2 ⟨subd18_0_173, List.forall_mem_cons.2 ⟨subd18_0_174, List.forall_mem_cons.2 ⟨subd18_0_175, List.forall_mem_cons.2 ⟨subd18_0_176, List.forall_mem_cons.2 ⟨subd18_0_177, List.forall_mem_cons.2 ⟨subd18_0_178, List.forall_mem_cons.2 ⟨subd18_0_179, List.forall_mem_cons.2 ⟨subd18_0_180, List.forall_mem_cons.2 ⟨subd18_0_181, List.forall_mem_cons.2 ⟨subd18_0_182, List.forall_mem_cons.2 ⟨subd18_0_183, List.forall_mem_cons.2 ⟨subd18_0_184, List.forall_mem_cons.2 ⟨subd18_0_185, List.forall_mem_cons.2 ⟨subd18_0_186, List.forall_mem_cons.2 ⟨subd18_0_187, List.forall_mem_cons.2 ⟨subd18_0_188, List.forall_mem_cons.2 ⟨subd18_0_189, List.forall_mem_cons.2 ⟨subd18_0_190, List.forall_mem_cons.2 ⟨subd18_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_192 : subd18_0 [1, 1, -6] = true := by decide +kernel
theorem subd18_0_193 : subd18_0 [1, 1, -5] = true := by decide +kernel
theorem subd18_0_194 : subd18_0 [1, 1, -4] = true := by decide +kernel
theorem subd18_0_195 : subd18_0 [1, 1, -3] = true := by decide +kernel
theorem subd18_0_196 : subd18_0 [1, 1, -2] = true := by decide +kernel
theorem subd18_0_197 : subd18_0 [1, 1, -1] = true := by decide +kernel
theorem subd18_0_198 : subd18_0 [1, 1, 0] = true := by decide +kernel
theorem subd18_0_199 : subd18_0 [1, 1, 1] = true := by decide +kernel
theorem subd18_0_200 : subd18_0 [1, 1, 2] = true := by decide +kernel
theorem subd18_0_201 : subd18_0 [1, 1, 3] = true := by decide +kernel
theorem subd18_0_202 : subd18_0 [1, 1, 4] = true := by decide +kernel
theorem subd18_0_203 : subd18_0 [1, 1, 5] = true := by decide +kernel
theorem subd18_0_204 : subd18_0 [1, 1, 6] = true := by decide +kernel
theorem subd18_0_205 : subd18_0 [1, 1, 7] = true := by decide +kernel
theorem subd18_0_206 : subd18_0 [1, 2] = true := by decide +kernel
theorem subd18_0_207 : subd18_0 [2, -3] = true := by decide +kernel
theorem subd18_0_208 : subd18_0 [2, -2] = true := by decide +kernel
theorem subd18_0_209 : subd18_0 [2, -1] = true := by decide +kernel
theorem subd18_0_210 : subd18_0 [2, 0, -8] = true := by decide +kernel
theorem subd18_0_211 : subd18_0 [2, 0, -7] = true := by decide +kernel
theorem subd18_0_212 : subd18_0 [2, 0, -6] = true := by decide +kernel
theorem subd18_0_213 : subd18_0 [2, 0, -5] = true := by decide +kernel
theorem subd18_0_214 : subd18_0 [2, 0, -4] = true := by decide +kernel
theorem subd18_0_215 : subd18_0 [2, 0, -3] = true := by decide +kernel
theorem subd18_0_216 : subd18_0 [2, 0, -2] = true := by decide +kernel
theorem subd18_0_217 : subd18_0 [2, 0, -1] = true := by decide +kernel
theorem subd18_0_218 : subd18_0 [2, 0, 0] = true := by decide +kernel
theorem subd18_0_219 : subd18_0 [2, 0, 1] = true := by decide +kernel
theorem subd18_0_220 : subd18_0 [2, 0, 2] = true := by decide +kernel
theorem subd18_0_221 : subd18_0 [2, 0, 3] = true := by decide +kernel
theorem subd18_0_222 : subd18_0 [2, 0, 4] = true := by decide +kernel
theorem subd18_0_223 : subd18_0 [2, 0, 5] = true := by decide +kernel
theorem sbd18_0_6 : ∀ q ∈ blkd18_0_6, subd18_0 q = true := by
  unfold blkd18_0_6
  exact List.forall_mem_cons.2 ⟨subd18_0_192, List.forall_mem_cons.2 ⟨subd18_0_193, List.forall_mem_cons.2 ⟨subd18_0_194, List.forall_mem_cons.2 ⟨subd18_0_195, List.forall_mem_cons.2 ⟨subd18_0_196, List.forall_mem_cons.2 ⟨subd18_0_197, List.forall_mem_cons.2 ⟨subd18_0_198, List.forall_mem_cons.2 ⟨subd18_0_199, List.forall_mem_cons.2 ⟨subd18_0_200, List.forall_mem_cons.2 ⟨subd18_0_201, List.forall_mem_cons.2 ⟨subd18_0_202, List.forall_mem_cons.2 ⟨subd18_0_203, List.forall_mem_cons.2 ⟨subd18_0_204, List.forall_mem_cons.2 ⟨subd18_0_205, List.forall_mem_cons.2 ⟨subd18_0_206, List.forall_mem_cons.2 ⟨subd18_0_207, List.forall_mem_cons.2 ⟨subd18_0_208, List.forall_mem_cons.2 ⟨subd18_0_209, List.forall_mem_cons.2 ⟨subd18_0_210, List.forall_mem_cons.2 ⟨subd18_0_211, List.forall_mem_cons.2 ⟨subd18_0_212, List.forall_mem_cons.2 ⟨subd18_0_213, List.forall_mem_cons.2 ⟨subd18_0_214, List.forall_mem_cons.2 ⟨subd18_0_215, List.forall_mem_cons.2 ⟨subd18_0_216, List.forall_mem_cons.2 ⟨subd18_0_217, List.forall_mem_cons.2 ⟨subd18_0_218, List.forall_mem_cons.2 ⟨subd18_0_219, List.forall_mem_cons.2 ⟨subd18_0_220, List.forall_mem_cons.2 ⟨subd18_0_221, List.forall_mem_cons.2 ⟨subd18_0_222, List.forall_mem_cons.2 ⟨subd18_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_224 : subd18_0 [2, 1] = true := by decide +kernel
theorem sbd18_0_7 : ∀ q ∈ blkd18_0_7, subd18_0 q = true := by
  unfold blkd18_0_7
  exact List.forall_mem_cons.2 ⟨subd18_0_224, List.forall_mem_nil _⟩
theorem ld_okd18_1 : ldCheck G d18_1.U d18_1.ms ldd18_1 = true := by decide +kernel
theorem pre_okd18_1 : subPre G cell18 d18_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C131
