import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_nil _⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [-2] = true := by decide +kernel
theorem subd7_2_1 : subd7_2 [-1] = true := by decide +kernel
theorem subd7_2_2 : subd7_2 [0] = true := by decide +kernel
theorem subd7_2_3 : subd7_2 [1] = true := by decide +kernel
theorem subd7_2_4 : subd7_2 [2] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_cons.2 ⟨subd7_2_1, List.forall_mem_cons.2 ⟨subd7_2_2, List.forall_mem_cons.2 ⟨subd7_2_3, List.forall_mem_cons.2 ⟨subd7_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-2, -2] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [-2, -1] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [-2, 0] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [-2, 1] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [-1, -3] = true := by decide +kernel
theorem subd7_3_5 : subd7_3 [-1, -2] = true := by decide +kernel
theorem subd7_3_6 : subd7_3 [-1, -1, -7] = true := by decide +kernel
theorem subd7_3_7 : subd7_3 [-1, -1, -6] = true := by decide +kernel
theorem subd7_3_8 : subd7_3 [-1, -1, -5] = true := by decide +kernel
theorem subd7_3_9 : subd7_3 [-1, -1, -4] = true := by decide +kernel
theorem subd7_3_10 : subd7_3 [-1, -1, -3] = true := by decide +kernel
theorem subd7_3_11 : subd7_3 [-1, -1, -2] = true := by decide +kernel
theorem subd7_3_12 : subd7_3 [-1, -1, -1] = true := by decide +kernel
theorem subd7_3_13 : subd7_3 [-1, -1, 0] = true := by decide +kernel
theorem subd7_3_14 : subd7_3 [-1, -1, 1] = true := by decide +kernel
theorem subd7_3_15 : subd7_3 [-1, -1, 2] = true := by decide +kernel
theorem subd7_3_16 : subd7_3 [-1, -1, 3] = true := by decide +kernel
theorem subd7_3_17 : subd7_3 [-1, -1, 4] = true := by decide +kernel
theorem subd7_3_18 : subd7_3 [-1, -1, 5] = true := by decide +kernel
theorem subd7_3_19 : subd7_3 [-1, -1, 6] = true := by decide +kernel
theorem subd7_3_20 : subd7_3 [-1, -1, 7] = true := by decide +kernel
theorem subd7_3_21 : subd7_3 [-1, 0, -8] = true := by decide +kernel
theorem subd7_3_22 : subd7_3 [-1, 0, -7] = true := by decide +kernel
theorem subd7_3_23 : subd7_3 [-1, 0, -6] = true := by decide +kernel
theorem subd7_3_24 : subd7_3 [-1, 0, -5] = true := by decide +kernel
theorem subd7_3_25 : subd7_3 [-1, 0, -4] = true := by decide +kernel
theorem subd7_3_26 : subd7_3 [-1, 0, -3] = true := by decide +kernel
theorem subd7_3_27 : subd7_3 [-1, 0, -2] = true := by decide +kernel
theorem subd7_3_28 : subd7_3 [-1, 0, -1] = true := by decide +kernel
theorem subd7_3_29 : subd7_3 [-1, 0, 0] = true := by decide +kernel
theorem subd7_3_30 : subd7_3 [-1, 0, 1] = true := by decide +kernel
theorem subd7_3_31 : subd7_3 [-1, 0, 2] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_cons.2 ⟨subd7_3_5, List.forall_mem_cons.2 ⟨subd7_3_6, List.forall_mem_cons.2 ⟨subd7_3_7, List.forall_mem_cons.2 ⟨subd7_3_8, List.forall_mem_cons.2 ⟨subd7_3_9, List.forall_mem_cons.2 ⟨subd7_3_10, List.forall_mem_cons.2 ⟨subd7_3_11, List.forall_mem_cons.2 ⟨subd7_3_12, List.forall_mem_cons.2 ⟨subd7_3_13, List.forall_mem_cons.2 ⟨subd7_3_14, List.forall_mem_cons.2 ⟨subd7_3_15, List.forall_mem_cons.2 ⟨subd7_3_16, List.forall_mem_cons.2 ⟨subd7_3_17, List.forall_mem_cons.2 ⟨subd7_3_18, List.forall_mem_cons.2 ⟨subd7_3_19, List.forall_mem_cons.2 ⟨subd7_3_20, List.forall_mem_cons.2 ⟨subd7_3_21, List.forall_mem_cons.2 ⟨subd7_3_22, List.forall_mem_cons.2 ⟨subd7_3_23, List.forall_mem_cons.2 ⟨subd7_3_24, List.forall_mem_cons.2 ⟨subd7_3_25, List.forall_mem_cons.2 ⟨subd7_3_26, List.forall_mem_cons.2 ⟨subd7_3_27, List.forall_mem_cons.2 ⟨subd7_3_28, List.forall_mem_cons.2 ⟨subd7_3_29, List.forall_mem_cons.2 ⟨subd7_3_30, List.forall_mem_cons.2 ⟨subd7_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_32 : subd7_3 [-1, 0, 3] = true := by decide +kernel
theorem subd7_3_33 : subd7_3 [-1, 0, 4] = true := by decide +kernel
theorem subd7_3_34 : subd7_3 [-1, 0, 5] = true := by decide +kernel
theorem subd7_3_35 : subd7_3 [-1, 0, 6] = true := by decide +kernel
theorem subd7_3_36 : subd7_3 [-1, 0, 7] = true := by decide +kernel
theorem subd7_3_37 : subd7_3 [-1, 0, 8] = true := by decide +kernel
theorem subd7_3_38 : subd7_3 [-1, 1, -7] = true := by decide +kernel
theorem subd7_3_39 : subd7_3 [-1, 1, -6] = true := by decide +kernel
theorem subd7_3_40 : subd7_3 [-1, 1, -5] = true := by decide +kernel
theorem subd7_3_41 : subd7_3 [-1, 1, -4] = true := by decide +kernel
theorem subd7_3_42 : subd7_3 [-1, 1, -3] = true := by decide +kernel
theorem subd7_3_43 : subd7_3 [-1, 1, -2] = true := by decide +kernel
theorem subd7_3_44 : subd7_3 [-1, 1, -1] = true := by decide +kernel
theorem subd7_3_45 : subd7_3 [-1, 1, 0] = true := by decide +kernel
theorem subd7_3_46 : subd7_3 [-1, 1, 1] = true := by decide +kernel
theorem subd7_3_47 : subd7_3 [-1, 1, 2] = true := by decide +kernel
theorem subd7_3_48 : subd7_3 [-1, 1, 3] = true := by decide +kernel
theorem subd7_3_49 : subd7_3 [-1, 1, 4] = true := by decide +kernel
theorem subd7_3_50 : subd7_3 [-1, 1, 5] = true := by decide +kernel
theorem subd7_3_51 : subd7_3 [-1, 1, 6] = true := by decide +kernel
theorem subd7_3_52 : subd7_3 [-1, 1, 7] = true := by decide +kernel
theorem subd7_3_53 : subd7_3 [-1, 2] = true := by decide +kernel
theorem subd7_3_54 : subd7_3 [0, -3] = true := by decide +kernel
theorem subd7_3_55 : subd7_3 [0, -2] = true := by decide +kernel
theorem subd7_3_56 : subd7_3 [0, -1, -8] = true := by decide +kernel
theorem subd7_3_57 : subd7_3 [0, -1, -7] = true := by decide +kernel
theorem subd7_3_58 : subd7_3 [0, -1, -6] = true := by decide +kernel
theorem subd7_3_59 : subd7_3 [0, -1, -5] = true := by decide +kernel
theorem subd7_3_60 : subd7_3 [0, -1, -4] = true := by decide +kernel
theorem subd7_3_61 : subd7_3 [0, -1, -3] = true := by decide +kernel
theorem subd7_3_62 : subd7_3 [0, -1, -2] = true := by decide +kernel
theorem subd7_3_63 : subd7_3 [0, -1, -1] = true := by decide +kernel
theorem sbd7_3_1 : ∀ q ∈ blkd7_3_1, subd7_3 q = true := by
  unfold blkd7_3_1
  exact List.forall_mem_cons.2 ⟨subd7_3_32, List.forall_mem_cons.2 ⟨subd7_3_33, List.forall_mem_cons.2 ⟨subd7_3_34, List.forall_mem_cons.2 ⟨subd7_3_35, List.forall_mem_cons.2 ⟨subd7_3_36, List.forall_mem_cons.2 ⟨subd7_3_37, List.forall_mem_cons.2 ⟨subd7_3_38, List.forall_mem_cons.2 ⟨subd7_3_39, List.forall_mem_cons.2 ⟨subd7_3_40, List.forall_mem_cons.2 ⟨subd7_3_41, List.forall_mem_cons.2 ⟨subd7_3_42, List.forall_mem_cons.2 ⟨subd7_3_43, List.forall_mem_cons.2 ⟨subd7_3_44, List.forall_mem_cons.2 ⟨subd7_3_45, List.forall_mem_cons.2 ⟨subd7_3_46, List.forall_mem_cons.2 ⟨subd7_3_47, List.forall_mem_cons.2 ⟨subd7_3_48, List.forall_mem_cons.2 ⟨subd7_3_49, List.forall_mem_cons.2 ⟨subd7_3_50, List.forall_mem_cons.2 ⟨subd7_3_51, List.forall_mem_cons.2 ⟨subd7_3_52, List.forall_mem_cons.2 ⟨subd7_3_53, List.forall_mem_cons.2 ⟨subd7_3_54, List.forall_mem_cons.2 ⟨subd7_3_55, List.forall_mem_cons.2 ⟨subd7_3_56, List.forall_mem_cons.2 ⟨subd7_3_57, List.forall_mem_cons.2 ⟨subd7_3_58, List.forall_mem_cons.2 ⟨subd7_3_59, List.forall_mem_cons.2 ⟨subd7_3_60, List.forall_mem_cons.2 ⟨subd7_3_61, List.forall_mem_cons.2 ⟨subd7_3_62, List.forall_mem_cons.2 ⟨subd7_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_64 : subd7_3 [0, -1, 0] = true := by decide +kernel
theorem subd7_3_65 : subd7_3 [0, -1, 1] = true := by decide +kernel
theorem subd7_3_66 : subd7_3 [0, -1, 2] = true := by decide +kernel
theorem subd7_3_67 : subd7_3 [0, -1, 3] = true := by decide +kernel
theorem subd7_3_68 : subd7_3 [0, -1, 4] = true := by decide +kernel
theorem subd7_3_69 : subd7_3 [0, -1, 5] = true := by decide +kernel
theorem subd7_3_70 : subd7_3 [0, -1, 6] = true := by decide +kernel
theorem subd7_3_71 : subd7_3 [0, -1, 7] = true := by decide +kernel
theorem subd7_3_72 : subd7_3 [0, -1, 8] = true := by decide +kernel
theorem subd7_3_73 : subd7_3 [0, 0, -9] = true := by decide +kernel
theorem subd7_3_74 : subd7_3 [0, 0, -8] = true := by decide +kernel
theorem subd7_3_75 : subd7_3 [0, 0, -7] = true := by decide +kernel
theorem subd7_3_76 : subd7_3 [0, 0, -6] = true := by decide +kernel
theorem subd7_3_77 : subd7_3 [0, 0, -5] = true := by decide +kernel
theorem subd7_3_78 : subd7_3 [0, 0, -4] = true := by decide +kernel
theorem subd7_3_79 : subd7_3 [0, 0, -3] = true := by decide +kernel
theorem subd7_3_80 : subd7_3 [0, 0, -2] = true := by decide +kernel
theorem subd7_3_81 : subd7_3 [0, 0, -1] = true := by decide +kernel
theorem subd7_3_82 : subd7_3 [0, 0, 0] = true := by decide +kernel
theorem subd7_3_83 : subd7_3 [0, 0, 1] = true := by decide +kernel
theorem subd7_3_84 : subd7_3 [0, 0, 2] = true := by decide +kernel
theorem subd7_3_85 : subd7_3 [0, 0, 3] = true := by decide +kernel
theorem subd7_3_86 : subd7_3 [0, 0, 4] = true := by decide +kernel
theorem subd7_3_87 : subd7_3 [0, 0, 5] = true := by decide +kernel
theorem subd7_3_88 : subd7_3 [0, 0, 6] = true := by decide +kernel
theorem subd7_3_89 : subd7_3 [0, 0, 7] = true := by decide +kernel
theorem subd7_3_90 : subd7_3 [0, 0, 8] = true := by decide +kernel
theorem subd7_3_91 : subd7_3 [0, 1, -9] = true := by decide +kernel
theorem subd7_3_92 : subd7_3 [0, 1, -8] = true := by decide +kernel
theorem subd7_3_93 : subd7_3 [0, 1, -7] = true := by decide +kernel
theorem subd7_3_94 : subd7_3 [0, 1, -6] = true := by decide +kernel
theorem subd7_3_95 : subd7_3 [0, 1, -5] = true := by decide +kernel
theorem sbd7_3_2 : ∀ q ∈ blkd7_3_2, subd7_3 q = true := by
  unfold blkd7_3_2
  exact List.forall_mem_cons.2 ⟨subd7_3_64, List.forall_mem_cons.2 ⟨subd7_3_65, List.forall_mem_cons.2 ⟨subd7_3_66, List.forall_mem_cons.2 ⟨subd7_3_67, List.forall_mem_cons.2 ⟨subd7_3_68, List.forall_mem_cons.2 ⟨subd7_3_69, List.forall_mem_cons.2 ⟨subd7_3_70, List.forall_mem_cons.2 ⟨subd7_3_71, List.forall_mem_cons.2 ⟨subd7_3_72, List.forall_mem_cons.2 ⟨subd7_3_73, List.forall_mem_cons.2 ⟨subd7_3_74, List.forall_mem_cons.2 ⟨subd7_3_75, List.forall_mem_cons.2 ⟨subd7_3_76, List.forall_mem_cons.2 ⟨subd7_3_77, List.forall_mem_cons.2 ⟨subd7_3_78, List.forall_mem_cons.2 ⟨subd7_3_79, List.forall_mem_cons.2 ⟨subd7_3_80, List.forall_mem_cons.2 ⟨subd7_3_81, List.forall_mem_cons.2 ⟨subd7_3_82, List.forall_mem_cons.2 ⟨subd7_3_83, List.forall_mem_cons.2 ⟨subd7_3_84, List.forall_mem_cons.2 ⟨subd7_3_85, List.forall_mem_cons.2 ⟨subd7_3_86, List.forall_mem_cons.2 ⟨subd7_3_87, List.forall_mem_cons.2 ⟨subd7_3_88, List.forall_mem_cons.2 ⟨subd7_3_89, List.forall_mem_cons.2 ⟨subd7_3_90, List.forall_mem_cons.2 ⟨subd7_3_91, List.forall_mem_cons.2 ⟨subd7_3_92, List.forall_mem_cons.2 ⟨subd7_3_93, List.forall_mem_cons.2 ⟨subd7_3_94, List.forall_mem_cons.2 ⟨subd7_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_96 : subd7_3 [0, 1, -4] = true := by decide +kernel
theorem subd7_3_97 : subd7_3 [0, 1, -3] = true := by decide +kernel
theorem subd7_3_98 : subd7_3 [0, 1, -2] = true := by decide +kernel
theorem subd7_3_99 : subd7_3 [0, 1, -1] = true := by decide +kernel
theorem subd7_3_100 : subd7_3 [0, 1, 0] = true := by decide +kernel
theorem subd7_3_101 : subd7_3 [0, 1, 1] = true := by decide +kernel
theorem subd7_3_102 : subd7_3 [0, 1, 2] = true := by decide +kernel
theorem subd7_3_103 : subd7_3 [0, 1, 3] = true := by decide +kernel
theorem subd7_3_104 : subd7_3 [0, 1, 4] = true := by decide +kernel
theorem subd7_3_105 : subd7_3 [0, 1, 5] = true := by decide +kernel
theorem subd7_3_106 : subd7_3 [0, 1, 6] = true := by decide +kernel
theorem subd7_3_107 : subd7_3 [0, 1, 7] = true := by decide +kernel
theorem subd7_3_108 : subd7_3 [0, 2] = true := by decide +kernel
theorem subd7_3_109 : subd7_3 [1, -3] = true := by decide +kernel
theorem subd7_3_110 : subd7_3 [1, -2] = true := by decide +kernel
theorem subd7_3_111 : subd7_3 [1, -1, -8] = true := by decide +kernel
theorem subd7_3_112 : subd7_3 [1, -1, -7] = true := by decide +kernel
theorem subd7_3_113 : subd7_3 [1, -1, -6] = true := by decide +kernel
theorem subd7_3_114 : subd7_3 [1, -1, -5] = true := by decide +kernel
theorem subd7_3_115 : subd7_3 [1, -1, -4] = true := by decide +kernel
theorem subd7_3_116 : subd7_3 [1, -1, -3] = true := by decide +kernel
theorem subd7_3_117 : subd7_3 [1, -1, -2] = true := by decide +kernel
theorem subd7_3_118 : subd7_3 [1, -1, -1] = true := by decide +kernel
theorem subd7_3_119 : subd7_3 [1, -1, 0] = true := by decide +kernel
theorem subd7_3_120 : subd7_3 [1, -1, 1] = true := by decide +kernel
theorem subd7_3_121 : subd7_3 [1, -1, 2] = true := by decide +kernel
theorem subd7_3_122 : subd7_3 [1, -1, 3] = true := by decide +kernel
theorem subd7_3_123 : subd7_3 [1, -1, 4] = true := by decide +kernel
theorem subd7_3_124 : subd7_3 [1, -1, 5] = true := by decide +kernel
theorem subd7_3_125 : subd7_3 [1, -1, 6] = true := by decide +kernel
theorem subd7_3_126 : subd7_3 [1, 0, -9] = true := by decide +kernel
theorem subd7_3_127 : subd7_3 [1, 0, -8] = true := by decide +kernel
theorem sbd7_3_3 : ∀ q ∈ blkd7_3_3, subd7_3 q = true := by
  unfold blkd7_3_3
  exact List.forall_mem_cons.2 ⟨subd7_3_96, List.forall_mem_cons.2 ⟨subd7_3_97, List.forall_mem_cons.2 ⟨subd7_3_98, List.forall_mem_cons.2 ⟨subd7_3_99, List.forall_mem_cons.2 ⟨subd7_3_100, List.forall_mem_cons.2 ⟨subd7_3_101, List.forall_mem_cons.2 ⟨subd7_3_102, List.forall_mem_cons.2 ⟨subd7_3_103, List.forall_mem_cons.2 ⟨subd7_3_104, List.forall_mem_cons.2 ⟨subd7_3_105, List.forall_mem_cons.2 ⟨subd7_3_106, List.forall_mem_cons.2 ⟨subd7_3_107, List.forall_mem_cons.2 ⟨subd7_3_108, List.forall_mem_cons.2 ⟨subd7_3_109, List.forall_mem_cons.2 ⟨subd7_3_110, List.forall_mem_cons.2 ⟨subd7_3_111, List.forall_mem_cons.2 ⟨subd7_3_112, List.forall_mem_cons.2 ⟨subd7_3_113, List.forall_mem_cons.2 ⟨subd7_3_114, List.forall_mem_cons.2 ⟨subd7_3_115, List.forall_mem_cons.2 ⟨subd7_3_116, List.forall_mem_cons.2 ⟨subd7_3_117, List.forall_mem_cons.2 ⟨subd7_3_118, List.forall_mem_cons.2 ⟨subd7_3_119, List.forall_mem_cons.2 ⟨subd7_3_120, List.forall_mem_cons.2 ⟨subd7_3_121, List.forall_mem_cons.2 ⟨subd7_3_122, List.forall_mem_cons.2 ⟨subd7_3_123, List.forall_mem_cons.2 ⟨subd7_3_124, List.forall_mem_cons.2 ⟨subd7_3_125, List.forall_mem_cons.2 ⟨subd7_3_126, List.forall_mem_cons.2 ⟨subd7_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_128 : subd7_3 [1, 0, -7] = true := by decide +kernel
theorem subd7_3_129 : subd7_3 [1, 0, -6] = true := by decide +kernel
theorem subd7_3_130 : subd7_3 [1, 0, -5] = true := by decide +kernel
theorem subd7_3_131 : subd7_3 [1, 0, -4] = true := by decide +kernel
theorem subd7_3_132 : subd7_3 [1, 0, -3] = true := by decide +kernel
theorem subd7_3_133 : subd7_3 [1, 0, -2] = true := by decide +kernel
theorem subd7_3_134 : subd7_3 [1, 0, -1] = true := by decide +kernel
theorem subd7_3_135 : subd7_3 [1, 0, 0] = true := by decide +kernel
theorem subd7_3_136 : subd7_3 [1, 0, 1] = true := by decide +kernel
theorem subd7_3_137 : subd7_3 [1, 0, 2] = true := by decide +kernel
theorem subd7_3_138 : subd7_3 [1, 0, 3] = true := by decide +kernel
theorem subd7_3_139 : subd7_3 [1, 0, 4] = true := by decide +kernel
theorem subd7_3_140 : subd7_3 [1, 0, 5] = true := by decide +kernel
theorem subd7_3_141 : subd7_3 [1, 0, 6] = true := by decide +kernel
theorem subd7_3_142 : subd7_3 [1, 0, 7] = true := by decide +kernel
theorem subd7_3_143 : subd7_3 [1, 1, -8] = true := by decide +kernel
theorem subd7_3_144 : subd7_3 [1, 1, -7] = true := by decide +kernel
theorem subd7_3_145 : subd7_3 [1, 1, -6] = true := by decide +kernel
theorem subd7_3_146 : subd7_3 [1, 1, -5] = true := by decide +kernel
theorem subd7_3_147 : subd7_3 [1, 1, -4] = true := by decide +kernel
theorem subd7_3_148 : subd7_3 [1, 1, -3] = true := by decide +kernel
theorem subd7_3_149 : subd7_3 [1, 1, -2] = true := by decide +kernel
theorem subd7_3_150 : subd7_3 [1, 1, -1] = true := by decide +kernel
theorem subd7_3_151 : subd7_3 [1, 1, 0] = true := by decide +kernel
theorem subd7_3_152 : subd7_3 [1, 1, 1] = true := by decide +kernel
theorem subd7_3_153 : subd7_3 [1, 1, 2] = true := by decide +kernel
theorem subd7_3_154 : subd7_3 [1, 1, 3] = true := by decide +kernel
theorem subd7_3_155 : subd7_3 [1, 1, 4] = true := by decide +kernel
theorem subd7_3_156 : subd7_3 [1, 1, 5] = true := by decide +kernel
theorem subd7_3_157 : subd7_3 [1, 1, 6] = true := by decide +kernel
theorem subd7_3_158 : subd7_3 [1, 2] = true := by decide +kernel
theorem subd7_3_159 : subd7_3 [2, -2] = true := by decide +kernel
theorem sbd7_3_4 : ∀ q ∈ blkd7_3_4, subd7_3 q = true := by
  unfold blkd7_3_4
  exact List.forall_mem_cons.2 ⟨subd7_3_128, List.forall_mem_cons.2 ⟨subd7_3_129, List.forall_mem_cons.2 ⟨subd7_3_130, List.forall_mem_cons.2 ⟨subd7_3_131, List.forall_mem_cons.2 ⟨subd7_3_132, List.forall_mem_cons.2 ⟨subd7_3_133, List.forall_mem_cons.2 ⟨subd7_3_134, List.forall_mem_cons.2 ⟨subd7_3_135, List.forall_mem_cons.2 ⟨subd7_3_136, List.forall_mem_cons.2 ⟨subd7_3_137, List.forall_mem_cons.2 ⟨subd7_3_138, List.forall_mem_cons.2 ⟨subd7_3_139, List.forall_mem_cons.2 ⟨subd7_3_140, List.forall_mem_cons.2 ⟨subd7_3_141, List.forall_mem_cons.2 ⟨subd7_3_142, List.forall_mem_cons.2 ⟨subd7_3_143, List.forall_mem_cons.2 ⟨subd7_3_144, List.forall_mem_cons.2 ⟨subd7_3_145, List.forall_mem_cons.2 ⟨subd7_3_146, List.forall_mem_cons.2 ⟨subd7_3_147, List.forall_mem_cons.2 ⟨subd7_3_148, List.forall_mem_cons.2 ⟨subd7_3_149, List.forall_mem_cons.2 ⟨subd7_3_150, List.forall_mem_cons.2 ⟨subd7_3_151, List.forall_mem_cons.2 ⟨subd7_3_152, List.forall_mem_cons.2 ⟨subd7_3_153, List.forall_mem_cons.2 ⟨subd7_3_154, List.forall_mem_cons.2 ⟨subd7_3_155, List.forall_mem_cons.2 ⟨subd7_3_156, List.forall_mem_cons.2 ⟨subd7_3_157, List.forall_mem_cons.2 ⟨subd7_3_158, List.forall_mem_cons.2 ⟨subd7_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_160 : subd7_3 [2, -1] = true := by decide +kernel
theorem subd7_3_161 : subd7_3 [2, 0] = true := by decide +kernel
theorem subd7_3_162 : subd7_3 [2, 1] = true := by decide +kernel
theorem sbd7_3_5 : ∀ q ∈ blkd7_3_5, subd7_3 q = true := by
  unfold blkd7_3_5
  exact List.forall_mem_cons.2 ⟨subd7_3_160, List.forall_mem_cons.2 ⟨subd7_3_161, List.forall_mem_cons.2 ⟨subd7_3_162, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd7_4 : ldCheck G d7_4.U d7_4.ms ldd7_4 = true := by decide +kernel
theorem pre_okd7_4 : subPre G cell7 d7_4 = true := by decide +kernel
theorem subd7_4_0 : subd7_4 [-2, -2] = true := by decide +kernel
theorem subd7_4_1 : subd7_4 [-2, -1] = true := by decide +kernel
theorem subd7_4_2 : subd7_4 [-2, 0] = true := by decide +kernel
theorem subd7_4_3 : subd7_4 [-2, 1] = true := by decide +kernel
theorem subd7_4_4 : subd7_4 [-2, 2] = true := by decide +kernel
theorem subd7_4_5 : subd7_4 [-2, 3] = true := by decide +kernel
theorem subd7_4_6 : subd7_4 [-1, -3] = true := by decide +kernel
theorem subd7_4_7 : subd7_4 [-1, -2] = true := by decide +kernel
theorem subd7_4_8 : subd7_4 [-1, -1] = true := by decide +kernel
theorem subd7_4_9 : subd7_4 [-1, 0] = true := by decide +kernel
theorem subd7_4_10 : subd7_4 [-1, 1] = true := by decide +kernel
theorem subd7_4_11 : subd7_4 [-1, 2] = true := by decide +kernel
theorem subd7_4_12 : subd7_4 [-1, 3] = true := by decide +kernel
theorem subd7_4_13 : subd7_4 [0, -4] = true := by decide +kernel
theorem subd7_4_14 : subd7_4 [0, -3] = true := by decide +kernel
theorem subd7_4_15 : subd7_4 [0, -2] = true := by decide +kernel
theorem subd7_4_16 : subd7_4 [0, -1] = true := by decide +kernel
theorem subd7_4_17 : subd7_4 [0, 0] = true := by decide +kernel
theorem subd7_4_18 : subd7_4 [0, 1] = true := by decide +kernel
theorem subd7_4_19 : subd7_4 [0, 2] = true := by decide +kernel
theorem subd7_4_20 : subd7_4 [0, 3] = true := by decide +kernel
theorem subd7_4_21 : subd7_4 [1, -4] = true := by decide +kernel
theorem subd7_4_22 : subd7_4 [1, -3] = true := by decide +kernel
theorem subd7_4_23 : subd7_4 [1, -2] = true := by decide +kernel
theorem subd7_4_24 : subd7_4 [1, -1] = true := by decide +kernel
theorem subd7_4_25 : subd7_4 [1, 0] = true := by decide +kernel
theorem subd7_4_26 : subd7_4 [1, 1] = true := by decide +kernel
theorem subd7_4_27 : subd7_4 [1, 2] = true := by decide +kernel
theorem subd7_4_28 : subd7_4 [2, -4] = true := by decide +kernel
theorem subd7_4_29 : subd7_4 [2, -3] = true := by decide +kernel
theorem subd7_4_30 : subd7_4 [2, -2] = true := by decide +kernel
theorem subd7_4_31 : subd7_4 [2, -1] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_cons.2 ⟨subd7_4_1, List.forall_mem_cons.2 ⟨subd7_4_2, List.forall_mem_cons.2 ⟨subd7_4_3, List.forall_mem_cons.2 ⟨subd7_4_4, List.forall_mem_cons.2 ⟨subd7_4_5, List.forall_mem_cons.2 ⟨subd7_4_6, List.forall_mem_cons.2 ⟨subd7_4_7, List.forall_mem_cons.2 ⟨subd7_4_8, List.forall_mem_cons.2 ⟨subd7_4_9, List.forall_mem_cons.2 ⟨subd7_4_10, List.forall_mem_cons.2 ⟨subd7_4_11, List.forall_mem_cons.2 ⟨subd7_4_12, List.forall_mem_cons.2 ⟨subd7_4_13, List.forall_mem_cons.2 ⟨subd7_4_14, List.forall_mem_cons.2 ⟨subd7_4_15, List.forall_mem_cons.2 ⟨subd7_4_16, List.forall_mem_cons.2 ⟨subd7_4_17, List.forall_mem_cons.2 ⟨subd7_4_18, List.forall_mem_cons.2 ⟨subd7_4_19, List.forall_mem_cons.2 ⟨subd7_4_20, List.forall_mem_cons.2 ⟨subd7_4_21, List.forall_mem_cons.2 ⟨subd7_4_22, List.forall_mem_cons.2 ⟨subd7_4_23, List.forall_mem_cons.2 ⟨subd7_4_24, List.forall_mem_cons.2 ⟨subd7_4_25, List.forall_mem_cons.2 ⟨subd7_4_26, List.forall_mem_cons.2 ⟨subd7_4_27, List.forall_mem_cons.2 ⟨subd7_4_28, List.forall_mem_cons.2 ⟨subd7_4_29, List.forall_mem_cons.2 ⟨subd7_4_30, List.forall_mem_cons.2 ⟨subd7_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C140
