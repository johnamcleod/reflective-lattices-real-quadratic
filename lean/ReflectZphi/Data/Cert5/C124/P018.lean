import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_7_96 : subd6_7 [2, -3] = true := by decide +kernel
theorem subd6_7_97 : subd6_7 [2, -2] = true := by decide +kernel
theorem subd6_7_98 : subd6_7 [2, -1] = true := by decide +kernel
theorem subd6_7_99 : subd6_7 [2, 0] = true := by decide +kernel
theorem subd6_7_100 : subd6_7 [2, 1] = true := by decide +kernel
theorem subd6_7_101 : subd6_7 [2, 2] = true := by decide +kernel
theorem subd6_7_102 : subd6_7 [2, 3] = true := by decide +kernel
theorem subd6_7_103 : subd6_7 [2, 4] = true := by decide +kernel
theorem subd6_7_104 : subd6_7 [2, 5] = true := by decide +kernel
theorem subd6_7_105 : subd6_7 [2, 6] = true := by decide +kernel
theorem subd6_7_106 : subd6_7 [2, 7] = true := by decide +kernel
theorem subd6_7_107 : subd6_7 [3, -5] = true := by decide +kernel
theorem subd6_7_108 : subd6_7 [3, -4] = true := by decide +kernel
theorem subd6_7_109 : subd6_7 [3, -3] = true := by decide +kernel
theorem subd6_7_110 : subd6_7 [3, -2] = true := by decide +kernel
theorem subd6_7_111 : subd6_7 [3, -1] = true := by decide +kernel
theorem subd6_7_112 : subd6_7 [3, 0] = true := by decide +kernel
theorem subd6_7_113 : subd6_7 [3, 1] = true := by decide +kernel
theorem subd6_7_114 : subd6_7 [3, 2] = true := by decide +kernel
theorem subd6_7_115 : subd6_7 [3, 3] = true := by decide +kernel
theorem subd6_7_116 : subd6_7 [3, 4] = true := by decide +kernel
theorem subd6_7_117 : subd6_7 [3, 5] = true := by decide +kernel
theorem subd6_7_118 : subd6_7 [3, 6] = true := by decide +kernel
theorem subd6_7_119 : subd6_7 [3, 7] = true := by decide +kernel
theorem subd6_7_120 : subd6_7 [4, -4] = true := by decide +kernel
theorem subd6_7_121 : subd6_7 [4, -3] = true := by decide +kernel
theorem subd6_7_122 : subd6_7 [4, -2] = true := by decide +kernel
theorem subd6_7_123 : subd6_7 [4, -1] = true := by decide +kernel
theorem subd6_7_124 : subd6_7 [4, 0] = true := by decide +kernel
theorem subd6_7_125 : subd6_7 [4, 1] = true := by decide +kernel
theorem subd6_7_126 : subd6_7 [4, 2] = true := by decide +kernel
theorem subd6_7_127 : subd6_7 [4, 3] = true := by decide +kernel
theorem sbd6_7_3 : ∀ q ∈ blkd6_7_3, subd6_7 q = true := by
  unfold blkd6_7_3
  exact List.forall_mem_cons.2 ⟨subd6_7_96, List.forall_mem_cons.2 ⟨subd6_7_97, List.forall_mem_cons.2 ⟨subd6_7_98, List.forall_mem_cons.2 ⟨subd6_7_99, List.forall_mem_cons.2 ⟨subd6_7_100, List.forall_mem_cons.2 ⟨subd6_7_101, List.forall_mem_cons.2 ⟨subd6_7_102, List.forall_mem_cons.2 ⟨subd6_7_103, List.forall_mem_cons.2 ⟨subd6_7_104, List.forall_mem_cons.2 ⟨subd6_7_105, List.forall_mem_cons.2 ⟨subd6_7_106, List.forall_mem_cons.2 ⟨subd6_7_107, List.forall_mem_cons.2 ⟨subd6_7_108, List.forall_mem_cons.2 ⟨subd6_7_109, List.forall_mem_cons.2 ⟨subd6_7_110, List.forall_mem_cons.2 ⟨subd6_7_111, List.forall_mem_cons.2 ⟨subd6_7_112, List.forall_mem_cons.2 ⟨subd6_7_113, List.forall_mem_cons.2 ⟨subd6_7_114, List.forall_mem_cons.2 ⟨subd6_7_115, List.forall_mem_cons.2 ⟨subd6_7_116, List.forall_mem_cons.2 ⟨subd6_7_117, List.forall_mem_cons.2 ⟨subd6_7_118, List.forall_mem_cons.2 ⟨subd6_7_119, List.forall_mem_cons.2 ⟨subd6_7_120, List.forall_mem_cons.2 ⟨subd6_7_121, List.forall_mem_cons.2 ⟨subd6_7_122, List.forall_mem_cons.2 ⟨subd6_7_123, List.forall_mem_cons.2 ⟨subd6_7_124, List.forall_mem_cons.2 ⟨subd6_7_125, List.forall_mem_cons.2 ⟨subd6_7_126, List.forall_mem_cons.2 ⟨subd6_7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_7_128 : subd6_7 [4, 4] = true := by decide +kernel
theorem subd6_7_129 : subd6_7 [4, 5] = true := by decide +kernel
theorem subd6_7_130 : subd6_7 [4, 6] = true := by decide +kernel
theorem subd6_7_131 : subd6_7 [4, 7] = true := by decide +kernel
theorem subd6_7_132 : subd6_7 [5, -2] = true := by decide +kernel
theorem subd6_7_133 : subd6_7 [5, -1] = true := by decide +kernel
theorem subd6_7_134 : subd6_7 [5, 0] = true := by decide +kernel
theorem subd6_7_135 : subd6_7 [5, 1] = true := by decide +kernel
theorem subd6_7_136 : subd6_7 [5, 2] = true := by decide +kernel
theorem subd6_7_137 : subd6_7 [5, 3] = true := by decide +kernel
theorem subd6_7_138 : subd6_7 [5, 4] = true := by decide +kernel
theorem subd6_7_139 : subd6_7 [5, 5] = true := by decide +kernel
theorem subd6_7_140 : subd6_7 [5, 6] = true := by decide +kernel
theorem subd6_7_141 : subd6_7 [6] = true := by decide +kernel
theorem sbd6_7_4 : ∀ q ∈ blkd6_7_4, subd6_7 q = true := by
  unfold blkd6_7_4
  exact List.forall_mem_cons.2 ⟨subd6_7_128, List.forall_mem_cons.2 ⟨subd6_7_129, List.forall_mem_cons.2 ⟨subd6_7_130, List.forall_mem_cons.2 ⟨subd6_7_131, List.forall_mem_cons.2 ⟨subd6_7_132, List.forall_mem_cons.2 ⟨subd6_7_133, List.forall_mem_cons.2 ⟨subd6_7_134, List.forall_mem_cons.2 ⟨subd6_7_135, List.forall_mem_cons.2 ⟨subd6_7_136, List.forall_mem_cons.2 ⟨subd6_7_137, List.forall_mem_cons.2 ⟨subd6_7_138, List.forall_mem_cons.2 ⟨subd6_7_139, List.forall_mem_cons.2 ⟨subd6_7_140, List.forall_mem_cons.2 ⟨subd6_7_141, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_8 : ldCheck G d6_8.U d6_8.ms ldd6_8 = true := by decide +kernel
theorem pre_okd6_8 : subPre G cell6 d6_8 = true := by decide +kernel
theorem subd6_8_0 : subd6_8 [-1, -2] = true := by decide +kernel
theorem subd6_8_1 : subd6_8 [-1, -1, -21] = true := by decide +kernel
theorem subd6_8_2 : subd6_8 [-1, -1, -20] = true := by decide +kernel
theorem subd6_8_3 : subd6_8 [-1, -1, -19] = true := by decide +kernel
theorem subd6_8_4 : subd6_8 [-1, -1, -18] = true := by decide +kernel
theorem subd6_8_5 : subd6_8 [-1, -1, -17] = true := by decide +kernel
theorem subd6_8_6 : subd6_8 [-1, -1, -16] = true := by decide +kernel
theorem subd6_8_7 : subd6_8 [-1, -1, -15] = true := by decide +kernel
theorem subd6_8_8 : subd6_8 [-1, -1, -14] = true := by decide +kernel
theorem subd6_8_9 : subd6_8 [-1, -1, -13] = true := by decide +kernel
theorem subd6_8_10 : subd6_8 [-1, -1, -12] = true := by decide +kernel
theorem subd6_8_11 : subd6_8 [-1, -1, -11] = true := by decide +kernel
theorem subd6_8_12 : subd6_8 [-1, -1, -10] = true := by decide +kernel
theorem subd6_8_13 : subd6_8 [-1, -1, -9] = true := by decide +kernel
theorem subd6_8_14 : subd6_8 [-1, -1, -8] = true := by decide +kernel
theorem subd6_8_15 : subd6_8 [-1, -1, -7] = true := by decide +kernel
theorem subd6_8_16 : subd6_8 [-1, -1, -6] = true := by decide +kernel
theorem subd6_8_17 : subd6_8 [-1, -1, -5] = true := by decide +kernel
theorem subd6_8_18 : subd6_8 [-1, -1, -4] = true := by decide +kernel
theorem subd6_8_19 : subd6_8 [-1, -1, -3] = true := by decide +kernel
theorem subd6_8_20 : subd6_8 [-1, -1, -2] = true := by decide +kernel
theorem subd6_8_21 : subd6_8 [-1, -1, -1] = true := by decide +kernel
theorem subd6_8_22 : subd6_8 [-1, -1, 0] = true := by decide +kernel
theorem subd6_8_23 : subd6_8 [-1, -1, 1] = true := by decide +kernel
theorem subd6_8_24 : subd6_8 [-1, -1, 2] = true := by decide +kernel
theorem subd6_8_25 : subd6_8 [-1, -1, 3] = true := by decide +kernel
theorem subd6_8_26 : subd6_8 [-1, -1, 4] = true := by decide +kernel
theorem subd6_8_27 : subd6_8 [-1, -1, 5] = true := by decide +kernel
theorem subd6_8_28 : subd6_8 [-1, -1, 6] = true := by decide +kernel
theorem subd6_8_29 : subd6_8 [-1, -1, 7] = true := by decide +kernel
theorem subd6_8_30 : subd6_8 [-1, -1, 8] = true := by decide +kernel
theorem subd6_8_31 : subd6_8 [-1, -1, 9] = true := by decide +kernel
theorem sbd6_8_0 : ∀ q ∈ blkd6_8_0, subd6_8 q = true := by
  unfold blkd6_8_0
  exact List.forall_mem_cons.2 ⟨subd6_8_0, List.forall_mem_cons.2 ⟨subd6_8_1, List.forall_mem_cons.2 ⟨subd6_8_2, List.forall_mem_cons.2 ⟨subd6_8_3, List.forall_mem_cons.2 ⟨subd6_8_4, List.forall_mem_cons.2 ⟨subd6_8_5, List.forall_mem_cons.2 ⟨subd6_8_6, List.forall_mem_cons.2 ⟨subd6_8_7, List.forall_mem_cons.2 ⟨subd6_8_8, List.forall_mem_cons.2 ⟨subd6_8_9, List.forall_mem_cons.2 ⟨subd6_8_10, List.forall_mem_cons.2 ⟨subd6_8_11, List.forall_mem_cons.2 ⟨subd6_8_12, List.forall_mem_cons.2 ⟨subd6_8_13, List.forall_mem_cons.2 ⟨subd6_8_14, List.forall_mem_cons.2 ⟨subd6_8_15, List.forall_mem_cons.2 ⟨subd6_8_16, List.forall_mem_cons.2 ⟨subd6_8_17, List.forall_mem_cons.2 ⟨subd6_8_18, List.forall_mem_cons.2 ⟨subd6_8_19, List.forall_mem_cons.2 ⟨subd6_8_20, List.forall_mem_cons.2 ⟨subd6_8_21, List.forall_mem_cons.2 ⟨subd6_8_22, List.forall_mem_cons.2 ⟨subd6_8_23, List.forall_mem_cons.2 ⟨subd6_8_24, List.forall_mem_cons.2 ⟨subd6_8_25, List.forall_mem_cons.2 ⟨subd6_8_26, List.forall_mem_cons.2 ⟨subd6_8_27, List.forall_mem_cons.2 ⟨subd6_8_28, List.forall_mem_cons.2 ⟨subd6_8_29, List.forall_mem_cons.2 ⟨subd6_8_30, List.forall_mem_cons.2 ⟨subd6_8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_8_32 : subd6_8 [-1, -1, 10] = true := by decide +kernel
theorem subd6_8_33 : subd6_8 [-1, -1, 11] = true := by decide +kernel
theorem subd6_8_34 : subd6_8 [-1, -1, 12] = true := by decide +kernel
theorem subd6_8_35 : subd6_8 [-1, -1, 13] = true := by decide +kernel
theorem subd6_8_36 : subd6_8 [-1, -1, 14] = true := by decide +kernel
theorem subd6_8_37 : subd6_8 [-1, -1, 15] = true := by decide +kernel
theorem subd6_8_38 : subd6_8 [-1, -1, 16] = true := by decide +kernel
theorem subd6_8_39 : subd6_8 [-1, -1, 17] = true := by decide +kernel
theorem subd6_8_40 : subd6_8 [-1, -1, 18] = true := by decide +kernel
theorem subd6_8_41 : subd6_8 [-1, 0, -26] = true := by decide +kernel
theorem subd6_8_42 : subd6_8 [-1, 0, -25] = true := by decide +kernel
theorem subd6_8_43 : subd6_8 [-1, 0, -24] = true := by decide +kernel
theorem subd6_8_44 : subd6_8 [-1, 0, -23] = true := by decide +kernel
theorem subd6_8_45 : subd6_8 [-1, 0, -22] = true := by decide +kernel
theorem subd6_8_46 : subd6_8 [-1, 0, -21] = true := by decide +kernel
theorem subd6_8_47 : subd6_8 [-1, 0, -20] = true := by decide +kernel
theorem subd6_8_48 : subd6_8 [-1, 0, -19] = true := by decide +kernel
theorem subd6_8_49 : subd6_8 [-1, 0, -18] = true := by decide +kernel
theorem subd6_8_50 : subd6_8 [-1, 0, -17] = true := by decide +kernel
theorem subd6_8_51 : subd6_8 [-1, 0, -16] = true := by decide +kernel
theorem subd6_8_52 : subd6_8 [-1, 0, -15] = true := by decide +kernel
theorem subd6_8_53 : subd6_8 [-1, 0, -14] = true := by decide +kernel
theorem subd6_8_54 : subd6_8 [-1, 0, -13] = true := by decide +kernel
theorem subd6_8_55 : subd6_8 [-1, 0, -12] = true := by decide +kernel
theorem subd6_8_56 : subd6_8 [-1, 0, -11] = true := by decide +kernel
theorem subd6_8_57 : subd6_8 [-1, 0, -10] = true := by decide +kernel
theorem subd6_8_58 : subd6_8 [-1, 0, -9] = true := by decide +kernel
theorem subd6_8_59 : subd6_8 [-1, 0, -8] = true := by decide +kernel
theorem subd6_8_60 : subd6_8 [-1, 0, -7] = true := by decide +kernel
theorem subd6_8_61 : subd6_8 [-1, 0, -6] = true := by decide +kernel
theorem subd6_8_62 : subd6_8 [-1, 0, -5] = true := by decide +kernel
theorem subd6_8_63 : subd6_8 [-1, 0, -4] = true := by decide +kernel
theorem sbd6_8_1 : ∀ q ∈ blkd6_8_1, subd6_8 q = true := by
  unfold blkd6_8_1
  exact List.forall_mem_cons.2 ⟨subd6_8_32, List.forall_mem_cons.2 ⟨subd6_8_33, List.forall_mem_cons.2 ⟨subd6_8_34, List.forall_mem_cons.2 ⟨subd6_8_35, List.forall_mem_cons.2 ⟨subd6_8_36, List.forall_mem_cons.2 ⟨subd6_8_37, List.forall_mem_cons.2 ⟨subd6_8_38, List.forall_mem_cons.2 ⟨subd6_8_39, List.forall_mem_cons.2 ⟨subd6_8_40, List.forall_mem_cons.2 ⟨subd6_8_41, List.forall_mem_cons.2 ⟨subd6_8_42, List.forall_mem_cons.2 ⟨subd6_8_43, List.forall_mem_cons.2 ⟨subd6_8_44, List.forall_mem_cons.2 ⟨subd6_8_45, List.forall_mem_cons.2 ⟨subd6_8_46, List.forall_mem_cons.2 ⟨subd6_8_47, List.forall_mem_cons.2 ⟨subd6_8_48, List.forall_mem_cons.2 ⟨subd6_8_49, List.forall_mem_cons.2 ⟨subd6_8_50, List.forall_mem_cons.2 ⟨subd6_8_51, List.forall_mem_cons.2 ⟨subd6_8_52, List.forall_mem_cons.2 ⟨subd6_8_53, List.forall_mem_cons.2 ⟨subd6_8_54, List.forall_mem_cons.2 ⟨subd6_8_55, List.forall_mem_cons.2 ⟨subd6_8_56, List.forall_mem_cons.2 ⟨subd6_8_57, List.forall_mem_cons.2 ⟨subd6_8_58, List.forall_mem_cons.2 ⟨subd6_8_59, List.forall_mem_cons.2 ⟨subd6_8_60, List.forall_mem_cons.2 ⟨subd6_8_61, List.forall_mem_cons.2 ⟨subd6_8_62, List.forall_mem_cons.2 ⟨subd6_8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_8_64 : subd6_8 [-1, 0, -3] = true := by decide +kernel
theorem subd6_8_65 : subd6_8 [-1, 0, -2] = true := by decide +kernel
theorem subd6_8_66 : subd6_8 [-1, 0, -1] = true := by decide +kernel
theorem subd6_8_67 : subd6_8 [-1, 0, 0] = true := by decide +kernel
theorem subd6_8_68 : subd6_8 [-1, 0, 1] = true := by decide +kernel
theorem subd6_8_69 : subd6_8 [-1, 0, 2] = true := by decide +kernel
theorem subd6_8_70 : subd6_8 [-1, 0, 3] = true := by decide +kernel
theorem subd6_8_71 : subd6_8 [-1, 0, 4] = true := by decide +kernel
theorem subd6_8_72 : subd6_8 [-1, 0, 5] = true := by decide +kernel
theorem subd6_8_73 : subd6_8 [-1, 0, 6] = true := by decide +kernel
theorem subd6_8_74 : subd6_8 [-1, 0, 7] = true := by decide +kernel
theorem subd6_8_75 : subd6_8 [-1, 0, 8] = true := by decide +kernel
theorem subd6_8_76 : subd6_8 [-1, 0, 9] = true := by decide +kernel
theorem subd6_8_77 : subd6_8 [-1, 0, 10] = true := by decide +kernel
theorem subd6_8_78 : subd6_8 [-1, 0, 11] = true := by decide +kernel
theorem subd6_8_79 : subd6_8 [-1, 0, 12] = true := by decide +kernel
theorem subd6_8_80 : subd6_8 [-1, 0, 13] = true := by decide +kernel
theorem subd6_8_81 : subd6_8 [-1, 0, 14] = true := by decide +kernel
theorem subd6_8_82 : subd6_8 [-1, 0, 15] = true := by decide +kernel
theorem subd6_8_83 : subd6_8 [-1, 0, 16] = true := by decide +kernel
theorem subd6_8_84 : subd6_8 [-1, 0, 17] = true := by decide +kernel
theorem subd6_8_85 : subd6_8 [-1, 0, 18] = true := by decide +kernel
theorem subd6_8_86 : subd6_8 [-1, 0, 19] = true := by decide +kernel
theorem subd6_8_87 : subd6_8 [-1, 0, 20] = true := by decide +kernel
theorem subd6_8_88 : subd6_8 [-1, 0, 21] = true := by decide +kernel
theorem subd6_8_89 : subd6_8 [-1, 0, 22] = true := by decide +kernel
theorem subd6_8_90 : subd6_8 [-1, 0, 23] = true := by decide +kernel
theorem subd6_8_91 : subd6_8 [-1, 0, 24] = true := by decide +kernel
theorem subd6_8_92 : subd6_8 [0, -2] = true := by decide +kernel
theorem subd6_8_93 : subd6_8 [0, -1, -32] = true := by decide +kernel
theorem subd6_8_94 : subd6_8 [0, -1, -31] = true := by decide +kernel
theorem subd6_8_95 : subd6_8 [0, -1, -30] = true := by decide +kernel
theorem sbd6_8_2 : ∀ q ∈ blkd6_8_2, subd6_8 q = true := by
  unfold blkd6_8_2
  exact List.forall_mem_cons.2 ⟨subd6_8_64, List.forall_mem_cons.2 ⟨subd6_8_65, List.forall_mem_cons.2 ⟨subd6_8_66, List.forall_mem_cons.2 ⟨subd6_8_67, List.forall_mem_cons.2 ⟨subd6_8_68, List.forall_mem_cons.2 ⟨subd6_8_69, List.forall_mem_cons.2 ⟨subd6_8_70, List.forall_mem_cons.2 ⟨subd6_8_71, List.forall_mem_cons.2 ⟨subd6_8_72, List.forall_mem_cons.2 ⟨subd6_8_73, List.forall_mem_cons.2 ⟨subd6_8_74, List.forall_mem_cons.2 ⟨subd6_8_75, List.forall_mem_cons.2 ⟨subd6_8_76, List.forall_mem_cons.2 ⟨subd6_8_77, List.forall_mem_cons.2 ⟨subd6_8_78, List.forall_mem_cons.2 ⟨subd6_8_79, List.forall_mem_cons.2 ⟨subd6_8_80, List.forall_mem_cons.2 ⟨subd6_8_81, List.forall_mem_cons.2 ⟨subd6_8_82, List.forall_mem_cons.2 ⟨subd6_8_83, List.forall_mem_cons.2 ⟨subd6_8_84, List.forall_mem_cons.2 ⟨subd6_8_85, List.forall_mem_cons.2 ⟨subd6_8_86, List.forall_mem_cons.2 ⟨subd6_8_87, List.forall_mem_cons.2 ⟨subd6_8_88, List.forall_mem_cons.2 ⟨subd6_8_89, List.forall_mem_cons.2 ⟨subd6_8_90, List.forall_mem_cons.2 ⟨subd6_8_91, List.forall_mem_cons.2 ⟨subd6_8_92, List.forall_mem_cons.2 ⟨subd6_8_93, List.forall_mem_cons.2 ⟨subd6_8_94, List.forall_mem_cons.2 ⟨subd6_8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
