import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd22_1_64 : subd22_1 [0, -1, 5] = true := by decide +kernel
theorem subd22_1_65 : subd22_1 [0, -1, 6] = true := by decide +kernel
theorem subd22_1_66 : subd22_1 [0, -1, 7] = true := by decide +kernel
theorem subd22_1_67 : subd22_1 [0, -1, 8] = true := by decide +kernel
theorem subd22_1_68 : subd22_1 [0, 0, -10] = true := by decide +kernel
theorem subd22_1_69 : subd22_1 [0, 0, -9] = true := by decide +kernel
theorem subd22_1_70 : subd22_1 [0, 0, -8] = true := by decide +kernel
theorem subd22_1_71 : subd22_1 [0, 0, -7] = true := by decide +kernel
theorem subd22_1_72 : subd22_1 [0, 0, -6] = true := by decide +kernel
theorem subd22_1_73 : subd22_1 [0, 0, -5] = true := by decide +kernel
theorem subd22_1_74 : subd22_1 [0, 0, -4] = true := by decide +kernel
theorem subd22_1_75 : subd22_1 [0, 0, -3] = true := by decide +kernel
theorem subd22_1_76 : subd22_1 [0, 0, -2] = true := by decide +kernel
theorem subd22_1_77 : subd22_1 [0, 0, -1] = true := by decide +kernel
theorem subd22_1_78 : subd22_1 [0, 0, 0] = true := by decide +kernel
theorem subd22_1_79 : subd22_1 [0, 0, 1] = true := by decide +kernel
theorem subd22_1_80 : subd22_1 [0, 0, 2] = true := by decide +kernel
theorem subd22_1_81 : subd22_1 [0, 0, 3] = true := by decide +kernel
theorem subd22_1_82 : subd22_1 [0, 0, 4] = true := by decide +kernel
theorem subd22_1_83 : subd22_1 [0, 0, 5] = true := by decide +kernel
theorem subd22_1_84 : subd22_1 [0, 0, 6] = true := by decide +kernel
theorem subd22_1_85 : subd22_1 [0, 0, 7] = true := by decide +kernel
theorem subd22_1_86 : subd22_1 [0, 0, 8] = true := by decide +kernel
theorem subd22_1_87 : subd22_1 [0, 0, 9] = true := by decide +kernel
theorem subd22_1_88 : subd22_1 [0, 1, -9] = true := by decide +kernel
theorem subd22_1_89 : subd22_1 [0, 1, -8] = true := by decide +kernel
theorem subd22_1_90 : subd22_1 [0, 1, -7] = true := by decide +kernel
theorem subd22_1_91 : subd22_1 [0, 1, -6] = true := by decide +kernel
theorem subd22_1_92 : subd22_1 [0, 1, -5] = true := by decide +kernel
theorem subd22_1_93 : subd22_1 [0, 1, -4] = true := by decide +kernel
theorem subd22_1_94 : subd22_1 [0, 1, -3] = true := by decide +kernel
theorem subd22_1_95 : subd22_1 [0, 1, -2] = true := by decide +kernel
theorem sbd22_1_2 : ∀ q ∈ blkd22_1_2, subd22_1 q = true := by
  unfold blkd22_1_2
  exact List.forall_mem_cons.2 ⟨subd22_1_64, List.forall_mem_cons.2 ⟨subd22_1_65, List.forall_mem_cons.2 ⟨subd22_1_66, List.forall_mem_cons.2 ⟨subd22_1_67, List.forall_mem_cons.2 ⟨subd22_1_68, List.forall_mem_cons.2 ⟨subd22_1_69, List.forall_mem_cons.2 ⟨subd22_1_70, List.forall_mem_cons.2 ⟨subd22_1_71, List.forall_mem_cons.2 ⟨subd22_1_72, List.forall_mem_cons.2 ⟨subd22_1_73, List.forall_mem_cons.2 ⟨subd22_1_74, List.forall_mem_cons.2 ⟨subd22_1_75, List.forall_mem_cons.2 ⟨subd22_1_76, List.forall_mem_cons.2 ⟨subd22_1_77, List.forall_mem_cons.2 ⟨subd22_1_78, List.forall_mem_cons.2 ⟨subd22_1_79, List.forall_mem_cons.2 ⟨subd22_1_80, List.forall_mem_cons.2 ⟨subd22_1_81, List.forall_mem_cons.2 ⟨subd22_1_82, List.forall_mem_cons.2 ⟨subd22_1_83, List.forall_mem_cons.2 ⟨subd22_1_84, List.forall_mem_cons.2 ⟨subd22_1_85, List.forall_mem_cons.2 ⟨subd22_1_86, List.forall_mem_cons.2 ⟨subd22_1_87, List.forall_mem_cons.2 ⟨subd22_1_88, List.forall_mem_cons.2 ⟨subd22_1_89, List.forall_mem_cons.2 ⟨subd22_1_90, List.forall_mem_cons.2 ⟨subd22_1_91, List.forall_mem_cons.2 ⟨subd22_1_92, List.forall_mem_cons.2 ⟨subd22_1_93, List.forall_mem_cons.2 ⟨subd22_1_94, List.forall_mem_cons.2 ⟨subd22_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd22_1_96 : subd22_1 [0, 1, -1] = true := by decide +kernel
theorem subd22_1_97 : subd22_1 [0, 1, 0] = true := by decide +kernel
theorem subd22_1_98 : subd22_1 [0, 1, 1] = true := by decide +kernel
theorem subd22_1_99 : subd22_1 [0, 1, 2] = true := by decide +kernel
theorem subd22_1_100 : subd22_1 [0, 1, 3] = true := by decide +kernel
theorem subd22_1_101 : subd22_1 [0, 1, 4] = true := by decide +kernel
theorem subd22_1_102 : subd22_1 [0, 1, 5] = true := by decide +kernel
theorem subd22_1_103 : subd22_1 [0, 1, 6] = true := by decide +kernel
theorem subd22_1_104 : subd22_1 [0, 1, 7] = true := by decide +kernel
theorem subd22_1_105 : subd22_1 [0, 1, 8] = true := by decide +kernel
theorem subd22_1_106 : subd22_1 [0, 2] = true := by decide +kernel
theorem subd22_1_107 : subd22_1 [1, -2] = true := by decide +kernel
theorem subd22_1_108 : subd22_1 [1, -1, -7] = true := by decide +kernel
theorem subd22_1_109 : subd22_1 [1, -1, -6] = true := by decide +kernel
theorem subd22_1_110 : subd22_1 [1, -1, -5] = true := by decide +kernel
theorem subd22_1_111 : subd22_1 [1, -1, -4] = true := by decide +kernel
theorem subd22_1_112 : subd22_1 [1, -1, -3] = true := by decide +kernel
theorem subd22_1_113 : subd22_1 [1, -1, -2] = true := by decide +kernel
theorem subd22_1_114 : subd22_1 [1, -1, -1] = true := by decide +kernel
theorem subd22_1_115 : subd22_1 [1, -1, 0] = true := by decide +kernel
theorem subd22_1_116 : subd22_1 [1, -1, 1] = true := by decide +kernel
theorem subd22_1_117 : subd22_1 [1, -1, 2] = true := by decide +kernel
theorem subd22_1_118 : subd22_1 [1, -1, 3] = true := by decide +kernel
theorem subd22_1_119 : subd22_1 [1, -1, 4] = true := by decide +kernel
theorem subd22_1_120 : subd22_1 [1, -1, 5] = true := by decide +kernel
theorem subd22_1_121 : subd22_1 [1, -1, 6] = true := by decide +kernel
theorem subd22_1_122 : subd22_1 [1, 0, -9] = true := by decide +kernel
theorem subd22_1_123 : subd22_1 [1, 0, -8] = true := by decide +kernel
theorem subd22_1_124 : subd22_1 [1, 0, -7] = true := by decide +kernel
theorem subd22_1_125 : subd22_1 [1, 0, -6] = true := by decide +kernel
theorem subd22_1_126 : subd22_1 [1, 0, -5] = true := by decide +kernel
theorem subd22_1_127 : subd22_1 [1, 0, -4] = true := by decide +kernel
theorem sbd22_1_3 : ∀ q ∈ blkd22_1_3, subd22_1 q = true := by
  unfold blkd22_1_3
  exact List.forall_mem_cons.2 ⟨subd22_1_96, List.forall_mem_cons.2 ⟨subd22_1_97, List.forall_mem_cons.2 ⟨subd22_1_98, List.forall_mem_cons.2 ⟨subd22_1_99, List.forall_mem_cons.2 ⟨subd22_1_100, List.forall_mem_cons.2 ⟨subd22_1_101, List.forall_mem_cons.2 ⟨subd22_1_102, List.forall_mem_cons.2 ⟨subd22_1_103, List.forall_mem_cons.2 ⟨subd22_1_104, List.forall_mem_cons.2 ⟨subd22_1_105, List.forall_mem_cons.2 ⟨subd22_1_106, List.forall_mem_cons.2 ⟨subd22_1_107, List.forall_mem_cons.2 ⟨subd22_1_108, List.forall_mem_cons.2 ⟨subd22_1_109, List.forall_mem_cons.2 ⟨subd22_1_110, List.forall_mem_cons.2 ⟨subd22_1_111, List.forall_mem_cons.2 ⟨subd22_1_112, List.forall_mem_cons.2 ⟨subd22_1_113, List.forall_mem_cons.2 ⟨subd22_1_114, List.forall_mem_cons.2 ⟨subd22_1_115, List.forall_mem_cons.2 ⟨subd22_1_116, List.forall_mem_cons.2 ⟨subd22_1_117, List.forall_mem_cons.2 ⟨subd22_1_118, List.forall_mem_cons.2 ⟨subd22_1_119, List.forall_mem_cons.2 ⟨subd22_1_120, List.forall_mem_cons.2 ⟨subd22_1_121, List.forall_mem_cons.2 ⟨subd22_1_122, List.forall_mem_cons.2 ⟨subd22_1_123, List.forall_mem_cons.2 ⟨subd22_1_124, List.forall_mem_cons.2 ⟨subd22_1_125, List.forall_mem_cons.2 ⟨subd22_1_126, List.forall_mem_cons.2 ⟨subd22_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd22_1_128 : subd22_1 [1, 0, -3] = true := by decide +kernel
theorem subd22_1_129 : subd22_1 [1, 0, -2] = true := by decide +kernel
theorem subd22_1_130 : subd22_1 [1, 0, -1] = true := by decide +kernel
theorem subd22_1_131 : subd22_1 [1, 0, 0] = true := by decide +kernel
theorem subd22_1_132 : subd22_1 [1, 0, 1] = true := by decide +kernel
theorem subd22_1_133 : subd22_1 [1, 0, 2] = true := by decide +kernel
theorem subd22_1_134 : subd22_1 [1, 0, 3] = true := by decide +kernel
theorem subd22_1_135 : subd22_1 [1, 0, 4] = true := by decide +kernel
theorem subd22_1_136 : subd22_1 [1, 0, 5] = true := by decide +kernel
theorem subd22_1_137 : subd22_1 [1, 0, 6] = true := by decide +kernel
theorem subd22_1_138 : subd22_1 [1, 0, 7] = true := by decide +kernel
theorem subd22_1_139 : subd22_1 [1, 0, 8] = true := by decide +kernel
theorem subd22_1_140 : subd22_1 [1, 1, -7] = true := by decide +kernel
theorem subd22_1_141 : subd22_1 [1, 1, -6] = true := by decide +kernel
theorem subd22_1_142 : subd22_1 [1, 1, -5] = true := by decide +kernel
theorem subd22_1_143 : subd22_1 [1, 1, -4] = true := by decide +kernel
theorem subd22_1_144 : subd22_1 [1, 1, -3] = true := by decide +kernel
theorem subd22_1_145 : subd22_1 [1, 1, -2] = true := by decide +kernel
theorem subd22_1_146 : subd22_1 [1, 1, -1] = true := by decide +kernel
theorem subd22_1_147 : subd22_1 [1, 1, 0] = true := by decide +kernel
theorem subd22_1_148 : subd22_1 [1, 1, 1] = true := by decide +kernel
theorem subd22_1_149 : subd22_1 [1, 1, 2] = true := by decide +kernel
theorem subd22_1_150 : subd22_1 [1, 1, 3] = true := by decide +kernel
theorem subd22_1_151 : subd22_1 [1, 1, 4] = true := by decide +kernel
theorem subd22_1_152 : subd22_1 [1, 1, 5] = true := by decide +kernel
theorem subd22_1_153 : subd22_1 [1, 1, 6] = true := by decide +kernel
theorem subd22_1_154 : subd22_1 [1, 1, 7] = true := by decide +kernel
theorem sbd22_1_4 : ∀ q ∈ blkd22_1_4, subd22_1 q = true := by
  unfold blkd22_1_4
  exact List.forall_mem_cons.2 ⟨subd22_1_128, List.forall_mem_cons.2 ⟨subd22_1_129, List.forall_mem_cons.2 ⟨subd22_1_130, List.forall_mem_cons.2 ⟨subd22_1_131, List.forall_mem_cons.2 ⟨subd22_1_132, List.forall_mem_cons.2 ⟨subd22_1_133, List.forall_mem_cons.2 ⟨subd22_1_134, List.forall_mem_cons.2 ⟨subd22_1_135, List.forall_mem_cons.2 ⟨subd22_1_136, List.forall_mem_cons.2 ⟨subd22_1_137, List.forall_mem_cons.2 ⟨subd22_1_138, List.forall_mem_cons.2 ⟨subd22_1_139, List.forall_mem_cons.2 ⟨subd22_1_140, List.forall_mem_cons.2 ⟨subd22_1_141, List.forall_mem_cons.2 ⟨subd22_1_142, List.forall_mem_cons.2 ⟨subd22_1_143, List.forall_mem_cons.2 ⟨subd22_1_144, List.forall_mem_cons.2 ⟨subd22_1_145, List.forall_mem_cons.2 ⟨subd22_1_146, List.forall_mem_cons.2 ⟨subd22_1_147, List.forall_mem_cons.2 ⟨subd22_1_148, List.forall_mem_cons.2 ⟨subd22_1_149, List.forall_mem_cons.2 ⟨subd22_1_150, List.forall_mem_cons.2 ⟨subd22_1_151, List.forall_mem_cons.2 ⟨subd22_1_152, List.forall_mem_cons.2 ⟨subd22_1_153, List.forall_mem_cons.2 ⟨subd22_1_154, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd22_2 : ldCheck G d22_2.U d22_2.ms ldd22_2 = true := by decide +kernel
theorem pre_okd22_2 : subPre G cell22 d22_2 = true := by decide +kernel
theorem subd22_2_0 : subd22_2 [-3] = true := by decide +kernel
theorem subd22_2_1 : subd22_2 [-2, -2] = true := by decide +kernel
theorem subd22_2_2 : subd22_2 [-2, -1] = true := by decide +kernel
theorem subd22_2_3 : subd22_2 [-2, 0] = true := by decide +kernel
theorem subd22_2_4 : subd22_2 [-2, 1] = true := by decide +kernel
theorem subd22_2_5 : subd22_2 [-2, 2] = true := by decide +kernel
theorem subd22_2_6 : subd22_2 [-1, -3] = true := by decide +kernel
theorem subd22_2_7 : subd22_2 [-1, -2] = true := by decide +kernel
theorem subd22_2_8 : subd22_2 [-1, -1] = true := by decide +kernel
theorem subd22_2_9 : subd22_2 [-1, 0] = true := by decide +kernel
theorem subd22_2_10 : subd22_2 [-1, 1] = true := by decide +kernel
theorem subd22_2_11 : subd22_2 [-1, 2] = true := by decide +kernel
theorem subd22_2_12 : subd22_2 [-1, 3] = true := by decide +kernel
theorem subd22_2_13 : subd22_2 [0, -3] = true := by decide +kernel
theorem subd22_2_14 : subd22_2 [0, -2] = true := by decide +kernel
theorem subd22_2_15 : subd22_2 [0, -1] = true := by decide +kernel
theorem subd22_2_16 : subd22_2 [0, 0] = true := by decide +kernel
theorem subd22_2_17 : subd22_2 [0, 1] = true := by decide +kernel
theorem subd22_2_18 : subd22_2 [0, 2] = true := by decide +kernel
theorem subd22_2_19 : subd22_2 [1, -4] = true := by decide +kernel
theorem subd22_2_20 : subd22_2 [1, -3] = true := by decide +kernel
theorem subd22_2_21 : subd22_2 [1, -2] = true := by decide +kernel
theorem subd22_2_22 : subd22_2 [1, -1] = true := by decide +kernel
theorem subd22_2_23 : subd22_2 [1, 0] = true := by decide +kernel
theorem subd22_2_24 : subd22_2 [1, 1] = true := by decide +kernel
theorem subd22_2_25 : subd22_2 [1, 2] = true := by decide +kernel
theorem subd22_2_26 : subd22_2 [2, -3] = true := by decide +kernel
theorem subd22_2_27 : subd22_2 [2, -2] = true := by decide +kernel
theorem subd22_2_28 : subd22_2 [2, -1] = true := by decide +kernel
theorem subd22_2_29 : subd22_2 [2, 0] = true := by decide +kernel
theorem subd22_2_30 : subd22_2 [2, 1] = true := by decide +kernel
theorem subd22_2_31 : subd22_2 [3] = true := by decide +kernel
theorem sbd22_2_0 : ∀ q ∈ blkd22_2_0, subd22_2 q = true := by
  unfold blkd22_2_0
  exact List.forall_mem_cons.2 ⟨subd22_2_0, List.forall_mem_cons.2 ⟨subd22_2_1, List.forall_mem_cons.2 ⟨subd22_2_2, List.forall_mem_cons.2 ⟨subd22_2_3, List.forall_mem_cons.2 ⟨subd22_2_4, List.forall_mem_cons.2 ⟨subd22_2_5, List.forall_mem_cons.2 ⟨subd22_2_6, List.forall_mem_cons.2 ⟨subd22_2_7, List.forall_mem_cons.2 ⟨subd22_2_8, List.forall_mem_cons.2 ⟨subd22_2_9, List.forall_mem_cons.2 ⟨subd22_2_10, List.forall_mem_cons.2 ⟨subd22_2_11, List.forall_mem_cons.2 ⟨subd22_2_12, List.forall_mem_cons.2 ⟨subd22_2_13, List.forall_mem_cons.2 ⟨subd22_2_14, List.forall_mem_cons.2 ⟨subd22_2_15, List.forall_mem_cons.2 ⟨subd22_2_16, List.forall_mem_cons.2 ⟨subd22_2_17, List.forall_mem_cons.2 ⟨subd22_2_18, List.forall_mem_cons.2 ⟨subd22_2_19, List.forall_mem_cons.2 ⟨subd22_2_20, List.forall_mem_cons.2 ⟨subd22_2_21, List.forall_mem_cons.2 ⟨subd22_2_22, List.forall_mem_cons.2 ⟨subd22_2_23, List.forall_mem_cons.2 ⟨subd22_2_24, List.forall_mem_cons.2 ⟨subd22_2_25, List.forall_mem_cons.2 ⟨subd22_2_26, List.forall_mem_cons.2 ⟨subd22_2_27, List.forall_mem_cons.2 ⟨subd22_2_28, List.forall_mem_cons.2 ⟨subd22_2_29, List.forall_mem_cons.2 ⟨subd22_2_30, List.forall_mem_cons.2 ⟨subd22_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd22_3 : ldCheck G d22_3.U d22_3.ms ldd22_3 = true := by decide +kernel
theorem pre_okd22_3 : subPre G cell22 d22_3 = true := by decide +kernel
theorem subd22_3_0 : subd22_3 [-3] = true := by decide +kernel
theorem subd22_3_1 : subd22_3 [-2, -4] = true := by decide +kernel
theorem subd22_3_2 : subd22_3 [-2, -3] = true := by decide +kernel
theorem subd22_3_3 : subd22_3 [-2, -2] = true := by decide +kernel
theorem subd22_3_4 : subd22_3 [-2, -1] = true := by decide +kernel
theorem subd22_3_5 : subd22_3 [-2, 0] = true := by decide +kernel
theorem subd22_3_6 : subd22_3 [-2, 1] = true := by decide +kernel
theorem subd22_3_7 : subd22_3 [-2, 2] = true := by decide +kernel
theorem subd22_3_8 : subd22_3 [-1, -4] = true := by decide +kernel
theorem subd22_3_9 : subd22_3 [-1, -3] = true := by decide +kernel
theorem subd22_3_10 : subd22_3 [-1, -2] = true := by decide +kernel
theorem subd22_3_11 : subd22_3 [-1, -1] = true := by decide +kernel
theorem subd22_3_12 : subd22_3 [-1, 0] = true := by decide +kernel
theorem subd22_3_13 : subd22_3 [-1, 1] = true := by decide +kernel
theorem subd22_3_14 : subd22_3 [-1, 2] = true := by decide +kernel
theorem subd22_3_15 : subd22_3 [-1, 3] = true := by decide +kernel
theorem subd22_3_16 : subd22_3 [0, -4] = true := by decide +kernel
theorem subd22_3_17 : subd22_3 [0, -3] = true := by decide +kernel
theorem subd22_3_18 : subd22_3 [0, -2] = true := by decide +kernel
theorem subd22_3_19 : subd22_3 [0, -1] = true := by decide +kernel
theorem subd22_3_20 : subd22_3 [0, 0] = true := by decide +kernel
theorem subd22_3_21 : subd22_3 [0, 1] = true := by decide +kernel
theorem subd22_3_22 : subd22_3 [0, 2] = true := by decide +kernel
theorem subd22_3_23 : subd22_3 [0, 3] = true := by decide +kernel
theorem subd22_3_24 : subd22_3 [1, -4] = true := by decide +kernel
theorem subd22_3_25 : subd22_3 [1, -3] = true := by decide +kernel
theorem subd22_3_26 : subd22_3 [1, -2] = true := by decide +kernel
theorem subd22_3_27 : subd22_3 [1, -1] = true := by decide +kernel
theorem subd22_3_28 : subd22_3 [1, 0] = true := by decide +kernel
theorem subd22_3_29 : subd22_3 [1, 1] = true := by decide +kernel
theorem subd22_3_30 : subd22_3 [1, 2] = true := by decide +kernel
theorem subd22_3_31 : subd22_3 [1, 3] = true := by decide +kernel
theorem sbd22_3_0 : ∀ q ∈ blkd22_3_0, subd22_3 q = true := by
  unfold blkd22_3_0
  exact List.forall_mem_cons.2 ⟨subd22_3_0, List.forall_mem_cons.2 ⟨subd22_3_1, List.forall_mem_cons.2 ⟨subd22_3_2, List.forall_mem_cons.2 ⟨subd22_3_3, List.forall_mem_cons.2 ⟨subd22_3_4, List.forall_mem_cons.2 ⟨subd22_3_5, List.forall_mem_cons.2 ⟨subd22_3_6, List.forall_mem_cons.2 ⟨subd22_3_7, List.forall_mem_cons.2 ⟨subd22_3_8, List.forall_mem_cons.2 ⟨subd22_3_9, List.forall_mem_cons.2 ⟨subd22_3_10, List.forall_mem_cons.2 ⟨subd22_3_11, List.forall_mem_cons.2 ⟨subd22_3_12, List.forall_mem_cons.2 ⟨subd22_3_13, List.forall_mem_cons.2 ⟨subd22_3_14, List.forall_mem_cons.2 ⟨subd22_3_15, List.forall_mem_cons.2 ⟨subd22_3_16, List.forall_mem_cons.2 ⟨subd22_3_17, List.forall_mem_cons.2 ⟨subd22_3_18, List.forall_mem_cons.2 ⟨subd22_3_19, List.forall_mem_cons.2 ⟨subd22_3_20, List.forall_mem_cons.2 ⟨subd22_3_21, List.forall_mem_cons.2 ⟨subd22_3_22, List.forall_mem_cons.2 ⟨subd22_3_23, List.forall_mem_cons.2 ⟨subd22_3_24, List.forall_mem_cons.2 ⟨subd22_3_25, List.forall_mem_cons.2 ⟨subd22_3_26, List.forall_mem_cons.2 ⟨subd22_3_27, List.forall_mem_cons.2 ⟨subd22_3_28, List.forall_mem_cons.2 ⟨subd22_3_29, List.forall_mem_cons.2 ⟨subd22_3_30, List.forall_mem_cons.2 ⟨subd22_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd22_3_32 : subd22_3 [2, -3] = true := by decide +kernel
theorem subd22_3_33 : subd22_3 [2, -2] = true := by decide +kernel
theorem subd22_3_34 : subd22_3 [2, -1] = true := by decide +kernel
theorem subd22_3_35 : subd22_3 [2, 0] = true := by decide +kernel
theorem subd22_3_36 : subd22_3 [2, 1] = true := by decide +kernel
theorem subd22_3_37 : subd22_3 [2, 2] = true := by decide +kernel
theorem subd22_3_38 : subd22_3 [2, 3] = true := by decide +kernel
theorem subd22_3_39 : subd22_3 [3] = true := by decide +kernel
theorem sbd22_3_1 : ∀ q ∈ blkd22_3_1, subd22_3 q = true := by
  unfold blkd22_3_1
  exact List.forall_mem_cons.2 ⟨subd22_3_32, List.forall_mem_cons.2 ⟨subd22_3_33, List.forall_mem_cons.2 ⟨subd22_3_34, List.forall_mem_cons.2 ⟨subd22_3_35, List.forall_mem_cons.2 ⟨subd22_3_36, List.forall_mem_cons.2 ⟨subd22_3_37, List.forall_mem_cons.2 ⟨subd22_3_38, List.forall_mem_cons.2 ⟨subd22_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd23_0 : ldCheck G d23_0.U d23_0.ms ldd23_0 = true := by decide +kernel
theorem pre_okd23_0 : subPre G cell23 d23_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
