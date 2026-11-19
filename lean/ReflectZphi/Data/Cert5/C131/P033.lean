import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd16_0_64 : subd16_0 [0, -1, -2] = true := by decide +kernel
theorem subd16_0_65 : subd16_0 [0, -1, -1] = true := by decide +kernel
theorem subd16_0_66 : subd16_0 [0, -1, 0] = true := by decide +kernel
theorem subd16_0_67 : subd16_0 [0, -1, 1] = true := by decide +kernel
theorem subd16_0_68 : subd16_0 [0, -1, 2] = true := by decide +kernel
theorem subd16_0_69 : subd16_0 [0, -1, 3] = true := by decide +kernel
theorem subd16_0_70 : subd16_0 [0, -1, 4] = true := by decide +kernel
theorem subd16_0_71 : subd16_0 [0, -1, 5] = true := by decide +kernel
theorem subd16_0_72 : subd16_0 [0, -1, 6] = true := by decide +kernel
theorem subd16_0_73 : subd16_0 [0, -1, 7] = true := by decide +kernel
theorem subd16_0_74 : subd16_0 [0, 0, -8] = true := by decide +kernel
theorem subd16_0_75 : subd16_0 [0, 0, -7] = true := by decide +kernel
theorem subd16_0_76 : subd16_0 [0, 0, -6] = true := by decide +kernel
theorem subd16_0_77 : subd16_0 [0, 0, -5] = true := by decide +kernel
theorem subd16_0_78 : subd16_0 [0, 0, -4] = true := by decide +kernel
theorem subd16_0_79 : subd16_0 [0, 0, -3] = true := by decide +kernel
theorem subd16_0_80 : subd16_0 [0, 0, -2] = true := by decide +kernel
theorem subd16_0_81 : subd16_0 [0, 0, -1] = true := by decide +kernel
theorem subd16_0_82 : subd16_0 [0, 0, 0] = true := by decide +kernel
theorem subd16_0_83 : subd16_0 [0, 0, 1] = true := by decide +kernel
theorem subd16_0_84 : subd16_0 [0, 0, 2] = true := by decide +kernel
theorem subd16_0_85 : subd16_0 [0, 0, 3] = true := by decide +kernel
theorem subd16_0_86 : subd16_0 [0, 0, 4] = true := by decide +kernel
theorem subd16_0_87 : subd16_0 [0, 0, 5] = true := by decide +kernel
theorem subd16_0_88 : subd16_0 [0, 0, 6] = true := by decide +kernel
theorem subd16_0_89 : subd16_0 [0, 0, 7] = true := by decide +kernel
theorem subd16_0_90 : subd16_0 [0, 1, -8] = true := by decide +kernel
theorem subd16_0_91 : subd16_0 [0, 1, -7] = true := by decide +kernel
theorem subd16_0_92 : subd16_0 [0, 1, -6] = true := by decide +kernel
theorem subd16_0_93 : subd16_0 [0, 1, -5] = true := by decide +kernel
theorem subd16_0_94 : subd16_0 [0, 1, -4] = true := by decide +kernel
theorem subd16_0_95 : subd16_0 [0, 1, -3] = true := by decide +kernel
theorem sbd16_0_2 : ∀ q ∈ blkd16_0_2, subd16_0 q = true := by
  unfold blkd16_0_2
  exact List.forall_mem_cons.2 ⟨subd16_0_64, List.forall_mem_cons.2 ⟨subd16_0_65, List.forall_mem_cons.2 ⟨subd16_0_66, List.forall_mem_cons.2 ⟨subd16_0_67, List.forall_mem_cons.2 ⟨subd16_0_68, List.forall_mem_cons.2 ⟨subd16_0_69, List.forall_mem_cons.2 ⟨subd16_0_70, List.forall_mem_cons.2 ⟨subd16_0_71, List.forall_mem_cons.2 ⟨subd16_0_72, List.forall_mem_cons.2 ⟨subd16_0_73, List.forall_mem_cons.2 ⟨subd16_0_74, List.forall_mem_cons.2 ⟨subd16_0_75, List.forall_mem_cons.2 ⟨subd16_0_76, List.forall_mem_cons.2 ⟨subd16_0_77, List.forall_mem_cons.2 ⟨subd16_0_78, List.forall_mem_cons.2 ⟨subd16_0_79, List.forall_mem_cons.2 ⟨subd16_0_80, List.forall_mem_cons.2 ⟨subd16_0_81, List.forall_mem_cons.2 ⟨subd16_0_82, List.forall_mem_cons.2 ⟨subd16_0_83, List.forall_mem_cons.2 ⟨subd16_0_84, List.forall_mem_cons.2 ⟨subd16_0_85, List.forall_mem_cons.2 ⟨subd16_0_86, List.forall_mem_cons.2 ⟨subd16_0_87, List.forall_mem_cons.2 ⟨subd16_0_88, List.forall_mem_cons.2 ⟨subd16_0_89, List.forall_mem_cons.2 ⟨subd16_0_90, List.forall_mem_cons.2 ⟨subd16_0_91, List.forall_mem_cons.2 ⟨subd16_0_92, List.forall_mem_cons.2 ⟨subd16_0_93, List.forall_mem_cons.2 ⟨subd16_0_94, List.forall_mem_cons.2 ⟨subd16_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_96 : subd16_0 [0, 1, -2] = true := by decide +kernel
theorem subd16_0_97 : subd16_0 [0, 1, -1] = true := by decide +kernel
theorem subd16_0_98 : subd16_0 [0, 1, 0] = true := by decide +kernel
theorem subd16_0_99 : subd16_0 [0, 1, 1] = true := by decide +kernel
theorem subd16_0_100 : subd16_0 [0, 1, 2] = true := by decide +kernel
theorem subd16_0_101 : subd16_0 [0, 1, 3] = true := by decide +kernel
theorem subd16_0_102 : subd16_0 [0, 1, 4] = true := by decide +kernel
theorem subd16_0_103 : subd16_0 [0, 1, 5] = true := by decide +kernel
theorem subd16_0_104 : subd16_0 [0, 1, 6] = true := by decide +kernel
theorem subd16_0_105 : subd16_0 [0, 1, 7] = true := by decide +kernel
theorem subd16_0_106 : subd16_0 [0, 2] = true := by decide +kernel
theorem subd16_0_107 : subd16_0 [0, 3] = true := by decide +kernel
theorem subd16_0_108 : subd16_0 [1, -4] = true := by decide +kernel
theorem subd16_0_109 : subd16_0 [1, -3] = true := by decide +kernel
theorem subd16_0_110 : subd16_0 [1, -2] = true := by decide +kernel
theorem subd16_0_111 : subd16_0 [1, -1, -7] = true := by decide +kernel
theorem subd16_0_112 : subd16_0 [1, -1, -6] = true := by decide +kernel
theorem subd16_0_113 : subd16_0 [1, -1, -5] = true := by decide +kernel
theorem subd16_0_114 : subd16_0 [1, -1, -4] = true := by decide +kernel
theorem subd16_0_115 : subd16_0 [1, -1, -3] = true := by decide +kernel
theorem subd16_0_116 : subd16_0 [1, -1, -2] = true := by decide +kernel
theorem subd16_0_117 : subd16_0 [1, -1, -1] = true := by decide +kernel
theorem subd16_0_118 : subd16_0 [1, -1, 0] = true := by decide +kernel
theorem subd16_0_119 : subd16_0 [1, -1, 1] = true := by decide +kernel
theorem subd16_0_120 : subd16_0 [1, -1, 2] = true := by decide +kernel
theorem subd16_0_121 : subd16_0 [1, -1, 3] = true := by decide +kernel
theorem subd16_0_122 : subd16_0 [1, -1, 4] = true := by decide +kernel
theorem subd16_0_123 : subd16_0 [1, -1, 5] = true := by decide +kernel
theorem subd16_0_124 : subd16_0 [1, -1, 6] = true := by decide +kernel
theorem subd16_0_125 : subd16_0 [1, -1, 7] = true := by decide +kernel
theorem subd16_0_126 : subd16_0 [1, 0, -7] = true := by decide +kernel
theorem subd16_0_127 : subd16_0 [1, 0, -6] = true := by decide +kernel
theorem sbd16_0_3 : ∀ q ∈ blkd16_0_3, subd16_0 q = true := by
  unfold blkd16_0_3
  exact List.forall_mem_cons.2 ⟨subd16_0_96, List.forall_mem_cons.2 ⟨subd16_0_97, List.forall_mem_cons.2 ⟨subd16_0_98, List.forall_mem_cons.2 ⟨subd16_0_99, List.forall_mem_cons.2 ⟨subd16_0_100, List.forall_mem_cons.2 ⟨subd16_0_101, List.forall_mem_cons.2 ⟨subd16_0_102, List.forall_mem_cons.2 ⟨subd16_0_103, List.forall_mem_cons.2 ⟨subd16_0_104, List.forall_mem_cons.2 ⟨subd16_0_105, List.forall_mem_cons.2 ⟨subd16_0_106, List.forall_mem_cons.2 ⟨subd16_0_107, List.forall_mem_cons.2 ⟨subd16_0_108, List.forall_mem_cons.2 ⟨subd16_0_109, List.forall_mem_cons.2 ⟨subd16_0_110, List.forall_mem_cons.2 ⟨subd16_0_111, List.forall_mem_cons.2 ⟨subd16_0_112, List.forall_mem_cons.2 ⟨subd16_0_113, List.forall_mem_cons.2 ⟨subd16_0_114, List.forall_mem_cons.2 ⟨subd16_0_115, List.forall_mem_cons.2 ⟨subd16_0_116, List.forall_mem_cons.2 ⟨subd16_0_117, List.forall_mem_cons.2 ⟨subd16_0_118, List.forall_mem_cons.2 ⟨subd16_0_119, List.forall_mem_cons.2 ⟨subd16_0_120, List.forall_mem_cons.2 ⟨subd16_0_121, List.forall_mem_cons.2 ⟨subd16_0_122, List.forall_mem_cons.2 ⟨subd16_0_123, List.forall_mem_cons.2 ⟨subd16_0_124, List.forall_mem_cons.2 ⟨subd16_0_125, List.forall_mem_cons.2 ⟨subd16_0_126, List.forall_mem_cons.2 ⟨subd16_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_128 : subd16_0 [1, 0, -5] = true := by decide +kernel
theorem subd16_0_129 : subd16_0 [1, 0, -4] = true := by decide +kernel
theorem subd16_0_130 : subd16_0 [1, 0, -3] = true := by decide +kernel
theorem subd16_0_131 : subd16_0 [1, 0, -2] = true := by decide +kernel
theorem subd16_0_132 : subd16_0 [1, 0, -1] = true := by decide +kernel
theorem subd16_0_133 : subd16_0 [1, 0, 0] = true := by decide +kernel
theorem subd16_0_134 : subd16_0 [1, 0, 1] = true := by decide +kernel
theorem subd16_0_135 : subd16_0 [1, 0, 2] = true := by decide +kernel
theorem subd16_0_136 : subd16_0 [1, 0, 3] = true := by decide +kernel
theorem subd16_0_137 : subd16_0 [1, 0, 4] = true := by decide +kernel
theorem subd16_0_138 : subd16_0 [1, 0, 5] = true := by decide +kernel
theorem subd16_0_139 : subd16_0 [1, 0, 6] = true := by decide +kernel
theorem subd16_0_140 : subd16_0 [1, 0, 7] = true := by decide +kernel
theorem subd16_0_141 : subd16_0 [1, 1, -7] = true := by decide +kernel
theorem subd16_0_142 : subd16_0 [1, 1, -6] = true := by decide +kernel
theorem subd16_0_143 : subd16_0 [1, 1, -5] = true := by decide +kernel
theorem subd16_0_144 : subd16_0 [1, 1, -4] = true := by decide +kernel
theorem subd16_0_145 : subd16_0 [1, 1, -3] = true := by decide +kernel
theorem subd16_0_146 : subd16_0 [1, 1, -2] = true := by decide +kernel
theorem subd16_0_147 : subd16_0 [1, 1, -1] = true := by decide +kernel
theorem subd16_0_148 : subd16_0 [1, 1, 0] = true := by decide +kernel
theorem subd16_0_149 : subd16_0 [1, 1, 1] = true := by decide +kernel
theorem subd16_0_150 : subd16_0 [1, 1, 2] = true := by decide +kernel
theorem subd16_0_151 : subd16_0 [1, 1, 3] = true := by decide +kernel
theorem subd16_0_152 : subd16_0 [1, 1, 4] = true := by decide +kernel
theorem subd16_0_153 : subd16_0 [1, 1, 5] = true := by decide +kernel
theorem subd16_0_154 : subd16_0 [1, 1, 6] = true := by decide +kernel
theorem subd16_0_155 : subd16_0 [1, 2] = true := by decide +kernel
theorem subd16_0_156 : subd16_0 [2, -4] = true := by decide +kernel
theorem subd16_0_157 : subd16_0 [2, -3] = true := by decide +kernel
theorem subd16_0_158 : subd16_0 [2, -2] = true := by decide +kernel
theorem subd16_0_159 : subd16_0 [2, -1] = true := by decide +kernel
theorem sbd16_0_4 : ∀ q ∈ blkd16_0_4, subd16_0 q = true := by
  unfold blkd16_0_4
  exact List.forall_mem_cons.2 ⟨subd16_0_128, List.forall_mem_cons.2 ⟨subd16_0_129, List.forall_mem_cons.2 ⟨subd16_0_130, List.forall_mem_cons.2 ⟨subd16_0_131, List.forall_mem_cons.2 ⟨subd16_0_132, List.forall_mem_cons.2 ⟨subd16_0_133, List.forall_mem_cons.2 ⟨subd16_0_134, List.forall_mem_cons.2 ⟨subd16_0_135, List.forall_mem_cons.2 ⟨subd16_0_136, List.forall_mem_cons.2 ⟨subd16_0_137, List.forall_mem_cons.2 ⟨subd16_0_138, List.forall_mem_cons.2 ⟨subd16_0_139, List.forall_mem_cons.2 ⟨subd16_0_140, List.forall_mem_cons.2 ⟨subd16_0_141, List.forall_mem_cons.2 ⟨subd16_0_142, List.forall_mem_cons.2 ⟨subd16_0_143, List.forall_mem_cons.2 ⟨subd16_0_144, List.forall_mem_cons.2 ⟨subd16_0_145, List.forall_mem_cons.2 ⟨subd16_0_146, List.forall_mem_cons.2 ⟨subd16_0_147, List.forall_mem_cons.2 ⟨subd16_0_148, List.forall_mem_cons.2 ⟨subd16_0_149, List.forall_mem_cons.2 ⟨subd16_0_150, List.forall_mem_cons.2 ⟨subd16_0_151, List.forall_mem_cons.2 ⟨subd16_0_152, List.forall_mem_cons.2 ⟨subd16_0_153, List.forall_mem_cons.2 ⟨subd16_0_154, List.forall_mem_cons.2 ⟨subd16_0_155, List.forall_mem_cons.2 ⟨subd16_0_156, List.forall_mem_cons.2 ⟨subd16_0_157, List.forall_mem_cons.2 ⟨subd16_0_158, List.forall_mem_cons.2 ⟨subd16_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_160 : subd16_0 [2, 0] = true := by decide +kernel
theorem subd16_0_161 : subd16_0 [2, 1] = true := by decide +kernel
theorem subd16_0_162 : subd16_0 [3] = true := by decide +kernel
theorem sbd16_0_5 : ∀ q ∈ blkd16_0_5, subd16_0 q = true := by
  unfold blkd16_0_5
  exact List.forall_mem_cons.2 ⟨subd16_0_160, List.forall_mem_cons.2 ⟨subd16_0_161, List.forall_mem_cons.2 ⟨subd16_0_162, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd16_1 : ldCheck G d16_1.U d16_1.ms ldd16_1 = true := by decide +kernel
theorem pre_okd16_1 : subPre G cell16 d16_1 = true := by decide +kernel
theorem subd16_1_0 : subd16_1 [-2] = true := by decide +kernel
theorem subd16_1_1 : subd16_1 [-1, -3] = true := by decide +kernel
theorem subd16_1_2 : subd16_1 [-1, -2] = true := by decide +kernel
theorem subd16_1_3 : subd16_1 [-1, -1] = true := by decide +kernel
theorem subd16_1_4 : subd16_1 [-1, 0] = true := by decide +kernel
theorem subd16_1_5 : subd16_1 [-1, 1] = true := by decide +kernel
theorem subd16_1_6 : subd16_1 [-1, 2] = true := by decide +kernel
theorem subd16_1_7 : subd16_1 [0, -3] = true := by decide +kernel
theorem subd16_1_8 : subd16_1 [0, -2] = true := by decide +kernel
theorem subd16_1_9 : subd16_1 [0, -1] = true := by decide +kernel
theorem subd16_1_10 : subd16_1 [0, 0, -7] = true := by decide +kernel
theorem subd16_1_11 : subd16_1 [0, 0, -6] = true := by decide +kernel
theorem subd16_1_12 : subd16_1 [0, 0, -5] = true := by decide +kernel
theorem subd16_1_13 : subd16_1 [0, 0, -4] = true := by decide +kernel
theorem subd16_1_14 : subd16_1 [0, 0, -3] = true := by decide +kernel
theorem subd16_1_15 : subd16_1 [0, 0, -2] = true := by decide +kernel
theorem subd16_1_16 : subd16_1 [0, 0, -1] = true := by decide +kernel
theorem subd16_1_17 : subd16_1 [0, 0, 0] = true := by decide +kernel
theorem subd16_1_18 : subd16_1 [0, 0, 1] = true := by decide +kernel
theorem subd16_1_19 : subd16_1 [0, 0, 2] = true := by decide +kernel
theorem subd16_1_20 : subd16_1 [0, 0, 3] = true := by decide +kernel
theorem subd16_1_21 : subd16_1 [0, 0, 4] = true := by decide +kernel
theorem subd16_1_22 : subd16_1 [0, 0, 5] = true := by decide +kernel
theorem subd16_1_23 : subd16_1 [0, 0, 6] = true := by decide +kernel
theorem subd16_1_24 : subd16_1 [0, 1] = true := by decide +kernel
theorem subd16_1_25 : subd16_1 [0, 2] = true := by decide +kernel
theorem subd16_1_26 : subd16_1 [1, -3] = true := by decide +kernel
theorem subd16_1_27 : subd16_1 [1, -2] = true := by decide +kernel
theorem subd16_1_28 : subd16_1 [1, -1] = true := by decide +kernel
theorem subd16_1_29 : subd16_1 [1, 0] = true := by decide +kernel
theorem subd16_1_30 : subd16_1 [1, 1] = true := by decide +kernel
theorem subd16_1_31 : subd16_1 [1, 2] = true := by decide +kernel
theorem sbd16_1_0 : ∀ q ∈ blkd16_1_0, subd16_1 q = true := by
  unfold blkd16_1_0
  exact List.forall_mem_cons.2 ⟨subd16_1_0, List.forall_mem_cons.2 ⟨subd16_1_1, List.forall_mem_cons.2 ⟨subd16_1_2, List.forall_mem_cons.2 ⟨subd16_1_3, List.forall_mem_cons.2 ⟨subd16_1_4, List.forall_mem_cons.2 ⟨subd16_1_5, List.forall_mem_cons.2 ⟨subd16_1_6, List.forall_mem_cons.2 ⟨subd16_1_7, List.forall_mem_cons.2 ⟨subd16_1_8, List.forall_mem_cons.2 ⟨subd16_1_9, List.forall_mem_cons.2 ⟨subd16_1_10, List.forall_mem_cons.2 ⟨subd16_1_11, List.forall_mem_cons.2 ⟨subd16_1_12, List.forall_mem_cons.2 ⟨subd16_1_13, List.forall_mem_cons.2 ⟨subd16_1_14, List.forall_mem_cons.2 ⟨subd16_1_15, List.forall_mem_cons.2 ⟨subd16_1_16, List.forall_mem_cons.2 ⟨subd16_1_17, List.forall_mem_cons.2 ⟨subd16_1_18, List.forall_mem_cons.2 ⟨subd16_1_19, List.forall_mem_cons.2 ⟨subd16_1_20, List.forall_mem_cons.2 ⟨subd16_1_21, List.forall_mem_cons.2 ⟨subd16_1_22, List.forall_mem_cons.2 ⟨subd16_1_23, List.forall_mem_cons.2 ⟨subd16_1_24, List.forall_mem_cons.2 ⟨subd16_1_25, List.forall_mem_cons.2 ⟨subd16_1_26, List.forall_mem_cons.2 ⟨subd16_1_27, List.forall_mem_cons.2 ⟨subd16_1_28, List.forall_mem_cons.2 ⟨subd16_1_29, List.forall_mem_cons.2 ⟨subd16_1_30, List.forall_mem_cons.2 ⟨subd16_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_32 : subd16_1 [2] = true := by decide +kernel
theorem sbd16_1_1 : ∀ q ∈ blkd16_1_1, subd16_1 q = true := by
  unfold blkd16_1_1
  exact List.forall_mem_cons.2 ⟨subd16_1_32, List.forall_mem_nil _⟩
theorem ld_okd17_0 : ldCheck G d17_0.U d17_0.ms ldd17_0 = true := by decide +kernel
theorem pre_okd17_0 : subPre G cell17 d17_0 = true := by decide +kernel
theorem subd17_0_0 : subd17_0 [-2] = true := by decide +kernel
theorem subd17_0_1 : subd17_0 [-1, -3] = true := by decide +kernel
theorem subd17_0_2 : subd17_0 [-1, -2] = true := by decide +kernel
theorem subd17_0_3 : subd17_0 [-1, -1, -8] = true := by decide +kernel
theorem subd17_0_4 : subd17_0 [-1, -1, -7] = true := by decide +kernel
theorem subd17_0_5 : subd17_0 [-1, -1, -6] = true := by decide +kernel
theorem subd17_0_6 : subd17_0 [-1, -1, -5] = true := by decide +kernel
theorem subd17_0_7 : subd17_0 [-1, -1, -4] = true := by decide +kernel
theorem subd17_0_8 : subd17_0 [-1, -1, -3] = true := by decide +kernel
theorem subd17_0_9 : subd17_0 [-1, -1, -2] = true := by decide +kernel
theorem subd17_0_10 : subd17_0 [-1, -1, -1] = true := by decide +kernel
theorem subd17_0_11 : subd17_0 [-1, -1, 0] = true := by decide +kernel
theorem subd17_0_12 : subd17_0 [-1, -1, 1] = true := by decide +kernel
theorem subd17_0_13 : subd17_0 [-1, -1, 2] = true := by decide +kernel
theorem subd17_0_14 : subd17_0 [-1, -1, 3] = true := by decide +kernel
theorem subd17_0_15 : subd17_0 [-1, -1, 4] = true := by decide +kernel
theorem subd17_0_16 : subd17_0 [-1, -1, 5] = true := by decide +kernel
theorem subd17_0_17 : subd17_0 [-1, -1, 6] = true := by decide +kernel
theorem subd17_0_18 : subd17_0 [-1, 0, -8] = true := by decide +kernel
theorem subd17_0_19 : subd17_0 [-1, 0, -7] = true := by decide +kernel
theorem subd17_0_20 : subd17_0 [-1, 0, -6] = true := by decide +kernel
theorem subd17_0_21 : subd17_0 [-1, 0, -5] = true := by decide +kernel
theorem subd17_0_22 : subd17_0 [-1, 0, -4] = true := by decide +kernel
theorem subd17_0_23 : subd17_0 [-1, 0, -3] = true := by decide +kernel
theorem subd17_0_24 : subd17_0 [-1, 0, -2] = true := by decide +kernel
theorem subd17_0_25 : subd17_0 [-1, 0, -1] = true := by decide +kernel
theorem subd17_0_26 : subd17_0 [-1, 0, 0] = true := by decide +kernel
theorem subd17_0_27 : subd17_0 [-1, 0, 1] = true := by decide +kernel
theorem subd17_0_28 : subd17_0 [-1, 0, 2] = true := by decide +kernel
theorem subd17_0_29 : subd17_0 [-1, 0, 3] = true := by decide +kernel
theorem subd17_0_30 : subd17_0 [-1, 0, 4] = true := by decide +kernel
theorem subd17_0_31 : subd17_0 [-1, 0, 5] = true := by decide +kernel
theorem sbd17_0_0 : ∀ q ∈ blkd17_0_0, subd17_0 q = true := by
  unfold blkd17_0_0
  exact List.forall_mem_cons.2 ⟨subd17_0_0, List.forall_mem_cons.2 ⟨subd17_0_1, List.forall_mem_cons.2 ⟨subd17_0_2, List.forall_mem_cons.2 ⟨subd17_0_3, List.forall_mem_cons.2 ⟨subd17_0_4, List.forall_mem_cons.2 ⟨subd17_0_5, List.forall_mem_cons.2 ⟨subd17_0_6, List.forall_mem_cons.2 ⟨subd17_0_7, List.forall_mem_cons.2 ⟨subd17_0_8, List.forall_mem_cons.2 ⟨subd17_0_9, List.forall_mem_cons.2 ⟨subd17_0_10, List.forall_mem_cons.2 ⟨subd17_0_11, List.forall_mem_cons.2 ⟨subd17_0_12, List.forall_mem_cons.2 ⟨subd17_0_13, List.forall_mem_cons.2 ⟨subd17_0_14, List.forall_mem_cons.2 ⟨subd17_0_15, List.forall_mem_cons.2 ⟨subd17_0_16, List.forall_mem_cons.2 ⟨subd17_0_17, List.forall_mem_cons.2 ⟨subd17_0_18, List.forall_mem_cons.2 ⟨subd17_0_19, List.forall_mem_cons.2 ⟨subd17_0_20, List.forall_mem_cons.2 ⟨subd17_0_21, List.forall_mem_cons.2 ⟨subd17_0_22, List.forall_mem_cons.2 ⟨subd17_0_23, List.forall_mem_cons.2 ⟨subd17_0_24, List.forall_mem_cons.2 ⟨subd17_0_25, List.forall_mem_cons.2 ⟨subd17_0_26, List.forall_mem_cons.2 ⟨subd17_0_27, List.forall_mem_cons.2 ⟨subd17_0_28, List.forall_mem_cons.2 ⟨subd17_0_29, List.forall_mem_cons.2 ⟨subd17_0_30, List.forall_mem_cons.2 ⟨subd17_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_32 : subd17_0 [-1, 0, 6] = true := by decide +kernel
theorem subd17_0_33 : subd17_0 [-1, 0, 7] = true := by decide +kernel
theorem subd17_0_34 : subd17_0 [-1, 1] = true := by decide +kernel
theorem subd17_0_35 : subd17_0 [0, -3] = true := by decide +kernel
theorem subd17_0_36 : subd17_0 [0, -2] = true := by decide +kernel
theorem subd17_0_37 : subd17_0 [0, -1, -9] = true := by decide +kernel
theorem subd17_0_38 : subd17_0 [0, -1, -8] = true := by decide +kernel
theorem subd17_0_39 : subd17_0 [0, -1, -7] = true := by decide +kernel
theorem subd17_0_40 : subd17_0 [0, -1, -6] = true := by decide +kernel
theorem subd17_0_41 : subd17_0 [0, -1, -5] = true := by decide +kernel
theorem subd17_0_42 : subd17_0 [0, -1, -4] = true := by decide +kernel
theorem subd17_0_43 : subd17_0 [0, -1, -3] = true := by decide +kernel
theorem subd17_0_44 : subd17_0 [0, -1, -2] = true := by decide +kernel
theorem subd17_0_45 : subd17_0 [0, -1, -1] = true := by decide +kernel
theorem subd17_0_46 : subd17_0 [0, -1, 0] = true := by decide +kernel
theorem subd17_0_47 : subd17_0 [0, -1, 1] = true := by decide +kernel
theorem subd17_0_48 : subd17_0 [0, -1, 2] = true := by decide +kernel
theorem subd17_0_49 : subd17_0 [0, -1, 3] = true := by decide +kernel
theorem subd17_0_50 : subd17_0 [0, -1, 4] = true := by decide +kernel
theorem subd17_0_51 : subd17_0 [0, -1, 5] = true := by decide +kernel
theorem subd17_0_52 : subd17_0 [0, -1, 6] = true := by decide +kernel
theorem subd17_0_53 : subd17_0 [0, -1, 7] = true := by decide +kernel
theorem subd17_0_54 : subd17_0 [0, 0, -9] = true := by decide +kernel
theorem subd17_0_55 : subd17_0 [0, 0, -8] = true := by decide +kernel
theorem subd17_0_56 : subd17_0 [0, 0, -7] = true := by decide +kernel
theorem subd17_0_57 : subd17_0 [0, 0, -6] = true := by decide +kernel
theorem subd17_0_58 : subd17_0 [0, 0, -5] = true := by decide +kernel
theorem subd17_0_59 : subd17_0 [0, 0, -4] = true := by decide +kernel
theorem subd17_0_60 : subd17_0 [0, 0, -3] = true := by decide +kernel
theorem subd17_0_61 : subd17_0 [0, 0, -2] = true := by decide +kernel
theorem subd17_0_62 : subd17_0 [0, 0, -1] = true := by decide +kernel
theorem subd17_0_63 : subd17_0 [0, 0, 0] = true := by decide +kernel
theorem sbd17_0_1 : ∀ q ∈ blkd17_0_1, subd17_0 q = true := by
  unfold blkd17_0_1
  exact List.forall_mem_cons.2 ⟨subd17_0_32, List.forall_mem_cons.2 ⟨subd17_0_33, List.forall_mem_cons.2 ⟨subd17_0_34, List.forall_mem_cons.2 ⟨subd17_0_35, List.forall_mem_cons.2 ⟨subd17_0_36, List.forall_mem_cons.2 ⟨subd17_0_37, List.forall_mem_cons.2 ⟨subd17_0_38, List.forall_mem_cons.2 ⟨subd17_0_39, List.forall_mem_cons.2 ⟨subd17_0_40, List.forall_mem_cons.2 ⟨subd17_0_41, List.forall_mem_cons.2 ⟨subd17_0_42, List.forall_mem_cons.2 ⟨subd17_0_43, List.forall_mem_cons.2 ⟨subd17_0_44, List.forall_mem_cons.2 ⟨subd17_0_45, List.forall_mem_cons.2 ⟨subd17_0_46, List.forall_mem_cons.2 ⟨subd17_0_47, List.forall_mem_cons.2 ⟨subd17_0_48, List.forall_mem_cons.2 ⟨subd17_0_49, List.forall_mem_cons.2 ⟨subd17_0_50, List.forall_mem_cons.2 ⟨subd17_0_51, List.forall_mem_cons.2 ⟨subd17_0_52, List.forall_mem_cons.2 ⟨subd17_0_53, List.forall_mem_cons.2 ⟨subd17_0_54, List.forall_mem_cons.2 ⟨subd17_0_55, List.forall_mem_cons.2 ⟨subd17_0_56, List.forall_mem_cons.2 ⟨subd17_0_57, List.forall_mem_cons.2 ⟨subd17_0_58, List.forall_mem_cons.2 ⟨subd17_0_59, List.forall_mem_cons.2 ⟨subd17_0_60, List.forall_mem_cons.2 ⟨subd17_0_61, List.forall_mem_cons.2 ⟨subd17_0_62, List.forall_mem_cons.2 ⟨subd17_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_64 : subd17_0 [0, 0, 1] = true := by decide +kernel
theorem subd17_0_65 : subd17_0 [0, 0, 2] = true := by decide +kernel
theorem subd17_0_66 : subd17_0 [0, 0, 3] = true := by decide +kernel
theorem subd17_0_67 : subd17_0 [0, 0, 4] = true := by decide +kernel
theorem subd17_0_68 : subd17_0 [0, 0, 5] = true := by decide +kernel
theorem subd17_0_69 : subd17_0 [0, 0, 6] = true := by decide +kernel
theorem subd17_0_70 : subd17_0 [0, 0, 7] = true := by decide +kernel
theorem subd17_0_71 : subd17_0 [0, 0, 8] = true := by decide +kernel
theorem subd17_0_72 : subd17_0 [0, 1, -8] = true := by decide +kernel
theorem subd17_0_73 : subd17_0 [0, 1, -7] = true := by decide +kernel
theorem subd17_0_74 : subd17_0 [0, 1, -6] = true := by decide +kernel
theorem subd17_0_75 : subd17_0 [0, 1, -5] = true := by decide +kernel
theorem subd17_0_76 : subd17_0 [0, 1, -4] = true := by decide +kernel
theorem subd17_0_77 : subd17_0 [0, 1, -3] = true := by decide +kernel
theorem subd17_0_78 : subd17_0 [0, 1, -2] = true := by decide +kernel
theorem subd17_0_79 : subd17_0 [0, 1, -1] = true := by decide +kernel
theorem subd17_0_80 : subd17_0 [0, 1, 0] = true := by decide +kernel
theorem subd17_0_81 : subd17_0 [0, 1, 1] = true := by decide +kernel
theorem subd17_0_82 : subd17_0 [0, 1, 2] = true := by decide +kernel
theorem subd17_0_83 : subd17_0 [0, 1, 3] = true := by decide +kernel
theorem subd17_0_84 : subd17_0 [0, 1, 4] = true := by decide +kernel
theorem subd17_0_85 : subd17_0 [0, 1, 5] = true := by decide +kernel
theorem subd17_0_86 : subd17_0 [0, 1, 6] = true := by decide +kernel
theorem subd17_0_87 : subd17_0 [0, 1, 7] = true := by decide +kernel
theorem subd17_0_88 : subd17_0 [0, 1, 8] = true := by decide +kernel
theorem subd17_0_89 : subd17_0 [0, 2] = true := by decide +kernel
theorem subd17_0_90 : subd17_0 [1, -2] = true := by decide +kernel
theorem subd17_0_91 : subd17_0 [1, -1] = true := by decide +kernel
theorem subd17_0_92 : subd17_0 [1, 0, -8] = true := by decide +kernel
theorem subd17_0_93 : subd17_0 [1, 0, -7] = true := by decide +kernel
theorem subd17_0_94 : subd17_0 [1, 0, -6] = true := by decide +kernel
theorem subd17_0_95 : subd17_0 [1, 0, -5] = true := by decide +kernel
theorem sbd17_0_2 : ∀ q ∈ blkd17_0_2, subd17_0 q = true := by
  unfold blkd17_0_2
  exact List.forall_mem_cons.2 ⟨subd17_0_64, List.forall_mem_cons.2 ⟨subd17_0_65, List.forall_mem_cons.2 ⟨subd17_0_66, List.forall_mem_cons.2 ⟨subd17_0_67, List.forall_mem_cons.2 ⟨subd17_0_68, List.forall_mem_cons.2 ⟨subd17_0_69, List.forall_mem_cons.2 ⟨subd17_0_70, List.forall_mem_cons.2 ⟨subd17_0_71, List.forall_mem_cons.2 ⟨subd17_0_72, List.forall_mem_cons.2 ⟨subd17_0_73, List.forall_mem_cons.2 ⟨subd17_0_74, List.forall_mem_cons.2 ⟨subd17_0_75, List.forall_mem_cons.2 ⟨subd17_0_76, List.forall_mem_cons.2 ⟨subd17_0_77, List.forall_mem_cons.2 ⟨subd17_0_78, List.forall_mem_cons.2 ⟨subd17_0_79, List.forall_mem_cons.2 ⟨subd17_0_80, List.forall_mem_cons.2 ⟨subd17_0_81, List.forall_mem_cons.2 ⟨subd17_0_82, List.forall_mem_cons.2 ⟨subd17_0_83, List.forall_mem_cons.2 ⟨subd17_0_84, List.forall_mem_cons.2 ⟨subd17_0_85, List.forall_mem_cons.2 ⟨subd17_0_86, List.forall_mem_cons.2 ⟨subd17_0_87, List.forall_mem_cons.2 ⟨subd17_0_88, List.forall_mem_cons.2 ⟨subd17_0_89, List.forall_mem_cons.2 ⟨subd17_0_90, List.forall_mem_cons.2 ⟨subd17_0_91, List.forall_mem_cons.2 ⟨subd17_0_92, List.forall_mem_cons.2 ⟨subd17_0_93, List.forall_mem_cons.2 ⟨subd17_0_94, List.forall_mem_cons.2 ⟨subd17_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_96 : subd17_0 [1, 0, -4] = true := by decide +kernel
theorem subd17_0_97 : subd17_0 [1, 0, -3] = true := by decide +kernel
theorem subd17_0_98 : subd17_0 [1, 0, -2] = true := by decide +kernel
theorem subd17_0_99 : subd17_0 [1, 0, -1] = true := by decide +kernel
theorem subd17_0_100 : subd17_0 [1, 0, 0] = true := by decide +kernel
theorem subd17_0_101 : subd17_0 [1, 0, 1] = true := by decide +kernel
theorem subd17_0_102 : subd17_0 [1, 0, 2] = true := by decide +kernel
theorem subd17_0_103 : subd17_0 [1, 0, 3] = true := by decide +kernel
theorem subd17_0_104 : subd17_0 [1, 0, 4] = true := by decide +kernel
theorem subd17_0_105 : subd17_0 [1, 0, 5] = true := by decide +kernel
theorem subd17_0_106 : subd17_0 [1, 0, 6] = true := by decide +kernel
theorem subd17_0_107 : subd17_0 [1, 0, 7] = true := by decide +kernel
theorem subd17_0_108 : subd17_0 [1, 1, -7] = true := by decide +kernel
theorem subd17_0_109 : subd17_0 [1, 1, -6] = true := by decide +kernel
theorem subd17_0_110 : subd17_0 [1, 1, -5] = true := by decide +kernel
theorem subd17_0_111 : subd17_0 [1, 1, -4] = true := by decide +kernel
theorem subd17_0_112 : subd17_0 [1, 1, -3] = true := by decide +kernel
theorem subd17_0_113 : subd17_0 [1, 1, -2] = true := by decide +kernel
theorem subd17_0_114 : subd17_0 [1, 1, -1] = true := by decide +kernel
theorem subd17_0_115 : subd17_0 [1, 1, 0] = true := by decide +kernel
theorem subd17_0_116 : subd17_0 [1, 1, 1] = true := by decide +kernel
theorem subd17_0_117 : subd17_0 [1, 1, 2] = true := by decide +kernel
theorem subd17_0_118 : subd17_0 [1, 1, 3] = true := by decide +kernel
theorem subd17_0_119 : subd17_0 [1, 1, 4] = true := by decide +kernel
theorem subd17_0_120 : subd17_0 [1, 1, 5] = true := by decide +kernel
theorem subd17_0_121 : subd17_0 [1, 1, 6] = true := by decide +kernel
theorem subd17_0_122 : subd17_0 [1, 1, 7] = true := by decide +kernel
theorem subd17_0_123 : subd17_0 [1, 2] = true := by decide +kernel
theorem subd17_0_124 : subd17_0 [2] = true := by decide +kernel
theorem sbd17_0_3 : ∀ q ∈ blkd17_0_3, subd17_0 q = true := by
  unfold blkd17_0_3
  exact List.forall_mem_cons.2 ⟨subd17_0_96, List.forall_mem_cons.2 ⟨subd17_0_97, List.forall_mem_cons.2 ⟨subd17_0_98, List.forall_mem_cons.2 ⟨subd17_0_99, List.forall_mem_cons.2 ⟨subd17_0_100, List.forall_mem_cons.2 ⟨subd17_0_101, List.forall_mem_cons.2 ⟨subd17_0_102, List.forall_mem_cons.2 ⟨subd17_0_103, List.forall_mem_cons.2 ⟨subd17_0_104, List.forall_mem_cons.2 ⟨subd17_0_105, List.forall_mem_cons.2 ⟨subd17_0_106, List.forall_mem_cons.2 ⟨subd17_0_107, List.forall_mem_cons.2 ⟨subd17_0_108, List.forall_mem_cons.2 ⟨subd17_0_109, List.forall_mem_cons.2 ⟨subd17_0_110, List.forall_mem_cons.2 ⟨subd17_0_111, List.forall_mem_cons.2 ⟨subd17_0_112, List.forall_mem_cons.2 ⟨subd17_0_113, List.forall_mem_cons.2 ⟨subd17_0_114, List.forall_mem_cons.2 ⟨subd17_0_115, List.forall_mem_cons.2 ⟨subd17_0_116, List.forall_mem_cons.2 ⟨subd17_0_117, List.forall_mem_cons.2 ⟨subd17_0_118, List.forall_mem_cons.2 ⟨subd17_0_119, List.forall_mem_cons.2 ⟨subd17_0_120, List.forall_mem_cons.2 ⟨subd17_0_121, List.forall_mem_cons.2 ⟨subd17_0_122, List.forall_mem_cons.2 ⟨subd17_0_123, List.forall_mem_cons.2 ⟨subd17_0_124, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
