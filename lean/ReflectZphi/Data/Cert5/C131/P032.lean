import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_0_96 : subd15_0 [0, 1, -5] = true := by decide +kernel
theorem subd15_0_97 : subd15_0 [0, 1, -4] = true := by decide +kernel
theorem subd15_0_98 : subd15_0 [0, 1, -3] = true := by decide +kernel
theorem subd15_0_99 : subd15_0 [0, 1, -2] = true := by decide +kernel
theorem subd15_0_100 : subd15_0 [0, 1, -1] = true := by decide +kernel
theorem subd15_0_101 : subd15_0 [0, 1, 0] = true := by decide +kernel
theorem subd15_0_102 : subd15_0 [0, 1, 1] = true := by decide +kernel
theorem subd15_0_103 : subd15_0 [0, 1, 2] = true := by decide +kernel
theorem subd15_0_104 : subd15_0 [0, 1, 3] = true := by decide +kernel
theorem subd15_0_105 : subd15_0 [0, 1, 4] = true := by decide +kernel
theorem subd15_0_106 : subd15_0 [0, 1, 5] = true := by decide +kernel
theorem subd15_0_107 : subd15_0 [0, 1, 6] = true := by decide +kernel
theorem subd15_0_108 : subd15_0 [0, 2] = true := by decide +kernel
theorem subd15_0_109 : subd15_0 [0, 3] = true := by decide +kernel
theorem subd15_0_110 : subd15_0 [0, 4] = true := by decide +kernel
theorem subd15_0_111 : subd15_0 [1, -4] = true := by decide +kernel
theorem subd15_0_112 : subd15_0 [1, -3] = true := by decide +kernel
theorem subd15_0_113 : subd15_0 [1, -2] = true := by decide +kernel
theorem subd15_0_114 : subd15_0 [1, -1, -7] = true := by decide +kernel
theorem subd15_0_115 : subd15_0 [1, -1, -6] = true := by decide +kernel
theorem subd15_0_116 : subd15_0 [1, -1, -5] = true := by decide +kernel
theorem subd15_0_117 : subd15_0 [1, -1, -4] = true := by decide +kernel
theorem subd15_0_118 : subd15_0 [1, -1, -3] = true := by decide +kernel
theorem subd15_0_119 : subd15_0 [1, -1, -2] = true := by decide +kernel
theorem subd15_0_120 : subd15_0 [1, -1, -1] = true := by decide +kernel
theorem subd15_0_121 : subd15_0 [1, -1, 0] = true := by decide +kernel
theorem subd15_0_122 : subd15_0 [1, -1, 1] = true := by decide +kernel
theorem subd15_0_123 : subd15_0 [1, -1, 2] = true := by decide +kernel
theorem subd15_0_124 : subd15_0 [1, -1, 3] = true := by decide +kernel
theorem subd15_0_125 : subd15_0 [1, -1, 4] = true := by decide +kernel
theorem subd15_0_126 : subd15_0 [1, -1, 5] = true := by decide +kernel
theorem subd15_0_127 : subd15_0 [1, 0, -7] = true := by decide +kernel
theorem sbd15_0_3 : ∀ q ∈ blkd15_0_3, subd15_0 q = true := by
  unfold blkd15_0_3
  exact List.forall_mem_cons.2 ⟨subd15_0_96, List.forall_mem_cons.2 ⟨subd15_0_97, List.forall_mem_cons.2 ⟨subd15_0_98, List.forall_mem_cons.2 ⟨subd15_0_99, List.forall_mem_cons.2 ⟨subd15_0_100, List.forall_mem_cons.2 ⟨subd15_0_101, List.forall_mem_cons.2 ⟨subd15_0_102, List.forall_mem_cons.2 ⟨subd15_0_103, List.forall_mem_cons.2 ⟨subd15_0_104, List.forall_mem_cons.2 ⟨subd15_0_105, List.forall_mem_cons.2 ⟨subd15_0_106, List.forall_mem_cons.2 ⟨subd15_0_107, List.forall_mem_cons.2 ⟨subd15_0_108, List.forall_mem_cons.2 ⟨subd15_0_109, List.forall_mem_cons.2 ⟨subd15_0_110, List.forall_mem_cons.2 ⟨subd15_0_111, List.forall_mem_cons.2 ⟨subd15_0_112, List.forall_mem_cons.2 ⟨subd15_0_113, List.forall_mem_cons.2 ⟨subd15_0_114, List.forall_mem_cons.2 ⟨subd15_0_115, List.forall_mem_cons.2 ⟨subd15_0_116, List.forall_mem_cons.2 ⟨subd15_0_117, List.forall_mem_cons.2 ⟨subd15_0_118, List.forall_mem_cons.2 ⟨subd15_0_119, List.forall_mem_cons.2 ⟨subd15_0_120, List.forall_mem_cons.2 ⟨subd15_0_121, List.forall_mem_cons.2 ⟨subd15_0_122, List.forall_mem_cons.2 ⟨subd15_0_123, List.forall_mem_cons.2 ⟨subd15_0_124, List.forall_mem_cons.2 ⟨subd15_0_125, List.forall_mem_cons.2 ⟨subd15_0_126, List.forall_mem_cons.2 ⟨subd15_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_128 : subd15_0 [1, 0, -6] = true := by decide +kernel
theorem subd15_0_129 : subd15_0 [1, 0, -5] = true := by decide +kernel
theorem subd15_0_130 : subd15_0 [1, 0, -4] = true := by decide +kernel
theorem subd15_0_131 : subd15_0 [1, 0, -3] = true := by decide +kernel
theorem subd15_0_132 : subd15_0 [1, 0, -2] = true := by decide +kernel
theorem subd15_0_133 : subd15_0 [1, 0, -1] = true := by decide +kernel
theorem subd15_0_134 : subd15_0 [1, 0, 0] = true := by decide +kernel
theorem subd15_0_135 : subd15_0 [1, 0, 1] = true := by decide +kernel
theorem subd15_0_136 : subd15_0 [1, 0, 2] = true := by decide +kernel
theorem subd15_0_137 : subd15_0 [1, 0, 3] = true := by decide +kernel
theorem subd15_0_138 : subd15_0 [1, 0, 4] = true := by decide +kernel
theorem subd15_0_139 : subd15_0 [1, 0, 5] = true := by decide +kernel
theorem subd15_0_140 : subd15_0 [1, 0, 6] = true := by decide +kernel
theorem subd15_0_141 : subd15_0 [1, 1, -7] = true := by decide +kernel
theorem subd15_0_142 : subd15_0 [1, 1, -6] = true := by decide +kernel
theorem subd15_0_143 : subd15_0 [1, 1, -5] = true := by decide +kernel
theorem subd15_0_144 : subd15_0 [1, 1, -4] = true := by decide +kernel
theorem subd15_0_145 : subd15_0 [1, 1, -3] = true := by decide +kernel
theorem subd15_0_146 : subd15_0 [1, 1, -2] = true := by decide +kernel
theorem subd15_0_147 : subd15_0 [1, 1, -1] = true := by decide +kernel
theorem subd15_0_148 : subd15_0 [1, 1, 0] = true := by decide +kernel
theorem subd15_0_149 : subd15_0 [1, 1, 1] = true := by decide +kernel
theorem subd15_0_150 : subd15_0 [1, 1, 2] = true := by decide +kernel
theorem subd15_0_151 : subd15_0 [1, 1, 3] = true := by decide +kernel
theorem subd15_0_152 : subd15_0 [1, 1, 4] = true := by decide +kernel
theorem subd15_0_153 : subd15_0 [1, 1, 5] = true := by decide +kernel
theorem subd15_0_154 : subd15_0 [1, 1, 6] = true := by decide +kernel
theorem subd15_0_155 : subd15_0 [1, 2] = true := by decide +kernel
theorem subd15_0_156 : subd15_0 [1, 3] = true := by decide +kernel
theorem subd15_0_157 : subd15_0 [1, 4] = true := by decide +kernel
theorem subd15_0_158 : subd15_0 [2, -4] = true := by decide +kernel
theorem subd15_0_159 : subd15_0 [2, -3] = true := by decide +kernel
theorem sbd15_0_4 : ∀ q ∈ blkd15_0_4, subd15_0 q = true := by
  unfold blkd15_0_4
  exact List.forall_mem_cons.2 ⟨subd15_0_128, List.forall_mem_cons.2 ⟨subd15_0_129, List.forall_mem_cons.2 ⟨subd15_0_130, List.forall_mem_cons.2 ⟨subd15_0_131, List.forall_mem_cons.2 ⟨subd15_0_132, List.forall_mem_cons.2 ⟨subd15_0_133, List.forall_mem_cons.2 ⟨subd15_0_134, List.forall_mem_cons.2 ⟨subd15_0_135, List.forall_mem_cons.2 ⟨subd15_0_136, List.forall_mem_cons.2 ⟨subd15_0_137, List.forall_mem_cons.2 ⟨subd15_0_138, List.forall_mem_cons.2 ⟨subd15_0_139, List.forall_mem_cons.2 ⟨subd15_0_140, List.forall_mem_cons.2 ⟨subd15_0_141, List.forall_mem_cons.2 ⟨subd15_0_142, List.forall_mem_cons.2 ⟨subd15_0_143, List.forall_mem_cons.2 ⟨subd15_0_144, List.forall_mem_cons.2 ⟨subd15_0_145, List.forall_mem_cons.2 ⟨subd15_0_146, List.forall_mem_cons.2 ⟨subd15_0_147, List.forall_mem_cons.2 ⟨subd15_0_148, List.forall_mem_cons.2 ⟨subd15_0_149, List.forall_mem_cons.2 ⟨subd15_0_150, List.forall_mem_cons.2 ⟨subd15_0_151, List.forall_mem_cons.2 ⟨subd15_0_152, List.forall_mem_cons.2 ⟨subd15_0_153, List.forall_mem_cons.2 ⟨subd15_0_154, List.forall_mem_cons.2 ⟨subd15_0_155, List.forall_mem_cons.2 ⟨subd15_0_156, List.forall_mem_cons.2 ⟨subd15_0_157, List.forall_mem_cons.2 ⟨subd15_0_158, List.forall_mem_cons.2 ⟨subd15_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_160 : subd15_0 [2, -2] = true := by decide +kernel
theorem subd15_0_161 : subd15_0 [2, -1] = true := by decide +kernel
theorem subd15_0_162 : subd15_0 [2, 0] = true := by decide +kernel
theorem subd15_0_163 : subd15_0 [2, 1] = true := by decide +kernel
theorem subd15_0_164 : subd15_0 [2, 2] = true := by decide +kernel
theorem subd15_0_165 : subd15_0 [2, 3] = true := by decide +kernel
theorem subd15_0_166 : subd15_0 [2, 4] = true := by decide +kernel
theorem subd15_0_167 : subd15_0 [3, -2] = true := by decide +kernel
theorem subd15_0_168 : subd15_0 [3, -1] = true := by decide +kernel
theorem subd15_0_169 : subd15_0 [3, 0] = true := by decide +kernel
theorem subd15_0_170 : subd15_0 [3, 1] = true := by decide +kernel
theorem subd15_0_171 : subd15_0 [3, 2] = true := by decide +kernel
theorem subd15_0_172 : subd15_0 [3, 3] = true := by decide +kernel
theorem sbd15_0_5 : ∀ q ∈ blkd15_0_5, subd15_0 q = true := by
  unfold blkd15_0_5
  exact List.forall_mem_cons.2 ⟨subd15_0_160, List.forall_mem_cons.2 ⟨subd15_0_161, List.forall_mem_cons.2 ⟨subd15_0_162, List.forall_mem_cons.2 ⟨subd15_0_163, List.forall_mem_cons.2 ⟨subd15_0_164, List.forall_mem_cons.2 ⟨subd15_0_165, List.forall_mem_cons.2 ⟨subd15_0_166, List.forall_mem_cons.2 ⟨subd15_0_167, List.forall_mem_cons.2 ⟨subd15_0_168, List.forall_mem_cons.2 ⟨subd15_0_169, List.forall_mem_cons.2 ⟨subd15_0_170, List.forall_mem_cons.2 ⟨subd15_0_171, List.forall_mem_cons.2 ⟨subd15_0_172, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel
theorem subd15_1_0 : subd15_1 [-3] = true := by decide +kernel
theorem subd15_1_1 : subd15_1 [-2, -4] = true := by decide +kernel
theorem subd15_1_2 : subd15_1 [-2, -3] = true := by decide +kernel
theorem subd15_1_3 : subd15_1 [-2, -2] = true := by decide +kernel
theorem subd15_1_4 : subd15_1 [-2, -1] = true := by decide +kernel
theorem subd15_1_5 : subd15_1 [-2, 0] = true := by decide +kernel
theorem subd15_1_6 : subd15_1 [-2, 1] = true := by decide +kernel
theorem subd15_1_7 : subd15_1 [-1, -4] = true := by decide +kernel
theorem subd15_1_8 : subd15_1 [-1, -3] = true := by decide +kernel
theorem subd15_1_9 : subd15_1 [-1, -2] = true := by decide +kernel
theorem subd15_1_10 : subd15_1 [-1, -1] = true := by decide +kernel
theorem subd15_1_11 : subd15_1 [-1, 0] = true := by decide +kernel
theorem subd15_1_12 : subd15_1 [-1, 1] = true := by decide +kernel
theorem subd15_1_13 : subd15_1 [-1, 2] = true := by decide +kernel
theorem subd15_1_14 : subd15_1 [0, -4] = true := by decide +kernel
theorem subd15_1_15 : subd15_1 [0, -3] = true := by decide +kernel
theorem subd15_1_16 : subd15_1 [0, -2] = true := by decide +kernel
theorem subd15_1_17 : subd15_1 [0, -1] = true := by decide +kernel
theorem subd15_1_18 : subd15_1 [0, 0] = true := by decide +kernel
theorem subd15_1_19 : subd15_1 [0, 1] = true := by decide +kernel
theorem subd15_1_20 : subd15_1 [0, 2] = true := by decide +kernel
theorem subd15_1_21 : subd15_1 [0, 3] = true := by decide +kernel
theorem subd15_1_22 : subd15_1 [1, -3] = true := by decide +kernel
theorem subd15_1_23 : subd15_1 [1, -2] = true := by decide +kernel
theorem subd15_1_24 : subd15_1 [1, -1] = true := by decide +kernel
theorem subd15_1_25 : subd15_1 [1, 0] = true := by decide +kernel
theorem subd15_1_26 : subd15_1 [1, 1] = true := by decide +kernel
theorem subd15_1_27 : subd15_1 [1, 2] = true := by decide +kernel
theorem subd15_1_28 : subd15_1 [1, 3] = true := by decide +kernel
theorem subd15_1_29 : subd15_1 [2, -2] = true := by decide +kernel
theorem subd15_1_30 : subd15_1 [2, -1] = true := by decide +kernel
theorem subd15_1_31 : subd15_1 [2, 0] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_cons.2 ⟨subd15_1_1, List.forall_mem_cons.2 ⟨subd15_1_2, List.forall_mem_cons.2 ⟨subd15_1_3, List.forall_mem_cons.2 ⟨subd15_1_4, List.forall_mem_cons.2 ⟨subd15_1_5, List.forall_mem_cons.2 ⟨subd15_1_6, List.forall_mem_cons.2 ⟨subd15_1_7, List.forall_mem_cons.2 ⟨subd15_1_8, List.forall_mem_cons.2 ⟨subd15_1_9, List.forall_mem_cons.2 ⟨subd15_1_10, List.forall_mem_cons.2 ⟨subd15_1_11, List.forall_mem_cons.2 ⟨subd15_1_12, List.forall_mem_cons.2 ⟨subd15_1_13, List.forall_mem_cons.2 ⟨subd15_1_14, List.forall_mem_cons.2 ⟨subd15_1_15, List.forall_mem_cons.2 ⟨subd15_1_16, List.forall_mem_cons.2 ⟨subd15_1_17, List.forall_mem_cons.2 ⟨subd15_1_18, List.forall_mem_cons.2 ⟨subd15_1_19, List.forall_mem_cons.2 ⟨subd15_1_20, List.forall_mem_cons.2 ⟨subd15_1_21, List.forall_mem_cons.2 ⟨subd15_1_22, List.forall_mem_cons.2 ⟨subd15_1_23, List.forall_mem_cons.2 ⟨subd15_1_24, List.forall_mem_cons.2 ⟨subd15_1_25, List.forall_mem_cons.2 ⟨subd15_1_26, List.forall_mem_cons.2 ⟨subd15_1_27, List.forall_mem_cons.2 ⟨subd15_1_28, List.forall_mem_cons.2 ⟨subd15_1_29, List.forall_mem_cons.2 ⟨subd15_1_30, List.forall_mem_cons.2 ⟨subd15_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_32 : subd15_1 [2, 1] = true := by decide +kernel
theorem subd15_1_33 : subd15_1 [2, 2] = true := by decide +kernel
theorem subd15_1_34 : subd15_1 [2, 3] = true := by decide +kernel
theorem subd15_1_35 : subd15_1 [3] = true := by decide +kernel
theorem sbd15_1_1 : ∀ q ∈ blkd15_1_1, subd15_1 q = true := by
  unfold blkd15_1_1
  exact List.forall_mem_cons.2 ⟨subd15_1_32, List.forall_mem_cons.2 ⟨subd15_1_33, List.forall_mem_cons.2 ⟨subd15_1_34, List.forall_mem_cons.2 ⟨subd15_1_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd16_0 : ldCheck G d16_0.U d16_0.ms ldd16_0 = true := by decide +kernel
theorem pre_okd16_0 : subPre G cell16 d16_0 = true := by decide +kernel
theorem subd16_0_0 : subd16_0 [-3] = true := by decide +kernel
theorem subd16_0_1 : subd16_0 [-2, -2] = true := by decide +kernel
theorem subd16_0_2 : subd16_0 [-2, -1] = true := by decide +kernel
theorem subd16_0_3 : subd16_0 [-2, 0] = true := by decide +kernel
theorem subd16_0_4 : subd16_0 [-2, 1] = true := by decide +kernel
theorem subd16_0_5 : subd16_0 [-2, 2] = true := by decide +kernel
theorem subd16_0_6 : subd16_0 [-2, 3] = true := by decide +kernel
theorem subd16_0_7 : subd16_0 [-1, -3] = true := by decide +kernel
theorem subd16_0_8 : subd16_0 [-1, -2] = true := by decide +kernel
theorem subd16_0_9 : subd16_0 [-1, -1, -7] = true := by decide +kernel
theorem subd16_0_10 : subd16_0 [-1, -1, -6] = true := by decide +kernel
theorem subd16_0_11 : subd16_0 [-1, -1, -5] = true := by decide +kernel
theorem subd16_0_12 : subd16_0 [-1, -1, -4] = true := by decide +kernel
theorem subd16_0_13 : subd16_0 [-1, -1, -3] = true := by decide +kernel
theorem subd16_0_14 : subd16_0 [-1, -1, -2] = true := by decide +kernel
theorem subd16_0_15 : subd16_0 [-1, -1, -1] = true := by decide +kernel
theorem subd16_0_16 : subd16_0 [-1, -1, 0] = true := by decide +kernel
theorem subd16_0_17 : subd16_0 [-1, -1, 1] = true := by decide +kernel
theorem subd16_0_18 : subd16_0 [-1, -1, 2] = true := by decide +kernel
theorem subd16_0_19 : subd16_0 [-1, -1, 3] = true := by decide +kernel
theorem subd16_0_20 : subd16_0 [-1, -1, 4] = true := by decide +kernel
theorem subd16_0_21 : subd16_0 [-1, -1, 5] = true := by decide +kernel
theorem subd16_0_22 : subd16_0 [-1, -1, 6] = true := by decide +kernel
theorem subd16_0_23 : subd16_0 [-1, 0, -8] = true := by decide +kernel
theorem subd16_0_24 : subd16_0 [-1, 0, -7] = true := by decide +kernel
theorem subd16_0_25 : subd16_0 [-1, 0, -6] = true := by decide +kernel
theorem subd16_0_26 : subd16_0 [-1, 0, -5] = true := by decide +kernel
theorem subd16_0_27 : subd16_0 [-1, 0, -4] = true := by decide +kernel
theorem subd16_0_28 : subd16_0 [-1, 0, -3] = true := by decide +kernel
theorem subd16_0_29 : subd16_0 [-1, 0, -2] = true := by decide +kernel
theorem subd16_0_30 : subd16_0 [-1, 0, -1] = true := by decide +kernel
theorem subd16_0_31 : subd16_0 [-1, 0, 0] = true := by decide +kernel
theorem sbd16_0_0 : ∀ q ∈ blkd16_0_0, subd16_0 q = true := by
  unfold blkd16_0_0
  exact List.forall_mem_cons.2 ⟨subd16_0_0, List.forall_mem_cons.2 ⟨subd16_0_1, List.forall_mem_cons.2 ⟨subd16_0_2, List.forall_mem_cons.2 ⟨subd16_0_3, List.forall_mem_cons.2 ⟨subd16_0_4, List.forall_mem_cons.2 ⟨subd16_0_5, List.forall_mem_cons.2 ⟨subd16_0_6, List.forall_mem_cons.2 ⟨subd16_0_7, List.forall_mem_cons.2 ⟨subd16_0_8, List.forall_mem_cons.2 ⟨subd16_0_9, List.forall_mem_cons.2 ⟨subd16_0_10, List.forall_mem_cons.2 ⟨subd16_0_11, List.forall_mem_cons.2 ⟨subd16_0_12, List.forall_mem_cons.2 ⟨subd16_0_13, List.forall_mem_cons.2 ⟨subd16_0_14, List.forall_mem_cons.2 ⟨subd16_0_15, List.forall_mem_cons.2 ⟨subd16_0_16, List.forall_mem_cons.2 ⟨subd16_0_17, List.forall_mem_cons.2 ⟨subd16_0_18, List.forall_mem_cons.2 ⟨subd16_0_19, List.forall_mem_cons.2 ⟨subd16_0_20, List.forall_mem_cons.2 ⟨subd16_0_21, List.forall_mem_cons.2 ⟨subd16_0_22, List.forall_mem_cons.2 ⟨subd16_0_23, List.forall_mem_cons.2 ⟨subd16_0_24, List.forall_mem_cons.2 ⟨subd16_0_25, List.forall_mem_cons.2 ⟨subd16_0_26, List.forall_mem_cons.2 ⟨subd16_0_27, List.forall_mem_cons.2 ⟨subd16_0_28, List.forall_mem_cons.2 ⟨subd16_0_29, List.forall_mem_cons.2 ⟨subd16_0_30, List.forall_mem_cons.2 ⟨subd16_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_32 : subd16_0 [-1, 0, 1] = true := by decide +kernel
theorem subd16_0_33 : subd16_0 [-1, 0, 2] = true := by decide +kernel
theorem subd16_0_34 : subd16_0 [-1, 0, 3] = true := by decide +kernel
theorem subd16_0_35 : subd16_0 [-1, 0, 4] = true := by decide +kernel
theorem subd16_0_36 : subd16_0 [-1, 0, 5] = true := by decide +kernel
theorem subd16_0_37 : subd16_0 [-1, 0, 6] = true := by decide +kernel
theorem subd16_0_38 : subd16_0 [-1, 1, -8] = true := by decide +kernel
theorem subd16_0_39 : subd16_0 [-1, 1, -7] = true := by decide +kernel
theorem subd16_0_40 : subd16_0 [-1, 1, -6] = true := by decide +kernel
theorem subd16_0_41 : subd16_0 [-1, 1, -5] = true := by decide +kernel
theorem subd16_0_42 : subd16_0 [-1, 1, -4] = true := by decide +kernel
theorem subd16_0_43 : subd16_0 [-1, 1, -3] = true := by decide +kernel
theorem subd16_0_44 : subd16_0 [-1, 1, -2] = true := by decide +kernel
theorem subd16_0_45 : subd16_0 [-1, 1, -1] = true := by decide +kernel
theorem subd16_0_46 : subd16_0 [-1, 1, 0] = true := by decide +kernel
theorem subd16_0_47 : subd16_0 [-1, 1, 1] = true := by decide +kernel
theorem subd16_0_48 : subd16_0 [-1, 1, 2] = true := by decide +kernel
theorem subd16_0_49 : subd16_0 [-1, 1, 3] = true := by decide +kernel
theorem subd16_0_50 : subd16_0 [-1, 1, 4] = true := by decide +kernel
theorem subd16_0_51 : subd16_0 [-1, 1, 5] = true := by decide +kernel
theorem subd16_0_52 : subd16_0 [-1, 1, 6] = true := by decide +kernel
theorem subd16_0_53 : subd16_0 [-1, 2] = true := by decide +kernel
theorem subd16_0_54 : subd16_0 [-1, 3] = true := by decide +kernel
theorem subd16_0_55 : subd16_0 [0, -4] = true := by decide +kernel
theorem subd16_0_56 : subd16_0 [0, -3] = true := by decide +kernel
theorem subd16_0_57 : subd16_0 [0, -2] = true := by decide +kernel
theorem subd16_0_58 : subd16_0 [0, -1, -8] = true := by decide +kernel
theorem subd16_0_59 : subd16_0 [0, -1, -7] = true := by decide +kernel
theorem subd16_0_60 : subd16_0 [0, -1, -6] = true := by decide +kernel
theorem subd16_0_61 : subd16_0 [0, -1, -5] = true := by decide +kernel
theorem subd16_0_62 : subd16_0 [0, -1, -4] = true := by decide +kernel
theorem subd16_0_63 : subd16_0 [0, -1, -3] = true := by decide +kernel
theorem sbd16_0_1 : ∀ q ∈ blkd16_0_1, subd16_0 q = true := by
  unfold blkd16_0_1
  exact List.forall_mem_cons.2 ⟨subd16_0_32, List.forall_mem_cons.2 ⟨subd16_0_33, List.forall_mem_cons.2 ⟨subd16_0_34, List.forall_mem_cons.2 ⟨subd16_0_35, List.forall_mem_cons.2 ⟨subd16_0_36, List.forall_mem_cons.2 ⟨subd16_0_37, List.forall_mem_cons.2 ⟨subd16_0_38, List.forall_mem_cons.2 ⟨subd16_0_39, List.forall_mem_cons.2 ⟨subd16_0_40, List.forall_mem_cons.2 ⟨subd16_0_41, List.forall_mem_cons.2 ⟨subd16_0_42, List.forall_mem_cons.2 ⟨subd16_0_43, List.forall_mem_cons.2 ⟨subd16_0_44, List.forall_mem_cons.2 ⟨subd16_0_45, List.forall_mem_cons.2 ⟨subd16_0_46, List.forall_mem_cons.2 ⟨subd16_0_47, List.forall_mem_cons.2 ⟨subd16_0_48, List.forall_mem_cons.2 ⟨subd16_0_49, List.forall_mem_cons.2 ⟨subd16_0_50, List.forall_mem_cons.2 ⟨subd16_0_51, List.forall_mem_cons.2 ⟨subd16_0_52, List.forall_mem_cons.2 ⟨subd16_0_53, List.forall_mem_cons.2 ⟨subd16_0_54, List.forall_mem_cons.2 ⟨subd16_0_55, List.forall_mem_cons.2 ⟨subd16_0_56, List.forall_mem_cons.2 ⟨subd16_0_57, List.forall_mem_cons.2 ⟨subd16_0_58, List.forall_mem_cons.2 ⟨subd16_0_59, List.forall_mem_cons.2 ⟨subd16_0_60, List.forall_mem_cons.2 ⟨subd16_0_61, List.forall_mem_cons.2 ⟨subd16_0_62, List.forall_mem_cons.2 ⟨subd16_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
