import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_4_96 : subd10_4 [0, 1, -6] = true := by decide +kernel
theorem subd10_4_97 : subd10_4 [0, 1, -5] = true := by decide +kernel
theorem subd10_4_98 : subd10_4 [0, 1, -4] = true := by decide +kernel
theorem subd10_4_99 : subd10_4 [0, 1, -3] = true := by decide +kernel
theorem subd10_4_100 : subd10_4 [0, 1, -2] = true := by decide +kernel
theorem subd10_4_101 : subd10_4 [0, 1, -1] = true := by decide +kernel
theorem subd10_4_102 : subd10_4 [0, 1, 0] = true := by decide +kernel
theorem subd10_4_103 : subd10_4 [0, 1, 1] = true := by decide +kernel
theorem subd10_4_104 : subd10_4 [0, 1, 2] = true := by decide +kernel
theorem subd10_4_105 : subd10_4 [0, 1, 3] = true := by decide +kernel
theorem subd10_4_106 : subd10_4 [0, 1, 4] = true := by decide +kernel
theorem subd10_4_107 : subd10_4 [0, 1, 5] = true := by decide +kernel
theorem subd10_4_108 : subd10_4 [0, 1, 6] = true := by decide +kernel
theorem subd10_4_109 : subd10_4 [0, 2] = true := by decide +kernel
theorem subd10_4_110 : subd10_4 [0, 3] = true := by decide +kernel
theorem subd10_4_111 : subd10_4 [1, -4] = true := by decide +kernel
theorem subd10_4_112 : subd10_4 [1, -3] = true := by decide +kernel
theorem subd10_4_113 : subd10_4 [1, -2] = true := by decide +kernel
theorem subd10_4_114 : subd10_4 [1, -1, -7] = true := by decide +kernel
theorem subd10_4_115 : subd10_4 [1, -1, -6] = true := by decide +kernel
theorem subd10_4_116 : subd10_4 [1, -1, -5] = true := by decide +kernel
theorem subd10_4_117 : subd10_4 [1, -1, -4] = true := by decide +kernel
theorem subd10_4_118 : subd10_4 [1, -1, -3] = true := by decide +kernel
theorem subd10_4_119 : subd10_4 [1, -1, -2] = true := by decide +kernel
theorem subd10_4_120 : subd10_4 [1, -1, -1] = true := by decide +kernel
theorem subd10_4_121 : subd10_4 [1, -1, 0] = true := by decide +kernel
theorem subd10_4_122 : subd10_4 [1, -1, 1] = true := by decide +kernel
theorem subd10_4_123 : subd10_4 [1, -1, 2] = true := by decide +kernel
theorem subd10_4_124 : subd10_4 [1, -1, 3] = true := by decide +kernel
theorem subd10_4_125 : subd10_4 [1, -1, 4] = true := by decide +kernel
theorem subd10_4_126 : subd10_4 [1, -1, 5] = true := by decide +kernel
theorem subd10_4_127 : subd10_4 [1, -1, 6] = true := by decide +kernel
theorem sbd10_4_3 : ∀ q ∈ blkd10_4_3, subd10_4 q = true := by
  unfold blkd10_4_3
  exact List.forall_mem_cons.2 ⟨subd10_4_96, List.forall_mem_cons.2 ⟨subd10_4_97, List.forall_mem_cons.2 ⟨subd10_4_98, List.forall_mem_cons.2 ⟨subd10_4_99, List.forall_mem_cons.2 ⟨subd10_4_100, List.forall_mem_cons.2 ⟨subd10_4_101, List.forall_mem_cons.2 ⟨subd10_4_102, List.forall_mem_cons.2 ⟨subd10_4_103, List.forall_mem_cons.2 ⟨subd10_4_104, List.forall_mem_cons.2 ⟨subd10_4_105, List.forall_mem_cons.2 ⟨subd10_4_106, List.forall_mem_cons.2 ⟨subd10_4_107, List.forall_mem_cons.2 ⟨subd10_4_108, List.forall_mem_cons.2 ⟨subd10_4_109, List.forall_mem_cons.2 ⟨subd10_4_110, List.forall_mem_cons.2 ⟨subd10_4_111, List.forall_mem_cons.2 ⟨subd10_4_112, List.forall_mem_cons.2 ⟨subd10_4_113, List.forall_mem_cons.2 ⟨subd10_4_114, List.forall_mem_cons.2 ⟨subd10_4_115, List.forall_mem_cons.2 ⟨subd10_4_116, List.forall_mem_cons.2 ⟨subd10_4_117, List.forall_mem_cons.2 ⟨subd10_4_118, List.forall_mem_cons.2 ⟨subd10_4_119, List.forall_mem_cons.2 ⟨subd10_4_120, List.forall_mem_cons.2 ⟨subd10_4_121, List.forall_mem_cons.2 ⟨subd10_4_122, List.forall_mem_cons.2 ⟨subd10_4_123, List.forall_mem_cons.2 ⟨subd10_4_124, List.forall_mem_cons.2 ⟨subd10_4_125, List.forall_mem_cons.2 ⟨subd10_4_126, List.forall_mem_cons.2 ⟨subd10_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_128 : subd10_4 [1, 0, -7] = true := by decide +kernel
theorem subd10_4_129 : subd10_4 [1, 0, -6] = true := by decide +kernel
theorem subd10_4_130 : subd10_4 [1, 0, -5] = true := by decide +kernel
theorem subd10_4_131 : subd10_4 [1, 0, -4] = true := by decide +kernel
theorem subd10_4_132 : subd10_4 [1, 0, -3] = true := by decide +kernel
theorem subd10_4_133 : subd10_4 [1, 0, -2] = true := by decide +kernel
theorem subd10_4_134 : subd10_4 [1, 0, -1] = true := by decide +kernel
theorem subd10_4_135 : subd10_4 [1, 0, 0] = true := by decide +kernel
theorem subd10_4_136 : subd10_4 [1, 0, 1] = true := by decide +kernel
theorem subd10_4_137 : subd10_4 [1, 0, 2] = true := by decide +kernel
theorem subd10_4_138 : subd10_4 [1, 0, 3] = true := by decide +kernel
theorem subd10_4_139 : subd10_4 [1, 0, 4] = true := by decide +kernel
theorem subd10_4_140 : subd10_4 [1, 0, 5] = true := by decide +kernel
theorem subd10_4_141 : subd10_4 [1, 0, 6] = true := by decide +kernel
theorem subd10_4_142 : subd10_4 [1, 0, 7] = true := by decide +kernel
theorem subd10_4_143 : subd10_4 [1, 1, -7] = true := by decide +kernel
theorem subd10_4_144 : subd10_4 [1, 1, -6] = true := by decide +kernel
theorem subd10_4_145 : subd10_4 [1, 1, -5] = true := by decide +kernel
theorem subd10_4_146 : subd10_4 [1, 1, -4] = true := by decide +kernel
theorem subd10_4_147 : subd10_4 [1, 1, -3] = true := by decide +kernel
theorem subd10_4_148 : subd10_4 [1, 1, -2] = true := by decide +kernel
theorem subd10_4_149 : subd10_4 [1, 1, -1] = true := by decide +kernel
theorem subd10_4_150 : subd10_4 [1, 1, 0] = true := by decide +kernel
theorem subd10_4_151 : subd10_4 [1, 1, 1] = true := by decide +kernel
theorem subd10_4_152 : subd10_4 [1, 1, 2] = true := by decide +kernel
theorem subd10_4_153 : subd10_4 [1, 1, 3] = true := by decide +kernel
theorem subd10_4_154 : subd10_4 [1, 1, 4] = true := by decide +kernel
theorem subd10_4_155 : subd10_4 [1, 1, 5] = true := by decide +kernel
theorem subd10_4_156 : subd10_4 [1, 1, 6] = true := by decide +kernel
theorem subd10_4_157 : subd10_4 [1, 2] = true := by decide +kernel
theorem subd10_4_158 : subd10_4 [1, 3] = true := by decide +kernel
theorem subd10_4_159 : subd10_4 [2, -4] = true := by decide +kernel
theorem sbd10_4_4 : ∀ q ∈ blkd10_4_4, subd10_4 q = true := by
  unfold blkd10_4_4
  exact List.forall_mem_cons.2 ⟨subd10_4_128, List.forall_mem_cons.2 ⟨subd10_4_129, List.forall_mem_cons.2 ⟨subd10_4_130, List.forall_mem_cons.2 ⟨subd10_4_131, List.forall_mem_cons.2 ⟨subd10_4_132, List.forall_mem_cons.2 ⟨subd10_4_133, List.forall_mem_cons.2 ⟨subd10_4_134, List.forall_mem_cons.2 ⟨subd10_4_135, List.forall_mem_cons.2 ⟨subd10_4_136, List.forall_mem_cons.2 ⟨subd10_4_137, List.forall_mem_cons.2 ⟨subd10_4_138, List.forall_mem_cons.2 ⟨subd10_4_139, List.forall_mem_cons.2 ⟨subd10_4_140, List.forall_mem_cons.2 ⟨subd10_4_141, List.forall_mem_cons.2 ⟨subd10_4_142, List.forall_mem_cons.2 ⟨subd10_4_143, List.forall_mem_cons.2 ⟨subd10_4_144, List.forall_mem_cons.2 ⟨subd10_4_145, List.forall_mem_cons.2 ⟨subd10_4_146, List.forall_mem_cons.2 ⟨subd10_4_147, List.forall_mem_cons.2 ⟨subd10_4_148, List.forall_mem_cons.2 ⟨subd10_4_149, List.forall_mem_cons.2 ⟨subd10_4_150, List.forall_mem_cons.2 ⟨subd10_4_151, List.forall_mem_cons.2 ⟨subd10_4_152, List.forall_mem_cons.2 ⟨subd10_4_153, List.forall_mem_cons.2 ⟨subd10_4_154, List.forall_mem_cons.2 ⟨subd10_4_155, List.forall_mem_cons.2 ⟨subd10_4_156, List.forall_mem_cons.2 ⟨subd10_4_157, List.forall_mem_cons.2 ⟨subd10_4_158, List.forall_mem_cons.2 ⟨subd10_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_160 : subd10_4 [2, -3] = true := by decide +kernel
theorem subd10_4_161 : subd10_4 [2, -2] = true := by decide +kernel
theorem subd10_4_162 : subd10_4 [2, -1] = true := by decide +kernel
theorem subd10_4_163 : subd10_4 [2, 0] = true := by decide +kernel
theorem subd10_4_164 : subd10_4 [2, 1] = true := by decide +kernel
theorem subd10_4_165 : subd10_4 [2, 2] = true := by decide +kernel
theorem subd10_4_166 : subd10_4 [2, 3] = true := by decide +kernel
theorem subd10_4_167 : subd10_4 [3, -3] = true := by decide +kernel
theorem subd10_4_168 : subd10_4 [3, -2] = true := by decide +kernel
theorem subd10_4_169 : subd10_4 [3, -1] = true := by decide +kernel
theorem subd10_4_170 : subd10_4 [3, 0] = true := by decide +kernel
theorem subd10_4_171 : subd10_4 [3, 1] = true := by decide +kernel
theorem subd10_4_172 : subd10_4 [3, 2] = true := by decide +kernel
theorem sbd10_4_5 : ∀ q ∈ blkd10_4_5, subd10_4 q = true := by
  unfold blkd10_4_5
  exact List.forall_mem_cons.2 ⟨subd10_4_160, List.forall_mem_cons.2 ⟨subd10_4_161, List.forall_mem_cons.2 ⟨subd10_4_162, List.forall_mem_cons.2 ⟨subd10_4_163, List.forall_mem_cons.2 ⟨subd10_4_164, List.forall_mem_cons.2 ⟨subd10_4_165, List.forall_mem_cons.2 ⟨subd10_4_166, List.forall_mem_cons.2 ⟨subd10_4_167, List.forall_mem_cons.2 ⟨subd10_4_168, List.forall_mem_cons.2 ⟨subd10_4_169, List.forall_mem_cons.2 ⟨subd10_4_170, List.forall_mem_cons.2 ⟨subd10_4_171, List.forall_mem_cons.2 ⟨subd10_4_172, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-2] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-1, -3] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-1, -2] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-1, -1] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-1, 0] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-1, 1] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [-1, 2] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [-1, 3] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [0, -4] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [0, -3] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [0, -2] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [0, -1] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [0, 0] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [0, 1] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [0, 2] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [0, 3] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [1, -4] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [1, -3] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [1, -2] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [1, -1] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [1, 0] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [1, 1] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [1, 2] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [2] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-2] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-1, -2] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-1, -1] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-1, 0] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-1, 1] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-1, 2] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [0, -2] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [0, -1] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [0, 0] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [0, 1] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [0, 2] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [1, -3] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [1, -2] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [1, -1] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [1, 0] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [1, 1] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [1, 2] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [2] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-3] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-2, -4] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [-2, -3] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [-2, -2] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [-2, -1] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [-2, 0] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [-2, 1] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [-2, 2] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [-1, -5] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [-1, -4] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [-1, -3] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [-1, -2] = true := by decide +kernel
theorem subd11_2_12 : subd11_2 [-1, -1] = true := by decide +kernel
theorem subd11_2_13 : subd11_2 [-1, 0] = true := by decide +kernel
theorem subd11_2_14 : subd11_2 [-1, 1] = true := by decide +kernel
theorem subd11_2_15 : subd11_2 [-1, 2] = true := by decide +kernel
theorem subd11_2_16 : subd11_2 [-1, 3] = true := by decide +kernel
theorem subd11_2_17 : subd11_2 [0, -4] = true := by decide +kernel
theorem subd11_2_18 : subd11_2 [0, -3] = true := by decide +kernel
theorem subd11_2_19 : subd11_2 [0, -2] = true := by decide +kernel
theorem subd11_2_20 : subd11_2 [0, -1] = true := by decide +kernel
theorem subd11_2_21 : subd11_2 [0, 0] = true := by decide +kernel
theorem subd11_2_22 : subd11_2 [0, 1] = true := by decide +kernel
theorem subd11_2_23 : subd11_2 [0, 2] = true := by decide +kernel
theorem subd11_2_24 : subd11_2 [0, 3] = true := by decide +kernel
theorem subd11_2_25 : subd11_2 [1, -4] = true := by decide +kernel
theorem subd11_2_26 : subd11_2 [1, -3] = true := by decide +kernel
theorem subd11_2_27 : subd11_2 [1, -2] = true := by decide +kernel
theorem subd11_2_28 : subd11_2 [1, -1] = true := by decide +kernel
theorem subd11_2_29 : subd11_2 [1, 0] = true := by decide +kernel
theorem subd11_2_30 : subd11_2 [1, 1] = true := by decide +kernel
theorem subd11_2_31 : subd11_2 [1, 2] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_cons.2 ⟨subd11_2_12, List.forall_mem_cons.2 ⟨subd11_2_13, List.forall_mem_cons.2 ⟨subd11_2_14, List.forall_mem_cons.2 ⟨subd11_2_15, List.forall_mem_cons.2 ⟨subd11_2_16, List.forall_mem_cons.2 ⟨subd11_2_17, List.forall_mem_cons.2 ⟨subd11_2_18, List.forall_mem_cons.2 ⟨subd11_2_19, List.forall_mem_cons.2 ⟨subd11_2_20, List.forall_mem_cons.2 ⟨subd11_2_21, List.forall_mem_cons.2 ⟨subd11_2_22, List.forall_mem_cons.2 ⟨subd11_2_23, List.forall_mem_cons.2 ⟨subd11_2_24, List.forall_mem_cons.2 ⟨subd11_2_25, List.forall_mem_cons.2 ⟨subd11_2_26, List.forall_mem_cons.2 ⟨subd11_2_27, List.forall_mem_cons.2 ⟨subd11_2_28, List.forall_mem_cons.2 ⟨subd11_2_29, List.forall_mem_cons.2 ⟨subd11_2_30, List.forall_mem_cons.2 ⟨subd11_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_32 : subd11_2 [1, 3] = true := by decide +kernel
theorem subd11_2_33 : subd11_2 [1, 4] = true := by decide +kernel
theorem subd11_2_34 : subd11_2 [2, -3] = true := by decide +kernel
theorem subd11_2_35 : subd11_2 [2, -2] = true := by decide +kernel
theorem subd11_2_36 : subd11_2 [2, -1] = true := by decide +kernel
theorem subd11_2_37 : subd11_2 [2, 0] = true := by decide +kernel
theorem subd11_2_38 : subd11_2 [2, 1] = true := by decide +kernel
theorem subd11_2_39 : subd11_2 [2, 2] = true := by decide +kernel
theorem subd11_2_40 : subd11_2 [2, 3] = true := by decide +kernel
theorem subd11_2_41 : subd11_2 [3] = true := by decide +kernel
theorem sbd11_2_1 : ∀ q ∈ blkd11_2_1, subd11_2 q = true := by
  unfold blkd11_2_1
  exact List.forall_mem_cons.2 ⟨subd11_2_32, List.forall_mem_cons.2 ⟨subd11_2_33, List.forall_mem_cons.2 ⟨subd11_2_34, List.forall_mem_cons.2 ⟨subd11_2_35, List.forall_mem_cons.2 ⟨subd11_2_36, List.forall_mem_cons.2 ⟨subd11_2_37, List.forall_mem_cons.2 ⟨subd11_2_38, List.forall_mem_cons.2 ⟨subd11_2_39, List.forall_mem_cons.2 ⟨subd11_2_40, List.forall_mem_cons.2 ⟨subd11_2_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C110
