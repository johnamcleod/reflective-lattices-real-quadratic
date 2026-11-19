import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_4_96 : subd10_4 [0, 0, 3] = true := by decide +kernel
theorem subd10_4_97 : subd10_4 [0, 0, 4] = true := by decide +kernel
theorem subd10_4_98 : subd10_4 [0, 0, 5] = true := by decide +kernel
theorem subd10_4_99 : subd10_4 [0, 0, 6] = true := by decide +kernel
theorem subd10_4_100 : subd10_4 [0, 1, -6] = true := by decide +kernel
theorem subd10_4_101 : subd10_4 [0, 1, -5] = true := by decide +kernel
theorem subd10_4_102 : subd10_4 [0, 1, -4] = true := by decide +kernel
theorem subd10_4_103 : subd10_4 [0, 1, -3] = true := by decide +kernel
theorem subd10_4_104 : subd10_4 [0, 1, -2] = true := by decide +kernel
theorem subd10_4_105 : subd10_4 [0, 1, -1] = true := by decide +kernel
theorem subd10_4_106 : subd10_4 [0, 1, 0] = true := by decide +kernel
theorem subd10_4_107 : subd10_4 [0, 1, 1] = true := by decide +kernel
theorem subd10_4_108 : subd10_4 [0, 1, 2] = true := by decide +kernel
theorem subd10_4_109 : subd10_4 [0, 1, 3] = true := by decide +kernel
theorem subd10_4_110 : subd10_4 [0, 1, 4] = true := by decide +kernel
theorem subd10_4_111 : subd10_4 [0, 1, 5] = true := by decide +kernel
theorem subd10_4_112 : subd10_4 [0, 1, 6] = true := by decide +kernel
theorem subd10_4_113 : subd10_4 [0, 2] = true := by decide +kernel
theorem subd10_4_114 : subd10_4 [0, 3] = true := by decide +kernel
theorem subd10_4_115 : subd10_4 [0, 4] = true := by decide +kernel
theorem subd10_4_116 : subd10_4 [0, 5] = true := by decide +kernel
theorem subd10_4_117 : subd10_4 [0, 6] = true := by decide +kernel
theorem subd10_4_118 : subd10_4 [0, 7] = true := by decide +kernel
theorem subd10_4_119 : subd10_4 [1, -7] = true := by decide +kernel
theorem subd10_4_120 : subd10_4 [1, -6] = true := by decide +kernel
theorem subd10_4_121 : subd10_4 [1, -5] = true := by decide +kernel
theorem subd10_4_122 : subd10_4 [1, -4] = true := by decide +kernel
theorem subd10_4_123 : subd10_4 [1, -3] = true := by decide +kernel
theorem subd10_4_124 : subd10_4 [1, -2] = true := by decide +kernel
theorem subd10_4_125 : subd10_4 [1, -1] = true := by decide +kernel
theorem subd10_4_126 : subd10_4 [1, 0] = true := by decide +kernel
theorem subd10_4_127 : subd10_4 [1, 1] = true := by decide +kernel
theorem sbd10_4_3 : ∀ q ∈ blkd10_4_3, subd10_4 q = true := by
  unfold blkd10_4_3
  exact List.forall_mem_cons.2 ⟨subd10_4_96, List.forall_mem_cons.2 ⟨subd10_4_97, List.forall_mem_cons.2 ⟨subd10_4_98, List.forall_mem_cons.2 ⟨subd10_4_99, List.forall_mem_cons.2 ⟨subd10_4_100, List.forall_mem_cons.2 ⟨subd10_4_101, List.forall_mem_cons.2 ⟨subd10_4_102, List.forall_mem_cons.2 ⟨subd10_4_103, List.forall_mem_cons.2 ⟨subd10_4_104, List.forall_mem_cons.2 ⟨subd10_4_105, List.forall_mem_cons.2 ⟨subd10_4_106, List.forall_mem_cons.2 ⟨subd10_4_107, List.forall_mem_cons.2 ⟨subd10_4_108, List.forall_mem_cons.2 ⟨subd10_4_109, List.forall_mem_cons.2 ⟨subd10_4_110, List.forall_mem_cons.2 ⟨subd10_4_111, List.forall_mem_cons.2 ⟨subd10_4_112, List.forall_mem_cons.2 ⟨subd10_4_113, List.forall_mem_cons.2 ⟨subd10_4_114, List.forall_mem_cons.2 ⟨subd10_4_115, List.forall_mem_cons.2 ⟨subd10_4_116, List.forall_mem_cons.2 ⟨subd10_4_117, List.forall_mem_cons.2 ⟨subd10_4_118, List.forall_mem_cons.2 ⟨subd10_4_119, List.forall_mem_cons.2 ⟨subd10_4_120, List.forall_mem_cons.2 ⟨subd10_4_121, List.forall_mem_cons.2 ⟨subd10_4_122, List.forall_mem_cons.2 ⟨subd10_4_123, List.forall_mem_cons.2 ⟨subd10_4_124, List.forall_mem_cons.2 ⟨subd10_4_125, List.forall_mem_cons.2 ⟨subd10_4_126, List.forall_mem_cons.2 ⟨subd10_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_128 : subd10_4 [1, 2] = true := by decide +kernel
theorem subd10_4_129 : subd10_4 [1, 3] = true := by decide +kernel
theorem subd10_4_130 : subd10_4 [1, 4] = true := by decide +kernel
theorem subd10_4_131 : subd10_4 [1, 5] = true := by decide +kernel
theorem subd10_4_132 : subd10_4 [1, 6] = true := by decide +kernel
theorem subd10_4_133 : subd10_4 [1, 7] = true := by decide +kernel
theorem subd10_4_134 : subd10_4 [2, -7] = true := by decide +kernel
theorem subd10_4_135 : subd10_4 [2, -6] = true := by decide +kernel
theorem subd10_4_136 : subd10_4 [2, -5] = true := by decide +kernel
theorem subd10_4_137 : subd10_4 [2, -4] = true := by decide +kernel
theorem subd10_4_138 : subd10_4 [2, -3] = true := by decide +kernel
theorem subd10_4_139 : subd10_4 [2, -2] = true := by decide +kernel
theorem subd10_4_140 : subd10_4 [2, -1] = true := by decide +kernel
theorem subd10_4_141 : subd10_4 [2, 0] = true := by decide +kernel
theorem subd10_4_142 : subd10_4 [2, 1] = true := by decide +kernel
theorem subd10_4_143 : subd10_4 [2, 2] = true := by decide +kernel
theorem subd10_4_144 : subd10_4 [2, 3] = true := by decide +kernel
theorem subd10_4_145 : subd10_4 [2, 4] = true := by decide +kernel
theorem subd10_4_146 : subd10_4 [2, 5] = true := by decide +kernel
theorem subd10_4_147 : subd10_4 [2, 6] = true := by decide +kernel
theorem subd10_4_148 : subd10_4 [3, -6] = true := by decide +kernel
theorem subd10_4_149 : subd10_4 [3, -5] = true := by decide +kernel
theorem subd10_4_150 : subd10_4 [3, -4] = true := by decide +kernel
theorem subd10_4_151 : subd10_4 [3, -3] = true := by decide +kernel
theorem subd10_4_152 : subd10_4 [3, -2] = true := by decide +kernel
theorem subd10_4_153 : subd10_4 [3, -1] = true := by decide +kernel
theorem subd10_4_154 : subd10_4 [3, 0] = true := by decide +kernel
theorem subd10_4_155 : subd10_4 [3, 1] = true := by decide +kernel
theorem subd10_4_156 : subd10_4 [3, 2] = true := by decide +kernel
theorem subd10_4_157 : subd10_4 [3, 3] = true := by decide +kernel
theorem subd10_4_158 : subd10_4 [3, 4] = true := by decide +kernel
theorem subd10_4_159 : subd10_4 [3, 5] = true := by decide +kernel
theorem sbd10_4_4 : ∀ q ∈ blkd10_4_4, subd10_4 q = true := by
  unfold blkd10_4_4
  exact List.forall_mem_cons.2 ⟨subd10_4_128, List.forall_mem_cons.2 ⟨subd10_4_129, List.forall_mem_cons.2 ⟨subd10_4_130, List.forall_mem_cons.2 ⟨subd10_4_131, List.forall_mem_cons.2 ⟨subd10_4_132, List.forall_mem_cons.2 ⟨subd10_4_133, List.forall_mem_cons.2 ⟨subd10_4_134, List.forall_mem_cons.2 ⟨subd10_4_135, List.forall_mem_cons.2 ⟨subd10_4_136, List.forall_mem_cons.2 ⟨subd10_4_137, List.forall_mem_cons.2 ⟨subd10_4_138, List.forall_mem_cons.2 ⟨subd10_4_139, List.forall_mem_cons.2 ⟨subd10_4_140, List.forall_mem_cons.2 ⟨subd10_4_141, List.forall_mem_cons.2 ⟨subd10_4_142, List.forall_mem_cons.2 ⟨subd10_4_143, List.forall_mem_cons.2 ⟨subd10_4_144, List.forall_mem_cons.2 ⟨subd10_4_145, List.forall_mem_cons.2 ⟨subd10_4_146, List.forall_mem_cons.2 ⟨subd10_4_147, List.forall_mem_cons.2 ⟨subd10_4_148, List.forall_mem_cons.2 ⟨subd10_4_149, List.forall_mem_cons.2 ⟨subd10_4_150, List.forall_mem_cons.2 ⟨subd10_4_151, List.forall_mem_cons.2 ⟨subd10_4_152, List.forall_mem_cons.2 ⟨subd10_4_153, List.forall_mem_cons.2 ⟨subd10_4_154, List.forall_mem_cons.2 ⟨subd10_4_155, List.forall_mem_cons.2 ⟨subd10_4_156, List.forall_mem_cons.2 ⟨subd10_4_157, List.forall_mem_cons.2 ⟨subd10_4_158, List.forall_mem_cons.2 ⟨subd10_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_160 : subd10_4 [3, 6] = true := by decide +kernel
theorem subd10_4_161 : subd10_4 [4, -6] = true := by decide +kernel
theorem subd10_4_162 : subd10_4 [4, -5] = true := by decide +kernel
theorem subd10_4_163 : subd10_4 [4, -4] = true := by decide +kernel
theorem subd10_4_164 : subd10_4 [4, -3] = true := by decide +kernel
theorem subd10_4_165 : subd10_4 [4, -2] = true := by decide +kernel
theorem subd10_4_166 : subd10_4 [4, -1] = true := by decide +kernel
theorem subd10_4_167 : subd10_4 [4, 0] = true := by decide +kernel
theorem subd10_4_168 : subd10_4 [4, 1] = true := by decide +kernel
theorem subd10_4_169 : subd10_4 [4, 2] = true := by decide +kernel
theorem subd10_4_170 : subd10_4 [4, 3] = true := by decide +kernel
theorem subd10_4_171 : subd10_4 [4, 4] = true := by decide +kernel
theorem subd10_4_172 : subd10_4 [4, 5] = true := by decide +kernel
theorem subd10_4_173 : subd10_4 [4, 6] = true := by decide +kernel
theorem subd10_4_174 : subd10_4 [5, -4] = true := by decide +kernel
theorem subd10_4_175 : subd10_4 [5, -3] = true := by decide +kernel
theorem subd10_4_176 : subd10_4 [5, -2] = true := by decide +kernel
theorem subd10_4_177 : subd10_4 [5, -1] = true := by decide +kernel
theorem subd10_4_178 : subd10_4 [5, 0] = true := by decide +kernel
theorem subd10_4_179 : subd10_4 [5, 1] = true := by decide +kernel
theorem subd10_4_180 : subd10_4 [5, 2] = true := by decide +kernel
theorem subd10_4_181 : subd10_4 [5, 3] = true := by decide +kernel
theorem subd10_4_182 : subd10_4 [5, 4] = true := by decide +kernel
theorem subd10_4_183 : subd10_4 [5, 5] = true := by decide +kernel
theorem subd10_4_184 : subd10_4 [6] = true := by decide +kernel
theorem sbd10_4_5 : ∀ q ∈ blkd10_4_5, subd10_4 q = true := by
  unfold blkd10_4_5
  exact List.forall_mem_cons.2 ⟨subd10_4_160, List.forall_mem_cons.2 ⟨subd10_4_161, List.forall_mem_cons.2 ⟨subd10_4_162, List.forall_mem_cons.2 ⟨subd10_4_163, List.forall_mem_cons.2 ⟨subd10_4_164, List.forall_mem_cons.2 ⟨subd10_4_165, List.forall_mem_cons.2 ⟨subd10_4_166, List.forall_mem_cons.2 ⟨subd10_4_167, List.forall_mem_cons.2 ⟨subd10_4_168, List.forall_mem_cons.2 ⟨subd10_4_169, List.forall_mem_cons.2 ⟨subd10_4_170, List.forall_mem_cons.2 ⟨subd10_4_171, List.forall_mem_cons.2 ⟨subd10_4_172, List.forall_mem_cons.2 ⟨subd10_4_173, List.forall_mem_cons.2 ⟨subd10_4_174, List.forall_mem_cons.2 ⟨subd10_4_175, List.forall_mem_cons.2 ⟨subd10_4_176, List.forall_mem_cons.2 ⟨subd10_4_177, List.forall_mem_cons.2 ⟨subd10_4_178, List.forall_mem_cons.2 ⟨subd10_4_179, List.forall_mem_cons.2 ⟨subd10_4_180, List.forall_mem_cons.2 ⟨subd10_4_181, List.forall_mem_cons.2 ⟨subd10_4_182, List.forall_mem_cons.2 ⟨subd10_4_183, List.forall_mem_cons.2 ⟨subd10_4_184, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_5 : ldCheck G d10_5.U d10_5.ms ldd10_5 = true := by decide +kernel
theorem pre_okd10_5 : subPre G cell10 d10_5 = true := by decide +kernel
theorem subd10_5_0 : subd10_5 [-3, -3] = true := by decide +kernel
theorem subd10_5_1 : subd10_5 [-3, -2] = true := by decide +kernel
theorem subd10_5_2 : subd10_5 [-3, -1] = true := by decide +kernel
theorem subd10_5_3 : subd10_5 [-3, 0] = true := by decide +kernel
theorem subd10_5_4 : subd10_5 [-3, 1] = true := by decide +kernel
theorem subd10_5_5 : subd10_5 [-2, -4] = true := by decide +kernel
theorem subd10_5_6 : subd10_5 [-2, -3] = true := by decide +kernel
theorem subd10_5_7 : subd10_5 [-2, -2, -7] = true := by decide +kernel
theorem subd10_5_8 : subd10_5 [-2, -2, -6] = true := by decide +kernel
theorem subd10_5_9 : subd10_5 [-2, -2, -5] = true := by decide +kernel
theorem subd10_5_10 : subd10_5 [-2, -2, -4] = true := by decide +kernel
theorem subd10_5_11 : subd10_5 [-2, -2, -3] = true := by decide +kernel
theorem subd10_5_12 : subd10_5 [-2, -2, -2] = true := by decide +kernel
theorem subd10_5_13 : subd10_5 [-2, -2, -1] = true := by decide +kernel
theorem subd10_5_14 : subd10_5 [-2, -2, 0] = true := by decide +kernel
theorem subd10_5_15 : subd10_5 [-2, -2, 1] = true := by decide +kernel
theorem subd10_5_16 : subd10_5 [-2, -2, 2] = true := by decide +kernel
theorem subd10_5_17 : subd10_5 [-2, -2, 3] = true := by decide +kernel
theorem subd10_5_18 : subd10_5 [-2, -2, 4] = true := by decide +kernel
theorem subd10_5_19 : subd10_5 [-2, -2, 5] = true := by decide +kernel
theorem subd10_5_20 : subd10_5 [-2, -2, 6] = true := by decide +kernel
theorem subd10_5_21 : subd10_5 [-2, -2, 7] = true := by decide +kernel
theorem subd10_5_22 : subd10_5 [-2, -1, -8] = true := by decide +kernel
theorem subd10_5_23 : subd10_5 [-2, -1, -7] = true := by decide +kernel
theorem subd10_5_24 : subd10_5 [-2, -1, -6] = true := by decide +kernel
theorem subd10_5_25 : subd10_5 [-2, -1, -5] = true := by decide +kernel
theorem subd10_5_26 : subd10_5 [-2, -1, -4] = true := by decide +kernel
theorem subd10_5_27 : subd10_5 [-2, -1, -3] = true := by decide +kernel
theorem subd10_5_28 : subd10_5 [-2, -1, -2] = true := by decide +kernel
theorem subd10_5_29 : subd10_5 [-2, -1, -1] = true := by decide +kernel
theorem subd10_5_30 : subd10_5 [-2, -1, 0] = true := by decide +kernel
theorem subd10_5_31 : subd10_5 [-2, -1, 1] = true := by decide +kernel
theorem sbd10_5_0 : ∀ q ∈ blkd10_5_0, subd10_5 q = true := by
  unfold blkd10_5_0
  exact List.forall_mem_cons.2 ⟨subd10_5_0, List.forall_mem_cons.2 ⟨subd10_5_1, List.forall_mem_cons.2 ⟨subd10_5_2, List.forall_mem_cons.2 ⟨subd10_5_3, List.forall_mem_cons.2 ⟨subd10_5_4, List.forall_mem_cons.2 ⟨subd10_5_5, List.forall_mem_cons.2 ⟨subd10_5_6, List.forall_mem_cons.2 ⟨subd10_5_7, List.forall_mem_cons.2 ⟨subd10_5_8, List.forall_mem_cons.2 ⟨subd10_5_9, List.forall_mem_cons.2 ⟨subd10_5_10, List.forall_mem_cons.2 ⟨subd10_5_11, List.forall_mem_cons.2 ⟨subd10_5_12, List.forall_mem_cons.2 ⟨subd10_5_13, List.forall_mem_cons.2 ⟨subd10_5_14, List.forall_mem_cons.2 ⟨subd10_5_15, List.forall_mem_cons.2 ⟨subd10_5_16, List.forall_mem_cons.2 ⟨subd10_5_17, List.forall_mem_cons.2 ⟨subd10_5_18, List.forall_mem_cons.2 ⟨subd10_5_19, List.forall_mem_cons.2 ⟨subd10_5_20, List.forall_mem_cons.2 ⟨subd10_5_21, List.forall_mem_cons.2 ⟨subd10_5_22, List.forall_mem_cons.2 ⟨subd10_5_23, List.forall_mem_cons.2 ⟨subd10_5_24, List.forall_mem_cons.2 ⟨subd10_5_25, List.forall_mem_cons.2 ⟨subd10_5_26, List.forall_mem_cons.2 ⟨subd10_5_27, List.forall_mem_cons.2 ⟨subd10_5_28, List.forall_mem_cons.2 ⟨subd10_5_29, List.forall_mem_cons.2 ⟨subd10_5_30, List.forall_mem_cons.2 ⟨subd10_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
