import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_8_96 : subd9_8 [0, 0, -8] = true := by decide +kernel
theorem subd9_8_97 : subd9_8 [0, 0, -7] = true := by decide +kernel
theorem subd9_8_98 : subd9_8 [0, 0, -6] = true := by decide +kernel
theorem subd9_8_99 : subd9_8 [0, 0, -5] = true := by decide +kernel
theorem subd9_8_100 : subd9_8 [0, 0, -4] = true := by decide +kernel
theorem subd9_8_101 : subd9_8 [0, 0, -3] = true := by decide +kernel
theorem subd9_8_102 : subd9_8 [0, 0, -2] = true := by decide +kernel
theorem subd9_8_103 : subd9_8 [0, 0, -1] = true := by decide +kernel
theorem subd9_8_104 : subd9_8 [0, 0, 0] = true := by decide +kernel
theorem subd9_8_105 : subd9_8 [0, 0, 1] = true := by decide +kernel
theorem subd9_8_106 : subd9_8 [0, 0, 2] = true := by decide +kernel
theorem subd9_8_107 : subd9_8 [0, 0, 3] = true := by decide +kernel
theorem subd9_8_108 : subd9_8 [0, 0, 4] = true := by decide +kernel
theorem subd9_8_109 : subd9_8 [0, 0, 5] = true := by decide +kernel
theorem subd9_8_110 : subd9_8 [0, 0, 6] = true := by decide +kernel
theorem subd9_8_111 : subd9_8 [0, 0, 7] = true := by decide +kernel
theorem subd9_8_112 : subd9_8 [0, 0, 8] = true := by decide +kernel
theorem subd9_8_113 : subd9_8 [0, 0, 9] = true := by decide +kernel
theorem subd9_8_114 : subd9_8 [0, 0, 10] = true := by decide +kernel
theorem subd9_8_115 : subd9_8 [0, 0, 11] = true := by decide +kernel
theorem subd9_8_116 : subd9_8 [0, 0, 12] = true := by decide +kernel
theorem subd9_8_117 : subd9_8 [0, 0, 13] = true := by decide +kernel
theorem subd9_8_118 : subd9_8 [0, 0, 14] = true := by decide +kernel
theorem subd9_8_119 : subd9_8 [0, 0, 15] = true := by decide +kernel
theorem subd9_8_120 : subd9_8 [0, 0, 16] = true := by decide +kernel
theorem subd9_8_121 : subd9_8 [0, 0, 17] = true := by decide +kernel
theorem subd9_8_122 : subd9_8 [0, 0, 18] = true := by decide +kernel
theorem subd9_8_123 : subd9_8 [0, 0, 19] = true := by decide +kernel
theorem subd9_8_124 : subd9_8 [0, 0, 20] = true := by decide +kernel
theorem subd9_8_125 : subd9_8 [0, 1, -16] = true := by decide +kernel
theorem subd9_8_126 : subd9_8 [0, 1, -15] = true := by decide +kernel
theorem subd9_8_127 : subd9_8 [0, 1, -14] = true := by decide +kernel
theorem sbd9_8_3 : ∀ q ∈ blkd9_8_3, subd9_8 q = true := by
  unfold blkd9_8_3
  exact List.forall_mem_cons.2 ⟨subd9_8_96, List.forall_mem_cons.2 ⟨subd9_8_97, List.forall_mem_cons.2 ⟨subd9_8_98, List.forall_mem_cons.2 ⟨subd9_8_99, List.forall_mem_cons.2 ⟨subd9_8_100, List.forall_mem_cons.2 ⟨subd9_8_101, List.forall_mem_cons.2 ⟨subd9_8_102, List.forall_mem_cons.2 ⟨subd9_8_103, List.forall_mem_cons.2 ⟨subd9_8_104, List.forall_mem_cons.2 ⟨subd9_8_105, List.forall_mem_cons.2 ⟨subd9_8_106, List.forall_mem_cons.2 ⟨subd9_8_107, List.forall_mem_cons.2 ⟨subd9_8_108, List.forall_mem_cons.2 ⟨subd9_8_109, List.forall_mem_cons.2 ⟨subd9_8_110, List.forall_mem_cons.2 ⟨subd9_8_111, List.forall_mem_cons.2 ⟨subd9_8_112, List.forall_mem_cons.2 ⟨subd9_8_113, List.forall_mem_cons.2 ⟨subd9_8_114, List.forall_mem_cons.2 ⟨subd9_8_115, List.forall_mem_cons.2 ⟨subd9_8_116, List.forall_mem_cons.2 ⟨subd9_8_117, List.forall_mem_cons.2 ⟨subd9_8_118, List.forall_mem_cons.2 ⟨subd9_8_119, List.forall_mem_cons.2 ⟨subd9_8_120, List.forall_mem_cons.2 ⟨subd9_8_121, List.forall_mem_cons.2 ⟨subd9_8_122, List.forall_mem_cons.2 ⟨subd9_8_123, List.forall_mem_cons.2 ⟨subd9_8_124, List.forall_mem_cons.2 ⟨subd9_8_125, List.forall_mem_cons.2 ⟨subd9_8_126, List.forall_mem_cons.2 ⟨subd9_8_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_8_128 : subd9_8 [0, 1, -13] = true := by decide +kernel
theorem subd9_8_129 : subd9_8 [0, 1, -12] = true := by decide +kernel
theorem subd9_8_130 : subd9_8 [0, 1, -11] = true := by decide +kernel
theorem subd9_8_131 : subd9_8 [0, 1, -10] = true := by decide +kernel
theorem subd9_8_132 : subd9_8 [0, 1, -9] = true := by decide +kernel
theorem subd9_8_133 : subd9_8 [0, 1, -8] = true := by decide +kernel
theorem subd9_8_134 : subd9_8 [0, 1, -7] = true := by decide +kernel
theorem subd9_8_135 : subd9_8 [0, 1, -6] = true := by decide +kernel
theorem subd9_8_136 : subd9_8 [0, 1, -5] = true := by decide +kernel
theorem subd9_8_137 : subd9_8 [0, 1, -4] = true := by decide +kernel
theorem subd9_8_138 : subd9_8 [0, 1, -3] = true := by decide +kernel
theorem subd9_8_139 : subd9_8 [0, 1, -2] = true := by decide +kernel
theorem subd9_8_140 : subd9_8 [0, 1, -1] = true := by decide +kernel
theorem subd9_8_141 : subd9_8 [0, 1, 0] = true := by decide +kernel
theorem subd9_8_142 : subd9_8 [0, 1, 1] = true := by decide +kernel
theorem subd9_8_143 : subd9_8 [0, 1, 2] = true := by decide +kernel
theorem subd9_8_144 : subd9_8 [0, 1, 3] = true := by decide +kernel
theorem subd9_8_145 : subd9_8 [0, 1, 4] = true := by decide +kernel
theorem subd9_8_146 : subd9_8 [0, 1, 5] = true := by decide +kernel
theorem subd9_8_147 : subd9_8 [0, 1, 6] = true := by decide +kernel
theorem subd9_8_148 : subd9_8 [0, 1, 7] = true := by decide +kernel
theorem subd9_8_149 : subd9_8 [0, 1, 8] = true := by decide +kernel
theorem subd9_8_150 : subd9_8 [0, 1, 9] = true := by decide +kernel
theorem subd9_8_151 : subd9_8 [0, 1, 10] = true := by decide +kernel
theorem subd9_8_152 : subd9_8 [0, 1, 11] = true := by decide +kernel
theorem subd9_8_153 : subd9_8 [0, 1, 12] = true := by decide +kernel
theorem subd9_8_154 : subd9_8 [0, 1, 13] = true := by decide +kernel
theorem subd9_8_155 : subd9_8 [0, 1, 14] = true := by decide +kernel
theorem subd9_8_156 : subd9_8 [0, 1, 15] = true := by decide +kernel
theorem subd9_8_157 : subd9_8 [1, -1] = true := by decide +kernel
theorem subd9_8_158 : subd9_8 [1, 0, -14] = true := by decide +kernel
theorem subd9_8_159 : subd9_8 [1, 0, -13] = true := by decide +kernel
theorem sbd9_8_4 : ∀ q ∈ blkd9_8_4, subd9_8 q = true := by
  unfold blkd9_8_4
  exact List.forall_mem_cons.2 ⟨subd9_8_128, List.forall_mem_cons.2 ⟨subd9_8_129, List.forall_mem_cons.2 ⟨subd9_8_130, List.forall_mem_cons.2 ⟨subd9_8_131, List.forall_mem_cons.2 ⟨subd9_8_132, List.forall_mem_cons.2 ⟨subd9_8_133, List.forall_mem_cons.2 ⟨subd9_8_134, List.forall_mem_cons.2 ⟨subd9_8_135, List.forall_mem_cons.2 ⟨subd9_8_136, List.forall_mem_cons.2 ⟨subd9_8_137, List.forall_mem_cons.2 ⟨subd9_8_138, List.forall_mem_cons.2 ⟨subd9_8_139, List.forall_mem_cons.2 ⟨subd9_8_140, List.forall_mem_cons.2 ⟨subd9_8_141, List.forall_mem_cons.2 ⟨subd9_8_142, List.forall_mem_cons.2 ⟨subd9_8_143, List.forall_mem_cons.2 ⟨subd9_8_144, List.forall_mem_cons.2 ⟨subd9_8_145, List.forall_mem_cons.2 ⟨subd9_8_146, List.forall_mem_cons.2 ⟨subd9_8_147, List.forall_mem_cons.2 ⟨subd9_8_148, List.forall_mem_cons.2 ⟨subd9_8_149, List.forall_mem_cons.2 ⟨subd9_8_150, List.forall_mem_cons.2 ⟨subd9_8_151, List.forall_mem_cons.2 ⟨subd9_8_152, List.forall_mem_cons.2 ⟨subd9_8_153, List.forall_mem_cons.2 ⟨subd9_8_154, List.forall_mem_cons.2 ⟨subd9_8_155, List.forall_mem_cons.2 ⟨subd9_8_156, List.forall_mem_cons.2 ⟨subd9_8_157, List.forall_mem_cons.2 ⟨subd9_8_158, List.forall_mem_cons.2 ⟨subd9_8_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_8_160 : subd9_8 [1, 0, -12] = true := by decide +kernel
theorem subd9_8_161 : subd9_8 [1, 0, -11] = true := by decide +kernel
theorem subd9_8_162 : subd9_8 [1, 0, -10] = true := by decide +kernel
theorem subd9_8_163 : subd9_8 [1, 0, -9] = true := by decide +kernel
theorem subd9_8_164 : subd9_8 [1, 0, -8] = true := by decide +kernel
theorem subd9_8_165 : subd9_8 [1, 0, -7] = true := by decide +kernel
theorem subd9_8_166 : subd9_8 [1, 0, -6] = true := by decide +kernel
theorem subd9_8_167 : subd9_8 [1, 0, -5] = true := by decide +kernel
theorem subd9_8_168 : subd9_8 [1, 0, -4] = true := by decide +kernel
theorem subd9_8_169 : subd9_8 [1, 0, -3] = true := by decide +kernel
theorem subd9_8_170 : subd9_8 [1, 0, -2] = true := by decide +kernel
theorem subd9_8_171 : subd9_8 [1, 0, -1] = true := by decide +kernel
theorem subd9_8_172 : subd9_8 [1, 0, 0] = true := by decide +kernel
theorem subd9_8_173 : subd9_8 [1, 0, 1] = true := by decide +kernel
theorem subd9_8_174 : subd9_8 [1, 0, 2] = true := by decide +kernel
theorem subd9_8_175 : subd9_8 [1, 0, 3] = true := by decide +kernel
theorem subd9_8_176 : subd9_8 [1, 0, 4] = true := by decide +kernel
theorem subd9_8_177 : subd9_8 [1, 0, 5] = true := by decide +kernel
theorem subd9_8_178 : subd9_8 [1, 0, 6] = true := by decide +kernel
theorem subd9_8_179 : subd9_8 [1, 0, 7] = true := by decide +kernel
theorem subd9_8_180 : subd9_8 [1, 0, 8] = true := by decide +kernel
theorem subd9_8_181 : subd9_8 [1, 0, 9] = true := by decide +kernel
theorem subd9_8_182 : subd9_8 [1, 0, 10] = true := by decide +kernel
theorem subd9_8_183 : subd9_8 [1, 0, 11] = true := by decide +kernel
theorem subd9_8_184 : subd9_8 [1, 0, 12] = true := by decide +kernel
theorem subd9_8_185 : subd9_8 [1, 0, 13] = true := by decide +kernel
theorem subd9_8_186 : subd9_8 [1, 1, -11] = true := by decide +kernel
theorem subd9_8_187 : subd9_8 [1, 1, -10] = true := by decide +kernel
theorem subd9_8_188 : subd9_8 [1, 1, -9] = true := by decide +kernel
theorem subd9_8_189 : subd9_8 [1, 1, -8] = true := by decide +kernel
theorem subd9_8_190 : subd9_8 [1, 1, -7] = true := by decide +kernel
theorem subd9_8_191 : subd9_8 [1, 1, -6] = true := by decide +kernel
theorem sbd9_8_5 : ∀ q ∈ blkd9_8_5, subd9_8 q = true := by
  unfold blkd9_8_5
  exact List.forall_mem_cons.2 ⟨subd9_8_160, List.forall_mem_cons.2 ⟨subd9_8_161, List.forall_mem_cons.2 ⟨subd9_8_162, List.forall_mem_cons.2 ⟨subd9_8_163, List.forall_mem_cons.2 ⟨subd9_8_164, List.forall_mem_cons.2 ⟨subd9_8_165, List.forall_mem_cons.2 ⟨subd9_8_166, List.forall_mem_cons.2 ⟨subd9_8_167, List.forall_mem_cons.2 ⟨subd9_8_168, List.forall_mem_cons.2 ⟨subd9_8_169, List.forall_mem_cons.2 ⟨subd9_8_170, List.forall_mem_cons.2 ⟨subd9_8_171, List.forall_mem_cons.2 ⟨subd9_8_172, List.forall_mem_cons.2 ⟨subd9_8_173, List.forall_mem_cons.2 ⟨subd9_8_174, List.forall_mem_cons.2 ⟨subd9_8_175, List.forall_mem_cons.2 ⟨subd9_8_176, List.forall_mem_cons.2 ⟨subd9_8_177, List.forall_mem_cons.2 ⟨subd9_8_178, List.forall_mem_cons.2 ⟨subd9_8_179, List.forall_mem_cons.2 ⟨subd9_8_180, List.forall_mem_cons.2 ⟨subd9_8_181, List.forall_mem_cons.2 ⟨subd9_8_182, List.forall_mem_cons.2 ⟨subd9_8_183, List.forall_mem_cons.2 ⟨subd9_8_184, List.forall_mem_cons.2 ⟨subd9_8_185, List.forall_mem_cons.2 ⟨subd9_8_186, List.forall_mem_cons.2 ⟨subd9_8_187, List.forall_mem_cons.2 ⟨subd9_8_188, List.forall_mem_cons.2 ⟨subd9_8_189, List.forall_mem_cons.2 ⟨subd9_8_190, List.forall_mem_cons.2 ⟨subd9_8_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_8_192 : subd9_8 [1, 1, -5] = true := by decide +kernel
theorem subd9_8_193 : subd9_8 [1, 1, -4] = true := by decide +kernel
theorem subd9_8_194 : subd9_8 [1, 1, -3] = true := by decide +kernel
theorem subd9_8_195 : subd9_8 [1, 1, -2] = true := by decide +kernel
theorem subd9_8_196 : subd9_8 [1, 1, -1] = true := by decide +kernel
theorem subd9_8_197 : subd9_8 [1, 1, 0] = true := by decide +kernel
theorem subd9_8_198 : subd9_8 [1, 1, 1] = true := by decide +kernel
theorem subd9_8_199 : subd9_8 [1, 1, 2] = true := by decide +kernel
theorem subd9_8_200 : subd9_8 [1, 1, 3] = true := by decide +kernel
theorem subd9_8_201 : subd9_8 [1, 1, 4] = true := by decide +kernel
theorem subd9_8_202 : subd9_8 [1, 1, 5] = true := by decide +kernel
theorem subd9_8_203 : subd9_8 [1, 1, 6] = true := by decide +kernel
theorem subd9_8_204 : subd9_8 [1, 1, 7] = true := by decide +kernel
theorem subd9_8_205 : subd9_8 [1, 1, 8] = true := by decide +kernel
theorem subd9_8_206 : subd9_8 [1, 1, 9] = true := by decide +kernel
theorem sbd9_8_6 : ∀ q ∈ blkd9_8_6, subd9_8 q = true := by
  unfold blkd9_8_6
  exact List.forall_mem_cons.2 ⟨subd9_8_192, List.forall_mem_cons.2 ⟨subd9_8_193, List.forall_mem_cons.2 ⟨subd9_8_194, List.forall_mem_cons.2 ⟨subd9_8_195, List.forall_mem_cons.2 ⟨subd9_8_196, List.forall_mem_cons.2 ⟨subd9_8_197, List.forall_mem_cons.2 ⟨subd9_8_198, List.forall_mem_cons.2 ⟨subd9_8_199, List.forall_mem_cons.2 ⟨subd9_8_200, List.forall_mem_cons.2 ⟨subd9_8_201, List.forall_mem_cons.2 ⟨subd9_8_202, List.forall_mem_cons.2 ⟨subd9_8_203, List.forall_mem_cons.2 ⟨subd9_8_204, List.forall_mem_cons.2 ⟨subd9_8_205, List.forall_mem_cons.2 ⟨subd9_8_206, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_9 : ldCheck G d9_9.U d9_9.ms ldd9_9 = true := by decide +kernel
theorem pre_okd9_9 : subPre G cell9 d9_9 = true := by decide +kernel
theorem subd9_9_0 : subd9_9 [-3, -3] = true := by decide +kernel
theorem subd9_9_1 : subd9_9 [-3, -2] = true := by decide +kernel
theorem subd9_9_2 : subd9_9 [-3, -1] = true := by decide +kernel
theorem subd9_9_3 : subd9_9 [-3, 0] = true := by decide +kernel
theorem subd9_9_4 : subd9_9 [-3, 1] = true := by decide +kernel
theorem subd9_9_5 : subd9_9 [-3, 2] = true := by decide +kernel
theorem subd9_9_6 : subd9_9 [-2, -4] = true := by decide +kernel
theorem subd9_9_7 : subd9_9 [-2, -3] = true := by decide +kernel
theorem subd9_9_8 : subd9_9 [-2, -2] = true := by decide +kernel
theorem subd9_9_9 : subd9_9 [-2, -1] = true := by decide +kernel
theorem subd9_9_10 : subd9_9 [-2, 0] = true := by decide +kernel
theorem subd9_9_11 : subd9_9 [-2, 1] = true := by decide +kernel
theorem subd9_9_12 : subd9_9 [-2, 2] = true := by decide +kernel
theorem subd9_9_13 : subd9_9 [-2, 3] = true := by decide +kernel
theorem subd9_9_14 : subd9_9 [-1, -4] = true := by decide +kernel
theorem subd9_9_15 : subd9_9 [-1, -3] = true := by decide +kernel
theorem subd9_9_16 : subd9_9 [-1, -2] = true := by decide +kernel
theorem subd9_9_17 : subd9_9 [-1, -1] = true := by decide +kernel
theorem subd9_9_18 : subd9_9 [-1, 0] = true := by decide +kernel
theorem subd9_9_19 : subd9_9 [-1, 1] = true := by decide +kernel
theorem subd9_9_20 : subd9_9 [-1, 2] = true := by decide +kernel
theorem subd9_9_21 : subd9_9 [-1, 3] = true := by decide +kernel
theorem subd9_9_22 : subd9_9 [0, -4] = true := by decide +kernel
theorem subd9_9_23 : subd9_9 [0, -3] = true := by decide +kernel
theorem subd9_9_24 : subd9_9 [0, -2] = true := by decide +kernel
theorem subd9_9_25 : subd9_9 [0, -1] = true := by decide +kernel
theorem subd9_9_26 : subd9_9 [0, 0, -7] = true := by decide +kernel
theorem subd9_9_27 : subd9_9 [0, 0, -6] = true := by decide +kernel
theorem subd9_9_28 : subd9_9 [0, 0, -5] = true := by decide +kernel
theorem subd9_9_29 : subd9_9 [0, 0, -4] = true := by decide +kernel
theorem subd9_9_30 : subd9_9 [0, 0, -3] = true := by decide +kernel
theorem subd9_9_31 : subd9_9 [0, 0, -2] = true := by decide +kernel
theorem sbd9_9_0 : ∀ q ∈ blkd9_9_0, subd9_9 q = true := by
  unfold blkd9_9_0
  exact List.forall_mem_cons.2 ⟨subd9_9_0, List.forall_mem_cons.2 ⟨subd9_9_1, List.forall_mem_cons.2 ⟨subd9_9_2, List.forall_mem_cons.2 ⟨subd9_9_3, List.forall_mem_cons.2 ⟨subd9_9_4, List.forall_mem_cons.2 ⟨subd9_9_5, List.forall_mem_cons.2 ⟨subd9_9_6, List.forall_mem_cons.2 ⟨subd9_9_7, List.forall_mem_cons.2 ⟨subd9_9_8, List.forall_mem_cons.2 ⟨subd9_9_9, List.forall_mem_cons.2 ⟨subd9_9_10, List.forall_mem_cons.2 ⟨subd9_9_11, List.forall_mem_cons.2 ⟨subd9_9_12, List.forall_mem_cons.2 ⟨subd9_9_13, List.forall_mem_cons.2 ⟨subd9_9_14, List.forall_mem_cons.2 ⟨subd9_9_15, List.forall_mem_cons.2 ⟨subd9_9_16, List.forall_mem_cons.2 ⟨subd9_9_17, List.forall_mem_cons.2 ⟨subd9_9_18, List.forall_mem_cons.2 ⟨subd9_9_19, List.forall_mem_cons.2 ⟨subd9_9_20, List.forall_mem_cons.2 ⟨subd9_9_21, List.forall_mem_cons.2 ⟨subd9_9_22, List.forall_mem_cons.2 ⟨subd9_9_23, List.forall_mem_cons.2 ⟨subd9_9_24, List.forall_mem_cons.2 ⟨subd9_9_25, List.forall_mem_cons.2 ⟨subd9_9_26, List.forall_mem_cons.2 ⟨subd9_9_27, List.forall_mem_cons.2 ⟨subd9_9_28, List.forall_mem_cons.2 ⟨subd9_9_29, List.forall_mem_cons.2 ⟨subd9_9_30, List.forall_mem_cons.2 ⟨subd9_9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_9_32 : subd9_9 [0, 0, -1] = true := by decide +kernel
theorem subd9_9_33 : subd9_9 [0, 0, 0] = true := by decide +kernel
theorem subd9_9_34 : subd9_9 [0, 0, 1] = true := by decide +kernel
theorem subd9_9_35 : subd9_9 [0, 0, 2] = true := by decide +kernel
theorem subd9_9_36 : subd9_9 [0, 0, 3] = true := by decide +kernel
theorem subd9_9_37 : subd9_9 [0, 0, 4] = true := by decide +kernel
theorem subd9_9_38 : subd9_9 [0, 0, 5] = true := by decide +kernel
theorem subd9_9_39 : subd9_9 [0, 0, 6] = true := by decide +kernel
theorem subd9_9_40 : subd9_9 [0, 1] = true := by decide +kernel
theorem subd9_9_41 : subd9_9 [0, 2] = true := by decide +kernel
theorem subd9_9_42 : subd9_9 [0, 3] = true := by decide +kernel
theorem subd9_9_43 : subd9_9 [1, -4] = true := by decide +kernel
theorem subd9_9_44 : subd9_9 [1, -3] = true := by decide +kernel
theorem subd9_9_45 : subd9_9 [1, -2] = true := by decide +kernel
theorem subd9_9_46 : subd9_9 [1, -1] = true := by decide +kernel
theorem subd9_9_47 : subd9_9 [1, 0] = true := by decide +kernel
theorem subd9_9_48 : subd9_9 [1, 1] = true := by decide +kernel
theorem subd9_9_49 : subd9_9 [1, 2] = true := by decide +kernel
theorem subd9_9_50 : subd9_9 [1, 3] = true := by decide +kernel
theorem subd9_9_51 : subd9_9 [2, -4] = true := by decide +kernel
theorem subd9_9_52 : subd9_9 [2, -3] = true := by decide +kernel
theorem subd9_9_53 : subd9_9 [2, -2] = true := by decide +kernel
theorem subd9_9_54 : subd9_9 [2, -1] = true := by decide +kernel
theorem subd9_9_55 : subd9_9 [2, 0] = true := by decide +kernel
theorem subd9_9_56 : subd9_9 [2, 1] = true := by decide +kernel
theorem subd9_9_57 : subd9_9 [2, 2] = true := by decide +kernel
theorem subd9_9_58 : subd9_9 [2, 3] = true := by decide +kernel
theorem subd9_9_59 : subd9_9 [3, -3] = true := by decide +kernel
theorem subd9_9_60 : subd9_9 [3, -2] = true := by decide +kernel
theorem subd9_9_61 : subd9_9 [3, -1] = true := by decide +kernel
theorem subd9_9_62 : subd9_9 [3, 0] = true := by decide +kernel
theorem subd9_9_63 : subd9_9 [3, 1] = true := by decide +kernel
theorem sbd9_9_1 : ∀ q ∈ blkd9_9_1, subd9_9 q = true := by
  unfold blkd9_9_1
  exact List.forall_mem_cons.2 ⟨subd9_9_32, List.forall_mem_cons.2 ⟨subd9_9_33, List.forall_mem_cons.2 ⟨subd9_9_34, List.forall_mem_cons.2 ⟨subd9_9_35, List.forall_mem_cons.2 ⟨subd9_9_36, List.forall_mem_cons.2 ⟨subd9_9_37, List.forall_mem_cons.2 ⟨subd9_9_38, List.forall_mem_cons.2 ⟨subd9_9_39, List.forall_mem_cons.2 ⟨subd9_9_40, List.forall_mem_cons.2 ⟨subd9_9_41, List.forall_mem_cons.2 ⟨subd9_9_42, List.forall_mem_cons.2 ⟨subd9_9_43, List.forall_mem_cons.2 ⟨subd9_9_44, List.forall_mem_cons.2 ⟨subd9_9_45, List.forall_mem_cons.2 ⟨subd9_9_46, List.forall_mem_cons.2 ⟨subd9_9_47, List.forall_mem_cons.2 ⟨subd9_9_48, List.forall_mem_cons.2 ⟨subd9_9_49, List.forall_mem_cons.2 ⟨subd9_9_50, List.forall_mem_cons.2 ⟨subd9_9_51, List.forall_mem_cons.2 ⟨subd9_9_52, List.forall_mem_cons.2 ⟨subd9_9_53, List.forall_mem_cons.2 ⟨subd9_9_54, List.forall_mem_cons.2 ⟨subd9_9_55, List.forall_mem_cons.2 ⟨subd9_9_56, List.forall_mem_cons.2 ⟨subd9_9_57, List.forall_mem_cons.2 ⟨subd9_9_58, List.forall_mem_cons.2 ⟨subd9_9_59, List.forall_mem_cons.2 ⟨subd9_9_60, List.forall_mem_cons.2 ⟨subd9_9_61, List.forall_mem_cons.2 ⟨subd9_9_62, List.forall_mem_cons.2 ⟨subd9_9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_9_64 : subd9_9 [3, 2] = true := by decide +kernel
theorem sbd9_9_2 : ∀ q ∈ blkd9_9_2, subd9_9 q = true := by
  unfold blkd9_9_2
  exact List.forall_mem_cons.2 ⟨subd9_9_64, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C124
