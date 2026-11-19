import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_2_128 : subd6_2 [1, -5] = true := by decide +kernel
theorem subd6_2_129 : subd6_2 [1, -4] = true := by decide +kernel
theorem subd6_2_130 : subd6_2 [1, -3] = true := by decide +kernel
theorem subd6_2_131 : subd6_2 [1, -2] = true := by decide +kernel
theorem subd6_2_132 : subd6_2 [1, -1, -7] = true := by decide +kernel
theorem subd6_2_133 : subd6_2 [1, -1, -6] = true := by decide +kernel
theorem subd6_2_134 : subd6_2 [1, -1, -5] = true := by decide +kernel
theorem subd6_2_135 : subd6_2 [1, -1, -4] = true := by decide +kernel
theorem subd6_2_136 : subd6_2 [1, -1, -3] = true := by decide +kernel
theorem subd6_2_137 : subd6_2 [1, -1, -2] = true := by decide +kernel
theorem subd6_2_138 : subd6_2 [1, -1, -1] = true := by decide +kernel
theorem subd6_2_139 : subd6_2 [1, -1, 0] = true := by decide +kernel
theorem subd6_2_140 : subd6_2 [1, -1, 1] = true := by decide +kernel
theorem subd6_2_141 : subd6_2 [1, -1, 2] = true := by decide +kernel
theorem subd6_2_142 : subd6_2 [1, -1, 3] = true := by decide +kernel
theorem subd6_2_143 : subd6_2 [1, -1, 4] = true := by decide +kernel
theorem subd6_2_144 : subd6_2 [1, -1, 5] = true := by decide +kernel
theorem subd6_2_145 : subd6_2 [1, -1, 6] = true := by decide +kernel
theorem subd6_2_146 : subd6_2 [1, 0, -7] = true := by decide +kernel
theorem subd6_2_147 : subd6_2 [1, 0, -6] = true := by decide +kernel
theorem subd6_2_148 : subd6_2 [1, 0, -5] = true := by decide +kernel
theorem subd6_2_149 : subd6_2 [1, 0, -4] = true := by decide +kernel
theorem subd6_2_150 : subd6_2 [1, 0, -3] = true := by decide +kernel
theorem subd6_2_151 : subd6_2 [1, 0, -2] = true := by decide +kernel
theorem subd6_2_152 : subd6_2 [1, 0, -1] = true := by decide +kernel
theorem subd6_2_153 : subd6_2 [1, 0, 0] = true := by decide +kernel
theorem subd6_2_154 : subd6_2 [1, 0, 1] = true := by decide +kernel
theorem subd6_2_155 : subd6_2 [1, 0, 2] = true := by decide +kernel
theorem subd6_2_156 : subd6_2 [1, 0, 3] = true := by decide +kernel
theorem subd6_2_157 : subd6_2 [1, 0, 4] = true := by decide +kernel
theorem subd6_2_158 : subd6_2 [1, 0, 5] = true := by decide +kernel
theorem subd6_2_159 : subd6_2 [1, 0, 6] = true := by decide +kernel
theorem sbd6_2_4 : ∀ q ∈ blkd6_2_4, subd6_2 q = true := by
  unfold blkd6_2_4
  exact List.forall_mem_cons.2 ⟨subd6_2_128, List.forall_mem_cons.2 ⟨subd6_2_129, List.forall_mem_cons.2 ⟨subd6_2_130, List.forall_mem_cons.2 ⟨subd6_2_131, List.forall_mem_cons.2 ⟨subd6_2_132, List.forall_mem_cons.2 ⟨subd6_2_133, List.forall_mem_cons.2 ⟨subd6_2_134, List.forall_mem_cons.2 ⟨subd6_2_135, List.forall_mem_cons.2 ⟨subd6_2_136, List.forall_mem_cons.2 ⟨subd6_2_137, List.forall_mem_cons.2 ⟨subd6_2_138, List.forall_mem_cons.2 ⟨subd6_2_139, List.forall_mem_cons.2 ⟨subd6_2_140, List.forall_mem_cons.2 ⟨subd6_2_141, List.forall_mem_cons.2 ⟨subd6_2_142, List.forall_mem_cons.2 ⟨subd6_2_143, List.forall_mem_cons.2 ⟨subd6_2_144, List.forall_mem_cons.2 ⟨subd6_2_145, List.forall_mem_cons.2 ⟨subd6_2_146, List.forall_mem_cons.2 ⟨subd6_2_147, List.forall_mem_cons.2 ⟨subd6_2_148, List.forall_mem_cons.2 ⟨subd6_2_149, List.forall_mem_cons.2 ⟨subd6_2_150, List.forall_mem_cons.2 ⟨subd6_2_151, List.forall_mem_cons.2 ⟨subd6_2_152, List.forall_mem_cons.2 ⟨subd6_2_153, List.forall_mem_cons.2 ⟨subd6_2_154, List.forall_mem_cons.2 ⟨subd6_2_155, List.forall_mem_cons.2 ⟨subd6_2_156, List.forall_mem_cons.2 ⟨subd6_2_157, List.forall_mem_cons.2 ⟨subd6_2_158, List.forall_mem_cons.2 ⟨subd6_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_160 : subd6_2 [1, 1, -6] = true := by decide +kernel
theorem subd6_2_161 : subd6_2 [1, 1, -5] = true := by decide +kernel
theorem subd6_2_162 : subd6_2 [1, 1, -4] = true := by decide +kernel
theorem subd6_2_163 : subd6_2 [1, 1, -3] = true := by decide +kernel
theorem subd6_2_164 : subd6_2 [1, 1, -2] = true := by decide +kernel
theorem subd6_2_165 : subd6_2 [1, 1, -1] = true := by decide +kernel
theorem subd6_2_166 : subd6_2 [1, 1, 0] = true := by decide +kernel
theorem subd6_2_167 : subd6_2 [1, 1, 1] = true := by decide +kernel
theorem subd6_2_168 : subd6_2 [1, 1, 2] = true := by decide +kernel
theorem subd6_2_169 : subd6_2 [1, 1, 3] = true := by decide +kernel
theorem subd6_2_170 : subd6_2 [1, 1, 4] = true := by decide +kernel
theorem subd6_2_171 : subd6_2 [1, 1, 5] = true := by decide +kernel
theorem subd6_2_172 : subd6_2 [1, 1, 6] = true := by decide +kernel
theorem subd6_2_173 : subd6_2 [1, 2] = true := by decide +kernel
theorem subd6_2_174 : subd6_2 [1, 3] = true := by decide +kernel
theorem subd6_2_175 : subd6_2 [1, 4] = true := by decide +kernel
theorem subd6_2_176 : subd6_2 [2, -5] = true := by decide +kernel
theorem subd6_2_177 : subd6_2 [2, -4] = true := by decide +kernel
theorem subd6_2_178 : subd6_2 [2, -3] = true := by decide +kernel
theorem subd6_2_179 : subd6_2 [2, -2] = true := by decide +kernel
theorem subd6_2_180 : subd6_2 [2, -1] = true := by decide +kernel
theorem subd6_2_181 : subd6_2 [2, 0] = true := by decide +kernel
theorem subd6_2_182 : subd6_2 [2, 1] = true := by decide +kernel
theorem subd6_2_183 : subd6_2 [2, 2] = true := by decide +kernel
theorem subd6_2_184 : subd6_2 [2, 3] = true := by decide +kernel
theorem subd6_2_185 : subd6_2 [2, 4] = true := by decide +kernel
theorem subd6_2_186 : subd6_2 [3, -5] = true := by decide +kernel
theorem subd6_2_187 : subd6_2 [3, -4] = true := by decide +kernel
theorem subd6_2_188 : subd6_2 [3, -3] = true := by decide +kernel
theorem subd6_2_189 : subd6_2 [3, -2] = true := by decide +kernel
theorem subd6_2_190 : subd6_2 [3, -1] = true := by decide +kernel
theorem subd6_2_191 : subd6_2 [3, 0] = true := by decide +kernel
theorem sbd6_2_5 : ∀ q ∈ blkd6_2_5, subd6_2 q = true := by
  unfold blkd6_2_5
  exact List.forall_mem_cons.2 ⟨subd6_2_160, List.forall_mem_cons.2 ⟨subd6_2_161, List.forall_mem_cons.2 ⟨subd6_2_162, List.forall_mem_cons.2 ⟨subd6_2_163, List.forall_mem_cons.2 ⟨subd6_2_164, List.forall_mem_cons.2 ⟨subd6_2_165, List.forall_mem_cons.2 ⟨subd6_2_166, List.forall_mem_cons.2 ⟨subd6_2_167, List.forall_mem_cons.2 ⟨subd6_2_168, List.forall_mem_cons.2 ⟨subd6_2_169, List.forall_mem_cons.2 ⟨subd6_2_170, List.forall_mem_cons.2 ⟨subd6_2_171, List.forall_mem_cons.2 ⟨subd6_2_172, List.forall_mem_cons.2 ⟨subd6_2_173, List.forall_mem_cons.2 ⟨subd6_2_174, List.forall_mem_cons.2 ⟨subd6_2_175, List.forall_mem_cons.2 ⟨subd6_2_176, List.forall_mem_cons.2 ⟨subd6_2_177, List.forall_mem_cons.2 ⟨subd6_2_178, List.forall_mem_cons.2 ⟨subd6_2_179, List.forall_mem_cons.2 ⟨subd6_2_180, List.forall_mem_cons.2 ⟨subd6_2_181, List.forall_mem_cons.2 ⟨subd6_2_182, List.forall_mem_cons.2 ⟨subd6_2_183, List.forall_mem_cons.2 ⟨subd6_2_184, List.forall_mem_cons.2 ⟨subd6_2_185, List.forall_mem_cons.2 ⟨subd6_2_186, List.forall_mem_cons.2 ⟨subd6_2_187, List.forall_mem_cons.2 ⟨subd6_2_188, List.forall_mem_cons.2 ⟨subd6_2_189, List.forall_mem_cons.2 ⟨subd6_2_190, List.forall_mem_cons.2 ⟨subd6_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_192 : subd6_2 [3, 1] = true := by decide +kernel
theorem subd6_2_193 : subd6_2 [3, 2] = true := by decide +kernel
theorem subd6_2_194 : subd6_2 [3, 3] = true := by decide +kernel
theorem subd6_2_195 : subd6_2 [4, -4] = true := by decide +kernel
theorem subd6_2_196 : subd6_2 [4, -3] = true := by decide +kernel
theorem subd6_2_197 : subd6_2 [4, -2] = true := by decide +kernel
theorem subd6_2_198 : subd6_2 [4, -1] = true := by decide +kernel
theorem subd6_2_199 : subd6_2 [4, 0] = true := by decide +kernel
theorem subd6_2_200 : subd6_2 [4, 1] = true := by decide +kernel
theorem subd6_2_201 : subd6_2 [4, 2] = true := by decide +kernel
theorem subd6_2_202 : subd6_2 [5] = true := by decide +kernel
theorem sbd6_2_6 : ∀ q ∈ blkd6_2_6, subd6_2 q = true := by
  unfold blkd6_2_6
  exact List.forall_mem_cons.2 ⟨subd6_2_192, List.forall_mem_cons.2 ⟨subd6_2_193, List.forall_mem_cons.2 ⟨subd6_2_194, List.forall_mem_cons.2 ⟨subd6_2_195, List.forall_mem_cons.2 ⟨subd6_2_196, List.forall_mem_cons.2 ⟨subd6_2_197, List.forall_mem_cons.2 ⟨subd6_2_198, List.forall_mem_cons.2 ⟨subd6_2_199, List.forall_mem_cons.2 ⟨subd6_2_200, List.forall_mem_cons.2 ⟨subd6_2_201, List.forall_mem_cons.2 ⟨subd6_2_202, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [-5] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-4, -7] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [-4, -6] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [-4, -5] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [-4, -4] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [-4, -3] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [-4, -2] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [-4, -1] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [-4, 0] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [-4, 1] = true := by decide +kernel
theorem subd6_3_10 : subd6_3 [-4, 2] = true := by decide +kernel
theorem subd6_3_11 : subd6_3 [-3, -7] = true := by decide +kernel
theorem subd6_3_12 : subd6_3 [-3, -6] = true := by decide +kernel
theorem subd6_3_13 : subd6_3 [-3, -5] = true := by decide +kernel
theorem subd6_3_14 : subd6_3 [-3, -4] = true := by decide +kernel
theorem subd6_3_15 : subd6_3 [-3, -3] = true := by decide +kernel
theorem subd6_3_16 : subd6_3 [-3, -2] = true := by decide +kernel
theorem subd6_3_17 : subd6_3 [-3, -1] = true := by decide +kernel
theorem subd6_3_18 : subd6_3 [-3, 0] = true := by decide +kernel
theorem subd6_3_19 : subd6_3 [-3, 1] = true := by decide +kernel
theorem subd6_3_20 : subd6_3 [-3, 2] = true := by decide +kernel
theorem subd6_3_21 : subd6_3 [-3, 3] = true := by decide +kernel
theorem subd6_3_22 : subd6_3 [-3, 4] = true := by decide +kernel
theorem subd6_3_23 : subd6_3 [-2, -7] = true := by decide +kernel
theorem subd6_3_24 : subd6_3 [-2, -6] = true := by decide +kernel
theorem subd6_3_25 : subd6_3 [-2, -5] = true := by decide +kernel
theorem subd6_3_26 : subd6_3 [-2, -4] = true := by decide +kernel
theorem subd6_3_27 : subd6_3 [-2, -3] = true := by decide +kernel
theorem subd6_3_28 : subd6_3 [-2, -2] = true := by decide +kernel
theorem subd6_3_29 : subd6_3 [-2, -1] = true := by decide +kernel
theorem subd6_3_30 : subd6_3 [-2, 0] = true := by decide +kernel
theorem subd6_3_31 : subd6_3 [-2, 1] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_cons.2 ⟨subd6_3_10, List.forall_mem_cons.2 ⟨subd6_3_11, List.forall_mem_cons.2 ⟨subd6_3_12, List.forall_mem_cons.2 ⟨subd6_3_13, List.forall_mem_cons.2 ⟨subd6_3_14, List.forall_mem_cons.2 ⟨subd6_3_15, List.forall_mem_cons.2 ⟨subd6_3_16, List.forall_mem_cons.2 ⟨subd6_3_17, List.forall_mem_cons.2 ⟨subd6_3_18, List.forall_mem_cons.2 ⟨subd6_3_19, List.forall_mem_cons.2 ⟨subd6_3_20, List.forall_mem_cons.2 ⟨subd6_3_21, List.forall_mem_cons.2 ⟨subd6_3_22, List.forall_mem_cons.2 ⟨subd6_3_23, List.forall_mem_cons.2 ⟨subd6_3_24, List.forall_mem_cons.2 ⟨subd6_3_25, List.forall_mem_cons.2 ⟨subd6_3_26, List.forall_mem_cons.2 ⟨subd6_3_27, List.forall_mem_cons.2 ⟨subd6_3_28, List.forall_mem_cons.2 ⟨subd6_3_29, List.forall_mem_cons.2 ⟨subd6_3_30, List.forall_mem_cons.2 ⟨subd6_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
