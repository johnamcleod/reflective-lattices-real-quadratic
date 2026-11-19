import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_2_128 : subd11_2 [0, 1, -5] = true := by decide +kernel
theorem subd11_2_129 : subd11_2 [0, 1, -4] = true := by decide +kernel
theorem subd11_2_130 : subd11_2 [0, 1, -3] = true := by decide +kernel
theorem subd11_2_131 : subd11_2 [0, 1, -2] = true := by decide +kernel
theorem subd11_2_132 : subd11_2 [0, 1, -1] = true := by decide +kernel
theorem subd11_2_133 : subd11_2 [0, 1, 0] = true := by decide +kernel
theorem subd11_2_134 : subd11_2 [0, 1, 1] = true := by decide +kernel
theorem subd11_2_135 : subd11_2 [0, 1, 2] = true := by decide +kernel
theorem subd11_2_136 : subd11_2 [0, 1, 3] = true := by decide +kernel
theorem subd11_2_137 : subd11_2 [0, 1, 4] = true := by decide +kernel
theorem subd11_2_138 : subd11_2 [0, 1, 5] = true := by decide +kernel
theorem subd11_2_139 : subd11_2 [0, 1, 6] = true := by decide +kernel
theorem subd11_2_140 : subd11_2 [0, 1, 7] = true := by decide +kernel
theorem subd11_2_141 : subd11_2 [0, 1, 8] = true := by decide +kernel
theorem subd11_2_142 : subd11_2 [0, 2, -6] = true := by decide +kernel
theorem subd11_2_143 : subd11_2 [0, 2, -5] = true := by decide +kernel
theorem subd11_2_144 : subd11_2 [0, 2, -4] = true := by decide +kernel
theorem subd11_2_145 : subd11_2 [0, 2, -3] = true := by decide +kernel
theorem subd11_2_146 : subd11_2 [0, 2, -2] = true := by decide +kernel
theorem subd11_2_147 : subd11_2 [0, 2, -1] = true := by decide +kernel
theorem subd11_2_148 : subd11_2 [0, 2, 0] = true := by decide +kernel
theorem subd11_2_149 : subd11_2 [0, 2, 1] = true := by decide +kernel
theorem subd11_2_150 : subd11_2 [0, 2, 2] = true := by decide +kernel
theorem subd11_2_151 : subd11_2 [0, 2, 3] = true := by decide +kernel
theorem subd11_2_152 : subd11_2 [0, 2, 4] = true := by decide +kernel
theorem subd11_2_153 : subd11_2 [0, 2, 5] = true := by decide +kernel
theorem subd11_2_154 : subd11_2 [0, 2, 6] = true := by decide +kernel
theorem subd11_2_155 : subd11_2 [0, 2, 7] = true := by decide +kernel
theorem subd11_2_156 : subd11_2 [1, -3] = true := by decide +kernel
theorem subd11_2_157 : subd11_2 [1, -2] = true := by decide +kernel
theorem subd11_2_158 : subd11_2 [1, -1, -7] = true := by decide +kernel
theorem subd11_2_159 : subd11_2 [1, -1, -6] = true := by decide +kernel
theorem sbd11_2_4 : ∀ q ∈ blkd11_2_4, subd11_2 q = true := by
  unfold blkd11_2_4
  exact List.forall_mem_cons.2 ⟨subd11_2_128, List.forall_mem_cons.2 ⟨subd11_2_129, List.forall_mem_cons.2 ⟨subd11_2_130, List.forall_mem_cons.2 ⟨subd11_2_131, List.forall_mem_cons.2 ⟨subd11_2_132, List.forall_mem_cons.2 ⟨subd11_2_133, List.forall_mem_cons.2 ⟨subd11_2_134, List.forall_mem_cons.2 ⟨subd11_2_135, List.forall_mem_cons.2 ⟨subd11_2_136, List.forall_mem_cons.2 ⟨subd11_2_137, List.forall_mem_cons.2 ⟨subd11_2_138, List.forall_mem_cons.2 ⟨subd11_2_139, List.forall_mem_cons.2 ⟨subd11_2_140, List.forall_mem_cons.2 ⟨subd11_2_141, List.forall_mem_cons.2 ⟨subd11_2_142, List.forall_mem_cons.2 ⟨subd11_2_143, List.forall_mem_cons.2 ⟨subd11_2_144, List.forall_mem_cons.2 ⟨subd11_2_145, List.forall_mem_cons.2 ⟨subd11_2_146, List.forall_mem_cons.2 ⟨subd11_2_147, List.forall_mem_cons.2 ⟨subd11_2_148, List.forall_mem_cons.2 ⟨subd11_2_149, List.forall_mem_cons.2 ⟨subd11_2_150, List.forall_mem_cons.2 ⟨subd11_2_151, List.forall_mem_cons.2 ⟨subd11_2_152, List.forall_mem_cons.2 ⟨subd11_2_153, List.forall_mem_cons.2 ⟨subd11_2_154, List.forall_mem_cons.2 ⟨subd11_2_155, List.forall_mem_cons.2 ⟨subd11_2_156, List.forall_mem_cons.2 ⟨subd11_2_157, List.forall_mem_cons.2 ⟨subd11_2_158, List.forall_mem_cons.2 ⟨subd11_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_160 : subd11_2 [1, -1, -5] = true := by decide +kernel
theorem subd11_2_161 : subd11_2 [1, -1, -4] = true := by decide +kernel
theorem subd11_2_162 : subd11_2 [1, -1, -3] = true := by decide +kernel
theorem subd11_2_163 : subd11_2 [1, -1, -2] = true := by decide +kernel
theorem subd11_2_164 : subd11_2 [1, -1, -1] = true := by decide +kernel
theorem subd11_2_165 : subd11_2 [1, -1, 0] = true := by decide +kernel
theorem subd11_2_166 : subd11_2 [1, -1, 1] = true := by decide +kernel
theorem subd11_2_167 : subd11_2 [1, -1, 2] = true := by decide +kernel
theorem subd11_2_168 : subd11_2 [1, -1, 3] = true := by decide +kernel
theorem subd11_2_169 : subd11_2 [1, -1, 4] = true := by decide +kernel
theorem subd11_2_170 : subd11_2 [1, -1, 5] = true := by decide +kernel
theorem subd11_2_171 : subd11_2 [1, -1, 6] = true := by decide +kernel
theorem subd11_2_172 : subd11_2 [1, -1, 7] = true := by decide +kernel
theorem subd11_2_173 : subd11_2 [1, 0, -8] = true := by decide +kernel
theorem subd11_2_174 : subd11_2 [1, 0, -7] = true := by decide +kernel
theorem subd11_2_175 : subd11_2 [1, 0, -6] = true := by decide +kernel
theorem subd11_2_176 : subd11_2 [1, 0, -5] = true := by decide +kernel
theorem subd11_2_177 : subd11_2 [1, 0, -4] = true := by decide +kernel
theorem subd11_2_178 : subd11_2 [1, 0, -3] = true := by decide +kernel
theorem subd11_2_179 : subd11_2 [1, 0, -2] = true := by decide +kernel
theorem subd11_2_180 : subd11_2 [1, 0, -1] = true := by decide +kernel
theorem subd11_2_181 : subd11_2 [1, 0, 0] = true := by decide +kernel
theorem subd11_2_182 : subd11_2 [1, 0, 1] = true := by decide +kernel
theorem subd11_2_183 : subd11_2 [1, 0, 2] = true := by decide +kernel
theorem subd11_2_184 : subd11_2 [1, 0, 3] = true := by decide +kernel
theorem subd11_2_185 : subd11_2 [1, 0, 4] = true := by decide +kernel
theorem subd11_2_186 : subd11_2 [1, 0, 5] = true := by decide +kernel
theorem subd11_2_187 : subd11_2 [1, 0, 6] = true := by decide +kernel
theorem subd11_2_188 : subd11_2 [1, 0, 7] = true := by decide +kernel
theorem subd11_2_189 : subd11_2 [1, 0, 8] = true := by decide +kernel
theorem subd11_2_190 : subd11_2 [1, 1, -8] = true := by decide +kernel
theorem subd11_2_191 : subd11_2 [1, 1, -7] = true := by decide +kernel
theorem sbd11_2_5 : ∀ q ∈ blkd11_2_5, subd11_2 q = true := by
  unfold blkd11_2_5
  exact List.forall_mem_cons.2 ⟨subd11_2_160, List.forall_mem_cons.2 ⟨subd11_2_161, List.forall_mem_cons.2 ⟨subd11_2_162, List.forall_mem_cons.2 ⟨subd11_2_163, List.forall_mem_cons.2 ⟨subd11_2_164, List.forall_mem_cons.2 ⟨subd11_2_165, List.forall_mem_cons.2 ⟨subd11_2_166, List.forall_mem_cons.2 ⟨subd11_2_167, List.forall_mem_cons.2 ⟨subd11_2_168, List.forall_mem_cons.2 ⟨subd11_2_169, List.forall_mem_cons.2 ⟨subd11_2_170, List.forall_mem_cons.2 ⟨subd11_2_171, List.forall_mem_cons.2 ⟨subd11_2_172, List.forall_mem_cons.2 ⟨subd11_2_173, List.forall_mem_cons.2 ⟨subd11_2_174, List.forall_mem_cons.2 ⟨subd11_2_175, List.forall_mem_cons.2 ⟨subd11_2_176, List.forall_mem_cons.2 ⟨subd11_2_177, List.forall_mem_cons.2 ⟨subd11_2_178, List.forall_mem_cons.2 ⟨subd11_2_179, List.forall_mem_cons.2 ⟨subd11_2_180, List.forall_mem_cons.2 ⟨subd11_2_181, List.forall_mem_cons.2 ⟨subd11_2_182, List.forall_mem_cons.2 ⟨subd11_2_183, List.forall_mem_cons.2 ⟨subd11_2_184, List.forall_mem_cons.2 ⟨subd11_2_185, List.forall_mem_cons.2 ⟨subd11_2_186, List.forall_mem_cons.2 ⟨subd11_2_187, List.forall_mem_cons.2 ⟨subd11_2_188, List.forall_mem_cons.2 ⟨subd11_2_189, List.forall_mem_cons.2 ⟨subd11_2_190, List.forall_mem_cons.2 ⟨subd11_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_192 : subd11_2 [1, 1, -6] = true := by decide +kernel
theorem subd11_2_193 : subd11_2 [1, 1, -5] = true := by decide +kernel
theorem subd11_2_194 : subd11_2 [1, 1, -4] = true := by decide +kernel
theorem subd11_2_195 : subd11_2 [1, 1, -3] = true := by decide +kernel
theorem subd11_2_196 : subd11_2 [1, 1, -2] = true := by decide +kernel
theorem subd11_2_197 : subd11_2 [1, 1, -1] = true := by decide +kernel
theorem subd11_2_198 : subd11_2 [1, 1, 0] = true := by decide +kernel
theorem subd11_2_199 : subd11_2 [1, 1, 1] = true := by decide +kernel
theorem subd11_2_200 : subd11_2 [1, 1, 2] = true := by decide +kernel
theorem subd11_2_201 : subd11_2 [1, 1, 3] = true := by decide +kernel
theorem subd11_2_202 : subd11_2 [1, 1, 4] = true := by decide +kernel
theorem subd11_2_203 : subd11_2 [1, 1, 5] = true := by decide +kernel
theorem subd11_2_204 : subd11_2 [1, 1, 6] = true := by decide +kernel
theorem subd11_2_205 : subd11_2 [1, 1, 7] = true := by decide +kernel
theorem subd11_2_206 : subd11_2 [1, 1, 8] = true := by decide +kernel
theorem subd11_2_207 : subd11_2 [1, 2, -6] = true := by decide +kernel
theorem subd11_2_208 : subd11_2 [1, 2, -5] = true := by decide +kernel
theorem subd11_2_209 : subd11_2 [1, 2, -4] = true := by decide +kernel
theorem subd11_2_210 : subd11_2 [1, 2, -3] = true := by decide +kernel
theorem subd11_2_211 : subd11_2 [1, 2, -2] = true := by decide +kernel
theorem subd11_2_212 : subd11_2 [1, 2, -1] = true := by decide +kernel
theorem subd11_2_213 : subd11_2 [1, 2, 0] = true := by decide +kernel
theorem subd11_2_214 : subd11_2 [1, 2, 1] = true := by decide +kernel
theorem subd11_2_215 : subd11_2 [1, 2, 2] = true := by decide +kernel
theorem subd11_2_216 : subd11_2 [1, 2, 3] = true := by decide +kernel
theorem subd11_2_217 : subd11_2 [1, 2, 4] = true := by decide +kernel
theorem subd11_2_218 : subd11_2 [1, 2, 5] = true := by decide +kernel
theorem subd11_2_219 : subd11_2 [1, 2, 6] = true := by decide +kernel
theorem subd11_2_220 : subd11_2 [1, 2, 7] = true := by decide +kernel
theorem subd11_2_221 : subd11_2 [1, 2, 8] = true := by decide +kernel
theorem subd11_2_222 : subd11_2 [1, 3] = true := by decide +kernel
theorem subd11_2_223 : subd11_2 [2, -1] = true := by decide +kernel
theorem sbd11_2_6 : ∀ q ∈ blkd11_2_6, subd11_2 q = true := by
  unfold blkd11_2_6
  exact List.forall_mem_cons.2 ⟨subd11_2_192, List.forall_mem_cons.2 ⟨subd11_2_193, List.forall_mem_cons.2 ⟨subd11_2_194, List.forall_mem_cons.2 ⟨subd11_2_195, List.forall_mem_cons.2 ⟨subd11_2_196, List.forall_mem_cons.2 ⟨subd11_2_197, List.forall_mem_cons.2 ⟨subd11_2_198, List.forall_mem_cons.2 ⟨subd11_2_199, List.forall_mem_cons.2 ⟨subd11_2_200, List.forall_mem_cons.2 ⟨subd11_2_201, List.forall_mem_cons.2 ⟨subd11_2_202, List.forall_mem_cons.2 ⟨subd11_2_203, List.forall_mem_cons.2 ⟨subd11_2_204, List.forall_mem_cons.2 ⟨subd11_2_205, List.forall_mem_cons.2 ⟨subd11_2_206, List.forall_mem_cons.2 ⟨subd11_2_207, List.forall_mem_cons.2 ⟨subd11_2_208, List.forall_mem_cons.2 ⟨subd11_2_209, List.forall_mem_cons.2 ⟨subd11_2_210, List.forall_mem_cons.2 ⟨subd11_2_211, List.forall_mem_cons.2 ⟨subd11_2_212, List.forall_mem_cons.2 ⟨subd11_2_213, List.forall_mem_cons.2 ⟨subd11_2_214, List.forall_mem_cons.2 ⟨subd11_2_215, List.forall_mem_cons.2 ⟨subd11_2_216, List.forall_mem_cons.2 ⟨subd11_2_217, List.forall_mem_cons.2 ⟨subd11_2_218, List.forall_mem_cons.2 ⟨subd11_2_219, List.forall_mem_cons.2 ⟨subd11_2_220, List.forall_mem_cons.2 ⟨subd11_2_221, List.forall_mem_cons.2 ⟨subd11_2_222, List.forall_mem_cons.2 ⟨subd11_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_224 : subd11_2 [2, 0] = true := by decide +kernel
theorem subd11_2_225 : subd11_2 [2, 1] = true := by decide +kernel
theorem subd11_2_226 : subd11_2 [2, 2] = true := by decide +kernel
theorem sbd11_2_7 : ∀ q ∈ blkd11_2_7, subd11_2 q = true := by
  unfold blkd11_2_7
  exact List.forall_mem_cons.2 ⟨subd11_2_224, List.forall_mem_cons.2 ⟨subd11_2_225, List.forall_mem_cons.2 ⟨subd11_2_226, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel
theorem subd11_3_0 : subd11_3 [-2] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-1, -2] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [-1, -1] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [-1, 0] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [-1, 1] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [-1, 2] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [0, -3] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [0, -2] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [0, -1] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [0, 0] = true := by decide +kernel
theorem subd11_3_10 : subd11_3 [0, 1] = true := by decide +kernel
theorem subd11_3_11 : subd11_3 [0, 2] = true := by decide +kernel
theorem subd11_3_12 : subd11_3 [1, -3] = true := by decide +kernel
theorem subd11_3_13 : subd11_3 [1, -2] = true := by decide +kernel
theorem subd11_3_14 : subd11_3 [1, -1] = true := by decide +kernel
theorem subd11_3_15 : subd11_3 [1, 0] = true := by decide +kernel
theorem subd11_3_16 : subd11_3 [1, 1] = true := by decide +kernel
theorem subd11_3_17 : subd11_3 [2] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_cons.2 ⟨subd11_3_10, List.forall_mem_cons.2 ⟨subd11_3_11, List.forall_mem_cons.2 ⟨subd11_3_12, List.forall_mem_cons.2 ⟨subd11_3_13, List.forall_mem_cons.2 ⟨subd11_3_14, List.forall_mem_cons.2 ⟨subd11_3_15, List.forall_mem_cons.2 ⟨subd11_3_16, List.forall_mem_cons.2 ⟨subd11_3_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [-3] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [-2, -3] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [-2, -2] = true := by decide +kernel
theorem subd12_0_3 : subd12_0 [-2, -1] = true := by decide +kernel
theorem subd12_0_4 : subd12_0 [-2, 0] = true := by decide +kernel
theorem subd12_0_5 : subd12_0 [-2, 1] = true := by decide +kernel
theorem subd12_0_6 : subd12_0 [-2, 2] = true := by decide +kernel
theorem subd12_0_7 : subd12_0 [-2, 3] = true := by decide +kernel
theorem subd12_0_8 : subd12_0 [-1, -4] = true := by decide +kernel
theorem subd12_0_9 : subd12_0 [-1, -3] = true := by decide +kernel
theorem subd12_0_10 : subd12_0 [-1, -2] = true := by decide +kernel
theorem subd12_0_11 : subd12_0 [-1, -1] = true := by decide +kernel
theorem subd12_0_12 : subd12_0 [-1, 0] = true := by decide +kernel
theorem subd12_0_13 : subd12_0 [-1, 1] = true := by decide +kernel
theorem subd12_0_14 : subd12_0 [-1, 2] = true := by decide +kernel
theorem subd12_0_15 : subd12_0 [-1, 3] = true := by decide +kernel
theorem subd12_0_16 : subd12_0 [0, -4] = true := by decide +kernel
theorem subd12_0_17 : subd12_0 [0, -3] = true := by decide +kernel
theorem subd12_0_18 : subd12_0 [0, -2] = true := by decide +kernel
theorem subd12_0_19 : subd12_0 [0, -1] = true := by decide +kernel
theorem subd12_0_20 : subd12_0 [0, 0] = true := by decide +kernel
theorem subd12_0_21 : subd12_0 [0, 1] = true := by decide +kernel
theorem subd12_0_22 : subd12_0 [0, 2] = true := by decide +kernel
theorem subd12_0_23 : subd12_0 [0, 3] = true := by decide +kernel
theorem subd12_0_24 : subd12_0 [1, -4] = true := by decide +kernel
theorem subd12_0_25 : subd12_0 [1, -3] = true := by decide +kernel
theorem subd12_0_26 : subd12_0 [1, -2] = true := by decide +kernel
theorem subd12_0_27 : subd12_0 [1, -1] = true := by decide +kernel
theorem subd12_0_28 : subd12_0 [1, 0] = true := by decide +kernel
theorem subd12_0_29 : subd12_0 [1, 1] = true := by decide +kernel
theorem subd12_0_30 : subd12_0 [1, 2] = true := by decide +kernel
theorem subd12_0_31 : subd12_0 [1, 3] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_cons.2 ⟨subd12_0_3, List.forall_mem_cons.2 ⟨subd12_0_4, List.forall_mem_cons.2 ⟨subd12_0_5, List.forall_mem_cons.2 ⟨subd12_0_6, List.forall_mem_cons.2 ⟨subd12_0_7, List.forall_mem_cons.2 ⟨subd12_0_8, List.forall_mem_cons.2 ⟨subd12_0_9, List.forall_mem_cons.2 ⟨subd12_0_10, List.forall_mem_cons.2 ⟨subd12_0_11, List.forall_mem_cons.2 ⟨subd12_0_12, List.forall_mem_cons.2 ⟨subd12_0_13, List.forall_mem_cons.2 ⟨subd12_0_14, List.forall_mem_cons.2 ⟨subd12_0_15, List.forall_mem_cons.2 ⟨subd12_0_16, List.forall_mem_cons.2 ⟨subd12_0_17, List.forall_mem_cons.2 ⟨subd12_0_18, List.forall_mem_cons.2 ⟨subd12_0_19, List.forall_mem_cons.2 ⟨subd12_0_20, List.forall_mem_cons.2 ⟨subd12_0_21, List.forall_mem_cons.2 ⟨subd12_0_22, List.forall_mem_cons.2 ⟨subd12_0_23, List.forall_mem_cons.2 ⟨subd12_0_24, List.forall_mem_cons.2 ⟨subd12_0_25, List.forall_mem_cons.2 ⟨subd12_0_26, List.forall_mem_cons.2 ⟨subd12_0_27, List.forall_mem_cons.2 ⟨subd12_0_28, List.forall_mem_cons.2 ⟨subd12_0_29, List.forall_mem_cons.2 ⟨subd12_0_30, List.forall_mem_cons.2 ⟨subd12_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_32 : subd12_0 [2, -4] = true := by decide +kernel
theorem subd12_0_33 : subd12_0 [2, -3] = true := by decide +kernel
theorem subd12_0_34 : subd12_0 [2, -2] = true := by decide +kernel
theorem subd12_0_35 : subd12_0 [2, -1] = true := by decide +kernel
theorem subd12_0_36 : subd12_0 [2, 0] = true := by decide +kernel
theorem subd12_0_37 : subd12_0 [2, 1] = true := by decide +kernel
theorem subd12_0_38 : subd12_0 [2, 2] = true := by decide +kernel
theorem subd12_0_39 : subd12_0 [3] = true := by decide +kernel
theorem sbd12_0_1 : ∀ q ∈ blkd12_0_1, subd12_0 q = true := by
  unfold blkd12_0_1
  exact List.forall_mem_cons.2 ⟨subd12_0_32, List.forall_mem_cons.2 ⟨subd12_0_33, List.forall_mem_cons.2 ⟨subd12_0_34, List.forall_mem_cons.2 ⟨subd12_0_35, List.forall_mem_cons.2 ⟨subd12_0_36, List.forall_mem_cons.2 ⟨subd12_0_37, List.forall_mem_cons.2 ⟨subd12_0_38, List.forall_mem_cons.2 ⟨subd12_0_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [-2] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [-1] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [0] = true := by decide +kernel
theorem subd12_1_3 : subd12_1 [1] = true := by decide +kernel
theorem subd12_1_4 : subd12_1 [2] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_cons.2 ⟨subd12_1_3, List.forall_mem_cons.2 ⟨subd12_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_2 : ldCheck G d12_2.U d12_2.ms ldd12_2 = true := by decide +kernel
theorem pre_okd12_2 : subPre G cell12 d12_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C141
