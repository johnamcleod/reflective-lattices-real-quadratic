import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_5_128 : subd8_5 [0, 0, 1] = true := by decide +kernel
theorem subd8_5_129 : subd8_5 [0, 0, 2] = true := by decide +kernel
theorem subd8_5_130 : subd8_5 [0, 0, 3] = true := by decide +kernel
theorem subd8_5_131 : subd8_5 [0, 0, 4] = true := by decide +kernel
theorem subd8_5_132 : subd8_5 [0, 0, 5] = true := by decide +kernel
theorem subd8_5_133 : subd8_5 [0, 0, 6] = true := by decide +kernel
theorem subd8_5_134 : subd8_5 [0, 0, 7] = true := by decide +kernel
theorem subd8_5_135 : subd8_5 [0, 0, 8] = true := by decide +kernel
theorem subd8_5_136 : subd8_5 [0, 0, 9] = true := by decide +kernel
theorem subd8_5_137 : subd8_5 [0, 0, 10] = true := by decide +kernel
theorem subd8_5_138 : subd8_5 [0, 0, 11] = true := by decide +kernel
theorem subd8_5_139 : subd8_5 [0, 0, 12] = true := by decide +kernel
theorem subd8_5_140 : subd8_5 [0, 0, 13] = true := by decide +kernel
theorem subd8_5_141 : subd8_5 [0, 0, 14] = true := by decide +kernel
theorem subd8_5_142 : subd8_5 [0, 0, 15] = true := by decide +kernel
theorem subd8_5_143 : subd8_5 [0, 0, 16] = true := by decide +kernel
theorem subd8_5_144 : subd8_5 [0, 0, 17] = true := by decide +kernel
theorem subd8_5_145 : subd8_5 [0, 1, -16] = true := by decide +kernel
theorem subd8_5_146 : subd8_5 [0, 1, -15] = true := by decide +kernel
theorem subd8_5_147 : subd8_5 [0, 1, -14] = true := by decide +kernel
theorem subd8_5_148 : subd8_5 [0, 1, -13] = true := by decide +kernel
theorem subd8_5_149 : subd8_5 [0, 1, -12] = true := by decide +kernel
theorem subd8_5_150 : subd8_5 [0, 1, -11] = true := by decide +kernel
theorem subd8_5_151 : subd8_5 [0, 1, -10] = true := by decide +kernel
theorem subd8_5_152 : subd8_5 [0, 1, -9] = true := by decide +kernel
theorem subd8_5_153 : subd8_5 [0, 1, -8] = true := by decide +kernel
theorem subd8_5_154 : subd8_5 [0, 1, -7] = true := by decide +kernel
theorem subd8_5_155 : subd8_5 [0, 1, -6] = true := by decide +kernel
theorem subd8_5_156 : subd8_5 [0, 1, -5] = true := by decide +kernel
theorem subd8_5_157 : subd8_5 [0, 1, -4] = true := by decide +kernel
theorem subd8_5_158 : subd8_5 [0, 1, -3] = true := by decide +kernel
theorem subd8_5_159 : subd8_5 [0, 1, -2] = true := by decide +kernel
theorem sbd8_5_4 : ∀ q ∈ blkd8_5_4, subd8_5 q = true := by
  unfold blkd8_5_4
  exact List.forall_mem_cons.2 ⟨subd8_5_128, List.forall_mem_cons.2 ⟨subd8_5_129, List.forall_mem_cons.2 ⟨subd8_5_130, List.forall_mem_cons.2 ⟨subd8_5_131, List.forall_mem_cons.2 ⟨subd8_5_132, List.forall_mem_cons.2 ⟨subd8_5_133, List.forall_mem_cons.2 ⟨subd8_5_134, List.forall_mem_cons.2 ⟨subd8_5_135, List.forall_mem_cons.2 ⟨subd8_5_136, List.forall_mem_cons.2 ⟨subd8_5_137, List.forall_mem_cons.2 ⟨subd8_5_138, List.forall_mem_cons.2 ⟨subd8_5_139, List.forall_mem_cons.2 ⟨subd8_5_140, List.forall_mem_cons.2 ⟨subd8_5_141, List.forall_mem_cons.2 ⟨subd8_5_142, List.forall_mem_cons.2 ⟨subd8_5_143, List.forall_mem_cons.2 ⟨subd8_5_144, List.forall_mem_cons.2 ⟨subd8_5_145, List.forall_mem_cons.2 ⟨subd8_5_146, List.forall_mem_cons.2 ⟨subd8_5_147, List.forall_mem_cons.2 ⟨subd8_5_148, List.forall_mem_cons.2 ⟨subd8_5_149, List.forall_mem_cons.2 ⟨subd8_5_150, List.forall_mem_cons.2 ⟨subd8_5_151, List.forall_mem_cons.2 ⟨subd8_5_152, List.forall_mem_cons.2 ⟨subd8_5_153, List.forall_mem_cons.2 ⟨subd8_5_154, List.forall_mem_cons.2 ⟨subd8_5_155, List.forall_mem_cons.2 ⟨subd8_5_156, List.forall_mem_cons.2 ⟨subd8_5_157, List.forall_mem_cons.2 ⟨subd8_5_158, List.forall_mem_cons.2 ⟨subd8_5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_160 : subd8_5 [0, 1, -1] = true := by decide +kernel
theorem subd8_5_161 : subd8_5 [0, 1, 0] = true := by decide +kernel
theorem subd8_5_162 : subd8_5 [0, 1, 1] = true := by decide +kernel
theorem subd8_5_163 : subd8_5 [0, 1, 2] = true := by decide +kernel
theorem subd8_5_164 : subd8_5 [0, 1, 3] = true := by decide +kernel
theorem subd8_5_165 : subd8_5 [0, 1, 4] = true := by decide +kernel
theorem subd8_5_166 : subd8_5 [0, 1, 5] = true := by decide +kernel
theorem subd8_5_167 : subd8_5 [0, 1, 6] = true := by decide +kernel
theorem subd8_5_168 : subd8_5 [0, 1, 7] = true := by decide +kernel
theorem subd8_5_169 : subd8_5 [0, 1, 8] = true := by decide +kernel
theorem subd8_5_170 : subd8_5 [0, 1, 9] = true := by decide +kernel
theorem subd8_5_171 : subd8_5 [0, 1, 10] = true := by decide +kernel
theorem subd8_5_172 : subd8_5 [0, 1, 11] = true := by decide +kernel
theorem subd8_5_173 : subd8_5 [0, 1, 12] = true := by decide +kernel
theorem subd8_5_174 : subd8_5 [0, 1, 13] = true := by decide +kernel
theorem subd8_5_175 : subd8_5 [0, 1, 14] = true := by decide +kernel
theorem subd8_5_176 : subd8_5 [0, 1, 15] = true := by decide +kernel
theorem subd8_5_177 : subd8_5 [1, -2] = true := by decide +kernel
theorem subd8_5_178 : subd8_5 [1, -1, -14] = true := by decide +kernel
theorem subd8_5_179 : subd8_5 [1, -1, -13] = true := by decide +kernel
theorem subd8_5_180 : subd8_5 [1, -1, -12] = true := by decide +kernel
theorem subd8_5_181 : subd8_5 [1, -1, -11] = true := by decide +kernel
theorem subd8_5_182 : subd8_5 [1, -1, -10] = true := by decide +kernel
theorem subd8_5_183 : subd8_5 [1, -1, -9] = true := by decide +kernel
theorem subd8_5_184 : subd8_5 [1, -1, -8] = true := by decide +kernel
theorem subd8_5_185 : subd8_5 [1, -1, -7] = true := by decide +kernel
theorem subd8_5_186 : subd8_5 [1, -1, -6] = true := by decide +kernel
theorem subd8_5_187 : subd8_5 [1, -1, -5] = true := by decide +kernel
theorem subd8_5_188 : subd8_5 [1, -1, -4] = true := by decide +kernel
theorem subd8_5_189 : subd8_5 [1, -1, -3] = true := by decide +kernel
theorem subd8_5_190 : subd8_5 [1, -1, -2] = true := by decide +kernel
theorem subd8_5_191 : subd8_5 [1, -1, -1] = true := by decide +kernel
theorem sbd8_5_5 : ∀ q ∈ blkd8_5_5, subd8_5 q = true := by
  unfold blkd8_5_5
  exact List.forall_mem_cons.2 ⟨subd8_5_160, List.forall_mem_cons.2 ⟨subd8_5_161, List.forall_mem_cons.2 ⟨subd8_5_162, List.forall_mem_cons.2 ⟨subd8_5_163, List.forall_mem_cons.2 ⟨subd8_5_164, List.forall_mem_cons.2 ⟨subd8_5_165, List.forall_mem_cons.2 ⟨subd8_5_166, List.forall_mem_cons.2 ⟨subd8_5_167, List.forall_mem_cons.2 ⟨subd8_5_168, List.forall_mem_cons.2 ⟨subd8_5_169, List.forall_mem_cons.2 ⟨subd8_5_170, List.forall_mem_cons.2 ⟨subd8_5_171, List.forall_mem_cons.2 ⟨subd8_5_172, List.forall_mem_cons.2 ⟨subd8_5_173, List.forall_mem_cons.2 ⟨subd8_5_174, List.forall_mem_cons.2 ⟨subd8_5_175, List.forall_mem_cons.2 ⟨subd8_5_176, List.forall_mem_cons.2 ⟨subd8_5_177, List.forall_mem_cons.2 ⟨subd8_5_178, List.forall_mem_cons.2 ⟨subd8_5_179, List.forall_mem_cons.2 ⟨subd8_5_180, List.forall_mem_cons.2 ⟨subd8_5_181, List.forall_mem_cons.2 ⟨subd8_5_182, List.forall_mem_cons.2 ⟨subd8_5_183, List.forall_mem_cons.2 ⟨subd8_5_184, List.forall_mem_cons.2 ⟨subd8_5_185, List.forall_mem_cons.2 ⟨subd8_5_186, List.forall_mem_cons.2 ⟨subd8_5_187, List.forall_mem_cons.2 ⟨subd8_5_188, List.forall_mem_cons.2 ⟨subd8_5_189, List.forall_mem_cons.2 ⟨subd8_5_190, List.forall_mem_cons.2 ⟨subd8_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_192 : subd8_5 [1, -1, 0] = true := by decide +kernel
theorem subd8_5_193 : subd8_5 [1, -1, 1] = true := by decide +kernel
theorem subd8_5_194 : subd8_5 [1, -1, 2] = true := by decide +kernel
theorem subd8_5_195 : subd8_5 [1, -1, 3] = true := by decide +kernel
theorem subd8_5_196 : subd8_5 [1, -1, 4] = true := by decide +kernel
theorem subd8_5_197 : subd8_5 [1, -1, 5] = true := by decide +kernel
theorem subd8_5_198 : subd8_5 [1, -1, 6] = true := by decide +kernel
theorem subd8_5_199 : subd8_5 [1, -1, 7] = true := by decide +kernel
theorem subd8_5_200 : subd8_5 [1, -1, 8] = true := by decide +kernel
theorem subd8_5_201 : subd8_5 [1, -1, 9] = true := by decide +kernel
theorem subd8_5_202 : subd8_5 [1, -1, 10] = true := by decide +kernel
theorem subd8_5_203 : subd8_5 [1, -1, 11] = true := by decide +kernel
theorem subd8_5_204 : subd8_5 [1, -1, 12] = true := by decide +kernel
theorem subd8_5_205 : subd8_5 [1, -1, 13] = true := by decide +kernel
theorem subd8_5_206 : subd8_5 [1, 0, -15] = true := by decide +kernel
theorem subd8_5_207 : subd8_5 [1, 0, -14] = true := by decide +kernel
theorem subd8_5_208 : subd8_5 [1, 0, -13] = true := by decide +kernel
theorem subd8_5_209 : subd8_5 [1, 0, -12] = true := by decide +kernel
theorem subd8_5_210 : subd8_5 [1, 0, -11] = true := by decide +kernel
theorem subd8_5_211 : subd8_5 [1, 0, -10] = true := by decide +kernel
theorem subd8_5_212 : subd8_5 [1, 0, -9] = true := by decide +kernel
theorem subd8_5_213 : subd8_5 [1, 0, -8] = true := by decide +kernel
theorem subd8_5_214 : subd8_5 [1, 0, -7] = true := by decide +kernel
theorem subd8_5_215 : subd8_5 [1, 0, -6] = true := by decide +kernel
theorem subd8_5_216 : subd8_5 [1, 0, -5] = true := by decide +kernel
theorem subd8_5_217 : subd8_5 [1, 0, -4] = true := by decide +kernel
theorem subd8_5_218 : subd8_5 [1, 0, -3] = true := by decide +kernel
theorem subd8_5_219 : subd8_5 [1, 0, -2] = true := by decide +kernel
theorem subd8_5_220 : subd8_5 [1, 0, -1] = true := by decide +kernel
theorem subd8_5_221 : subd8_5 [1, 0, 0] = true := by decide +kernel
theorem subd8_5_222 : subd8_5 [1, 0, 1] = true := by decide +kernel
theorem subd8_5_223 : subd8_5 [1, 0, 2] = true := by decide +kernel
theorem sbd8_5_6 : ∀ q ∈ blkd8_5_6, subd8_5 q = true := by
  unfold blkd8_5_6
  exact List.forall_mem_cons.2 ⟨subd8_5_192, List.forall_mem_cons.2 ⟨subd8_5_193, List.forall_mem_cons.2 ⟨subd8_5_194, List.forall_mem_cons.2 ⟨subd8_5_195, List.forall_mem_cons.2 ⟨subd8_5_196, List.forall_mem_cons.2 ⟨subd8_5_197, List.forall_mem_cons.2 ⟨subd8_5_198, List.forall_mem_cons.2 ⟨subd8_5_199, List.forall_mem_cons.2 ⟨subd8_5_200, List.forall_mem_cons.2 ⟨subd8_5_201, List.forall_mem_cons.2 ⟨subd8_5_202, List.forall_mem_cons.2 ⟨subd8_5_203, List.forall_mem_cons.2 ⟨subd8_5_204, List.forall_mem_cons.2 ⟨subd8_5_205, List.forall_mem_cons.2 ⟨subd8_5_206, List.forall_mem_cons.2 ⟨subd8_5_207, List.forall_mem_cons.2 ⟨subd8_5_208, List.forall_mem_cons.2 ⟨subd8_5_209, List.forall_mem_cons.2 ⟨subd8_5_210, List.forall_mem_cons.2 ⟨subd8_5_211, List.forall_mem_cons.2 ⟨subd8_5_212, List.forall_mem_cons.2 ⟨subd8_5_213, List.forall_mem_cons.2 ⟨subd8_5_214, List.forall_mem_cons.2 ⟨subd8_5_215, List.forall_mem_cons.2 ⟨subd8_5_216, List.forall_mem_cons.2 ⟨subd8_5_217, List.forall_mem_cons.2 ⟨subd8_5_218, List.forall_mem_cons.2 ⟨subd8_5_219, List.forall_mem_cons.2 ⟨subd8_5_220, List.forall_mem_cons.2 ⟨subd8_5_221, List.forall_mem_cons.2 ⟨subd8_5_222, List.forall_mem_cons.2 ⟨subd8_5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_224 : subd8_5 [1, 0, 3] = true := by decide +kernel
theorem subd8_5_225 : subd8_5 [1, 0, 4] = true := by decide +kernel
theorem subd8_5_226 : subd8_5 [1, 0, 5] = true := by decide +kernel
theorem subd8_5_227 : subd8_5 [1, 0, 6] = true := by decide +kernel
theorem subd8_5_228 : subd8_5 [1, 0, 7] = true := by decide +kernel
theorem subd8_5_229 : subd8_5 [1, 0, 8] = true := by decide +kernel
theorem subd8_5_230 : subd8_5 [1, 0, 9] = true := by decide +kernel
theorem subd8_5_231 : subd8_5 [1, 0, 10] = true := by decide +kernel
theorem subd8_5_232 : subd8_5 [1, 0, 11] = true := by decide +kernel
theorem subd8_5_233 : subd8_5 [1, 0, 12] = true := by decide +kernel
theorem subd8_5_234 : subd8_5 [1, 0, 13] = true := by decide +kernel
theorem subd8_5_235 : subd8_5 [1, 0, 14] = true := by decide +kernel
theorem subd8_5_236 : subd8_5 [1, 1, -9] = true := by decide +kernel
theorem subd8_5_237 : subd8_5 [1, 1, -8] = true := by decide +kernel
theorem subd8_5_238 : subd8_5 [1, 1, -7] = true := by decide +kernel
theorem subd8_5_239 : subd8_5 [1, 1, -6] = true := by decide +kernel
theorem subd8_5_240 : subd8_5 [1, 1, -5] = true := by decide +kernel
theorem subd8_5_241 : subd8_5 [1, 1, -4] = true := by decide +kernel
theorem subd8_5_242 : subd8_5 [1, 1, -3] = true := by decide +kernel
theorem subd8_5_243 : subd8_5 [1, 1, -2] = true := by decide +kernel
theorem subd8_5_244 : subd8_5 [1, 1, -1] = true := by decide +kernel
theorem subd8_5_245 : subd8_5 [1, 1, 0] = true := by decide +kernel
theorem subd8_5_246 : subd8_5 [1, 1, 1] = true := by decide +kernel
theorem subd8_5_247 : subd8_5 [1, 1, 2] = true := by decide +kernel
theorem subd8_5_248 : subd8_5 [1, 1, 3] = true := by decide +kernel
theorem subd8_5_249 : subd8_5 [1, 1, 4] = true := by decide +kernel
theorem subd8_5_250 : subd8_5 [1, 1, 5] = true := by decide +kernel
theorem subd8_5_251 : subd8_5 [1, 1, 6] = true := by decide +kernel
theorem subd8_5_252 : subd8_5 [1, 1, 7] = true := by decide +kernel
theorem sbd8_5_7 : ∀ q ∈ blkd8_5_7, subd8_5 q = true := by
  unfold blkd8_5_7
  exact List.forall_mem_cons.2 ⟨subd8_5_224, List.forall_mem_cons.2 ⟨subd8_5_225, List.forall_mem_cons.2 ⟨subd8_5_226, List.forall_mem_cons.2 ⟨subd8_5_227, List.forall_mem_cons.2 ⟨subd8_5_228, List.forall_mem_cons.2 ⟨subd8_5_229, List.forall_mem_cons.2 ⟨subd8_5_230, List.forall_mem_cons.2 ⟨subd8_5_231, List.forall_mem_cons.2 ⟨subd8_5_232, List.forall_mem_cons.2 ⟨subd8_5_233, List.forall_mem_cons.2 ⟨subd8_5_234, List.forall_mem_cons.2 ⟨subd8_5_235, List.forall_mem_cons.2 ⟨subd8_5_236, List.forall_mem_cons.2 ⟨subd8_5_237, List.forall_mem_cons.2 ⟨subd8_5_238, List.forall_mem_cons.2 ⟨subd8_5_239, List.forall_mem_cons.2 ⟨subd8_5_240, List.forall_mem_cons.2 ⟨subd8_5_241, List.forall_mem_cons.2 ⟨subd8_5_242, List.forall_mem_cons.2 ⟨subd8_5_243, List.forall_mem_cons.2 ⟨subd8_5_244, List.forall_mem_cons.2 ⟨subd8_5_245, List.forall_mem_cons.2 ⟨subd8_5_246, List.forall_mem_cons.2 ⟨subd8_5_247, List.forall_mem_cons.2 ⟨subd8_5_248, List.forall_mem_cons.2 ⟨subd8_5_249, List.forall_mem_cons.2 ⟨subd8_5_250, List.forall_mem_cons.2 ⟨subd8_5_251, List.forall_mem_cons.2 ⟨subd8_5_252, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_6 : ldCheck G d8_6.U d8_6.ms ldd8_6 = true := by decide +kernel
theorem pre_okd8_6 : subPre G cell8 d8_6 = true := by decide +kernel
theorem subd8_6_0 : subd8_6 [-5] = true := by decide +kernel
theorem subd8_6_1 : subd8_6 [-4, -3] = true := by decide +kernel
theorem subd8_6_2 : subd8_6 [-4, -2] = true := by decide +kernel
theorem subd8_6_3 : subd8_6 [-4, -1] = true := by decide +kernel
theorem subd8_6_4 : subd8_6 [-4, 0] = true := by decide +kernel
theorem subd8_6_5 : subd8_6 [-4, 1] = true := by decide +kernel
theorem subd8_6_6 : subd8_6 [-4, 2] = true := by decide +kernel
theorem subd8_6_7 : subd8_6 [-4, 3] = true := by decide +kernel
theorem subd8_6_8 : subd8_6 [-3, -4] = true := by decide +kernel
theorem subd8_6_9 : subd8_6 [-3, -3] = true := by decide +kernel
theorem subd8_6_10 : subd8_6 [-3, -2] = true := by decide +kernel
theorem subd8_6_11 : subd8_6 [-3, -1] = true := by decide +kernel
theorem subd8_6_12 : subd8_6 [-3, 0] = true := by decide +kernel
theorem subd8_6_13 : subd8_6 [-3, 1] = true := by decide +kernel
theorem subd8_6_14 : subd8_6 [-3, 2] = true := by decide +kernel
theorem subd8_6_15 : subd8_6 [-3, 3] = true := by decide +kernel
theorem subd8_6_16 : subd8_6 [-3, 4] = true := by decide +kernel
theorem subd8_6_17 : subd8_6 [-2, -5] = true := by decide +kernel
theorem subd8_6_18 : subd8_6 [-2, -4] = true := by decide +kernel
theorem subd8_6_19 : subd8_6 [-2, -3] = true := by decide +kernel
theorem subd8_6_20 : subd8_6 [-2, -2] = true := by decide +kernel
theorem subd8_6_21 : subd8_6 [-2, -1] = true := by decide +kernel
theorem subd8_6_22 : subd8_6 [-2, 0] = true := by decide +kernel
theorem subd8_6_23 : subd8_6 [-2, 1] = true := by decide +kernel
theorem subd8_6_24 : subd8_6 [-2, 2] = true := by decide +kernel
theorem subd8_6_25 : subd8_6 [-2, 3] = true := by decide +kernel
theorem subd8_6_26 : subd8_6 [-2, 4] = true := by decide +kernel
theorem subd8_6_27 : subd8_6 [-1, -5] = true := by decide +kernel
theorem subd8_6_28 : subd8_6 [-1, -4] = true := by decide +kernel
theorem subd8_6_29 : subd8_6 [-1, -3] = true := by decide +kernel
theorem subd8_6_30 : subd8_6 [-1, -2] = true := by decide +kernel
theorem subd8_6_31 : subd8_6 [-1, -1] = true := by decide +kernel
theorem sbd8_6_0 : ∀ q ∈ blkd8_6_0, subd8_6 q = true := by
  unfold blkd8_6_0
  exact List.forall_mem_cons.2 ⟨subd8_6_0, List.forall_mem_cons.2 ⟨subd8_6_1, List.forall_mem_cons.2 ⟨subd8_6_2, List.forall_mem_cons.2 ⟨subd8_6_3, List.forall_mem_cons.2 ⟨subd8_6_4, List.forall_mem_cons.2 ⟨subd8_6_5, List.forall_mem_cons.2 ⟨subd8_6_6, List.forall_mem_cons.2 ⟨subd8_6_7, List.forall_mem_cons.2 ⟨subd8_6_8, List.forall_mem_cons.2 ⟨subd8_6_9, List.forall_mem_cons.2 ⟨subd8_6_10, List.forall_mem_cons.2 ⟨subd8_6_11, List.forall_mem_cons.2 ⟨subd8_6_12, List.forall_mem_cons.2 ⟨subd8_6_13, List.forall_mem_cons.2 ⟨subd8_6_14, List.forall_mem_cons.2 ⟨subd8_6_15, List.forall_mem_cons.2 ⟨subd8_6_16, List.forall_mem_cons.2 ⟨subd8_6_17, List.forall_mem_cons.2 ⟨subd8_6_18, List.forall_mem_cons.2 ⟨subd8_6_19, List.forall_mem_cons.2 ⟨subd8_6_20, List.forall_mem_cons.2 ⟨subd8_6_21, List.forall_mem_cons.2 ⟨subd8_6_22, List.forall_mem_cons.2 ⟨subd8_6_23, List.forall_mem_cons.2 ⟨subd8_6_24, List.forall_mem_cons.2 ⟨subd8_6_25, List.forall_mem_cons.2 ⟨subd8_6_26, List.forall_mem_cons.2 ⟨subd8_6_27, List.forall_mem_cons.2 ⟨subd8_6_28, List.forall_mem_cons.2 ⟨subd8_6_29, List.forall_mem_cons.2 ⟨subd8_6_30, List.forall_mem_cons.2 ⟨subd8_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
