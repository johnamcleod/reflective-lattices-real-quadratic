import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_8_128 : subd8_8 [0, 0, -3] = true := by decide +kernel
theorem subd8_8_129 : subd8_8 [0, 0, -2] = true := by decide +kernel
theorem subd8_8_130 : subd8_8 [0, 0, -1] = true := by decide +kernel
theorem subd8_8_131 : subd8_8 [0, 0, 0] = true := by decide +kernel
theorem subd8_8_132 : subd8_8 [0, 0, 1] = true := by decide +kernel
theorem subd8_8_133 : subd8_8 [0, 0, 2] = true := by decide +kernel
theorem subd8_8_134 : subd8_8 [0, 0, 3] = true := by decide +kernel
theorem subd8_8_135 : subd8_8 [0, 0, 4] = true := by decide +kernel
theorem subd8_8_136 : subd8_8 [0, 0, 5] = true := by decide +kernel
theorem subd8_8_137 : subd8_8 [0, 0, 6] = true := by decide +kernel
theorem subd8_8_138 : subd8_8 [0, 0, 7] = true := by decide +kernel
theorem subd8_8_139 : subd8_8 [0, 0, 8] = true := by decide +kernel
theorem subd8_8_140 : subd8_8 [0, 0, 9] = true := by decide +kernel
theorem subd8_8_141 : subd8_8 [0, 0, 10] = true := by decide +kernel
theorem subd8_8_142 : subd8_8 [0, 0, 11] = true := by decide +kernel
theorem subd8_8_143 : subd8_8 [0, 0, 12] = true := by decide +kernel
theorem subd8_8_144 : subd8_8 [0, 0, 13] = true := by decide +kernel
theorem subd8_8_145 : subd8_8 [0, 0, 14] = true := by decide +kernel
theorem subd8_8_146 : subd8_8 [0, 0, 15] = true := by decide +kernel
theorem subd8_8_147 : subd8_8 [0, 0, 16] = true := by decide +kernel
theorem subd8_8_148 : subd8_8 [0, 0, 17] = true := by decide +kernel
theorem subd8_8_149 : subd8_8 [0, 0, 18] = true := by decide +kernel
theorem subd8_8_150 : subd8_8 [0, 0, 19] = true := by decide +kernel
theorem subd8_8_151 : subd8_8 [0, 0, 20] = true := by decide +kernel
theorem subd8_8_152 : subd8_8 [0, 0, 21] = true := by decide +kernel
theorem subd8_8_153 : subd8_8 [0, 0, 22] = true := by decide +kernel
theorem subd8_8_154 : subd8_8 [0, 0, 23] = true := by decide +kernel
theorem subd8_8_155 : subd8_8 [0, 0, 24] = true := by decide +kernel
theorem subd8_8_156 : subd8_8 [0, 0, 25] = true := by decide +kernel
theorem subd8_8_157 : subd8_8 [0, 0, 26] = true := by decide +kernel
theorem subd8_8_158 : subd8_8 [0, 0, 27] = true := by decide +kernel
theorem subd8_8_159 : subd8_8 [0, 0, 28] = true := by decide +kernel
theorem sbd8_8_4 : ∀ q ∈ blkd8_8_4, subd8_8 q = true := by
  unfold blkd8_8_4
  exact List.forall_mem_cons.2 ⟨subd8_8_128, List.forall_mem_cons.2 ⟨subd8_8_129, List.forall_mem_cons.2 ⟨subd8_8_130, List.forall_mem_cons.2 ⟨subd8_8_131, List.forall_mem_cons.2 ⟨subd8_8_132, List.forall_mem_cons.2 ⟨subd8_8_133, List.forall_mem_cons.2 ⟨subd8_8_134, List.forall_mem_cons.2 ⟨subd8_8_135, List.forall_mem_cons.2 ⟨subd8_8_136, List.forall_mem_cons.2 ⟨subd8_8_137, List.forall_mem_cons.2 ⟨subd8_8_138, List.forall_mem_cons.2 ⟨subd8_8_139, List.forall_mem_cons.2 ⟨subd8_8_140, List.forall_mem_cons.2 ⟨subd8_8_141, List.forall_mem_cons.2 ⟨subd8_8_142, List.forall_mem_cons.2 ⟨subd8_8_143, List.forall_mem_cons.2 ⟨subd8_8_144, List.forall_mem_cons.2 ⟨subd8_8_145, List.forall_mem_cons.2 ⟨subd8_8_146, List.forall_mem_cons.2 ⟨subd8_8_147, List.forall_mem_cons.2 ⟨subd8_8_148, List.forall_mem_cons.2 ⟨subd8_8_149, List.forall_mem_cons.2 ⟨subd8_8_150, List.forall_mem_cons.2 ⟨subd8_8_151, List.forall_mem_cons.2 ⟨subd8_8_152, List.forall_mem_cons.2 ⟨subd8_8_153, List.forall_mem_cons.2 ⟨subd8_8_154, List.forall_mem_cons.2 ⟨subd8_8_155, List.forall_mem_cons.2 ⟨subd8_8_156, List.forall_mem_cons.2 ⟨subd8_8_157, List.forall_mem_cons.2 ⟨subd8_8_158, List.forall_mem_cons.2 ⟨subd8_8_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_8_160 : subd8_8 [0, 0, 29] = true := by decide +kernel
theorem subd8_8_161 : subd8_8 [0, 0, 30] = true := by decide +kernel
theorem subd8_8_162 : subd8_8 [0, 1, -21] = true := by decide +kernel
theorem subd8_8_163 : subd8_8 [0, 1, -20] = true := by decide +kernel
theorem subd8_8_164 : subd8_8 [0, 1, -19] = true := by decide +kernel
theorem subd8_8_165 : subd8_8 [0, 1, -18] = true := by decide +kernel
theorem subd8_8_166 : subd8_8 [0, 1, -17] = true := by decide +kernel
theorem subd8_8_167 : subd8_8 [0, 1, -16] = true := by decide +kernel
theorem subd8_8_168 : subd8_8 [0, 1, -15] = true := by decide +kernel
theorem subd8_8_169 : subd8_8 [0, 1, -14] = true := by decide +kernel
theorem subd8_8_170 : subd8_8 [0, 1, -13] = true := by decide +kernel
theorem subd8_8_171 : subd8_8 [0, 1, -12] = true := by decide +kernel
theorem subd8_8_172 : subd8_8 [0, 1, -11] = true := by decide +kernel
theorem subd8_8_173 : subd8_8 [0, 1, -10] = true := by decide +kernel
theorem subd8_8_174 : subd8_8 [0, 1, -9] = true := by decide +kernel
theorem subd8_8_175 : subd8_8 [0, 1, -8] = true := by decide +kernel
theorem subd8_8_176 : subd8_8 [0, 1, -7] = true := by decide +kernel
theorem subd8_8_177 : subd8_8 [0, 1, -6] = true := by decide +kernel
theorem subd8_8_178 : subd8_8 [0, 1, -5] = true := by decide +kernel
theorem subd8_8_179 : subd8_8 [0, 1, -4] = true := by decide +kernel
theorem subd8_8_180 : subd8_8 [0, 1, -3] = true := by decide +kernel
theorem subd8_8_181 : subd8_8 [0, 1, -2] = true := by decide +kernel
theorem subd8_8_182 : subd8_8 [0, 1, -1] = true := by decide +kernel
theorem subd8_8_183 : subd8_8 [0, 1, 0] = true := by decide +kernel
theorem subd8_8_184 : subd8_8 [0, 1, 1] = true := by decide +kernel
theorem subd8_8_185 : subd8_8 [0, 1, 2] = true := by decide +kernel
theorem subd8_8_186 : subd8_8 [0, 1, 3] = true := by decide +kernel
theorem subd8_8_187 : subd8_8 [0, 1, 4] = true := by decide +kernel
theorem subd8_8_188 : subd8_8 [0, 1, 5] = true := by decide +kernel
theorem subd8_8_189 : subd8_8 [0, 1, 6] = true := by decide +kernel
theorem subd8_8_190 : subd8_8 [0, 1, 7] = true := by decide +kernel
theorem subd8_8_191 : subd8_8 [0, 1, 8] = true := by decide +kernel
theorem sbd8_8_5 : ∀ q ∈ blkd8_8_5, subd8_8 q = true := by
  unfold blkd8_8_5
  exact List.forall_mem_cons.2 ⟨subd8_8_160, List.forall_mem_cons.2 ⟨subd8_8_161, List.forall_mem_cons.2 ⟨subd8_8_162, List.forall_mem_cons.2 ⟨subd8_8_163, List.forall_mem_cons.2 ⟨subd8_8_164, List.forall_mem_cons.2 ⟨subd8_8_165, List.forall_mem_cons.2 ⟨subd8_8_166, List.forall_mem_cons.2 ⟨subd8_8_167, List.forall_mem_cons.2 ⟨subd8_8_168, List.forall_mem_cons.2 ⟨subd8_8_169, List.forall_mem_cons.2 ⟨subd8_8_170, List.forall_mem_cons.2 ⟨subd8_8_171, List.forall_mem_cons.2 ⟨subd8_8_172, List.forall_mem_cons.2 ⟨subd8_8_173, List.forall_mem_cons.2 ⟨subd8_8_174, List.forall_mem_cons.2 ⟨subd8_8_175, List.forall_mem_cons.2 ⟨subd8_8_176, List.forall_mem_cons.2 ⟨subd8_8_177, List.forall_mem_cons.2 ⟨subd8_8_178, List.forall_mem_cons.2 ⟨subd8_8_179, List.forall_mem_cons.2 ⟨subd8_8_180, List.forall_mem_cons.2 ⟨subd8_8_181, List.forall_mem_cons.2 ⟨subd8_8_182, List.forall_mem_cons.2 ⟨subd8_8_183, List.forall_mem_cons.2 ⟨subd8_8_184, List.forall_mem_cons.2 ⟨subd8_8_185, List.forall_mem_cons.2 ⟨subd8_8_186, List.forall_mem_cons.2 ⟨subd8_8_187, List.forall_mem_cons.2 ⟨subd8_8_188, List.forall_mem_cons.2 ⟨subd8_8_189, List.forall_mem_cons.2 ⟨subd8_8_190, List.forall_mem_cons.2 ⟨subd8_8_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_8_192 : subd8_8 [0, 1, 9] = true := by decide +kernel
theorem subd8_8_193 : subd8_8 [0, 1, 10] = true := by decide +kernel
theorem subd8_8_194 : subd8_8 [0, 1, 11] = true := by decide +kernel
theorem subd8_8_195 : subd8_8 [0, 1, 12] = true := by decide +kernel
theorem subd8_8_196 : subd8_8 [0, 1, 13] = true := by decide +kernel
theorem subd8_8_197 : subd8_8 [0, 1, 14] = true := by decide +kernel
theorem subd8_8_198 : subd8_8 [0, 1, 15] = true := by decide +kernel
theorem subd8_8_199 : subd8_8 [0, 1, 16] = true := by decide +kernel
theorem subd8_8_200 : subd8_8 [0, 1, 17] = true := by decide +kernel
theorem subd8_8_201 : subd8_8 [0, 1, 18] = true := by decide +kernel
theorem subd8_8_202 : subd8_8 [0, 1, 19] = true := by decide +kernel
theorem subd8_8_203 : subd8_8 [0, 1, 20] = true := by decide +kernel
theorem subd8_8_204 : subd8_8 [0, 1, 21] = true := by decide +kernel
theorem subd8_8_205 : subd8_8 [1, -2] = true := by decide +kernel
theorem subd8_8_206 : subd8_8 [1, -1, -14] = true := by decide +kernel
theorem subd8_8_207 : subd8_8 [1, -1, -13] = true := by decide +kernel
theorem subd8_8_208 : subd8_8 [1, -1, -12] = true := by decide +kernel
theorem subd8_8_209 : subd8_8 [1, -1, -11] = true := by decide +kernel
theorem subd8_8_210 : subd8_8 [1, -1, -10] = true := by decide +kernel
theorem subd8_8_211 : subd8_8 [1, -1, -9] = true := by decide +kernel
theorem subd8_8_212 : subd8_8 [1, -1, -8] = true := by decide +kernel
theorem subd8_8_213 : subd8_8 [1, -1, -7] = true := by decide +kernel
theorem subd8_8_214 : subd8_8 [1, -1, -6] = true := by decide +kernel
theorem subd8_8_215 : subd8_8 [1, -1, -5] = true := by decide +kernel
theorem subd8_8_216 : subd8_8 [1, -1, -4] = true := by decide +kernel
theorem subd8_8_217 : subd8_8 [1, -1, -3] = true := by decide +kernel
theorem subd8_8_218 : subd8_8 [1, -1, -2] = true := by decide +kernel
theorem subd8_8_219 : subd8_8 [1, -1, -1] = true := by decide +kernel
theorem subd8_8_220 : subd8_8 [1, -1, 0] = true := by decide +kernel
theorem subd8_8_221 : subd8_8 [1, -1, 1] = true := by decide +kernel
theorem subd8_8_222 : subd8_8 [1, -1, 2] = true := by decide +kernel
theorem subd8_8_223 : subd8_8 [1, -1, 3] = true := by decide +kernel
theorem sbd8_8_6 : ∀ q ∈ blkd8_8_6, subd8_8 q = true := by
  unfold blkd8_8_6
  exact List.forall_mem_cons.2 ⟨subd8_8_192, List.forall_mem_cons.2 ⟨subd8_8_193, List.forall_mem_cons.2 ⟨subd8_8_194, List.forall_mem_cons.2 ⟨subd8_8_195, List.forall_mem_cons.2 ⟨subd8_8_196, List.forall_mem_cons.2 ⟨subd8_8_197, List.forall_mem_cons.2 ⟨subd8_8_198, List.forall_mem_cons.2 ⟨subd8_8_199, List.forall_mem_cons.2 ⟨subd8_8_200, List.forall_mem_cons.2 ⟨subd8_8_201, List.forall_mem_cons.2 ⟨subd8_8_202, List.forall_mem_cons.2 ⟨subd8_8_203, List.forall_mem_cons.2 ⟨subd8_8_204, List.forall_mem_cons.2 ⟨subd8_8_205, List.forall_mem_cons.2 ⟨subd8_8_206, List.forall_mem_cons.2 ⟨subd8_8_207, List.forall_mem_cons.2 ⟨subd8_8_208, List.forall_mem_cons.2 ⟨subd8_8_209, List.forall_mem_cons.2 ⟨subd8_8_210, List.forall_mem_cons.2 ⟨subd8_8_211, List.forall_mem_cons.2 ⟨subd8_8_212, List.forall_mem_cons.2 ⟨subd8_8_213, List.forall_mem_cons.2 ⟨subd8_8_214, List.forall_mem_cons.2 ⟨subd8_8_215, List.forall_mem_cons.2 ⟨subd8_8_216, List.forall_mem_cons.2 ⟨subd8_8_217, List.forall_mem_cons.2 ⟨subd8_8_218, List.forall_mem_cons.2 ⟨subd8_8_219, List.forall_mem_cons.2 ⟨subd8_8_220, List.forall_mem_cons.2 ⟨subd8_8_221, List.forall_mem_cons.2 ⟨subd8_8_222, List.forall_mem_cons.2 ⟨subd8_8_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_8_224 : subd8_8 [1, -1, 4] = true := by decide +kernel
theorem subd8_8_225 : subd8_8 [1, -1, 5] = true := by decide +kernel
theorem subd8_8_226 : subd8_8 [1, -1, 6] = true := by decide +kernel
theorem subd8_8_227 : subd8_8 [1, -1, 7] = true := by decide +kernel
theorem subd8_8_228 : subd8_8 [1, -1, 8] = true := by decide +kernel
theorem subd8_8_229 : subd8_8 [1, -1, 9] = true := by decide +kernel
theorem subd8_8_230 : subd8_8 [1, -1, 10] = true := by decide +kernel
theorem subd8_8_231 : subd8_8 [1, -1, 11] = true := by decide +kernel
theorem subd8_8_232 : subd8_8 [1, -1, 12] = true := by decide +kernel
theorem subd8_8_233 : subd8_8 [1, 0, -14] = true := by decide +kernel
theorem subd8_8_234 : subd8_8 [1, 0, -13] = true := by decide +kernel
theorem subd8_8_235 : subd8_8 [1, 0, -12] = true := by decide +kernel
theorem subd8_8_236 : subd8_8 [1, 0, -11] = true := by decide +kernel
theorem subd8_8_237 : subd8_8 [1, 0, -10] = true := by decide +kernel
theorem subd8_8_238 : subd8_8 [1, 0, -9] = true := by decide +kernel
theorem subd8_8_239 : subd8_8 [1, 0, -8] = true := by decide +kernel
theorem subd8_8_240 : subd8_8 [1, 0, -7] = true := by decide +kernel
theorem subd8_8_241 : subd8_8 [1, 0, -6] = true := by decide +kernel
theorem subd8_8_242 : subd8_8 [1, 0, -5] = true := by decide +kernel
theorem subd8_8_243 : subd8_8 [1, 0, -4] = true := by decide +kernel
theorem subd8_8_244 : subd8_8 [1, 0, -3] = true := by decide +kernel
theorem subd8_8_245 : subd8_8 [1, 0, -2] = true := by decide +kernel
theorem subd8_8_246 : subd8_8 [1, 0, -1] = true := by decide +kernel
theorem subd8_8_247 : subd8_8 [1, 0, 0] = true := by decide +kernel
theorem subd8_8_248 : subd8_8 [1, 0, 1] = true := by decide +kernel
theorem subd8_8_249 : subd8_8 [1, 0, 2] = true := by decide +kernel
theorem subd8_8_250 : subd8_8 [1, 0, 3] = true := by decide +kernel
theorem subd8_8_251 : subd8_8 [1, 0, 4] = true := by decide +kernel
theorem subd8_8_252 : subd8_8 [1, 0, 5] = true := by decide +kernel
theorem subd8_8_253 : subd8_8 [1, 0, 6] = true := by decide +kernel
theorem subd8_8_254 : subd8_8 [1, 0, 7] = true := by decide +kernel
theorem subd8_8_255 : subd8_8 [1, 0, 8] = true := by decide +kernel
theorem sbd8_8_7 : ∀ q ∈ blkd8_8_7, subd8_8 q = true := by
  unfold blkd8_8_7
  exact List.forall_mem_cons.2 ⟨subd8_8_224, List.forall_mem_cons.2 ⟨subd8_8_225, List.forall_mem_cons.2 ⟨subd8_8_226, List.forall_mem_cons.2 ⟨subd8_8_227, List.forall_mem_cons.2 ⟨subd8_8_228, List.forall_mem_cons.2 ⟨subd8_8_229, List.forall_mem_cons.2 ⟨subd8_8_230, List.forall_mem_cons.2 ⟨subd8_8_231, List.forall_mem_cons.2 ⟨subd8_8_232, List.forall_mem_cons.2 ⟨subd8_8_233, List.forall_mem_cons.2 ⟨subd8_8_234, List.forall_mem_cons.2 ⟨subd8_8_235, List.forall_mem_cons.2 ⟨subd8_8_236, List.forall_mem_cons.2 ⟨subd8_8_237, List.forall_mem_cons.2 ⟨subd8_8_238, List.forall_mem_cons.2 ⟨subd8_8_239, List.forall_mem_cons.2 ⟨subd8_8_240, List.forall_mem_cons.2 ⟨subd8_8_241, List.forall_mem_cons.2 ⟨subd8_8_242, List.forall_mem_cons.2 ⟨subd8_8_243, List.forall_mem_cons.2 ⟨subd8_8_244, List.forall_mem_cons.2 ⟨subd8_8_245, List.forall_mem_cons.2 ⟨subd8_8_246, List.forall_mem_cons.2 ⟨subd8_8_247, List.forall_mem_cons.2 ⟨subd8_8_248, List.forall_mem_cons.2 ⟨subd8_8_249, List.forall_mem_cons.2 ⟨subd8_8_250, List.forall_mem_cons.2 ⟨subd8_8_251, List.forall_mem_cons.2 ⟨subd8_8_252, List.forall_mem_cons.2 ⟨subd8_8_253, List.forall_mem_cons.2 ⟨subd8_8_254, List.forall_mem_cons.2 ⟨subd8_8_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_8_256 : subd8_8 [1, 0, 9] = true := by decide +kernel
theorem subd8_8_257 : subd8_8 [1, 0, 10] = true := by decide +kernel
theorem subd8_8_258 : subd8_8 [1, 0, 11] = true := by decide +kernel
theorem subd8_8_259 : subd8_8 [1, 0, 12] = true := by decide +kernel
theorem subd8_8_260 : subd8_8 [1, 0, 13] = true := by decide +kernel
theorem sbd8_8_8 : ∀ q ∈ blkd8_8_8, subd8_8 q = true := by
  unfold blkd8_8_8
  exact List.forall_mem_cons.2 ⟨subd8_8_256, List.forall_mem_cons.2 ⟨subd8_8_257, List.forall_mem_cons.2 ⟨subd8_8_258, List.forall_mem_cons.2 ⟨subd8_8_259, List.forall_mem_cons.2 ⟨subd8_8_260, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_9 : ldCheck G d8_9.U d8_9.ms ldd8_9 = true := by decide +kernel
theorem pre_okd8_9 : subPre G cell8 d8_9 = true := by decide +kernel
theorem subd8_9_0 : subd8_9 [-4, -5] = true := by decide +kernel
theorem subd8_9_1 : subd8_9 [-4, -4] = true := by decide +kernel
theorem subd8_9_2 : subd8_9 [-4, -3] = true := by decide +kernel
theorem subd8_9_3 : subd8_9 [-4, -2] = true := by decide +kernel
theorem subd8_9_4 : subd8_9 [-4, -1] = true := by decide +kernel
theorem subd8_9_5 : subd8_9 [-4, 0] = true := by decide +kernel
theorem subd8_9_6 : subd8_9 [-4, 1] = true := by decide +kernel
theorem subd8_9_7 : subd8_9 [-3, -6] = true := by decide +kernel
theorem subd8_9_8 : subd8_9 [-3, -5] = true := by decide +kernel
theorem subd8_9_9 : subd8_9 [-3, -4] = true := by decide +kernel
theorem subd8_9_10 : subd8_9 [-3, -3] = true := by decide +kernel
theorem subd8_9_11 : subd8_9 [-3, -2] = true := by decide +kernel
theorem subd8_9_12 : subd8_9 [-3, -1] = true := by decide +kernel
theorem subd8_9_13 : subd8_9 [-3, 0] = true := by decide +kernel
theorem subd8_9_14 : subd8_9 [-3, 1] = true := by decide +kernel
theorem subd8_9_15 : subd8_9 [-3, 2] = true := by decide +kernel
theorem subd8_9_16 : subd8_9 [-2, -6] = true := by decide +kernel
theorem subd8_9_17 : subd8_9 [-2, -5] = true := by decide +kernel
theorem subd8_9_18 : subd8_9 [-2, -4] = true := by decide +kernel
theorem subd8_9_19 : subd8_9 [-2, -3] = true := by decide +kernel
theorem subd8_9_20 : subd8_9 [-2, -2] = true := by decide +kernel
theorem subd8_9_21 : subd8_9 [-2, -1] = true := by decide +kernel
theorem subd8_9_22 : subd8_9 [-2, 0] = true := by decide +kernel
theorem subd8_9_23 : subd8_9 [-2, 1] = true := by decide +kernel
theorem subd8_9_24 : subd8_9 [-2, 2] = true := by decide +kernel
theorem subd8_9_25 : subd8_9 [-2, 3] = true := by decide +kernel
theorem subd8_9_26 : subd8_9 [-1, -6] = true := by decide +kernel
theorem subd8_9_27 : subd8_9 [-1, -5] = true := by decide +kernel
theorem subd8_9_28 : subd8_9 [-1, -4] = true := by decide +kernel
theorem subd8_9_29 : subd8_9 [-1, -3] = true := by decide +kernel
theorem subd8_9_30 : subd8_9 [-1, -2] = true := by decide +kernel
theorem subd8_9_31 : subd8_9 [-1, -1] = true := by decide +kernel
theorem sbd8_9_0 : ∀ q ∈ blkd8_9_0, subd8_9 q = true := by
  unfold blkd8_9_0
  exact List.forall_mem_cons.2 ⟨subd8_9_0, List.forall_mem_cons.2 ⟨subd8_9_1, List.forall_mem_cons.2 ⟨subd8_9_2, List.forall_mem_cons.2 ⟨subd8_9_3, List.forall_mem_cons.2 ⟨subd8_9_4, List.forall_mem_cons.2 ⟨subd8_9_5, List.forall_mem_cons.2 ⟨subd8_9_6, List.forall_mem_cons.2 ⟨subd8_9_7, List.forall_mem_cons.2 ⟨subd8_9_8, List.forall_mem_cons.2 ⟨subd8_9_9, List.forall_mem_cons.2 ⟨subd8_9_10, List.forall_mem_cons.2 ⟨subd8_9_11, List.forall_mem_cons.2 ⟨subd8_9_12, List.forall_mem_cons.2 ⟨subd8_9_13, List.forall_mem_cons.2 ⟨subd8_9_14, List.forall_mem_cons.2 ⟨subd8_9_15, List.forall_mem_cons.2 ⟨subd8_9_16, List.forall_mem_cons.2 ⟨subd8_9_17, List.forall_mem_cons.2 ⟨subd8_9_18, List.forall_mem_cons.2 ⟨subd8_9_19, List.forall_mem_cons.2 ⟨subd8_9_20, List.forall_mem_cons.2 ⟨subd8_9_21, List.forall_mem_cons.2 ⟨subd8_9_22, List.forall_mem_cons.2 ⟨subd8_9_23, List.forall_mem_cons.2 ⟨subd8_9_24, List.forall_mem_cons.2 ⟨subd8_9_25, List.forall_mem_cons.2 ⟨subd8_9_26, List.forall_mem_cons.2 ⟨subd8_9_27, List.forall_mem_cons.2 ⟨subd8_9_28, List.forall_mem_cons.2 ⟨subd8_9_29, List.forall_mem_cons.2 ⟨subd8_9_30, List.forall_mem_cons.2 ⟨subd8_9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
