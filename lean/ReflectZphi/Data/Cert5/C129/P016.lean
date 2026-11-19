import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_2_128 : subd7_2 [-2, 2, -3] = true := by decide +kernel
theorem subd7_2_129 : subd7_2 [-2, 2, -2] = true := by decide +kernel
theorem subd7_2_130 : subd7_2 [-2, 2, -1] = true := by decide +kernel
theorem subd7_2_131 : subd7_2 [-2, 2, 0] = true := by decide +kernel
theorem subd7_2_132 : subd7_2 [-2, 2, 1] = true := by decide +kernel
theorem subd7_2_133 : subd7_2 [-2, 2, 2] = true := by decide +kernel
theorem subd7_2_134 : subd7_2 [-2, 2, 3] = true := by decide +kernel
theorem subd7_2_135 : subd7_2 [-2, 2, 4] = true := by decide +kernel
theorem subd7_2_136 : subd7_2 [-2, 2, 5] = true := by decide +kernel
theorem subd7_2_137 : subd7_2 [-2, 2, 6] = true := by decide +kernel
theorem subd7_2_138 : subd7_2 [-2, 2, 7] = true := by decide +kernel
theorem subd7_2_139 : subd7_2 [-2, 2, 8] = true := by decide +kernel
theorem subd7_2_140 : subd7_2 [-2, 3] = true := by decide +kernel
theorem subd7_2_141 : subd7_2 [-2, 4] = true := by decide +kernel
theorem subd7_2_142 : subd7_2 [-1, -5] = true := by decide +kernel
theorem subd7_2_143 : subd7_2 [-1, -4] = true := by decide +kernel
theorem subd7_2_144 : subd7_2 [-1, -3, -8] = true := by decide +kernel
theorem subd7_2_145 : subd7_2 [-1, -3, -7] = true := by decide +kernel
theorem subd7_2_146 : subd7_2 [-1, -3, -6] = true := by decide +kernel
theorem subd7_2_147 : subd7_2 [-1, -3, -5] = true := by decide +kernel
theorem subd7_2_148 : subd7_2 [-1, -3, -4] = true := by decide +kernel
theorem subd7_2_149 : subd7_2 [-1, -3, -3] = true := by decide +kernel
theorem subd7_2_150 : subd7_2 [-1, -3, -2] = true := by decide +kernel
theorem subd7_2_151 : subd7_2 [-1, -3, -1] = true := by decide +kernel
theorem subd7_2_152 : subd7_2 [-1, -3, 0] = true := by decide +kernel
theorem subd7_2_153 : subd7_2 [-1, -3, 1] = true := by decide +kernel
theorem subd7_2_154 : subd7_2 [-1, -3, 2] = true := by decide +kernel
theorem subd7_2_155 : subd7_2 [-1, -3, 3] = true := by decide +kernel
theorem subd7_2_156 : subd7_2 [-1, -3, 4] = true := by decide +kernel
theorem subd7_2_157 : subd7_2 [-1, -3, 5] = true := by decide +kernel
theorem subd7_2_158 : subd7_2 [-1, -3, 6] = true := by decide +kernel
theorem subd7_2_159 : subd7_2 [-1, -2, -9] = true := by decide +kernel
theorem sbd7_2_4 : ∀ q ∈ blkd7_2_4, subd7_2 q = true := by
  unfold blkd7_2_4
  exact List.forall_mem_cons.2 ⟨subd7_2_128, List.forall_mem_cons.2 ⟨subd7_2_129, List.forall_mem_cons.2 ⟨subd7_2_130, List.forall_mem_cons.2 ⟨subd7_2_131, List.forall_mem_cons.2 ⟨subd7_2_132, List.forall_mem_cons.2 ⟨subd7_2_133, List.forall_mem_cons.2 ⟨subd7_2_134, List.forall_mem_cons.2 ⟨subd7_2_135, List.forall_mem_cons.2 ⟨subd7_2_136, List.forall_mem_cons.2 ⟨subd7_2_137, List.forall_mem_cons.2 ⟨subd7_2_138, List.forall_mem_cons.2 ⟨subd7_2_139, List.forall_mem_cons.2 ⟨subd7_2_140, List.forall_mem_cons.2 ⟨subd7_2_141, List.forall_mem_cons.2 ⟨subd7_2_142, List.forall_mem_cons.2 ⟨subd7_2_143, List.forall_mem_cons.2 ⟨subd7_2_144, List.forall_mem_cons.2 ⟨subd7_2_145, List.forall_mem_cons.2 ⟨subd7_2_146, List.forall_mem_cons.2 ⟨subd7_2_147, List.forall_mem_cons.2 ⟨subd7_2_148, List.forall_mem_cons.2 ⟨subd7_2_149, List.forall_mem_cons.2 ⟨subd7_2_150, List.forall_mem_cons.2 ⟨subd7_2_151, List.forall_mem_cons.2 ⟨subd7_2_152, List.forall_mem_cons.2 ⟨subd7_2_153, List.forall_mem_cons.2 ⟨subd7_2_154, List.forall_mem_cons.2 ⟨subd7_2_155, List.forall_mem_cons.2 ⟨subd7_2_156, List.forall_mem_cons.2 ⟨subd7_2_157, List.forall_mem_cons.2 ⟨subd7_2_158, List.forall_mem_cons.2 ⟨subd7_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_160 : subd7_2 [-1, -2, -8] = true := by decide +kernel
theorem subd7_2_161 : subd7_2 [-1, -2, -7] = true := by decide +kernel
theorem subd7_2_162 : subd7_2 [-1, -2, -6] = true := by decide +kernel
theorem subd7_2_163 : subd7_2 [-1, -2, -5] = true := by decide +kernel
theorem subd7_2_164 : subd7_2 [-1, -2, -4] = true := by decide +kernel
theorem subd7_2_165 : subd7_2 [-1, -2, -3] = true := by decide +kernel
theorem subd7_2_166 : subd7_2 [-1, -2, -2] = true := by decide +kernel
theorem subd7_2_167 : subd7_2 [-1, -2, -1] = true := by decide +kernel
theorem subd7_2_168 : subd7_2 [-1, -2, 0] = true := by decide +kernel
theorem subd7_2_169 : subd7_2 [-1, -2, 1] = true := by decide +kernel
theorem subd7_2_170 : subd7_2 [-1, -2, 2] = true := by decide +kernel
theorem subd7_2_171 : subd7_2 [-1, -2, 3] = true := by decide +kernel
theorem subd7_2_172 : subd7_2 [-1, -2, 4] = true := by decide +kernel
theorem subd7_2_173 : subd7_2 [-1, -2, 5] = true := by decide +kernel
theorem subd7_2_174 : subd7_2 [-1, -2, 6] = true := by decide +kernel
theorem subd7_2_175 : subd7_2 [-1, -2, 7] = true := by decide +kernel
theorem subd7_2_176 : subd7_2 [-1, -1, -9] = true := by decide +kernel
theorem subd7_2_177 : subd7_2 [-1, -1, -8] = true := by decide +kernel
theorem subd7_2_178 : subd7_2 [-1, -1, -7] = true := by decide +kernel
theorem subd7_2_179 : subd7_2 [-1, -1, -6] = true := by decide +kernel
theorem subd7_2_180 : subd7_2 [-1, -1, -5] = true := by decide +kernel
theorem subd7_2_181 : subd7_2 [-1, -1, -4] = true := by decide +kernel
theorem subd7_2_182 : subd7_2 [-1, -1, -3] = true := by decide +kernel
theorem subd7_2_183 : subd7_2 [-1, -1, -2] = true := by decide +kernel
theorem subd7_2_184 : subd7_2 [-1, -1, -1] = true := by decide +kernel
theorem subd7_2_185 : subd7_2 [-1, -1, 0] = true := by decide +kernel
theorem subd7_2_186 : subd7_2 [-1, -1, 1] = true := by decide +kernel
theorem subd7_2_187 : subd7_2 [-1, -1, 2] = true := by decide +kernel
theorem subd7_2_188 : subd7_2 [-1, -1, 3] = true := by decide +kernel
theorem subd7_2_189 : subd7_2 [-1, -1, 4] = true := by decide +kernel
theorem subd7_2_190 : subd7_2 [-1, -1, 5] = true := by decide +kernel
theorem subd7_2_191 : subd7_2 [-1, -1, 6] = true := by decide +kernel
theorem sbd7_2_5 : ∀ q ∈ blkd7_2_5, subd7_2 q = true := by
  unfold blkd7_2_5
  exact List.forall_mem_cons.2 ⟨subd7_2_160, List.forall_mem_cons.2 ⟨subd7_2_161, List.forall_mem_cons.2 ⟨subd7_2_162, List.forall_mem_cons.2 ⟨subd7_2_163, List.forall_mem_cons.2 ⟨subd7_2_164, List.forall_mem_cons.2 ⟨subd7_2_165, List.forall_mem_cons.2 ⟨subd7_2_166, List.forall_mem_cons.2 ⟨subd7_2_167, List.forall_mem_cons.2 ⟨subd7_2_168, List.forall_mem_cons.2 ⟨subd7_2_169, List.forall_mem_cons.2 ⟨subd7_2_170, List.forall_mem_cons.2 ⟨subd7_2_171, List.forall_mem_cons.2 ⟨subd7_2_172, List.forall_mem_cons.2 ⟨subd7_2_173, List.forall_mem_cons.2 ⟨subd7_2_174, List.forall_mem_cons.2 ⟨subd7_2_175, List.forall_mem_cons.2 ⟨subd7_2_176, List.forall_mem_cons.2 ⟨subd7_2_177, List.forall_mem_cons.2 ⟨subd7_2_178, List.forall_mem_cons.2 ⟨subd7_2_179, List.forall_mem_cons.2 ⟨subd7_2_180, List.forall_mem_cons.2 ⟨subd7_2_181, List.forall_mem_cons.2 ⟨subd7_2_182, List.forall_mem_cons.2 ⟨subd7_2_183, List.forall_mem_cons.2 ⟨subd7_2_184, List.forall_mem_cons.2 ⟨subd7_2_185, List.forall_mem_cons.2 ⟨subd7_2_186, List.forall_mem_cons.2 ⟨subd7_2_187, List.forall_mem_cons.2 ⟨subd7_2_188, List.forall_mem_cons.2 ⟨subd7_2_189, List.forall_mem_cons.2 ⟨subd7_2_190, List.forall_mem_cons.2 ⟨subd7_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_192 : subd7_2 [-1, -1, 7] = true := by decide +kernel
theorem subd7_2_193 : subd7_2 [-1, -1, 8] = true := by decide +kernel
theorem subd7_2_194 : subd7_2 [-1, 0, -9] = true := by decide +kernel
theorem subd7_2_195 : subd7_2 [-1, 0, -8] = true := by decide +kernel
theorem subd7_2_196 : subd7_2 [-1, 0, -7] = true := by decide +kernel
theorem subd7_2_197 : subd7_2 [-1, 0, -6] = true := by decide +kernel
theorem subd7_2_198 : subd7_2 [-1, 0, -5] = true := by decide +kernel
theorem subd7_2_199 : subd7_2 [-1, 0, -4] = true := by decide +kernel
theorem subd7_2_200 : subd7_2 [-1, 0, -3] = true := by decide +kernel
theorem subd7_2_201 : subd7_2 [-1, 0, -2] = true := by decide +kernel
theorem subd7_2_202 : subd7_2 [-1, 0, -1] = true := by decide +kernel
theorem subd7_2_203 : subd7_2 [-1, 0, 0] = true := by decide +kernel
theorem subd7_2_204 : subd7_2 [-1, 0, 1] = true := by decide +kernel
theorem subd7_2_205 : subd7_2 [-1, 0, 2] = true := by decide +kernel
theorem subd7_2_206 : subd7_2 [-1, 0, 3] = true := by decide +kernel
theorem subd7_2_207 : subd7_2 [-1, 0, 4] = true := by decide +kernel
theorem subd7_2_208 : subd7_2 [-1, 0, 5] = true := by decide +kernel
theorem subd7_2_209 : subd7_2 [-1, 0, 6] = true := by decide +kernel
theorem subd7_2_210 : subd7_2 [-1, 0, 7] = true := by decide +kernel
theorem subd7_2_211 : subd7_2 [-1, 0, 8] = true := by decide +kernel
theorem subd7_2_212 : subd7_2 [-1, 0, 9] = true := by decide +kernel
theorem subd7_2_213 : subd7_2 [-1, 1, -8] = true := by decide +kernel
theorem subd7_2_214 : subd7_2 [-1, 1, -7] = true := by decide +kernel
theorem subd7_2_215 : subd7_2 [-1, 1, -6] = true := by decide +kernel
theorem subd7_2_216 : subd7_2 [-1, 1, -5] = true := by decide +kernel
theorem subd7_2_217 : subd7_2 [-1, 1, -4] = true := by decide +kernel
theorem subd7_2_218 : subd7_2 [-1, 1, -3] = true := by decide +kernel
theorem subd7_2_219 : subd7_2 [-1, 1, -2] = true := by decide +kernel
theorem subd7_2_220 : subd7_2 [-1, 1, -1] = true := by decide +kernel
theorem subd7_2_221 : subd7_2 [-1, 1, 0] = true := by decide +kernel
theorem subd7_2_222 : subd7_2 [-1, 1, 1] = true := by decide +kernel
theorem subd7_2_223 : subd7_2 [-1, 1, 2] = true := by decide +kernel
theorem sbd7_2_6 : ∀ q ∈ blkd7_2_6, subd7_2 q = true := by
  unfold blkd7_2_6
  exact List.forall_mem_cons.2 ⟨subd7_2_192, List.forall_mem_cons.2 ⟨subd7_2_193, List.forall_mem_cons.2 ⟨subd7_2_194, List.forall_mem_cons.2 ⟨subd7_2_195, List.forall_mem_cons.2 ⟨subd7_2_196, List.forall_mem_cons.2 ⟨subd7_2_197, List.forall_mem_cons.2 ⟨subd7_2_198, List.forall_mem_cons.2 ⟨subd7_2_199, List.forall_mem_cons.2 ⟨subd7_2_200, List.forall_mem_cons.2 ⟨subd7_2_201, List.forall_mem_cons.2 ⟨subd7_2_202, List.forall_mem_cons.2 ⟨subd7_2_203, List.forall_mem_cons.2 ⟨subd7_2_204, List.forall_mem_cons.2 ⟨subd7_2_205, List.forall_mem_cons.2 ⟨subd7_2_206, List.forall_mem_cons.2 ⟨subd7_2_207, List.forall_mem_cons.2 ⟨subd7_2_208, List.forall_mem_cons.2 ⟨subd7_2_209, List.forall_mem_cons.2 ⟨subd7_2_210, List.forall_mem_cons.2 ⟨subd7_2_211, List.forall_mem_cons.2 ⟨subd7_2_212, List.forall_mem_cons.2 ⟨subd7_2_213, List.forall_mem_cons.2 ⟨subd7_2_214, List.forall_mem_cons.2 ⟨subd7_2_215, List.forall_mem_cons.2 ⟨subd7_2_216, List.forall_mem_cons.2 ⟨subd7_2_217, List.forall_mem_cons.2 ⟨subd7_2_218, List.forall_mem_cons.2 ⟨subd7_2_219, List.forall_mem_cons.2 ⟨subd7_2_220, List.forall_mem_cons.2 ⟨subd7_2_221, List.forall_mem_cons.2 ⟨subd7_2_222, List.forall_mem_cons.2 ⟨subd7_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_224 : subd7_2 [-1, 1, 3] = true := by decide +kernel
theorem subd7_2_225 : subd7_2 [-1, 1, 4] = true := by decide +kernel
theorem subd7_2_226 : subd7_2 [-1, 1, 5] = true := by decide +kernel
theorem subd7_2_227 : subd7_2 [-1, 1, 6] = true := by decide +kernel
theorem subd7_2_228 : subd7_2 [-1, 1, 7] = true := by decide +kernel
theorem subd7_2_229 : subd7_2 [-1, 1, 8] = true := by decide +kernel
theorem subd7_2_230 : subd7_2 [-1, 1, 9] = true := by decide +kernel
theorem subd7_2_231 : subd7_2 [-1, 2, -7] = true := by decide +kernel
theorem subd7_2_232 : subd7_2 [-1, 2, -6] = true := by decide +kernel
theorem subd7_2_233 : subd7_2 [-1, 2, -5] = true := by decide +kernel
theorem subd7_2_234 : subd7_2 [-1, 2, -4] = true := by decide +kernel
theorem subd7_2_235 : subd7_2 [-1, 2, -3] = true := by decide +kernel
theorem subd7_2_236 : subd7_2 [-1, 2, -2] = true := by decide +kernel
theorem subd7_2_237 : subd7_2 [-1, 2, -1] = true := by decide +kernel
theorem subd7_2_238 : subd7_2 [-1, 2, 0] = true := by decide +kernel
theorem subd7_2_239 : subd7_2 [-1, 2, 1] = true := by decide +kernel
theorem subd7_2_240 : subd7_2 [-1, 2, 2] = true := by decide +kernel
theorem subd7_2_241 : subd7_2 [-1, 2, 3] = true := by decide +kernel
theorem subd7_2_242 : subd7_2 [-1, 2, 4] = true := by decide +kernel
theorem subd7_2_243 : subd7_2 [-1, 2, 5] = true := by decide +kernel
theorem subd7_2_244 : subd7_2 [-1, 2, 6] = true := by decide +kernel
theorem subd7_2_245 : subd7_2 [-1, 2, 7] = true := by decide +kernel
theorem subd7_2_246 : subd7_2 [-1, 2, 8] = true := by decide +kernel
theorem subd7_2_247 : subd7_2 [-1, 3, -6] = true := by decide +kernel
theorem subd7_2_248 : subd7_2 [-1, 3, -5] = true := by decide +kernel
theorem subd7_2_249 : subd7_2 [-1, 3, -4] = true := by decide +kernel
theorem subd7_2_250 : subd7_2 [-1, 3, -3] = true := by decide +kernel
theorem subd7_2_251 : subd7_2 [-1, 3, -2] = true := by decide +kernel
theorem subd7_2_252 : subd7_2 [-1, 3, -1] = true := by decide +kernel
theorem subd7_2_253 : subd7_2 [-1, 3, 0] = true := by decide +kernel
theorem subd7_2_254 : subd7_2 [-1, 3, 1] = true := by decide +kernel
theorem subd7_2_255 : subd7_2 [-1, 3, 2] = true := by decide +kernel
theorem sbd7_2_7 : ∀ q ∈ blkd7_2_7, subd7_2 q = true := by
  unfold blkd7_2_7
  exact List.forall_mem_cons.2 ⟨subd7_2_224, List.forall_mem_cons.2 ⟨subd7_2_225, List.forall_mem_cons.2 ⟨subd7_2_226, List.forall_mem_cons.2 ⟨subd7_2_227, List.forall_mem_cons.2 ⟨subd7_2_228, List.forall_mem_cons.2 ⟨subd7_2_229, List.forall_mem_cons.2 ⟨subd7_2_230, List.forall_mem_cons.2 ⟨subd7_2_231, List.forall_mem_cons.2 ⟨subd7_2_232, List.forall_mem_cons.2 ⟨subd7_2_233, List.forall_mem_cons.2 ⟨subd7_2_234, List.forall_mem_cons.2 ⟨subd7_2_235, List.forall_mem_cons.2 ⟨subd7_2_236, List.forall_mem_cons.2 ⟨subd7_2_237, List.forall_mem_cons.2 ⟨subd7_2_238, List.forall_mem_cons.2 ⟨subd7_2_239, List.forall_mem_cons.2 ⟨subd7_2_240, List.forall_mem_cons.2 ⟨subd7_2_241, List.forall_mem_cons.2 ⟨subd7_2_242, List.forall_mem_cons.2 ⟨subd7_2_243, List.forall_mem_cons.2 ⟨subd7_2_244, List.forall_mem_cons.2 ⟨subd7_2_245, List.forall_mem_cons.2 ⟨subd7_2_246, List.forall_mem_cons.2 ⟨subd7_2_247, List.forall_mem_cons.2 ⟨subd7_2_248, List.forall_mem_cons.2 ⟨subd7_2_249, List.forall_mem_cons.2 ⟨subd7_2_250, List.forall_mem_cons.2 ⟨subd7_2_251, List.forall_mem_cons.2 ⟨subd7_2_252, List.forall_mem_cons.2 ⟨subd7_2_253, List.forall_mem_cons.2 ⟨subd7_2_254, List.forall_mem_cons.2 ⟨subd7_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_256 : subd7_2 [-1, 3, 3] = true := by decide +kernel
theorem subd7_2_257 : subd7_2 [-1, 3, 4] = true := by decide +kernel
theorem subd7_2_258 : subd7_2 [-1, 3, 5] = true := by decide +kernel
theorem subd7_2_259 : subd7_2 [-1, 3, 6] = true := by decide +kernel
theorem subd7_2_260 : subd7_2 [-1, 3, 7] = true := by decide +kernel
theorem subd7_2_261 : subd7_2 [-1, 3, 8] = true := by decide +kernel
theorem subd7_2_262 : subd7_2 [-1, 4] = true := by decide +kernel
theorem subd7_2_263 : subd7_2 [0, -5] = true := by decide +kernel
theorem subd7_2_264 : subd7_2 [0, -4] = true := by decide +kernel
theorem subd7_2_265 : subd7_2 [0, -3, -9] = true := by decide +kernel
theorem subd7_2_266 : subd7_2 [0, -3, -8] = true := by decide +kernel
theorem subd7_2_267 : subd7_2 [0, -3, -7] = true := by decide +kernel
theorem subd7_2_268 : subd7_2 [0, -3, -6] = true := by decide +kernel
theorem subd7_2_269 : subd7_2 [0, -3, -5] = true := by decide +kernel
theorem subd7_2_270 : subd7_2 [0, -3, -4] = true := by decide +kernel
theorem subd7_2_271 : subd7_2 [0, -3, -3] = true := by decide +kernel
theorem subd7_2_272 : subd7_2 [0, -3, -2] = true := by decide +kernel
theorem subd7_2_273 : subd7_2 [0, -3, -1] = true := by decide +kernel
theorem subd7_2_274 : subd7_2 [0, -3, 0] = true := by decide +kernel
theorem subd7_2_275 : subd7_2 [0, -3, 1] = true := by decide +kernel
theorem subd7_2_276 : subd7_2 [0, -3, 2] = true := by decide +kernel
theorem subd7_2_277 : subd7_2 [0, -3, 3] = true := by decide +kernel
theorem subd7_2_278 : subd7_2 [0, -3, 4] = true := by decide +kernel
theorem subd7_2_279 : subd7_2 [0, -3, 5] = true := by decide +kernel
theorem subd7_2_280 : subd7_2 [0, -2, -9] = true := by decide +kernel
theorem subd7_2_281 : subd7_2 [0, -2, -8] = true := by decide +kernel
theorem subd7_2_282 : subd7_2 [0, -2, -7] = true := by decide +kernel
theorem subd7_2_283 : subd7_2 [0, -2, -6] = true := by decide +kernel
theorem subd7_2_284 : subd7_2 [0, -2, -5] = true := by decide +kernel
theorem subd7_2_285 : subd7_2 [0, -2, -4] = true := by decide +kernel
theorem subd7_2_286 : subd7_2 [0, -2, -3] = true := by decide +kernel
theorem subd7_2_287 : subd7_2 [0, -2, -2] = true := by decide +kernel
theorem sbd7_2_8 : ∀ q ∈ blkd7_2_8, subd7_2 q = true := by
  unfold blkd7_2_8
  exact List.forall_mem_cons.2 ⟨subd7_2_256, List.forall_mem_cons.2 ⟨subd7_2_257, List.forall_mem_cons.2 ⟨subd7_2_258, List.forall_mem_cons.2 ⟨subd7_2_259, List.forall_mem_cons.2 ⟨subd7_2_260, List.forall_mem_cons.2 ⟨subd7_2_261, List.forall_mem_cons.2 ⟨subd7_2_262, List.forall_mem_cons.2 ⟨subd7_2_263, List.forall_mem_cons.2 ⟨subd7_2_264, List.forall_mem_cons.2 ⟨subd7_2_265, List.forall_mem_cons.2 ⟨subd7_2_266, List.forall_mem_cons.2 ⟨subd7_2_267, List.forall_mem_cons.2 ⟨subd7_2_268, List.forall_mem_cons.2 ⟨subd7_2_269, List.forall_mem_cons.2 ⟨subd7_2_270, List.forall_mem_cons.2 ⟨subd7_2_271, List.forall_mem_cons.2 ⟨subd7_2_272, List.forall_mem_cons.2 ⟨subd7_2_273, List.forall_mem_cons.2 ⟨subd7_2_274, List.forall_mem_cons.2 ⟨subd7_2_275, List.forall_mem_cons.2 ⟨subd7_2_276, List.forall_mem_cons.2 ⟨subd7_2_277, List.forall_mem_cons.2 ⟨subd7_2_278, List.forall_mem_cons.2 ⟨subd7_2_279, List.forall_mem_cons.2 ⟨subd7_2_280, List.forall_mem_cons.2 ⟨subd7_2_281, List.forall_mem_cons.2 ⟨subd7_2_282, List.forall_mem_cons.2 ⟨subd7_2_283, List.forall_mem_cons.2 ⟨subd7_2_284, List.forall_mem_cons.2 ⟨subd7_2_285, List.forall_mem_cons.2 ⟨subd7_2_286, List.forall_mem_cons.2 ⟨subd7_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_288 : subd7_2 [0, -2, -1] = true := by decide +kernel
theorem subd7_2_289 : subd7_2 [0, -2, 0] = true := by decide +kernel
theorem subd7_2_290 : subd7_2 [0, -2, 1] = true := by decide +kernel
theorem subd7_2_291 : subd7_2 [0, -2, 2] = true := by decide +kernel
theorem subd7_2_292 : subd7_2 [0, -2, 3] = true := by decide +kernel
theorem subd7_2_293 : subd7_2 [0, -2, 4] = true := by decide +kernel
theorem subd7_2_294 : subd7_2 [0, -2, 5] = true := by decide +kernel
theorem subd7_2_295 : subd7_2 [0, -2, 6] = true := by decide +kernel
theorem subd7_2_296 : subd7_2 [0, -2, 7] = true := by decide +kernel
theorem subd7_2_297 : subd7_2 [0, -1, -9] = true := by decide +kernel
theorem subd7_2_298 : subd7_2 [0, -1, -8] = true := by decide +kernel
theorem subd7_2_299 : subd7_2 [0, -1, -7] = true := by decide +kernel
theorem subd7_2_300 : subd7_2 [0, -1, -6] = true := by decide +kernel
theorem subd7_2_301 : subd7_2 [0, -1, -5] = true := by decide +kernel
theorem subd7_2_302 : subd7_2 [0, -1, -4] = true := by decide +kernel
theorem subd7_2_303 : subd7_2 [0, -1, -3] = true := by decide +kernel
theorem subd7_2_304 : subd7_2 [0, -1, -2] = true := by decide +kernel
theorem subd7_2_305 : subd7_2 [0, -1, -1] = true := by decide +kernel
theorem subd7_2_306 : subd7_2 [0, -1, 0] = true := by decide +kernel
theorem subd7_2_307 : subd7_2 [0, -1, 1] = true := by decide +kernel
theorem subd7_2_308 : subd7_2 [0, -1, 2] = true := by decide +kernel
theorem subd7_2_309 : subd7_2 [0, -1, 3] = true := by decide +kernel
theorem subd7_2_310 : subd7_2 [0, -1, 4] = true := by decide +kernel
theorem subd7_2_311 : subd7_2 [0, -1, 5] = true := by decide +kernel
theorem subd7_2_312 : subd7_2 [0, -1, 6] = true := by decide +kernel
theorem subd7_2_313 : subd7_2 [0, -1, 7] = true := by decide +kernel
theorem subd7_2_314 : subd7_2 [0, -1, 8] = true := by decide +kernel
theorem subd7_2_315 : subd7_2 [0, 0, -9] = true := by decide +kernel
theorem subd7_2_316 : subd7_2 [0, 0, -8] = true := by decide +kernel
theorem subd7_2_317 : subd7_2 [0, 0, -7] = true := by decide +kernel
theorem subd7_2_318 : subd7_2 [0, 0, -6] = true := by decide +kernel
theorem subd7_2_319 : subd7_2 [0, 0, -5] = true := by decide +kernel
theorem sbd7_2_9 : ∀ q ∈ blkd7_2_9, subd7_2 q = true := by
  unfold blkd7_2_9
  exact List.forall_mem_cons.2 ⟨subd7_2_288, List.forall_mem_cons.2 ⟨subd7_2_289, List.forall_mem_cons.2 ⟨subd7_2_290, List.forall_mem_cons.2 ⟨subd7_2_291, List.forall_mem_cons.2 ⟨subd7_2_292, List.forall_mem_cons.2 ⟨subd7_2_293, List.forall_mem_cons.2 ⟨subd7_2_294, List.forall_mem_cons.2 ⟨subd7_2_295, List.forall_mem_cons.2 ⟨subd7_2_296, List.forall_mem_cons.2 ⟨subd7_2_297, List.forall_mem_cons.2 ⟨subd7_2_298, List.forall_mem_cons.2 ⟨subd7_2_299, List.forall_mem_cons.2 ⟨subd7_2_300, List.forall_mem_cons.2 ⟨subd7_2_301, List.forall_mem_cons.2 ⟨subd7_2_302, List.forall_mem_cons.2 ⟨subd7_2_303, List.forall_mem_cons.2 ⟨subd7_2_304, List.forall_mem_cons.2 ⟨subd7_2_305, List.forall_mem_cons.2 ⟨subd7_2_306, List.forall_mem_cons.2 ⟨subd7_2_307, List.forall_mem_cons.2 ⟨subd7_2_308, List.forall_mem_cons.2 ⟨subd7_2_309, List.forall_mem_cons.2 ⟨subd7_2_310, List.forall_mem_cons.2 ⟨subd7_2_311, List.forall_mem_cons.2 ⟨subd7_2_312, List.forall_mem_cons.2 ⟨subd7_2_313, List.forall_mem_cons.2 ⟨subd7_2_314, List.forall_mem_cons.2 ⟨subd7_2_315, List.forall_mem_cons.2 ⟨subd7_2_316, List.forall_mem_cons.2 ⟨subd7_2_317, List.forall_mem_cons.2 ⟨subd7_2_318, List.forall_mem_cons.2 ⟨subd7_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_320 : subd7_2 [0, 0, -4] = true := by decide +kernel
theorem subd7_2_321 : subd7_2 [0, 0, -3] = true := by decide +kernel
theorem subd7_2_322 : subd7_2 [0, 0, -2] = true := by decide +kernel
theorem subd7_2_323 : subd7_2 [0, 0, -1] = true := by decide +kernel
theorem subd7_2_324 : subd7_2 [0, 0, 0] = true := by decide +kernel
theorem subd7_2_325 : subd7_2 [0, 0, 1] = true := by decide +kernel
theorem subd7_2_326 : subd7_2 [0, 0, 2] = true := by decide +kernel
theorem subd7_2_327 : subd7_2 [0, 0, 3] = true := by decide +kernel
theorem subd7_2_328 : subd7_2 [0, 0, 4] = true := by decide +kernel
theorem subd7_2_329 : subd7_2 [0, 0, 5] = true := by decide +kernel
theorem subd7_2_330 : subd7_2 [0, 0, 6] = true := by decide +kernel
theorem subd7_2_331 : subd7_2 [0, 0, 7] = true := by decide +kernel
theorem subd7_2_332 : subd7_2 [0, 0, 8] = true := by decide +kernel
theorem subd7_2_333 : subd7_2 [0, 1, -9] = true := by decide +kernel
theorem subd7_2_334 : subd7_2 [0, 1, -8] = true := by decide +kernel
theorem subd7_2_335 : subd7_2 [0, 1, -7] = true := by decide +kernel
theorem subd7_2_336 : subd7_2 [0, 1, -6] = true := by decide +kernel
theorem subd7_2_337 : subd7_2 [0, 1, -5] = true := by decide +kernel
theorem subd7_2_338 : subd7_2 [0, 1, -4] = true := by decide +kernel
theorem subd7_2_339 : subd7_2 [0, 1, -3] = true := by decide +kernel
theorem subd7_2_340 : subd7_2 [0, 1, -2] = true := by decide +kernel
theorem subd7_2_341 : subd7_2 [0, 1, -1] = true := by decide +kernel
theorem subd7_2_342 : subd7_2 [0, 1, 0] = true := by decide +kernel
theorem subd7_2_343 : subd7_2 [0, 1, 1] = true := by decide +kernel
theorem subd7_2_344 : subd7_2 [0, 1, 2] = true := by decide +kernel
theorem subd7_2_345 : subd7_2 [0, 1, 3] = true := by decide +kernel
theorem subd7_2_346 : subd7_2 [0, 1, 4] = true := by decide +kernel
theorem subd7_2_347 : subd7_2 [0, 1, 5] = true := by decide +kernel
theorem subd7_2_348 : subd7_2 [0, 1, 6] = true := by decide +kernel
theorem subd7_2_349 : subd7_2 [0, 1, 7] = true := by decide +kernel
theorem subd7_2_350 : subd7_2 [0, 1, 8] = true := by decide +kernel
theorem subd7_2_351 : subd7_2 [0, 2, -8] = true := by decide +kernel
theorem sbd7_2_10 : ∀ q ∈ blkd7_2_10, subd7_2 q = true := by
  unfold blkd7_2_10
  exact List.forall_mem_cons.2 ⟨subd7_2_320, List.forall_mem_cons.2 ⟨subd7_2_321, List.forall_mem_cons.2 ⟨subd7_2_322, List.forall_mem_cons.2 ⟨subd7_2_323, List.forall_mem_cons.2 ⟨subd7_2_324, List.forall_mem_cons.2 ⟨subd7_2_325, List.forall_mem_cons.2 ⟨subd7_2_326, List.forall_mem_cons.2 ⟨subd7_2_327, List.forall_mem_cons.2 ⟨subd7_2_328, List.forall_mem_cons.2 ⟨subd7_2_329, List.forall_mem_cons.2 ⟨subd7_2_330, List.forall_mem_cons.2 ⟨subd7_2_331, List.forall_mem_cons.2 ⟨subd7_2_332, List.forall_mem_cons.2 ⟨subd7_2_333, List.forall_mem_cons.2 ⟨subd7_2_334, List.forall_mem_cons.2 ⟨subd7_2_335, List.forall_mem_cons.2 ⟨subd7_2_336, List.forall_mem_cons.2 ⟨subd7_2_337, List.forall_mem_cons.2 ⟨subd7_2_338, List.forall_mem_cons.2 ⟨subd7_2_339, List.forall_mem_cons.2 ⟨subd7_2_340, List.forall_mem_cons.2 ⟨subd7_2_341, List.forall_mem_cons.2 ⟨subd7_2_342, List.forall_mem_cons.2 ⟨subd7_2_343, List.forall_mem_cons.2 ⟨subd7_2_344, List.forall_mem_cons.2 ⟨subd7_2_345, List.forall_mem_cons.2 ⟨subd7_2_346, List.forall_mem_cons.2 ⟨subd7_2_347, List.forall_mem_cons.2 ⟨subd7_2_348, List.forall_mem_cons.2 ⟨subd7_2_349, List.forall_mem_cons.2 ⟨subd7_2_350, List.forall_mem_cons.2 ⟨subd7_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_352 : subd7_2 [0, 2, -7] = true := by decide +kernel
theorem subd7_2_353 : subd7_2 [0, 2, -6] = true := by decide +kernel
theorem subd7_2_354 : subd7_2 [0, 2, -5] = true := by decide +kernel
theorem subd7_2_355 : subd7_2 [0, 2, -4] = true := by decide +kernel
theorem subd7_2_356 : subd7_2 [0, 2, -3] = true := by decide +kernel
theorem subd7_2_357 : subd7_2 [0, 2, -2] = true := by decide +kernel
theorem subd7_2_358 : subd7_2 [0, 2, -1] = true := by decide +kernel
theorem subd7_2_359 : subd7_2 [0, 2, 0] = true := by decide +kernel
theorem subd7_2_360 : subd7_2 [0, 2, 1] = true := by decide +kernel
theorem subd7_2_361 : subd7_2 [0, 2, 2] = true := by decide +kernel
theorem subd7_2_362 : subd7_2 [0, 2, 3] = true := by decide +kernel
theorem subd7_2_363 : subd7_2 [0, 2, 4] = true := by decide +kernel
theorem subd7_2_364 : subd7_2 [0, 2, 5] = true := by decide +kernel
theorem subd7_2_365 : subd7_2 [0, 2, 6] = true := by decide +kernel
theorem subd7_2_366 : subd7_2 [0, 2, 7] = true := by decide +kernel
theorem subd7_2_367 : subd7_2 [0, 2, 8] = true := by decide +kernel
theorem subd7_2_368 : subd7_2 [0, 3, -6] = true := by decide +kernel
theorem subd7_2_369 : subd7_2 [0, 3, -5] = true := by decide +kernel
theorem subd7_2_370 : subd7_2 [0, 3, -4] = true := by decide +kernel
theorem subd7_2_371 : subd7_2 [0, 3, -3] = true := by decide +kernel
theorem subd7_2_372 : subd7_2 [0, 3, -2] = true := by decide +kernel
theorem subd7_2_373 : subd7_2 [0, 3, -1] = true := by decide +kernel
theorem subd7_2_374 : subd7_2 [0, 3, 0] = true := by decide +kernel
theorem subd7_2_375 : subd7_2 [0, 3, 1] = true := by decide +kernel
theorem subd7_2_376 : subd7_2 [0, 3, 2] = true := by decide +kernel
theorem subd7_2_377 : subd7_2 [0, 3, 3] = true := by decide +kernel
theorem subd7_2_378 : subd7_2 [0, 3, 4] = true := by decide +kernel
theorem subd7_2_379 : subd7_2 [0, 3, 5] = true := by decide +kernel
theorem subd7_2_380 : subd7_2 [0, 3, 6] = true := by decide +kernel
theorem subd7_2_381 : subd7_2 [0, 3, 7] = true := by decide +kernel
theorem subd7_2_382 : subd7_2 [0, 3, 8] = true := by decide +kernel
theorem subd7_2_383 : subd7_2 [0, 4] = true := by decide +kernel
theorem sbd7_2_11 : ∀ q ∈ blkd7_2_11, subd7_2 q = true := by
  unfold blkd7_2_11
  exact List.forall_mem_cons.2 ⟨subd7_2_352, List.forall_mem_cons.2 ⟨subd7_2_353, List.forall_mem_cons.2 ⟨subd7_2_354, List.forall_mem_cons.2 ⟨subd7_2_355, List.forall_mem_cons.2 ⟨subd7_2_356, List.forall_mem_cons.2 ⟨subd7_2_357, List.forall_mem_cons.2 ⟨subd7_2_358, List.forall_mem_cons.2 ⟨subd7_2_359, List.forall_mem_cons.2 ⟨subd7_2_360, List.forall_mem_cons.2 ⟨subd7_2_361, List.forall_mem_cons.2 ⟨subd7_2_362, List.forall_mem_cons.2 ⟨subd7_2_363, List.forall_mem_cons.2 ⟨subd7_2_364, List.forall_mem_cons.2 ⟨subd7_2_365, List.forall_mem_cons.2 ⟨subd7_2_366, List.forall_mem_cons.2 ⟨subd7_2_367, List.forall_mem_cons.2 ⟨subd7_2_368, List.forall_mem_cons.2 ⟨subd7_2_369, List.forall_mem_cons.2 ⟨subd7_2_370, List.forall_mem_cons.2 ⟨subd7_2_371, List.forall_mem_cons.2 ⟨subd7_2_372, List.forall_mem_cons.2 ⟨subd7_2_373, List.forall_mem_cons.2 ⟨subd7_2_374, List.forall_mem_cons.2 ⟨subd7_2_375, List.forall_mem_cons.2 ⟨subd7_2_376, List.forall_mem_cons.2 ⟨subd7_2_377, List.forall_mem_cons.2 ⟨subd7_2_378, List.forall_mem_cons.2 ⟨subd7_2_379, List.forall_mem_cons.2 ⟨subd7_2_380, List.forall_mem_cons.2 ⟨subd7_2_381, List.forall_mem_cons.2 ⟨subd7_2_382, List.forall_mem_cons.2 ⟨subd7_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_384 : subd7_2 [1, -5] = true := by decide +kernel
theorem subd7_2_385 : subd7_2 [1, -4] = true := by decide +kernel
theorem subd7_2_386 : subd7_2 [1, -3, -9] = true := by decide +kernel
theorem subd7_2_387 : subd7_2 [1, -3, -8] = true := by decide +kernel
theorem subd7_2_388 : subd7_2 [1, -3, -7] = true := by decide +kernel
theorem subd7_2_389 : subd7_2 [1, -3, -6] = true := by decide +kernel
theorem subd7_2_390 : subd7_2 [1, -3, -5] = true := by decide +kernel
theorem subd7_2_391 : subd7_2 [1, -3, -4] = true := by decide +kernel
theorem subd7_2_392 : subd7_2 [1, -3, -3] = true := by decide +kernel
theorem subd7_2_393 : subd7_2 [1, -3, -2] = true := by decide +kernel
theorem subd7_2_394 : subd7_2 [1, -3, -1] = true := by decide +kernel
theorem subd7_2_395 : subd7_2 [1, -3, 0] = true := by decide +kernel
theorem subd7_2_396 : subd7_2 [1, -3, 1] = true := by decide +kernel
theorem subd7_2_397 : subd7_2 [1, -3, 2] = true := by decide +kernel
theorem subd7_2_398 : subd7_2 [1, -3, 3] = true := by decide +kernel
theorem subd7_2_399 : subd7_2 [1, -3, 4] = true := by decide +kernel
theorem subd7_2_400 : subd7_2 [1, -3, 5] = true := by decide +kernel
theorem subd7_2_401 : subd7_2 [1, -2, -9] = true := by decide +kernel
theorem subd7_2_402 : subd7_2 [1, -2, -8] = true := by decide +kernel
theorem subd7_2_403 : subd7_2 [1, -2, -7] = true := by decide +kernel
theorem subd7_2_404 : subd7_2 [1, -2, -6] = true := by decide +kernel
theorem subd7_2_405 : subd7_2 [1, -2, -5] = true := by decide +kernel
theorem subd7_2_406 : subd7_2 [1, -2, -4] = true := by decide +kernel
theorem subd7_2_407 : subd7_2 [1, -2, -3] = true := by decide +kernel
theorem subd7_2_408 : subd7_2 [1, -2, -2] = true := by decide +kernel
theorem subd7_2_409 : subd7_2 [1, -2, -1] = true := by decide +kernel
theorem subd7_2_410 : subd7_2 [1, -2, 0] = true := by decide +kernel
theorem subd7_2_411 : subd7_2 [1, -2, 1] = true := by decide +kernel
theorem subd7_2_412 : subd7_2 [1, -2, 2] = true := by decide +kernel
theorem subd7_2_413 : subd7_2 [1, -2, 3] = true := by decide +kernel
theorem subd7_2_414 : subd7_2 [1, -2, 4] = true := by decide +kernel
theorem subd7_2_415 : subd7_2 [1, -2, 5] = true := by decide +kernel
theorem sbd7_2_12 : ∀ q ∈ blkd7_2_12, subd7_2 q = true := by
  unfold blkd7_2_12
  exact List.forall_mem_cons.2 ⟨subd7_2_384, List.forall_mem_cons.2 ⟨subd7_2_385, List.forall_mem_cons.2 ⟨subd7_2_386, List.forall_mem_cons.2 ⟨subd7_2_387, List.forall_mem_cons.2 ⟨subd7_2_388, List.forall_mem_cons.2 ⟨subd7_2_389, List.forall_mem_cons.2 ⟨subd7_2_390, List.forall_mem_cons.2 ⟨subd7_2_391, List.forall_mem_cons.2 ⟨subd7_2_392, List.forall_mem_cons.2 ⟨subd7_2_393, List.forall_mem_cons.2 ⟨subd7_2_394, List.forall_mem_cons.2 ⟨subd7_2_395, List.forall_mem_cons.2 ⟨subd7_2_396, List.forall_mem_cons.2 ⟨subd7_2_397, List.forall_mem_cons.2 ⟨subd7_2_398, List.forall_mem_cons.2 ⟨subd7_2_399, List.forall_mem_cons.2 ⟨subd7_2_400, List.forall_mem_cons.2 ⟨subd7_2_401, List.forall_mem_cons.2 ⟨subd7_2_402, List.forall_mem_cons.2 ⟨subd7_2_403, List.forall_mem_cons.2 ⟨subd7_2_404, List.forall_mem_cons.2 ⟨subd7_2_405, List.forall_mem_cons.2 ⟨subd7_2_406, List.forall_mem_cons.2 ⟨subd7_2_407, List.forall_mem_cons.2 ⟨subd7_2_408, List.forall_mem_cons.2 ⟨subd7_2_409, List.forall_mem_cons.2 ⟨subd7_2_410, List.forall_mem_cons.2 ⟨subd7_2_411, List.forall_mem_cons.2 ⟨subd7_2_412, List.forall_mem_cons.2 ⟨subd7_2_413, List.forall_mem_cons.2 ⟨subd7_2_414, List.forall_mem_cons.2 ⟨subd7_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_416 : subd7_2 [1, -2, 6] = true := by decide +kernel
theorem subd7_2_417 : subd7_2 [1, -1, -10] = true := by decide +kernel
theorem subd7_2_418 : subd7_2 [1, -1, -9] = true := by decide +kernel
theorem subd7_2_419 : subd7_2 [1, -1, -8] = true := by decide +kernel
theorem subd7_2_420 : subd7_2 [1, -1, -7] = true := by decide +kernel
theorem subd7_2_421 : subd7_2 [1, -1, -6] = true := by decide +kernel
theorem subd7_2_422 : subd7_2 [1, -1, -5] = true := by decide +kernel
theorem subd7_2_423 : subd7_2 [1, -1, -4] = true := by decide +kernel
theorem subd7_2_424 : subd7_2 [1, -1, -3] = true := by decide +kernel
theorem subd7_2_425 : subd7_2 [1, -1, -2] = true := by decide +kernel
theorem subd7_2_426 : subd7_2 [1, -1, -1] = true := by decide +kernel
theorem subd7_2_427 : subd7_2 [1, -1, 0] = true := by decide +kernel
theorem subd7_2_428 : subd7_2 [1, -1, 1] = true := by decide +kernel
theorem subd7_2_429 : subd7_2 [1, -1, 2] = true := by decide +kernel
theorem subd7_2_430 : subd7_2 [1, -1, 3] = true := by decide +kernel
theorem subd7_2_431 : subd7_2 [1, -1, 4] = true := by decide +kernel
theorem subd7_2_432 : subd7_2 [1, -1, 5] = true := by decide +kernel
theorem subd7_2_433 : subd7_2 [1, -1, 6] = true := by decide +kernel
theorem subd7_2_434 : subd7_2 [1, -1, 7] = true := by decide +kernel
theorem subd7_2_435 : subd7_2 [1, 0, -10] = true := by decide +kernel
theorem subd7_2_436 : subd7_2 [1, 0, -9] = true := by decide +kernel
theorem subd7_2_437 : subd7_2 [1, 0, -8] = true := by decide +kernel
theorem subd7_2_438 : subd7_2 [1, 0, -7] = true := by decide +kernel
theorem subd7_2_439 : subd7_2 [1, 0, -6] = true := by decide +kernel
theorem subd7_2_440 : subd7_2 [1, 0, -5] = true := by decide +kernel
theorem subd7_2_441 : subd7_2 [1, 0, -4] = true := by decide +kernel
theorem subd7_2_442 : subd7_2 [1, 0, -3] = true := by decide +kernel
theorem subd7_2_443 : subd7_2 [1, 0, -2] = true := by decide +kernel
theorem subd7_2_444 : subd7_2 [1, 0, -1] = true := by decide +kernel
theorem subd7_2_445 : subd7_2 [1, 0, 0] = true := by decide +kernel
theorem subd7_2_446 : subd7_2 [1, 0, 1] = true := by decide +kernel
theorem subd7_2_447 : subd7_2 [1, 0, 2] = true := by decide +kernel
theorem sbd7_2_13 : ∀ q ∈ blkd7_2_13, subd7_2 q = true := by
  unfold blkd7_2_13
  exact List.forall_mem_cons.2 ⟨subd7_2_416, List.forall_mem_cons.2 ⟨subd7_2_417, List.forall_mem_cons.2 ⟨subd7_2_418, List.forall_mem_cons.2 ⟨subd7_2_419, List.forall_mem_cons.2 ⟨subd7_2_420, List.forall_mem_cons.2 ⟨subd7_2_421, List.forall_mem_cons.2 ⟨subd7_2_422, List.forall_mem_cons.2 ⟨subd7_2_423, List.forall_mem_cons.2 ⟨subd7_2_424, List.forall_mem_cons.2 ⟨subd7_2_425, List.forall_mem_cons.2 ⟨subd7_2_426, List.forall_mem_cons.2 ⟨subd7_2_427, List.forall_mem_cons.2 ⟨subd7_2_428, List.forall_mem_cons.2 ⟨subd7_2_429, List.forall_mem_cons.2 ⟨subd7_2_430, List.forall_mem_cons.2 ⟨subd7_2_431, List.forall_mem_cons.2 ⟨subd7_2_432, List.forall_mem_cons.2 ⟨subd7_2_433, List.forall_mem_cons.2 ⟨subd7_2_434, List.forall_mem_cons.2 ⟨subd7_2_435, List.forall_mem_cons.2 ⟨subd7_2_436, List.forall_mem_cons.2 ⟨subd7_2_437, List.forall_mem_cons.2 ⟨subd7_2_438, List.forall_mem_cons.2 ⟨subd7_2_439, List.forall_mem_cons.2 ⟨subd7_2_440, List.forall_mem_cons.2 ⟨subd7_2_441, List.forall_mem_cons.2 ⟨subd7_2_442, List.forall_mem_cons.2 ⟨subd7_2_443, List.forall_mem_cons.2 ⟨subd7_2_444, List.forall_mem_cons.2 ⟨subd7_2_445, List.forall_mem_cons.2 ⟨subd7_2_446, List.forall_mem_cons.2 ⟨subd7_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_448 : subd7_2 [1, 0, 3] = true := by decide +kernel
theorem subd7_2_449 : subd7_2 [1, 0, 4] = true := by decide +kernel
theorem subd7_2_450 : subd7_2 [1, 0, 5] = true := by decide +kernel
theorem subd7_2_451 : subd7_2 [1, 0, 6] = true := by decide +kernel
theorem subd7_2_452 : subd7_2 [1, 0, 7] = true := by decide +kernel
theorem subd7_2_453 : subd7_2 [1, 0, 8] = true := by decide +kernel
theorem subd7_2_454 : subd7_2 [1, 1, -9] = true := by decide +kernel
theorem subd7_2_455 : subd7_2 [1, 1, -8] = true := by decide +kernel
theorem subd7_2_456 : subd7_2 [1, 1, -7] = true := by decide +kernel
theorem subd7_2_457 : subd7_2 [1, 1, -6] = true := by decide +kernel
theorem subd7_2_458 : subd7_2 [1, 1, -5] = true := by decide +kernel
theorem subd7_2_459 : subd7_2 [1, 1, -4] = true := by decide +kernel
theorem subd7_2_460 : subd7_2 [1, 1, -3] = true := by decide +kernel
theorem subd7_2_461 : subd7_2 [1, 1, -2] = true := by decide +kernel
theorem subd7_2_462 : subd7_2 [1, 1, -1] = true := by decide +kernel
theorem subd7_2_463 : subd7_2 [1, 1, 0] = true := by decide +kernel
theorem subd7_2_464 : subd7_2 [1, 1, 1] = true := by decide +kernel
theorem subd7_2_465 : subd7_2 [1, 1, 2] = true := by decide +kernel
theorem subd7_2_466 : subd7_2 [1, 1, 3] = true := by decide +kernel
theorem subd7_2_467 : subd7_2 [1, 1, 4] = true := by decide +kernel
theorem subd7_2_468 : subd7_2 [1, 1, 5] = true := by decide +kernel
theorem subd7_2_469 : subd7_2 [1, 1, 6] = true := by decide +kernel
theorem subd7_2_470 : subd7_2 [1, 1, 7] = true := by decide +kernel
theorem subd7_2_471 : subd7_2 [1, 1, 8] = true := by decide +kernel
theorem subd7_2_472 : subd7_2 [1, 2, -8] = true := by decide +kernel
theorem subd7_2_473 : subd7_2 [1, 2, -7] = true := by decide +kernel
theorem subd7_2_474 : subd7_2 [1, 2, -6] = true := by decide +kernel
theorem subd7_2_475 : subd7_2 [1, 2, -5] = true := by decide +kernel
theorem subd7_2_476 : subd7_2 [1, 2, -4] = true := by decide +kernel
theorem subd7_2_477 : subd7_2 [1, 2, -3] = true := by decide +kernel
theorem subd7_2_478 : subd7_2 [1, 2, -2] = true := by decide +kernel
theorem subd7_2_479 : subd7_2 [1, 2, -1] = true := by decide +kernel
theorem sbd7_2_14 : ∀ q ∈ blkd7_2_14, subd7_2 q = true := by
  unfold blkd7_2_14
  exact List.forall_mem_cons.2 ⟨subd7_2_448, List.forall_mem_cons.2 ⟨subd7_2_449, List.forall_mem_cons.2 ⟨subd7_2_450, List.forall_mem_cons.2 ⟨subd7_2_451, List.forall_mem_cons.2 ⟨subd7_2_452, List.forall_mem_cons.2 ⟨subd7_2_453, List.forall_mem_cons.2 ⟨subd7_2_454, List.forall_mem_cons.2 ⟨subd7_2_455, List.forall_mem_cons.2 ⟨subd7_2_456, List.forall_mem_cons.2 ⟨subd7_2_457, List.forall_mem_cons.2 ⟨subd7_2_458, List.forall_mem_cons.2 ⟨subd7_2_459, List.forall_mem_cons.2 ⟨subd7_2_460, List.forall_mem_cons.2 ⟨subd7_2_461, List.forall_mem_cons.2 ⟨subd7_2_462, List.forall_mem_cons.2 ⟨subd7_2_463, List.forall_mem_cons.2 ⟨subd7_2_464, List.forall_mem_cons.2 ⟨subd7_2_465, List.forall_mem_cons.2 ⟨subd7_2_466, List.forall_mem_cons.2 ⟨subd7_2_467, List.forall_mem_cons.2 ⟨subd7_2_468, List.forall_mem_cons.2 ⟨subd7_2_469, List.forall_mem_cons.2 ⟨subd7_2_470, List.forall_mem_cons.2 ⟨subd7_2_471, List.forall_mem_cons.2 ⟨subd7_2_472, List.forall_mem_cons.2 ⟨subd7_2_473, List.forall_mem_cons.2 ⟨subd7_2_474, List.forall_mem_cons.2 ⟨subd7_2_475, List.forall_mem_cons.2 ⟨subd7_2_476, List.forall_mem_cons.2 ⟨subd7_2_477, List.forall_mem_cons.2 ⟨subd7_2_478, List.forall_mem_cons.2 ⟨subd7_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_480 : subd7_2 [1, 2, 0] = true := by decide +kernel
theorem subd7_2_481 : subd7_2 [1, 2, 1] = true := by decide +kernel
theorem subd7_2_482 : subd7_2 [1, 2, 2] = true := by decide +kernel
theorem subd7_2_483 : subd7_2 [1, 2, 3] = true := by decide +kernel
theorem subd7_2_484 : subd7_2 [1, 2, 4] = true := by decide +kernel
theorem subd7_2_485 : subd7_2 [1, 2, 5] = true := by decide +kernel
theorem subd7_2_486 : subd7_2 [1, 2, 6] = true := by decide +kernel
theorem subd7_2_487 : subd7_2 [1, 2, 7] = true := by decide +kernel
theorem subd7_2_488 : subd7_2 [1, 2, 8] = true := by decide +kernel
theorem subd7_2_489 : subd7_2 [1, 3, -7] = true := by decide +kernel
theorem subd7_2_490 : subd7_2 [1, 3, -6] = true := by decide +kernel
theorem subd7_2_491 : subd7_2 [1, 3, -5] = true := by decide +kernel
theorem subd7_2_492 : subd7_2 [1, 3, -4] = true := by decide +kernel
theorem subd7_2_493 : subd7_2 [1, 3, -3] = true := by decide +kernel
theorem subd7_2_494 : subd7_2 [1, 3, -2] = true := by decide +kernel
theorem subd7_2_495 : subd7_2 [1, 3, -1] = true := by decide +kernel
theorem subd7_2_496 : subd7_2 [1, 3, 0] = true := by decide +kernel
theorem subd7_2_497 : subd7_2 [1, 3, 1] = true := by decide +kernel
theorem subd7_2_498 : subd7_2 [1, 3, 2] = true := by decide +kernel
theorem subd7_2_499 : subd7_2 [1, 3, 3] = true := by decide +kernel
theorem subd7_2_500 : subd7_2 [1, 3, 4] = true := by decide +kernel
theorem subd7_2_501 : subd7_2 [1, 3, 5] = true := by decide +kernel
theorem subd7_2_502 : subd7_2 [1, 3, 6] = true := by decide +kernel
theorem subd7_2_503 : subd7_2 [1, 3, 7] = true := by decide +kernel
theorem subd7_2_504 : subd7_2 [1, 4] = true := by decide +kernel
theorem subd7_2_505 : subd7_2 [2, -5] = true := by decide +kernel
theorem subd7_2_506 : subd7_2 [2, -4] = true := by decide +kernel
theorem subd7_2_507 : subd7_2 [2, -3] = true := by decide +kernel
theorem subd7_2_508 : subd7_2 [2, -2, -9] = true := by decide +kernel
theorem subd7_2_509 : subd7_2 [2, -2, -8] = true := by decide +kernel
theorem subd7_2_510 : subd7_2 [2, -2, -7] = true := by decide +kernel
theorem subd7_2_511 : subd7_2 [2, -2, -6] = true := by decide +kernel
theorem sbd7_2_15 : ∀ q ∈ blkd7_2_15, subd7_2 q = true := by
  unfold blkd7_2_15
  exact List.forall_mem_cons.2 ⟨subd7_2_480, List.forall_mem_cons.2 ⟨subd7_2_481, List.forall_mem_cons.2 ⟨subd7_2_482, List.forall_mem_cons.2 ⟨subd7_2_483, List.forall_mem_cons.2 ⟨subd7_2_484, List.forall_mem_cons.2 ⟨subd7_2_485, List.forall_mem_cons.2 ⟨subd7_2_486, List.forall_mem_cons.2 ⟨subd7_2_487, List.forall_mem_cons.2 ⟨subd7_2_488, List.forall_mem_cons.2 ⟨subd7_2_489, List.forall_mem_cons.2 ⟨subd7_2_490, List.forall_mem_cons.2 ⟨subd7_2_491, List.forall_mem_cons.2 ⟨subd7_2_492, List.forall_mem_cons.2 ⟨subd7_2_493, List.forall_mem_cons.2 ⟨subd7_2_494, List.forall_mem_cons.2 ⟨subd7_2_495, List.forall_mem_cons.2 ⟨subd7_2_496, List.forall_mem_cons.2 ⟨subd7_2_497, List.forall_mem_cons.2 ⟨subd7_2_498, List.forall_mem_cons.2 ⟨subd7_2_499, List.forall_mem_cons.2 ⟨subd7_2_500, List.forall_mem_cons.2 ⟨subd7_2_501, List.forall_mem_cons.2 ⟨subd7_2_502, List.forall_mem_cons.2 ⟨subd7_2_503, List.forall_mem_cons.2 ⟨subd7_2_504, List.forall_mem_cons.2 ⟨subd7_2_505, List.forall_mem_cons.2 ⟨subd7_2_506, List.forall_mem_cons.2 ⟨subd7_2_507, List.forall_mem_cons.2 ⟨subd7_2_508, List.forall_mem_cons.2 ⟨subd7_2_509, List.forall_mem_cons.2 ⟨subd7_2_510, List.forall_mem_cons.2 ⟨subd7_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_512 : subd7_2 [2, -2, -5] = true := by decide +kernel
theorem subd7_2_513 : subd7_2 [2, -2, -4] = true := by decide +kernel
theorem subd7_2_514 : subd7_2 [2, -2, -3] = true := by decide +kernel
theorem subd7_2_515 : subd7_2 [2, -2, -2] = true := by decide +kernel
theorem subd7_2_516 : subd7_2 [2, -2, -1] = true := by decide +kernel
theorem subd7_2_517 : subd7_2 [2, -2, 0] = true := by decide +kernel
theorem subd7_2_518 : subd7_2 [2, -2, 1] = true := by decide +kernel
theorem subd7_2_519 : subd7_2 [2, -2, 2] = true := by decide +kernel
theorem subd7_2_520 : subd7_2 [2, -2, 3] = true := by decide +kernel
theorem subd7_2_521 : subd7_2 [2, -2, 4] = true := by decide +kernel
theorem subd7_2_522 : subd7_2 [2, -2, 5] = true := by decide +kernel
theorem subd7_2_523 : subd7_2 [2, -1, -10] = true := by decide +kernel
theorem subd7_2_524 : subd7_2 [2, -1, -9] = true := by decide +kernel
theorem subd7_2_525 : subd7_2 [2, -1, -8] = true := by decide +kernel
theorem subd7_2_526 : subd7_2 [2, -1, -7] = true := by decide +kernel
theorem subd7_2_527 : subd7_2 [2, -1, -6] = true := by decide +kernel
theorem subd7_2_528 : subd7_2 [2, -1, -5] = true := by decide +kernel
theorem subd7_2_529 : subd7_2 [2, -1, -4] = true := by decide +kernel
theorem subd7_2_530 : subd7_2 [2, -1, -3] = true := by decide +kernel
theorem subd7_2_531 : subd7_2 [2, -1, -2] = true := by decide +kernel
theorem subd7_2_532 : subd7_2 [2, -1, -1] = true := by decide +kernel
theorem subd7_2_533 : subd7_2 [2, -1, 0] = true := by decide +kernel
theorem subd7_2_534 : subd7_2 [2, -1, 1] = true := by decide +kernel
theorem subd7_2_535 : subd7_2 [2, -1, 2] = true := by decide +kernel
theorem subd7_2_536 : subd7_2 [2, -1, 3] = true := by decide +kernel
theorem subd7_2_537 : subd7_2 [2, -1, 4] = true := by decide +kernel
theorem subd7_2_538 : subd7_2 [2, -1, 5] = true := by decide +kernel
theorem subd7_2_539 : subd7_2 [2, -1, 6] = true := by decide +kernel
theorem subd7_2_540 : subd7_2 [2, 0, -9] = true := by decide +kernel
theorem subd7_2_541 : subd7_2 [2, 0, -8] = true := by decide +kernel
theorem subd7_2_542 : subd7_2 [2, 0, -7] = true := by decide +kernel
theorem subd7_2_543 : subd7_2 [2, 0, -6] = true := by decide +kernel
theorem sbd7_2_16 : ∀ q ∈ blkd7_2_16, subd7_2 q = true := by
  unfold blkd7_2_16
  exact List.forall_mem_cons.2 ⟨subd7_2_512, List.forall_mem_cons.2 ⟨subd7_2_513, List.forall_mem_cons.2 ⟨subd7_2_514, List.forall_mem_cons.2 ⟨subd7_2_515, List.forall_mem_cons.2 ⟨subd7_2_516, List.forall_mem_cons.2 ⟨subd7_2_517, List.forall_mem_cons.2 ⟨subd7_2_518, List.forall_mem_cons.2 ⟨subd7_2_519, List.forall_mem_cons.2 ⟨subd7_2_520, List.forall_mem_cons.2 ⟨subd7_2_521, List.forall_mem_cons.2 ⟨subd7_2_522, List.forall_mem_cons.2 ⟨subd7_2_523, List.forall_mem_cons.2 ⟨subd7_2_524, List.forall_mem_cons.2 ⟨subd7_2_525, List.forall_mem_cons.2 ⟨subd7_2_526, List.forall_mem_cons.2 ⟨subd7_2_527, List.forall_mem_cons.2 ⟨subd7_2_528, List.forall_mem_cons.2 ⟨subd7_2_529, List.forall_mem_cons.2 ⟨subd7_2_530, List.forall_mem_cons.2 ⟨subd7_2_531, List.forall_mem_cons.2 ⟨subd7_2_532, List.forall_mem_cons.2 ⟨subd7_2_533, List.forall_mem_cons.2 ⟨subd7_2_534, List.forall_mem_cons.2 ⟨subd7_2_535, List.forall_mem_cons.2 ⟨subd7_2_536, List.forall_mem_cons.2 ⟨subd7_2_537, List.forall_mem_cons.2 ⟨subd7_2_538, List.forall_mem_cons.2 ⟨subd7_2_539, List.forall_mem_cons.2 ⟨subd7_2_540, List.forall_mem_cons.2 ⟨subd7_2_541, List.forall_mem_cons.2 ⟨subd7_2_542, List.forall_mem_cons.2 ⟨subd7_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_544 : subd7_2 [2, 0, -5] = true := by decide +kernel
theorem subd7_2_545 : subd7_2 [2, 0, -4] = true := by decide +kernel
theorem subd7_2_546 : subd7_2 [2, 0, -3] = true := by decide +kernel
theorem subd7_2_547 : subd7_2 [2, 0, -2] = true := by decide +kernel
theorem subd7_2_548 : subd7_2 [2, 0, -1] = true := by decide +kernel
theorem subd7_2_549 : subd7_2 [2, 0, 0] = true := by decide +kernel
theorem subd7_2_550 : subd7_2 [2, 0, 1] = true := by decide +kernel
theorem subd7_2_551 : subd7_2 [2, 0, 2] = true := by decide +kernel
theorem subd7_2_552 : subd7_2 [2, 0, 3] = true := by decide +kernel
theorem subd7_2_553 : subd7_2 [2, 0, 4] = true := by decide +kernel
theorem subd7_2_554 : subd7_2 [2, 0, 5] = true := by decide +kernel
theorem subd7_2_555 : subd7_2 [2, 0, 6] = true := by decide +kernel
theorem subd7_2_556 : subd7_2 [2, 0, 7] = true := by decide +kernel
theorem subd7_2_557 : subd7_2 [2, 1, -9] = true := by decide +kernel
theorem subd7_2_558 : subd7_2 [2, 1, -8] = true := by decide +kernel
theorem subd7_2_559 : subd7_2 [2, 1, -7] = true := by decide +kernel
theorem subd7_2_560 : subd7_2 [2, 1, -6] = true := by decide +kernel
theorem subd7_2_561 : subd7_2 [2, 1, -5] = true := by decide +kernel
theorem subd7_2_562 : subd7_2 [2, 1, -4] = true := by decide +kernel
theorem subd7_2_563 : subd7_2 [2, 1, -3] = true := by decide +kernel
theorem subd7_2_564 : subd7_2 [2, 1, -2] = true := by decide +kernel
theorem subd7_2_565 : subd7_2 [2, 1, -1] = true := by decide +kernel
theorem subd7_2_566 : subd7_2 [2, 1, 0] = true := by decide +kernel
theorem subd7_2_567 : subd7_2 [2, 1, 1] = true := by decide +kernel
theorem subd7_2_568 : subd7_2 [2, 1, 2] = true := by decide +kernel
theorem subd7_2_569 : subd7_2 [2, 1, 3] = true := by decide +kernel
theorem subd7_2_570 : subd7_2 [2, 1, 4] = true := by decide +kernel
theorem subd7_2_571 : subd7_2 [2, 1, 5] = true := by decide +kernel
theorem subd7_2_572 : subd7_2 [2, 1, 6] = true := by decide +kernel
theorem subd7_2_573 : subd7_2 [2, 1, 7] = true := by decide +kernel
theorem subd7_2_574 : subd7_2 [2, 2, -8] = true := by decide +kernel
theorem subd7_2_575 : subd7_2 [2, 2, -7] = true := by decide +kernel
theorem sbd7_2_17 : ∀ q ∈ blkd7_2_17, subd7_2 q = true := by
  unfold blkd7_2_17
  exact List.forall_mem_cons.2 ⟨subd7_2_544, List.forall_mem_cons.2 ⟨subd7_2_545, List.forall_mem_cons.2 ⟨subd7_2_546, List.forall_mem_cons.2 ⟨subd7_2_547, List.forall_mem_cons.2 ⟨subd7_2_548, List.forall_mem_cons.2 ⟨subd7_2_549, List.forall_mem_cons.2 ⟨subd7_2_550, List.forall_mem_cons.2 ⟨subd7_2_551, List.forall_mem_cons.2 ⟨subd7_2_552, List.forall_mem_cons.2 ⟨subd7_2_553, List.forall_mem_cons.2 ⟨subd7_2_554, List.forall_mem_cons.2 ⟨subd7_2_555, List.forall_mem_cons.2 ⟨subd7_2_556, List.forall_mem_cons.2 ⟨subd7_2_557, List.forall_mem_cons.2 ⟨subd7_2_558, List.forall_mem_cons.2 ⟨subd7_2_559, List.forall_mem_cons.2 ⟨subd7_2_560, List.forall_mem_cons.2 ⟨subd7_2_561, List.forall_mem_cons.2 ⟨subd7_2_562, List.forall_mem_cons.2 ⟨subd7_2_563, List.forall_mem_cons.2 ⟨subd7_2_564, List.forall_mem_cons.2 ⟨subd7_2_565, List.forall_mem_cons.2 ⟨subd7_2_566, List.forall_mem_cons.2 ⟨subd7_2_567, List.forall_mem_cons.2 ⟨subd7_2_568, List.forall_mem_cons.2 ⟨subd7_2_569, List.forall_mem_cons.2 ⟨subd7_2_570, List.forall_mem_cons.2 ⟨subd7_2_571, List.forall_mem_cons.2 ⟨subd7_2_572, List.forall_mem_cons.2 ⟨subd7_2_573, List.forall_mem_cons.2 ⟨subd7_2_574, List.forall_mem_cons.2 ⟨subd7_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
