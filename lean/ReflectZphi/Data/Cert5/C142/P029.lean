import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_2_128 : subd15_2 [-3, 0, -7] = true := by decide +kernel
theorem subd15_2_129 : subd15_2 [-3, 0, -6] = true := by decide +kernel
theorem subd15_2_130 : subd15_2 [-3, 0, -5] = true := by decide +kernel
theorem subd15_2_131 : subd15_2 [-3, 0, -4] = true := by decide +kernel
theorem subd15_2_132 : subd15_2 [-3, 0, -3] = true := by decide +kernel
theorem subd15_2_133 : subd15_2 [-3, 0, -2] = true := by decide +kernel
theorem subd15_2_134 : subd15_2 [-3, 0, -1] = true := by decide +kernel
theorem subd15_2_135 : subd15_2 [-3, 0, 0] = true := by decide +kernel
theorem subd15_2_136 : subd15_2 [-3, 0, 1] = true := by decide +kernel
theorem subd15_2_137 : subd15_2 [-3, 0, 2] = true := by decide +kernel
theorem subd15_2_138 : subd15_2 [-3, 0, 3] = true := by decide +kernel
theorem subd15_2_139 : subd15_2 [-3, 0, 4] = true := by decide +kernel
theorem subd15_2_140 : subd15_2 [-3, 0, 5] = true := by decide +kernel
theorem subd15_2_141 : subd15_2 [-3, 0, 6] = true := by decide +kernel
theorem subd15_2_142 : subd15_2 [-3, 1, -8] = true := by decide +kernel
theorem subd15_2_143 : subd15_2 [-3, 1, -7] = true := by decide +kernel
theorem subd15_2_144 : subd15_2 [-3, 1, -6] = true := by decide +kernel
theorem subd15_2_145 : subd15_2 [-3, 1, -5] = true := by decide +kernel
theorem subd15_2_146 : subd15_2 [-3, 1, -4] = true := by decide +kernel
theorem subd15_2_147 : subd15_2 [-3, 1, -3] = true := by decide +kernel
theorem subd15_2_148 : subd15_2 [-3, 1, -2] = true := by decide +kernel
theorem subd15_2_149 : subd15_2 [-3, 1, -1] = true := by decide +kernel
theorem subd15_2_150 : subd15_2 [-3, 1, 0] = true := by decide +kernel
theorem subd15_2_151 : subd15_2 [-3, 1, 1] = true := by decide +kernel
theorem subd15_2_152 : subd15_2 [-3, 1, 2] = true := by decide +kernel
theorem subd15_2_153 : subd15_2 [-3, 1, 3] = true := by decide +kernel
theorem subd15_2_154 : subd15_2 [-3, 1, 4] = true := by decide +kernel
theorem subd15_2_155 : subd15_2 [-3, 1, 5] = true := by decide +kernel
theorem subd15_2_156 : subd15_2 [-3, 1, 6] = true := by decide +kernel
theorem subd15_2_157 : subd15_2 [-3, 2] = true := by decide +kernel
theorem subd15_2_158 : subd15_2 [-3, 3] = true := by decide +kernel
theorem subd15_2_159 : subd15_2 [-3, 4] = true := by decide +kernel
theorem sbd15_2_4 : ∀ q ∈ blkd15_2_4, subd15_2 q = true := by
  unfold blkd15_2_4
  exact List.forall_mem_cons.2 ⟨subd15_2_128, List.forall_mem_cons.2 ⟨subd15_2_129, List.forall_mem_cons.2 ⟨subd15_2_130, List.forall_mem_cons.2 ⟨subd15_2_131, List.forall_mem_cons.2 ⟨subd15_2_132, List.forall_mem_cons.2 ⟨subd15_2_133, List.forall_mem_cons.2 ⟨subd15_2_134, List.forall_mem_cons.2 ⟨subd15_2_135, List.forall_mem_cons.2 ⟨subd15_2_136, List.forall_mem_cons.2 ⟨subd15_2_137, List.forall_mem_cons.2 ⟨subd15_2_138, List.forall_mem_cons.2 ⟨subd15_2_139, List.forall_mem_cons.2 ⟨subd15_2_140, List.forall_mem_cons.2 ⟨subd15_2_141, List.forall_mem_cons.2 ⟨subd15_2_142, List.forall_mem_cons.2 ⟨subd15_2_143, List.forall_mem_cons.2 ⟨subd15_2_144, List.forall_mem_cons.2 ⟨subd15_2_145, List.forall_mem_cons.2 ⟨subd15_2_146, List.forall_mem_cons.2 ⟨subd15_2_147, List.forall_mem_cons.2 ⟨subd15_2_148, List.forall_mem_cons.2 ⟨subd15_2_149, List.forall_mem_cons.2 ⟨subd15_2_150, List.forall_mem_cons.2 ⟨subd15_2_151, List.forall_mem_cons.2 ⟨subd15_2_152, List.forall_mem_cons.2 ⟨subd15_2_153, List.forall_mem_cons.2 ⟨subd15_2_154, List.forall_mem_cons.2 ⟨subd15_2_155, List.forall_mem_cons.2 ⟨subd15_2_156, List.forall_mem_cons.2 ⟨subd15_2_157, List.forall_mem_cons.2 ⟨subd15_2_158, List.forall_mem_cons.2 ⟨subd15_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_160 : subd15_2 [-2, -8] = true := by decide +kernel
theorem subd15_2_161 : subd15_2 [-2, -7] = true := by decide +kernel
theorem subd15_2_162 : subd15_2 [-2, -6] = true := by decide +kernel
theorem subd15_2_163 : subd15_2 [-2, -5, -8] = true := by decide +kernel
theorem subd15_2_164 : subd15_2 [-2, -5, -7] = true := by decide +kernel
theorem subd15_2_165 : subd15_2 [-2, -5, -6] = true := by decide +kernel
theorem subd15_2_166 : subd15_2 [-2, -5, -5] = true := by decide +kernel
theorem subd15_2_167 : subd15_2 [-2, -5, -4] = true := by decide +kernel
theorem subd15_2_168 : subd15_2 [-2, -5, -3] = true := by decide +kernel
theorem subd15_2_169 : subd15_2 [-2, -5, -2] = true := by decide +kernel
theorem subd15_2_170 : subd15_2 [-2, -5, -1] = true := by decide +kernel
theorem subd15_2_171 : subd15_2 [-2, -5, 0] = true := by decide +kernel
theorem subd15_2_172 : subd15_2 [-2, -5, 1] = true := by decide +kernel
theorem subd15_2_173 : subd15_2 [-2, -5, 2] = true := by decide +kernel
theorem subd15_2_174 : subd15_2 [-2, -5, 3] = true := by decide +kernel
theorem subd15_2_175 : subd15_2 [-2, -5, 4] = true := by decide +kernel
theorem subd15_2_176 : subd15_2 [-2, -5, 5] = true := by decide +kernel
theorem subd15_2_177 : subd15_2 [-2, -4, -9] = true := by decide +kernel
theorem subd15_2_178 : subd15_2 [-2, -4, -8] = true := by decide +kernel
theorem subd15_2_179 : subd15_2 [-2, -4, -7] = true := by decide +kernel
theorem subd15_2_180 : subd15_2 [-2, -4, -6] = true := by decide +kernel
theorem subd15_2_181 : subd15_2 [-2, -4, -5] = true := by decide +kernel
theorem subd15_2_182 : subd15_2 [-2, -4, -4] = true := by decide +kernel
theorem subd15_2_183 : subd15_2 [-2, -4, -3] = true := by decide +kernel
theorem subd15_2_184 : subd15_2 [-2, -4, -2] = true := by decide +kernel
theorem subd15_2_185 : subd15_2 [-2, -4, -1] = true := by decide +kernel
theorem subd15_2_186 : subd15_2 [-2, -4, 0] = true := by decide +kernel
theorem subd15_2_187 : subd15_2 [-2, -4, 1] = true := by decide +kernel
theorem subd15_2_188 : subd15_2 [-2, -4, 2] = true := by decide +kernel
theorem subd15_2_189 : subd15_2 [-2, -4, 3] = true := by decide +kernel
theorem subd15_2_190 : subd15_2 [-2, -4, 4] = true := by decide +kernel
theorem subd15_2_191 : subd15_2 [-2, -4, 5] = true := by decide +kernel
theorem sbd15_2_5 : ∀ q ∈ blkd15_2_5, subd15_2 q = true := by
  unfold blkd15_2_5
  exact List.forall_mem_cons.2 ⟨subd15_2_160, List.forall_mem_cons.2 ⟨subd15_2_161, List.forall_mem_cons.2 ⟨subd15_2_162, List.forall_mem_cons.2 ⟨subd15_2_163, List.forall_mem_cons.2 ⟨subd15_2_164, List.forall_mem_cons.2 ⟨subd15_2_165, List.forall_mem_cons.2 ⟨subd15_2_166, List.forall_mem_cons.2 ⟨subd15_2_167, List.forall_mem_cons.2 ⟨subd15_2_168, List.forall_mem_cons.2 ⟨subd15_2_169, List.forall_mem_cons.2 ⟨subd15_2_170, List.forall_mem_cons.2 ⟨subd15_2_171, List.forall_mem_cons.2 ⟨subd15_2_172, List.forall_mem_cons.2 ⟨subd15_2_173, List.forall_mem_cons.2 ⟨subd15_2_174, List.forall_mem_cons.2 ⟨subd15_2_175, List.forall_mem_cons.2 ⟨subd15_2_176, List.forall_mem_cons.2 ⟨subd15_2_177, List.forall_mem_cons.2 ⟨subd15_2_178, List.forall_mem_cons.2 ⟨subd15_2_179, List.forall_mem_cons.2 ⟨subd15_2_180, List.forall_mem_cons.2 ⟨subd15_2_181, List.forall_mem_cons.2 ⟨subd15_2_182, List.forall_mem_cons.2 ⟨subd15_2_183, List.forall_mem_cons.2 ⟨subd15_2_184, List.forall_mem_cons.2 ⟨subd15_2_185, List.forall_mem_cons.2 ⟨subd15_2_186, List.forall_mem_cons.2 ⟨subd15_2_187, List.forall_mem_cons.2 ⟨subd15_2_188, List.forall_mem_cons.2 ⟨subd15_2_189, List.forall_mem_cons.2 ⟨subd15_2_190, List.forall_mem_cons.2 ⟨subd15_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_192 : subd15_2 [-2, -4, 6] = true := by decide +kernel
theorem subd15_2_193 : subd15_2 [-2, -3, -9] = true := by decide +kernel
theorem subd15_2_194 : subd15_2 [-2, -3, -8] = true := by decide +kernel
theorem subd15_2_195 : subd15_2 [-2, -3, -7] = true := by decide +kernel
theorem subd15_2_196 : subd15_2 [-2, -3, -6] = true := by decide +kernel
theorem subd15_2_197 : subd15_2 [-2, -3, -5] = true := by decide +kernel
theorem subd15_2_198 : subd15_2 [-2, -3, -4] = true := by decide +kernel
theorem subd15_2_199 : subd15_2 [-2, -3, -3] = true := by decide +kernel
theorem subd15_2_200 : subd15_2 [-2, -3, -2] = true := by decide +kernel
theorem subd15_2_201 : subd15_2 [-2, -3, -1] = true := by decide +kernel
theorem subd15_2_202 : subd15_2 [-2, -3, 0] = true := by decide +kernel
theorem subd15_2_203 : subd15_2 [-2, -3, 1] = true := by decide +kernel
theorem subd15_2_204 : subd15_2 [-2, -3, 2] = true := by decide +kernel
theorem subd15_2_205 : subd15_2 [-2, -3, 3] = true := by decide +kernel
theorem subd15_2_206 : subd15_2 [-2, -3, 4] = true := by decide +kernel
theorem subd15_2_207 : subd15_2 [-2, -3, 5] = true := by decide +kernel
theorem subd15_2_208 : subd15_2 [-2, -3, 6] = true := by decide +kernel
theorem subd15_2_209 : subd15_2 [-2, -3, 7] = true := by decide +kernel
theorem subd15_2_210 : subd15_2 [-2, -2, -9] = true := by decide +kernel
theorem subd15_2_211 : subd15_2 [-2, -2, -8] = true := by decide +kernel
theorem subd15_2_212 : subd15_2 [-2, -2, -7] = true := by decide +kernel
theorem subd15_2_213 : subd15_2 [-2, -2, -6] = true := by decide +kernel
theorem subd15_2_214 : subd15_2 [-2, -2, -5] = true := by decide +kernel
theorem subd15_2_215 : subd15_2 [-2, -2, -4] = true := by decide +kernel
theorem subd15_2_216 : subd15_2 [-2, -2, -3] = true := by decide +kernel
theorem subd15_2_217 : subd15_2 [-2, -2, -2] = true := by decide +kernel
theorem subd15_2_218 : subd15_2 [-2, -2, -1] = true := by decide +kernel
theorem subd15_2_219 : subd15_2 [-2, -2, 0] = true := by decide +kernel
theorem subd15_2_220 : subd15_2 [-2, -2, 1] = true := by decide +kernel
theorem subd15_2_221 : subd15_2 [-2, -2, 2] = true := by decide +kernel
theorem subd15_2_222 : subd15_2 [-2, -2, 3] = true := by decide +kernel
theorem subd15_2_223 : subd15_2 [-2, -2, 4] = true := by decide +kernel
theorem sbd15_2_6 : ∀ q ∈ blkd15_2_6, subd15_2 q = true := by
  unfold blkd15_2_6
  exact List.forall_mem_cons.2 ⟨subd15_2_192, List.forall_mem_cons.2 ⟨subd15_2_193, List.forall_mem_cons.2 ⟨subd15_2_194, List.forall_mem_cons.2 ⟨subd15_2_195, List.forall_mem_cons.2 ⟨subd15_2_196, List.forall_mem_cons.2 ⟨subd15_2_197, List.forall_mem_cons.2 ⟨subd15_2_198, List.forall_mem_cons.2 ⟨subd15_2_199, List.forall_mem_cons.2 ⟨subd15_2_200, List.forall_mem_cons.2 ⟨subd15_2_201, List.forall_mem_cons.2 ⟨subd15_2_202, List.forall_mem_cons.2 ⟨subd15_2_203, List.forall_mem_cons.2 ⟨subd15_2_204, List.forall_mem_cons.2 ⟨subd15_2_205, List.forall_mem_cons.2 ⟨subd15_2_206, List.forall_mem_cons.2 ⟨subd15_2_207, List.forall_mem_cons.2 ⟨subd15_2_208, List.forall_mem_cons.2 ⟨subd15_2_209, List.forall_mem_cons.2 ⟨subd15_2_210, List.forall_mem_cons.2 ⟨subd15_2_211, List.forall_mem_cons.2 ⟨subd15_2_212, List.forall_mem_cons.2 ⟨subd15_2_213, List.forall_mem_cons.2 ⟨subd15_2_214, List.forall_mem_cons.2 ⟨subd15_2_215, List.forall_mem_cons.2 ⟨subd15_2_216, List.forall_mem_cons.2 ⟨subd15_2_217, List.forall_mem_cons.2 ⟨subd15_2_218, List.forall_mem_cons.2 ⟨subd15_2_219, List.forall_mem_cons.2 ⟨subd15_2_220, List.forall_mem_cons.2 ⟨subd15_2_221, List.forall_mem_cons.2 ⟨subd15_2_222, List.forall_mem_cons.2 ⟨subd15_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_224 : subd15_2 [-2, -2, 5] = true := by decide +kernel
theorem subd15_2_225 : subd15_2 [-2, -2, 6] = true := by decide +kernel
theorem subd15_2_226 : subd15_2 [-2, -2, 7] = true := by decide +kernel
theorem subd15_2_227 : subd15_2 [-2, -1, -10] = true := by decide +kernel
theorem subd15_2_228 : subd15_2 [-2, -1, -9] = true := by decide +kernel
theorem subd15_2_229 : subd15_2 [-2, -1, -8] = true := by decide +kernel
theorem subd15_2_230 : subd15_2 [-2, -1, -7] = true := by decide +kernel
theorem subd15_2_231 : subd15_2 [-2, -1, -6] = true := by decide +kernel
theorem subd15_2_232 : subd15_2 [-2, -1, -5] = true := by decide +kernel
theorem subd15_2_233 : subd15_2 [-2, -1, -4] = true := by decide +kernel
theorem subd15_2_234 : subd15_2 [-2, -1, -3] = true := by decide +kernel
theorem subd15_2_235 : subd15_2 [-2, -1, -2] = true := by decide +kernel
theorem subd15_2_236 : subd15_2 [-2, -1, -1] = true := by decide +kernel
theorem subd15_2_237 : subd15_2 [-2, -1, 0] = true := by decide +kernel
theorem subd15_2_238 : subd15_2 [-2, -1, 1] = true := by decide +kernel
theorem subd15_2_239 : subd15_2 [-2, -1, 2] = true := by decide +kernel
theorem subd15_2_240 : subd15_2 [-2, -1, 3] = true := by decide +kernel
theorem subd15_2_241 : subd15_2 [-2, -1, 4] = true := by decide +kernel
theorem subd15_2_242 : subd15_2 [-2, -1, 5] = true := by decide +kernel
theorem subd15_2_243 : subd15_2 [-2, -1, 6] = true := by decide +kernel
theorem subd15_2_244 : subd15_2 [-2, -1, 7] = true := by decide +kernel
theorem subd15_2_245 : subd15_2 [-2, 0, -9] = true := by decide +kernel
theorem subd15_2_246 : subd15_2 [-2, 0, -8] = true := by decide +kernel
theorem subd15_2_247 : subd15_2 [-2, 0, -7] = true := by decide +kernel
theorem subd15_2_248 : subd15_2 [-2, 0, -6] = true := by decide +kernel
theorem subd15_2_249 : subd15_2 [-2, 0, -5] = true := by decide +kernel
theorem subd15_2_250 : subd15_2 [-2, 0, -4] = true := by decide +kernel
theorem subd15_2_251 : subd15_2 [-2, 0, -3] = true := by decide +kernel
theorem subd15_2_252 : subd15_2 [-2, 0, -2] = true := by decide +kernel
theorem subd15_2_253 : subd15_2 [-2, 0, -1] = true := by decide +kernel
theorem subd15_2_254 : subd15_2 [-2, 0, 0] = true := by decide +kernel
theorem subd15_2_255 : subd15_2 [-2, 0, 1] = true := by decide +kernel
theorem sbd15_2_7 : ∀ q ∈ blkd15_2_7, subd15_2 q = true := by
  unfold blkd15_2_7
  exact List.forall_mem_cons.2 ⟨subd15_2_224, List.forall_mem_cons.2 ⟨subd15_2_225, List.forall_mem_cons.2 ⟨subd15_2_226, List.forall_mem_cons.2 ⟨subd15_2_227, List.forall_mem_cons.2 ⟨subd15_2_228, List.forall_mem_cons.2 ⟨subd15_2_229, List.forall_mem_cons.2 ⟨subd15_2_230, List.forall_mem_cons.2 ⟨subd15_2_231, List.forall_mem_cons.2 ⟨subd15_2_232, List.forall_mem_cons.2 ⟨subd15_2_233, List.forall_mem_cons.2 ⟨subd15_2_234, List.forall_mem_cons.2 ⟨subd15_2_235, List.forall_mem_cons.2 ⟨subd15_2_236, List.forall_mem_cons.2 ⟨subd15_2_237, List.forall_mem_cons.2 ⟨subd15_2_238, List.forall_mem_cons.2 ⟨subd15_2_239, List.forall_mem_cons.2 ⟨subd15_2_240, List.forall_mem_cons.2 ⟨subd15_2_241, List.forall_mem_cons.2 ⟨subd15_2_242, List.forall_mem_cons.2 ⟨subd15_2_243, List.forall_mem_cons.2 ⟨subd15_2_244, List.forall_mem_cons.2 ⟨subd15_2_245, List.forall_mem_cons.2 ⟨subd15_2_246, List.forall_mem_cons.2 ⟨subd15_2_247, List.forall_mem_cons.2 ⟨subd15_2_248, List.forall_mem_cons.2 ⟨subd15_2_249, List.forall_mem_cons.2 ⟨subd15_2_250, List.forall_mem_cons.2 ⟨subd15_2_251, List.forall_mem_cons.2 ⟨subd15_2_252, List.forall_mem_cons.2 ⟨subd15_2_253, List.forall_mem_cons.2 ⟨subd15_2_254, List.forall_mem_cons.2 ⟨subd15_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_256 : subd15_2 [-2, 0, 2] = true := by decide +kernel
theorem subd15_2_257 : subd15_2 [-2, 0, 3] = true := by decide +kernel
theorem subd15_2_258 : subd15_2 [-2, 0, 4] = true := by decide +kernel
theorem subd15_2_259 : subd15_2 [-2, 0, 5] = true := by decide +kernel
theorem subd15_2_260 : subd15_2 [-2, 0, 6] = true := by decide +kernel
theorem subd15_2_261 : subd15_2 [-2, 0, 7] = true := by decide +kernel
theorem subd15_2_262 : subd15_2 [-2, 1, -9] = true := by decide +kernel
theorem subd15_2_263 : subd15_2 [-2, 1, -8] = true := by decide +kernel
theorem subd15_2_264 : subd15_2 [-2, 1, -7] = true := by decide +kernel
theorem subd15_2_265 : subd15_2 [-2, 1, -6] = true := by decide +kernel
theorem subd15_2_266 : subd15_2 [-2, 1, -5] = true := by decide +kernel
theorem subd15_2_267 : subd15_2 [-2, 1, -4] = true := by decide +kernel
theorem subd15_2_268 : subd15_2 [-2, 1, -3] = true := by decide +kernel
theorem subd15_2_269 : subd15_2 [-2, 1, -2] = true := by decide +kernel
theorem subd15_2_270 : subd15_2 [-2, 1, -1] = true := by decide +kernel
theorem subd15_2_271 : subd15_2 [-2, 1, 0] = true := by decide +kernel
theorem subd15_2_272 : subd15_2 [-2, 1, 1] = true := by decide +kernel
theorem subd15_2_273 : subd15_2 [-2, 1, 2] = true := by decide +kernel
theorem subd15_2_274 : subd15_2 [-2, 1, 3] = true := by decide +kernel
theorem subd15_2_275 : subd15_2 [-2, 1, 4] = true := by decide +kernel
theorem subd15_2_276 : subd15_2 [-2, 1, 5] = true := by decide +kernel
theorem subd15_2_277 : subd15_2 [-2, 1, 6] = true := by decide +kernel
theorem subd15_2_278 : subd15_2 [-2, 1, 7] = true := by decide +kernel
theorem subd15_2_279 : subd15_2 [-2, 2, -8] = true := by decide +kernel
theorem subd15_2_280 : subd15_2 [-2, 2, -7] = true := by decide +kernel
theorem subd15_2_281 : subd15_2 [-2, 2, -6] = true := by decide +kernel
theorem subd15_2_282 : subd15_2 [-2, 2, -5] = true := by decide +kernel
theorem subd15_2_283 : subd15_2 [-2, 2, -4] = true := by decide +kernel
theorem subd15_2_284 : subd15_2 [-2, 2, -3] = true := by decide +kernel
theorem subd15_2_285 : subd15_2 [-2, 2, -2] = true := by decide +kernel
theorem subd15_2_286 : subd15_2 [-2, 2, -1] = true := by decide +kernel
theorem subd15_2_287 : subd15_2 [-2, 2, 0] = true := by decide +kernel
theorem sbd15_2_8 : ∀ q ∈ blkd15_2_8, subd15_2 q = true := by
  unfold blkd15_2_8
  exact List.forall_mem_cons.2 ⟨subd15_2_256, List.forall_mem_cons.2 ⟨subd15_2_257, List.forall_mem_cons.2 ⟨subd15_2_258, List.forall_mem_cons.2 ⟨subd15_2_259, List.forall_mem_cons.2 ⟨subd15_2_260, List.forall_mem_cons.2 ⟨subd15_2_261, List.forall_mem_cons.2 ⟨subd15_2_262, List.forall_mem_cons.2 ⟨subd15_2_263, List.forall_mem_cons.2 ⟨subd15_2_264, List.forall_mem_cons.2 ⟨subd15_2_265, List.forall_mem_cons.2 ⟨subd15_2_266, List.forall_mem_cons.2 ⟨subd15_2_267, List.forall_mem_cons.2 ⟨subd15_2_268, List.forall_mem_cons.2 ⟨subd15_2_269, List.forall_mem_cons.2 ⟨subd15_2_270, List.forall_mem_cons.2 ⟨subd15_2_271, List.forall_mem_cons.2 ⟨subd15_2_272, List.forall_mem_cons.2 ⟨subd15_2_273, List.forall_mem_cons.2 ⟨subd15_2_274, List.forall_mem_cons.2 ⟨subd15_2_275, List.forall_mem_cons.2 ⟨subd15_2_276, List.forall_mem_cons.2 ⟨subd15_2_277, List.forall_mem_cons.2 ⟨subd15_2_278, List.forall_mem_cons.2 ⟨subd15_2_279, List.forall_mem_cons.2 ⟨subd15_2_280, List.forall_mem_cons.2 ⟨subd15_2_281, List.forall_mem_cons.2 ⟨subd15_2_282, List.forall_mem_cons.2 ⟨subd15_2_283, List.forall_mem_cons.2 ⟨subd15_2_284, List.forall_mem_cons.2 ⟨subd15_2_285, List.forall_mem_cons.2 ⟨subd15_2_286, List.forall_mem_cons.2 ⟨subd15_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_288 : subd15_2 [-2, 2, 1] = true := by decide +kernel
theorem subd15_2_289 : subd15_2 [-2, 2, 2] = true := by decide +kernel
theorem subd15_2_290 : subd15_2 [-2, 2, 3] = true := by decide +kernel
theorem subd15_2_291 : subd15_2 [-2, 2, 4] = true := by decide +kernel
theorem subd15_2_292 : subd15_2 [-2, 2, 5] = true := by decide +kernel
theorem subd15_2_293 : subd15_2 [-2, 2, 6] = true := by decide +kernel
theorem subd15_2_294 : subd15_2 [-2, 2, 7] = true := by decide +kernel
theorem subd15_2_295 : subd15_2 [-2, 3, -7] = true := by decide +kernel
theorem subd15_2_296 : subd15_2 [-2, 3, -6] = true := by decide +kernel
theorem subd15_2_297 : subd15_2 [-2, 3, -5] = true := by decide +kernel
theorem subd15_2_298 : subd15_2 [-2, 3, -4] = true := by decide +kernel
theorem subd15_2_299 : subd15_2 [-2, 3, -3] = true := by decide +kernel
theorem subd15_2_300 : subd15_2 [-2, 3, -2] = true := by decide +kernel
theorem subd15_2_301 : subd15_2 [-2, 3, -1] = true := by decide +kernel
theorem subd15_2_302 : subd15_2 [-2, 3, 0] = true := by decide +kernel
theorem subd15_2_303 : subd15_2 [-2, 3, 1] = true := by decide +kernel
theorem subd15_2_304 : subd15_2 [-2, 3, 2] = true := by decide +kernel
theorem subd15_2_305 : subd15_2 [-2, 3, 3] = true := by decide +kernel
theorem subd15_2_306 : subd15_2 [-2, 3, 4] = true := by decide +kernel
theorem subd15_2_307 : subd15_2 [-2, 3, 5] = true := by decide +kernel
theorem subd15_2_308 : subd15_2 [-2, 3, 6] = true := by decide +kernel
theorem subd15_2_309 : subd15_2 [-2, 4] = true := by decide +kernel
theorem subd15_2_310 : subd15_2 [-2, 5] = true := by decide +kernel
theorem subd15_2_311 : subd15_2 [-1, -8] = true := by decide +kernel
theorem subd15_2_312 : subd15_2 [-1, -7] = true := by decide +kernel
theorem subd15_2_313 : subd15_2 [-1, -6] = true := by decide +kernel
theorem subd15_2_314 : subd15_2 [-1, -5, -7] = true := by decide +kernel
theorem subd15_2_315 : subd15_2 [-1, -5, -6] = true := by decide +kernel
theorem subd15_2_316 : subd15_2 [-1, -5, -5] = true := by decide +kernel
theorem subd15_2_317 : subd15_2 [-1, -5, -4] = true := by decide +kernel
theorem subd15_2_318 : subd15_2 [-1, -5, -3] = true := by decide +kernel
theorem subd15_2_319 : subd15_2 [-1, -5, -2] = true := by decide +kernel
theorem sbd15_2_9 : ∀ q ∈ blkd15_2_9, subd15_2 q = true := by
  unfold blkd15_2_9
  exact List.forall_mem_cons.2 ⟨subd15_2_288, List.forall_mem_cons.2 ⟨subd15_2_289, List.forall_mem_cons.2 ⟨subd15_2_290, List.forall_mem_cons.2 ⟨subd15_2_291, List.forall_mem_cons.2 ⟨subd15_2_292, List.forall_mem_cons.2 ⟨subd15_2_293, List.forall_mem_cons.2 ⟨subd15_2_294, List.forall_mem_cons.2 ⟨subd15_2_295, List.forall_mem_cons.2 ⟨subd15_2_296, List.forall_mem_cons.2 ⟨subd15_2_297, List.forall_mem_cons.2 ⟨subd15_2_298, List.forall_mem_cons.2 ⟨subd15_2_299, List.forall_mem_cons.2 ⟨subd15_2_300, List.forall_mem_cons.2 ⟨subd15_2_301, List.forall_mem_cons.2 ⟨subd15_2_302, List.forall_mem_cons.2 ⟨subd15_2_303, List.forall_mem_cons.2 ⟨subd15_2_304, List.forall_mem_cons.2 ⟨subd15_2_305, List.forall_mem_cons.2 ⟨subd15_2_306, List.forall_mem_cons.2 ⟨subd15_2_307, List.forall_mem_cons.2 ⟨subd15_2_308, List.forall_mem_cons.2 ⟨subd15_2_309, List.forall_mem_cons.2 ⟨subd15_2_310, List.forall_mem_cons.2 ⟨subd15_2_311, List.forall_mem_cons.2 ⟨subd15_2_312, List.forall_mem_cons.2 ⟨subd15_2_313, List.forall_mem_cons.2 ⟨subd15_2_314, List.forall_mem_cons.2 ⟨subd15_2_315, List.forall_mem_cons.2 ⟨subd15_2_316, List.forall_mem_cons.2 ⟨subd15_2_317, List.forall_mem_cons.2 ⟨subd15_2_318, List.forall_mem_cons.2 ⟨subd15_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_320 : subd15_2 [-1, -5, -1] = true := by decide +kernel
theorem subd15_2_321 : subd15_2 [-1, -5, 0] = true := by decide +kernel
theorem subd15_2_322 : subd15_2 [-1, -5, 1] = true := by decide +kernel
theorem subd15_2_323 : subd15_2 [-1, -5, 2] = true := by decide +kernel
theorem subd15_2_324 : subd15_2 [-1, -5, 3] = true := by decide +kernel
theorem subd15_2_325 : subd15_2 [-1, -5, 4] = true := by decide +kernel
theorem subd15_2_326 : subd15_2 [-1, -5, 5] = true := by decide +kernel
theorem subd15_2_327 : subd15_2 [-1, -5, 6] = true := by decide +kernel
theorem subd15_2_328 : subd15_2 [-1, -4, -8] = true := by decide +kernel
theorem subd15_2_329 : subd15_2 [-1, -4, -7] = true := by decide +kernel
theorem subd15_2_330 : subd15_2 [-1, -4, -6] = true := by decide +kernel
theorem subd15_2_331 : subd15_2 [-1, -4, -5] = true := by decide +kernel
theorem subd15_2_332 : subd15_2 [-1, -4, -4] = true := by decide +kernel
theorem subd15_2_333 : subd15_2 [-1, -4, -3] = true := by decide +kernel
theorem subd15_2_334 : subd15_2 [-1, -4, -2] = true := by decide +kernel
theorem subd15_2_335 : subd15_2 [-1, -4, -1] = true := by decide +kernel
theorem subd15_2_336 : subd15_2 [-1, -4, 0] = true := by decide +kernel
theorem subd15_2_337 : subd15_2 [-1, -4, 1] = true := by decide +kernel
theorem subd15_2_338 : subd15_2 [-1, -4, 2] = true := by decide +kernel
theorem subd15_2_339 : subd15_2 [-1, -4, 3] = true := by decide +kernel
theorem subd15_2_340 : subd15_2 [-1, -4, 4] = true := by decide +kernel
theorem subd15_2_341 : subd15_2 [-1, -4, 5] = true := by decide +kernel
theorem subd15_2_342 : subd15_2 [-1, -4, 6] = true := by decide +kernel
theorem subd15_2_343 : subd15_2 [-1, -4, 7] = true := by decide +kernel
theorem subd15_2_344 : subd15_2 [-1, -3, -9] = true := by decide +kernel
theorem subd15_2_345 : subd15_2 [-1, -3, -8] = true := by decide +kernel
theorem subd15_2_346 : subd15_2 [-1, -3, -7] = true := by decide +kernel
theorem subd15_2_347 : subd15_2 [-1, -3, -6] = true := by decide +kernel
theorem subd15_2_348 : subd15_2 [-1, -3, -5] = true := by decide +kernel
theorem subd15_2_349 : subd15_2 [-1, -3, -4] = true := by decide +kernel
theorem subd15_2_350 : subd15_2 [-1, -3, -3] = true := by decide +kernel
theorem subd15_2_351 : subd15_2 [-1, -3, -2] = true := by decide +kernel
theorem sbd15_2_10 : ∀ q ∈ blkd15_2_10, subd15_2 q = true := by
  unfold blkd15_2_10
  exact List.forall_mem_cons.2 ⟨subd15_2_320, List.forall_mem_cons.2 ⟨subd15_2_321, List.forall_mem_cons.2 ⟨subd15_2_322, List.forall_mem_cons.2 ⟨subd15_2_323, List.forall_mem_cons.2 ⟨subd15_2_324, List.forall_mem_cons.2 ⟨subd15_2_325, List.forall_mem_cons.2 ⟨subd15_2_326, List.forall_mem_cons.2 ⟨subd15_2_327, List.forall_mem_cons.2 ⟨subd15_2_328, List.forall_mem_cons.2 ⟨subd15_2_329, List.forall_mem_cons.2 ⟨subd15_2_330, List.forall_mem_cons.2 ⟨subd15_2_331, List.forall_mem_cons.2 ⟨subd15_2_332, List.forall_mem_cons.2 ⟨subd15_2_333, List.forall_mem_cons.2 ⟨subd15_2_334, List.forall_mem_cons.2 ⟨subd15_2_335, List.forall_mem_cons.2 ⟨subd15_2_336, List.forall_mem_cons.2 ⟨subd15_2_337, List.forall_mem_cons.2 ⟨subd15_2_338, List.forall_mem_cons.2 ⟨subd15_2_339, List.forall_mem_cons.2 ⟨subd15_2_340, List.forall_mem_cons.2 ⟨subd15_2_341, List.forall_mem_cons.2 ⟨subd15_2_342, List.forall_mem_cons.2 ⟨subd15_2_343, List.forall_mem_cons.2 ⟨subd15_2_344, List.forall_mem_cons.2 ⟨subd15_2_345, List.forall_mem_cons.2 ⟨subd15_2_346, List.forall_mem_cons.2 ⟨subd15_2_347, List.forall_mem_cons.2 ⟨subd15_2_348, List.forall_mem_cons.2 ⟨subd15_2_349, List.forall_mem_cons.2 ⟨subd15_2_350, List.forall_mem_cons.2 ⟨subd15_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_352 : subd15_2 [-1, -3, -1] = true := by decide +kernel
theorem subd15_2_353 : subd15_2 [-1, -3, 0] = true := by decide +kernel
theorem subd15_2_354 : subd15_2 [-1, -3, 1] = true := by decide +kernel
theorem subd15_2_355 : subd15_2 [-1, -3, 2] = true := by decide +kernel
theorem subd15_2_356 : subd15_2 [-1, -3, 3] = true := by decide +kernel
theorem subd15_2_357 : subd15_2 [-1, -3, 4] = true := by decide +kernel
theorem subd15_2_358 : subd15_2 [-1, -3, 5] = true := by decide +kernel
theorem subd15_2_359 : subd15_2 [-1, -3, 6] = true := by decide +kernel
theorem subd15_2_360 : subd15_2 [-1, -3, 7] = true := by decide +kernel
theorem subd15_2_361 : subd15_2 [-1, -2, -9] = true := by decide +kernel
theorem subd15_2_362 : subd15_2 [-1, -2, -8] = true := by decide +kernel
theorem subd15_2_363 : subd15_2 [-1, -2, -7] = true := by decide +kernel
theorem subd15_2_364 : subd15_2 [-1, -2, -6] = true := by decide +kernel
theorem subd15_2_365 : subd15_2 [-1, -2, -5] = true := by decide +kernel
theorem subd15_2_366 : subd15_2 [-1, -2, -4] = true := by decide +kernel
theorem subd15_2_367 : subd15_2 [-1, -2, -3] = true := by decide +kernel
theorem subd15_2_368 : subd15_2 [-1, -2, -2] = true := by decide +kernel
theorem subd15_2_369 : subd15_2 [-1, -2, -1] = true := by decide +kernel
theorem subd15_2_370 : subd15_2 [-1, -2, 0] = true := by decide +kernel
theorem subd15_2_371 : subd15_2 [-1, -2, 1] = true := by decide +kernel
theorem subd15_2_372 : subd15_2 [-1, -2, 2] = true := by decide +kernel
theorem subd15_2_373 : subd15_2 [-1, -2, 3] = true := by decide +kernel
theorem subd15_2_374 : subd15_2 [-1, -2, 4] = true := by decide +kernel
theorem subd15_2_375 : subd15_2 [-1, -2, 5] = true := by decide +kernel
theorem subd15_2_376 : subd15_2 [-1, -2, 6] = true := by decide +kernel
theorem subd15_2_377 : subd15_2 [-1, -2, 7] = true := by decide +kernel
theorem subd15_2_378 : subd15_2 [-1, -2, 8] = true := by decide +kernel
theorem subd15_2_379 : subd15_2 [-1, -1, -10] = true := by decide +kernel
theorem subd15_2_380 : subd15_2 [-1, -1, -9] = true := by decide +kernel
theorem subd15_2_381 : subd15_2 [-1, -1, -8] = true := by decide +kernel
theorem subd15_2_382 : subd15_2 [-1, -1, -7] = true := by decide +kernel
theorem subd15_2_383 : subd15_2 [-1, -1, -6] = true := by decide +kernel
theorem sbd15_2_11 : ∀ q ∈ blkd15_2_11, subd15_2 q = true := by
  unfold blkd15_2_11
  exact List.forall_mem_cons.2 ⟨subd15_2_352, List.forall_mem_cons.2 ⟨subd15_2_353, List.forall_mem_cons.2 ⟨subd15_2_354, List.forall_mem_cons.2 ⟨subd15_2_355, List.forall_mem_cons.2 ⟨subd15_2_356, List.forall_mem_cons.2 ⟨subd15_2_357, List.forall_mem_cons.2 ⟨subd15_2_358, List.forall_mem_cons.2 ⟨subd15_2_359, List.forall_mem_cons.2 ⟨subd15_2_360, List.forall_mem_cons.2 ⟨subd15_2_361, List.forall_mem_cons.2 ⟨subd15_2_362, List.forall_mem_cons.2 ⟨subd15_2_363, List.forall_mem_cons.2 ⟨subd15_2_364, List.forall_mem_cons.2 ⟨subd15_2_365, List.forall_mem_cons.2 ⟨subd15_2_366, List.forall_mem_cons.2 ⟨subd15_2_367, List.forall_mem_cons.2 ⟨subd15_2_368, List.forall_mem_cons.2 ⟨subd15_2_369, List.forall_mem_cons.2 ⟨subd15_2_370, List.forall_mem_cons.2 ⟨subd15_2_371, List.forall_mem_cons.2 ⟨subd15_2_372, List.forall_mem_cons.2 ⟨subd15_2_373, List.forall_mem_cons.2 ⟨subd15_2_374, List.forall_mem_cons.2 ⟨subd15_2_375, List.forall_mem_cons.2 ⟨subd15_2_376, List.forall_mem_cons.2 ⟨subd15_2_377, List.forall_mem_cons.2 ⟨subd15_2_378, List.forall_mem_cons.2 ⟨subd15_2_379, List.forall_mem_cons.2 ⟨subd15_2_380, List.forall_mem_cons.2 ⟨subd15_2_381, List.forall_mem_cons.2 ⟨subd15_2_382, List.forall_mem_cons.2 ⟨subd15_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_384 : subd15_2 [-1, -1, -5] = true := by decide +kernel
theorem subd15_2_385 : subd15_2 [-1, -1, -4] = true := by decide +kernel
theorem subd15_2_386 : subd15_2 [-1, -1, -3] = true := by decide +kernel
theorem subd15_2_387 : subd15_2 [-1, -1, -2] = true := by decide +kernel
theorem subd15_2_388 : subd15_2 [-1, -1, -1] = true := by decide +kernel
theorem subd15_2_389 : subd15_2 [-1, -1, 0] = true := by decide +kernel
theorem subd15_2_390 : subd15_2 [-1, -1, 1] = true := by decide +kernel
theorem subd15_2_391 : subd15_2 [-1, -1, 2] = true := by decide +kernel
theorem subd15_2_392 : subd15_2 [-1, -1, 3] = true := by decide +kernel
theorem subd15_2_393 : subd15_2 [-1, -1, 4] = true := by decide +kernel
theorem subd15_2_394 : subd15_2 [-1, -1, 5] = true := by decide +kernel
theorem subd15_2_395 : subd15_2 [-1, -1, 6] = true := by decide +kernel
theorem subd15_2_396 : subd15_2 [-1, -1, 7] = true := by decide +kernel
theorem subd15_2_397 : subd15_2 [-1, -1, 8] = true := by decide +kernel
theorem subd15_2_398 : subd15_2 [-1, 0, -10] = true := by decide +kernel
theorem subd15_2_399 : subd15_2 [-1, 0, -9] = true := by decide +kernel
theorem subd15_2_400 : subd15_2 [-1, 0, -8] = true := by decide +kernel
theorem subd15_2_401 : subd15_2 [-1, 0, -7] = true := by decide +kernel
theorem subd15_2_402 : subd15_2 [-1, 0, -6] = true := by decide +kernel
theorem subd15_2_403 : subd15_2 [-1, 0, -5] = true := by decide +kernel
theorem subd15_2_404 : subd15_2 [-1, 0, -4] = true := by decide +kernel
theorem subd15_2_405 : subd15_2 [-1, 0, -3] = true := by decide +kernel
theorem subd15_2_406 : subd15_2 [-1, 0, -2] = true := by decide +kernel
theorem subd15_2_407 : subd15_2 [-1, 0, -1] = true := by decide +kernel
theorem subd15_2_408 : subd15_2 [-1, 0, 0] = true := by decide +kernel
theorem subd15_2_409 : subd15_2 [-1, 0, 1] = true := by decide +kernel
theorem subd15_2_410 : subd15_2 [-1, 0, 2] = true := by decide +kernel
theorem subd15_2_411 : subd15_2 [-1, 0, 3] = true := by decide +kernel
theorem subd15_2_412 : subd15_2 [-1, 0, 4] = true := by decide +kernel
theorem subd15_2_413 : subd15_2 [-1, 0, 5] = true := by decide +kernel
theorem subd15_2_414 : subd15_2 [-1, 0, 6] = true := by decide +kernel
theorem subd15_2_415 : subd15_2 [-1, 0, 7] = true := by decide +kernel
theorem sbd15_2_12 : ∀ q ∈ blkd15_2_12, subd15_2 q = true := by
  unfold blkd15_2_12
  exact List.forall_mem_cons.2 ⟨subd15_2_384, List.forall_mem_cons.2 ⟨subd15_2_385, List.forall_mem_cons.2 ⟨subd15_2_386, List.forall_mem_cons.2 ⟨subd15_2_387, List.forall_mem_cons.2 ⟨subd15_2_388, List.forall_mem_cons.2 ⟨subd15_2_389, List.forall_mem_cons.2 ⟨subd15_2_390, List.forall_mem_cons.2 ⟨subd15_2_391, List.forall_mem_cons.2 ⟨subd15_2_392, List.forall_mem_cons.2 ⟨subd15_2_393, List.forall_mem_cons.2 ⟨subd15_2_394, List.forall_mem_cons.2 ⟨subd15_2_395, List.forall_mem_cons.2 ⟨subd15_2_396, List.forall_mem_cons.2 ⟨subd15_2_397, List.forall_mem_cons.2 ⟨subd15_2_398, List.forall_mem_cons.2 ⟨subd15_2_399, List.forall_mem_cons.2 ⟨subd15_2_400, List.forall_mem_cons.2 ⟨subd15_2_401, List.forall_mem_cons.2 ⟨subd15_2_402, List.forall_mem_cons.2 ⟨subd15_2_403, List.forall_mem_cons.2 ⟨subd15_2_404, List.forall_mem_cons.2 ⟨subd15_2_405, List.forall_mem_cons.2 ⟨subd15_2_406, List.forall_mem_cons.2 ⟨subd15_2_407, List.forall_mem_cons.2 ⟨subd15_2_408, List.forall_mem_cons.2 ⟨subd15_2_409, List.forall_mem_cons.2 ⟨subd15_2_410, List.forall_mem_cons.2 ⟨subd15_2_411, List.forall_mem_cons.2 ⟨subd15_2_412, List.forall_mem_cons.2 ⟨subd15_2_413, List.forall_mem_cons.2 ⟨subd15_2_414, List.forall_mem_cons.2 ⟨subd15_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_416 : subd15_2 [-1, 0, 8] = true := by decide +kernel
theorem subd15_2_417 : subd15_2 [-1, 1, -9] = true := by decide +kernel
theorem subd15_2_418 : subd15_2 [-1, 1, -8] = true := by decide +kernel
theorem subd15_2_419 : subd15_2 [-1, 1, -7] = true := by decide +kernel
theorem subd15_2_420 : subd15_2 [-1, 1, -6] = true := by decide +kernel
theorem subd15_2_421 : subd15_2 [-1, 1, -5] = true := by decide +kernel
theorem subd15_2_422 : subd15_2 [-1, 1, -4] = true := by decide +kernel
theorem subd15_2_423 : subd15_2 [-1, 1, -3] = true := by decide +kernel
theorem subd15_2_424 : subd15_2 [-1, 1, -2] = true := by decide +kernel
theorem subd15_2_425 : subd15_2 [-1, 1, -1] = true := by decide +kernel
theorem subd15_2_426 : subd15_2 [-1, 1, 0] = true := by decide +kernel
theorem subd15_2_427 : subd15_2 [-1, 1, 1] = true := by decide +kernel
theorem subd15_2_428 : subd15_2 [-1, 1, 2] = true := by decide +kernel
theorem subd15_2_429 : subd15_2 [-1, 1, 3] = true := by decide +kernel
theorem subd15_2_430 : subd15_2 [-1, 1, 4] = true := by decide +kernel
theorem subd15_2_431 : subd15_2 [-1, 1, 5] = true := by decide +kernel
theorem subd15_2_432 : subd15_2 [-1, 1, 6] = true := by decide +kernel
theorem subd15_2_433 : subd15_2 [-1, 1, 7] = true := by decide +kernel
theorem subd15_2_434 : subd15_2 [-1, 1, 8] = true := by decide +kernel
theorem subd15_2_435 : subd15_2 [-1, 2, -9] = true := by decide +kernel
theorem subd15_2_436 : subd15_2 [-1, 2, -8] = true := by decide +kernel
theorem subd15_2_437 : subd15_2 [-1, 2, -7] = true := by decide +kernel
theorem subd15_2_438 : subd15_2 [-1, 2, -6] = true := by decide +kernel
theorem subd15_2_439 : subd15_2 [-1, 2, -5] = true := by decide +kernel
theorem subd15_2_440 : subd15_2 [-1, 2, -4] = true := by decide +kernel
theorem subd15_2_441 : subd15_2 [-1, 2, -3] = true := by decide +kernel
theorem subd15_2_442 : subd15_2 [-1, 2, -2] = true := by decide +kernel
theorem subd15_2_443 : subd15_2 [-1, 2, -1] = true := by decide +kernel
theorem subd15_2_444 : subd15_2 [-1, 2, 0] = true := by decide +kernel
theorem subd15_2_445 : subd15_2 [-1, 2, 1] = true := by decide +kernel
theorem subd15_2_446 : subd15_2 [-1, 2, 2] = true := by decide +kernel
theorem subd15_2_447 : subd15_2 [-1, 2, 3] = true := by decide +kernel
theorem sbd15_2_13 : ∀ q ∈ blkd15_2_13, subd15_2 q = true := by
  unfold blkd15_2_13
  exact List.forall_mem_cons.2 ⟨subd15_2_416, List.forall_mem_cons.2 ⟨subd15_2_417, List.forall_mem_cons.2 ⟨subd15_2_418, List.forall_mem_cons.2 ⟨subd15_2_419, List.forall_mem_cons.2 ⟨subd15_2_420, List.forall_mem_cons.2 ⟨subd15_2_421, List.forall_mem_cons.2 ⟨subd15_2_422, List.forall_mem_cons.2 ⟨subd15_2_423, List.forall_mem_cons.2 ⟨subd15_2_424, List.forall_mem_cons.2 ⟨subd15_2_425, List.forall_mem_cons.2 ⟨subd15_2_426, List.forall_mem_cons.2 ⟨subd15_2_427, List.forall_mem_cons.2 ⟨subd15_2_428, List.forall_mem_cons.2 ⟨subd15_2_429, List.forall_mem_cons.2 ⟨subd15_2_430, List.forall_mem_cons.2 ⟨subd15_2_431, List.forall_mem_cons.2 ⟨subd15_2_432, List.forall_mem_cons.2 ⟨subd15_2_433, List.forall_mem_cons.2 ⟨subd15_2_434, List.forall_mem_cons.2 ⟨subd15_2_435, List.forall_mem_cons.2 ⟨subd15_2_436, List.forall_mem_cons.2 ⟨subd15_2_437, List.forall_mem_cons.2 ⟨subd15_2_438, List.forall_mem_cons.2 ⟨subd15_2_439, List.forall_mem_cons.2 ⟨subd15_2_440, List.forall_mem_cons.2 ⟨subd15_2_441, List.forall_mem_cons.2 ⟨subd15_2_442, List.forall_mem_cons.2 ⟨subd15_2_443, List.forall_mem_cons.2 ⟨subd15_2_444, List.forall_mem_cons.2 ⟨subd15_2_445, List.forall_mem_cons.2 ⟨subd15_2_446, List.forall_mem_cons.2 ⟨subd15_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_448 : subd15_2 [-1, 2, 4] = true := by decide +kernel
theorem subd15_2_449 : subd15_2 [-1, 2, 5] = true := by decide +kernel
theorem subd15_2_450 : subd15_2 [-1, 2, 6] = true := by decide +kernel
theorem subd15_2_451 : subd15_2 [-1, 2, 7] = true := by decide +kernel
theorem subd15_2_452 : subd15_2 [-1, 2, 8] = true := by decide +kernel
theorem subd15_2_453 : subd15_2 [-1, 3, -8] = true := by decide +kernel
theorem subd15_2_454 : subd15_2 [-1, 3, -7] = true := by decide +kernel
theorem subd15_2_455 : subd15_2 [-1, 3, -6] = true := by decide +kernel
theorem subd15_2_456 : subd15_2 [-1, 3, -5] = true := by decide +kernel
theorem subd15_2_457 : subd15_2 [-1, 3, -4] = true := by decide +kernel
theorem subd15_2_458 : subd15_2 [-1, 3, -3] = true := by decide +kernel
theorem subd15_2_459 : subd15_2 [-1, 3, -2] = true := by decide +kernel
theorem subd15_2_460 : subd15_2 [-1, 3, -1] = true := by decide +kernel
theorem subd15_2_461 : subd15_2 [-1, 3, 0] = true := by decide +kernel
theorem subd15_2_462 : subd15_2 [-1, 3, 1] = true := by decide +kernel
theorem subd15_2_463 : subd15_2 [-1, 3, 2] = true := by decide +kernel
theorem subd15_2_464 : subd15_2 [-1, 3, 3] = true := by decide +kernel
theorem subd15_2_465 : subd15_2 [-1, 3, 4] = true := by decide +kernel
theorem subd15_2_466 : subd15_2 [-1, 3, 5] = true := by decide +kernel
theorem subd15_2_467 : subd15_2 [-1, 3, 6] = true := by decide +kernel
theorem subd15_2_468 : subd15_2 [-1, 3, 7] = true := by decide +kernel
theorem subd15_2_469 : subd15_2 [-1, 4, -7] = true := by decide +kernel
theorem subd15_2_470 : subd15_2 [-1, 4, -6] = true := by decide +kernel
theorem subd15_2_471 : subd15_2 [-1, 4, -5] = true := by decide +kernel
theorem subd15_2_472 : subd15_2 [-1, 4, -4] = true := by decide +kernel
theorem subd15_2_473 : subd15_2 [-1, 4, -3] = true := by decide +kernel
theorem subd15_2_474 : subd15_2 [-1, 4, -2] = true := by decide +kernel
theorem subd15_2_475 : subd15_2 [-1, 4, -1] = true := by decide +kernel
theorem subd15_2_476 : subd15_2 [-1, 4, 0] = true := by decide +kernel
theorem subd15_2_477 : subd15_2 [-1, 4, 1] = true := by decide +kernel
theorem subd15_2_478 : subd15_2 [-1, 4, 2] = true := by decide +kernel
theorem subd15_2_479 : subd15_2 [-1, 4, 3] = true := by decide +kernel
theorem sbd15_2_14 : ∀ q ∈ blkd15_2_14, subd15_2 q = true := by
  unfold blkd15_2_14
  exact List.forall_mem_cons.2 ⟨subd15_2_448, List.forall_mem_cons.2 ⟨subd15_2_449, List.forall_mem_cons.2 ⟨subd15_2_450, List.forall_mem_cons.2 ⟨subd15_2_451, List.forall_mem_cons.2 ⟨subd15_2_452, List.forall_mem_cons.2 ⟨subd15_2_453, List.forall_mem_cons.2 ⟨subd15_2_454, List.forall_mem_cons.2 ⟨subd15_2_455, List.forall_mem_cons.2 ⟨subd15_2_456, List.forall_mem_cons.2 ⟨subd15_2_457, List.forall_mem_cons.2 ⟨subd15_2_458, List.forall_mem_cons.2 ⟨subd15_2_459, List.forall_mem_cons.2 ⟨subd15_2_460, List.forall_mem_cons.2 ⟨subd15_2_461, List.forall_mem_cons.2 ⟨subd15_2_462, List.forall_mem_cons.2 ⟨subd15_2_463, List.forall_mem_cons.2 ⟨subd15_2_464, List.forall_mem_cons.2 ⟨subd15_2_465, List.forall_mem_cons.2 ⟨subd15_2_466, List.forall_mem_cons.2 ⟨subd15_2_467, List.forall_mem_cons.2 ⟨subd15_2_468, List.forall_mem_cons.2 ⟨subd15_2_469, List.forall_mem_cons.2 ⟨subd15_2_470, List.forall_mem_cons.2 ⟨subd15_2_471, List.forall_mem_cons.2 ⟨subd15_2_472, List.forall_mem_cons.2 ⟨subd15_2_473, List.forall_mem_cons.2 ⟨subd15_2_474, List.forall_mem_cons.2 ⟨subd15_2_475, List.forall_mem_cons.2 ⟨subd15_2_476, List.forall_mem_cons.2 ⟨subd15_2_477, List.forall_mem_cons.2 ⟨subd15_2_478, List.forall_mem_cons.2 ⟨subd15_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_480 : subd15_2 [-1, 4, 4] = true := by decide +kernel
theorem subd15_2_481 : subd15_2 [-1, 4, 5] = true := by decide +kernel
theorem subd15_2_482 : subd15_2 [-1, 4, 6] = true := by decide +kernel
theorem subd15_2_483 : subd15_2 [-1, 5] = true := by decide +kernel
theorem subd15_2_484 : subd15_2 [-1, 6] = true := by decide +kernel
theorem subd15_2_485 : subd15_2 [0, -7] = true := by decide +kernel
theorem subd15_2_486 : subd15_2 [0, -6] = true := by decide +kernel
theorem subd15_2_487 : subd15_2 [0, -5] = true := by decide +kernel
theorem subd15_2_488 : subd15_2 [0, -4, -8] = true := by decide +kernel
theorem subd15_2_489 : subd15_2 [0, -4, -7] = true := by decide +kernel
theorem subd15_2_490 : subd15_2 [0, -4, -6] = true := by decide +kernel
theorem subd15_2_491 : subd15_2 [0, -4, -5] = true := by decide +kernel
theorem subd15_2_492 : subd15_2 [0, -4, -4] = true := by decide +kernel
theorem subd15_2_493 : subd15_2 [0, -4, -3] = true := by decide +kernel
theorem subd15_2_494 : subd15_2 [0, -4, -2] = true := by decide +kernel
theorem subd15_2_495 : subd15_2 [0, -4, -1] = true := by decide +kernel
theorem subd15_2_496 : subd15_2 [0, -4, 0] = true := by decide +kernel
theorem subd15_2_497 : subd15_2 [0, -4, 1] = true := by decide +kernel
theorem subd15_2_498 : subd15_2 [0, -4, 2] = true := by decide +kernel
theorem subd15_2_499 : subd15_2 [0, -4, 3] = true := by decide +kernel
theorem subd15_2_500 : subd15_2 [0, -4, 4] = true := by decide +kernel
theorem subd15_2_501 : subd15_2 [0, -4, 5] = true := by decide +kernel
theorem subd15_2_502 : subd15_2 [0, -4, 6] = true := by decide +kernel
theorem subd15_2_503 : subd15_2 [0, -4, 7] = true := by decide +kernel
theorem subd15_2_504 : subd15_2 [0, -3, -9] = true := by decide +kernel
theorem subd15_2_505 : subd15_2 [0, -3, -8] = true := by decide +kernel
theorem subd15_2_506 : subd15_2 [0, -3, -7] = true := by decide +kernel
theorem subd15_2_507 : subd15_2 [0, -3, -6] = true := by decide +kernel
theorem subd15_2_508 : subd15_2 [0, -3, -5] = true := by decide +kernel
theorem subd15_2_509 : subd15_2 [0, -3, -4] = true := by decide +kernel
theorem subd15_2_510 : subd15_2 [0, -3, -3] = true := by decide +kernel
theorem subd15_2_511 : subd15_2 [0, -3, -2] = true := by decide +kernel
theorem sbd15_2_15 : ∀ q ∈ blkd15_2_15, subd15_2 q = true := by
  unfold blkd15_2_15
  exact List.forall_mem_cons.2 ⟨subd15_2_480, List.forall_mem_cons.2 ⟨subd15_2_481, List.forall_mem_cons.2 ⟨subd15_2_482, List.forall_mem_cons.2 ⟨subd15_2_483, List.forall_mem_cons.2 ⟨subd15_2_484, List.forall_mem_cons.2 ⟨subd15_2_485, List.forall_mem_cons.2 ⟨subd15_2_486, List.forall_mem_cons.2 ⟨subd15_2_487, List.forall_mem_cons.2 ⟨subd15_2_488, List.forall_mem_cons.2 ⟨subd15_2_489, List.forall_mem_cons.2 ⟨subd15_2_490, List.forall_mem_cons.2 ⟨subd15_2_491, List.forall_mem_cons.2 ⟨subd15_2_492, List.forall_mem_cons.2 ⟨subd15_2_493, List.forall_mem_cons.2 ⟨subd15_2_494, List.forall_mem_cons.2 ⟨subd15_2_495, List.forall_mem_cons.2 ⟨subd15_2_496, List.forall_mem_cons.2 ⟨subd15_2_497, List.forall_mem_cons.2 ⟨subd15_2_498, List.forall_mem_cons.2 ⟨subd15_2_499, List.forall_mem_cons.2 ⟨subd15_2_500, List.forall_mem_cons.2 ⟨subd15_2_501, List.forall_mem_cons.2 ⟨subd15_2_502, List.forall_mem_cons.2 ⟨subd15_2_503, List.forall_mem_cons.2 ⟨subd15_2_504, List.forall_mem_cons.2 ⟨subd15_2_505, List.forall_mem_cons.2 ⟨subd15_2_506, List.forall_mem_cons.2 ⟨subd15_2_507, List.forall_mem_cons.2 ⟨subd15_2_508, List.forall_mem_cons.2 ⟨subd15_2_509, List.forall_mem_cons.2 ⟨subd15_2_510, List.forall_mem_cons.2 ⟨subd15_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_512 : subd15_2 [0, -3, -1] = true := by decide +kernel
theorem subd15_2_513 : subd15_2 [0, -3, 0] = true := by decide +kernel
theorem subd15_2_514 : subd15_2 [0, -3, 1] = true := by decide +kernel
theorem subd15_2_515 : subd15_2 [0, -3, 2] = true := by decide +kernel
theorem subd15_2_516 : subd15_2 [0, -3, 3] = true := by decide +kernel
theorem subd15_2_517 : subd15_2 [0, -3, 4] = true := by decide +kernel
theorem subd15_2_518 : subd15_2 [0, -3, 5] = true := by decide +kernel
theorem subd15_2_519 : subd15_2 [0, -3, 6] = true := by decide +kernel
theorem subd15_2_520 : subd15_2 [0, -3, 7] = true := by decide +kernel
theorem subd15_2_521 : subd15_2 [0, -2, -9] = true := by decide +kernel
theorem subd15_2_522 : subd15_2 [0, -2, -8] = true := by decide +kernel
theorem subd15_2_523 : subd15_2 [0, -2, -7] = true := by decide +kernel
theorem subd15_2_524 : subd15_2 [0, -2, -6] = true := by decide +kernel
theorem subd15_2_525 : subd15_2 [0, -2, -5] = true := by decide +kernel
theorem subd15_2_526 : subd15_2 [0, -2, -4] = true := by decide +kernel
theorem subd15_2_527 : subd15_2 [0, -2, -3] = true := by decide +kernel
theorem subd15_2_528 : subd15_2 [0, -2, -2] = true := by decide +kernel
theorem subd15_2_529 : subd15_2 [0, -2, -1] = true := by decide +kernel
theorem subd15_2_530 : subd15_2 [0, -2, 0] = true := by decide +kernel
theorem subd15_2_531 : subd15_2 [0, -2, 1] = true := by decide +kernel
theorem subd15_2_532 : subd15_2 [0, -2, 2] = true := by decide +kernel
theorem subd15_2_533 : subd15_2 [0, -2, 3] = true := by decide +kernel
theorem subd15_2_534 : subd15_2 [0, -2, 4] = true := by decide +kernel
theorem subd15_2_535 : subd15_2 [0, -2, 5] = true := by decide +kernel
theorem subd15_2_536 : subd15_2 [0, -2, 6] = true := by decide +kernel
theorem subd15_2_537 : subd15_2 [0, -2, 7] = true := by decide +kernel
theorem subd15_2_538 : subd15_2 [0, -2, 8] = true := by decide +kernel
theorem subd15_2_539 : subd15_2 [0, -1, -9] = true := by decide +kernel
theorem subd15_2_540 : subd15_2 [0, -1, -8] = true := by decide +kernel
theorem subd15_2_541 : subd15_2 [0, -1, -7] = true := by decide +kernel
theorem subd15_2_542 : subd15_2 [0, -1, -6] = true := by decide +kernel
theorem subd15_2_543 : subd15_2 [0, -1, -5] = true := by decide +kernel
theorem sbd15_2_16 : ∀ q ∈ blkd15_2_16, subd15_2 q = true := by
  unfold blkd15_2_16
  exact List.forall_mem_cons.2 ⟨subd15_2_512, List.forall_mem_cons.2 ⟨subd15_2_513, List.forall_mem_cons.2 ⟨subd15_2_514, List.forall_mem_cons.2 ⟨subd15_2_515, List.forall_mem_cons.2 ⟨subd15_2_516, List.forall_mem_cons.2 ⟨subd15_2_517, List.forall_mem_cons.2 ⟨subd15_2_518, List.forall_mem_cons.2 ⟨subd15_2_519, List.forall_mem_cons.2 ⟨subd15_2_520, List.forall_mem_cons.2 ⟨subd15_2_521, List.forall_mem_cons.2 ⟨subd15_2_522, List.forall_mem_cons.2 ⟨subd15_2_523, List.forall_mem_cons.2 ⟨subd15_2_524, List.forall_mem_cons.2 ⟨subd15_2_525, List.forall_mem_cons.2 ⟨subd15_2_526, List.forall_mem_cons.2 ⟨subd15_2_527, List.forall_mem_cons.2 ⟨subd15_2_528, List.forall_mem_cons.2 ⟨subd15_2_529, List.forall_mem_cons.2 ⟨subd15_2_530, List.forall_mem_cons.2 ⟨subd15_2_531, List.forall_mem_cons.2 ⟨subd15_2_532, List.forall_mem_cons.2 ⟨subd15_2_533, List.forall_mem_cons.2 ⟨subd15_2_534, List.forall_mem_cons.2 ⟨subd15_2_535, List.forall_mem_cons.2 ⟨subd15_2_536, List.forall_mem_cons.2 ⟨subd15_2_537, List.forall_mem_cons.2 ⟨subd15_2_538, List.forall_mem_cons.2 ⟨subd15_2_539, List.forall_mem_cons.2 ⟨subd15_2_540, List.forall_mem_cons.2 ⟨subd15_2_541, List.forall_mem_cons.2 ⟨subd15_2_542, List.forall_mem_cons.2 ⟨subd15_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_544 : subd15_2 [0, -1, -4] = true := by decide +kernel
theorem subd15_2_545 : subd15_2 [0, -1, -3] = true := by decide +kernel
theorem subd15_2_546 : subd15_2 [0, -1, -2] = true := by decide +kernel
theorem subd15_2_547 : subd15_2 [0, -1, -1] = true := by decide +kernel
theorem subd15_2_548 : subd15_2 [0, -1, 0] = true := by decide +kernel
theorem subd15_2_549 : subd15_2 [0, -1, 1] = true := by decide +kernel
theorem subd15_2_550 : subd15_2 [0, -1, 2] = true := by decide +kernel
theorem subd15_2_551 : subd15_2 [0, -1, 3] = true := by decide +kernel
theorem subd15_2_552 : subd15_2 [0, -1, 4] = true := by decide +kernel
theorem subd15_2_553 : subd15_2 [0, -1, 5] = true := by decide +kernel
theorem subd15_2_554 : subd15_2 [0, -1, 6] = true := by decide +kernel
theorem subd15_2_555 : subd15_2 [0, -1, 7] = true := by decide +kernel
theorem subd15_2_556 : subd15_2 [0, -1, 8] = true := by decide +kernel
theorem subd15_2_557 : subd15_2 [0, 0, -9] = true := by decide +kernel
theorem subd15_2_558 : subd15_2 [0, 0, -8] = true := by decide +kernel
theorem subd15_2_559 : subd15_2 [0, 0, -7] = true := by decide +kernel
theorem subd15_2_560 : subd15_2 [0, 0, -6] = true := by decide +kernel
theorem subd15_2_561 : subd15_2 [0, 0, -5] = true := by decide +kernel
theorem subd15_2_562 : subd15_2 [0, 0, -4] = true := by decide +kernel
theorem subd15_2_563 : subd15_2 [0, 0, -3] = true := by decide +kernel
theorem subd15_2_564 : subd15_2 [0, 0, -2] = true := by decide +kernel
theorem subd15_2_565 : subd15_2 [0, 0, -1] = true := by decide +kernel
theorem subd15_2_566 : subd15_2 [0, 0, 0] = true := by decide +kernel
theorem subd15_2_567 : subd15_2 [0, 0, 1] = true := by decide +kernel
theorem subd15_2_568 : subd15_2 [0, 0, 2] = true := by decide +kernel
theorem subd15_2_569 : subd15_2 [0, 0, 3] = true := by decide +kernel
theorem subd15_2_570 : subd15_2 [0, 0, 4] = true := by decide +kernel
theorem subd15_2_571 : subd15_2 [0, 0, 5] = true := by decide +kernel
theorem subd15_2_572 : subd15_2 [0, 0, 6] = true := by decide +kernel
theorem subd15_2_573 : subd15_2 [0, 0, 7] = true := by decide +kernel
theorem subd15_2_574 : subd15_2 [0, 0, 8] = true := by decide +kernel
theorem subd15_2_575 : subd15_2 [0, 1, -9] = true := by decide +kernel
theorem sbd15_2_17 : ∀ q ∈ blkd15_2_17, subd15_2 q = true := by
  unfold blkd15_2_17
  exact List.forall_mem_cons.2 ⟨subd15_2_544, List.forall_mem_cons.2 ⟨subd15_2_545, List.forall_mem_cons.2 ⟨subd15_2_546, List.forall_mem_cons.2 ⟨subd15_2_547, List.forall_mem_cons.2 ⟨subd15_2_548, List.forall_mem_cons.2 ⟨subd15_2_549, List.forall_mem_cons.2 ⟨subd15_2_550, List.forall_mem_cons.2 ⟨subd15_2_551, List.forall_mem_cons.2 ⟨subd15_2_552, List.forall_mem_cons.2 ⟨subd15_2_553, List.forall_mem_cons.2 ⟨subd15_2_554, List.forall_mem_cons.2 ⟨subd15_2_555, List.forall_mem_cons.2 ⟨subd15_2_556, List.forall_mem_cons.2 ⟨subd15_2_557, List.forall_mem_cons.2 ⟨subd15_2_558, List.forall_mem_cons.2 ⟨subd15_2_559, List.forall_mem_cons.2 ⟨subd15_2_560, List.forall_mem_cons.2 ⟨subd15_2_561, List.forall_mem_cons.2 ⟨subd15_2_562, List.forall_mem_cons.2 ⟨subd15_2_563, List.forall_mem_cons.2 ⟨subd15_2_564, List.forall_mem_cons.2 ⟨subd15_2_565, List.forall_mem_cons.2 ⟨subd15_2_566, List.forall_mem_cons.2 ⟨subd15_2_567, List.forall_mem_cons.2 ⟨subd15_2_568, List.forall_mem_cons.2 ⟨subd15_2_569, List.forall_mem_cons.2 ⟨subd15_2_570, List.forall_mem_cons.2 ⟨subd15_2_571, List.forall_mem_cons.2 ⟨subd15_2_572, List.forall_mem_cons.2 ⟨subd15_2_573, List.forall_mem_cons.2 ⟨subd15_2_574, List.forall_mem_cons.2 ⟨subd15_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_576 : subd15_2 [0, 1, -8] = true := by decide +kernel
theorem subd15_2_577 : subd15_2 [0, 1, -7] = true := by decide +kernel
theorem subd15_2_578 : subd15_2 [0, 1, -6] = true := by decide +kernel
theorem subd15_2_579 : subd15_2 [0, 1, -5] = true := by decide +kernel
theorem subd15_2_580 : subd15_2 [0, 1, -4] = true := by decide +kernel
theorem subd15_2_581 : subd15_2 [0, 1, -3] = true := by decide +kernel
theorem subd15_2_582 : subd15_2 [0, 1, -2] = true := by decide +kernel
theorem subd15_2_583 : subd15_2 [0, 1, -1] = true := by decide +kernel
theorem subd15_2_584 : subd15_2 [0, 1, 0] = true := by decide +kernel
theorem subd15_2_585 : subd15_2 [0, 1, 1] = true := by decide +kernel
theorem subd15_2_586 : subd15_2 [0, 1, 2] = true := by decide +kernel
theorem subd15_2_587 : subd15_2 [0, 1, 3] = true := by decide +kernel
theorem subd15_2_588 : subd15_2 [0, 1, 4] = true := by decide +kernel
theorem subd15_2_589 : subd15_2 [0, 1, 5] = true := by decide +kernel
theorem subd15_2_590 : subd15_2 [0, 1, 6] = true := by decide +kernel
theorem subd15_2_591 : subd15_2 [0, 1, 7] = true := by decide +kernel
theorem subd15_2_592 : subd15_2 [0, 1, 8] = true := by decide +kernel
theorem subd15_2_593 : subd15_2 [0, 2, -9] = true := by decide +kernel
theorem subd15_2_594 : subd15_2 [0, 2, -8] = true := by decide +kernel
theorem subd15_2_595 : subd15_2 [0, 2, -7] = true := by decide +kernel
theorem subd15_2_596 : subd15_2 [0, 2, -6] = true := by decide +kernel
theorem subd15_2_597 : subd15_2 [0, 2, -5] = true := by decide +kernel
theorem subd15_2_598 : subd15_2 [0, 2, -4] = true := by decide +kernel
theorem subd15_2_599 : subd15_2 [0, 2, -3] = true := by decide +kernel
theorem subd15_2_600 : subd15_2 [0, 2, -2] = true := by decide +kernel
theorem subd15_2_601 : subd15_2 [0, 2, -1] = true := by decide +kernel
theorem subd15_2_602 : subd15_2 [0, 2, 0] = true := by decide +kernel
theorem subd15_2_603 : subd15_2 [0, 2, 1] = true := by decide +kernel
theorem subd15_2_604 : subd15_2 [0, 2, 2] = true := by decide +kernel
theorem subd15_2_605 : subd15_2 [0, 2, 3] = true := by decide +kernel
theorem subd15_2_606 : subd15_2 [0, 2, 4] = true := by decide +kernel
theorem subd15_2_607 : subd15_2 [0, 2, 5] = true := by decide +kernel
theorem sbd15_2_18 : ∀ q ∈ blkd15_2_18, subd15_2 q = true := by
  unfold blkd15_2_18
  exact List.forall_mem_cons.2 ⟨subd15_2_576, List.forall_mem_cons.2 ⟨subd15_2_577, List.forall_mem_cons.2 ⟨subd15_2_578, List.forall_mem_cons.2 ⟨subd15_2_579, List.forall_mem_cons.2 ⟨subd15_2_580, List.forall_mem_cons.2 ⟨subd15_2_581, List.forall_mem_cons.2 ⟨subd15_2_582, List.forall_mem_cons.2 ⟨subd15_2_583, List.forall_mem_cons.2 ⟨subd15_2_584, List.forall_mem_cons.2 ⟨subd15_2_585, List.forall_mem_cons.2 ⟨subd15_2_586, List.forall_mem_cons.2 ⟨subd15_2_587, List.forall_mem_cons.2 ⟨subd15_2_588, List.forall_mem_cons.2 ⟨subd15_2_589, List.forall_mem_cons.2 ⟨subd15_2_590, List.forall_mem_cons.2 ⟨subd15_2_591, List.forall_mem_cons.2 ⟨subd15_2_592, List.forall_mem_cons.2 ⟨subd15_2_593, List.forall_mem_cons.2 ⟨subd15_2_594, List.forall_mem_cons.2 ⟨subd15_2_595, List.forall_mem_cons.2 ⟨subd15_2_596, List.forall_mem_cons.2 ⟨subd15_2_597, List.forall_mem_cons.2 ⟨subd15_2_598, List.forall_mem_cons.2 ⟨subd15_2_599, List.forall_mem_cons.2 ⟨subd15_2_600, List.forall_mem_cons.2 ⟨subd15_2_601, List.forall_mem_cons.2 ⟨subd15_2_602, List.forall_mem_cons.2 ⟨subd15_2_603, List.forall_mem_cons.2 ⟨subd15_2_604, List.forall_mem_cons.2 ⟨subd15_2_605, List.forall_mem_cons.2 ⟨subd15_2_606, List.forall_mem_cons.2 ⟨subd15_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
