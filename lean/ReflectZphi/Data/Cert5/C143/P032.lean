import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_1_128 : subd15_1 [-2, 0, -5] = true := by decide +kernel
theorem subd15_1_129 : subd15_1 [-2, 0, -4] = true := by decide +kernel
theorem subd15_1_130 : subd15_1 [-2, 0, -3] = true := by decide +kernel
theorem subd15_1_131 : subd15_1 [-2, 0, -2] = true := by decide +kernel
theorem subd15_1_132 : subd15_1 [-2, 0, -1] = true := by decide +kernel
theorem subd15_1_133 : subd15_1 [-2, 0, 0] = true := by decide +kernel
theorem subd15_1_134 : subd15_1 [-2, 0, 1] = true := by decide +kernel
theorem subd15_1_135 : subd15_1 [-2, 0, 2] = true := by decide +kernel
theorem subd15_1_136 : subd15_1 [-2, 0, 3] = true := by decide +kernel
theorem subd15_1_137 : subd15_1 [-2, 0, 4] = true := by decide +kernel
theorem subd15_1_138 : subd15_1 [-2, 0, 5] = true := by decide +kernel
theorem subd15_1_139 : subd15_1 [-2, 0, 6] = true := by decide +kernel
theorem subd15_1_140 : subd15_1 [-2, 0, 7] = true := by decide +kernel
theorem subd15_1_141 : subd15_1 [-2, 0, 8] = true := by decide +kernel
theorem subd15_1_142 : subd15_1 [-2, 1, -8] = true := by decide +kernel
theorem subd15_1_143 : subd15_1 [-2, 1, -7] = true := by decide +kernel
theorem subd15_1_144 : subd15_1 [-2, 1, -6] = true := by decide +kernel
theorem subd15_1_145 : subd15_1 [-2, 1, -5] = true := by decide +kernel
theorem subd15_1_146 : subd15_1 [-2, 1, -4] = true := by decide +kernel
theorem subd15_1_147 : subd15_1 [-2, 1, -3] = true := by decide +kernel
theorem subd15_1_148 : subd15_1 [-2, 1, -2] = true := by decide +kernel
theorem subd15_1_149 : subd15_1 [-2, 1, -1] = true := by decide +kernel
theorem subd15_1_150 : subd15_1 [-2, 1, 0] = true := by decide +kernel
theorem subd15_1_151 : subd15_1 [-2, 1, 1] = true := by decide +kernel
theorem subd15_1_152 : subd15_1 [-2, 1, 2] = true := by decide +kernel
theorem subd15_1_153 : subd15_1 [-2, 1, 3] = true := by decide +kernel
theorem subd15_1_154 : subd15_1 [-2, 1, 4] = true := by decide +kernel
theorem subd15_1_155 : subd15_1 [-2, 1, 5] = true := by decide +kernel
theorem subd15_1_156 : subd15_1 [-2, 1, 6] = true := by decide +kernel
theorem subd15_1_157 : subd15_1 [-2, 1, 7] = true := by decide +kernel
theorem subd15_1_158 : subd15_1 [-2, 1, 8] = true := by decide +kernel
theorem subd15_1_159 : subd15_1 [-2, 2, -8] = true := by decide +kernel
theorem sbd15_1_4 : ∀ q ∈ blkd15_1_4, subd15_1 q = true := by
  unfold blkd15_1_4
  exact List.forall_mem_cons.2 ⟨subd15_1_128, List.forall_mem_cons.2 ⟨subd15_1_129, List.forall_mem_cons.2 ⟨subd15_1_130, List.forall_mem_cons.2 ⟨subd15_1_131, List.forall_mem_cons.2 ⟨subd15_1_132, List.forall_mem_cons.2 ⟨subd15_1_133, List.forall_mem_cons.2 ⟨subd15_1_134, List.forall_mem_cons.2 ⟨subd15_1_135, List.forall_mem_cons.2 ⟨subd15_1_136, List.forall_mem_cons.2 ⟨subd15_1_137, List.forall_mem_cons.2 ⟨subd15_1_138, List.forall_mem_cons.2 ⟨subd15_1_139, List.forall_mem_cons.2 ⟨subd15_1_140, List.forall_mem_cons.2 ⟨subd15_1_141, List.forall_mem_cons.2 ⟨subd15_1_142, List.forall_mem_cons.2 ⟨subd15_1_143, List.forall_mem_cons.2 ⟨subd15_1_144, List.forall_mem_cons.2 ⟨subd15_1_145, List.forall_mem_cons.2 ⟨subd15_1_146, List.forall_mem_cons.2 ⟨subd15_1_147, List.forall_mem_cons.2 ⟨subd15_1_148, List.forall_mem_cons.2 ⟨subd15_1_149, List.forall_mem_cons.2 ⟨subd15_1_150, List.forall_mem_cons.2 ⟨subd15_1_151, List.forall_mem_cons.2 ⟨subd15_1_152, List.forall_mem_cons.2 ⟨subd15_1_153, List.forall_mem_cons.2 ⟨subd15_1_154, List.forall_mem_cons.2 ⟨subd15_1_155, List.forall_mem_cons.2 ⟨subd15_1_156, List.forall_mem_cons.2 ⟨subd15_1_157, List.forall_mem_cons.2 ⟨subd15_1_158, List.forall_mem_cons.2 ⟨subd15_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_160 : subd15_1 [-2, 2, -7] = true := by decide +kernel
theorem subd15_1_161 : subd15_1 [-2, 2, -6] = true := by decide +kernel
theorem subd15_1_162 : subd15_1 [-2, 2, -5] = true := by decide +kernel
theorem subd15_1_163 : subd15_1 [-2, 2, -4] = true := by decide +kernel
theorem subd15_1_164 : subd15_1 [-2, 2, -3] = true := by decide +kernel
theorem subd15_1_165 : subd15_1 [-2, 2, -2] = true := by decide +kernel
theorem subd15_1_166 : subd15_1 [-2, 2, -1] = true := by decide +kernel
theorem subd15_1_167 : subd15_1 [-2, 2, 0] = true := by decide +kernel
theorem subd15_1_168 : subd15_1 [-2, 2, 1] = true := by decide +kernel
theorem subd15_1_169 : subd15_1 [-2, 2, 2] = true := by decide +kernel
theorem subd15_1_170 : subd15_1 [-2, 2, 3] = true := by decide +kernel
theorem subd15_1_171 : subd15_1 [-2, 2, 4] = true := by decide +kernel
theorem subd15_1_172 : subd15_1 [-2, 2, 5] = true := by decide +kernel
theorem subd15_1_173 : subd15_1 [-2, 2, 6] = true := by decide +kernel
theorem subd15_1_174 : subd15_1 [-2, 2, 7] = true := by decide +kernel
theorem subd15_1_175 : subd15_1 [-2, 3, -8] = true := by decide +kernel
theorem subd15_1_176 : subd15_1 [-2, 3, -7] = true := by decide +kernel
theorem subd15_1_177 : subd15_1 [-2, 3, -6] = true := by decide +kernel
theorem subd15_1_178 : subd15_1 [-2, 3, -5] = true := by decide +kernel
theorem subd15_1_179 : subd15_1 [-2, 3, -4] = true := by decide +kernel
theorem subd15_1_180 : subd15_1 [-2, 3, -3] = true := by decide +kernel
theorem subd15_1_181 : subd15_1 [-2, 3, -2] = true := by decide +kernel
theorem subd15_1_182 : subd15_1 [-2, 3, -1] = true := by decide +kernel
theorem subd15_1_183 : subd15_1 [-2, 3, 0] = true := by decide +kernel
theorem subd15_1_184 : subd15_1 [-2, 3, 1] = true := by decide +kernel
theorem subd15_1_185 : subd15_1 [-2, 3, 2] = true := by decide +kernel
theorem subd15_1_186 : subd15_1 [-2, 3, 3] = true := by decide +kernel
theorem subd15_1_187 : subd15_1 [-2, 3, 4] = true := by decide +kernel
theorem subd15_1_188 : subd15_1 [-2, 3, 5] = true := by decide +kernel
theorem subd15_1_189 : subd15_1 [-2, 3, 6] = true := by decide +kernel
theorem subd15_1_190 : subd15_1 [-2, 4, -7] = true := by decide +kernel
theorem subd15_1_191 : subd15_1 [-2, 4, -6] = true := by decide +kernel
theorem sbd15_1_5 : ∀ q ∈ blkd15_1_5, subd15_1 q = true := by
  unfold blkd15_1_5
  exact List.forall_mem_cons.2 ⟨subd15_1_160, List.forall_mem_cons.2 ⟨subd15_1_161, List.forall_mem_cons.2 ⟨subd15_1_162, List.forall_mem_cons.2 ⟨subd15_1_163, List.forall_mem_cons.2 ⟨subd15_1_164, List.forall_mem_cons.2 ⟨subd15_1_165, List.forall_mem_cons.2 ⟨subd15_1_166, List.forall_mem_cons.2 ⟨subd15_1_167, List.forall_mem_cons.2 ⟨subd15_1_168, List.forall_mem_cons.2 ⟨subd15_1_169, List.forall_mem_cons.2 ⟨subd15_1_170, List.forall_mem_cons.2 ⟨subd15_1_171, List.forall_mem_cons.2 ⟨subd15_1_172, List.forall_mem_cons.2 ⟨subd15_1_173, List.forall_mem_cons.2 ⟨subd15_1_174, List.forall_mem_cons.2 ⟨subd15_1_175, List.forall_mem_cons.2 ⟨subd15_1_176, List.forall_mem_cons.2 ⟨subd15_1_177, List.forall_mem_cons.2 ⟨subd15_1_178, List.forall_mem_cons.2 ⟨subd15_1_179, List.forall_mem_cons.2 ⟨subd15_1_180, List.forall_mem_cons.2 ⟨subd15_1_181, List.forall_mem_cons.2 ⟨subd15_1_182, List.forall_mem_cons.2 ⟨subd15_1_183, List.forall_mem_cons.2 ⟨subd15_1_184, List.forall_mem_cons.2 ⟨subd15_1_185, List.forall_mem_cons.2 ⟨subd15_1_186, List.forall_mem_cons.2 ⟨subd15_1_187, List.forall_mem_cons.2 ⟨subd15_1_188, List.forall_mem_cons.2 ⟨subd15_1_189, List.forall_mem_cons.2 ⟨subd15_1_190, List.forall_mem_cons.2 ⟨subd15_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_192 : subd15_1 [-2, 4, -5] = true := by decide +kernel
theorem subd15_1_193 : subd15_1 [-2, 4, -4] = true := by decide +kernel
theorem subd15_1_194 : subd15_1 [-2, 4, -3] = true := by decide +kernel
theorem subd15_1_195 : subd15_1 [-2, 4, -2] = true := by decide +kernel
theorem subd15_1_196 : subd15_1 [-2, 4, -1] = true := by decide +kernel
theorem subd15_1_197 : subd15_1 [-2, 4, 0] = true := by decide +kernel
theorem subd15_1_198 : subd15_1 [-2, 4, 1] = true := by decide +kernel
theorem subd15_1_199 : subd15_1 [-2, 4, 2] = true := by decide +kernel
theorem subd15_1_200 : subd15_1 [-2, 4, 3] = true := by decide +kernel
theorem subd15_1_201 : subd15_1 [-2, 4, 4] = true := by decide +kernel
theorem subd15_1_202 : subd15_1 [-2, 4, 5] = true := by decide +kernel
theorem subd15_1_203 : subd15_1 [-2, 5] = true := by decide +kernel
theorem subd15_1_204 : subd15_1 [-2, 6] = true := by decide +kernel
theorem subd15_1_205 : subd15_1 [-1, -6] = true := by decide +kernel
theorem subd15_1_206 : subd15_1 [-1, -5] = true := by decide +kernel
theorem subd15_1_207 : subd15_1 [-1, -4] = true := by decide +kernel
theorem subd15_1_208 : subd15_1 [-1, -3, -6] = true := by decide +kernel
theorem subd15_1_209 : subd15_1 [-1, -3, -5] = true := by decide +kernel
theorem subd15_1_210 : subd15_1 [-1, -3, -4] = true := by decide +kernel
theorem subd15_1_211 : subd15_1 [-1, -3, -3] = true := by decide +kernel
theorem subd15_1_212 : subd15_1 [-1, -3, -2] = true := by decide +kernel
theorem subd15_1_213 : subd15_1 [-1, -3, -1] = true := by decide +kernel
theorem subd15_1_214 : subd15_1 [-1, -3, 0] = true := by decide +kernel
theorem subd15_1_215 : subd15_1 [-1, -3, 1] = true := by decide +kernel
theorem subd15_1_216 : subd15_1 [-1, -3, 2] = true := by decide +kernel
theorem subd15_1_217 : subd15_1 [-1, -3, 3] = true := by decide +kernel
theorem subd15_1_218 : subd15_1 [-1, -3, 4] = true := by decide +kernel
theorem subd15_1_219 : subd15_1 [-1, -3, 5] = true := by decide +kernel
theorem subd15_1_220 : subd15_1 [-1, -3, 6] = true := by decide +kernel
theorem subd15_1_221 : subd15_1 [-1, -3, 7] = true := by decide +kernel
theorem subd15_1_222 : subd15_1 [-1, -3, 8] = true := by decide +kernel
theorem subd15_1_223 : subd15_1 [-1, -2, -7] = true := by decide +kernel
theorem sbd15_1_6 : ∀ q ∈ blkd15_1_6, subd15_1 q = true := by
  unfold blkd15_1_6
  exact List.forall_mem_cons.2 ⟨subd15_1_192, List.forall_mem_cons.2 ⟨subd15_1_193, List.forall_mem_cons.2 ⟨subd15_1_194, List.forall_mem_cons.2 ⟨subd15_1_195, List.forall_mem_cons.2 ⟨subd15_1_196, List.forall_mem_cons.2 ⟨subd15_1_197, List.forall_mem_cons.2 ⟨subd15_1_198, List.forall_mem_cons.2 ⟨subd15_1_199, List.forall_mem_cons.2 ⟨subd15_1_200, List.forall_mem_cons.2 ⟨subd15_1_201, List.forall_mem_cons.2 ⟨subd15_1_202, List.forall_mem_cons.2 ⟨subd15_1_203, List.forall_mem_cons.2 ⟨subd15_1_204, List.forall_mem_cons.2 ⟨subd15_1_205, List.forall_mem_cons.2 ⟨subd15_1_206, List.forall_mem_cons.2 ⟨subd15_1_207, List.forall_mem_cons.2 ⟨subd15_1_208, List.forall_mem_cons.2 ⟨subd15_1_209, List.forall_mem_cons.2 ⟨subd15_1_210, List.forall_mem_cons.2 ⟨subd15_1_211, List.forall_mem_cons.2 ⟨subd15_1_212, List.forall_mem_cons.2 ⟨subd15_1_213, List.forall_mem_cons.2 ⟨subd15_1_214, List.forall_mem_cons.2 ⟨subd15_1_215, List.forall_mem_cons.2 ⟨subd15_1_216, List.forall_mem_cons.2 ⟨subd15_1_217, List.forall_mem_cons.2 ⟨subd15_1_218, List.forall_mem_cons.2 ⟨subd15_1_219, List.forall_mem_cons.2 ⟨subd15_1_220, List.forall_mem_cons.2 ⟨subd15_1_221, List.forall_mem_cons.2 ⟨subd15_1_222, List.forall_mem_cons.2 ⟨subd15_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_224 : subd15_1 [-1, -2, -6] = true := by decide +kernel
theorem subd15_1_225 : subd15_1 [-1, -2, -5] = true := by decide +kernel
theorem subd15_1_226 : subd15_1 [-1, -2, -4] = true := by decide +kernel
theorem subd15_1_227 : subd15_1 [-1, -2, -3] = true := by decide +kernel
theorem subd15_1_228 : subd15_1 [-1, -2, -2] = true := by decide +kernel
theorem subd15_1_229 : subd15_1 [-1, -2, -1] = true := by decide +kernel
theorem subd15_1_230 : subd15_1 [-1, -2, 0] = true := by decide +kernel
theorem subd15_1_231 : subd15_1 [-1, -2, 1] = true := by decide +kernel
theorem subd15_1_232 : subd15_1 [-1, -2, 2] = true := by decide +kernel
theorem subd15_1_233 : subd15_1 [-1, -2, 3] = true := by decide +kernel
theorem subd15_1_234 : subd15_1 [-1, -2, 4] = true := by decide +kernel
theorem subd15_1_235 : subd15_1 [-1, -2, 5] = true := by decide +kernel
theorem subd15_1_236 : subd15_1 [-1, -2, 6] = true := by decide +kernel
theorem subd15_1_237 : subd15_1 [-1, -2, 7] = true := by decide +kernel
theorem subd15_1_238 : subd15_1 [-1, -2, 8] = true := by decide +kernel
theorem subd15_1_239 : subd15_1 [-1, -1, -7] = true := by decide +kernel
theorem subd15_1_240 : subd15_1 [-1, -1, -6] = true := by decide +kernel
theorem subd15_1_241 : subd15_1 [-1, -1, -5] = true := by decide +kernel
theorem subd15_1_242 : subd15_1 [-1, -1, -4] = true := by decide +kernel
theorem subd15_1_243 : subd15_1 [-1, -1, -3] = true := by decide +kernel
theorem subd15_1_244 : subd15_1 [-1, -1, -2] = true := by decide +kernel
theorem subd15_1_245 : subd15_1 [-1, -1, -1] = true := by decide +kernel
theorem subd15_1_246 : subd15_1 [-1, -1, 0] = true := by decide +kernel
theorem subd15_1_247 : subd15_1 [-1, -1, 1] = true := by decide +kernel
theorem subd15_1_248 : subd15_1 [-1, -1, 2] = true := by decide +kernel
theorem subd15_1_249 : subd15_1 [-1, -1, 3] = true := by decide +kernel
theorem subd15_1_250 : subd15_1 [-1, -1, 4] = true := by decide +kernel
theorem subd15_1_251 : subd15_1 [-1, -1, 5] = true := by decide +kernel
theorem subd15_1_252 : subd15_1 [-1, -1, 6] = true := by decide +kernel
theorem subd15_1_253 : subd15_1 [-1, -1, 7] = true := by decide +kernel
theorem subd15_1_254 : subd15_1 [-1, -1, 8] = true := by decide +kernel
theorem subd15_1_255 : subd15_1 [-1, 0, -8] = true := by decide +kernel
theorem sbd15_1_7 : ∀ q ∈ blkd15_1_7, subd15_1 q = true := by
  unfold blkd15_1_7
  exact List.forall_mem_cons.2 ⟨subd15_1_224, List.forall_mem_cons.2 ⟨subd15_1_225, List.forall_mem_cons.2 ⟨subd15_1_226, List.forall_mem_cons.2 ⟨subd15_1_227, List.forall_mem_cons.2 ⟨subd15_1_228, List.forall_mem_cons.2 ⟨subd15_1_229, List.forall_mem_cons.2 ⟨subd15_1_230, List.forall_mem_cons.2 ⟨subd15_1_231, List.forall_mem_cons.2 ⟨subd15_1_232, List.forall_mem_cons.2 ⟨subd15_1_233, List.forall_mem_cons.2 ⟨subd15_1_234, List.forall_mem_cons.2 ⟨subd15_1_235, List.forall_mem_cons.2 ⟨subd15_1_236, List.forall_mem_cons.2 ⟨subd15_1_237, List.forall_mem_cons.2 ⟨subd15_1_238, List.forall_mem_cons.2 ⟨subd15_1_239, List.forall_mem_cons.2 ⟨subd15_1_240, List.forall_mem_cons.2 ⟨subd15_1_241, List.forall_mem_cons.2 ⟨subd15_1_242, List.forall_mem_cons.2 ⟨subd15_1_243, List.forall_mem_cons.2 ⟨subd15_1_244, List.forall_mem_cons.2 ⟨subd15_1_245, List.forall_mem_cons.2 ⟨subd15_1_246, List.forall_mem_cons.2 ⟨subd15_1_247, List.forall_mem_cons.2 ⟨subd15_1_248, List.forall_mem_cons.2 ⟨subd15_1_249, List.forall_mem_cons.2 ⟨subd15_1_250, List.forall_mem_cons.2 ⟨subd15_1_251, List.forall_mem_cons.2 ⟨subd15_1_252, List.forall_mem_cons.2 ⟨subd15_1_253, List.forall_mem_cons.2 ⟨subd15_1_254, List.forall_mem_cons.2 ⟨subd15_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_256 : subd15_1 [-1, 0, -7] = true := by decide +kernel
theorem subd15_1_257 : subd15_1 [-1, 0, -6] = true := by decide +kernel
theorem subd15_1_258 : subd15_1 [-1, 0, -5] = true := by decide +kernel
theorem subd15_1_259 : subd15_1 [-1, 0, -4] = true := by decide +kernel
theorem subd15_1_260 : subd15_1 [-1, 0, -3] = true := by decide +kernel
theorem subd15_1_261 : subd15_1 [-1, 0, -2] = true := by decide +kernel
theorem subd15_1_262 : subd15_1 [-1, 0, -1] = true := by decide +kernel
theorem subd15_1_263 : subd15_1 [-1, 0, 0] = true := by decide +kernel
theorem subd15_1_264 : subd15_1 [-1, 0, 1] = true := by decide +kernel
theorem subd15_1_265 : subd15_1 [-1, 0, 2] = true := by decide +kernel
theorem subd15_1_266 : subd15_1 [-1, 0, 3] = true := by decide +kernel
theorem subd15_1_267 : subd15_1 [-1, 0, 4] = true := by decide +kernel
theorem subd15_1_268 : subd15_1 [-1, 0, 5] = true := by decide +kernel
theorem subd15_1_269 : subd15_1 [-1, 0, 6] = true := by decide +kernel
theorem subd15_1_270 : subd15_1 [-1, 0, 7] = true := by decide +kernel
theorem subd15_1_271 : subd15_1 [-1, 0, 8] = true := by decide +kernel
theorem subd15_1_272 : subd15_1 [-1, 1, -8] = true := by decide +kernel
theorem subd15_1_273 : subd15_1 [-1, 1, -7] = true := by decide +kernel
theorem subd15_1_274 : subd15_1 [-1, 1, -6] = true := by decide +kernel
theorem subd15_1_275 : subd15_1 [-1, 1, -5] = true := by decide +kernel
theorem subd15_1_276 : subd15_1 [-1, 1, -4] = true := by decide +kernel
theorem subd15_1_277 : subd15_1 [-1, 1, -3] = true := by decide +kernel
theorem subd15_1_278 : subd15_1 [-1, 1, -2] = true := by decide +kernel
theorem subd15_1_279 : subd15_1 [-1, 1, -1] = true := by decide +kernel
theorem subd15_1_280 : subd15_1 [-1, 1, 0] = true := by decide +kernel
theorem subd15_1_281 : subd15_1 [-1, 1, 1] = true := by decide +kernel
theorem subd15_1_282 : subd15_1 [-1, 1, 2] = true := by decide +kernel
theorem subd15_1_283 : subd15_1 [-1, 1, 3] = true := by decide +kernel
theorem subd15_1_284 : subd15_1 [-1, 1, 4] = true := by decide +kernel
theorem subd15_1_285 : subd15_1 [-1, 1, 5] = true := by decide +kernel
theorem subd15_1_286 : subd15_1 [-1, 1, 6] = true := by decide +kernel
theorem subd15_1_287 : subd15_1 [-1, 1, 7] = true := by decide +kernel
theorem sbd15_1_8 : ∀ q ∈ blkd15_1_8, subd15_1 q = true := by
  unfold blkd15_1_8
  exact List.forall_mem_cons.2 ⟨subd15_1_256, List.forall_mem_cons.2 ⟨subd15_1_257, List.forall_mem_cons.2 ⟨subd15_1_258, List.forall_mem_cons.2 ⟨subd15_1_259, List.forall_mem_cons.2 ⟨subd15_1_260, List.forall_mem_cons.2 ⟨subd15_1_261, List.forall_mem_cons.2 ⟨subd15_1_262, List.forall_mem_cons.2 ⟨subd15_1_263, List.forall_mem_cons.2 ⟨subd15_1_264, List.forall_mem_cons.2 ⟨subd15_1_265, List.forall_mem_cons.2 ⟨subd15_1_266, List.forall_mem_cons.2 ⟨subd15_1_267, List.forall_mem_cons.2 ⟨subd15_1_268, List.forall_mem_cons.2 ⟨subd15_1_269, List.forall_mem_cons.2 ⟨subd15_1_270, List.forall_mem_cons.2 ⟨subd15_1_271, List.forall_mem_cons.2 ⟨subd15_1_272, List.forall_mem_cons.2 ⟨subd15_1_273, List.forall_mem_cons.2 ⟨subd15_1_274, List.forall_mem_cons.2 ⟨subd15_1_275, List.forall_mem_cons.2 ⟨subd15_1_276, List.forall_mem_cons.2 ⟨subd15_1_277, List.forall_mem_cons.2 ⟨subd15_1_278, List.forall_mem_cons.2 ⟨subd15_1_279, List.forall_mem_cons.2 ⟨subd15_1_280, List.forall_mem_cons.2 ⟨subd15_1_281, List.forall_mem_cons.2 ⟨subd15_1_282, List.forall_mem_cons.2 ⟨subd15_1_283, List.forall_mem_cons.2 ⟨subd15_1_284, List.forall_mem_cons.2 ⟨subd15_1_285, List.forall_mem_cons.2 ⟨subd15_1_286, List.forall_mem_cons.2 ⟨subd15_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_288 : subd15_1 [-1, 1, 8] = true := by decide +kernel
theorem subd15_1_289 : subd15_1 [-1, 2, -8] = true := by decide +kernel
theorem subd15_1_290 : subd15_1 [-1, 2, -7] = true := by decide +kernel
theorem subd15_1_291 : subd15_1 [-1, 2, -6] = true := by decide +kernel
theorem subd15_1_292 : subd15_1 [-1, 2, -5] = true := by decide +kernel
theorem subd15_1_293 : subd15_1 [-1, 2, -4] = true := by decide +kernel
theorem subd15_1_294 : subd15_1 [-1, 2, -3] = true := by decide +kernel
theorem subd15_1_295 : subd15_1 [-1, 2, -2] = true := by decide +kernel
theorem subd15_1_296 : subd15_1 [-1, 2, -1] = true := by decide +kernel
theorem subd15_1_297 : subd15_1 [-1, 2, 0] = true := by decide +kernel
theorem subd15_1_298 : subd15_1 [-1, 2, 1] = true := by decide +kernel
theorem subd15_1_299 : subd15_1 [-1, 2, 2] = true := by decide +kernel
theorem subd15_1_300 : subd15_1 [-1, 2, 3] = true := by decide +kernel
theorem subd15_1_301 : subd15_1 [-1, 2, 4] = true := by decide +kernel
theorem subd15_1_302 : subd15_1 [-1, 2, 5] = true := by decide +kernel
theorem subd15_1_303 : subd15_1 [-1, 2, 6] = true := by decide +kernel
theorem subd15_1_304 : subd15_1 [-1, 2, 7] = true := by decide +kernel
theorem subd15_1_305 : subd15_1 [-1, 3, -8] = true := by decide +kernel
theorem subd15_1_306 : subd15_1 [-1, 3, -7] = true := by decide +kernel
theorem subd15_1_307 : subd15_1 [-1, 3, -6] = true := by decide +kernel
theorem subd15_1_308 : subd15_1 [-1, 3, -5] = true := by decide +kernel
theorem subd15_1_309 : subd15_1 [-1, 3, -4] = true := by decide +kernel
theorem subd15_1_310 : subd15_1 [-1, 3, -3] = true := by decide +kernel
theorem subd15_1_311 : subd15_1 [-1, 3, -2] = true := by decide +kernel
theorem subd15_1_312 : subd15_1 [-1, 3, -1] = true := by decide +kernel
theorem subd15_1_313 : subd15_1 [-1, 3, 0] = true := by decide +kernel
theorem subd15_1_314 : subd15_1 [-1, 3, 1] = true := by decide +kernel
theorem subd15_1_315 : subd15_1 [-1, 3, 2] = true := by decide +kernel
theorem subd15_1_316 : subd15_1 [-1, 3, 3] = true := by decide +kernel
theorem subd15_1_317 : subd15_1 [-1, 3, 4] = true := by decide +kernel
theorem subd15_1_318 : subd15_1 [-1, 3, 5] = true := by decide +kernel
theorem subd15_1_319 : subd15_1 [-1, 3, 6] = true := by decide +kernel
theorem sbd15_1_9 : ∀ q ∈ blkd15_1_9, subd15_1 q = true := by
  unfold blkd15_1_9
  exact List.forall_mem_cons.2 ⟨subd15_1_288, List.forall_mem_cons.2 ⟨subd15_1_289, List.forall_mem_cons.2 ⟨subd15_1_290, List.forall_mem_cons.2 ⟨subd15_1_291, List.forall_mem_cons.2 ⟨subd15_1_292, List.forall_mem_cons.2 ⟨subd15_1_293, List.forall_mem_cons.2 ⟨subd15_1_294, List.forall_mem_cons.2 ⟨subd15_1_295, List.forall_mem_cons.2 ⟨subd15_1_296, List.forall_mem_cons.2 ⟨subd15_1_297, List.forall_mem_cons.2 ⟨subd15_1_298, List.forall_mem_cons.2 ⟨subd15_1_299, List.forall_mem_cons.2 ⟨subd15_1_300, List.forall_mem_cons.2 ⟨subd15_1_301, List.forall_mem_cons.2 ⟨subd15_1_302, List.forall_mem_cons.2 ⟨subd15_1_303, List.forall_mem_cons.2 ⟨subd15_1_304, List.forall_mem_cons.2 ⟨subd15_1_305, List.forall_mem_cons.2 ⟨subd15_1_306, List.forall_mem_cons.2 ⟨subd15_1_307, List.forall_mem_cons.2 ⟨subd15_1_308, List.forall_mem_cons.2 ⟨subd15_1_309, List.forall_mem_cons.2 ⟨subd15_1_310, List.forall_mem_cons.2 ⟨subd15_1_311, List.forall_mem_cons.2 ⟨subd15_1_312, List.forall_mem_cons.2 ⟨subd15_1_313, List.forall_mem_cons.2 ⟨subd15_1_314, List.forall_mem_cons.2 ⟨subd15_1_315, List.forall_mem_cons.2 ⟨subd15_1_316, List.forall_mem_cons.2 ⟨subd15_1_317, List.forall_mem_cons.2 ⟨subd15_1_318, List.forall_mem_cons.2 ⟨subd15_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_320 : subd15_1 [-1, 4, -8] = true := by decide +kernel
theorem subd15_1_321 : subd15_1 [-1, 4, -7] = true := by decide +kernel
theorem subd15_1_322 : subd15_1 [-1, 4, -6] = true := by decide +kernel
theorem subd15_1_323 : subd15_1 [-1, 4, -5] = true := by decide +kernel
theorem subd15_1_324 : subd15_1 [-1, 4, -4] = true := by decide +kernel
theorem subd15_1_325 : subd15_1 [-1, 4, -3] = true := by decide +kernel
theorem subd15_1_326 : subd15_1 [-1, 4, -2] = true := by decide +kernel
theorem subd15_1_327 : subd15_1 [-1, 4, -1] = true := by decide +kernel
theorem subd15_1_328 : subd15_1 [-1, 4, 0] = true := by decide +kernel
theorem subd15_1_329 : subd15_1 [-1, 4, 1] = true := by decide +kernel
theorem subd15_1_330 : subd15_1 [-1, 4, 2] = true := by decide +kernel
theorem subd15_1_331 : subd15_1 [-1, 4, 3] = true := by decide +kernel
theorem subd15_1_332 : subd15_1 [-1, 4, 4] = true := by decide +kernel
theorem subd15_1_333 : subd15_1 [-1, 4, 5] = true := by decide +kernel
theorem subd15_1_334 : subd15_1 [-1, 5] = true := by decide +kernel
theorem subd15_1_335 : subd15_1 [-1, 6] = true := by decide +kernel
theorem subd15_1_336 : subd15_1 [0, -7] = true := by decide +kernel
theorem subd15_1_337 : subd15_1 [0, -6] = true := by decide +kernel
theorem subd15_1_338 : subd15_1 [0, -5] = true := by decide +kernel
theorem subd15_1_339 : subd15_1 [0, -4] = true := by decide +kernel
theorem subd15_1_340 : subd15_1 [0, -3, -6] = true := by decide +kernel
theorem subd15_1_341 : subd15_1 [0, -3, -5] = true := by decide +kernel
theorem subd15_1_342 : subd15_1 [0, -3, -4] = true := by decide +kernel
theorem subd15_1_343 : subd15_1 [0, -3, -3] = true := by decide +kernel
theorem subd15_1_344 : subd15_1 [0, -3, -2] = true := by decide +kernel
theorem subd15_1_345 : subd15_1 [0, -3, -1] = true := by decide +kernel
theorem subd15_1_346 : subd15_1 [0, -3, 0] = true := by decide +kernel
theorem subd15_1_347 : subd15_1 [0, -3, 1] = true := by decide +kernel
theorem subd15_1_348 : subd15_1 [0, -3, 2] = true := by decide +kernel
theorem subd15_1_349 : subd15_1 [0, -3, 3] = true := by decide +kernel
theorem subd15_1_350 : subd15_1 [0, -3, 4] = true := by decide +kernel
theorem subd15_1_351 : subd15_1 [0, -3, 5] = true := by decide +kernel
theorem sbd15_1_10 : ∀ q ∈ blkd15_1_10, subd15_1 q = true := by
  unfold blkd15_1_10
  exact List.forall_mem_cons.2 ⟨subd15_1_320, List.forall_mem_cons.2 ⟨subd15_1_321, List.forall_mem_cons.2 ⟨subd15_1_322, List.forall_mem_cons.2 ⟨subd15_1_323, List.forall_mem_cons.2 ⟨subd15_1_324, List.forall_mem_cons.2 ⟨subd15_1_325, List.forall_mem_cons.2 ⟨subd15_1_326, List.forall_mem_cons.2 ⟨subd15_1_327, List.forall_mem_cons.2 ⟨subd15_1_328, List.forall_mem_cons.2 ⟨subd15_1_329, List.forall_mem_cons.2 ⟨subd15_1_330, List.forall_mem_cons.2 ⟨subd15_1_331, List.forall_mem_cons.2 ⟨subd15_1_332, List.forall_mem_cons.2 ⟨subd15_1_333, List.forall_mem_cons.2 ⟨subd15_1_334, List.forall_mem_cons.2 ⟨subd15_1_335, List.forall_mem_cons.2 ⟨subd15_1_336, List.forall_mem_cons.2 ⟨subd15_1_337, List.forall_mem_cons.2 ⟨subd15_1_338, List.forall_mem_cons.2 ⟨subd15_1_339, List.forall_mem_cons.2 ⟨subd15_1_340, List.forall_mem_cons.2 ⟨subd15_1_341, List.forall_mem_cons.2 ⟨subd15_1_342, List.forall_mem_cons.2 ⟨subd15_1_343, List.forall_mem_cons.2 ⟨subd15_1_344, List.forall_mem_cons.2 ⟨subd15_1_345, List.forall_mem_cons.2 ⟨subd15_1_346, List.forall_mem_cons.2 ⟨subd15_1_347, List.forall_mem_cons.2 ⟨subd15_1_348, List.forall_mem_cons.2 ⟨subd15_1_349, List.forall_mem_cons.2 ⟨subd15_1_350, List.forall_mem_cons.2 ⟨subd15_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_352 : subd15_1 [0, -3, 6] = true := by decide +kernel
theorem subd15_1_353 : subd15_1 [0, -3, 7] = true := by decide +kernel
theorem subd15_1_354 : subd15_1 [0, -3, 8] = true := by decide +kernel
theorem subd15_1_355 : subd15_1 [0, -2, -7] = true := by decide +kernel
theorem subd15_1_356 : subd15_1 [0, -2, -6] = true := by decide +kernel
theorem subd15_1_357 : subd15_1 [0, -2, -5] = true := by decide +kernel
theorem subd15_1_358 : subd15_1 [0, -2, -4] = true := by decide +kernel
theorem subd15_1_359 : subd15_1 [0, -2, -3] = true := by decide +kernel
theorem subd15_1_360 : subd15_1 [0, -2, -2] = true := by decide +kernel
theorem subd15_1_361 : subd15_1 [0, -2, -1] = true := by decide +kernel
theorem subd15_1_362 : subd15_1 [0, -2, 0] = true := by decide +kernel
theorem subd15_1_363 : subd15_1 [0, -2, 1] = true := by decide +kernel
theorem subd15_1_364 : subd15_1 [0, -2, 2] = true := by decide +kernel
theorem subd15_1_365 : subd15_1 [0, -2, 3] = true := by decide +kernel
theorem subd15_1_366 : subd15_1 [0, -2, 4] = true := by decide +kernel
theorem subd15_1_367 : subd15_1 [0, -2, 5] = true := by decide +kernel
theorem subd15_1_368 : subd15_1 [0, -2, 6] = true := by decide +kernel
theorem subd15_1_369 : subd15_1 [0, -2, 7] = true := by decide +kernel
theorem subd15_1_370 : subd15_1 [0, -2, 8] = true := by decide +kernel
theorem subd15_1_371 : subd15_1 [0, -1, -8] = true := by decide +kernel
theorem subd15_1_372 : subd15_1 [0, -1, -7] = true := by decide +kernel
theorem subd15_1_373 : subd15_1 [0, -1, -6] = true := by decide +kernel
theorem subd15_1_374 : subd15_1 [0, -1, -5] = true := by decide +kernel
theorem subd15_1_375 : subd15_1 [0, -1, -4] = true := by decide +kernel
theorem subd15_1_376 : subd15_1 [0, -1, -3] = true := by decide +kernel
theorem subd15_1_377 : subd15_1 [0, -1, -2] = true := by decide +kernel
theorem subd15_1_378 : subd15_1 [0, -1, -1] = true := by decide +kernel
theorem subd15_1_379 : subd15_1 [0, -1, 0] = true := by decide +kernel
theorem subd15_1_380 : subd15_1 [0, -1, 1] = true := by decide +kernel
theorem subd15_1_381 : subd15_1 [0, -1, 2] = true := by decide +kernel
theorem subd15_1_382 : subd15_1 [0, -1, 3] = true := by decide +kernel
theorem subd15_1_383 : subd15_1 [0, -1, 4] = true := by decide +kernel
theorem sbd15_1_11 : ∀ q ∈ blkd15_1_11, subd15_1 q = true := by
  unfold blkd15_1_11
  exact List.forall_mem_cons.2 ⟨subd15_1_352, List.forall_mem_cons.2 ⟨subd15_1_353, List.forall_mem_cons.2 ⟨subd15_1_354, List.forall_mem_cons.2 ⟨subd15_1_355, List.forall_mem_cons.2 ⟨subd15_1_356, List.forall_mem_cons.2 ⟨subd15_1_357, List.forall_mem_cons.2 ⟨subd15_1_358, List.forall_mem_cons.2 ⟨subd15_1_359, List.forall_mem_cons.2 ⟨subd15_1_360, List.forall_mem_cons.2 ⟨subd15_1_361, List.forall_mem_cons.2 ⟨subd15_1_362, List.forall_mem_cons.2 ⟨subd15_1_363, List.forall_mem_cons.2 ⟨subd15_1_364, List.forall_mem_cons.2 ⟨subd15_1_365, List.forall_mem_cons.2 ⟨subd15_1_366, List.forall_mem_cons.2 ⟨subd15_1_367, List.forall_mem_cons.2 ⟨subd15_1_368, List.forall_mem_cons.2 ⟨subd15_1_369, List.forall_mem_cons.2 ⟨subd15_1_370, List.forall_mem_cons.2 ⟨subd15_1_371, List.forall_mem_cons.2 ⟨subd15_1_372, List.forall_mem_cons.2 ⟨subd15_1_373, List.forall_mem_cons.2 ⟨subd15_1_374, List.forall_mem_cons.2 ⟨subd15_1_375, List.forall_mem_cons.2 ⟨subd15_1_376, List.forall_mem_cons.2 ⟨subd15_1_377, List.forall_mem_cons.2 ⟨subd15_1_378, List.forall_mem_cons.2 ⟨subd15_1_379, List.forall_mem_cons.2 ⟨subd15_1_380, List.forall_mem_cons.2 ⟨subd15_1_381, List.forall_mem_cons.2 ⟨subd15_1_382, List.forall_mem_cons.2 ⟨subd15_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_384 : subd15_1 [0, -1, 5] = true := by decide +kernel
theorem subd15_1_385 : subd15_1 [0, -1, 6] = true := by decide +kernel
theorem subd15_1_386 : subd15_1 [0, -1, 7] = true := by decide +kernel
theorem subd15_1_387 : subd15_1 [0, -1, 8] = true := by decide +kernel
theorem subd15_1_388 : subd15_1 [0, 0, -9] = true := by decide +kernel
theorem subd15_1_389 : subd15_1 [0, 0, -8] = true := by decide +kernel
theorem subd15_1_390 : subd15_1 [0, 0, -7] = true := by decide +kernel
theorem subd15_1_391 : subd15_1 [0, 0, -6] = true := by decide +kernel
theorem subd15_1_392 : subd15_1 [0, 0, -5] = true := by decide +kernel
theorem subd15_1_393 : subd15_1 [0, 0, -4] = true := by decide +kernel
theorem subd15_1_394 : subd15_1 [0, 0, -3] = true := by decide +kernel
theorem subd15_1_395 : subd15_1 [0, 0, -2] = true := by decide +kernel
theorem subd15_1_396 : subd15_1 [0, 0, -1] = true := by decide +kernel
theorem subd15_1_397 : subd15_1 [0, 0, 0] = true := by decide +kernel
theorem subd15_1_398 : subd15_1 [0, 0, 1] = true := by decide +kernel
theorem subd15_1_399 : subd15_1 [0, 0, 2] = true := by decide +kernel
theorem subd15_1_400 : subd15_1 [0, 0, 3] = true := by decide +kernel
theorem subd15_1_401 : subd15_1 [0, 0, 4] = true := by decide +kernel
theorem subd15_1_402 : subd15_1 [0, 0, 5] = true := by decide +kernel
theorem subd15_1_403 : subd15_1 [0, 0, 6] = true := by decide +kernel
theorem subd15_1_404 : subd15_1 [0, 0, 7] = true := by decide +kernel
theorem subd15_1_405 : subd15_1 [0, 0, 8] = true := by decide +kernel
theorem subd15_1_406 : subd15_1 [0, 1, -9] = true := by decide +kernel
theorem subd15_1_407 : subd15_1 [0, 1, -8] = true := by decide +kernel
theorem subd15_1_408 : subd15_1 [0, 1, -7] = true := by decide +kernel
theorem subd15_1_409 : subd15_1 [0, 1, -6] = true := by decide +kernel
theorem subd15_1_410 : subd15_1 [0, 1, -5] = true := by decide +kernel
theorem subd15_1_411 : subd15_1 [0, 1, -4] = true := by decide +kernel
theorem subd15_1_412 : subd15_1 [0, 1, -3] = true := by decide +kernel
theorem subd15_1_413 : subd15_1 [0, 1, -2] = true := by decide +kernel
theorem subd15_1_414 : subd15_1 [0, 1, -1] = true := by decide +kernel
theorem subd15_1_415 : subd15_1 [0, 1, 0] = true := by decide +kernel
theorem sbd15_1_12 : ∀ q ∈ blkd15_1_12, subd15_1 q = true := by
  unfold blkd15_1_12
  exact List.forall_mem_cons.2 ⟨subd15_1_384, List.forall_mem_cons.2 ⟨subd15_1_385, List.forall_mem_cons.2 ⟨subd15_1_386, List.forall_mem_cons.2 ⟨subd15_1_387, List.forall_mem_cons.2 ⟨subd15_1_388, List.forall_mem_cons.2 ⟨subd15_1_389, List.forall_mem_cons.2 ⟨subd15_1_390, List.forall_mem_cons.2 ⟨subd15_1_391, List.forall_mem_cons.2 ⟨subd15_1_392, List.forall_mem_cons.2 ⟨subd15_1_393, List.forall_mem_cons.2 ⟨subd15_1_394, List.forall_mem_cons.2 ⟨subd15_1_395, List.forall_mem_cons.2 ⟨subd15_1_396, List.forall_mem_cons.2 ⟨subd15_1_397, List.forall_mem_cons.2 ⟨subd15_1_398, List.forall_mem_cons.2 ⟨subd15_1_399, List.forall_mem_cons.2 ⟨subd15_1_400, List.forall_mem_cons.2 ⟨subd15_1_401, List.forall_mem_cons.2 ⟨subd15_1_402, List.forall_mem_cons.2 ⟨subd15_1_403, List.forall_mem_cons.2 ⟨subd15_1_404, List.forall_mem_cons.2 ⟨subd15_1_405, List.forall_mem_cons.2 ⟨subd15_1_406, List.forall_mem_cons.2 ⟨subd15_1_407, List.forall_mem_cons.2 ⟨subd15_1_408, List.forall_mem_cons.2 ⟨subd15_1_409, List.forall_mem_cons.2 ⟨subd15_1_410, List.forall_mem_cons.2 ⟨subd15_1_411, List.forall_mem_cons.2 ⟨subd15_1_412, List.forall_mem_cons.2 ⟨subd15_1_413, List.forall_mem_cons.2 ⟨subd15_1_414, List.forall_mem_cons.2 ⟨subd15_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_416 : subd15_1 [0, 1, 1] = true := by decide +kernel
theorem subd15_1_417 : subd15_1 [0, 1, 2] = true := by decide +kernel
theorem subd15_1_418 : subd15_1 [0, 1, 3] = true := by decide +kernel
theorem subd15_1_419 : subd15_1 [0, 1, 4] = true := by decide +kernel
theorem subd15_1_420 : subd15_1 [0, 1, 5] = true := by decide +kernel
theorem subd15_1_421 : subd15_1 [0, 1, 6] = true := by decide +kernel
theorem subd15_1_422 : subd15_1 [0, 1, 7] = true := by decide +kernel
theorem subd15_1_423 : subd15_1 [0, 2, -9] = true := by decide +kernel
theorem subd15_1_424 : subd15_1 [0, 2, -8] = true := by decide +kernel
theorem subd15_1_425 : subd15_1 [0, 2, -7] = true := by decide +kernel
theorem subd15_1_426 : subd15_1 [0, 2, -6] = true := by decide +kernel
theorem subd15_1_427 : subd15_1 [0, 2, -5] = true := by decide +kernel
theorem subd15_1_428 : subd15_1 [0, 2, -4] = true := by decide +kernel
theorem subd15_1_429 : subd15_1 [0, 2, -3] = true := by decide +kernel
theorem subd15_1_430 : subd15_1 [0, 2, -2] = true := by decide +kernel
theorem subd15_1_431 : subd15_1 [0, 2, -1] = true := by decide +kernel
theorem subd15_1_432 : subd15_1 [0, 2, 0] = true := by decide +kernel
theorem subd15_1_433 : subd15_1 [0, 2, 1] = true := by decide +kernel
theorem subd15_1_434 : subd15_1 [0, 2, 2] = true := by decide +kernel
theorem subd15_1_435 : subd15_1 [0, 2, 3] = true := by decide +kernel
theorem subd15_1_436 : subd15_1 [0, 2, 4] = true := by decide +kernel
theorem subd15_1_437 : subd15_1 [0, 2, 5] = true := by decide +kernel
theorem subd15_1_438 : subd15_1 [0, 2, 6] = true := by decide +kernel
theorem subd15_1_439 : subd15_1 [0, 3, -9] = true := by decide +kernel
theorem subd15_1_440 : subd15_1 [0, 3, -8] = true := by decide +kernel
theorem subd15_1_441 : subd15_1 [0, 3, -7] = true := by decide +kernel
theorem subd15_1_442 : subd15_1 [0, 3, -6] = true := by decide +kernel
theorem subd15_1_443 : subd15_1 [0, 3, -5] = true := by decide +kernel
theorem subd15_1_444 : subd15_1 [0, 3, -4] = true := by decide +kernel
theorem subd15_1_445 : subd15_1 [0, 3, -3] = true := by decide +kernel
theorem subd15_1_446 : subd15_1 [0, 3, -2] = true := by decide +kernel
theorem subd15_1_447 : subd15_1 [0, 3, -1] = true := by decide +kernel
theorem sbd15_1_13 : ∀ q ∈ blkd15_1_13, subd15_1 q = true := by
  unfold blkd15_1_13
  exact List.forall_mem_cons.2 ⟨subd15_1_416, List.forall_mem_cons.2 ⟨subd15_1_417, List.forall_mem_cons.2 ⟨subd15_1_418, List.forall_mem_cons.2 ⟨subd15_1_419, List.forall_mem_cons.2 ⟨subd15_1_420, List.forall_mem_cons.2 ⟨subd15_1_421, List.forall_mem_cons.2 ⟨subd15_1_422, List.forall_mem_cons.2 ⟨subd15_1_423, List.forall_mem_cons.2 ⟨subd15_1_424, List.forall_mem_cons.2 ⟨subd15_1_425, List.forall_mem_cons.2 ⟨subd15_1_426, List.forall_mem_cons.2 ⟨subd15_1_427, List.forall_mem_cons.2 ⟨subd15_1_428, List.forall_mem_cons.2 ⟨subd15_1_429, List.forall_mem_cons.2 ⟨subd15_1_430, List.forall_mem_cons.2 ⟨subd15_1_431, List.forall_mem_cons.2 ⟨subd15_1_432, List.forall_mem_cons.2 ⟨subd15_1_433, List.forall_mem_cons.2 ⟨subd15_1_434, List.forall_mem_cons.2 ⟨subd15_1_435, List.forall_mem_cons.2 ⟨subd15_1_436, List.forall_mem_cons.2 ⟨subd15_1_437, List.forall_mem_cons.2 ⟨subd15_1_438, List.forall_mem_cons.2 ⟨subd15_1_439, List.forall_mem_cons.2 ⟨subd15_1_440, List.forall_mem_cons.2 ⟨subd15_1_441, List.forall_mem_cons.2 ⟨subd15_1_442, List.forall_mem_cons.2 ⟨subd15_1_443, List.forall_mem_cons.2 ⟨subd15_1_444, List.forall_mem_cons.2 ⟨subd15_1_445, List.forall_mem_cons.2 ⟨subd15_1_446, List.forall_mem_cons.2 ⟨subd15_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_448 : subd15_1 [0, 3, 0] = true := by decide +kernel
theorem subd15_1_449 : subd15_1 [0, 3, 1] = true := by decide +kernel
theorem subd15_1_450 : subd15_1 [0, 3, 2] = true := by decide +kernel
theorem subd15_1_451 : subd15_1 [0, 3, 3] = true := by decide +kernel
theorem subd15_1_452 : subd15_1 [0, 3, 4] = true := by decide +kernel
theorem subd15_1_453 : subd15_1 [0, 3, 5] = true := by decide +kernel
theorem subd15_1_454 : subd15_1 [0, 4] = true := by decide +kernel
theorem subd15_1_455 : subd15_1 [0, 5] = true := by decide +kernel
theorem subd15_1_456 : subd15_1 [0, 6] = true := by decide +kernel
theorem subd15_1_457 : subd15_1 [1, -7] = true := by decide +kernel
theorem subd15_1_458 : subd15_1 [1, -6] = true := by decide +kernel
theorem subd15_1_459 : subd15_1 [1, -5] = true := by decide +kernel
theorem subd15_1_460 : subd15_1 [1, -4, -6] = true := by decide +kernel
theorem subd15_1_461 : subd15_1 [1, -4, -5] = true := by decide +kernel
theorem subd15_1_462 : subd15_1 [1, -4, -4] = true := by decide +kernel
theorem subd15_1_463 : subd15_1 [1, -4, -3] = true := by decide +kernel
theorem subd15_1_464 : subd15_1 [1, -4, -2] = true := by decide +kernel
theorem subd15_1_465 : subd15_1 [1, -4, -1] = true := by decide +kernel
theorem subd15_1_466 : subd15_1 [1, -4, 0] = true := by decide +kernel
theorem subd15_1_467 : subd15_1 [1, -4, 1] = true := by decide +kernel
theorem subd15_1_468 : subd15_1 [1, -4, 2] = true := by decide +kernel
theorem subd15_1_469 : subd15_1 [1, -4, 3] = true := by decide +kernel
theorem subd15_1_470 : subd15_1 [1, -4, 4] = true := by decide +kernel
theorem subd15_1_471 : subd15_1 [1, -4, 5] = true := by decide +kernel
theorem subd15_1_472 : subd15_1 [1, -4, 6] = true := by decide +kernel
theorem subd15_1_473 : subd15_1 [1, -4, 7] = true := by decide +kernel
theorem subd15_1_474 : subd15_1 [1, -3, -7] = true := by decide +kernel
theorem subd15_1_475 : subd15_1 [1, -3, -6] = true := by decide +kernel
theorem subd15_1_476 : subd15_1 [1, -3, -5] = true := by decide +kernel
theorem subd15_1_477 : subd15_1 [1, -3, -4] = true := by decide +kernel
theorem subd15_1_478 : subd15_1 [1, -3, -3] = true := by decide +kernel
theorem subd15_1_479 : subd15_1 [1, -3, -2] = true := by decide +kernel
theorem sbd15_1_14 : ∀ q ∈ blkd15_1_14, subd15_1 q = true := by
  unfold blkd15_1_14
  exact List.forall_mem_cons.2 ⟨subd15_1_448, List.forall_mem_cons.2 ⟨subd15_1_449, List.forall_mem_cons.2 ⟨subd15_1_450, List.forall_mem_cons.2 ⟨subd15_1_451, List.forall_mem_cons.2 ⟨subd15_1_452, List.forall_mem_cons.2 ⟨subd15_1_453, List.forall_mem_cons.2 ⟨subd15_1_454, List.forall_mem_cons.2 ⟨subd15_1_455, List.forall_mem_cons.2 ⟨subd15_1_456, List.forall_mem_cons.2 ⟨subd15_1_457, List.forall_mem_cons.2 ⟨subd15_1_458, List.forall_mem_cons.2 ⟨subd15_1_459, List.forall_mem_cons.2 ⟨subd15_1_460, List.forall_mem_cons.2 ⟨subd15_1_461, List.forall_mem_cons.2 ⟨subd15_1_462, List.forall_mem_cons.2 ⟨subd15_1_463, List.forall_mem_cons.2 ⟨subd15_1_464, List.forall_mem_cons.2 ⟨subd15_1_465, List.forall_mem_cons.2 ⟨subd15_1_466, List.forall_mem_cons.2 ⟨subd15_1_467, List.forall_mem_cons.2 ⟨subd15_1_468, List.forall_mem_cons.2 ⟨subd15_1_469, List.forall_mem_cons.2 ⟨subd15_1_470, List.forall_mem_cons.2 ⟨subd15_1_471, List.forall_mem_cons.2 ⟨subd15_1_472, List.forall_mem_cons.2 ⟨subd15_1_473, List.forall_mem_cons.2 ⟨subd15_1_474, List.forall_mem_cons.2 ⟨subd15_1_475, List.forall_mem_cons.2 ⟨subd15_1_476, List.forall_mem_cons.2 ⟨subd15_1_477, List.forall_mem_cons.2 ⟨subd15_1_478, List.forall_mem_cons.2 ⟨subd15_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_480 : subd15_1 [1, -3, -1] = true := by decide +kernel
theorem subd15_1_481 : subd15_1 [1, -3, 0] = true := by decide +kernel
theorem subd15_1_482 : subd15_1 [1, -3, 1] = true := by decide +kernel
theorem subd15_1_483 : subd15_1 [1, -3, 2] = true := by decide +kernel
theorem subd15_1_484 : subd15_1 [1, -3, 3] = true := by decide +kernel
theorem subd15_1_485 : subd15_1 [1, -3, 4] = true := by decide +kernel
theorem subd15_1_486 : subd15_1 [1, -3, 5] = true := by decide +kernel
theorem subd15_1_487 : subd15_1 [1, -3, 6] = true := by decide +kernel
theorem subd15_1_488 : subd15_1 [1, -3, 7] = true := by decide +kernel
theorem subd15_1_489 : subd15_1 [1, -2, -8] = true := by decide +kernel
theorem subd15_1_490 : subd15_1 [1, -2, -7] = true := by decide +kernel
theorem subd15_1_491 : subd15_1 [1, -2, -6] = true := by decide +kernel
theorem subd15_1_492 : subd15_1 [1, -2, -5] = true := by decide +kernel
theorem subd15_1_493 : subd15_1 [1, -2, -4] = true := by decide +kernel
theorem subd15_1_494 : subd15_1 [1, -2, -3] = true := by decide +kernel
theorem subd15_1_495 : subd15_1 [1, -2, -2] = true := by decide +kernel
theorem subd15_1_496 : subd15_1 [1, -2, -1] = true := by decide +kernel
theorem subd15_1_497 : subd15_1 [1, -2, 0] = true := by decide +kernel
theorem subd15_1_498 : subd15_1 [1, -2, 1] = true := by decide +kernel
theorem subd15_1_499 : subd15_1 [1, -2, 2] = true := by decide +kernel
theorem subd15_1_500 : subd15_1 [1, -2, 3] = true := by decide +kernel
theorem subd15_1_501 : subd15_1 [1, -2, 4] = true := by decide +kernel
theorem subd15_1_502 : subd15_1 [1, -2, 5] = true := by decide +kernel
theorem subd15_1_503 : subd15_1 [1, -2, 6] = true := by decide +kernel
theorem subd15_1_504 : subd15_1 [1, -2, 7] = true := by decide +kernel
theorem subd15_1_505 : subd15_1 [1, -1, -9] = true := by decide +kernel
theorem subd15_1_506 : subd15_1 [1, -1, -8] = true := by decide +kernel
theorem subd15_1_507 : subd15_1 [1, -1, -7] = true := by decide +kernel
theorem subd15_1_508 : subd15_1 [1, -1, -6] = true := by decide +kernel
theorem subd15_1_509 : subd15_1 [1, -1, -5] = true := by decide +kernel
theorem subd15_1_510 : subd15_1 [1, -1, -4] = true := by decide +kernel
theorem subd15_1_511 : subd15_1 [1, -1, -3] = true := by decide +kernel
theorem sbd15_1_15 : ∀ q ∈ blkd15_1_15, subd15_1 q = true := by
  unfold blkd15_1_15
  exact List.forall_mem_cons.2 ⟨subd15_1_480, List.forall_mem_cons.2 ⟨subd15_1_481, List.forall_mem_cons.2 ⟨subd15_1_482, List.forall_mem_cons.2 ⟨subd15_1_483, List.forall_mem_cons.2 ⟨subd15_1_484, List.forall_mem_cons.2 ⟨subd15_1_485, List.forall_mem_cons.2 ⟨subd15_1_486, List.forall_mem_cons.2 ⟨subd15_1_487, List.forall_mem_cons.2 ⟨subd15_1_488, List.forall_mem_cons.2 ⟨subd15_1_489, List.forall_mem_cons.2 ⟨subd15_1_490, List.forall_mem_cons.2 ⟨subd15_1_491, List.forall_mem_cons.2 ⟨subd15_1_492, List.forall_mem_cons.2 ⟨subd15_1_493, List.forall_mem_cons.2 ⟨subd15_1_494, List.forall_mem_cons.2 ⟨subd15_1_495, List.forall_mem_cons.2 ⟨subd15_1_496, List.forall_mem_cons.2 ⟨subd15_1_497, List.forall_mem_cons.2 ⟨subd15_1_498, List.forall_mem_cons.2 ⟨subd15_1_499, List.forall_mem_cons.2 ⟨subd15_1_500, List.forall_mem_cons.2 ⟨subd15_1_501, List.forall_mem_cons.2 ⟨subd15_1_502, List.forall_mem_cons.2 ⟨subd15_1_503, List.forall_mem_cons.2 ⟨subd15_1_504, List.forall_mem_cons.2 ⟨subd15_1_505, List.forall_mem_cons.2 ⟨subd15_1_506, List.forall_mem_cons.2 ⟨subd15_1_507, List.forall_mem_cons.2 ⟨subd15_1_508, List.forall_mem_cons.2 ⟨subd15_1_509, List.forall_mem_cons.2 ⟨subd15_1_510, List.forall_mem_cons.2 ⟨subd15_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_512 : subd15_1 [1, -1, -2] = true := by decide +kernel
theorem subd15_1_513 : subd15_1 [1, -1, -1] = true := by decide +kernel
theorem subd15_1_514 : subd15_1 [1, -1, 0] = true := by decide +kernel
theorem subd15_1_515 : subd15_1 [1, -1, 1] = true := by decide +kernel
theorem subd15_1_516 : subd15_1 [1, -1, 2] = true := by decide +kernel
theorem subd15_1_517 : subd15_1 [1, -1, 3] = true := by decide +kernel
theorem subd15_1_518 : subd15_1 [1, -1, 4] = true := by decide +kernel
theorem subd15_1_519 : subd15_1 [1, -1, 5] = true := by decide +kernel
theorem subd15_1_520 : subd15_1 [1, -1, 6] = true := by decide +kernel
theorem subd15_1_521 : subd15_1 [1, -1, 7] = true := by decide +kernel
theorem subd15_1_522 : subd15_1 [1, 0, -9] = true := by decide +kernel
theorem subd15_1_523 : subd15_1 [1, 0, -8] = true := by decide +kernel
theorem subd15_1_524 : subd15_1 [1, 0, -7] = true := by decide +kernel
theorem subd15_1_525 : subd15_1 [1, 0, -6] = true := by decide +kernel
theorem subd15_1_526 : subd15_1 [1, 0, -5] = true := by decide +kernel
theorem subd15_1_527 : subd15_1 [1, 0, -4] = true := by decide +kernel
theorem subd15_1_528 : subd15_1 [1, 0, -3] = true := by decide +kernel
theorem subd15_1_529 : subd15_1 [1, 0, -2] = true := by decide +kernel
theorem subd15_1_530 : subd15_1 [1, 0, -1] = true := by decide +kernel
theorem subd15_1_531 : subd15_1 [1, 0, 0] = true := by decide +kernel
theorem subd15_1_532 : subd15_1 [1, 0, 1] = true := by decide +kernel
theorem subd15_1_533 : subd15_1 [1, 0, 2] = true := by decide +kernel
theorem subd15_1_534 : subd15_1 [1, 0, 3] = true := by decide +kernel
theorem subd15_1_535 : subd15_1 [1, 0, 4] = true := by decide +kernel
theorem subd15_1_536 : subd15_1 [1, 0, 5] = true := by decide +kernel
theorem subd15_1_537 : subd15_1 [1, 0, 6] = true := by decide +kernel
theorem subd15_1_538 : subd15_1 [1, 0, 7] = true := by decide +kernel
theorem subd15_1_539 : subd15_1 [1, 1, -9] = true := by decide +kernel
theorem subd15_1_540 : subd15_1 [1, 1, -8] = true := by decide +kernel
theorem subd15_1_541 : subd15_1 [1, 1, -7] = true := by decide +kernel
theorem subd15_1_542 : subd15_1 [1, 1, -6] = true := by decide +kernel
theorem subd15_1_543 : subd15_1 [1, 1, -5] = true := by decide +kernel
theorem sbd15_1_16 : ∀ q ∈ blkd15_1_16, subd15_1 q = true := by
  unfold blkd15_1_16
  exact List.forall_mem_cons.2 ⟨subd15_1_512, List.forall_mem_cons.2 ⟨subd15_1_513, List.forall_mem_cons.2 ⟨subd15_1_514, List.forall_mem_cons.2 ⟨subd15_1_515, List.forall_mem_cons.2 ⟨subd15_1_516, List.forall_mem_cons.2 ⟨subd15_1_517, List.forall_mem_cons.2 ⟨subd15_1_518, List.forall_mem_cons.2 ⟨subd15_1_519, List.forall_mem_cons.2 ⟨subd15_1_520, List.forall_mem_cons.2 ⟨subd15_1_521, List.forall_mem_cons.2 ⟨subd15_1_522, List.forall_mem_cons.2 ⟨subd15_1_523, List.forall_mem_cons.2 ⟨subd15_1_524, List.forall_mem_cons.2 ⟨subd15_1_525, List.forall_mem_cons.2 ⟨subd15_1_526, List.forall_mem_cons.2 ⟨subd15_1_527, List.forall_mem_cons.2 ⟨subd15_1_528, List.forall_mem_cons.2 ⟨subd15_1_529, List.forall_mem_cons.2 ⟨subd15_1_530, List.forall_mem_cons.2 ⟨subd15_1_531, List.forall_mem_cons.2 ⟨subd15_1_532, List.forall_mem_cons.2 ⟨subd15_1_533, List.forall_mem_cons.2 ⟨subd15_1_534, List.forall_mem_cons.2 ⟨subd15_1_535, List.forall_mem_cons.2 ⟨subd15_1_536, List.forall_mem_cons.2 ⟨subd15_1_537, List.forall_mem_cons.2 ⟨subd15_1_538, List.forall_mem_cons.2 ⟨subd15_1_539, List.forall_mem_cons.2 ⟨subd15_1_540, List.forall_mem_cons.2 ⟨subd15_1_541, List.forall_mem_cons.2 ⟨subd15_1_542, List.forall_mem_cons.2 ⟨subd15_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_544 : subd15_1 [1, 1, -4] = true := by decide +kernel
theorem subd15_1_545 : subd15_1 [1, 1, -3] = true := by decide +kernel
theorem subd15_1_546 : subd15_1 [1, 1, -2] = true := by decide +kernel
theorem subd15_1_547 : subd15_1 [1, 1, -1] = true := by decide +kernel
theorem subd15_1_548 : subd15_1 [1, 1, 0] = true := by decide +kernel
theorem subd15_1_549 : subd15_1 [1, 1, 1] = true := by decide +kernel
theorem subd15_1_550 : subd15_1 [1, 1, 2] = true := by decide +kernel
theorem subd15_1_551 : subd15_1 [1, 1, 3] = true := by decide +kernel
theorem subd15_1_552 : subd15_1 [1, 1, 4] = true := by decide +kernel
theorem subd15_1_553 : subd15_1 [1, 1, 5] = true := by decide +kernel
theorem subd15_1_554 : subd15_1 [1, 1, 6] = true := by decide +kernel
theorem subd15_1_555 : subd15_1 [1, 2, -9] = true := by decide +kernel
theorem subd15_1_556 : subd15_1 [1, 2, -8] = true := by decide +kernel
theorem subd15_1_557 : subd15_1 [1, 2, -7] = true := by decide +kernel
theorem subd15_1_558 : subd15_1 [1, 2, -6] = true := by decide +kernel
theorem subd15_1_559 : subd15_1 [1, 2, -5] = true := by decide +kernel
theorem subd15_1_560 : subd15_1 [1, 2, -4] = true := by decide +kernel
theorem subd15_1_561 : subd15_1 [1, 2, -3] = true := by decide +kernel
theorem subd15_1_562 : subd15_1 [1, 2, -2] = true := by decide +kernel
theorem subd15_1_563 : subd15_1 [1, 2, -1] = true := by decide +kernel
theorem subd15_1_564 : subd15_1 [1, 2, 0] = true := by decide +kernel
theorem subd15_1_565 : subd15_1 [1, 2, 1] = true := by decide +kernel
theorem subd15_1_566 : subd15_1 [1, 2, 2] = true := by decide +kernel
theorem subd15_1_567 : subd15_1 [1, 2, 3] = true := by decide +kernel
theorem subd15_1_568 : subd15_1 [1, 2, 4] = true := by decide +kernel
theorem subd15_1_569 : subd15_1 [1, 2, 5] = true := by decide +kernel
theorem subd15_1_570 : subd15_1 [1, 2, 6] = true := by decide +kernel
theorem subd15_1_571 : subd15_1 [1, 3, -9] = true := by decide +kernel
theorem subd15_1_572 : subd15_1 [1, 3, -8] = true := by decide +kernel
theorem subd15_1_573 : subd15_1 [1, 3, -7] = true := by decide +kernel
theorem subd15_1_574 : subd15_1 [1, 3, -6] = true := by decide +kernel
theorem subd15_1_575 : subd15_1 [1, 3, -5] = true := by decide +kernel
theorem sbd15_1_17 : ∀ q ∈ blkd15_1_17, subd15_1 q = true := by
  unfold blkd15_1_17
  exact List.forall_mem_cons.2 ⟨subd15_1_544, List.forall_mem_cons.2 ⟨subd15_1_545, List.forall_mem_cons.2 ⟨subd15_1_546, List.forall_mem_cons.2 ⟨subd15_1_547, List.forall_mem_cons.2 ⟨subd15_1_548, List.forall_mem_cons.2 ⟨subd15_1_549, List.forall_mem_cons.2 ⟨subd15_1_550, List.forall_mem_cons.2 ⟨subd15_1_551, List.forall_mem_cons.2 ⟨subd15_1_552, List.forall_mem_cons.2 ⟨subd15_1_553, List.forall_mem_cons.2 ⟨subd15_1_554, List.forall_mem_cons.2 ⟨subd15_1_555, List.forall_mem_cons.2 ⟨subd15_1_556, List.forall_mem_cons.2 ⟨subd15_1_557, List.forall_mem_cons.2 ⟨subd15_1_558, List.forall_mem_cons.2 ⟨subd15_1_559, List.forall_mem_cons.2 ⟨subd15_1_560, List.forall_mem_cons.2 ⟨subd15_1_561, List.forall_mem_cons.2 ⟨subd15_1_562, List.forall_mem_cons.2 ⟨subd15_1_563, List.forall_mem_cons.2 ⟨subd15_1_564, List.forall_mem_cons.2 ⟨subd15_1_565, List.forall_mem_cons.2 ⟨subd15_1_566, List.forall_mem_cons.2 ⟨subd15_1_567, List.forall_mem_cons.2 ⟨subd15_1_568, List.forall_mem_cons.2 ⟨subd15_1_569, List.forall_mem_cons.2 ⟨subd15_1_570, List.forall_mem_cons.2 ⟨subd15_1_571, List.forall_mem_cons.2 ⟨subd15_1_572, List.forall_mem_cons.2 ⟨subd15_1_573, List.forall_mem_cons.2 ⟨subd15_1_574, List.forall_mem_cons.2 ⟨subd15_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_576 : subd15_1 [1, 3, -4] = true := by decide +kernel
theorem subd15_1_577 : subd15_1 [1, 3, -3] = true := by decide +kernel
theorem subd15_1_578 : subd15_1 [1, 3, -2] = true := by decide +kernel
theorem subd15_1_579 : subd15_1 [1, 3, -1] = true := by decide +kernel
theorem subd15_1_580 : subd15_1 [1, 3, 0] = true := by decide +kernel
theorem subd15_1_581 : subd15_1 [1, 3, 1] = true := by decide +kernel
theorem subd15_1_582 : subd15_1 [1, 3, 2] = true := by decide +kernel
theorem subd15_1_583 : subd15_1 [1, 3, 3] = true := by decide +kernel
theorem subd15_1_584 : subd15_1 [1, 3, 4] = true := by decide +kernel
theorem subd15_1_585 : subd15_1 [1, 3, 5] = true := by decide +kernel
theorem subd15_1_586 : subd15_1 [1, 4] = true := by decide +kernel
theorem subd15_1_587 : subd15_1 [1, 5] = true := by decide +kernel
theorem subd15_1_588 : subd15_1 [2, -7] = true := by decide +kernel
theorem subd15_1_589 : subd15_1 [2, -6] = true := by decide +kernel
theorem subd15_1_590 : subd15_1 [2, -5] = true := by decide +kernel
theorem subd15_1_591 : subd15_1 [2, -4, -6] = true := by decide +kernel
theorem subd15_1_592 : subd15_1 [2, -4, -5] = true := by decide +kernel
theorem subd15_1_593 : subd15_1 [2, -4, -4] = true := by decide +kernel
theorem subd15_1_594 : subd15_1 [2, -4, -3] = true := by decide +kernel
theorem subd15_1_595 : subd15_1 [2, -4, -2] = true := by decide +kernel
theorem subd15_1_596 : subd15_1 [2, -4, -1] = true := by decide +kernel
theorem subd15_1_597 : subd15_1 [2, -4, 0] = true := by decide +kernel
theorem subd15_1_598 : subd15_1 [2, -4, 1] = true := by decide +kernel
theorem subd15_1_599 : subd15_1 [2, -4, 2] = true := by decide +kernel
theorem subd15_1_600 : subd15_1 [2, -4, 3] = true := by decide +kernel
theorem subd15_1_601 : subd15_1 [2, -4, 4] = true := by decide +kernel
theorem subd15_1_602 : subd15_1 [2, -4, 5] = true := by decide +kernel
theorem subd15_1_603 : subd15_1 [2, -4, 6] = true := by decide +kernel
theorem subd15_1_604 : subd15_1 [2, -3, -7] = true := by decide +kernel
theorem subd15_1_605 : subd15_1 [2, -3, -6] = true := by decide +kernel
theorem subd15_1_606 : subd15_1 [2, -3, -5] = true := by decide +kernel
theorem subd15_1_607 : subd15_1 [2, -3, -4] = true := by decide +kernel
theorem sbd15_1_18 : ∀ q ∈ blkd15_1_18, subd15_1 q = true := by
  unfold blkd15_1_18
  exact List.forall_mem_cons.2 ⟨subd15_1_576, List.forall_mem_cons.2 ⟨subd15_1_577, List.forall_mem_cons.2 ⟨subd15_1_578, List.forall_mem_cons.2 ⟨subd15_1_579, List.forall_mem_cons.2 ⟨subd15_1_580, List.forall_mem_cons.2 ⟨subd15_1_581, List.forall_mem_cons.2 ⟨subd15_1_582, List.forall_mem_cons.2 ⟨subd15_1_583, List.forall_mem_cons.2 ⟨subd15_1_584, List.forall_mem_cons.2 ⟨subd15_1_585, List.forall_mem_cons.2 ⟨subd15_1_586, List.forall_mem_cons.2 ⟨subd15_1_587, List.forall_mem_cons.2 ⟨subd15_1_588, List.forall_mem_cons.2 ⟨subd15_1_589, List.forall_mem_cons.2 ⟨subd15_1_590, List.forall_mem_cons.2 ⟨subd15_1_591, List.forall_mem_cons.2 ⟨subd15_1_592, List.forall_mem_cons.2 ⟨subd15_1_593, List.forall_mem_cons.2 ⟨subd15_1_594, List.forall_mem_cons.2 ⟨subd15_1_595, List.forall_mem_cons.2 ⟨subd15_1_596, List.forall_mem_cons.2 ⟨subd15_1_597, List.forall_mem_cons.2 ⟨subd15_1_598, List.forall_mem_cons.2 ⟨subd15_1_599, List.forall_mem_cons.2 ⟨subd15_1_600, List.forall_mem_cons.2 ⟨subd15_1_601, List.forall_mem_cons.2 ⟨subd15_1_602, List.forall_mem_cons.2 ⟨subd15_1_603, List.forall_mem_cons.2 ⟨subd15_1_604, List.forall_mem_cons.2 ⟨subd15_1_605, List.forall_mem_cons.2 ⟨subd15_1_606, List.forall_mem_cons.2 ⟨subd15_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
