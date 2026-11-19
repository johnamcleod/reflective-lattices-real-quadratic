import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_0_128 : subd14_0 [-2, 1, -2] = true := by decide +kernel
theorem subd14_0_129 : subd14_0 [-2, 1, -1] = true := by decide +kernel
theorem subd14_0_130 : subd14_0 [-2, 1, 0] = true := by decide +kernel
theorem subd14_0_131 : subd14_0 [-2, 1, 1] = true := by decide +kernel
theorem subd14_0_132 : subd14_0 [-2, 1, 2] = true := by decide +kernel
theorem subd14_0_133 : subd14_0 [-2, 1, 3] = true := by decide +kernel
theorem subd14_0_134 : subd14_0 [-2, 1, 4] = true := by decide +kernel
theorem subd14_0_135 : subd14_0 [-2, 1, 5] = true := by decide +kernel
theorem subd14_0_136 : subd14_0 [-2, 1, 6] = true := by decide +kernel
theorem subd14_0_137 : subd14_0 [-2, 1, 7] = true := by decide +kernel
theorem subd14_0_138 : subd14_0 [-2, 2, -7] = true := by decide +kernel
theorem subd14_0_139 : subd14_0 [-2, 2, -6] = true := by decide +kernel
theorem subd14_0_140 : subd14_0 [-2, 2, -5] = true := by decide +kernel
theorem subd14_0_141 : subd14_0 [-2, 2, -4] = true := by decide +kernel
theorem subd14_0_142 : subd14_0 [-2, 2, -3] = true := by decide +kernel
theorem subd14_0_143 : subd14_0 [-2, 2, -2] = true := by decide +kernel
theorem subd14_0_144 : subd14_0 [-2, 2, -1] = true := by decide +kernel
theorem subd14_0_145 : subd14_0 [-2, 2, 0] = true := by decide +kernel
theorem subd14_0_146 : subd14_0 [-2, 2, 1] = true := by decide +kernel
theorem subd14_0_147 : subd14_0 [-2, 2, 2] = true := by decide +kernel
theorem subd14_0_148 : subd14_0 [-2, 2, 3] = true := by decide +kernel
theorem subd14_0_149 : subd14_0 [-2, 2, 4] = true := by decide +kernel
theorem subd14_0_150 : subd14_0 [-2, 2, 5] = true := by decide +kernel
theorem subd14_0_151 : subd14_0 [-2, 2, 6] = true := by decide +kernel
theorem subd14_0_152 : subd14_0 [-2, 3] = true := by decide +kernel
theorem subd14_0_153 : subd14_0 [-2, 4] = true := by decide +kernel
theorem subd14_0_154 : subd14_0 [-2, 5] = true := by decide +kernel
theorem subd14_0_155 : subd14_0 [-2, 6] = true := by decide +kernel
theorem subd14_0_156 : subd14_0 [-1, -7] = true := by decide +kernel
theorem subd14_0_157 : subd14_0 [-1, -6] = true := by decide +kernel
theorem subd14_0_158 : subd14_0 [-1, -5] = true := by decide +kernel
theorem subd14_0_159 : subd14_0 [-1, -4] = true := by decide +kernel
theorem sbd14_0_4 : ∀ q ∈ blkd14_0_4, subd14_0 q = true := by
  unfold blkd14_0_4
  exact List.forall_mem_cons.2 ⟨subd14_0_128, List.forall_mem_cons.2 ⟨subd14_0_129, List.forall_mem_cons.2 ⟨subd14_0_130, List.forall_mem_cons.2 ⟨subd14_0_131, List.forall_mem_cons.2 ⟨subd14_0_132, List.forall_mem_cons.2 ⟨subd14_0_133, List.forall_mem_cons.2 ⟨subd14_0_134, List.forall_mem_cons.2 ⟨subd14_0_135, List.forall_mem_cons.2 ⟨subd14_0_136, List.forall_mem_cons.2 ⟨subd14_0_137, List.forall_mem_cons.2 ⟨subd14_0_138, List.forall_mem_cons.2 ⟨subd14_0_139, List.forall_mem_cons.2 ⟨subd14_0_140, List.forall_mem_cons.2 ⟨subd14_0_141, List.forall_mem_cons.2 ⟨subd14_0_142, List.forall_mem_cons.2 ⟨subd14_0_143, List.forall_mem_cons.2 ⟨subd14_0_144, List.forall_mem_cons.2 ⟨subd14_0_145, List.forall_mem_cons.2 ⟨subd14_0_146, List.forall_mem_cons.2 ⟨subd14_0_147, List.forall_mem_cons.2 ⟨subd14_0_148, List.forall_mem_cons.2 ⟨subd14_0_149, List.forall_mem_cons.2 ⟨subd14_0_150, List.forall_mem_cons.2 ⟨subd14_0_151, List.forall_mem_cons.2 ⟨subd14_0_152, List.forall_mem_cons.2 ⟨subd14_0_153, List.forall_mem_cons.2 ⟨subd14_0_154, List.forall_mem_cons.2 ⟨subd14_0_155, List.forall_mem_cons.2 ⟨subd14_0_156, List.forall_mem_cons.2 ⟨subd14_0_157, List.forall_mem_cons.2 ⟨subd14_0_158, List.forall_mem_cons.2 ⟨subd14_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_160 : subd14_0 [-1, -3, -6] = true := by decide +kernel
theorem subd14_0_161 : subd14_0 [-1, -3, -5] = true := by decide +kernel
theorem subd14_0_162 : subd14_0 [-1, -3, -4] = true := by decide +kernel
theorem subd14_0_163 : subd14_0 [-1, -3, -3] = true := by decide +kernel
theorem subd14_0_164 : subd14_0 [-1, -3, -2] = true := by decide +kernel
theorem subd14_0_165 : subd14_0 [-1, -3, -1] = true := by decide +kernel
theorem subd14_0_166 : subd14_0 [-1, -3, 0] = true := by decide +kernel
theorem subd14_0_167 : subd14_0 [-1, -3, 1] = true := by decide +kernel
theorem subd14_0_168 : subd14_0 [-1, -3, 2] = true := by decide +kernel
theorem subd14_0_169 : subd14_0 [-1, -3, 3] = true := by decide +kernel
theorem subd14_0_170 : subd14_0 [-1, -3, 4] = true := by decide +kernel
theorem subd14_0_171 : subd14_0 [-1, -3, 5] = true := by decide +kernel
theorem subd14_0_172 : subd14_0 [-1, -3, 6] = true := by decide +kernel
theorem subd14_0_173 : subd14_0 [-1, -3, 7] = true := by decide +kernel
theorem subd14_0_174 : subd14_0 [-1, -2, -7] = true := by decide +kernel
theorem subd14_0_175 : subd14_0 [-1, -2, -6] = true := by decide +kernel
theorem subd14_0_176 : subd14_0 [-1, -2, -5] = true := by decide +kernel
theorem subd14_0_177 : subd14_0 [-1, -2, -4] = true := by decide +kernel
theorem subd14_0_178 : subd14_0 [-1, -2, -3] = true := by decide +kernel
theorem subd14_0_179 : subd14_0 [-1, -2, -2] = true := by decide +kernel
theorem subd14_0_180 : subd14_0 [-1, -2, -1] = true := by decide +kernel
theorem subd14_0_181 : subd14_0 [-1, -2, 0] = true := by decide +kernel
theorem subd14_0_182 : subd14_0 [-1, -2, 1] = true := by decide +kernel
theorem subd14_0_183 : subd14_0 [-1, -2, 2] = true := by decide +kernel
theorem subd14_0_184 : subd14_0 [-1, -2, 3] = true := by decide +kernel
theorem subd14_0_185 : subd14_0 [-1, -2, 4] = true := by decide +kernel
theorem subd14_0_186 : subd14_0 [-1, -2, 5] = true := by decide +kernel
theorem subd14_0_187 : subd14_0 [-1, -2, 6] = true := by decide +kernel
theorem subd14_0_188 : subd14_0 [-1, -2, 7] = true := by decide +kernel
theorem subd14_0_189 : subd14_0 [-1, -1, -7] = true := by decide +kernel
theorem subd14_0_190 : subd14_0 [-1, -1, -6] = true := by decide +kernel
theorem subd14_0_191 : subd14_0 [-1, -1, -5] = true := by decide +kernel
theorem sbd14_0_5 : ∀ q ∈ blkd14_0_5, subd14_0 q = true := by
  unfold blkd14_0_5
  exact List.forall_mem_cons.2 ⟨subd14_0_160, List.forall_mem_cons.2 ⟨subd14_0_161, List.forall_mem_cons.2 ⟨subd14_0_162, List.forall_mem_cons.2 ⟨subd14_0_163, List.forall_mem_cons.2 ⟨subd14_0_164, List.forall_mem_cons.2 ⟨subd14_0_165, List.forall_mem_cons.2 ⟨subd14_0_166, List.forall_mem_cons.2 ⟨subd14_0_167, List.forall_mem_cons.2 ⟨subd14_0_168, List.forall_mem_cons.2 ⟨subd14_0_169, List.forall_mem_cons.2 ⟨subd14_0_170, List.forall_mem_cons.2 ⟨subd14_0_171, List.forall_mem_cons.2 ⟨subd14_0_172, List.forall_mem_cons.2 ⟨subd14_0_173, List.forall_mem_cons.2 ⟨subd14_0_174, List.forall_mem_cons.2 ⟨subd14_0_175, List.forall_mem_cons.2 ⟨subd14_0_176, List.forall_mem_cons.2 ⟨subd14_0_177, List.forall_mem_cons.2 ⟨subd14_0_178, List.forall_mem_cons.2 ⟨subd14_0_179, List.forall_mem_cons.2 ⟨subd14_0_180, List.forall_mem_cons.2 ⟨subd14_0_181, List.forall_mem_cons.2 ⟨subd14_0_182, List.forall_mem_cons.2 ⟨subd14_0_183, List.forall_mem_cons.2 ⟨subd14_0_184, List.forall_mem_cons.2 ⟨subd14_0_185, List.forall_mem_cons.2 ⟨subd14_0_186, List.forall_mem_cons.2 ⟨subd14_0_187, List.forall_mem_cons.2 ⟨subd14_0_188, List.forall_mem_cons.2 ⟨subd14_0_189, List.forall_mem_cons.2 ⟨subd14_0_190, List.forall_mem_cons.2 ⟨subd14_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_192 : subd14_0 [-1, -1, -4] = true := by decide +kernel
theorem subd14_0_193 : subd14_0 [-1, -1, -3] = true := by decide +kernel
theorem subd14_0_194 : subd14_0 [-1, -1, -2] = true := by decide +kernel
theorem subd14_0_195 : subd14_0 [-1, -1, -1] = true := by decide +kernel
theorem subd14_0_196 : subd14_0 [-1, -1, 0] = true := by decide +kernel
theorem subd14_0_197 : subd14_0 [-1, -1, 1] = true := by decide +kernel
theorem subd14_0_198 : subd14_0 [-1, -1, 2] = true := by decide +kernel
theorem subd14_0_199 : subd14_0 [-1, -1, 3] = true := by decide +kernel
theorem subd14_0_200 : subd14_0 [-1, -1, 4] = true := by decide +kernel
theorem subd14_0_201 : subd14_0 [-1, -1, 5] = true := by decide +kernel
theorem subd14_0_202 : subd14_0 [-1, -1, 6] = true := by decide +kernel
theorem subd14_0_203 : subd14_0 [-1, -1, 7] = true := by decide +kernel
theorem subd14_0_204 : subd14_0 [-1, 0, -8] = true := by decide +kernel
theorem subd14_0_205 : subd14_0 [-1, 0, -7] = true := by decide +kernel
theorem subd14_0_206 : subd14_0 [-1, 0, -6] = true := by decide +kernel
theorem subd14_0_207 : subd14_0 [-1, 0, -5] = true := by decide +kernel
theorem subd14_0_208 : subd14_0 [-1, 0, -4] = true := by decide +kernel
theorem subd14_0_209 : subd14_0 [-1, 0, -3] = true := by decide +kernel
theorem subd14_0_210 : subd14_0 [-1, 0, -2] = true := by decide +kernel
theorem subd14_0_211 : subd14_0 [-1, 0, -1] = true := by decide +kernel
theorem subd14_0_212 : subd14_0 [-1, 0, 0] = true := by decide +kernel
theorem subd14_0_213 : subd14_0 [-1, 0, 1] = true := by decide +kernel
theorem subd14_0_214 : subd14_0 [-1, 0, 2] = true := by decide +kernel
theorem subd14_0_215 : subd14_0 [-1, 0, 3] = true := by decide +kernel
theorem subd14_0_216 : subd14_0 [-1, 0, 4] = true := by decide +kernel
theorem subd14_0_217 : subd14_0 [-1, 0, 5] = true := by decide +kernel
theorem subd14_0_218 : subd14_0 [-1, 0, 6] = true := by decide +kernel
theorem subd14_0_219 : subd14_0 [-1, 0, 7] = true := by decide +kernel
theorem subd14_0_220 : subd14_0 [-1, 1, -8] = true := by decide +kernel
theorem subd14_0_221 : subd14_0 [-1, 1, -7] = true := by decide +kernel
theorem subd14_0_222 : subd14_0 [-1, 1, -6] = true := by decide +kernel
theorem subd14_0_223 : subd14_0 [-1, 1, -5] = true := by decide +kernel
theorem sbd14_0_6 : ∀ q ∈ blkd14_0_6, subd14_0 q = true := by
  unfold blkd14_0_6
  exact List.forall_mem_cons.2 ⟨subd14_0_192, List.forall_mem_cons.2 ⟨subd14_0_193, List.forall_mem_cons.2 ⟨subd14_0_194, List.forall_mem_cons.2 ⟨subd14_0_195, List.forall_mem_cons.2 ⟨subd14_0_196, List.forall_mem_cons.2 ⟨subd14_0_197, List.forall_mem_cons.2 ⟨subd14_0_198, List.forall_mem_cons.2 ⟨subd14_0_199, List.forall_mem_cons.2 ⟨subd14_0_200, List.forall_mem_cons.2 ⟨subd14_0_201, List.forall_mem_cons.2 ⟨subd14_0_202, List.forall_mem_cons.2 ⟨subd14_0_203, List.forall_mem_cons.2 ⟨subd14_0_204, List.forall_mem_cons.2 ⟨subd14_0_205, List.forall_mem_cons.2 ⟨subd14_0_206, List.forall_mem_cons.2 ⟨subd14_0_207, List.forall_mem_cons.2 ⟨subd14_0_208, List.forall_mem_cons.2 ⟨subd14_0_209, List.forall_mem_cons.2 ⟨subd14_0_210, List.forall_mem_cons.2 ⟨subd14_0_211, List.forall_mem_cons.2 ⟨subd14_0_212, List.forall_mem_cons.2 ⟨subd14_0_213, List.forall_mem_cons.2 ⟨subd14_0_214, List.forall_mem_cons.2 ⟨subd14_0_215, List.forall_mem_cons.2 ⟨subd14_0_216, List.forall_mem_cons.2 ⟨subd14_0_217, List.forall_mem_cons.2 ⟨subd14_0_218, List.forall_mem_cons.2 ⟨subd14_0_219, List.forall_mem_cons.2 ⟨subd14_0_220, List.forall_mem_cons.2 ⟨subd14_0_221, List.forall_mem_cons.2 ⟨subd14_0_222, List.forall_mem_cons.2 ⟨subd14_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_224 : subd14_0 [-1, 1, -4] = true := by decide +kernel
theorem subd14_0_225 : subd14_0 [-1, 1, -3] = true := by decide +kernel
theorem subd14_0_226 : subd14_0 [-1, 1, -2] = true := by decide +kernel
theorem subd14_0_227 : subd14_0 [-1, 1, -1] = true := by decide +kernel
theorem subd14_0_228 : subd14_0 [-1, 1, 0] = true := by decide +kernel
theorem subd14_0_229 : subd14_0 [-1, 1, 1] = true := by decide +kernel
theorem subd14_0_230 : subd14_0 [-1, 1, 2] = true := by decide +kernel
theorem subd14_0_231 : subd14_0 [-1, 1, 3] = true := by decide +kernel
theorem subd14_0_232 : subd14_0 [-1, 1, 4] = true := by decide +kernel
theorem subd14_0_233 : subd14_0 [-1, 1, 5] = true := by decide +kernel
theorem subd14_0_234 : subd14_0 [-1, 1, 6] = true := by decide +kernel
theorem subd14_0_235 : subd14_0 [-1, 1, 7] = true := by decide +kernel
theorem subd14_0_236 : subd14_0 [-1, 2, -8] = true := by decide +kernel
theorem subd14_0_237 : subd14_0 [-1, 2, -7] = true := by decide +kernel
theorem subd14_0_238 : subd14_0 [-1, 2, -6] = true := by decide +kernel
theorem subd14_0_239 : subd14_0 [-1, 2, -5] = true := by decide +kernel
theorem subd14_0_240 : subd14_0 [-1, 2, -4] = true := by decide +kernel
theorem subd14_0_241 : subd14_0 [-1, 2, -3] = true := by decide +kernel
theorem subd14_0_242 : subd14_0 [-1, 2, -2] = true := by decide +kernel
theorem subd14_0_243 : subd14_0 [-1, 2, -1] = true := by decide +kernel
theorem subd14_0_244 : subd14_0 [-1, 2, 0] = true := by decide +kernel
theorem subd14_0_245 : subd14_0 [-1, 2, 1] = true := by decide +kernel
theorem subd14_0_246 : subd14_0 [-1, 2, 2] = true := by decide +kernel
theorem subd14_0_247 : subd14_0 [-1, 2, 3] = true := by decide +kernel
theorem subd14_0_248 : subd14_0 [-1, 2, 4] = true := by decide +kernel
theorem subd14_0_249 : subd14_0 [-1, 2, 5] = true := by decide +kernel
theorem subd14_0_250 : subd14_0 [-1, 2, 6] = true := by decide +kernel
theorem subd14_0_251 : subd14_0 [-1, 3, -8] = true := by decide +kernel
theorem subd14_0_252 : subd14_0 [-1, 3, -7] = true := by decide +kernel
theorem subd14_0_253 : subd14_0 [-1, 3, -6] = true := by decide +kernel
theorem subd14_0_254 : subd14_0 [-1, 3, -5] = true := by decide +kernel
theorem subd14_0_255 : subd14_0 [-1, 3, -4] = true := by decide +kernel
theorem sbd14_0_7 : ∀ q ∈ blkd14_0_7, subd14_0 q = true := by
  unfold blkd14_0_7
  exact List.forall_mem_cons.2 ⟨subd14_0_224, List.forall_mem_cons.2 ⟨subd14_0_225, List.forall_mem_cons.2 ⟨subd14_0_226, List.forall_mem_cons.2 ⟨subd14_0_227, List.forall_mem_cons.2 ⟨subd14_0_228, List.forall_mem_cons.2 ⟨subd14_0_229, List.forall_mem_cons.2 ⟨subd14_0_230, List.forall_mem_cons.2 ⟨subd14_0_231, List.forall_mem_cons.2 ⟨subd14_0_232, List.forall_mem_cons.2 ⟨subd14_0_233, List.forall_mem_cons.2 ⟨subd14_0_234, List.forall_mem_cons.2 ⟨subd14_0_235, List.forall_mem_cons.2 ⟨subd14_0_236, List.forall_mem_cons.2 ⟨subd14_0_237, List.forall_mem_cons.2 ⟨subd14_0_238, List.forall_mem_cons.2 ⟨subd14_0_239, List.forall_mem_cons.2 ⟨subd14_0_240, List.forall_mem_cons.2 ⟨subd14_0_241, List.forall_mem_cons.2 ⟨subd14_0_242, List.forall_mem_cons.2 ⟨subd14_0_243, List.forall_mem_cons.2 ⟨subd14_0_244, List.forall_mem_cons.2 ⟨subd14_0_245, List.forall_mem_cons.2 ⟨subd14_0_246, List.forall_mem_cons.2 ⟨subd14_0_247, List.forall_mem_cons.2 ⟨subd14_0_248, List.forall_mem_cons.2 ⟨subd14_0_249, List.forall_mem_cons.2 ⟨subd14_0_250, List.forall_mem_cons.2 ⟨subd14_0_251, List.forall_mem_cons.2 ⟨subd14_0_252, List.forall_mem_cons.2 ⟨subd14_0_253, List.forall_mem_cons.2 ⟨subd14_0_254, List.forall_mem_cons.2 ⟨subd14_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_256 : subd14_0 [-1, 3, -3] = true := by decide +kernel
theorem subd14_0_257 : subd14_0 [-1, 3, -2] = true := by decide +kernel
theorem subd14_0_258 : subd14_0 [-1, 3, -1] = true := by decide +kernel
theorem subd14_0_259 : subd14_0 [-1, 3, 0] = true := by decide +kernel
theorem subd14_0_260 : subd14_0 [-1, 3, 1] = true := by decide +kernel
theorem subd14_0_261 : subd14_0 [-1, 3, 2] = true := by decide +kernel
theorem subd14_0_262 : subd14_0 [-1, 3, 3] = true := by decide +kernel
theorem subd14_0_263 : subd14_0 [-1, 3, 4] = true := by decide +kernel
theorem subd14_0_264 : subd14_0 [-1, 3, 5] = true := by decide +kernel
theorem subd14_0_265 : subd14_0 [-1, 3, 6] = true := by decide +kernel
theorem subd14_0_266 : subd14_0 [-1, 4] = true := by decide +kernel
theorem subd14_0_267 : subd14_0 [-1, 5] = true := by decide +kernel
theorem subd14_0_268 : subd14_0 [-1, 6] = true := by decide +kernel
theorem subd14_0_269 : subd14_0 [0, -7] = true := by decide +kernel
theorem subd14_0_270 : subd14_0 [0, -6] = true := by decide +kernel
theorem subd14_0_271 : subd14_0 [0, -5] = true := by decide +kernel
theorem subd14_0_272 : subd14_0 [0, -4] = true := by decide +kernel
theorem subd14_0_273 : subd14_0 [0, -3, -6] = true := by decide +kernel
theorem subd14_0_274 : subd14_0 [0, -3, -5] = true := by decide +kernel
theorem subd14_0_275 : subd14_0 [0, -3, -4] = true := by decide +kernel
theorem subd14_0_276 : subd14_0 [0, -3, -3] = true := by decide +kernel
theorem subd14_0_277 : subd14_0 [0, -3, -2] = true := by decide +kernel
theorem subd14_0_278 : subd14_0 [0, -3, -1] = true := by decide +kernel
theorem subd14_0_279 : subd14_0 [0, -3, 0] = true := by decide +kernel
theorem subd14_0_280 : subd14_0 [0, -3, 1] = true := by decide +kernel
theorem subd14_0_281 : subd14_0 [0, -3, 2] = true := by decide +kernel
theorem subd14_0_282 : subd14_0 [0, -3, 3] = true := by decide +kernel
theorem subd14_0_283 : subd14_0 [0, -3, 4] = true := by decide +kernel
theorem subd14_0_284 : subd14_0 [0, -3, 5] = true := by decide +kernel
theorem subd14_0_285 : subd14_0 [0, -3, 6] = true := by decide +kernel
theorem subd14_0_286 : subd14_0 [0, -3, 7] = true := by decide +kernel
theorem subd14_0_287 : subd14_0 [0, -2, -7] = true := by decide +kernel
theorem sbd14_0_8 : ∀ q ∈ blkd14_0_8, subd14_0 q = true := by
  unfold blkd14_0_8
  exact List.forall_mem_cons.2 ⟨subd14_0_256, List.forall_mem_cons.2 ⟨subd14_0_257, List.forall_mem_cons.2 ⟨subd14_0_258, List.forall_mem_cons.2 ⟨subd14_0_259, List.forall_mem_cons.2 ⟨subd14_0_260, List.forall_mem_cons.2 ⟨subd14_0_261, List.forall_mem_cons.2 ⟨subd14_0_262, List.forall_mem_cons.2 ⟨subd14_0_263, List.forall_mem_cons.2 ⟨subd14_0_264, List.forall_mem_cons.2 ⟨subd14_0_265, List.forall_mem_cons.2 ⟨subd14_0_266, List.forall_mem_cons.2 ⟨subd14_0_267, List.forall_mem_cons.2 ⟨subd14_0_268, List.forall_mem_cons.2 ⟨subd14_0_269, List.forall_mem_cons.2 ⟨subd14_0_270, List.forall_mem_cons.2 ⟨subd14_0_271, List.forall_mem_cons.2 ⟨subd14_0_272, List.forall_mem_cons.2 ⟨subd14_0_273, List.forall_mem_cons.2 ⟨subd14_0_274, List.forall_mem_cons.2 ⟨subd14_0_275, List.forall_mem_cons.2 ⟨subd14_0_276, List.forall_mem_cons.2 ⟨subd14_0_277, List.forall_mem_cons.2 ⟨subd14_0_278, List.forall_mem_cons.2 ⟨subd14_0_279, List.forall_mem_cons.2 ⟨subd14_0_280, List.forall_mem_cons.2 ⟨subd14_0_281, List.forall_mem_cons.2 ⟨subd14_0_282, List.forall_mem_cons.2 ⟨subd14_0_283, List.forall_mem_cons.2 ⟨subd14_0_284, List.forall_mem_cons.2 ⟨subd14_0_285, List.forall_mem_cons.2 ⟨subd14_0_286, List.forall_mem_cons.2 ⟨subd14_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_288 : subd14_0 [0, -2, -6] = true := by decide +kernel
theorem subd14_0_289 : subd14_0 [0, -2, -5] = true := by decide +kernel
theorem subd14_0_290 : subd14_0 [0, -2, -4] = true := by decide +kernel
theorem subd14_0_291 : subd14_0 [0, -2, -3] = true := by decide +kernel
theorem subd14_0_292 : subd14_0 [0, -2, -2] = true := by decide +kernel
theorem subd14_0_293 : subd14_0 [0, -2, -1] = true := by decide +kernel
theorem subd14_0_294 : subd14_0 [0, -2, 0] = true := by decide +kernel
theorem subd14_0_295 : subd14_0 [0, -2, 1] = true := by decide +kernel
theorem subd14_0_296 : subd14_0 [0, -2, 2] = true := by decide +kernel
theorem subd14_0_297 : subd14_0 [0, -2, 3] = true := by decide +kernel
theorem subd14_0_298 : subd14_0 [0, -2, 4] = true := by decide +kernel
theorem subd14_0_299 : subd14_0 [0, -2, 5] = true := by decide +kernel
theorem subd14_0_300 : subd14_0 [0, -2, 6] = true := by decide +kernel
theorem subd14_0_301 : subd14_0 [0, -2, 7] = true := by decide +kernel
theorem subd14_0_302 : subd14_0 [0, -1, -8] = true := by decide +kernel
theorem subd14_0_303 : subd14_0 [0, -1, -7] = true := by decide +kernel
theorem subd14_0_304 : subd14_0 [0, -1, -6] = true := by decide +kernel
theorem subd14_0_305 : subd14_0 [0, -1, -5] = true := by decide +kernel
theorem subd14_0_306 : subd14_0 [0, -1, -4] = true := by decide +kernel
theorem subd14_0_307 : subd14_0 [0, -1, -3] = true := by decide +kernel
theorem subd14_0_308 : subd14_0 [0, -1, -2] = true := by decide +kernel
theorem subd14_0_309 : subd14_0 [0, -1, -1] = true := by decide +kernel
theorem subd14_0_310 : subd14_0 [0, -1, 0] = true := by decide +kernel
theorem subd14_0_311 : subd14_0 [0, -1, 1] = true := by decide +kernel
theorem subd14_0_312 : subd14_0 [0, -1, 2] = true := by decide +kernel
theorem subd14_0_313 : subd14_0 [0, -1, 3] = true := by decide +kernel
theorem subd14_0_314 : subd14_0 [0, -1, 4] = true := by decide +kernel
theorem subd14_0_315 : subd14_0 [0, -1, 5] = true := by decide +kernel
theorem subd14_0_316 : subd14_0 [0, -1, 6] = true := by decide +kernel
theorem subd14_0_317 : subd14_0 [0, -1, 7] = true := by decide +kernel
theorem subd14_0_318 : subd14_0 [0, 0, -8] = true := by decide +kernel
theorem subd14_0_319 : subd14_0 [0, 0, -7] = true := by decide +kernel
theorem sbd14_0_9 : ∀ q ∈ blkd14_0_9, subd14_0 q = true := by
  unfold blkd14_0_9
  exact List.forall_mem_cons.2 ⟨subd14_0_288, List.forall_mem_cons.2 ⟨subd14_0_289, List.forall_mem_cons.2 ⟨subd14_0_290, List.forall_mem_cons.2 ⟨subd14_0_291, List.forall_mem_cons.2 ⟨subd14_0_292, List.forall_mem_cons.2 ⟨subd14_0_293, List.forall_mem_cons.2 ⟨subd14_0_294, List.forall_mem_cons.2 ⟨subd14_0_295, List.forall_mem_cons.2 ⟨subd14_0_296, List.forall_mem_cons.2 ⟨subd14_0_297, List.forall_mem_cons.2 ⟨subd14_0_298, List.forall_mem_cons.2 ⟨subd14_0_299, List.forall_mem_cons.2 ⟨subd14_0_300, List.forall_mem_cons.2 ⟨subd14_0_301, List.forall_mem_cons.2 ⟨subd14_0_302, List.forall_mem_cons.2 ⟨subd14_0_303, List.forall_mem_cons.2 ⟨subd14_0_304, List.forall_mem_cons.2 ⟨subd14_0_305, List.forall_mem_cons.2 ⟨subd14_0_306, List.forall_mem_cons.2 ⟨subd14_0_307, List.forall_mem_cons.2 ⟨subd14_0_308, List.forall_mem_cons.2 ⟨subd14_0_309, List.forall_mem_cons.2 ⟨subd14_0_310, List.forall_mem_cons.2 ⟨subd14_0_311, List.forall_mem_cons.2 ⟨subd14_0_312, List.forall_mem_cons.2 ⟨subd14_0_313, List.forall_mem_cons.2 ⟨subd14_0_314, List.forall_mem_cons.2 ⟨subd14_0_315, List.forall_mem_cons.2 ⟨subd14_0_316, List.forall_mem_cons.2 ⟨subd14_0_317, List.forall_mem_cons.2 ⟨subd14_0_318, List.forall_mem_cons.2 ⟨subd14_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_320 : subd14_0 [0, 0, -6] = true := by decide +kernel
theorem subd14_0_321 : subd14_0 [0, 0, -5] = true := by decide +kernel
theorem subd14_0_322 : subd14_0 [0, 0, -4] = true := by decide +kernel
theorem subd14_0_323 : subd14_0 [0, 0, -3] = true := by decide +kernel
theorem subd14_0_324 : subd14_0 [0, 0, -2] = true := by decide +kernel
theorem subd14_0_325 : subd14_0 [0, 0, -1] = true := by decide +kernel
theorem subd14_0_326 : subd14_0 [0, 0, 0] = true := by decide +kernel
theorem subd14_0_327 : subd14_0 [0, 0, 1] = true := by decide +kernel
theorem subd14_0_328 : subd14_0 [0, 0, 2] = true := by decide +kernel
theorem subd14_0_329 : subd14_0 [0, 0, 3] = true := by decide +kernel
theorem subd14_0_330 : subd14_0 [0, 0, 4] = true := by decide +kernel
theorem subd14_0_331 : subd14_0 [0, 0, 5] = true := by decide +kernel
theorem subd14_0_332 : subd14_0 [0, 0, 6] = true := by decide +kernel
theorem subd14_0_333 : subd14_0 [0, 0, 7] = true := by decide +kernel
theorem subd14_0_334 : subd14_0 [0, 1, -8] = true := by decide +kernel
theorem subd14_0_335 : subd14_0 [0, 1, -7] = true := by decide +kernel
theorem subd14_0_336 : subd14_0 [0, 1, -6] = true := by decide +kernel
theorem subd14_0_337 : subd14_0 [0, 1, -5] = true := by decide +kernel
theorem subd14_0_338 : subd14_0 [0, 1, -4] = true := by decide +kernel
theorem subd14_0_339 : subd14_0 [0, 1, -3] = true := by decide +kernel
theorem subd14_0_340 : subd14_0 [0, 1, -2] = true := by decide +kernel
theorem subd14_0_341 : subd14_0 [0, 1, -1] = true := by decide +kernel
theorem subd14_0_342 : subd14_0 [0, 1, 0] = true := by decide +kernel
theorem subd14_0_343 : subd14_0 [0, 1, 1] = true := by decide +kernel
theorem subd14_0_344 : subd14_0 [0, 1, 2] = true := by decide +kernel
theorem subd14_0_345 : subd14_0 [0, 1, 3] = true := by decide +kernel
theorem subd14_0_346 : subd14_0 [0, 1, 4] = true := by decide +kernel
theorem subd14_0_347 : subd14_0 [0, 1, 5] = true := by decide +kernel
theorem subd14_0_348 : subd14_0 [0, 1, 6] = true := by decide +kernel
theorem subd14_0_349 : subd14_0 [0, 1, 7] = true := by decide +kernel
theorem subd14_0_350 : subd14_0 [0, 2, -8] = true := by decide +kernel
theorem subd14_0_351 : subd14_0 [0, 2, -7] = true := by decide +kernel
theorem sbd14_0_10 : ∀ q ∈ blkd14_0_10, subd14_0 q = true := by
  unfold blkd14_0_10
  exact List.forall_mem_cons.2 ⟨subd14_0_320, List.forall_mem_cons.2 ⟨subd14_0_321, List.forall_mem_cons.2 ⟨subd14_0_322, List.forall_mem_cons.2 ⟨subd14_0_323, List.forall_mem_cons.2 ⟨subd14_0_324, List.forall_mem_cons.2 ⟨subd14_0_325, List.forall_mem_cons.2 ⟨subd14_0_326, List.forall_mem_cons.2 ⟨subd14_0_327, List.forall_mem_cons.2 ⟨subd14_0_328, List.forall_mem_cons.2 ⟨subd14_0_329, List.forall_mem_cons.2 ⟨subd14_0_330, List.forall_mem_cons.2 ⟨subd14_0_331, List.forall_mem_cons.2 ⟨subd14_0_332, List.forall_mem_cons.2 ⟨subd14_0_333, List.forall_mem_cons.2 ⟨subd14_0_334, List.forall_mem_cons.2 ⟨subd14_0_335, List.forall_mem_cons.2 ⟨subd14_0_336, List.forall_mem_cons.2 ⟨subd14_0_337, List.forall_mem_cons.2 ⟨subd14_0_338, List.forall_mem_cons.2 ⟨subd14_0_339, List.forall_mem_cons.2 ⟨subd14_0_340, List.forall_mem_cons.2 ⟨subd14_0_341, List.forall_mem_cons.2 ⟨subd14_0_342, List.forall_mem_cons.2 ⟨subd14_0_343, List.forall_mem_cons.2 ⟨subd14_0_344, List.forall_mem_cons.2 ⟨subd14_0_345, List.forall_mem_cons.2 ⟨subd14_0_346, List.forall_mem_cons.2 ⟨subd14_0_347, List.forall_mem_cons.2 ⟨subd14_0_348, List.forall_mem_cons.2 ⟨subd14_0_349, List.forall_mem_cons.2 ⟨subd14_0_350, List.forall_mem_cons.2 ⟨subd14_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_352 : subd14_0 [0, 2, -6] = true := by decide +kernel
theorem subd14_0_353 : subd14_0 [0, 2, -5] = true := by decide +kernel
theorem subd14_0_354 : subd14_0 [0, 2, -4] = true := by decide +kernel
theorem subd14_0_355 : subd14_0 [0, 2, -3] = true := by decide +kernel
theorem subd14_0_356 : subd14_0 [0, 2, -2] = true := by decide +kernel
theorem subd14_0_357 : subd14_0 [0, 2, -1] = true := by decide +kernel
theorem subd14_0_358 : subd14_0 [0, 2, 0] = true := by decide +kernel
theorem subd14_0_359 : subd14_0 [0, 2, 1] = true := by decide +kernel
theorem subd14_0_360 : subd14_0 [0, 2, 2] = true := by decide +kernel
theorem subd14_0_361 : subd14_0 [0, 2, 3] = true := by decide +kernel
theorem subd14_0_362 : subd14_0 [0, 2, 4] = true := by decide +kernel
theorem subd14_0_363 : subd14_0 [0, 2, 5] = true := by decide +kernel
theorem subd14_0_364 : subd14_0 [0, 2, 6] = true := by decide +kernel
theorem subd14_0_365 : subd14_0 [0, 3, -8] = true := by decide +kernel
theorem subd14_0_366 : subd14_0 [0, 3, -7] = true := by decide +kernel
theorem subd14_0_367 : subd14_0 [0, 3, -6] = true := by decide +kernel
theorem subd14_0_368 : subd14_0 [0, 3, -5] = true := by decide +kernel
theorem subd14_0_369 : subd14_0 [0, 3, -4] = true := by decide +kernel
theorem subd14_0_370 : subd14_0 [0, 3, -3] = true := by decide +kernel
theorem subd14_0_371 : subd14_0 [0, 3, -2] = true := by decide +kernel
theorem subd14_0_372 : subd14_0 [0, 3, -1] = true := by decide +kernel
theorem subd14_0_373 : subd14_0 [0, 3, 0] = true := by decide +kernel
theorem subd14_0_374 : subd14_0 [0, 3, 1] = true := by decide +kernel
theorem subd14_0_375 : subd14_0 [0, 3, 2] = true := by decide +kernel
theorem subd14_0_376 : subd14_0 [0, 3, 3] = true := by decide +kernel
theorem subd14_0_377 : subd14_0 [0, 3, 4] = true := by decide +kernel
theorem subd14_0_378 : subd14_0 [0, 3, 5] = true := by decide +kernel
theorem subd14_0_379 : subd14_0 [0, 4] = true := by decide +kernel
theorem subd14_0_380 : subd14_0 [0, 5] = true := by decide +kernel
theorem subd14_0_381 : subd14_0 [0, 6] = true := by decide +kernel
theorem subd14_0_382 : subd14_0 [1, -7] = true := by decide +kernel
theorem subd14_0_383 : subd14_0 [1, -6] = true := by decide +kernel
theorem sbd14_0_11 : ∀ q ∈ blkd14_0_11, subd14_0 q = true := by
  unfold blkd14_0_11
  exact List.forall_mem_cons.2 ⟨subd14_0_352, List.forall_mem_cons.2 ⟨subd14_0_353, List.forall_mem_cons.2 ⟨subd14_0_354, List.forall_mem_cons.2 ⟨subd14_0_355, List.forall_mem_cons.2 ⟨subd14_0_356, List.forall_mem_cons.2 ⟨subd14_0_357, List.forall_mem_cons.2 ⟨subd14_0_358, List.forall_mem_cons.2 ⟨subd14_0_359, List.forall_mem_cons.2 ⟨subd14_0_360, List.forall_mem_cons.2 ⟨subd14_0_361, List.forall_mem_cons.2 ⟨subd14_0_362, List.forall_mem_cons.2 ⟨subd14_0_363, List.forall_mem_cons.2 ⟨subd14_0_364, List.forall_mem_cons.2 ⟨subd14_0_365, List.forall_mem_cons.2 ⟨subd14_0_366, List.forall_mem_cons.2 ⟨subd14_0_367, List.forall_mem_cons.2 ⟨subd14_0_368, List.forall_mem_cons.2 ⟨subd14_0_369, List.forall_mem_cons.2 ⟨subd14_0_370, List.forall_mem_cons.2 ⟨subd14_0_371, List.forall_mem_cons.2 ⟨subd14_0_372, List.forall_mem_cons.2 ⟨subd14_0_373, List.forall_mem_cons.2 ⟨subd14_0_374, List.forall_mem_cons.2 ⟨subd14_0_375, List.forall_mem_cons.2 ⟨subd14_0_376, List.forall_mem_cons.2 ⟨subd14_0_377, List.forall_mem_cons.2 ⟨subd14_0_378, List.forall_mem_cons.2 ⟨subd14_0_379, List.forall_mem_cons.2 ⟨subd14_0_380, List.forall_mem_cons.2 ⟨subd14_0_381, List.forall_mem_cons.2 ⟨subd14_0_382, List.forall_mem_cons.2 ⟨subd14_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_384 : subd14_0 [1, -5] = true := by decide +kernel
theorem subd14_0_385 : subd14_0 [1, -4] = true := by decide +kernel
theorem subd14_0_386 : subd14_0 [1, -3, -7] = true := by decide +kernel
theorem subd14_0_387 : subd14_0 [1, -3, -6] = true := by decide +kernel
theorem subd14_0_388 : subd14_0 [1, -3, -5] = true := by decide +kernel
theorem subd14_0_389 : subd14_0 [1, -3, -4] = true := by decide +kernel
theorem subd14_0_390 : subd14_0 [1, -3, -3] = true := by decide +kernel
theorem subd14_0_391 : subd14_0 [1, -3, -2] = true := by decide +kernel
theorem subd14_0_392 : subd14_0 [1, -3, -1] = true := by decide +kernel
theorem subd14_0_393 : subd14_0 [1, -3, 0] = true := by decide +kernel
theorem subd14_0_394 : subd14_0 [1, -3, 1] = true := by decide +kernel
theorem subd14_0_395 : subd14_0 [1, -3, 2] = true := by decide +kernel
theorem subd14_0_396 : subd14_0 [1, -3, 3] = true := by decide +kernel
theorem subd14_0_397 : subd14_0 [1, -3, 4] = true := by decide +kernel
theorem subd14_0_398 : subd14_0 [1, -3, 5] = true := by decide +kernel
theorem subd14_0_399 : subd14_0 [1, -3, 6] = true := by decide +kernel
theorem subd14_0_400 : subd14_0 [1, -3, 7] = true := by decide +kernel
theorem subd14_0_401 : subd14_0 [1, -2, -7] = true := by decide +kernel
theorem subd14_0_402 : subd14_0 [1, -2, -6] = true := by decide +kernel
theorem subd14_0_403 : subd14_0 [1, -2, -5] = true := by decide +kernel
theorem subd14_0_404 : subd14_0 [1, -2, -4] = true := by decide +kernel
theorem subd14_0_405 : subd14_0 [1, -2, -3] = true := by decide +kernel
theorem subd14_0_406 : subd14_0 [1, -2, -2] = true := by decide +kernel
theorem subd14_0_407 : subd14_0 [1, -2, -1] = true := by decide +kernel
theorem subd14_0_408 : subd14_0 [1, -2, 0] = true := by decide +kernel
theorem subd14_0_409 : subd14_0 [1, -2, 1] = true := by decide +kernel
theorem subd14_0_410 : subd14_0 [1, -2, 2] = true := by decide +kernel
theorem subd14_0_411 : subd14_0 [1, -2, 3] = true := by decide +kernel
theorem subd14_0_412 : subd14_0 [1, -2, 4] = true := by decide +kernel
theorem subd14_0_413 : subd14_0 [1, -2, 5] = true := by decide +kernel
theorem subd14_0_414 : subd14_0 [1, -2, 6] = true := by decide +kernel
theorem subd14_0_415 : subd14_0 [1, -2, 7] = true := by decide +kernel
theorem sbd14_0_12 : ∀ q ∈ blkd14_0_12, subd14_0 q = true := by
  unfold blkd14_0_12
  exact List.forall_mem_cons.2 ⟨subd14_0_384, List.forall_mem_cons.2 ⟨subd14_0_385, List.forall_mem_cons.2 ⟨subd14_0_386, List.forall_mem_cons.2 ⟨subd14_0_387, List.forall_mem_cons.2 ⟨subd14_0_388, List.forall_mem_cons.2 ⟨subd14_0_389, List.forall_mem_cons.2 ⟨subd14_0_390, List.forall_mem_cons.2 ⟨subd14_0_391, List.forall_mem_cons.2 ⟨subd14_0_392, List.forall_mem_cons.2 ⟨subd14_0_393, List.forall_mem_cons.2 ⟨subd14_0_394, List.forall_mem_cons.2 ⟨subd14_0_395, List.forall_mem_cons.2 ⟨subd14_0_396, List.forall_mem_cons.2 ⟨subd14_0_397, List.forall_mem_cons.2 ⟨subd14_0_398, List.forall_mem_cons.2 ⟨subd14_0_399, List.forall_mem_cons.2 ⟨subd14_0_400, List.forall_mem_cons.2 ⟨subd14_0_401, List.forall_mem_cons.2 ⟨subd14_0_402, List.forall_mem_cons.2 ⟨subd14_0_403, List.forall_mem_cons.2 ⟨subd14_0_404, List.forall_mem_cons.2 ⟨subd14_0_405, List.forall_mem_cons.2 ⟨subd14_0_406, List.forall_mem_cons.2 ⟨subd14_0_407, List.forall_mem_cons.2 ⟨subd14_0_408, List.forall_mem_cons.2 ⟨subd14_0_409, List.forall_mem_cons.2 ⟨subd14_0_410, List.forall_mem_cons.2 ⟨subd14_0_411, List.forall_mem_cons.2 ⟨subd14_0_412, List.forall_mem_cons.2 ⟨subd14_0_413, List.forall_mem_cons.2 ⟨subd14_0_414, List.forall_mem_cons.2 ⟨subd14_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_416 : subd14_0 [1, -1, -8] = true := by decide +kernel
theorem subd14_0_417 : subd14_0 [1, -1, -7] = true := by decide +kernel
theorem subd14_0_418 : subd14_0 [1, -1, -6] = true := by decide +kernel
theorem subd14_0_419 : subd14_0 [1, -1, -5] = true := by decide +kernel
theorem subd14_0_420 : subd14_0 [1, -1, -4] = true := by decide +kernel
theorem subd14_0_421 : subd14_0 [1, -1, -3] = true := by decide +kernel
theorem subd14_0_422 : subd14_0 [1, -1, -2] = true := by decide +kernel
theorem subd14_0_423 : subd14_0 [1, -1, -1] = true := by decide +kernel
theorem subd14_0_424 : subd14_0 [1, -1, 0] = true := by decide +kernel
theorem subd14_0_425 : subd14_0 [1, -1, 1] = true := by decide +kernel
theorem subd14_0_426 : subd14_0 [1, -1, 2] = true := by decide +kernel
theorem subd14_0_427 : subd14_0 [1, -1, 3] = true := by decide +kernel
theorem subd14_0_428 : subd14_0 [1, -1, 4] = true := by decide +kernel
theorem subd14_0_429 : subd14_0 [1, -1, 5] = true := by decide +kernel
theorem subd14_0_430 : subd14_0 [1, -1, 6] = true := by decide +kernel
theorem subd14_0_431 : subd14_0 [1, -1, 7] = true := by decide +kernel
theorem subd14_0_432 : subd14_0 [1, 0, -8] = true := by decide +kernel
theorem subd14_0_433 : subd14_0 [1, 0, -7] = true := by decide +kernel
theorem subd14_0_434 : subd14_0 [1, 0, -6] = true := by decide +kernel
theorem subd14_0_435 : subd14_0 [1, 0, -5] = true := by decide +kernel
theorem subd14_0_436 : subd14_0 [1, 0, -4] = true := by decide +kernel
theorem subd14_0_437 : subd14_0 [1, 0, -3] = true := by decide +kernel
theorem subd14_0_438 : subd14_0 [1, 0, -2] = true := by decide +kernel
theorem subd14_0_439 : subd14_0 [1, 0, -1] = true := by decide +kernel
theorem subd14_0_440 : subd14_0 [1, 0, 0] = true := by decide +kernel
theorem subd14_0_441 : subd14_0 [1, 0, 1] = true := by decide +kernel
theorem subd14_0_442 : subd14_0 [1, 0, 2] = true := by decide +kernel
theorem subd14_0_443 : subd14_0 [1, 0, 3] = true := by decide +kernel
theorem subd14_0_444 : subd14_0 [1, 0, 4] = true := by decide +kernel
theorem subd14_0_445 : subd14_0 [1, 0, 5] = true := by decide +kernel
theorem subd14_0_446 : subd14_0 [1, 0, 6] = true := by decide +kernel
theorem subd14_0_447 : subd14_0 [1, 0, 7] = true := by decide +kernel
theorem sbd14_0_13 : ∀ q ∈ blkd14_0_13, subd14_0 q = true := by
  unfold blkd14_0_13
  exact List.forall_mem_cons.2 ⟨subd14_0_416, List.forall_mem_cons.2 ⟨subd14_0_417, List.forall_mem_cons.2 ⟨subd14_0_418, List.forall_mem_cons.2 ⟨subd14_0_419, List.forall_mem_cons.2 ⟨subd14_0_420, List.forall_mem_cons.2 ⟨subd14_0_421, List.forall_mem_cons.2 ⟨subd14_0_422, List.forall_mem_cons.2 ⟨subd14_0_423, List.forall_mem_cons.2 ⟨subd14_0_424, List.forall_mem_cons.2 ⟨subd14_0_425, List.forall_mem_cons.2 ⟨subd14_0_426, List.forall_mem_cons.2 ⟨subd14_0_427, List.forall_mem_cons.2 ⟨subd14_0_428, List.forall_mem_cons.2 ⟨subd14_0_429, List.forall_mem_cons.2 ⟨subd14_0_430, List.forall_mem_cons.2 ⟨subd14_0_431, List.forall_mem_cons.2 ⟨subd14_0_432, List.forall_mem_cons.2 ⟨subd14_0_433, List.forall_mem_cons.2 ⟨subd14_0_434, List.forall_mem_cons.2 ⟨subd14_0_435, List.forall_mem_cons.2 ⟨subd14_0_436, List.forall_mem_cons.2 ⟨subd14_0_437, List.forall_mem_cons.2 ⟨subd14_0_438, List.forall_mem_cons.2 ⟨subd14_0_439, List.forall_mem_cons.2 ⟨subd14_0_440, List.forall_mem_cons.2 ⟨subd14_0_441, List.forall_mem_cons.2 ⟨subd14_0_442, List.forall_mem_cons.2 ⟨subd14_0_443, List.forall_mem_cons.2 ⟨subd14_0_444, List.forall_mem_cons.2 ⟨subd14_0_445, List.forall_mem_cons.2 ⟨subd14_0_446, List.forall_mem_cons.2 ⟨subd14_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_448 : subd14_0 [1, 1, -8] = true := by decide +kernel
theorem subd14_0_449 : subd14_0 [1, 1, -7] = true := by decide +kernel
theorem subd14_0_450 : subd14_0 [1, 1, -6] = true := by decide +kernel
theorem subd14_0_451 : subd14_0 [1, 1, -5] = true := by decide +kernel
theorem subd14_0_452 : subd14_0 [1, 1, -4] = true := by decide +kernel
theorem subd14_0_453 : subd14_0 [1, 1, -3] = true := by decide +kernel
theorem subd14_0_454 : subd14_0 [1, 1, -2] = true := by decide +kernel
theorem subd14_0_455 : subd14_0 [1, 1, -1] = true := by decide +kernel
theorem subd14_0_456 : subd14_0 [1, 1, 0] = true := by decide +kernel
theorem subd14_0_457 : subd14_0 [1, 1, 1] = true := by decide +kernel
theorem subd14_0_458 : subd14_0 [1, 1, 2] = true := by decide +kernel
theorem subd14_0_459 : subd14_0 [1, 1, 3] = true := by decide +kernel
theorem subd14_0_460 : subd14_0 [1, 1, 4] = true := by decide +kernel
theorem subd14_0_461 : subd14_0 [1, 1, 5] = true := by decide +kernel
theorem subd14_0_462 : subd14_0 [1, 1, 6] = true := by decide +kernel
theorem subd14_0_463 : subd14_0 [1, 2, -8] = true := by decide +kernel
theorem subd14_0_464 : subd14_0 [1, 2, -7] = true := by decide +kernel
theorem subd14_0_465 : subd14_0 [1, 2, -6] = true := by decide +kernel
theorem subd14_0_466 : subd14_0 [1, 2, -5] = true := by decide +kernel
theorem subd14_0_467 : subd14_0 [1, 2, -4] = true := by decide +kernel
theorem subd14_0_468 : subd14_0 [1, 2, -3] = true := by decide +kernel
theorem subd14_0_469 : subd14_0 [1, 2, -2] = true := by decide +kernel
theorem subd14_0_470 : subd14_0 [1, 2, -1] = true := by decide +kernel
theorem subd14_0_471 : subd14_0 [1, 2, 0] = true := by decide +kernel
theorem subd14_0_472 : subd14_0 [1, 2, 1] = true := by decide +kernel
theorem subd14_0_473 : subd14_0 [1, 2, 2] = true := by decide +kernel
theorem subd14_0_474 : subd14_0 [1, 2, 3] = true := by decide +kernel
theorem subd14_0_475 : subd14_0 [1, 2, 4] = true := by decide +kernel
theorem subd14_0_476 : subd14_0 [1, 2, 5] = true := by decide +kernel
theorem subd14_0_477 : subd14_0 [1, 2, 6] = true := by decide +kernel
theorem subd14_0_478 : subd14_0 [1, 3, -8] = true := by decide +kernel
theorem subd14_0_479 : subd14_0 [1, 3, -7] = true := by decide +kernel
theorem sbd14_0_14 : ∀ q ∈ blkd14_0_14, subd14_0 q = true := by
  unfold blkd14_0_14
  exact List.forall_mem_cons.2 ⟨subd14_0_448, List.forall_mem_cons.2 ⟨subd14_0_449, List.forall_mem_cons.2 ⟨subd14_0_450, List.forall_mem_cons.2 ⟨subd14_0_451, List.forall_mem_cons.2 ⟨subd14_0_452, List.forall_mem_cons.2 ⟨subd14_0_453, List.forall_mem_cons.2 ⟨subd14_0_454, List.forall_mem_cons.2 ⟨subd14_0_455, List.forall_mem_cons.2 ⟨subd14_0_456, List.forall_mem_cons.2 ⟨subd14_0_457, List.forall_mem_cons.2 ⟨subd14_0_458, List.forall_mem_cons.2 ⟨subd14_0_459, List.forall_mem_cons.2 ⟨subd14_0_460, List.forall_mem_cons.2 ⟨subd14_0_461, List.forall_mem_cons.2 ⟨subd14_0_462, List.forall_mem_cons.2 ⟨subd14_0_463, List.forall_mem_cons.2 ⟨subd14_0_464, List.forall_mem_cons.2 ⟨subd14_0_465, List.forall_mem_cons.2 ⟨subd14_0_466, List.forall_mem_cons.2 ⟨subd14_0_467, List.forall_mem_cons.2 ⟨subd14_0_468, List.forall_mem_cons.2 ⟨subd14_0_469, List.forall_mem_cons.2 ⟨subd14_0_470, List.forall_mem_cons.2 ⟨subd14_0_471, List.forall_mem_cons.2 ⟨subd14_0_472, List.forall_mem_cons.2 ⟨subd14_0_473, List.forall_mem_cons.2 ⟨subd14_0_474, List.forall_mem_cons.2 ⟨subd14_0_475, List.forall_mem_cons.2 ⟨subd14_0_476, List.forall_mem_cons.2 ⟨subd14_0_477, List.forall_mem_cons.2 ⟨subd14_0_478, List.forall_mem_cons.2 ⟨subd14_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_480 : subd14_0 [1, 3, -6] = true := by decide +kernel
theorem subd14_0_481 : subd14_0 [1, 3, -5] = true := by decide +kernel
theorem subd14_0_482 : subd14_0 [1, 3, -4] = true := by decide +kernel
theorem subd14_0_483 : subd14_0 [1, 3, -3] = true := by decide +kernel
theorem subd14_0_484 : subd14_0 [1, 3, -2] = true := by decide +kernel
theorem subd14_0_485 : subd14_0 [1, 3, -1] = true := by decide +kernel
theorem subd14_0_486 : subd14_0 [1, 3, 0] = true := by decide +kernel
theorem subd14_0_487 : subd14_0 [1, 3, 1] = true := by decide +kernel
theorem subd14_0_488 : subd14_0 [1, 3, 2] = true := by decide +kernel
theorem subd14_0_489 : subd14_0 [1, 3, 3] = true := by decide +kernel
theorem subd14_0_490 : subd14_0 [1, 3, 4] = true := by decide +kernel
theorem subd14_0_491 : subd14_0 [1, 3, 5] = true := by decide +kernel
theorem subd14_0_492 : subd14_0 [1, 4] = true := by decide +kernel
theorem subd14_0_493 : subd14_0 [1, 5] = true := by decide +kernel
theorem subd14_0_494 : subd14_0 [1, 6] = true := by decide +kernel
theorem subd14_0_495 : subd14_0 [2, -7] = true := by decide +kernel
theorem subd14_0_496 : subd14_0 [2, -6] = true := by decide +kernel
theorem subd14_0_497 : subd14_0 [2, -5] = true := by decide +kernel
theorem subd14_0_498 : subd14_0 [2, -4] = true := by decide +kernel
theorem subd14_0_499 : subd14_0 [2, -3] = true := by decide +kernel
theorem subd14_0_500 : subd14_0 [2, -2, -7] = true := by decide +kernel
theorem subd14_0_501 : subd14_0 [2, -2, -6] = true := by decide +kernel
theorem subd14_0_502 : subd14_0 [2, -2, -5] = true := by decide +kernel
theorem subd14_0_503 : subd14_0 [2, -2, -4] = true := by decide +kernel
theorem subd14_0_504 : subd14_0 [2, -2, -3] = true := by decide +kernel
theorem subd14_0_505 : subd14_0 [2, -2, -2] = true := by decide +kernel
theorem subd14_0_506 : subd14_0 [2, -2, -1] = true := by decide +kernel
theorem subd14_0_507 : subd14_0 [2, -2, 0] = true := by decide +kernel
theorem subd14_0_508 : subd14_0 [2, -2, 1] = true := by decide +kernel
theorem subd14_0_509 : subd14_0 [2, -2, 2] = true := by decide +kernel
theorem subd14_0_510 : subd14_0 [2, -2, 3] = true := by decide +kernel
theorem subd14_0_511 : subd14_0 [2, -2, 4] = true := by decide +kernel
theorem sbd14_0_15 : ∀ q ∈ blkd14_0_15, subd14_0 q = true := by
  unfold blkd14_0_15
  exact List.forall_mem_cons.2 ⟨subd14_0_480, List.forall_mem_cons.2 ⟨subd14_0_481, List.forall_mem_cons.2 ⟨subd14_0_482, List.forall_mem_cons.2 ⟨subd14_0_483, List.forall_mem_cons.2 ⟨subd14_0_484, List.forall_mem_cons.2 ⟨subd14_0_485, List.forall_mem_cons.2 ⟨subd14_0_486, List.forall_mem_cons.2 ⟨subd14_0_487, List.forall_mem_cons.2 ⟨subd14_0_488, List.forall_mem_cons.2 ⟨subd14_0_489, List.forall_mem_cons.2 ⟨subd14_0_490, List.forall_mem_cons.2 ⟨subd14_0_491, List.forall_mem_cons.2 ⟨subd14_0_492, List.forall_mem_cons.2 ⟨subd14_0_493, List.forall_mem_cons.2 ⟨subd14_0_494, List.forall_mem_cons.2 ⟨subd14_0_495, List.forall_mem_cons.2 ⟨subd14_0_496, List.forall_mem_cons.2 ⟨subd14_0_497, List.forall_mem_cons.2 ⟨subd14_0_498, List.forall_mem_cons.2 ⟨subd14_0_499, List.forall_mem_cons.2 ⟨subd14_0_500, List.forall_mem_cons.2 ⟨subd14_0_501, List.forall_mem_cons.2 ⟨subd14_0_502, List.forall_mem_cons.2 ⟨subd14_0_503, List.forall_mem_cons.2 ⟨subd14_0_504, List.forall_mem_cons.2 ⟨subd14_0_505, List.forall_mem_cons.2 ⟨subd14_0_506, List.forall_mem_cons.2 ⟨subd14_0_507, List.forall_mem_cons.2 ⟨subd14_0_508, List.forall_mem_cons.2 ⟨subd14_0_509, List.forall_mem_cons.2 ⟨subd14_0_510, List.forall_mem_cons.2 ⟨subd14_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_512 : subd14_0 [2, -2, 5] = true := by decide +kernel
theorem subd14_0_513 : subd14_0 [2, -2, 6] = true := by decide +kernel
theorem subd14_0_514 : subd14_0 [2, -1, -8] = true := by decide +kernel
theorem subd14_0_515 : subd14_0 [2, -1, -7] = true := by decide +kernel
theorem subd14_0_516 : subd14_0 [2, -1, -6] = true := by decide +kernel
theorem subd14_0_517 : subd14_0 [2, -1, -5] = true := by decide +kernel
theorem subd14_0_518 : subd14_0 [2, -1, -4] = true := by decide +kernel
theorem subd14_0_519 : subd14_0 [2, -1, -3] = true := by decide +kernel
theorem subd14_0_520 : subd14_0 [2, -1, -2] = true := by decide +kernel
theorem subd14_0_521 : subd14_0 [2, -1, -1] = true := by decide +kernel
theorem subd14_0_522 : subd14_0 [2, -1, 0] = true := by decide +kernel
theorem subd14_0_523 : subd14_0 [2, -1, 1] = true := by decide +kernel
theorem subd14_0_524 : subd14_0 [2, -1, 2] = true := by decide +kernel
theorem subd14_0_525 : subd14_0 [2, -1, 3] = true := by decide +kernel
theorem subd14_0_526 : subd14_0 [2, -1, 4] = true := by decide +kernel
theorem subd14_0_527 : subd14_0 [2, -1, 5] = true := by decide +kernel
theorem subd14_0_528 : subd14_0 [2, -1, 6] = true := by decide +kernel
theorem subd14_0_529 : subd14_0 [2, 0, -8] = true := by decide +kernel
theorem subd14_0_530 : subd14_0 [2, 0, -7] = true := by decide +kernel
theorem subd14_0_531 : subd14_0 [2, 0, -6] = true := by decide +kernel
theorem subd14_0_532 : subd14_0 [2, 0, -5] = true := by decide +kernel
theorem subd14_0_533 : subd14_0 [2, 0, -4] = true := by decide +kernel
theorem subd14_0_534 : subd14_0 [2, 0, -3] = true := by decide +kernel
theorem subd14_0_535 : subd14_0 [2, 0, -2] = true := by decide +kernel
theorem subd14_0_536 : subd14_0 [2, 0, -1] = true := by decide +kernel
theorem subd14_0_537 : subd14_0 [2, 0, 0] = true := by decide +kernel
theorem subd14_0_538 : subd14_0 [2, 0, 1] = true := by decide +kernel
theorem subd14_0_539 : subd14_0 [2, 0, 2] = true := by decide +kernel
theorem subd14_0_540 : subd14_0 [2, 0, 3] = true := by decide +kernel
theorem subd14_0_541 : subd14_0 [2, 0, 4] = true := by decide +kernel
theorem subd14_0_542 : subd14_0 [2, 0, 5] = true := by decide +kernel
theorem subd14_0_543 : subd14_0 [2, 0, 6] = true := by decide +kernel
theorem sbd14_0_16 : ∀ q ∈ blkd14_0_16, subd14_0 q = true := by
  unfold blkd14_0_16
  exact List.forall_mem_cons.2 ⟨subd14_0_512, List.forall_mem_cons.2 ⟨subd14_0_513, List.forall_mem_cons.2 ⟨subd14_0_514, List.forall_mem_cons.2 ⟨subd14_0_515, List.forall_mem_cons.2 ⟨subd14_0_516, List.forall_mem_cons.2 ⟨subd14_0_517, List.forall_mem_cons.2 ⟨subd14_0_518, List.forall_mem_cons.2 ⟨subd14_0_519, List.forall_mem_cons.2 ⟨subd14_0_520, List.forall_mem_cons.2 ⟨subd14_0_521, List.forall_mem_cons.2 ⟨subd14_0_522, List.forall_mem_cons.2 ⟨subd14_0_523, List.forall_mem_cons.2 ⟨subd14_0_524, List.forall_mem_cons.2 ⟨subd14_0_525, List.forall_mem_cons.2 ⟨subd14_0_526, List.forall_mem_cons.2 ⟨subd14_0_527, List.forall_mem_cons.2 ⟨subd14_0_528, List.forall_mem_cons.2 ⟨subd14_0_529, List.forall_mem_cons.2 ⟨subd14_0_530, List.forall_mem_cons.2 ⟨subd14_0_531, List.forall_mem_cons.2 ⟨subd14_0_532, List.forall_mem_cons.2 ⟨subd14_0_533, List.forall_mem_cons.2 ⟨subd14_0_534, List.forall_mem_cons.2 ⟨subd14_0_535, List.forall_mem_cons.2 ⟨subd14_0_536, List.forall_mem_cons.2 ⟨subd14_0_537, List.forall_mem_cons.2 ⟨subd14_0_538, List.forall_mem_cons.2 ⟨subd14_0_539, List.forall_mem_cons.2 ⟨subd14_0_540, List.forall_mem_cons.2 ⟨subd14_0_541, List.forall_mem_cons.2 ⟨subd14_0_542, List.forall_mem_cons.2 ⟨subd14_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_544 : subd14_0 [2, 1, -8] = true := by decide +kernel
theorem subd14_0_545 : subd14_0 [2, 1, -7] = true := by decide +kernel
theorem subd14_0_546 : subd14_0 [2, 1, -6] = true := by decide +kernel
theorem subd14_0_547 : subd14_0 [2, 1, -5] = true := by decide +kernel
theorem subd14_0_548 : subd14_0 [2, 1, -4] = true := by decide +kernel
theorem subd14_0_549 : subd14_0 [2, 1, -3] = true := by decide +kernel
theorem subd14_0_550 : subd14_0 [2, 1, -2] = true := by decide +kernel
theorem subd14_0_551 : subd14_0 [2, 1, -1] = true := by decide +kernel
theorem subd14_0_552 : subd14_0 [2, 1, 0] = true := by decide +kernel
theorem subd14_0_553 : subd14_0 [2, 1, 1] = true := by decide +kernel
theorem subd14_0_554 : subd14_0 [2, 1, 2] = true := by decide +kernel
theorem subd14_0_555 : subd14_0 [2, 1, 3] = true := by decide +kernel
theorem subd14_0_556 : subd14_0 [2, 1, 4] = true := by decide +kernel
theorem subd14_0_557 : subd14_0 [2, 1, 5] = true := by decide +kernel
theorem subd14_0_558 : subd14_0 [2, 1, 6] = true := by decide +kernel
theorem subd14_0_559 : subd14_0 [2, 2, -8] = true := by decide +kernel
theorem subd14_0_560 : subd14_0 [2, 2, -7] = true := by decide +kernel
theorem subd14_0_561 : subd14_0 [2, 2, -6] = true := by decide +kernel
theorem subd14_0_562 : subd14_0 [2, 2, -5] = true := by decide +kernel
theorem subd14_0_563 : subd14_0 [2, 2, -4] = true := by decide +kernel
theorem subd14_0_564 : subd14_0 [2, 2, -3] = true := by decide +kernel
theorem subd14_0_565 : subd14_0 [2, 2, -2] = true := by decide +kernel
theorem subd14_0_566 : subd14_0 [2, 2, -1] = true := by decide +kernel
theorem subd14_0_567 : subd14_0 [2, 2, 0] = true := by decide +kernel
theorem subd14_0_568 : subd14_0 [2, 2, 1] = true := by decide +kernel
theorem subd14_0_569 : subd14_0 [2, 2, 2] = true := by decide +kernel
theorem subd14_0_570 : subd14_0 [2, 2, 3] = true := by decide +kernel
theorem subd14_0_571 : subd14_0 [2, 2, 4] = true := by decide +kernel
theorem subd14_0_572 : subd14_0 [2, 2, 5] = true := by decide +kernel
theorem subd14_0_573 : subd14_0 [2, 3] = true := by decide +kernel
theorem subd14_0_574 : subd14_0 [2, 4] = true := by decide +kernel
theorem subd14_0_575 : subd14_0 [2, 5] = true := by decide +kernel
theorem sbd14_0_17 : ∀ q ∈ blkd14_0_17, subd14_0 q = true := by
  unfold blkd14_0_17
  exact List.forall_mem_cons.2 ⟨subd14_0_544, List.forall_mem_cons.2 ⟨subd14_0_545, List.forall_mem_cons.2 ⟨subd14_0_546, List.forall_mem_cons.2 ⟨subd14_0_547, List.forall_mem_cons.2 ⟨subd14_0_548, List.forall_mem_cons.2 ⟨subd14_0_549, List.forall_mem_cons.2 ⟨subd14_0_550, List.forall_mem_cons.2 ⟨subd14_0_551, List.forall_mem_cons.2 ⟨subd14_0_552, List.forall_mem_cons.2 ⟨subd14_0_553, List.forall_mem_cons.2 ⟨subd14_0_554, List.forall_mem_cons.2 ⟨subd14_0_555, List.forall_mem_cons.2 ⟨subd14_0_556, List.forall_mem_cons.2 ⟨subd14_0_557, List.forall_mem_cons.2 ⟨subd14_0_558, List.forall_mem_cons.2 ⟨subd14_0_559, List.forall_mem_cons.2 ⟨subd14_0_560, List.forall_mem_cons.2 ⟨subd14_0_561, List.forall_mem_cons.2 ⟨subd14_0_562, List.forall_mem_cons.2 ⟨subd14_0_563, List.forall_mem_cons.2 ⟨subd14_0_564, List.forall_mem_cons.2 ⟨subd14_0_565, List.forall_mem_cons.2 ⟨subd14_0_566, List.forall_mem_cons.2 ⟨subd14_0_567, List.forall_mem_cons.2 ⟨subd14_0_568, List.forall_mem_cons.2 ⟨subd14_0_569, List.forall_mem_cons.2 ⟨subd14_0_570, List.forall_mem_cons.2 ⟨subd14_0_571, List.forall_mem_cons.2 ⟨subd14_0_572, List.forall_mem_cons.2 ⟨subd14_0_573, List.forall_mem_cons.2 ⟨subd14_0_574, List.forall_mem_cons.2 ⟨subd14_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
