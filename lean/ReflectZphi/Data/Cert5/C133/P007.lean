import ReflectZphi.Data.Cert5.C133.Base

namespace ReflectZphi.Data.Cert5.C133

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_2_128 : subd6_2 [0, -1, 5] = true := by decide +kernel
theorem subd6_2_129 : subd6_2 [0, -1, 6] = true := by decide +kernel
theorem subd6_2_130 : subd6_2 [0, -1, 7] = true := by decide +kernel
theorem subd6_2_131 : subd6_2 [0, 0, -9] = true := by decide +kernel
theorem subd6_2_132 : subd6_2 [0, 0, -8] = true := by decide +kernel
theorem subd6_2_133 : subd6_2 [0, 0, -7] = true := by decide +kernel
theorem subd6_2_134 : subd6_2 [0, 0, -6] = true := by decide +kernel
theorem subd6_2_135 : subd6_2 [0, 0, -5] = true := by decide +kernel
theorem subd6_2_136 : subd6_2 [0, 0, -4] = true := by decide +kernel
theorem subd6_2_137 : subd6_2 [0, 0, -3] = true := by decide +kernel
theorem subd6_2_138 : subd6_2 [0, 0, -2] = true := by decide +kernel
theorem subd6_2_139 : subd6_2 [0, 0, -1] = true := by decide +kernel
theorem subd6_2_140 : subd6_2 [0, 0, 0] = true := by decide +kernel
theorem subd6_2_141 : subd6_2 [0, 0, 1] = true := by decide +kernel
theorem subd6_2_142 : subd6_2 [0, 0, 2] = true := by decide +kernel
theorem subd6_2_143 : subd6_2 [0, 0, 3] = true := by decide +kernel
theorem subd6_2_144 : subd6_2 [0, 0, 4] = true := by decide +kernel
theorem subd6_2_145 : subd6_2 [0, 0, 5] = true := by decide +kernel
theorem subd6_2_146 : subd6_2 [0, 0, 6] = true := by decide +kernel
theorem subd6_2_147 : subd6_2 [0, 0, 7] = true := by decide +kernel
theorem subd6_2_148 : subd6_2 [0, 0, 8] = true := by decide +kernel
theorem subd6_2_149 : subd6_2 [0, 1, -8] = true := by decide +kernel
theorem subd6_2_150 : subd6_2 [0, 1, -7] = true := by decide +kernel
theorem subd6_2_151 : subd6_2 [0, 1, -6] = true := by decide +kernel
theorem subd6_2_152 : subd6_2 [0, 1, -5] = true := by decide +kernel
theorem subd6_2_153 : subd6_2 [0, 1, -4] = true := by decide +kernel
theorem subd6_2_154 : subd6_2 [0, 1, -3] = true := by decide +kernel
theorem subd6_2_155 : subd6_2 [0, 1, -2] = true := by decide +kernel
theorem subd6_2_156 : subd6_2 [0, 1, -1] = true := by decide +kernel
theorem subd6_2_157 : subd6_2 [0, 1, 0] = true := by decide +kernel
theorem subd6_2_158 : subd6_2 [0, 1, 1] = true := by decide +kernel
theorem subd6_2_159 : subd6_2 [0, 1, 2] = true := by decide +kernel
theorem sbd6_2_4 : ∀ q ∈ blkd6_2_4, subd6_2 q = true := by
  unfold blkd6_2_4
  exact List.forall_mem_cons.2 ⟨subd6_2_128, List.forall_mem_cons.2 ⟨subd6_2_129, List.forall_mem_cons.2 ⟨subd6_2_130, List.forall_mem_cons.2 ⟨subd6_2_131, List.forall_mem_cons.2 ⟨subd6_2_132, List.forall_mem_cons.2 ⟨subd6_2_133, List.forall_mem_cons.2 ⟨subd6_2_134, List.forall_mem_cons.2 ⟨subd6_2_135, List.forall_mem_cons.2 ⟨subd6_2_136, List.forall_mem_cons.2 ⟨subd6_2_137, List.forall_mem_cons.2 ⟨subd6_2_138, List.forall_mem_cons.2 ⟨subd6_2_139, List.forall_mem_cons.2 ⟨subd6_2_140, List.forall_mem_cons.2 ⟨subd6_2_141, List.forall_mem_cons.2 ⟨subd6_2_142, List.forall_mem_cons.2 ⟨subd6_2_143, List.forall_mem_cons.2 ⟨subd6_2_144, List.forall_mem_cons.2 ⟨subd6_2_145, List.forall_mem_cons.2 ⟨subd6_2_146, List.forall_mem_cons.2 ⟨subd6_2_147, List.forall_mem_cons.2 ⟨subd6_2_148, List.forall_mem_cons.2 ⟨subd6_2_149, List.forall_mem_cons.2 ⟨subd6_2_150, List.forall_mem_cons.2 ⟨subd6_2_151, List.forall_mem_cons.2 ⟨subd6_2_152, List.forall_mem_cons.2 ⟨subd6_2_153, List.forall_mem_cons.2 ⟨subd6_2_154, List.forall_mem_cons.2 ⟨subd6_2_155, List.forall_mem_cons.2 ⟨subd6_2_156, List.forall_mem_cons.2 ⟨subd6_2_157, List.forall_mem_cons.2 ⟨subd6_2_158, List.forall_mem_cons.2 ⟨subd6_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_160 : subd6_2 [0, 1, 3] = true := by decide +kernel
theorem subd6_2_161 : subd6_2 [0, 1, 4] = true := by decide +kernel
theorem subd6_2_162 : subd6_2 [0, 1, 5] = true := by decide +kernel
theorem subd6_2_163 : subd6_2 [0, 1, 6] = true := by decide +kernel
theorem subd6_2_164 : subd6_2 [0, 1, 7] = true := by decide +kernel
theorem subd6_2_165 : subd6_2 [0, 2, -8] = true := by decide +kernel
theorem subd6_2_166 : subd6_2 [0, 2, -7] = true := by decide +kernel
theorem subd6_2_167 : subd6_2 [0, 2, -6] = true := by decide +kernel
theorem subd6_2_168 : subd6_2 [0, 2, -5] = true := by decide +kernel
theorem subd6_2_169 : subd6_2 [0, 2, -4] = true := by decide +kernel
theorem subd6_2_170 : subd6_2 [0, 2, -3] = true := by decide +kernel
theorem subd6_2_171 : subd6_2 [0, 2, -2] = true := by decide +kernel
theorem subd6_2_172 : subd6_2 [0, 2, -1] = true := by decide +kernel
theorem subd6_2_173 : subd6_2 [0, 2, 0] = true := by decide +kernel
theorem subd6_2_174 : subd6_2 [0, 2, 1] = true := by decide +kernel
theorem subd6_2_175 : subd6_2 [0, 2, 2] = true := by decide +kernel
theorem subd6_2_176 : subd6_2 [0, 2, 3] = true := by decide +kernel
theorem subd6_2_177 : subd6_2 [0, 2, 4] = true := by decide +kernel
theorem subd6_2_178 : subd6_2 [0, 2, 5] = true := by decide +kernel
theorem subd6_2_179 : subd6_2 [0, 2, 6] = true := by decide +kernel
theorem subd6_2_180 : subd6_2 [0, 3] = true := by decide +kernel
theorem subd6_2_181 : subd6_2 [0, 4] = true := by decide +kernel
theorem subd6_2_182 : subd6_2 [1, -4] = true := by decide +kernel
theorem subd6_2_183 : subd6_2 [1, -3] = true := by decide +kernel
theorem subd6_2_184 : subd6_2 [1, -2] = true := by decide +kernel
theorem subd6_2_185 : subd6_2 [1, -1, -7] = true := by decide +kernel
theorem subd6_2_186 : subd6_2 [1, -1, -6] = true := by decide +kernel
theorem subd6_2_187 : subd6_2 [1, -1, -5] = true := by decide +kernel
theorem subd6_2_188 : subd6_2 [1, -1, -4] = true := by decide +kernel
theorem subd6_2_189 : subd6_2 [1, -1, -3] = true := by decide +kernel
theorem subd6_2_190 : subd6_2 [1, -1, -2] = true := by decide +kernel
theorem subd6_2_191 : subd6_2 [1, -1, -1] = true := by decide +kernel
theorem sbd6_2_5 : ∀ q ∈ blkd6_2_5, subd6_2 q = true := by
  unfold blkd6_2_5
  exact List.forall_mem_cons.2 ⟨subd6_2_160, List.forall_mem_cons.2 ⟨subd6_2_161, List.forall_mem_cons.2 ⟨subd6_2_162, List.forall_mem_cons.2 ⟨subd6_2_163, List.forall_mem_cons.2 ⟨subd6_2_164, List.forall_mem_cons.2 ⟨subd6_2_165, List.forall_mem_cons.2 ⟨subd6_2_166, List.forall_mem_cons.2 ⟨subd6_2_167, List.forall_mem_cons.2 ⟨subd6_2_168, List.forall_mem_cons.2 ⟨subd6_2_169, List.forall_mem_cons.2 ⟨subd6_2_170, List.forall_mem_cons.2 ⟨subd6_2_171, List.forall_mem_cons.2 ⟨subd6_2_172, List.forall_mem_cons.2 ⟨subd6_2_173, List.forall_mem_cons.2 ⟨subd6_2_174, List.forall_mem_cons.2 ⟨subd6_2_175, List.forall_mem_cons.2 ⟨subd6_2_176, List.forall_mem_cons.2 ⟨subd6_2_177, List.forall_mem_cons.2 ⟨subd6_2_178, List.forall_mem_cons.2 ⟨subd6_2_179, List.forall_mem_cons.2 ⟨subd6_2_180, List.forall_mem_cons.2 ⟨subd6_2_181, List.forall_mem_cons.2 ⟨subd6_2_182, List.forall_mem_cons.2 ⟨subd6_2_183, List.forall_mem_cons.2 ⟨subd6_2_184, List.forall_mem_cons.2 ⟨subd6_2_185, List.forall_mem_cons.2 ⟨subd6_2_186, List.forall_mem_cons.2 ⟨subd6_2_187, List.forall_mem_cons.2 ⟨subd6_2_188, List.forall_mem_cons.2 ⟨subd6_2_189, List.forall_mem_cons.2 ⟨subd6_2_190, List.forall_mem_cons.2 ⟨subd6_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_192 : subd6_2 [1, -1, 0] = true := by decide +kernel
theorem subd6_2_193 : subd6_2 [1, -1, 1] = true := by decide +kernel
theorem subd6_2_194 : subd6_2 [1, -1, 2] = true := by decide +kernel
theorem subd6_2_195 : subd6_2 [1, -1, 3] = true := by decide +kernel
theorem subd6_2_196 : subd6_2 [1, -1, 4] = true := by decide +kernel
theorem subd6_2_197 : subd6_2 [1, -1, 5] = true := by decide +kernel
theorem subd6_2_198 : subd6_2 [1, -1, 6] = true := by decide +kernel
theorem subd6_2_199 : subd6_2 [1, -1, 7] = true := by decide +kernel
theorem subd6_2_200 : subd6_2 [1, 0, -8] = true := by decide +kernel
theorem subd6_2_201 : subd6_2 [1, 0, -7] = true := by decide +kernel
theorem subd6_2_202 : subd6_2 [1, 0, -6] = true := by decide +kernel
theorem subd6_2_203 : subd6_2 [1, 0, -5] = true := by decide +kernel
theorem subd6_2_204 : subd6_2 [1, 0, -4] = true := by decide +kernel
theorem subd6_2_205 : subd6_2 [1, 0, -3] = true := by decide +kernel
theorem subd6_2_206 : subd6_2 [1, 0, -2] = true := by decide +kernel
theorem subd6_2_207 : subd6_2 [1, 0, -1] = true := by decide +kernel
theorem subd6_2_208 : subd6_2 [1, 0, 0] = true := by decide +kernel
theorem subd6_2_209 : subd6_2 [1, 0, 1] = true := by decide +kernel
theorem subd6_2_210 : subd6_2 [1, 0, 2] = true := by decide +kernel
theorem subd6_2_211 : subd6_2 [1, 0, 3] = true := by decide +kernel
theorem subd6_2_212 : subd6_2 [1, 0, 4] = true := by decide +kernel
theorem subd6_2_213 : subd6_2 [1, 0, 5] = true := by decide +kernel
theorem subd6_2_214 : subd6_2 [1, 0, 6] = true := by decide +kernel
theorem subd6_2_215 : subd6_2 [1, 0, 7] = true := by decide +kernel
theorem subd6_2_216 : subd6_2 [1, 0, 8] = true := by decide +kernel
theorem subd6_2_217 : subd6_2 [1, 1, -8] = true := by decide +kernel
theorem subd6_2_218 : subd6_2 [1, 1, -7] = true := by decide +kernel
theorem subd6_2_219 : subd6_2 [1, 1, -6] = true := by decide +kernel
theorem subd6_2_220 : subd6_2 [1, 1, -5] = true := by decide +kernel
theorem subd6_2_221 : subd6_2 [1, 1, -4] = true := by decide +kernel
theorem subd6_2_222 : subd6_2 [1, 1, -3] = true := by decide +kernel
theorem subd6_2_223 : subd6_2 [1, 1, -2] = true := by decide +kernel
theorem sbd6_2_6 : ∀ q ∈ blkd6_2_6, subd6_2 q = true := by
  unfold blkd6_2_6
  exact List.forall_mem_cons.2 ⟨subd6_2_192, List.forall_mem_cons.2 ⟨subd6_2_193, List.forall_mem_cons.2 ⟨subd6_2_194, List.forall_mem_cons.2 ⟨subd6_2_195, List.forall_mem_cons.2 ⟨subd6_2_196, List.forall_mem_cons.2 ⟨subd6_2_197, List.forall_mem_cons.2 ⟨subd6_2_198, List.forall_mem_cons.2 ⟨subd6_2_199, List.forall_mem_cons.2 ⟨subd6_2_200, List.forall_mem_cons.2 ⟨subd6_2_201, List.forall_mem_cons.2 ⟨subd6_2_202, List.forall_mem_cons.2 ⟨subd6_2_203, List.forall_mem_cons.2 ⟨subd6_2_204, List.forall_mem_cons.2 ⟨subd6_2_205, List.forall_mem_cons.2 ⟨subd6_2_206, List.forall_mem_cons.2 ⟨subd6_2_207, List.forall_mem_cons.2 ⟨subd6_2_208, List.forall_mem_cons.2 ⟨subd6_2_209, List.forall_mem_cons.2 ⟨subd6_2_210, List.forall_mem_cons.2 ⟨subd6_2_211, List.forall_mem_cons.2 ⟨subd6_2_212, List.forall_mem_cons.2 ⟨subd6_2_213, List.forall_mem_cons.2 ⟨subd6_2_214, List.forall_mem_cons.2 ⟨subd6_2_215, List.forall_mem_cons.2 ⟨subd6_2_216, List.forall_mem_cons.2 ⟨subd6_2_217, List.forall_mem_cons.2 ⟨subd6_2_218, List.forall_mem_cons.2 ⟨subd6_2_219, List.forall_mem_cons.2 ⟨subd6_2_220, List.forall_mem_cons.2 ⟨subd6_2_221, List.forall_mem_cons.2 ⟨subd6_2_222, List.forall_mem_cons.2 ⟨subd6_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_224 : subd6_2 [1, 1, -1] = true := by decide +kernel
theorem subd6_2_225 : subd6_2 [1, 1, 0] = true := by decide +kernel
theorem subd6_2_226 : subd6_2 [1, 1, 1] = true := by decide +kernel
theorem subd6_2_227 : subd6_2 [1, 1, 2] = true := by decide +kernel
theorem subd6_2_228 : subd6_2 [1, 1, 3] = true := by decide +kernel
theorem subd6_2_229 : subd6_2 [1, 1, 4] = true := by decide +kernel
theorem subd6_2_230 : subd6_2 [1, 1, 5] = true := by decide +kernel
theorem subd6_2_231 : subd6_2 [1, 1, 6] = true := by decide +kernel
theorem subd6_2_232 : subd6_2 [1, 1, 7] = true := by decide +kernel
theorem subd6_2_233 : subd6_2 [1, 1, 8] = true := by decide +kernel
theorem subd6_2_234 : subd6_2 [1, 2, -8] = true := by decide +kernel
theorem subd6_2_235 : subd6_2 [1, 2, -7] = true := by decide +kernel
theorem subd6_2_236 : subd6_2 [1, 2, -6] = true := by decide +kernel
theorem subd6_2_237 : subd6_2 [1, 2, -5] = true := by decide +kernel
theorem subd6_2_238 : subd6_2 [1, 2, -4] = true := by decide +kernel
theorem subd6_2_239 : subd6_2 [1, 2, -3] = true := by decide +kernel
theorem subd6_2_240 : subd6_2 [1, 2, -2] = true := by decide +kernel
theorem subd6_2_241 : subd6_2 [1, 2, -1] = true := by decide +kernel
theorem subd6_2_242 : subd6_2 [1, 2, 0] = true := by decide +kernel
theorem subd6_2_243 : subd6_2 [1, 2, 1] = true := by decide +kernel
theorem subd6_2_244 : subd6_2 [1, 2, 2] = true := by decide +kernel
theorem subd6_2_245 : subd6_2 [1, 2, 3] = true := by decide +kernel
theorem subd6_2_246 : subd6_2 [1, 2, 4] = true := by decide +kernel
theorem subd6_2_247 : subd6_2 [1, 2, 5] = true := by decide +kernel
theorem subd6_2_248 : subd6_2 [1, 2, 6] = true := by decide +kernel
theorem subd6_2_249 : subd6_2 [1, 2, 7] = true := by decide +kernel
theorem subd6_2_250 : subd6_2 [1, 3] = true := by decide +kernel
theorem subd6_2_251 : subd6_2 [1, 4] = true := by decide +kernel
theorem subd6_2_252 : subd6_2 [2, -3] = true := by decide +kernel
theorem subd6_2_253 : subd6_2 [2, -2] = true := by decide +kernel
theorem subd6_2_254 : subd6_2 [2, -1] = true := by decide +kernel
theorem subd6_2_255 : subd6_2 [2, 0] = true := by decide +kernel
theorem sbd6_2_7 : ∀ q ∈ blkd6_2_7, subd6_2 q = true := by
  unfold blkd6_2_7
  exact List.forall_mem_cons.2 ⟨subd6_2_224, List.forall_mem_cons.2 ⟨subd6_2_225, List.forall_mem_cons.2 ⟨subd6_2_226, List.forall_mem_cons.2 ⟨subd6_2_227, List.forall_mem_cons.2 ⟨subd6_2_228, List.forall_mem_cons.2 ⟨subd6_2_229, List.forall_mem_cons.2 ⟨subd6_2_230, List.forall_mem_cons.2 ⟨subd6_2_231, List.forall_mem_cons.2 ⟨subd6_2_232, List.forall_mem_cons.2 ⟨subd6_2_233, List.forall_mem_cons.2 ⟨subd6_2_234, List.forall_mem_cons.2 ⟨subd6_2_235, List.forall_mem_cons.2 ⟨subd6_2_236, List.forall_mem_cons.2 ⟨subd6_2_237, List.forall_mem_cons.2 ⟨subd6_2_238, List.forall_mem_cons.2 ⟨subd6_2_239, List.forall_mem_cons.2 ⟨subd6_2_240, List.forall_mem_cons.2 ⟨subd6_2_241, List.forall_mem_cons.2 ⟨subd6_2_242, List.forall_mem_cons.2 ⟨subd6_2_243, List.forall_mem_cons.2 ⟨subd6_2_244, List.forall_mem_cons.2 ⟨subd6_2_245, List.forall_mem_cons.2 ⟨subd6_2_246, List.forall_mem_cons.2 ⟨subd6_2_247, List.forall_mem_cons.2 ⟨subd6_2_248, List.forall_mem_cons.2 ⟨subd6_2_249, List.forall_mem_cons.2 ⟨subd6_2_250, List.forall_mem_cons.2 ⟨subd6_2_251, List.forall_mem_cons.2 ⟨subd6_2_252, List.forall_mem_cons.2 ⟨subd6_2_253, List.forall_mem_cons.2 ⟨subd6_2_254, List.forall_mem_cons.2 ⟨subd6_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_256 : subd6_2 [2, 1, -7] = true := by decide +kernel
theorem subd6_2_257 : subd6_2 [2, 1, -6] = true := by decide +kernel
theorem subd6_2_258 : subd6_2 [2, 1, -5] = true := by decide +kernel
theorem subd6_2_259 : subd6_2 [2, 1, -4] = true := by decide +kernel
theorem subd6_2_260 : subd6_2 [2, 1, -3] = true := by decide +kernel
theorem subd6_2_261 : subd6_2 [2, 1, -2] = true := by decide +kernel
theorem subd6_2_262 : subd6_2 [2, 1, -1] = true := by decide +kernel
theorem subd6_2_263 : subd6_2 [2, 1, 0] = true := by decide +kernel
theorem subd6_2_264 : subd6_2 [2, 1, 1] = true := by decide +kernel
theorem subd6_2_265 : subd6_2 [2, 1, 2] = true := by decide +kernel
theorem subd6_2_266 : subd6_2 [2, 1, 3] = true := by decide +kernel
theorem subd6_2_267 : subd6_2 [2, 1, 4] = true := by decide +kernel
theorem subd6_2_268 : subd6_2 [2, 1, 5] = true := by decide +kernel
theorem subd6_2_269 : subd6_2 [2, 1, 6] = true := by decide +kernel
theorem subd6_2_270 : subd6_2 [2, 1, 7] = true := by decide +kernel
theorem subd6_2_271 : subd6_2 [2, 2] = true := by decide +kernel
theorem subd6_2_272 : subd6_2 [2, 3] = true := by decide +kernel
theorem subd6_2_273 : subd6_2 [2, 4] = true := by decide +kernel
theorem subd6_2_274 : subd6_2 [3, -1] = true := by decide +kernel
theorem subd6_2_275 : subd6_2 [3, 0] = true := by decide +kernel
theorem subd6_2_276 : subd6_2 [3, 1] = true := by decide +kernel
theorem subd6_2_277 : subd6_2 [3, 2] = true := by decide +kernel
theorem subd6_2_278 : subd6_2 [3, 3] = true := by decide +kernel
theorem sbd6_2_8 : ∀ q ∈ blkd6_2_8, subd6_2 q = true := by
  unfold blkd6_2_8
  exact List.forall_mem_cons.2 ⟨subd6_2_256, List.forall_mem_cons.2 ⟨subd6_2_257, List.forall_mem_cons.2 ⟨subd6_2_258, List.forall_mem_cons.2 ⟨subd6_2_259, List.forall_mem_cons.2 ⟨subd6_2_260, List.forall_mem_cons.2 ⟨subd6_2_261, List.forall_mem_cons.2 ⟨subd6_2_262, List.forall_mem_cons.2 ⟨subd6_2_263, List.forall_mem_cons.2 ⟨subd6_2_264, List.forall_mem_cons.2 ⟨subd6_2_265, List.forall_mem_cons.2 ⟨subd6_2_266, List.forall_mem_cons.2 ⟨subd6_2_267, List.forall_mem_cons.2 ⟨subd6_2_268, List.forall_mem_cons.2 ⟨subd6_2_269, List.forall_mem_cons.2 ⟨subd6_2_270, List.forall_mem_cons.2 ⟨subd6_2_271, List.forall_mem_cons.2 ⟨subd6_2_272, List.forall_mem_cons.2 ⟨subd6_2_273, List.forall_mem_cons.2 ⟨subd6_2_274, List.forall_mem_cons.2 ⟨subd6_2_275, List.forall_mem_cons.2 ⟨subd6_2_276, List.forall_mem_cons.2 ⟨subd6_2_277, List.forall_mem_cons.2 ⟨subd6_2_278, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [-2, -3] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-2, -2] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [-2, -1] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [-2, 0] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [-1, -3] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [-1, -2, -8] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [-1, -2, -7] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [-1, -2, -6] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [-1, -2, -5] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [-1, -2, -4] = true := by decide +kernel
theorem subd6_3_10 : subd6_3 [-1, -2, -3] = true := by decide +kernel
theorem subd6_3_11 : subd6_3 [-1, -2, -2] = true := by decide +kernel
theorem subd6_3_12 : subd6_3 [-1, -2, -1] = true := by decide +kernel
theorem subd6_3_13 : subd6_3 [-1, -2, 0] = true := by decide +kernel
theorem subd6_3_14 : subd6_3 [-1, -2, 1] = true := by decide +kernel
theorem subd6_3_15 : subd6_3 [-1, -2, 2] = true := by decide +kernel
theorem subd6_3_16 : subd6_3 [-1, -2, 3] = true := by decide +kernel
theorem subd6_3_17 : subd6_3 [-1, -2, 4] = true := by decide +kernel
theorem subd6_3_18 : subd6_3 [-1, -2, 5] = true := by decide +kernel
theorem subd6_3_19 : subd6_3 [-1, -2, 6] = true := by decide +kernel
theorem subd6_3_20 : subd6_3 [-1, -2, 7] = true := by decide +kernel
theorem subd6_3_21 : subd6_3 [-1, -2, 8] = true := by decide +kernel
theorem subd6_3_22 : subd6_3 [-1, -1, -10] = true := by decide +kernel
theorem subd6_3_23 : subd6_3 [-1, -1, -9] = true := by decide +kernel
theorem subd6_3_24 : subd6_3 [-1, -1, -8] = true := by decide +kernel
theorem subd6_3_25 : subd6_3 [-1, -1, -7] = true := by decide +kernel
theorem subd6_3_26 : subd6_3 [-1, -1, -6] = true := by decide +kernel
theorem subd6_3_27 : subd6_3 [-1, -1, -5] = true := by decide +kernel
theorem subd6_3_28 : subd6_3 [-1, -1, -4] = true := by decide +kernel
theorem subd6_3_29 : subd6_3 [-1, -1, -3] = true := by decide +kernel
theorem subd6_3_30 : subd6_3 [-1, -1, -2] = true := by decide +kernel
theorem subd6_3_31 : subd6_3 [-1, -1, -1] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_cons.2 ⟨subd6_3_10, List.forall_mem_cons.2 ⟨subd6_3_11, List.forall_mem_cons.2 ⟨subd6_3_12, List.forall_mem_cons.2 ⟨subd6_3_13, List.forall_mem_cons.2 ⟨subd6_3_14, List.forall_mem_cons.2 ⟨subd6_3_15, List.forall_mem_cons.2 ⟨subd6_3_16, List.forall_mem_cons.2 ⟨subd6_3_17, List.forall_mem_cons.2 ⟨subd6_3_18, List.forall_mem_cons.2 ⟨subd6_3_19, List.forall_mem_cons.2 ⟨subd6_3_20, List.forall_mem_cons.2 ⟨subd6_3_21, List.forall_mem_cons.2 ⟨subd6_3_22, List.forall_mem_cons.2 ⟨subd6_3_23, List.forall_mem_cons.2 ⟨subd6_3_24, List.forall_mem_cons.2 ⟨subd6_3_25, List.forall_mem_cons.2 ⟨subd6_3_26, List.forall_mem_cons.2 ⟨subd6_3_27, List.forall_mem_cons.2 ⟨subd6_3_28, List.forall_mem_cons.2 ⟨subd6_3_29, List.forall_mem_cons.2 ⟨subd6_3_30, List.forall_mem_cons.2 ⟨subd6_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_32 : subd6_3 [-1, -1, 0] = true := by decide +kernel
theorem subd6_3_33 : subd6_3 [-1, -1, 1] = true := by decide +kernel
theorem subd6_3_34 : subd6_3 [-1, -1, 2] = true := by decide +kernel
theorem subd6_3_35 : subd6_3 [-1, -1, 3] = true := by decide +kernel
theorem subd6_3_36 : subd6_3 [-1, -1, 4] = true := by decide +kernel
theorem subd6_3_37 : subd6_3 [-1, -1, 5] = true := by decide +kernel
theorem subd6_3_38 : subd6_3 [-1, -1, 6] = true := by decide +kernel
theorem subd6_3_39 : subd6_3 [-1, -1, 7] = true := by decide +kernel
theorem subd6_3_40 : subd6_3 [-1, -1, 8] = true := by decide +kernel
theorem subd6_3_41 : subd6_3 [-1, -1, 9] = true := by decide +kernel
theorem subd6_3_42 : subd6_3 [-1, 0, -10] = true := by decide +kernel
theorem subd6_3_43 : subd6_3 [-1, 0, -9] = true := by decide +kernel
theorem subd6_3_44 : subd6_3 [-1, 0, -8] = true := by decide +kernel
theorem subd6_3_45 : subd6_3 [-1, 0, -7] = true := by decide +kernel
theorem subd6_3_46 : subd6_3 [-1, 0, -6] = true := by decide +kernel
theorem subd6_3_47 : subd6_3 [-1, 0, -5] = true := by decide +kernel
theorem subd6_3_48 : subd6_3 [-1, 0, -4] = true := by decide +kernel
theorem subd6_3_49 : subd6_3 [-1, 0, -3] = true := by decide +kernel
theorem subd6_3_50 : subd6_3 [-1, 0, -2] = true := by decide +kernel
theorem subd6_3_51 : subd6_3 [-1, 0, -1] = true := by decide +kernel
theorem subd6_3_52 : subd6_3 [-1, 0, 0] = true := by decide +kernel
theorem subd6_3_53 : subd6_3 [-1, 0, 1] = true := by decide +kernel
theorem subd6_3_54 : subd6_3 [-1, 0, 2] = true := by decide +kernel
theorem subd6_3_55 : subd6_3 [-1, 0, 3] = true := by decide +kernel
theorem subd6_3_56 : subd6_3 [-1, 0, 4] = true := by decide +kernel
theorem subd6_3_57 : subd6_3 [-1, 0, 5] = true := by decide +kernel
theorem subd6_3_58 : subd6_3 [-1, 0, 6] = true := by decide +kernel
theorem subd6_3_59 : subd6_3 [-1, 0, 7] = true := by decide +kernel
theorem subd6_3_60 : subd6_3 [-1, 0, 8] = true := by decide +kernel
theorem subd6_3_61 : subd6_3 [-1, 0, 9] = true := by decide +kernel
theorem subd6_3_62 : subd6_3 [-1, 1, -8] = true := by decide +kernel
theorem subd6_3_63 : subd6_3 [-1, 1, -7] = true := by decide +kernel
theorem sbd6_3_1 : ∀ q ∈ blkd6_3_1, subd6_3 q = true := by
  unfold blkd6_3_1
  exact List.forall_mem_cons.2 ⟨subd6_3_32, List.forall_mem_cons.2 ⟨subd6_3_33, List.forall_mem_cons.2 ⟨subd6_3_34, List.forall_mem_cons.2 ⟨subd6_3_35, List.forall_mem_cons.2 ⟨subd6_3_36, List.forall_mem_cons.2 ⟨subd6_3_37, List.forall_mem_cons.2 ⟨subd6_3_38, List.forall_mem_cons.2 ⟨subd6_3_39, List.forall_mem_cons.2 ⟨subd6_3_40, List.forall_mem_cons.2 ⟨subd6_3_41, List.forall_mem_cons.2 ⟨subd6_3_42, List.forall_mem_cons.2 ⟨subd6_3_43, List.forall_mem_cons.2 ⟨subd6_3_44, List.forall_mem_cons.2 ⟨subd6_3_45, List.forall_mem_cons.2 ⟨subd6_3_46, List.forall_mem_cons.2 ⟨subd6_3_47, List.forall_mem_cons.2 ⟨subd6_3_48, List.forall_mem_cons.2 ⟨subd6_3_49, List.forall_mem_cons.2 ⟨subd6_3_50, List.forall_mem_cons.2 ⟨subd6_3_51, List.forall_mem_cons.2 ⟨subd6_3_52, List.forall_mem_cons.2 ⟨subd6_3_53, List.forall_mem_cons.2 ⟨subd6_3_54, List.forall_mem_cons.2 ⟨subd6_3_55, List.forall_mem_cons.2 ⟨subd6_3_56, List.forall_mem_cons.2 ⟨subd6_3_57, List.forall_mem_cons.2 ⟨subd6_3_58, List.forall_mem_cons.2 ⟨subd6_3_59, List.forall_mem_cons.2 ⟨subd6_3_60, List.forall_mem_cons.2 ⟨subd6_3_61, List.forall_mem_cons.2 ⟨subd6_3_62, List.forall_mem_cons.2 ⟨subd6_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_64 : subd6_3 [-1, 1, -6] = true := by decide +kernel
theorem subd6_3_65 : subd6_3 [-1, 1, -5] = true := by decide +kernel
theorem subd6_3_66 : subd6_3 [-1, 1, -4] = true := by decide +kernel
theorem subd6_3_67 : subd6_3 [-1, 1, -3] = true := by decide +kernel
theorem subd6_3_68 : subd6_3 [-1, 1, -2] = true := by decide +kernel
theorem subd6_3_69 : subd6_3 [-1, 1, -1] = true := by decide +kernel
theorem subd6_3_70 : subd6_3 [-1, 1, 0] = true := by decide +kernel
theorem subd6_3_71 : subd6_3 [-1, 1, 1] = true := by decide +kernel
theorem subd6_3_72 : subd6_3 [-1, 1, 2] = true := by decide +kernel
theorem subd6_3_73 : subd6_3 [-1, 1, 3] = true := by decide +kernel
theorem subd6_3_74 : subd6_3 [-1, 1, 4] = true := by decide +kernel
theorem subd6_3_75 : subd6_3 [-1, 1, 5] = true := by decide +kernel
theorem subd6_3_76 : subd6_3 [-1, 1, 6] = true := by decide +kernel
theorem subd6_3_77 : subd6_3 [-1, 1, 7] = true := by decide +kernel
theorem subd6_3_78 : subd6_3 [-1, 1, 8] = true := by decide +kernel
theorem subd6_3_79 : subd6_3 [0, -3] = true := by decide +kernel
theorem subd6_3_80 : subd6_3 [0, -2, -8] = true := by decide +kernel
theorem subd6_3_81 : subd6_3 [0, -2, -7] = true := by decide +kernel
theorem subd6_3_82 : subd6_3 [0, -2, -6] = true := by decide +kernel
theorem subd6_3_83 : subd6_3 [0, -2, -5] = true := by decide +kernel
theorem subd6_3_84 : subd6_3 [0, -2, -4] = true := by decide +kernel
theorem subd6_3_85 : subd6_3 [0, -2, -3] = true := by decide +kernel
theorem subd6_3_86 : subd6_3 [0, -2, -2] = true := by decide +kernel
theorem subd6_3_87 : subd6_3 [0, -2, -1] = true := by decide +kernel
theorem subd6_3_88 : subd6_3 [0, -2, 0] = true := by decide +kernel
theorem subd6_3_89 : subd6_3 [0, -2, 1] = true := by decide +kernel
theorem subd6_3_90 : subd6_3 [0, -2, 2] = true := by decide +kernel
theorem subd6_3_91 : subd6_3 [0, -2, 3] = true := by decide +kernel
theorem subd6_3_92 : subd6_3 [0, -2, 4] = true := by decide +kernel
theorem subd6_3_93 : subd6_3 [0, -2, 5] = true := by decide +kernel
theorem subd6_3_94 : subd6_3 [0, -2, 6] = true := by decide +kernel
theorem subd6_3_95 : subd6_3 [0, -2, 7] = true := by decide +kernel
theorem sbd6_3_2 : ∀ q ∈ blkd6_3_2, subd6_3 q = true := by
  unfold blkd6_3_2
  exact List.forall_mem_cons.2 ⟨subd6_3_64, List.forall_mem_cons.2 ⟨subd6_3_65, List.forall_mem_cons.2 ⟨subd6_3_66, List.forall_mem_cons.2 ⟨subd6_3_67, List.forall_mem_cons.2 ⟨subd6_3_68, List.forall_mem_cons.2 ⟨subd6_3_69, List.forall_mem_cons.2 ⟨subd6_3_70, List.forall_mem_cons.2 ⟨subd6_3_71, List.forall_mem_cons.2 ⟨subd6_3_72, List.forall_mem_cons.2 ⟨subd6_3_73, List.forall_mem_cons.2 ⟨subd6_3_74, List.forall_mem_cons.2 ⟨subd6_3_75, List.forall_mem_cons.2 ⟨subd6_3_76, List.forall_mem_cons.2 ⟨subd6_3_77, List.forall_mem_cons.2 ⟨subd6_3_78, List.forall_mem_cons.2 ⟨subd6_3_79, List.forall_mem_cons.2 ⟨subd6_3_80, List.forall_mem_cons.2 ⟨subd6_3_81, List.forall_mem_cons.2 ⟨subd6_3_82, List.forall_mem_cons.2 ⟨subd6_3_83, List.forall_mem_cons.2 ⟨subd6_3_84, List.forall_mem_cons.2 ⟨subd6_3_85, List.forall_mem_cons.2 ⟨subd6_3_86, List.forall_mem_cons.2 ⟨subd6_3_87, List.forall_mem_cons.2 ⟨subd6_3_88, List.forall_mem_cons.2 ⟨subd6_3_89, List.forall_mem_cons.2 ⟨subd6_3_90, List.forall_mem_cons.2 ⟨subd6_3_91, List.forall_mem_cons.2 ⟨subd6_3_92, List.forall_mem_cons.2 ⟨subd6_3_93, List.forall_mem_cons.2 ⟨subd6_3_94, List.forall_mem_cons.2 ⟨subd6_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_96 : subd6_3 [0, -1, -11] = true := by decide +kernel
theorem subd6_3_97 : subd6_3 [0, -1, -10] = true := by decide +kernel
theorem subd6_3_98 : subd6_3 [0, -1, -9] = true := by decide +kernel
theorem subd6_3_99 : subd6_3 [0, -1, -8] = true := by decide +kernel
theorem subd6_3_100 : subd6_3 [0, -1, -7] = true := by decide +kernel
theorem subd6_3_101 : subd6_3 [0, -1, -6] = true := by decide +kernel
theorem subd6_3_102 : subd6_3 [0, -1, -5] = true := by decide +kernel
theorem subd6_3_103 : subd6_3 [0, -1, -4] = true := by decide +kernel
theorem subd6_3_104 : subd6_3 [0, -1, -3] = true := by decide +kernel
theorem subd6_3_105 : subd6_3 [0, -1, -2] = true := by decide +kernel
theorem subd6_3_106 : subd6_3 [0, -1, -1] = true := by decide +kernel
theorem subd6_3_107 : subd6_3 [0, -1, 0] = true := by decide +kernel
theorem subd6_3_108 : subd6_3 [0, -1, 1] = true := by decide +kernel
theorem subd6_3_109 : subd6_3 [0, -1, 2] = true := by decide +kernel
theorem subd6_3_110 : subd6_3 [0, -1, 3] = true := by decide +kernel
theorem subd6_3_111 : subd6_3 [0, -1, 4] = true := by decide +kernel
theorem subd6_3_112 : subd6_3 [0, -1, 5] = true := by decide +kernel
theorem subd6_3_113 : subd6_3 [0, -1, 6] = true := by decide +kernel
theorem subd6_3_114 : subd6_3 [0, -1, 7] = true := by decide +kernel
theorem subd6_3_115 : subd6_3 [0, -1, 8] = true := by decide +kernel
theorem subd6_3_116 : subd6_3 [0, -1, 9] = true := by decide +kernel
theorem subd6_3_117 : subd6_3 [0, -1, 10] = true := by decide +kernel
theorem subd6_3_118 : subd6_3 [0, 0, -11] = true := by decide +kernel
theorem subd6_3_119 : subd6_3 [0, 0, -10] = true := by decide +kernel
theorem subd6_3_120 : subd6_3 [0, 0, -9] = true := by decide +kernel
theorem subd6_3_121 : subd6_3 [0, 0, -8] = true := by decide +kernel
theorem subd6_3_122 : subd6_3 [0, 0, -7] = true := by decide +kernel
theorem subd6_3_123 : subd6_3 [0, 0, -6] = true := by decide +kernel
theorem subd6_3_124 : subd6_3 [0, 0, -5] = true := by decide +kernel
theorem subd6_3_125 : subd6_3 [0, 0, -4] = true := by decide +kernel
theorem subd6_3_126 : subd6_3 [0, 0, -3] = true := by decide +kernel
theorem subd6_3_127 : subd6_3 [0, 0, -2] = true := by decide +kernel
theorem sbd6_3_3 : ∀ q ∈ blkd6_3_3, subd6_3 q = true := by
  unfold blkd6_3_3
  exact List.forall_mem_cons.2 ⟨subd6_3_96, List.forall_mem_cons.2 ⟨subd6_3_97, List.forall_mem_cons.2 ⟨subd6_3_98, List.forall_mem_cons.2 ⟨subd6_3_99, List.forall_mem_cons.2 ⟨subd6_3_100, List.forall_mem_cons.2 ⟨subd6_3_101, List.forall_mem_cons.2 ⟨subd6_3_102, List.forall_mem_cons.2 ⟨subd6_3_103, List.forall_mem_cons.2 ⟨subd6_3_104, List.forall_mem_cons.2 ⟨subd6_3_105, List.forall_mem_cons.2 ⟨subd6_3_106, List.forall_mem_cons.2 ⟨subd6_3_107, List.forall_mem_cons.2 ⟨subd6_3_108, List.forall_mem_cons.2 ⟨subd6_3_109, List.forall_mem_cons.2 ⟨subd6_3_110, List.forall_mem_cons.2 ⟨subd6_3_111, List.forall_mem_cons.2 ⟨subd6_3_112, List.forall_mem_cons.2 ⟨subd6_3_113, List.forall_mem_cons.2 ⟨subd6_3_114, List.forall_mem_cons.2 ⟨subd6_3_115, List.forall_mem_cons.2 ⟨subd6_3_116, List.forall_mem_cons.2 ⟨subd6_3_117, List.forall_mem_cons.2 ⟨subd6_3_118, List.forall_mem_cons.2 ⟨subd6_3_119, List.forall_mem_cons.2 ⟨subd6_3_120, List.forall_mem_cons.2 ⟨subd6_3_121, List.forall_mem_cons.2 ⟨subd6_3_122, List.forall_mem_cons.2 ⟨subd6_3_123, List.forall_mem_cons.2 ⟨subd6_3_124, List.forall_mem_cons.2 ⟨subd6_3_125, List.forall_mem_cons.2 ⟨subd6_3_126, List.forall_mem_cons.2 ⟨subd6_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_128 : subd6_3 [0, 0, -1] = true := by decide +kernel
theorem subd6_3_129 : subd6_3 [0, 0, 0] = true := by decide +kernel
theorem subd6_3_130 : subd6_3 [0, 0, 1] = true := by decide +kernel
theorem subd6_3_131 : subd6_3 [0, 0, 2] = true := by decide +kernel
theorem subd6_3_132 : subd6_3 [0, 0, 3] = true := by decide +kernel
theorem subd6_3_133 : subd6_3 [0, 0, 4] = true := by decide +kernel
theorem subd6_3_134 : subd6_3 [0, 0, 5] = true := by decide +kernel
theorem subd6_3_135 : subd6_3 [0, 0, 6] = true := by decide +kernel
theorem subd6_3_136 : subd6_3 [0, 0, 7] = true := by decide +kernel
theorem subd6_3_137 : subd6_3 [0, 0, 8] = true := by decide +kernel
theorem subd6_3_138 : subd6_3 [0, 0, 9] = true := by decide +kernel
theorem subd6_3_139 : subd6_3 [0, 0, 10] = true := by decide +kernel
theorem subd6_3_140 : subd6_3 [0, 1, -11] = true := by decide +kernel
theorem subd6_3_141 : subd6_3 [0, 1, -10] = true := by decide +kernel
theorem subd6_3_142 : subd6_3 [0, 1, -9] = true := by decide +kernel
theorem subd6_3_143 : subd6_3 [0, 1, -8] = true := by decide +kernel
theorem subd6_3_144 : subd6_3 [0, 1, -7] = true := by decide +kernel
theorem subd6_3_145 : subd6_3 [0, 1, -6] = true := by decide +kernel
theorem subd6_3_146 : subd6_3 [0, 1, -5] = true := by decide +kernel
theorem subd6_3_147 : subd6_3 [0, 1, -4] = true := by decide +kernel
theorem subd6_3_148 : subd6_3 [0, 1, -3] = true := by decide +kernel
theorem subd6_3_149 : subd6_3 [0, 1, -2] = true := by decide +kernel
theorem subd6_3_150 : subd6_3 [0, 1, -1] = true := by decide +kernel
theorem subd6_3_151 : subd6_3 [0, 1, 0] = true := by decide +kernel
theorem subd6_3_152 : subd6_3 [0, 1, 1] = true := by decide +kernel
theorem subd6_3_153 : subd6_3 [0, 1, 2] = true := by decide +kernel
theorem subd6_3_154 : subd6_3 [0, 1, 3] = true := by decide +kernel
theorem subd6_3_155 : subd6_3 [0, 1, 4] = true := by decide +kernel
theorem subd6_3_156 : subd6_3 [0, 1, 5] = true := by decide +kernel
theorem subd6_3_157 : subd6_3 [0, 1, 6] = true := by decide +kernel
theorem subd6_3_158 : subd6_3 [0, 1, 7] = true := by decide +kernel
theorem subd6_3_159 : subd6_3 [0, 1, 8] = true := by decide +kernel
theorem sbd6_3_4 : ∀ q ∈ blkd6_3_4, subd6_3 q = true := by
  unfold blkd6_3_4
  exact List.forall_mem_cons.2 ⟨subd6_3_128, List.forall_mem_cons.2 ⟨subd6_3_129, List.forall_mem_cons.2 ⟨subd6_3_130, List.forall_mem_cons.2 ⟨subd6_3_131, List.forall_mem_cons.2 ⟨subd6_3_132, List.forall_mem_cons.2 ⟨subd6_3_133, List.forall_mem_cons.2 ⟨subd6_3_134, List.forall_mem_cons.2 ⟨subd6_3_135, List.forall_mem_cons.2 ⟨subd6_3_136, List.forall_mem_cons.2 ⟨subd6_3_137, List.forall_mem_cons.2 ⟨subd6_3_138, List.forall_mem_cons.2 ⟨subd6_3_139, List.forall_mem_cons.2 ⟨subd6_3_140, List.forall_mem_cons.2 ⟨subd6_3_141, List.forall_mem_cons.2 ⟨subd6_3_142, List.forall_mem_cons.2 ⟨subd6_3_143, List.forall_mem_cons.2 ⟨subd6_3_144, List.forall_mem_cons.2 ⟨subd6_3_145, List.forall_mem_cons.2 ⟨subd6_3_146, List.forall_mem_cons.2 ⟨subd6_3_147, List.forall_mem_cons.2 ⟨subd6_3_148, List.forall_mem_cons.2 ⟨subd6_3_149, List.forall_mem_cons.2 ⟨subd6_3_150, List.forall_mem_cons.2 ⟨subd6_3_151, List.forall_mem_cons.2 ⟨subd6_3_152, List.forall_mem_cons.2 ⟨subd6_3_153, List.forall_mem_cons.2 ⟨subd6_3_154, List.forall_mem_cons.2 ⟨subd6_3_155, List.forall_mem_cons.2 ⟨subd6_3_156, List.forall_mem_cons.2 ⟨subd6_3_157, List.forall_mem_cons.2 ⟨subd6_3_158, List.forall_mem_cons.2 ⟨subd6_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_160 : subd6_3 [0, 1, 9] = true := by decide +kernel
theorem subd6_3_161 : subd6_3 [0, 1, 10] = true := by decide +kernel
theorem subd6_3_162 : subd6_3 [0, 2, -8] = true := by decide +kernel
theorem subd6_3_163 : subd6_3 [0, 2, -7] = true := by decide +kernel
theorem subd6_3_164 : subd6_3 [0, 2, -6] = true := by decide +kernel
theorem subd6_3_165 : subd6_3 [0, 2, -5] = true := by decide +kernel
theorem subd6_3_166 : subd6_3 [0, 2, -4] = true := by decide +kernel
theorem subd6_3_167 : subd6_3 [0, 2, -3] = true := by decide +kernel
theorem subd6_3_168 : subd6_3 [0, 2, -2] = true := by decide +kernel
theorem subd6_3_169 : subd6_3 [0, 2, -1] = true := by decide +kernel
theorem subd6_3_170 : subd6_3 [0, 2, 0] = true := by decide +kernel
theorem subd6_3_171 : subd6_3 [0, 2, 1] = true := by decide +kernel
theorem subd6_3_172 : subd6_3 [0, 2, 2] = true := by decide +kernel
theorem subd6_3_173 : subd6_3 [0, 2, 3] = true := by decide +kernel
theorem subd6_3_174 : subd6_3 [0, 2, 4] = true := by decide +kernel
theorem subd6_3_175 : subd6_3 [0, 2, 5] = true := by decide +kernel
theorem subd6_3_176 : subd6_3 [0, 2, 6] = true := by decide +kernel
theorem subd6_3_177 : subd6_3 [0, 2, 7] = true := by decide +kernel
theorem subd6_3_178 : subd6_3 [1, -2] = true := by decide +kernel
theorem subd6_3_179 : subd6_3 [1, -1, -9] = true := by decide +kernel
theorem subd6_3_180 : subd6_3 [1, -1, -8] = true := by decide +kernel
theorem subd6_3_181 : subd6_3 [1, -1, -7] = true := by decide +kernel
theorem subd6_3_182 : subd6_3 [1, -1, -6] = true := by decide +kernel
theorem subd6_3_183 : subd6_3 [1, -1, -5] = true := by decide +kernel
theorem subd6_3_184 : subd6_3 [1, -1, -4] = true := by decide +kernel
theorem subd6_3_185 : subd6_3 [1, -1, -3] = true := by decide +kernel
theorem subd6_3_186 : subd6_3 [1, -1, -2] = true := by decide +kernel
theorem subd6_3_187 : subd6_3 [1, -1, -1] = true := by decide +kernel
theorem subd6_3_188 : subd6_3 [1, -1, 0] = true := by decide +kernel
theorem subd6_3_189 : subd6_3 [1, -1, 1] = true := by decide +kernel
theorem subd6_3_190 : subd6_3 [1, -1, 2] = true := by decide +kernel
theorem subd6_3_191 : subd6_3 [1, -1, 3] = true := by decide +kernel
theorem sbd6_3_5 : ∀ q ∈ blkd6_3_5, subd6_3 q = true := by
  unfold blkd6_3_5
  exact List.forall_mem_cons.2 ⟨subd6_3_160, List.forall_mem_cons.2 ⟨subd6_3_161, List.forall_mem_cons.2 ⟨subd6_3_162, List.forall_mem_cons.2 ⟨subd6_3_163, List.forall_mem_cons.2 ⟨subd6_3_164, List.forall_mem_cons.2 ⟨subd6_3_165, List.forall_mem_cons.2 ⟨subd6_3_166, List.forall_mem_cons.2 ⟨subd6_3_167, List.forall_mem_cons.2 ⟨subd6_3_168, List.forall_mem_cons.2 ⟨subd6_3_169, List.forall_mem_cons.2 ⟨subd6_3_170, List.forall_mem_cons.2 ⟨subd6_3_171, List.forall_mem_cons.2 ⟨subd6_3_172, List.forall_mem_cons.2 ⟨subd6_3_173, List.forall_mem_cons.2 ⟨subd6_3_174, List.forall_mem_cons.2 ⟨subd6_3_175, List.forall_mem_cons.2 ⟨subd6_3_176, List.forall_mem_cons.2 ⟨subd6_3_177, List.forall_mem_cons.2 ⟨subd6_3_178, List.forall_mem_cons.2 ⟨subd6_3_179, List.forall_mem_cons.2 ⟨subd6_3_180, List.forall_mem_cons.2 ⟨subd6_3_181, List.forall_mem_cons.2 ⟨subd6_3_182, List.forall_mem_cons.2 ⟨subd6_3_183, List.forall_mem_cons.2 ⟨subd6_3_184, List.forall_mem_cons.2 ⟨subd6_3_185, List.forall_mem_cons.2 ⟨subd6_3_186, List.forall_mem_cons.2 ⟨subd6_3_187, List.forall_mem_cons.2 ⟨subd6_3_188, List.forall_mem_cons.2 ⟨subd6_3_189, List.forall_mem_cons.2 ⟨subd6_3_190, List.forall_mem_cons.2 ⟨subd6_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_192 : subd6_3 [1, -1, 4] = true := by decide +kernel
theorem subd6_3_193 : subd6_3 [1, -1, 5] = true := by decide +kernel
theorem subd6_3_194 : subd6_3 [1, -1, 6] = true := by decide +kernel
theorem subd6_3_195 : subd6_3 [1, -1, 7] = true := by decide +kernel
theorem subd6_3_196 : subd6_3 [1, 0, -10] = true := by decide +kernel
theorem subd6_3_197 : subd6_3 [1, 0, -9] = true := by decide +kernel
theorem subd6_3_198 : subd6_3 [1, 0, -8] = true := by decide +kernel
theorem subd6_3_199 : subd6_3 [1, 0, -7] = true := by decide +kernel
theorem subd6_3_200 : subd6_3 [1, 0, -6] = true := by decide +kernel
theorem subd6_3_201 : subd6_3 [1, 0, -5] = true := by decide +kernel
theorem subd6_3_202 : subd6_3 [1, 0, -4] = true := by decide +kernel
theorem subd6_3_203 : subd6_3 [1, 0, -3] = true := by decide +kernel
theorem subd6_3_204 : subd6_3 [1, 0, -2] = true := by decide +kernel
theorem subd6_3_205 : subd6_3 [1, 0, -1] = true := by decide +kernel
theorem subd6_3_206 : subd6_3 [1, 0, 0] = true := by decide +kernel
theorem subd6_3_207 : subd6_3 [1, 0, 1] = true := by decide +kernel
theorem subd6_3_208 : subd6_3 [1, 0, 2] = true := by decide +kernel
theorem subd6_3_209 : subd6_3 [1, 0, 3] = true := by decide +kernel
theorem subd6_3_210 : subd6_3 [1, 0, 4] = true := by decide +kernel
theorem subd6_3_211 : subd6_3 [1, 0, 5] = true := by decide +kernel
theorem subd6_3_212 : subd6_3 [1, 0, 6] = true := by decide +kernel
theorem subd6_3_213 : subd6_3 [1, 0, 7] = true := by decide +kernel
theorem subd6_3_214 : subd6_3 [1, 0, 8] = true := by decide +kernel
theorem subd6_3_215 : subd6_3 [1, 0, 9] = true := by decide +kernel
theorem subd6_3_216 : subd6_3 [1, 1, -10] = true := by decide +kernel
theorem subd6_3_217 : subd6_3 [1, 1, -9] = true := by decide +kernel
theorem subd6_3_218 : subd6_3 [1, 1, -8] = true := by decide +kernel
theorem subd6_3_219 : subd6_3 [1, 1, -7] = true := by decide +kernel
theorem subd6_3_220 : subd6_3 [1, 1, -6] = true := by decide +kernel
theorem subd6_3_221 : subd6_3 [1, 1, -5] = true := by decide +kernel
theorem subd6_3_222 : subd6_3 [1, 1, -4] = true := by decide +kernel
theorem subd6_3_223 : subd6_3 [1, 1, -3] = true := by decide +kernel
theorem sbd6_3_6 : ∀ q ∈ blkd6_3_6, subd6_3 q = true := by
  unfold blkd6_3_6
  exact List.forall_mem_cons.2 ⟨subd6_3_192, List.forall_mem_cons.2 ⟨subd6_3_193, List.forall_mem_cons.2 ⟨subd6_3_194, List.forall_mem_cons.2 ⟨subd6_3_195, List.forall_mem_cons.2 ⟨subd6_3_196, List.forall_mem_cons.2 ⟨subd6_3_197, List.forall_mem_cons.2 ⟨subd6_3_198, List.forall_mem_cons.2 ⟨subd6_3_199, List.forall_mem_cons.2 ⟨subd6_3_200, List.forall_mem_cons.2 ⟨subd6_3_201, List.forall_mem_cons.2 ⟨subd6_3_202, List.forall_mem_cons.2 ⟨subd6_3_203, List.forall_mem_cons.2 ⟨subd6_3_204, List.forall_mem_cons.2 ⟨subd6_3_205, List.forall_mem_cons.2 ⟨subd6_3_206, List.forall_mem_cons.2 ⟨subd6_3_207, List.forall_mem_cons.2 ⟨subd6_3_208, List.forall_mem_cons.2 ⟨subd6_3_209, List.forall_mem_cons.2 ⟨subd6_3_210, List.forall_mem_cons.2 ⟨subd6_3_211, List.forall_mem_cons.2 ⟨subd6_3_212, List.forall_mem_cons.2 ⟨subd6_3_213, List.forall_mem_cons.2 ⟨subd6_3_214, List.forall_mem_cons.2 ⟨subd6_3_215, List.forall_mem_cons.2 ⟨subd6_3_216, List.forall_mem_cons.2 ⟨subd6_3_217, List.forall_mem_cons.2 ⟨subd6_3_218, List.forall_mem_cons.2 ⟨subd6_3_219, List.forall_mem_cons.2 ⟨subd6_3_220, List.forall_mem_cons.2 ⟨subd6_3_221, List.forall_mem_cons.2 ⟨subd6_3_222, List.forall_mem_cons.2 ⟨subd6_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C133
