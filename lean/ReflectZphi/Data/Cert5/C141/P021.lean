import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_2_128 : subd10_2 [0, -2, -8] = true := by decide +kernel
theorem subd10_2_129 : subd10_2 [0, -2, -7] = true := by decide +kernel
theorem subd10_2_130 : subd10_2 [0, -2, -6] = true := by decide +kernel
theorem subd10_2_131 : subd10_2 [0, -2, -5] = true := by decide +kernel
theorem subd10_2_132 : subd10_2 [0, -2, -4] = true := by decide +kernel
theorem subd10_2_133 : subd10_2 [0, -2, -3] = true := by decide +kernel
theorem subd10_2_134 : subd10_2 [0, -2, -2] = true := by decide +kernel
theorem subd10_2_135 : subd10_2 [0, -2, -1] = true := by decide +kernel
theorem subd10_2_136 : subd10_2 [0, -2, 0] = true := by decide +kernel
theorem subd10_2_137 : subd10_2 [0, -2, 1] = true := by decide +kernel
theorem subd10_2_138 : subd10_2 [0, -2, 2] = true := by decide +kernel
theorem subd10_2_139 : subd10_2 [0, -2, 3] = true := by decide +kernel
theorem subd10_2_140 : subd10_2 [0, -2, 4] = true := by decide +kernel
theorem subd10_2_141 : subd10_2 [0, -2, 5] = true := by decide +kernel
theorem subd10_2_142 : subd10_2 [0, -2, 6] = true := by decide +kernel
theorem subd10_2_143 : subd10_2 [0, -2, 7] = true := by decide +kernel
theorem subd10_2_144 : subd10_2 [0, -2, 8] = true := by decide +kernel
theorem subd10_2_145 : subd10_2 [0, -1, -9] = true := by decide +kernel
theorem subd10_2_146 : subd10_2 [0, -1, -8] = true := by decide +kernel
theorem subd10_2_147 : subd10_2 [0, -1, -7] = true := by decide +kernel
theorem subd10_2_148 : subd10_2 [0, -1, -6] = true := by decide +kernel
theorem subd10_2_149 : subd10_2 [0, -1, -5] = true := by decide +kernel
theorem subd10_2_150 : subd10_2 [0, -1, -4] = true := by decide +kernel
theorem subd10_2_151 : subd10_2 [0, -1, -3] = true := by decide +kernel
theorem subd10_2_152 : subd10_2 [0, -1, -2] = true := by decide +kernel
theorem subd10_2_153 : subd10_2 [0, -1, -1] = true := by decide +kernel
theorem subd10_2_154 : subd10_2 [0, -1, 0] = true := by decide +kernel
theorem subd10_2_155 : subd10_2 [0, -1, 1] = true := by decide +kernel
theorem subd10_2_156 : subd10_2 [0, -1, 2] = true := by decide +kernel
theorem subd10_2_157 : subd10_2 [0, -1, 3] = true := by decide +kernel
theorem subd10_2_158 : subd10_2 [0, -1, 4] = true := by decide +kernel
theorem subd10_2_159 : subd10_2 [0, -1, 5] = true := by decide +kernel
theorem sbd10_2_4 : ∀ q ∈ blkd10_2_4, subd10_2 q = true := by
  unfold blkd10_2_4
  exact List.forall_mem_cons.2 ⟨subd10_2_128, List.forall_mem_cons.2 ⟨subd10_2_129, List.forall_mem_cons.2 ⟨subd10_2_130, List.forall_mem_cons.2 ⟨subd10_2_131, List.forall_mem_cons.2 ⟨subd10_2_132, List.forall_mem_cons.2 ⟨subd10_2_133, List.forall_mem_cons.2 ⟨subd10_2_134, List.forall_mem_cons.2 ⟨subd10_2_135, List.forall_mem_cons.2 ⟨subd10_2_136, List.forall_mem_cons.2 ⟨subd10_2_137, List.forall_mem_cons.2 ⟨subd10_2_138, List.forall_mem_cons.2 ⟨subd10_2_139, List.forall_mem_cons.2 ⟨subd10_2_140, List.forall_mem_cons.2 ⟨subd10_2_141, List.forall_mem_cons.2 ⟨subd10_2_142, List.forall_mem_cons.2 ⟨subd10_2_143, List.forall_mem_cons.2 ⟨subd10_2_144, List.forall_mem_cons.2 ⟨subd10_2_145, List.forall_mem_cons.2 ⟨subd10_2_146, List.forall_mem_cons.2 ⟨subd10_2_147, List.forall_mem_cons.2 ⟨subd10_2_148, List.forall_mem_cons.2 ⟨subd10_2_149, List.forall_mem_cons.2 ⟨subd10_2_150, List.forall_mem_cons.2 ⟨subd10_2_151, List.forall_mem_cons.2 ⟨subd10_2_152, List.forall_mem_cons.2 ⟨subd10_2_153, List.forall_mem_cons.2 ⟨subd10_2_154, List.forall_mem_cons.2 ⟨subd10_2_155, List.forall_mem_cons.2 ⟨subd10_2_156, List.forall_mem_cons.2 ⟨subd10_2_157, List.forall_mem_cons.2 ⟨subd10_2_158, List.forall_mem_cons.2 ⟨subd10_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_160 : subd10_2 [0, -1, 6] = true := by decide +kernel
theorem subd10_2_161 : subd10_2 [0, -1, 7] = true := by decide +kernel
theorem subd10_2_162 : subd10_2 [0, -1, 8] = true := by decide +kernel
theorem subd10_2_163 : subd10_2 [0, -1, 9] = true := by decide +kernel
theorem subd10_2_164 : subd10_2 [0, 0, -10] = true := by decide +kernel
theorem subd10_2_165 : subd10_2 [0, 0, -9] = true := by decide +kernel
theorem subd10_2_166 : subd10_2 [0, 0, -8] = true := by decide +kernel
theorem subd10_2_167 : subd10_2 [0, 0, -7] = true := by decide +kernel
theorem subd10_2_168 : subd10_2 [0, 0, -6] = true := by decide +kernel
theorem subd10_2_169 : subd10_2 [0, 0, -5] = true := by decide +kernel
theorem subd10_2_170 : subd10_2 [0, 0, -4] = true := by decide +kernel
theorem subd10_2_171 : subd10_2 [0, 0, -3] = true := by decide +kernel
theorem subd10_2_172 : subd10_2 [0, 0, -2] = true := by decide +kernel
theorem subd10_2_173 : subd10_2 [0, 0, -1] = true := by decide +kernel
theorem subd10_2_174 : subd10_2 [0, 0, 0] = true := by decide +kernel
theorem subd10_2_175 : subd10_2 [0, 0, 1] = true := by decide +kernel
theorem subd10_2_176 : subd10_2 [0, 0, 2] = true := by decide +kernel
theorem subd10_2_177 : subd10_2 [0, 0, 3] = true := by decide +kernel
theorem subd10_2_178 : subd10_2 [0, 0, 4] = true := by decide +kernel
theorem subd10_2_179 : subd10_2 [0, 0, 5] = true := by decide +kernel
theorem subd10_2_180 : subd10_2 [0, 0, 6] = true := by decide +kernel
theorem subd10_2_181 : subd10_2 [0, 0, 7] = true := by decide +kernel
theorem subd10_2_182 : subd10_2 [0, 0, 8] = true := by decide +kernel
theorem subd10_2_183 : subd10_2 [0, 0, 9] = true := by decide +kernel
theorem subd10_2_184 : subd10_2 [0, 1, -10] = true := by decide +kernel
theorem subd10_2_185 : subd10_2 [0, 1, -9] = true := by decide +kernel
theorem subd10_2_186 : subd10_2 [0, 1, -8] = true := by decide +kernel
theorem subd10_2_187 : subd10_2 [0, 1, -7] = true := by decide +kernel
theorem subd10_2_188 : subd10_2 [0, 1, -6] = true := by decide +kernel
theorem subd10_2_189 : subd10_2 [0, 1, -5] = true := by decide +kernel
theorem subd10_2_190 : subd10_2 [0, 1, -4] = true := by decide +kernel
theorem subd10_2_191 : subd10_2 [0, 1, -3] = true := by decide +kernel
theorem sbd10_2_5 : ∀ q ∈ blkd10_2_5, subd10_2 q = true := by
  unfold blkd10_2_5
  exact List.forall_mem_cons.2 ⟨subd10_2_160, List.forall_mem_cons.2 ⟨subd10_2_161, List.forall_mem_cons.2 ⟨subd10_2_162, List.forall_mem_cons.2 ⟨subd10_2_163, List.forall_mem_cons.2 ⟨subd10_2_164, List.forall_mem_cons.2 ⟨subd10_2_165, List.forall_mem_cons.2 ⟨subd10_2_166, List.forall_mem_cons.2 ⟨subd10_2_167, List.forall_mem_cons.2 ⟨subd10_2_168, List.forall_mem_cons.2 ⟨subd10_2_169, List.forall_mem_cons.2 ⟨subd10_2_170, List.forall_mem_cons.2 ⟨subd10_2_171, List.forall_mem_cons.2 ⟨subd10_2_172, List.forall_mem_cons.2 ⟨subd10_2_173, List.forall_mem_cons.2 ⟨subd10_2_174, List.forall_mem_cons.2 ⟨subd10_2_175, List.forall_mem_cons.2 ⟨subd10_2_176, List.forall_mem_cons.2 ⟨subd10_2_177, List.forall_mem_cons.2 ⟨subd10_2_178, List.forall_mem_cons.2 ⟨subd10_2_179, List.forall_mem_cons.2 ⟨subd10_2_180, List.forall_mem_cons.2 ⟨subd10_2_181, List.forall_mem_cons.2 ⟨subd10_2_182, List.forall_mem_cons.2 ⟨subd10_2_183, List.forall_mem_cons.2 ⟨subd10_2_184, List.forall_mem_cons.2 ⟨subd10_2_185, List.forall_mem_cons.2 ⟨subd10_2_186, List.forall_mem_cons.2 ⟨subd10_2_187, List.forall_mem_cons.2 ⟨subd10_2_188, List.forall_mem_cons.2 ⟨subd10_2_189, List.forall_mem_cons.2 ⟨subd10_2_190, List.forall_mem_cons.2 ⟨subd10_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_192 : subd10_2 [0, 1, -2] = true := by decide +kernel
theorem subd10_2_193 : subd10_2 [0, 1, -1] = true := by decide +kernel
theorem subd10_2_194 : subd10_2 [0, 1, 0] = true := by decide +kernel
theorem subd10_2_195 : subd10_2 [0, 1, 1] = true := by decide +kernel
theorem subd10_2_196 : subd10_2 [0, 1, 2] = true := by decide +kernel
theorem subd10_2_197 : subd10_2 [0, 1, 3] = true := by decide +kernel
theorem subd10_2_198 : subd10_2 [0, 1, 4] = true := by decide +kernel
theorem subd10_2_199 : subd10_2 [0, 1, 5] = true := by decide +kernel
theorem subd10_2_200 : subd10_2 [0, 1, 6] = true := by decide +kernel
theorem subd10_2_201 : subd10_2 [0, 1, 7] = true := by decide +kernel
theorem subd10_2_202 : subd10_2 [0, 1, 8] = true := by decide +kernel
theorem subd10_2_203 : subd10_2 [0, 2, -9] = true := by decide +kernel
theorem subd10_2_204 : subd10_2 [0, 2, -8] = true := by decide +kernel
theorem subd10_2_205 : subd10_2 [0, 2, -7] = true := by decide +kernel
theorem subd10_2_206 : subd10_2 [0, 2, -6] = true := by decide +kernel
theorem subd10_2_207 : subd10_2 [0, 2, -5] = true := by decide +kernel
theorem subd10_2_208 : subd10_2 [0, 2, -4] = true := by decide +kernel
theorem subd10_2_209 : subd10_2 [0, 2, -3] = true := by decide +kernel
theorem subd10_2_210 : subd10_2 [0, 2, -2] = true := by decide +kernel
theorem subd10_2_211 : subd10_2 [0, 2, -1] = true := by decide +kernel
theorem subd10_2_212 : subd10_2 [0, 2, 0] = true := by decide +kernel
theorem subd10_2_213 : subd10_2 [0, 2, 1] = true := by decide +kernel
theorem subd10_2_214 : subd10_2 [0, 2, 2] = true := by decide +kernel
theorem subd10_2_215 : subd10_2 [0, 2, 3] = true := by decide +kernel
theorem subd10_2_216 : subd10_2 [0, 2, 4] = true := by decide +kernel
theorem subd10_2_217 : subd10_2 [0, 2, 5] = true := by decide +kernel
theorem subd10_2_218 : subd10_2 [0, 2, 6] = true := by decide +kernel
theorem subd10_2_219 : subd10_2 [0, 2, 7] = true := by decide +kernel
theorem subd10_2_220 : subd10_2 [0, 3] = true := by decide +kernel
theorem subd10_2_221 : subd10_2 [1, -4] = true := by decide +kernel
theorem subd10_2_222 : subd10_2 [1, -3] = true := by decide +kernel
theorem subd10_2_223 : subd10_2 [1, -2, -8] = true := by decide +kernel
theorem sbd10_2_6 : ∀ q ∈ blkd10_2_6, subd10_2 q = true := by
  unfold blkd10_2_6
  exact List.forall_mem_cons.2 ⟨subd10_2_192, List.forall_mem_cons.2 ⟨subd10_2_193, List.forall_mem_cons.2 ⟨subd10_2_194, List.forall_mem_cons.2 ⟨subd10_2_195, List.forall_mem_cons.2 ⟨subd10_2_196, List.forall_mem_cons.2 ⟨subd10_2_197, List.forall_mem_cons.2 ⟨subd10_2_198, List.forall_mem_cons.2 ⟨subd10_2_199, List.forall_mem_cons.2 ⟨subd10_2_200, List.forall_mem_cons.2 ⟨subd10_2_201, List.forall_mem_cons.2 ⟨subd10_2_202, List.forall_mem_cons.2 ⟨subd10_2_203, List.forall_mem_cons.2 ⟨subd10_2_204, List.forall_mem_cons.2 ⟨subd10_2_205, List.forall_mem_cons.2 ⟨subd10_2_206, List.forall_mem_cons.2 ⟨subd10_2_207, List.forall_mem_cons.2 ⟨subd10_2_208, List.forall_mem_cons.2 ⟨subd10_2_209, List.forall_mem_cons.2 ⟨subd10_2_210, List.forall_mem_cons.2 ⟨subd10_2_211, List.forall_mem_cons.2 ⟨subd10_2_212, List.forall_mem_cons.2 ⟨subd10_2_213, List.forall_mem_cons.2 ⟨subd10_2_214, List.forall_mem_cons.2 ⟨subd10_2_215, List.forall_mem_cons.2 ⟨subd10_2_216, List.forall_mem_cons.2 ⟨subd10_2_217, List.forall_mem_cons.2 ⟨subd10_2_218, List.forall_mem_cons.2 ⟨subd10_2_219, List.forall_mem_cons.2 ⟨subd10_2_220, List.forall_mem_cons.2 ⟨subd10_2_221, List.forall_mem_cons.2 ⟨subd10_2_222, List.forall_mem_cons.2 ⟨subd10_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_224 : subd10_2 [1, -2, -7] = true := by decide +kernel
theorem subd10_2_225 : subd10_2 [1, -2, -6] = true := by decide +kernel
theorem subd10_2_226 : subd10_2 [1, -2, -5] = true := by decide +kernel
theorem subd10_2_227 : subd10_2 [1, -2, -4] = true := by decide +kernel
theorem subd10_2_228 : subd10_2 [1, -2, -3] = true := by decide +kernel
theorem subd10_2_229 : subd10_2 [1, -2, -2] = true := by decide +kernel
theorem subd10_2_230 : subd10_2 [1, -2, -1] = true := by decide +kernel
theorem subd10_2_231 : subd10_2 [1, -2, 0] = true := by decide +kernel
theorem subd10_2_232 : subd10_2 [1, -2, 1] = true := by decide +kernel
theorem subd10_2_233 : subd10_2 [1, -2, 2] = true := by decide +kernel
theorem subd10_2_234 : subd10_2 [1, -2, 3] = true := by decide +kernel
theorem subd10_2_235 : subd10_2 [1, -2, 4] = true := by decide +kernel
theorem subd10_2_236 : subd10_2 [1, -2, 5] = true := by decide +kernel
theorem subd10_2_237 : subd10_2 [1, -2, 6] = true := by decide +kernel
theorem subd10_2_238 : subd10_2 [1, -2, 7] = true := by decide +kernel
theorem subd10_2_239 : subd10_2 [1, -1, -9] = true := by decide +kernel
theorem subd10_2_240 : subd10_2 [1, -1, -8] = true := by decide +kernel
theorem subd10_2_241 : subd10_2 [1, -1, -7] = true := by decide +kernel
theorem subd10_2_242 : subd10_2 [1, -1, -6] = true := by decide +kernel
theorem subd10_2_243 : subd10_2 [1, -1, -5] = true := by decide +kernel
theorem subd10_2_244 : subd10_2 [1, -1, -4] = true := by decide +kernel
theorem subd10_2_245 : subd10_2 [1, -1, -3] = true := by decide +kernel
theorem subd10_2_246 : subd10_2 [1, -1, -2] = true := by decide +kernel
theorem subd10_2_247 : subd10_2 [1, -1, -1] = true := by decide +kernel
theorem subd10_2_248 : subd10_2 [1, -1, 0] = true := by decide +kernel
theorem subd10_2_249 : subd10_2 [1, -1, 1] = true := by decide +kernel
theorem subd10_2_250 : subd10_2 [1, -1, 2] = true := by decide +kernel
theorem subd10_2_251 : subd10_2 [1, -1, 3] = true := by decide +kernel
theorem subd10_2_252 : subd10_2 [1, -1, 4] = true := by decide +kernel
theorem subd10_2_253 : subd10_2 [1, -1, 5] = true := by decide +kernel
theorem subd10_2_254 : subd10_2 [1, -1, 6] = true := by decide +kernel
theorem subd10_2_255 : subd10_2 [1, -1, 7] = true := by decide +kernel
theorem sbd10_2_7 : ∀ q ∈ blkd10_2_7, subd10_2 q = true := by
  unfold blkd10_2_7
  exact List.forall_mem_cons.2 ⟨subd10_2_224, List.forall_mem_cons.2 ⟨subd10_2_225, List.forall_mem_cons.2 ⟨subd10_2_226, List.forall_mem_cons.2 ⟨subd10_2_227, List.forall_mem_cons.2 ⟨subd10_2_228, List.forall_mem_cons.2 ⟨subd10_2_229, List.forall_mem_cons.2 ⟨subd10_2_230, List.forall_mem_cons.2 ⟨subd10_2_231, List.forall_mem_cons.2 ⟨subd10_2_232, List.forall_mem_cons.2 ⟨subd10_2_233, List.forall_mem_cons.2 ⟨subd10_2_234, List.forall_mem_cons.2 ⟨subd10_2_235, List.forall_mem_cons.2 ⟨subd10_2_236, List.forall_mem_cons.2 ⟨subd10_2_237, List.forall_mem_cons.2 ⟨subd10_2_238, List.forall_mem_cons.2 ⟨subd10_2_239, List.forall_mem_cons.2 ⟨subd10_2_240, List.forall_mem_cons.2 ⟨subd10_2_241, List.forall_mem_cons.2 ⟨subd10_2_242, List.forall_mem_cons.2 ⟨subd10_2_243, List.forall_mem_cons.2 ⟨subd10_2_244, List.forall_mem_cons.2 ⟨subd10_2_245, List.forall_mem_cons.2 ⟨subd10_2_246, List.forall_mem_cons.2 ⟨subd10_2_247, List.forall_mem_cons.2 ⟨subd10_2_248, List.forall_mem_cons.2 ⟨subd10_2_249, List.forall_mem_cons.2 ⟨subd10_2_250, List.forall_mem_cons.2 ⟨subd10_2_251, List.forall_mem_cons.2 ⟨subd10_2_252, List.forall_mem_cons.2 ⟨subd10_2_253, List.forall_mem_cons.2 ⟨subd10_2_254, List.forall_mem_cons.2 ⟨subd10_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_256 : subd10_2 [1, -1, 8] = true := by decide +kernel
theorem subd10_2_257 : subd10_2 [1, 0, -10] = true := by decide +kernel
theorem subd10_2_258 : subd10_2 [1, 0, -9] = true := by decide +kernel
theorem subd10_2_259 : subd10_2 [1, 0, -8] = true := by decide +kernel
theorem subd10_2_260 : subd10_2 [1, 0, -7] = true := by decide +kernel
theorem subd10_2_261 : subd10_2 [1, 0, -6] = true := by decide +kernel
theorem subd10_2_262 : subd10_2 [1, 0, -5] = true := by decide +kernel
theorem subd10_2_263 : subd10_2 [1, 0, -4] = true := by decide +kernel
theorem subd10_2_264 : subd10_2 [1, 0, -3] = true := by decide +kernel
theorem subd10_2_265 : subd10_2 [1, 0, -2] = true := by decide +kernel
theorem subd10_2_266 : subd10_2 [1, 0, -1] = true := by decide +kernel
theorem subd10_2_267 : subd10_2 [1, 0, 0] = true := by decide +kernel
theorem subd10_2_268 : subd10_2 [1, 0, 1] = true := by decide +kernel
theorem subd10_2_269 : subd10_2 [1, 0, 2] = true := by decide +kernel
theorem subd10_2_270 : subd10_2 [1, 0, 3] = true := by decide +kernel
theorem subd10_2_271 : subd10_2 [1, 0, 4] = true := by decide +kernel
theorem subd10_2_272 : subd10_2 [1, 0, 5] = true := by decide +kernel
theorem subd10_2_273 : subd10_2 [1, 0, 6] = true := by decide +kernel
theorem subd10_2_274 : subd10_2 [1, 0, 7] = true := by decide +kernel
theorem subd10_2_275 : subd10_2 [1, 0, 8] = true := by decide +kernel
theorem subd10_2_276 : subd10_2 [1, 1, -9] = true := by decide +kernel
theorem subd10_2_277 : subd10_2 [1, 1, -8] = true := by decide +kernel
theorem subd10_2_278 : subd10_2 [1, 1, -7] = true := by decide +kernel
theorem subd10_2_279 : subd10_2 [1, 1, -6] = true := by decide +kernel
theorem subd10_2_280 : subd10_2 [1, 1, -5] = true := by decide +kernel
theorem subd10_2_281 : subd10_2 [1, 1, -4] = true := by decide +kernel
theorem subd10_2_282 : subd10_2 [1, 1, -3] = true := by decide +kernel
theorem subd10_2_283 : subd10_2 [1, 1, -2] = true := by decide +kernel
theorem subd10_2_284 : subd10_2 [1, 1, -1] = true := by decide +kernel
theorem subd10_2_285 : subd10_2 [1, 1, 0] = true := by decide +kernel
theorem subd10_2_286 : subd10_2 [1, 1, 1] = true := by decide +kernel
theorem subd10_2_287 : subd10_2 [1, 1, 2] = true := by decide +kernel
theorem sbd10_2_8 : ∀ q ∈ blkd10_2_8, subd10_2 q = true := by
  unfold blkd10_2_8
  exact List.forall_mem_cons.2 ⟨subd10_2_256, List.forall_mem_cons.2 ⟨subd10_2_257, List.forall_mem_cons.2 ⟨subd10_2_258, List.forall_mem_cons.2 ⟨subd10_2_259, List.forall_mem_cons.2 ⟨subd10_2_260, List.forall_mem_cons.2 ⟨subd10_2_261, List.forall_mem_cons.2 ⟨subd10_2_262, List.forall_mem_cons.2 ⟨subd10_2_263, List.forall_mem_cons.2 ⟨subd10_2_264, List.forall_mem_cons.2 ⟨subd10_2_265, List.forall_mem_cons.2 ⟨subd10_2_266, List.forall_mem_cons.2 ⟨subd10_2_267, List.forall_mem_cons.2 ⟨subd10_2_268, List.forall_mem_cons.2 ⟨subd10_2_269, List.forall_mem_cons.2 ⟨subd10_2_270, List.forall_mem_cons.2 ⟨subd10_2_271, List.forall_mem_cons.2 ⟨subd10_2_272, List.forall_mem_cons.2 ⟨subd10_2_273, List.forall_mem_cons.2 ⟨subd10_2_274, List.forall_mem_cons.2 ⟨subd10_2_275, List.forall_mem_cons.2 ⟨subd10_2_276, List.forall_mem_cons.2 ⟨subd10_2_277, List.forall_mem_cons.2 ⟨subd10_2_278, List.forall_mem_cons.2 ⟨subd10_2_279, List.forall_mem_cons.2 ⟨subd10_2_280, List.forall_mem_cons.2 ⟨subd10_2_281, List.forall_mem_cons.2 ⟨subd10_2_282, List.forall_mem_cons.2 ⟨subd10_2_283, List.forall_mem_cons.2 ⟨subd10_2_284, List.forall_mem_cons.2 ⟨subd10_2_285, List.forall_mem_cons.2 ⟨subd10_2_286, List.forall_mem_cons.2 ⟨subd10_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_288 : subd10_2 [1, 1, 3] = true := by decide +kernel
theorem subd10_2_289 : subd10_2 [1, 1, 4] = true := by decide +kernel
theorem subd10_2_290 : subd10_2 [1, 1, 5] = true := by decide +kernel
theorem subd10_2_291 : subd10_2 [1, 1, 6] = true := by decide +kernel
theorem subd10_2_292 : subd10_2 [1, 1, 7] = true := by decide +kernel
theorem subd10_2_293 : subd10_2 [1, 1, 8] = true := by decide +kernel
theorem subd10_2_294 : subd10_2 [1, 2, -8] = true := by decide +kernel
theorem subd10_2_295 : subd10_2 [1, 2, -7] = true := by decide +kernel
theorem subd10_2_296 : subd10_2 [1, 2, -6] = true := by decide +kernel
theorem subd10_2_297 : subd10_2 [1, 2, -5] = true := by decide +kernel
theorem subd10_2_298 : subd10_2 [1, 2, -4] = true := by decide +kernel
theorem subd10_2_299 : subd10_2 [1, 2, -3] = true := by decide +kernel
theorem subd10_2_300 : subd10_2 [1, 2, -2] = true := by decide +kernel
theorem subd10_2_301 : subd10_2 [1, 2, -1] = true := by decide +kernel
theorem subd10_2_302 : subd10_2 [1, 2, 0] = true := by decide +kernel
theorem subd10_2_303 : subd10_2 [1, 2, 1] = true := by decide +kernel
theorem subd10_2_304 : subd10_2 [1, 2, 2] = true := by decide +kernel
theorem subd10_2_305 : subd10_2 [1, 2, 3] = true := by decide +kernel
theorem subd10_2_306 : subd10_2 [1, 2, 4] = true := by decide +kernel
theorem subd10_2_307 : subd10_2 [1, 2, 5] = true := by decide +kernel
theorem subd10_2_308 : subd10_2 [1, 2, 6] = true := by decide +kernel
theorem subd10_2_309 : subd10_2 [1, 3] = true := by decide +kernel
theorem subd10_2_310 : subd10_2 [2, -3] = true := by decide +kernel
theorem subd10_2_311 : subd10_2 [2, -2] = true := by decide +kernel
theorem subd10_2_312 : subd10_2 [2, -1, -8] = true := by decide +kernel
theorem subd10_2_313 : subd10_2 [2, -1, -7] = true := by decide +kernel
theorem subd10_2_314 : subd10_2 [2, -1, -6] = true := by decide +kernel
theorem subd10_2_315 : subd10_2 [2, -1, -5] = true := by decide +kernel
theorem subd10_2_316 : subd10_2 [2, -1, -4] = true := by decide +kernel
theorem subd10_2_317 : subd10_2 [2, -1, -3] = true := by decide +kernel
theorem subd10_2_318 : subd10_2 [2, -1, -2] = true := by decide +kernel
theorem subd10_2_319 : subd10_2 [2, -1, -1] = true := by decide +kernel
theorem sbd10_2_9 : ∀ q ∈ blkd10_2_9, subd10_2 q = true := by
  unfold blkd10_2_9
  exact List.forall_mem_cons.2 ⟨subd10_2_288, List.forall_mem_cons.2 ⟨subd10_2_289, List.forall_mem_cons.2 ⟨subd10_2_290, List.forall_mem_cons.2 ⟨subd10_2_291, List.forall_mem_cons.2 ⟨subd10_2_292, List.forall_mem_cons.2 ⟨subd10_2_293, List.forall_mem_cons.2 ⟨subd10_2_294, List.forall_mem_cons.2 ⟨subd10_2_295, List.forall_mem_cons.2 ⟨subd10_2_296, List.forall_mem_cons.2 ⟨subd10_2_297, List.forall_mem_cons.2 ⟨subd10_2_298, List.forall_mem_cons.2 ⟨subd10_2_299, List.forall_mem_cons.2 ⟨subd10_2_300, List.forall_mem_cons.2 ⟨subd10_2_301, List.forall_mem_cons.2 ⟨subd10_2_302, List.forall_mem_cons.2 ⟨subd10_2_303, List.forall_mem_cons.2 ⟨subd10_2_304, List.forall_mem_cons.2 ⟨subd10_2_305, List.forall_mem_cons.2 ⟨subd10_2_306, List.forall_mem_cons.2 ⟨subd10_2_307, List.forall_mem_cons.2 ⟨subd10_2_308, List.forall_mem_cons.2 ⟨subd10_2_309, List.forall_mem_cons.2 ⟨subd10_2_310, List.forall_mem_cons.2 ⟨subd10_2_311, List.forall_mem_cons.2 ⟨subd10_2_312, List.forall_mem_cons.2 ⟨subd10_2_313, List.forall_mem_cons.2 ⟨subd10_2_314, List.forall_mem_cons.2 ⟨subd10_2_315, List.forall_mem_cons.2 ⟨subd10_2_316, List.forall_mem_cons.2 ⟨subd10_2_317, List.forall_mem_cons.2 ⟨subd10_2_318, List.forall_mem_cons.2 ⟨subd10_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_320 : subd10_2 [2, -1, 0] = true := by decide +kernel
theorem subd10_2_321 : subd10_2 [2, -1, 1] = true := by decide +kernel
theorem subd10_2_322 : subd10_2 [2, -1, 2] = true := by decide +kernel
theorem subd10_2_323 : subd10_2 [2, -1, 3] = true := by decide +kernel
theorem subd10_2_324 : subd10_2 [2, -1, 4] = true := by decide +kernel
theorem subd10_2_325 : subd10_2 [2, -1, 5] = true := by decide +kernel
theorem subd10_2_326 : subd10_2 [2, -1, 6] = true := by decide +kernel
theorem subd10_2_327 : subd10_2 [2, -1, 7] = true := by decide +kernel
theorem subd10_2_328 : subd10_2 [2, 0, -8] = true := by decide +kernel
theorem subd10_2_329 : subd10_2 [2, 0, -7] = true := by decide +kernel
theorem subd10_2_330 : subd10_2 [2, 0, -6] = true := by decide +kernel
theorem subd10_2_331 : subd10_2 [2, 0, -5] = true := by decide +kernel
theorem subd10_2_332 : subd10_2 [2, 0, -4] = true := by decide +kernel
theorem subd10_2_333 : subd10_2 [2, 0, -3] = true := by decide +kernel
theorem subd10_2_334 : subd10_2 [2, 0, -2] = true := by decide +kernel
theorem subd10_2_335 : subd10_2 [2, 0, -1] = true := by decide +kernel
theorem subd10_2_336 : subd10_2 [2, 0, 0] = true := by decide +kernel
theorem subd10_2_337 : subd10_2 [2, 0, 1] = true := by decide +kernel
theorem subd10_2_338 : subd10_2 [2, 0, 2] = true := by decide +kernel
theorem subd10_2_339 : subd10_2 [2, 0, 3] = true := by decide +kernel
theorem subd10_2_340 : subd10_2 [2, 0, 4] = true := by decide +kernel
theorem subd10_2_341 : subd10_2 [2, 0, 5] = true := by decide +kernel
theorem subd10_2_342 : subd10_2 [2, 0, 6] = true := by decide +kernel
theorem subd10_2_343 : subd10_2 [2, 0, 7] = true := by decide +kernel
theorem subd10_2_344 : subd10_2 [2, 1] = true := by decide +kernel
theorem subd10_2_345 : subd10_2 [2, 2] = true := by decide +kernel
theorem subd10_2_346 : subd10_2 [3] = true := by decide +kernel
theorem sbd10_2_10 : ∀ q ∈ blkd10_2_10, subd10_2 q = true := by
  unfold blkd10_2_10
  exact List.forall_mem_cons.2 ⟨subd10_2_320, List.forall_mem_cons.2 ⟨subd10_2_321, List.forall_mem_cons.2 ⟨subd10_2_322, List.forall_mem_cons.2 ⟨subd10_2_323, List.forall_mem_cons.2 ⟨subd10_2_324, List.forall_mem_cons.2 ⟨subd10_2_325, List.forall_mem_cons.2 ⟨subd10_2_326, List.forall_mem_cons.2 ⟨subd10_2_327, List.forall_mem_cons.2 ⟨subd10_2_328, List.forall_mem_cons.2 ⟨subd10_2_329, List.forall_mem_cons.2 ⟨subd10_2_330, List.forall_mem_cons.2 ⟨subd10_2_331, List.forall_mem_cons.2 ⟨subd10_2_332, List.forall_mem_cons.2 ⟨subd10_2_333, List.forall_mem_cons.2 ⟨subd10_2_334, List.forall_mem_cons.2 ⟨subd10_2_335, List.forall_mem_cons.2 ⟨subd10_2_336, List.forall_mem_cons.2 ⟨subd10_2_337, List.forall_mem_cons.2 ⟨subd10_2_338, List.forall_mem_cons.2 ⟨subd10_2_339, List.forall_mem_cons.2 ⟨subd10_2_340, List.forall_mem_cons.2 ⟨subd10_2_341, List.forall_mem_cons.2 ⟨subd10_2_342, List.forall_mem_cons.2 ⟨subd10_2_343, List.forall_mem_cons.2 ⟨subd10_2_344, List.forall_mem_cons.2 ⟨subd10_2_345, List.forall_mem_cons.2 ⟨subd10_2_346, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-1, -2] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-1, -1] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-1, 0] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-1, 1] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [0, -2] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [0, -1] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [0, 0] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [0, 1] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [1, -2] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [1, -1] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [1, 0] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [1, 1] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-4] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-3, -5] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-3, -4] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-3, -3] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-3, -2] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-3, -1] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [-3, 0] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [-3, 1] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [-3, 2] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [-2, -6] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [-2, -5] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [-2, -4] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [-2, -3] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [-2, -2] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [-2, -1] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [-2, 0] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [-2, 1] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [-2, 2] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [-2, 3] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [-1, -6] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [-1, -5] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [-1, -4] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [-1, -3] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [-1, -2] = true := by decide +kernel
theorem subd11_0_24 : subd11_0 [-1, -1] = true := by decide +kernel
theorem subd11_0_25 : subd11_0 [-1, 0] = true := by decide +kernel
theorem subd11_0_26 : subd11_0 [-1, 1] = true := by decide +kernel
theorem subd11_0_27 : subd11_0 [-1, 2] = true := by decide +kernel
theorem subd11_0_28 : subd11_0 [-1, 3] = true := by decide +kernel
theorem subd11_0_29 : subd11_0 [-1, 4] = true := by decide +kernel
theorem subd11_0_30 : subd11_0 [0, -5] = true := by decide +kernel
theorem subd11_0_31 : subd11_0 [0, -4] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_cons.2 ⟨subd11_0_24, List.forall_mem_cons.2 ⟨subd11_0_25, List.forall_mem_cons.2 ⟨subd11_0_26, List.forall_mem_cons.2 ⟨subd11_0_27, List.forall_mem_cons.2 ⟨subd11_0_28, List.forall_mem_cons.2 ⟨subd11_0_29, List.forall_mem_cons.2 ⟨subd11_0_30, List.forall_mem_cons.2 ⟨subd11_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C141
