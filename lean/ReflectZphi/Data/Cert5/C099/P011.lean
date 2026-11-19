import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_7_128 : subd5_7 [0, -2, -4] = true := by decide +kernel
theorem subd5_7_129 : subd5_7 [0, -2, -3] = true := by decide +kernel
theorem subd5_7_130 : subd5_7 [0, -2, -2] = true := by decide +kernel
theorem subd5_7_131 : subd5_7 [0, -2, -1] = true := by decide +kernel
theorem subd5_7_132 : subd5_7 [0, -2, 0] = true := by decide +kernel
theorem subd5_7_133 : subd5_7 [0, -2, 1] = true := by decide +kernel
theorem subd5_7_134 : subd5_7 [0, -2, 2] = true := by decide +kernel
theorem subd5_7_135 : subd5_7 [0, -2, 3] = true := by decide +kernel
theorem subd5_7_136 : subd5_7 [0, -2, 4] = true := by decide +kernel
theorem subd5_7_137 : subd5_7 [0, -2, 5] = true := by decide +kernel
theorem subd5_7_138 : subd5_7 [0, -1, -7] = true := by decide +kernel
theorem subd5_7_139 : subd5_7 [0, -1, -6] = true := by decide +kernel
theorem subd5_7_140 : subd5_7 [0, -1, -5] = true := by decide +kernel
theorem subd5_7_141 : subd5_7 [0, -1, -4] = true := by decide +kernel
theorem subd5_7_142 : subd5_7 [0, -1, -3] = true := by decide +kernel
theorem subd5_7_143 : subd5_7 [0, -1, -2] = true := by decide +kernel
theorem subd5_7_144 : subd5_7 [0, -1, -1] = true := by decide +kernel
theorem subd5_7_145 : subd5_7 [0, -1, 0] = true := by decide +kernel
theorem subd5_7_146 : subd5_7 [0, -1, 1] = true := by decide +kernel
theorem subd5_7_147 : subd5_7 [0, -1, 2] = true := by decide +kernel
theorem subd5_7_148 : subd5_7 [0, -1, 3] = true := by decide +kernel
theorem subd5_7_149 : subd5_7 [0, -1, 4] = true := by decide +kernel
theorem subd5_7_150 : subd5_7 [0, -1, 5] = true := by decide +kernel
theorem subd5_7_151 : subd5_7 [0, -1, 6] = true := by decide +kernel
theorem subd5_7_152 : subd5_7 [0, 0, -7] = true := by decide +kernel
theorem subd5_7_153 : subd5_7 [0, 0, -6] = true := by decide +kernel
theorem subd5_7_154 : subd5_7 [0, 0, -5] = true := by decide +kernel
theorem subd5_7_155 : subd5_7 [0, 0, -4] = true := by decide +kernel
theorem subd5_7_156 : subd5_7 [0, 0, -3] = true := by decide +kernel
theorem subd5_7_157 : subd5_7 [0, 0, -2] = true := by decide +kernel
theorem subd5_7_158 : subd5_7 [0, 0, -1] = true := by decide +kernel
theorem subd5_7_159 : subd5_7 [0, 0, 0] = true := by decide +kernel
theorem sbd5_7_4 : ∀ q ∈ blkd5_7_4, subd5_7 q = true := by
  unfold blkd5_7_4
  exact List.forall_mem_cons.2 ⟨subd5_7_128, List.forall_mem_cons.2 ⟨subd5_7_129, List.forall_mem_cons.2 ⟨subd5_7_130, List.forall_mem_cons.2 ⟨subd5_7_131, List.forall_mem_cons.2 ⟨subd5_7_132, List.forall_mem_cons.2 ⟨subd5_7_133, List.forall_mem_cons.2 ⟨subd5_7_134, List.forall_mem_cons.2 ⟨subd5_7_135, List.forall_mem_cons.2 ⟨subd5_7_136, List.forall_mem_cons.2 ⟨subd5_7_137, List.forall_mem_cons.2 ⟨subd5_7_138, List.forall_mem_cons.2 ⟨subd5_7_139, List.forall_mem_cons.2 ⟨subd5_7_140, List.forall_mem_cons.2 ⟨subd5_7_141, List.forall_mem_cons.2 ⟨subd5_7_142, List.forall_mem_cons.2 ⟨subd5_7_143, List.forall_mem_cons.2 ⟨subd5_7_144, List.forall_mem_cons.2 ⟨subd5_7_145, List.forall_mem_cons.2 ⟨subd5_7_146, List.forall_mem_cons.2 ⟨subd5_7_147, List.forall_mem_cons.2 ⟨subd5_7_148, List.forall_mem_cons.2 ⟨subd5_7_149, List.forall_mem_cons.2 ⟨subd5_7_150, List.forall_mem_cons.2 ⟨subd5_7_151, List.forall_mem_cons.2 ⟨subd5_7_152, List.forall_mem_cons.2 ⟨subd5_7_153, List.forall_mem_cons.2 ⟨subd5_7_154, List.forall_mem_cons.2 ⟨subd5_7_155, List.forall_mem_cons.2 ⟨subd5_7_156, List.forall_mem_cons.2 ⟨subd5_7_157, List.forall_mem_cons.2 ⟨subd5_7_158, List.forall_mem_cons.2 ⟨subd5_7_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_160 : subd5_7 [0, 0, 1] = true := by decide +kernel
theorem subd5_7_161 : subd5_7 [0, 0, 2] = true := by decide +kernel
theorem subd5_7_162 : subd5_7 [0, 0, 3] = true := by decide +kernel
theorem subd5_7_163 : subd5_7 [0, 0, 4] = true := by decide +kernel
theorem subd5_7_164 : subd5_7 [0, 0, 5] = true := by decide +kernel
theorem subd5_7_165 : subd5_7 [0, 0, 6] = true := by decide +kernel
theorem subd5_7_166 : subd5_7 [0, 1, -7] = true := by decide +kernel
theorem subd5_7_167 : subd5_7 [0, 1, -6] = true := by decide +kernel
theorem subd5_7_168 : subd5_7 [0, 1, -5] = true := by decide +kernel
theorem subd5_7_169 : subd5_7 [0, 1, -4] = true := by decide +kernel
theorem subd5_7_170 : subd5_7 [0, 1, -3] = true := by decide +kernel
theorem subd5_7_171 : subd5_7 [0, 1, -2] = true := by decide +kernel
theorem subd5_7_172 : subd5_7 [0, 1, -1] = true := by decide +kernel
theorem subd5_7_173 : subd5_7 [0, 1, 0] = true := by decide +kernel
theorem subd5_7_174 : subd5_7 [0, 1, 1] = true := by decide +kernel
theorem subd5_7_175 : subd5_7 [0, 1, 2] = true := by decide +kernel
theorem subd5_7_176 : subd5_7 [0, 1, 3] = true := by decide +kernel
theorem subd5_7_177 : subd5_7 [0, 1, 4] = true := by decide +kernel
theorem subd5_7_178 : subd5_7 [0, 1, 5] = true := by decide +kernel
theorem subd5_7_179 : subd5_7 [0, 1, 6] = true := by decide +kernel
theorem subd5_7_180 : subd5_7 [0, 2, -6] = true := by decide +kernel
theorem subd5_7_181 : subd5_7 [0, 2, -5] = true := by decide +kernel
theorem subd5_7_182 : subd5_7 [0, 2, -4] = true := by decide +kernel
theorem subd5_7_183 : subd5_7 [0, 2, -3] = true := by decide +kernel
theorem subd5_7_184 : subd5_7 [0, 2, -2] = true := by decide +kernel
theorem subd5_7_185 : subd5_7 [0, 2, -1] = true := by decide +kernel
theorem subd5_7_186 : subd5_7 [0, 2, 0] = true := by decide +kernel
theorem subd5_7_187 : subd5_7 [0, 2, 1] = true := by decide +kernel
theorem subd5_7_188 : subd5_7 [0, 2, 2] = true := by decide +kernel
theorem subd5_7_189 : subd5_7 [0, 2, 3] = true := by decide +kernel
theorem subd5_7_190 : subd5_7 [0, 2, 4] = true := by decide +kernel
theorem subd5_7_191 : subd5_7 [0, 2, 5] = true := by decide +kernel
theorem sbd5_7_5 : ∀ q ∈ blkd5_7_5, subd5_7 q = true := by
  unfold blkd5_7_5
  exact List.forall_mem_cons.2 ⟨subd5_7_160, List.forall_mem_cons.2 ⟨subd5_7_161, List.forall_mem_cons.2 ⟨subd5_7_162, List.forall_mem_cons.2 ⟨subd5_7_163, List.forall_mem_cons.2 ⟨subd5_7_164, List.forall_mem_cons.2 ⟨subd5_7_165, List.forall_mem_cons.2 ⟨subd5_7_166, List.forall_mem_cons.2 ⟨subd5_7_167, List.forall_mem_cons.2 ⟨subd5_7_168, List.forall_mem_cons.2 ⟨subd5_7_169, List.forall_mem_cons.2 ⟨subd5_7_170, List.forall_mem_cons.2 ⟨subd5_7_171, List.forall_mem_cons.2 ⟨subd5_7_172, List.forall_mem_cons.2 ⟨subd5_7_173, List.forall_mem_cons.2 ⟨subd5_7_174, List.forall_mem_cons.2 ⟨subd5_7_175, List.forall_mem_cons.2 ⟨subd5_7_176, List.forall_mem_cons.2 ⟨subd5_7_177, List.forall_mem_cons.2 ⟨subd5_7_178, List.forall_mem_cons.2 ⟨subd5_7_179, List.forall_mem_cons.2 ⟨subd5_7_180, List.forall_mem_cons.2 ⟨subd5_7_181, List.forall_mem_cons.2 ⟨subd5_7_182, List.forall_mem_cons.2 ⟨subd5_7_183, List.forall_mem_cons.2 ⟨subd5_7_184, List.forall_mem_cons.2 ⟨subd5_7_185, List.forall_mem_cons.2 ⟨subd5_7_186, List.forall_mem_cons.2 ⟨subd5_7_187, List.forall_mem_cons.2 ⟨subd5_7_188, List.forall_mem_cons.2 ⟨subd5_7_189, List.forall_mem_cons.2 ⟨subd5_7_190, List.forall_mem_cons.2 ⟨subd5_7_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_192 : subd5_7 [0, 2, 6] = true := by decide +kernel
theorem subd5_7_193 : subd5_7 [0, 3] = true := by decide +kernel
theorem subd5_7_194 : subd5_7 [0, 4] = true := by decide +kernel
theorem subd5_7_195 : subd5_7 [0, 5] = true := by decide +kernel
theorem subd5_7_196 : subd5_7 [1, -6] = true := by decide +kernel
theorem subd5_7_197 : subd5_7 [1, -5] = true := by decide +kernel
theorem subd5_7_198 : subd5_7 [1, -4] = true := by decide +kernel
theorem subd5_7_199 : subd5_7 [1, -3] = true := by decide +kernel
theorem subd5_7_200 : subd5_7 [1, -2] = true := by decide +kernel
theorem subd5_7_201 : subd5_7 [1, -1, -7] = true := by decide +kernel
theorem subd5_7_202 : subd5_7 [1, -1, -6] = true := by decide +kernel
theorem subd5_7_203 : subd5_7 [1, -1, -5] = true := by decide +kernel
theorem subd5_7_204 : subd5_7 [1, -1, -4] = true := by decide +kernel
theorem subd5_7_205 : subd5_7 [1, -1, -3] = true := by decide +kernel
theorem subd5_7_206 : subd5_7 [1, -1, -2] = true := by decide +kernel
theorem subd5_7_207 : subd5_7 [1, -1, -1] = true := by decide +kernel
theorem subd5_7_208 : subd5_7 [1, -1, 0] = true := by decide +kernel
theorem subd5_7_209 : subd5_7 [1, -1, 1] = true := by decide +kernel
theorem subd5_7_210 : subd5_7 [1, -1, 2] = true := by decide +kernel
theorem subd5_7_211 : subd5_7 [1, -1, 3] = true := by decide +kernel
theorem subd5_7_212 : subd5_7 [1, -1, 4] = true := by decide +kernel
theorem subd5_7_213 : subd5_7 [1, -1, 5] = true := by decide +kernel
theorem subd5_7_214 : subd5_7 [1, -1, 6] = true := by decide +kernel
theorem subd5_7_215 : subd5_7 [1, 0, -7] = true := by decide +kernel
theorem subd5_7_216 : subd5_7 [1, 0, -6] = true := by decide +kernel
theorem subd5_7_217 : subd5_7 [1, 0, -5] = true := by decide +kernel
theorem subd5_7_218 : subd5_7 [1, 0, -4] = true := by decide +kernel
theorem subd5_7_219 : subd5_7 [1, 0, -3] = true := by decide +kernel
theorem subd5_7_220 : subd5_7 [1, 0, -2] = true := by decide +kernel
theorem subd5_7_221 : subd5_7 [1, 0, -1] = true := by decide +kernel
theorem subd5_7_222 : subd5_7 [1, 0, 0] = true := by decide +kernel
theorem subd5_7_223 : subd5_7 [1, 0, 1] = true := by decide +kernel
theorem sbd5_7_6 : ∀ q ∈ blkd5_7_6, subd5_7 q = true := by
  unfold blkd5_7_6
  exact List.forall_mem_cons.2 ⟨subd5_7_192, List.forall_mem_cons.2 ⟨subd5_7_193, List.forall_mem_cons.2 ⟨subd5_7_194, List.forall_mem_cons.2 ⟨subd5_7_195, List.forall_mem_cons.2 ⟨subd5_7_196, List.forall_mem_cons.2 ⟨subd5_7_197, List.forall_mem_cons.2 ⟨subd5_7_198, List.forall_mem_cons.2 ⟨subd5_7_199, List.forall_mem_cons.2 ⟨subd5_7_200, List.forall_mem_cons.2 ⟨subd5_7_201, List.forall_mem_cons.2 ⟨subd5_7_202, List.forall_mem_cons.2 ⟨subd5_7_203, List.forall_mem_cons.2 ⟨subd5_7_204, List.forall_mem_cons.2 ⟨subd5_7_205, List.forall_mem_cons.2 ⟨subd5_7_206, List.forall_mem_cons.2 ⟨subd5_7_207, List.forall_mem_cons.2 ⟨subd5_7_208, List.forall_mem_cons.2 ⟨subd5_7_209, List.forall_mem_cons.2 ⟨subd5_7_210, List.forall_mem_cons.2 ⟨subd5_7_211, List.forall_mem_cons.2 ⟨subd5_7_212, List.forall_mem_cons.2 ⟨subd5_7_213, List.forall_mem_cons.2 ⟨subd5_7_214, List.forall_mem_cons.2 ⟨subd5_7_215, List.forall_mem_cons.2 ⟨subd5_7_216, List.forall_mem_cons.2 ⟨subd5_7_217, List.forall_mem_cons.2 ⟨subd5_7_218, List.forall_mem_cons.2 ⟨subd5_7_219, List.forall_mem_cons.2 ⟨subd5_7_220, List.forall_mem_cons.2 ⟨subd5_7_221, List.forall_mem_cons.2 ⟨subd5_7_222, List.forall_mem_cons.2 ⟨subd5_7_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_224 : subd5_7 [1, 0, 2] = true := by decide +kernel
theorem subd5_7_225 : subd5_7 [1, 0, 3] = true := by decide +kernel
theorem subd5_7_226 : subd5_7 [1, 0, 4] = true := by decide +kernel
theorem subd5_7_227 : subd5_7 [1, 0, 5] = true := by decide +kernel
theorem subd5_7_228 : subd5_7 [1, 0, 6] = true := by decide +kernel
theorem subd5_7_229 : subd5_7 [1, 0, 7] = true := by decide +kernel
theorem subd5_7_230 : subd5_7 [1, 1, -7] = true := by decide +kernel
theorem subd5_7_231 : subd5_7 [1, 1, -6] = true := by decide +kernel
theorem subd5_7_232 : subd5_7 [1, 1, -5] = true := by decide +kernel
theorem subd5_7_233 : subd5_7 [1, 1, -4] = true := by decide +kernel
theorem subd5_7_234 : subd5_7 [1, 1, -3] = true := by decide +kernel
theorem subd5_7_235 : subd5_7 [1, 1, -2] = true := by decide +kernel
theorem subd5_7_236 : subd5_7 [1, 1, -1] = true := by decide +kernel
theorem subd5_7_237 : subd5_7 [1, 1, 0] = true := by decide +kernel
theorem subd5_7_238 : subd5_7 [1, 1, 1] = true := by decide +kernel
theorem subd5_7_239 : subd5_7 [1, 1, 2] = true := by decide +kernel
theorem subd5_7_240 : subd5_7 [1, 1, 3] = true := by decide +kernel
theorem subd5_7_241 : subd5_7 [1, 1, 4] = true := by decide +kernel
theorem subd5_7_242 : subd5_7 [1, 1, 5] = true := by decide +kernel
theorem subd5_7_243 : subd5_7 [1, 1, 6] = true := by decide +kernel
theorem subd5_7_244 : subd5_7 [1, 1, 7] = true := by decide +kernel
theorem subd5_7_245 : subd5_7 [1, 2, -6] = true := by decide +kernel
theorem subd5_7_246 : subd5_7 [1, 2, -5] = true := by decide +kernel
theorem subd5_7_247 : subd5_7 [1, 2, -4] = true := by decide +kernel
theorem subd5_7_248 : subd5_7 [1, 2, -3] = true := by decide +kernel
theorem subd5_7_249 : subd5_7 [1, 2, -2] = true := by decide +kernel
theorem subd5_7_250 : subd5_7 [1, 2, -1] = true := by decide +kernel
theorem subd5_7_251 : subd5_7 [1, 2, 0] = true := by decide +kernel
theorem subd5_7_252 : subd5_7 [1, 2, 1] = true := by decide +kernel
theorem subd5_7_253 : subd5_7 [1, 2, 2] = true := by decide +kernel
theorem subd5_7_254 : subd5_7 [1, 2, 3] = true := by decide +kernel
theorem subd5_7_255 : subd5_7 [1, 2, 4] = true := by decide +kernel
theorem sbd5_7_7 : ∀ q ∈ blkd5_7_7, subd5_7 q = true := by
  unfold blkd5_7_7
  exact List.forall_mem_cons.2 ⟨subd5_7_224, List.forall_mem_cons.2 ⟨subd5_7_225, List.forall_mem_cons.2 ⟨subd5_7_226, List.forall_mem_cons.2 ⟨subd5_7_227, List.forall_mem_cons.2 ⟨subd5_7_228, List.forall_mem_cons.2 ⟨subd5_7_229, List.forall_mem_cons.2 ⟨subd5_7_230, List.forall_mem_cons.2 ⟨subd5_7_231, List.forall_mem_cons.2 ⟨subd5_7_232, List.forall_mem_cons.2 ⟨subd5_7_233, List.forall_mem_cons.2 ⟨subd5_7_234, List.forall_mem_cons.2 ⟨subd5_7_235, List.forall_mem_cons.2 ⟨subd5_7_236, List.forall_mem_cons.2 ⟨subd5_7_237, List.forall_mem_cons.2 ⟨subd5_7_238, List.forall_mem_cons.2 ⟨subd5_7_239, List.forall_mem_cons.2 ⟨subd5_7_240, List.forall_mem_cons.2 ⟨subd5_7_241, List.forall_mem_cons.2 ⟨subd5_7_242, List.forall_mem_cons.2 ⟨subd5_7_243, List.forall_mem_cons.2 ⟨subd5_7_244, List.forall_mem_cons.2 ⟨subd5_7_245, List.forall_mem_cons.2 ⟨subd5_7_246, List.forall_mem_cons.2 ⟨subd5_7_247, List.forall_mem_cons.2 ⟨subd5_7_248, List.forall_mem_cons.2 ⟨subd5_7_249, List.forall_mem_cons.2 ⟨subd5_7_250, List.forall_mem_cons.2 ⟨subd5_7_251, List.forall_mem_cons.2 ⟨subd5_7_252, List.forall_mem_cons.2 ⟨subd5_7_253, List.forall_mem_cons.2 ⟨subd5_7_254, List.forall_mem_cons.2 ⟨subd5_7_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_256 : subd5_7 [1, 2, 5] = true := by decide +kernel
theorem subd5_7_257 : subd5_7 [1, 2, 6] = true := by decide +kernel
theorem subd5_7_258 : subd5_7 [1, 2, 7] = true := by decide +kernel
theorem subd5_7_259 : subd5_7 [1, 3] = true := by decide +kernel
theorem subd5_7_260 : subd5_7 [1, 4] = true := by decide +kernel
theorem subd5_7_261 : subd5_7 [1, 5] = true := by decide +kernel
theorem subd5_7_262 : subd5_7 [2, -5] = true := by decide +kernel
theorem subd5_7_263 : subd5_7 [2, -4] = true := by decide +kernel
theorem subd5_7_264 : subd5_7 [2, -3] = true := by decide +kernel
theorem subd5_7_265 : subd5_7 [2, -2] = true := by decide +kernel
theorem subd5_7_266 : subd5_7 [2, -1] = true := by decide +kernel
theorem subd5_7_267 : subd5_7 [2, 0, -6] = true := by decide +kernel
theorem subd5_7_268 : subd5_7 [2, 0, -5] = true := by decide +kernel
theorem subd5_7_269 : subd5_7 [2, 0, -4] = true := by decide +kernel
theorem subd5_7_270 : subd5_7 [2, 0, -3] = true := by decide +kernel
theorem subd5_7_271 : subd5_7 [2, 0, -2] = true := by decide +kernel
theorem subd5_7_272 : subd5_7 [2, 0, -1] = true := by decide +kernel
theorem subd5_7_273 : subd5_7 [2, 0, 0] = true := by decide +kernel
theorem subd5_7_274 : subd5_7 [2, 0, 1] = true := by decide +kernel
theorem subd5_7_275 : subd5_7 [2, 0, 2] = true := by decide +kernel
theorem subd5_7_276 : subd5_7 [2, 0, 3] = true := by decide +kernel
theorem subd5_7_277 : subd5_7 [2, 0, 4] = true := by decide +kernel
theorem subd5_7_278 : subd5_7 [2, 0, 5] = true := by decide +kernel
theorem subd5_7_279 : subd5_7 [2, 0, 6] = true := by decide +kernel
theorem subd5_7_280 : subd5_7 [2, 1, -6] = true := by decide +kernel
theorem subd5_7_281 : subd5_7 [2, 1, -5] = true := by decide +kernel
theorem subd5_7_282 : subd5_7 [2, 1, -4] = true := by decide +kernel
theorem subd5_7_283 : subd5_7 [2, 1, -3] = true := by decide +kernel
theorem subd5_7_284 : subd5_7 [2, 1, -2] = true := by decide +kernel
theorem subd5_7_285 : subd5_7 [2, 1, -1] = true := by decide +kernel
theorem subd5_7_286 : subd5_7 [2, 1, 0] = true := by decide +kernel
theorem subd5_7_287 : subd5_7 [2, 1, 1] = true := by decide +kernel
theorem sbd5_7_8 : ∀ q ∈ blkd5_7_8, subd5_7 q = true := by
  unfold blkd5_7_8
  exact List.forall_mem_cons.2 ⟨subd5_7_256, List.forall_mem_cons.2 ⟨subd5_7_257, List.forall_mem_cons.2 ⟨subd5_7_258, List.forall_mem_cons.2 ⟨subd5_7_259, List.forall_mem_cons.2 ⟨subd5_7_260, List.forall_mem_cons.2 ⟨subd5_7_261, List.forall_mem_cons.2 ⟨subd5_7_262, List.forall_mem_cons.2 ⟨subd5_7_263, List.forall_mem_cons.2 ⟨subd5_7_264, List.forall_mem_cons.2 ⟨subd5_7_265, List.forall_mem_cons.2 ⟨subd5_7_266, List.forall_mem_cons.2 ⟨subd5_7_267, List.forall_mem_cons.2 ⟨subd5_7_268, List.forall_mem_cons.2 ⟨subd5_7_269, List.forall_mem_cons.2 ⟨subd5_7_270, List.forall_mem_cons.2 ⟨subd5_7_271, List.forall_mem_cons.2 ⟨subd5_7_272, List.forall_mem_cons.2 ⟨subd5_7_273, List.forall_mem_cons.2 ⟨subd5_7_274, List.forall_mem_cons.2 ⟨subd5_7_275, List.forall_mem_cons.2 ⟨subd5_7_276, List.forall_mem_cons.2 ⟨subd5_7_277, List.forall_mem_cons.2 ⟨subd5_7_278, List.forall_mem_cons.2 ⟨subd5_7_279, List.forall_mem_cons.2 ⟨subd5_7_280, List.forall_mem_cons.2 ⟨subd5_7_281, List.forall_mem_cons.2 ⟨subd5_7_282, List.forall_mem_cons.2 ⟨subd5_7_283, List.forall_mem_cons.2 ⟨subd5_7_284, List.forall_mem_cons.2 ⟨subd5_7_285, List.forall_mem_cons.2 ⟨subd5_7_286, List.forall_mem_cons.2 ⟨subd5_7_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_288 : subd5_7 [2, 1, 2] = true := by decide +kernel
theorem subd5_7_289 : subd5_7 [2, 1, 3] = true := by decide +kernel
theorem subd5_7_290 : subd5_7 [2, 1, 4] = true := by decide +kernel
theorem subd5_7_291 : subd5_7 [2, 1, 5] = true := by decide +kernel
theorem subd5_7_292 : subd5_7 [2, 1, 6] = true := by decide +kernel
theorem subd5_7_293 : subd5_7 [2, 1, 7] = true := by decide +kernel
theorem subd5_7_294 : subd5_7 [2, 2] = true := by decide +kernel
theorem subd5_7_295 : subd5_7 [2, 3] = true := by decide +kernel
theorem subd5_7_296 : subd5_7 [2, 4] = true := by decide +kernel
theorem subd5_7_297 : subd5_7 [2, 5] = true := by decide +kernel
theorem subd5_7_298 : subd5_7 [3, -4] = true := by decide +kernel
theorem subd5_7_299 : subd5_7 [3, -3] = true := by decide +kernel
theorem subd5_7_300 : subd5_7 [3, -2] = true := by decide +kernel
theorem subd5_7_301 : subd5_7 [3, -1] = true := by decide +kernel
theorem subd5_7_302 : subd5_7 [3, 0] = true := by decide +kernel
theorem subd5_7_303 : subd5_7 [3, 1] = true := by decide +kernel
theorem subd5_7_304 : subd5_7 [3, 2] = true := by decide +kernel
theorem subd5_7_305 : subd5_7 [3, 3] = true := by decide +kernel
theorem subd5_7_306 : subd5_7 [3, 4] = true := by decide +kernel
theorem subd5_7_307 : subd5_7 [3, 5] = true := by decide +kernel
theorem subd5_7_308 : subd5_7 [4, -3] = true := by decide +kernel
theorem subd5_7_309 : subd5_7 [4, -2] = true := by decide +kernel
theorem subd5_7_310 : subd5_7 [4, -1] = true := by decide +kernel
theorem subd5_7_311 : subd5_7 [4, 0] = true := by decide +kernel
theorem subd5_7_312 : subd5_7 [4, 1] = true := by decide +kernel
theorem subd5_7_313 : subd5_7 [4, 2] = true := by decide +kernel
theorem subd5_7_314 : subd5_7 [4, 3] = true := by decide +kernel
theorem subd5_7_315 : subd5_7 [4, 4] = true := by decide +kernel
theorem subd5_7_316 : subd5_7 [5] = true := by decide +kernel
theorem sbd5_7_9 : ∀ q ∈ blkd5_7_9, subd5_7 q = true := by
  unfold blkd5_7_9
  exact List.forall_mem_cons.2 ⟨subd5_7_288, List.forall_mem_cons.2 ⟨subd5_7_289, List.forall_mem_cons.2 ⟨subd5_7_290, List.forall_mem_cons.2 ⟨subd5_7_291, List.forall_mem_cons.2 ⟨subd5_7_292, List.forall_mem_cons.2 ⟨subd5_7_293, List.forall_mem_cons.2 ⟨subd5_7_294, List.forall_mem_cons.2 ⟨subd5_7_295, List.forall_mem_cons.2 ⟨subd5_7_296, List.forall_mem_cons.2 ⟨subd5_7_297, List.forall_mem_cons.2 ⟨subd5_7_298, List.forall_mem_cons.2 ⟨subd5_7_299, List.forall_mem_cons.2 ⟨subd5_7_300, List.forall_mem_cons.2 ⟨subd5_7_301, List.forall_mem_cons.2 ⟨subd5_7_302, List.forall_mem_cons.2 ⟨subd5_7_303, List.forall_mem_cons.2 ⟨subd5_7_304, List.forall_mem_cons.2 ⟨subd5_7_305, List.forall_mem_cons.2 ⟨subd5_7_306, List.forall_mem_cons.2 ⟨subd5_7_307, List.forall_mem_cons.2 ⟨subd5_7_308, List.forall_mem_cons.2 ⟨subd5_7_309, List.forall_mem_cons.2 ⟨subd5_7_310, List.forall_mem_cons.2 ⟨subd5_7_311, List.forall_mem_cons.2 ⟨subd5_7_312, List.forall_mem_cons.2 ⟨subd5_7_313, List.forall_mem_cons.2 ⟨subd5_7_314, List.forall_mem_cons.2 ⟨subd5_7_315, List.forall_mem_cons.2 ⟨subd5_7_316, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-4] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-3, -5] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-3, -4] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [-3, -3] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [-3, -2] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [-3, -1] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [-3, 0] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [-3, 1] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [-3, 2] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [-2, -5] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [-2, -4] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [-2, -3] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [-2, -2] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [-2, -1] = true := by decide +kernel
theorem subd6_0_14 : subd6_0 [-2, 0] = true := by decide +kernel
theorem subd6_0_15 : subd6_0 [-2, 1] = true := by decide +kernel
theorem subd6_0_16 : subd6_0 [-2, 2] = true := by decide +kernel
theorem subd6_0_17 : subd6_0 [-2, 3] = true := by decide +kernel
theorem subd6_0_18 : subd6_0 [-1, -5] = true := by decide +kernel
theorem subd6_0_19 : subd6_0 [-1, -4] = true := by decide +kernel
theorem subd6_0_20 : subd6_0 [-1, -3] = true := by decide +kernel
theorem subd6_0_21 : subd6_0 [-1, -2] = true := by decide +kernel
theorem subd6_0_22 : subd6_0 [-1, -1] = true := by decide +kernel
theorem subd6_0_23 : subd6_0 [-1, 0] = true := by decide +kernel
theorem subd6_0_24 : subd6_0 [-1, 1] = true := by decide +kernel
theorem subd6_0_25 : subd6_0 [-1, 2] = true := by decide +kernel
theorem subd6_0_26 : subd6_0 [-1, 3] = true := by decide +kernel
theorem subd6_0_27 : subd6_0 [0, -5] = true := by decide +kernel
theorem subd6_0_28 : subd6_0 [0, -4] = true := by decide +kernel
theorem subd6_0_29 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_30 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_31 : subd6_0 [0, -1] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_cons.2 ⟨subd6_0_14, List.forall_mem_cons.2 ⟨subd6_0_15, List.forall_mem_cons.2 ⟨subd6_0_16, List.forall_mem_cons.2 ⟨subd6_0_17, List.forall_mem_cons.2 ⟨subd6_0_18, List.forall_mem_cons.2 ⟨subd6_0_19, List.forall_mem_cons.2 ⟨subd6_0_20, List.forall_mem_cons.2 ⟨subd6_0_21, List.forall_mem_cons.2 ⟨subd6_0_22, List.forall_mem_cons.2 ⟨subd6_0_23, List.forall_mem_cons.2 ⟨subd6_0_24, List.forall_mem_cons.2 ⟨subd6_0_25, List.forall_mem_cons.2 ⟨subd6_0_26, List.forall_mem_cons.2 ⟨subd6_0_27, List.forall_mem_cons.2 ⟨subd6_0_28, List.forall_mem_cons.2 ⟨subd6_0_29, List.forall_mem_cons.2 ⟨subd6_0_30, List.forall_mem_cons.2 ⟨subd6_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_32 : subd6_0 [0, 0] = true := by decide +kernel
theorem subd6_0_33 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_34 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_35 : subd6_0 [0, 3] = true := by decide +kernel
theorem subd6_0_36 : subd6_0 [0, 4] = true := by decide +kernel
theorem subd6_0_37 : subd6_0 [1, -4] = true := by decide +kernel
theorem subd6_0_38 : subd6_0 [1, -3] = true := by decide +kernel
theorem subd6_0_39 : subd6_0 [1, -2] = true := by decide +kernel
theorem subd6_0_40 : subd6_0 [1, -1] = true := by decide +kernel
theorem subd6_0_41 : subd6_0 [1, 0] = true := by decide +kernel
theorem subd6_0_42 : subd6_0 [1, 1] = true := by decide +kernel
theorem subd6_0_43 : subd6_0 [1, 2] = true := by decide +kernel
theorem subd6_0_44 : subd6_0 [1, 3] = true := by decide +kernel
theorem subd6_0_45 : subd6_0 [1, 4] = true := by decide +kernel
theorem subd6_0_46 : subd6_0 [2, -4] = true := by decide +kernel
theorem subd6_0_47 : subd6_0 [2, -3] = true := by decide +kernel
theorem subd6_0_48 : subd6_0 [2, -2] = true := by decide +kernel
theorem subd6_0_49 : subd6_0 [2, -1] = true := by decide +kernel
theorem subd6_0_50 : subd6_0 [2, 0] = true := by decide +kernel
theorem subd6_0_51 : subd6_0 [2, 1] = true := by decide +kernel
theorem subd6_0_52 : subd6_0 [2, 2] = true := by decide +kernel
theorem subd6_0_53 : subd6_0 [2, 3] = true := by decide +kernel
theorem subd6_0_54 : subd6_0 [2, 4] = true := by decide +kernel
theorem subd6_0_55 : subd6_0 [3, -3] = true := by decide +kernel
theorem subd6_0_56 : subd6_0 [3, -2] = true := by decide +kernel
theorem subd6_0_57 : subd6_0 [3, -1] = true := by decide +kernel
theorem subd6_0_58 : subd6_0 [3, 0] = true := by decide +kernel
theorem subd6_0_59 : subd6_0 [3, 1] = true := by decide +kernel
theorem subd6_0_60 : subd6_0 [3, 2] = true := by decide +kernel
theorem subd6_0_61 : subd6_0 [3, 3] = true := by decide +kernel
theorem subd6_0_62 : subd6_0 [3, 4] = true := by decide +kernel
theorem subd6_0_63 : subd6_0 [4] = true := by decide +kernel
theorem sbd6_0_1 : ∀ q ∈ blkd6_0_1, subd6_0 q = true := by
  unfold blkd6_0_1
  exact List.forall_mem_cons.2 ⟨subd6_0_32, List.forall_mem_cons.2 ⟨subd6_0_33, List.forall_mem_cons.2 ⟨subd6_0_34, List.forall_mem_cons.2 ⟨subd6_0_35, List.forall_mem_cons.2 ⟨subd6_0_36, List.forall_mem_cons.2 ⟨subd6_0_37, List.forall_mem_cons.2 ⟨subd6_0_38, List.forall_mem_cons.2 ⟨subd6_0_39, List.forall_mem_cons.2 ⟨subd6_0_40, List.forall_mem_cons.2 ⟨subd6_0_41, List.forall_mem_cons.2 ⟨subd6_0_42, List.forall_mem_cons.2 ⟨subd6_0_43, List.forall_mem_cons.2 ⟨subd6_0_44, List.forall_mem_cons.2 ⟨subd6_0_45, List.forall_mem_cons.2 ⟨subd6_0_46, List.forall_mem_cons.2 ⟨subd6_0_47, List.forall_mem_cons.2 ⟨subd6_0_48, List.forall_mem_cons.2 ⟨subd6_0_49, List.forall_mem_cons.2 ⟨subd6_0_50, List.forall_mem_cons.2 ⟨subd6_0_51, List.forall_mem_cons.2 ⟨subd6_0_52, List.forall_mem_cons.2 ⟨subd6_0_53, List.forall_mem_cons.2 ⟨subd6_0_54, List.forall_mem_cons.2 ⟨subd6_0_55, List.forall_mem_cons.2 ⟨subd6_0_56, List.forall_mem_cons.2 ⟨subd6_0_57, List.forall_mem_cons.2 ⟨subd6_0_58, List.forall_mem_cons.2 ⟨subd6_0_59, List.forall_mem_cons.2 ⟨subd6_0_60, List.forall_mem_cons.2 ⟨subd6_0_61, List.forall_mem_cons.2 ⟨subd6_0_62, List.forall_mem_cons.2 ⟨subd6_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C099
