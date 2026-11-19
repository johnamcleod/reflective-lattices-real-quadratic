import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_2_128 : subd5_2 [-1, 1, 4] = true := by decide +kernel
theorem subd5_2_129 : subd5_2 [-1, 1, 5] = true := by decide +kernel
theorem subd5_2_130 : subd5_2 [-1, 1, 6] = true := by decide +kernel
theorem subd5_2_131 : subd5_2 [-1, 2, -8] = true := by decide +kernel
theorem subd5_2_132 : subd5_2 [-1, 2, -7] = true := by decide +kernel
theorem subd5_2_133 : subd5_2 [-1, 2, -6] = true := by decide +kernel
theorem subd5_2_134 : subd5_2 [-1, 2, -5] = true := by decide +kernel
theorem subd5_2_135 : subd5_2 [-1, 2, -4] = true := by decide +kernel
theorem subd5_2_136 : subd5_2 [-1, 2, -3] = true := by decide +kernel
theorem subd5_2_137 : subd5_2 [-1, 2, -2] = true := by decide +kernel
theorem subd5_2_138 : subd5_2 [-1, 2, -1] = true := by decide +kernel
theorem subd5_2_139 : subd5_2 [-1, 2, 0] = true := by decide +kernel
theorem subd5_2_140 : subd5_2 [-1, 2, 1] = true := by decide +kernel
theorem subd5_2_141 : subd5_2 [-1, 2, 2] = true := by decide +kernel
theorem subd5_2_142 : subd5_2 [-1, 2, 3] = true := by decide +kernel
theorem subd5_2_143 : subd5_2 [-1, 2, 4] = true := by decide +kernel
theorem subd5_2_144 : subd5_2 [-1, 2, 5] = true := by decide +kernel
theorem subd5_2_145 : subd5_2 [-1, 3] = true := by decide +kernel
theorem subd5_2_146 : subd5_2 [-1, 4] = true := by decide +kernel
theorem subd5_2_147 : subd5_2 [-1, 5] = true := by decide +kernel
theorem subd5_2_148 : subd5_2 [0, -6] = true := by decide +kernel
theorem subd5_2_149 : subd5_2 [0, -5] = true := by decide +kernel
theorem subd5_2_150 : subd5_2 [0, -4] = true := by decide +kernel
theorem subd5_2_151 : subd5_2 [0, -3] = true := by decide +kernel
theorem subd5_2_152 : subd5_2 [0, -2, -6] = true := by decide +kernel
theorem subd5_2_153 : subd5_2 [0, -2, -5] = true := by decide +kernel
theorem subd5_2_154 : subd5_2 [0, -2, -4] = true := by decide +kernel
theorem subd5_2_155 : subd5_2 [0, -2, -3] = true := by decide +kernel
theorem subd5_2_156 : subd5_2 [0, -2, -2] = true := by decide +kernel
theorem subd5_2_157 : subd5_2 [0, -2, -1] = true := by decide +kernel
theorem subd5_2_158 : subd5_2 [0, -2, 0] = true := by decide +kernel
theorem subd5_2_159 : subd5_2 [0, -2, 1] = true := by decide +kernel
theorem sbd5_2_4 : ∀ q ∈ blkd5_2_4, subd5_2 q = true := by
  unfold blkd5_2_4
  exact List.forall_mem_cons.2 ⟨subd5_2_128, List.forall_mem_cons.2 ⟨subd5_2_129, List.forall_mem_cons.2 ⟨subd5_2_130, List.forall_mem_cons.2 ⟨subd5_2_131, List.forall_mem_cons.2 ⟨subd5_2_132, List.forall_mem_cons.2 ⟨subd5_2_133, List.forall_mem_cons.2 ⟨subd5_2_134, List.forall_mem_cons.2 ⟨subd5_2_135, List.forall_mem_cons.2 ⟨subd5_2_136, List.forall_mem_cons.2 ⟨subd5_2_137, List.forall_mem_cons.2 ⟨subd5_2_138, List.forall_mem_cons.2 ⟨subd5_2_139, List.forall_mem_cons.2 ⟨subd5_2_140, List.forall_mem_cons.2 ⟨subd5_2_141, List.forall_mem_cons.2 ⟨subd5_2_142, List.forall_mem_cons.2 ⟨subd5_2_143, List.forall_mem_cons.2 ⟨subd5_2_144, List.forall_mem_cons.2 ⟨subd5_2_145, List.forall_mem_cons.2 ⟨subd5_2_146, List.forall_mem_cons.2 ⟨subd5_2_147, List.forall_mem_cons.2 ⟨subd5_2_148, List.forall_mem_cons.2 ⟨subd5_2_149, List.forall_mem_cons.2 ⟨subd5_2_150, List.forall_mem_cons.2 ⟨subd5_2_151, List.forall_mem_cons.2 ⟨subd5_2_152, List.forall_mem_cons.2 ⟨subd5_2_153, List.forall_mem_cons.2 ⟨subd5_2_154, List.forall_mem_cons.2 ⟨subd5_2_155, List.forall_mem_cons.2 ⟨subd5_2_156, List.forall_mem_cons.2 ⟨subd5_2_157, List.forall_mem_cons.2 ⟨subd5_2_158, List.forall_mem_cons.2 ⟨subd5_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_160 : subd5_2 [0, -2, 2] = true := by decide +kernel
theorem subd5_2_161 : subd5_2 [0, -2, 3] = true := by decide +kernel
theorem subd5_2_162 : subd5_2 [0, -2, 4] = true := by decide +kernel
theorem subd5_2_163 : subd5_2 [0, -2, 5] = true := by decide +kernel
theorem subd5_2_164 : subd5_2 [0, -2, 6] = true := by decide +kernel
theorem subd5_2_165 : subd5_2 [0, -2, 7] = true := by decide +kernel
theorem subd5_2_166 : subd5_2 [0, -1, -7] = true := by decide +kernel
theorem subd5_2_167 : subd5_2 [0, -1, -6] = true := by decide +kernel
theorem subd5_2_168 : subd5_2 [0, -1, -5] = true := by decide +kernel
theorem subd5_2_169 : subd5_2 [0, -1, -4] = true := by decide +kernel
theorem subd5_2_170 : subd5_2 [0, -1, -3] = true := by decide +kernel
theorem subd5_2_171 : subd5_2 [0, -1, -2] = true := by decide +kernel
theorem subd5_2_172 : subd5_2 [0, -1, -1] = true := by decide +kernel
theorem subd5_2_173 : subd5_2 [0, -1, 0] = true := by decide +kernel
theorem subd5_2_174 : subd5_2 [0, -1, 1] = true := by decide +kernel
theorem subd5_2_175 : subd5_2 [0, -1, 2] = true := by decide +kernel
theorem subd5_2_176 : subd5_2 [0, -1, 3] = true := by decide +kernel
theorem subd5_2_177 : subd5_2 [0, -1, 4] = true := by decide +kernel
theorem subd5_2_178 : subd5_2 [0, -1, 5] = true := by decide +kernel
theorem subd5_2_179 : subd5_2 [0, -1, 6] = true := by decide +kernel
theorem subd5_2_180 : subd5_2 [0, -1, 7] = true := by decide +kernel
theorem subd5_2_181 : subd5_2 [0, 0, -7] = true := by decide +kernel
theorem subd5_2_182 : subd5_2 [0, 0, -6] = true := by decide +kernel
theorem subd5_2_183 : subd5_2 [0, 0, -5] = true := by decide +kernel
theorem subd5_2_184 : subd5_2 [0, 0, -4] = true := by decide +kernel
theorem subd5_2_185 : subd5_2 [0, 0, -3] = true := by decide +kernel
theorem subd5_2_186 : subd5_2 [0, 0, -2] = true := by decide +kernel
theorem subd5_2_187 : subd5_2 [0, 0, -1] = true := by decide +kernel
theorem subd5_2_188 : subd5_2 [0, 0, 0] = true := by decide +kernel
theorem subd5_2_189 : subd5_2 [0, 0, 1] = true := by decide +kernel
theorem subd5_2_190 : subd5_2 [0, 0, 2] = true := by decide +kernel
theorem subd5_2_191 : subd5_2 [0, 0, 3] = true := by decide +kernel
theorem sbd5_2_5 : ∀ q ∈ blkd5_2_5, subd5_2 q = true := by
  unfold blkd5_2_5
  exact List.forall_mem_cons.2 ⟨subd5_2_160, List.forall_mem_cons.2 ⟨subd5_2_161, List.forall_mem_cons.2 ⟨subd5_2_162, List.forall_mem_cons.2 ⟨subd5_2_163, List.forall_mem_cons.2 ⟨subd5_2_164, List.forall_mem_cons.2 ⟨subd5_2_165, List.forall_mem_cons.2 ⟨subd5_2_166, List.forall_mem_cons.2 ⟨subd5_2_167, List.forall_mem_cons.2 ⟨subd5_2_168, List.forall_mem_cons.2 ⟨subd5_2_169, List.forall_mem_cons.2 ⟨subd5_2_170, List.forall_mem_cons.2 ⟨subd5_2_171, List.forall_mem_cons.2 ⟨subd5_2_172, List.forall_mem_cons.2 ⟨subd5_2_173, List.forall_mem_cons.2 ⟨subd5_2_174, List.forall_mem_cons.2 ⟨subd5_2_175, List.forall_mem_cons.2 ⟨subd5_2_176, List.forall_mem_cons.2 ⟨subd5_2_177, List.forall_mem_cons.2 ⟨subd5_2_178, List.forall_mem_cons.2 ⟨subd5_2_179, List.forall_mem_cons.2 ⟨subd5_2_180, List.forall_mem_cons.2 ⟨subd5_2_181, List.forall_mem_cons.2 ⟨subd5_2_182, List.forall_mem_cons.2 ⟨subd5_2_183, List.forall_mem_cons.2 ⟨subd5_2_184, List.forall_mem_cons.2 ⟨subd5_2_185, List.forall_mem_cons.2 ⟨subd5_2_186, List.forall_mem_cons.2 ⟨subd5_2_187, List.forall_mem_cons.2 ⟨subd5_2_188, List.forall_mem_cons.2 ⟨subd5_2_189, List.forall_mem_cons.2 ⟨subd5_2_190, List.forall_mem_cons.2 ⟨subd5_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_192 : subd5_2 [0, 0, 4] = true := by decide +kernel
theorem subd5_2_193 : subd5_2 [0, 0, 5] = true := by decide +kernel
theorem subd5_2_194 : subd5_2 [0, 0, 6] = true := by decide +kernel
theorem subd5_2_195 : subd5_2 [0, 1, -8] = true := by decide +kernel
theorem subd5_2_196 : subd5_2 [0, 1, -7] = true := by decide +kernel
theorem subd5_2_197 : subd5_2 [0, 1, -6] = true := by decide +kernel
theorem subd5_2_198 : subd5_2 [0, 1, -5] = true := by decide +kernel
theorem subd5_2_199 : subd5_2 [0, 1, -4] = true := by decide +kernel
theorem subd5_2_200 : subd5_2 [0, 1, -3] = true := by decide +kernel
theorem subd5_2_201 : subd5_2 [0, 1, -2] = true := by decide +kernel
theorem subd5_2_202 : subd5_2 [0, 1, -1] = true := by decide +kernel
theorem subd5_2_203 : subd5_2 [0, 1, 0] = true := by decide +kernel
theorem subd5_2_204 : subd5_2 [0, 1, 1] = true := by decide +kernel
theorem subd5_2_205 : subd5_2 [0, 1, 2] = true := by decide +kernel
theorem subd5_2_206 : subd5_2 [0, 1, 3] = true := by decide +kernel
theorem subd5_2_207 : subd5_2 [0, 1, 4] = true := by decide +kernel
theorem subd5_2_208 : subd5_2 [0, 1, 5] = true := by decide +kernel
theorem subd5_2_209 : subd5_2 [0, 1, 6] = true := by decide +kernel
theorem subd5_2_210 : subd5_2 [0, 2, -8] = true := by decide +kernel
theorem subd5_2_211 : subd5_2 [0, 2, -7] = true := by decide +kernel
theorem subd5_2_212 : subd5_2 [0, 2, -6] = true := by decide +kernel
theorem subd5_2_213 : subd5_2 [0, 2, -5] = true := by decide +kernel
theorem subd5_2_214 : subd5_2 [0, 2, -4] = true := by decide +kernel
theorem subd5_2_215 : subd5_2 [0, 2, -3] = true := by decide +kernel
theorem subd5_2_216 : subd5_2 [0, 2, -2] = true := by decide +kernel
theorem subd5_2_217 : subd5_2 [0, 2, -1] = true := by decide +kernel
theorem subd5_2_218 : subd5_2 [0, 2, 0] = true := by decide +kernel
theorem subd5_2_219 : subd5_2 [0, 2, 1] = true := by decide +kernel
theorem subd5_2_220 : subd5_2 [0, 2, 2] = true := by decide +kernel
theorem subd5_2_221 : subd5_2 [0, 2, 3] = true := by decide +kernel
theorem subd5_2_222 : subd5_2 [0, 2, 4] = true := by decide +kernel
theorem subd5_2_223 : subd5_2 [0, 2, 5] = true := by decide +kernel
theorem sbd5_2_6 : ∀ q ∈ blkd5_2_6, subd5_2 q = true := by
  unfold blkd5_2_6
  exact List.forall_mem_cons.2 ⟨subd5_2_192, List.forall_mem_cons.2 ⟨subd5_2_193, List.forall_mem_cons.2 ⟨subd5_2_194, List.forall_mem_cons.2 ⟨subd5_2_195, List.forall_mem_cons.2 ⟨subd5_2_196, List.forall_mem_cons.2 ⟨subd5_2_197, List.forall_mem_cons.2 ⟨subd5_2_198, List.forall_mem_cons.2 ⟨subd5_2_199, List.forall_mem_cons.2 ⟨subd5_2_200, List.forall_mem_cons.2 ⟨subd5_2_201, List.forall_mem_cons.2 ⟨subd5_2_202, List.forall_mem_cons.2 ⟨subd5_2_203, List.forall_mem_cons.2 ⟨subd5_2_204, List.forall_mem_cons.2 ⟨subd5_2_205, List.forall_mem_cons.2 ⟨subd5_2_206, List.forall_mem_cons.2 ⟨subd5_2_207, List.forall_mem_cons.2 ⟨subd5_2_208, List.forall_mem_cons.2 ⟨subd5_2_209, List.forall_mem_cons.2 ⟨subd5_2_210, List.forall_mem_cons.2 ⟨subd5_2_211, List.forall_mem_cons.2 ⟨subd5_2_212, List.forall_mem_cons.2 ⟨subd5_2_213, List.forall_mem_cons.2 ⟨subd5_2_214, List.forall_mem_cons.2 ⟨subd5_2_215, List.forall_mem_cons.2 ⟨subd5_2_216, List.forall_mem_cons.2 ⟨subd5_2_217, List.forall_mem_cons.2 ⟨subd5_2_218, List.forall_mem_cons.2 ⟨subd5_2_219, List.forall_mem_cons.2 ⟨subd5_2_220, List.forall_mem_cons.2 ⟨subd5_2_221, List.forall_mem_cons.2 ⟨subd5_2_222, List.forall_mem_cons.2 ⟨subd5_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_224 : subd5_2 [0, 3] = true := by decide +kernel
theorem subd5_2_225 : subd5_2 [0, 4] = true := by decide +kernel
theorem subd5_2_226 : subd5_2 [0, 5] = true := by decide +kernel
theorem subd5_2_227 : subd5_2 [1, -6] = true := by decide +kernel
theorem subd5_2_228 : subd5_2 [1, -5] = true := by decide +kernel
theorem subd5_2_229 : subd5_2 [1, -4] = true := by decide +kernel
theorem subd5_2_230 : subd5_2 [1, -3] = true := by decide +kernel
theorem subd5_2_231 : subd5_2 [1, -2, -6] = true := by decide +kernel
theorem subd5_2_232 : subd5_2 [1, -2, -5] = true := by decide +kernel
theorem subd5_2_233 : subd5_2 [1, -2, -4] = true := by decide +kernel
theorem subd5_2_234 : subd5_2 [1, -2, -3] = true := by decide +kernel
theorem subd5_2_235 : subd5_2 [1, -2, -2] = true := by decide +kernel
theorem subd5_2_236 : subd5_2 [1, -2, -1] = true := by decide +kernel
theorem subd5_2_237 : subd5_2 [1, -2, 0] = true := by decide +kernel
theorem subd5_2_238 : subd5_2 [1, -2, 1] = true := by decide +kernel
theorem subd5_2_239 : subd5_2 [1, -2, 2] = true := by decide +kernel
theorem subd5_2_240 : subd5_2 [1, -2, 3] = true := by decide +kernel
theorem subd5_2_241 : subd5_2 [1, -2, 4] = true := by decide +kernel
theorem subd5_2_242 : subd5_2 [1, -2, 5] = true := by decide +kernel
theorem subd5_2_243 : subd5_2 [1, -2, 6] = true := by decide +kernel
theorem subd5_2_244 : subd5_2 [1, -2, 7] = true := by decide +kernel
theorem subd5_2_245 : subd5_2 [1, -1, -7] = true := by decide +kernel
theorem subd5_2_246 : subd5_2 [1, -1, -6] = true := by decide +kernel
theorem subd5_2_247 : subd5_2 [1, -1, -5] = true := by decide +kernel
theorem subd5_2_248 : subd5_2 [1, -1, -4] = true := by decide +kernel
theorem subd5_2_249 : subd5_2 [1, -1, -3] = true := by decide +kernel
theorem subd5_2_250 : subd5_2 [1, -1, -2] = true := by decide +kernel
theorem subd5_2_251 : subd5_2 [1, -1, -1] = true := by decide +kernel
theorem subd5_2_252 : subd5_2 [1, -1, 0] = true := by decide +kernel
theorem subd5_2_253 : subd5_2 [1, -1, 1] = true := by decide +kernel
theorem subd5_2_254 : subd5_2 [1, -1, 2] = true := by decide +kernel
theorem subd5_2_255 : subd5_2 [1, -1, 3] = true := by decide +kernel
theorem sbd5_2_7 : ∀ q ∈ blkd5_2_7, subd5_2 q = true := by
  unfold blkd5_2_7
  exact List.forall_mem_cons.2 ⟨subd5_2_224, List.forall_mem_cons.2 ⟨subd5_2_225, List.forall_mem_cons.2 ⟨subd5_2_226, List.forall_mem_cons.2 ⟨subd5_2_227, List.forall_mem_cons.2 ⟨subd5_2_228, List.forall_mem_cons.2 ⟨subd5_2_229, List.forall_mem_cons.2 ⟨subd5_2_230, List.forall_mem_cons.2 ⟨subd5_2_231, List.forall_mem_cons.2 ⟨subd5_2_232, List.forall_mem_cons.2 ⟨subd5_2_233, List.forall_mem_cons.2 ⟨subd5_2_234, List.forall_mem_cons.2 ⟨subd5_2_235, List.forall_mem_cons.2 ⟨subd5_2_236, List.forall_mem_cons.2 ⟨subd5_2_237, List.forall_mem_cons.2 ⟨subd5_2_238, List.forall_mem_cons.2 ⟨subd5_2_239, List.forall_mem_cons.2 ⟨subd5_2_240, List.forall_mem_cons.2 ⟨subd5_2_241, List.forall_mem_cons.2 ⟨subd5_2_242, List.forall_mem_cons.2 ⟨subd5_2_243, List.forall_mem_cons.2 ⟨subd5_2_244, List.forall_mem_cons.2 ⟨subd5_2_245, List.forall_mem_cons.2 ⟨subd5_2_246, List.forall_mem_cons.2 ⟨subd5_2_247, List.forall_mem_cons.2 ⟨subd5_2_248, List.forall_mem_cons.2 ⟨subd5_2_249, List.forall_mem_cons.2 ⟨subd5_2_250, List.forall_mem_cons.2 ⟨subd5_2_251, List.forall_mem_cons.2 ⟨subd5_2_252, List.forall_mem_cons.2 ⟨subd5_2_253, List.forall_mem_cons.2 ⟨subd5_2_254, List.forall_mem_cons.2 ⟨subd5_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_256 : subd5_2 [1, -1, 4] = true := by decide +kernel
theorem subd5_2_257 : subd5_2 [1, -1, 5] = true := by decide +kernel
theorem subd5_2_258 : subd5_2 [1, -1, 6] = true := by decide +kernel
theorem subd5_2_259 : subd5_2 [1, -1, 7] = true := by decide +kernel
theorem subd5_2_260 : subd5_2 [1, 0, -7] = true := by decide +kernel
theorem subd5_2_261 : subd5_2 [1, 0, -6] = true := by decide +kernel
theorem subd5_2_262 : subd5_2 [1, 0, -5] = true := by decide +kernel
theorem subd5_2_263 : subd5_2 [1, 0, -4] = true := by decide +kernel
theorem subd5_2_264 : subd5_2 [1, 0, -3] = true := by decide +kernel
theorem subd5_2_265 : subd5_2 [1, 0, -2] = true := by decide +kernel
theorem subd5_2_266 : subd5_2 [1, 0, -1] = true := by decide +kernel
theorem subd5_2_267 : subd5_2 [1, 0, 0] = true := by decide +kernel
theorem subd5_2_268 : subd5_2 [1, 0, 1] = true := by decide +kernel
theorem subd5_2_269 : subd5_2 [1, 0, 2] = true := by decide +kernel
theorem subd5_2_270 : subd5_2 [1, 0, 3] = true := by decide +kernel
theorem subd5_2_271 : subd5_2 [1, 0, 4] = true := by decide +kernel
theorem subd5_2_272 : subd5_2 [1, 0, 5] = true := by decide +kernel
theorem subd5_2_273 : subd5_2 [1, 0, 6] = true := by decide +kernel
theorem subd5_2_274 : subd5_2 [1, 1, -8] = true := by decide +kernel
theorem subd5_2_275 : subd5_2 [1, 1, -7] = true := by decide +kernel
theorem subd5_2_276 : subd5_2 [1, 1, -6] = true := by decide +kernel
theorem subd5_2_277 : subd5_2 [1, 1, -5] = true := by decide +kernel
theorem subd5_2_278 : subd5_2 [1, 1, -4] = true := by decide +kernel
theorem subd5_2_279 : subd5_2 [1, 1, -3] = true := by decide +kernel
theorem subd5_2_280 : subd5_2 [1, 1, -2] = true := by decide +kernel
theorem subd5_2_281 : subd5_2 [1, 1, -1] = true := by decide +kernel
theorem subd5_2_282 : subd5_2 [1, 1, 0] = true := by decide +kernel
theorem subd5_2_283 : subd5_2 [1, 1, 1] = true := by decide +kernel
theorem subd5_2_284 : subd5_2 [1, 1, 2] = true := by decide +kernel
theorem subd5_2_285 : subd5_2 [1, 1, 3] = true := by decide +kernel
theorem subd5_2_286 : subd5_2 [1, 1, 4] = true := by decide +kernel
theorem subd5_2_287 : subd5_2 [1, 1, 5] = true := by decide +kernel
theorem sbd5_2_8 : ∀ q ∈ blkd5_2_8, subd5_2 q = true := by
  unfold blkd5_2_8
  exact List.forall_mem_cons.2 ⟨subd5_2_256, List.forall_mem_cons.2 ⟨subd5_2_257, List.forall_mem_cons.2 ⟨subd5_2_258, List.forall_mem_cons.2 ⟨subd5_2_259, List.forall_mem_cons.2 ⟨subd5_2_260, List.forall_mem_cons.2 ⟨subd5_2_261, List.forall_mem_cons.2 ⟨subd5_2_262, List.forall_mem_cons.2 ⟨subd5_2_263, List.forall_mem_cons.2 ⟨subd5_2_264, List.forall_mem_cons.2 ⟨subd5_2_265, List.forall_mem_cons.2 ⟨subd5_2_266, List.forall_mem_cons.2 ⟨subd5_2_267, List.forall_mem_cons.2 ⟨subd5_2_268, List.forall_mem_cons.2 ⟨subd5_2_269, List.forall_mem_cons.2 ⟨subd5_2_270, List.forall_mem_cons.2 ⟨subd5_2_271, List.forall_mem_cons.2 ⟨subd5_2_272, List.forall_mem_cons.2 ⟨subd5_2_273, List.forall_mem_cons.2 ⟨subd5_2_274, List.forall_mem_cons.2 ⟨subd5_2_275, List.forall_mem_cons.2 ⟨subd5_2_276, List.forall_mem_cons.2 ⟨subd5_2_277, List.forall_mem_cons.2 ⟨subd5_2_278, List.forall_mem_cons.2 ⟨subd5_2_279, List.forall_mem_cons.2 ⟨subd5_2_280, List.forall_mem_cons.2 ⟨subd5_2_281, List.forall_mem_cons.2 ⟨subd5_2_282, List.forall_mem_cons.2 ⟨subd5_2_283, List.forall_mem_cons.2 ⟨subd5_2_284, List.forall_mem_cons.2 ⟨subd5_2_285, List.forall_mem_cons.2 ⟨subd5_2_286, List.forall_mem_cons.2 ⟨subd5_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_288 : subd5_2 [1, 1, 6] = true := by decide +kernel
theorem subd5_2_289 : subd5_2 [1, 2, -8] = true := by decide +kernel
theorem subd5_2_290 : subd5_2 [1, 2, -7] = true := by decide +kernel
theorem subd5_2_291 : subd5_2 [1, 2, -6] = true := by decide +kernel
theorem subd5_2_292 : subd5_2 [1, 2, -5] = true := by decide +kernel
theorem subd5_2_293 : subd5_2 [1, 2, -4] = true := by decide +kernel
theorem subd5_2_294 : subd5_2 [1, 2, -3] = true := by decide +kernel
theorem subd5_2_295 : subd5_2 [1, 2, -2] = true := by decide +kernel
theorem subd5_2_296 : subd5_2 [1, 2, -1] = true := by decide +kernel
theorem subd5_2_297 : subd5_2 [1, 2, 0] = true := by decide +kernel
theorem subd5_2_298 : subd5_2 [1, 2, 1] = true := by decide +kernel
theorem subd5_2_299 : subd5_2 [1, 2, 2] = true := by decide +kernel
theorem subd5_2_300 : subd5_2 [1, 2, 3] = true := by decide +kernel
theorem subd5_2_301 : subd5_2 [1, 2, 4] = true := by decide +kernel
theorem subd5_2_302 : subd5_2 [1, 2, 5] = true := by decide +kernel
theorem subd5_2_303 : subd5_2 [1, 3] = true := by decide +kernel
theorem subd5_2_304 : subd5_2 [1, 4] = true := by decide +kernel
theorem subd5_2_305 : subd5_2 [1, 5] = true := by decide +kernel
theorem subd5_2_306 : subd5_2 [2, -6] = true := by decide +kernel
theorem subd5_2_307 : subd5_2 [2, -5] = true := by decide +kernel
theorem subd5_2_308 : subd5_2 [2, -4] = true := by decide +kernel
theorem subd5_2_309 : subd5_2 [2, -3] = true := by decide +kernel
theorem subd5_2_310 : subd5_2 [2, -2] = true := by decide +kernel
theorem subd5_2_311 : subd5_2 [2, -1, -7] = true := by decide +kernel
theorem subd5_2_312 : subd5_2 [2, -1, -6] = true := by decide +kernel
theorem subd5_2_313 : subd5_2 [2, -1, -5] = true := by decide +kernel
theorem subd5_2_314 : subd5_2 [2, -1, -4] = true := by decide +kernel
theorem subd5_2_315 : subd5_2 [2, -1, -3] = true := by decide +kernel
theorem subd5_2_316 : subd5_2 [2, -1, -2] = true := by decide +kernel
theorem subd5_2_317 : subd5_2 [2, -1, -1] = true := by decide +kernel
theorem subd5_2_318 : subd5_2 [2, -1, 0] = true := by decide +kernel
theorem subd5_2_319 : subd5_2 [2, -1, 1] = true := by decide +kernel
theorem sbd5_2_9 : ∀ q ∈ blkd5_2_9, subd5_2 q = true := by
  unfold blkd5_2_9
  exact List.forall_mem_cons.2 ⟨subd5_2_288, List.forall_mem_cons.2 ⟨subd5_2_289, List.forall_mem_cons.2 ⟨subd5_2_290, List.forall_mem_cons.2 ⟨subd5_2_291, List.forall_mem_cons.2 ⟨subd5_2_292, List.forall_mem_cons.2 ⟨subd5_2_293, List.forall_mem_cons.2 ⟨subd5_2_294, List.forall_mem_cons.2 ⟨subd5_2_295, List.forall_mem_cons.2 ⟨subd5_2_296, List.forall_mem_cons.2 ⟨subd5_2_297, List.forall_mem_cons.2 ⟨subd5_2_298, List.forall_mem_cons.2 ⟨subd5_2_299, List.forall_mem_cons.2 ⟨subd5_2_300, List.forall_mem_cons.2 ⟨subd5_2_301, List.forall_mem_cons.2 ⟨subd5_2_302, List.forall_mem_cons.2 ⟨subd5_2_303, List.forall_mem_cons.2 ⟨subd5_2_304, List.forall_mem_cons.2 ⟨subd5_2_305, List.forall_mem_cons.2 ⟨subd5_2_306, List.forall_mem_cons.2 ⟨subd5_2_307, List.forall_mem_cons.2 ⟨subd5_2_308, List.forall_mem_cons.2 ⟨subd5_2_309, List.forall_mem_cons.2 ⟨subd5_2_310, List.forall_mem_cons.2 ⟨subd5_2_311, List.forall_mem_cons.2 ⟨subd5_2_312, List.forall_mem_cons.2 ⟨subd5_2_313, List.forall_mem_cons.2 ⟨subd5_2_314, List.forall_mem_cons.2 ⟨subd5_2_315, List.forall_mem_cons.2 ⟨subd5_2_316, List.forall_mem_cons.2 ⟨subd5_2_317, List.forall_mem_cons.2 ⟨subd5_2_318, List.forall_mem_cons.2 ⟨subd5_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_320 : subd5_2 [2, -1, 2] = true := by decide +kernel
theorem subd5_2_321 : subd5_2 [2, -1, 3] = true := by decide +kernel
theorem subd5_2_322 : subd5_2 [2, -1, 4] = true := by decide +kernel
theorem subd5_2_323 : subd5_2 [2, -1, 5] = true := by decide +kernel
theorem subd5_2_324 : subd5_2 [2, -1, 6] = true := by decide +kernel
theorem subd5_2_325 : subd5_2 [2, 0, -7] = true := by decide +kernel
theorem subd5_2_326 : subd5_2 [2, 0, -6] = true := by decide +kernel
theorem subd5_2_327 : subd5_2 [2, 0, -5] = true := by decide +kernel
theorem subd5_2_328 : subd5_2 [2, 0, -4] = true := by decide +kernel
theorem subd5_2_329 : subd5_2 [2, 0, -3] = true := by decide +kernel
theorem subd5_2_330 : subd5_2 [2, 0, -2] = true := by decide +kernel
theorem subd5_2_331 : subd5_2 [2, 0, -1] = true := by decide +kernel
theorem subd5_2_332 : subd5_2 [2, 0, 0] = true := by decide +kernel
theorem subd5_2_333 : subd5_2 [2, 0, 1] = true := by decide +kernel
theorem subd5_2_334 : subd5_2 [2, 0, 2] = true := by decide +kernel
theorem subd5_2_335 : subd5_2 [2, 0, 3] = true := by decide +kernel
theorem subd5_2_336 : subd5_2 [2, 0, 4] = true := by decide +kernel
theorem subd5_2_337 : subd5_2 [2, 0, 5] = true := by decide +kernel
theorem subd5_2_338 : subd5_2 [2, 0, 6] = true := by decide +kernel
theorem subd5_2_339 : subd5_2 [2, 1, -7] = true := by decide +kernel
theorem subd5_2_340 : subd5_2 [2, 1, -6] = true := by decide +kernel
theorem subd5_2_341 : subd5_2 [2, 1, -5] = true := by decide +kernel
theorem subd5_2_342 : subd5_2 [2, 1, -4] = true := by decide +kernel
theorem subd5_2_343 : subd5_2 [2, 1, -3] = true := by decide +kernel
theorem subd5_2_344 : subd5_2 [2, 1, -2] = true := by decide +kernel
theorem subd5_2_345 : subd5_2 [2, 1, -1] = true := by decide +kernel
theorem subd5_2_346 : subd5_2 [2, 1, 0] = true := by decide +kernel
theorem subd5_2_347 : subd5_2 [2, 1, 1] = true := by decide +kernel
theorem subd5_2_348 : subd5_2 [2, 1, 2] = true := by decide +kernel
theorem subd5_2_349 : subd5_2 [2, 1, 3] = true := by decide +kernel
theorem subd5_2_350 : subd5_2 [2, 1, 4] = true := by decide +kernel
theorem subd5_2_351 : subd5_2 [2, 1, 5] = true := by decide +kernel
theorem sbd5_2_10 : ∀ q ∈ blkd5_2_10, subd5_2 q = true := by
  unfold blkd5_2_10
  exact List.forall_mem_cons.2 ⟨subd5_2_320, List.forall_mem_cons.2 ⟨subd5_2_321, List.forall_mem_cons.2 ⟨subd5_2_322, List.forall_mem_cons.2 ⟨subd5_2_323, List.forall_mem_cons.2 ⟨subd5_2_324, List.forall_mem_cons.2 ⟨subd5_2_325, List.forall_mem_cons.2 ⟨subd5_2_326, List.forall_mem_cons.2 ⟨subd5_2_327, List.forall_mem_cons.2 ⟨subd5_2_328, List.forall_mem_cons.2 ⟨subd5_2_329, List.forall_mem_cons.2 ⟨subd5_2_330, List.forall_mem_cons.2 ⟨subd5_2_331, List.forall_mem_cons.2 ⟨subd5_2_332, List.forall_mem_cons.2 ⟨subd5_2_333, List.forall_mem_cons.2 ⟨subd5_2_334, List.forall_mem_cons.2 ⟨subd5_2_335, List.forall_mem_cons.2 ⟨subd5_2_336, List.forall_mem_cons.2 ⟨subd5_2_337, List.forall_mem_cons.2 ⟨subd5_2_338, List.forall_mem_cons.2 ⟨subd5_2_339, List.forall_mem_cons.2 ⟨subd5_2_340, List.forall_mem_cons.2 ⟨subd5_2_341, List.forall_mem_cons.2 ⟨subd5_2_342, List.forall_mem_cons.2 ⟨subd5_2_343, List.forall_mem_cons.2 ⟨subd5_2_344, List.forall_mem_cons.2 ⟨subd5_2_345, List.forall_mem_cons.2 ⟨subd5_2_346, List.forall_mem_cons.2 ⟨subd5_2_347, List.forall_mem_cons.2 ⟨subd5_2_348, List.forall_mem_cons.2 ⟨subd5_2_349, List.forall_mem_cons.2 ⟨subd5_2_350, List.forall_mem_cons.2 ⟨subd5_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_352 : subd5_2 [2, 2] = true := by decide +kernel
theorem subd5_2_353 : subd5_2 [2, 3] = true := by decide +kernel
theorem subd5_2_354 : subd5_2 [2, 4] = true := by decide +kernel
theorem subd5_2_355 : subd5_2 [3, -5] = true := by decide +kernel
theorem subd5_2_356 : subd5_2 [3, -4] = true := by decide +kernel
theorem subd5_2_357 : subd5_2 [3, -3] = true := by decide +kernel
theorem subd5_2_358 : subd5_2 [3, -2] = true := by decide +kernel
theorem subd5_2_359 : subd5_2 [3, -1] = true := by decide +kernel
theorem subd5_2_360 : subd5_2 [3, 0] = true := by decide +kernel
theorem subd5_2_361 : subd5_2 [3, 1] = true := by decide +kernel
theorem subd5_2_362 : subd5_2 [3, 2] = true := by decide +kernel
theorem subd5_2_363 : subd5_2 [3, 3] = true := by decide +kernel
theorem subd5_2_364 : subd5_2 [3, 4] = true := by decide +kernel
theorem subd5_2_365 : subd5_2 [4, -5] = true := by decide +kernel
theorem subd5_2_366 : subd5_2 [4, -4] = true := by decide +kernel
theorem subd5_2_367 : subd5_2 [4, -3] = true := by decide +kernel
theorem subd5_2_368 : subd5_2 [4, -2] = true := by decide +kernel
theorem subd5_2_369 : subd5_2 [4, -1] = true := by decide +kernel
theorem subd5_2_370 : subd5_2 [4, 0] = true := by decide +kernel
theorem subd5_2_371 : subd5_2 [4, 1] = true := by decide +kernel
theorem subd5_2_372 : subd5_2 [4, 2] = true := by decide +kernel
theorem subd5_2_373 : subd5_2 [4, 3] = true := by decide +kernel
theorem subd5_2_374 : subd5_2 [5] = true := by decide +kernel
theorem sbd5_2_11 : ∀ q ∈ blkd5_2_11, subd5_2 q = true := by
  unfold blkd5_2_11
  exact List.forall_mem_cons.2 ⟨subd5_2_352, List.forall_mem_cons.2 ⟨subd5_2_353, List.forall_mem_cons.2 ⟨subd5_2_354, List.forall_mem_cons.2 ⟨subd5_2_355, List.forall_mem_cons.2 ⟨subd5_2_356, List.forall_mem_cons.2 ⟨subd5_2_357, List.forall_mem_cons.2 ⟨subd5_2_358, List.forall_mem_cons.2 ⟨subd5_2_359, List.forall_mem_cons.2 ⟨subd5_2_360, List.forall_mem_cons.2 ⟨subd5_2_361, List.forall_mem_cons.2 ⟨subd5_2_362, List.forall_mem_cons.2 ⟨subd5_2_363, List.forall_mem_cons.2 ⟨subd5_2_364, List.forall_mem_cons.2 ⟨subd5_2_365, List.forall_mem_cons.2 ⟨subd5_2_366, List.forall_mem_cons.2 ⟨subd5_2_367, List.forall_mem_cons.2 ⟨subd5_2_368, List.forall_mem_cons.2 ⟨subd5_2_369, List.forall_mem_cons.2 ⟨subd5_2_370, List.forall_mem_cons.2 ⟨subd5_2_371, List.forall_mem_cons.2 ⟨subd5_2_372, List.forall_mem_cons.2 ⟨subd5_2_373, List.forall_mem_cons.2 ⟨subd5_2_374, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
