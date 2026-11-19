import ReflectZphi.Data.Cert5.C111.Base

namespace ReflectZphi.Data.Cert5.C111

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_3_128 : subd5_3 [-1, -1, 2] = true := by decide +kernel
theorem subd5_3_129 : subd5_3 [-1, -1, 3] = true := by decide +kernel
theorem subd5_3_130 : subd5_3 [-1, -1, 4] = true := by decide +kernel
theorem subd5_3_131 : subd5_3 [-1, -1, 5] = true := by decide +kernel
theorem subd5_3_132 : subd5_3 [-1, -1, 6] = true := by decide +kernel
theorem subd5_3_133 : subd5_3 [-1, -1, 7] = true := by decide +kernel
theorem subd5_3_134 : subd5_3 [-1, -1, 8] = true := by decide +kernel
theorem subd5_3_135 : subd5_3 [-1, 0, -8] = true := by decide +kernel
theorem subd5_3_136 : subd5_3 [-1, 0, -7] = true := by decide +kernel
theorem subd5_3_137 : subd5_3 [-1, 0, -6] = true := by decide +kernel
theorem subd5_3_138 : subd5_3 [-1, 0, -5] = true := by decide +kernel
theorem subd5_3_139 : subd5_3 [-1, 0, -4] = true := by decide +kernel
theorem subd5_3_140 : subd5_3 [-1, 0, -3] = true := by decide +kernel
theorem subd5_3_141 : subd5_3 [-1, 0, -2] = true := by decide +kernel
theorem subd5_3_142 : subd5_3 [-1, 0, -1] = true := by decide +kernel
theorem subd5_3_143 : subd5_3 [-1, 0, 0] = true := by decide +kernel
theorem subd5_3_144 : subd5_3 [-1, 0, 1] = true := by decide +kernel
theorem subd5_3_145 : subd5_3 [-1, 0, 2] = true := by decide +kernel
theorem subd5_3_146 : subd5_3 [-1, 0, 3] = true := by decide +kernel
theorem subd5_3_147 : subd5_3 [-1, 0, 4] = true := by decide +kernel
theorem subd5_3_148 : subd5_3 [-1, 0, 5] = true := by decide +kernel
theorem subd5_3_149 : subd5_3 [-1, 0, 6] = true := by decide +kernel
theorem subd5_3_150 : subd5_3 [-1, 0, 7] = true := by decide +kernel
theorem subd5_3_151 : subd5_3 [-1, 0, 8] = true := by decide +kernel
theorem subd5_3_152 : subd5_3 [-1, 1, -8] = true := by decide +kernel
theorem subd5_3_153 : subd5_3 [-1, 1, -7] = true := by decide +kernel
theorem subd5_3_154 : subd5_3 [-1, 1, -6] = true := by decide +kernel
theorem subd5_3_155 : subd5_3 [-1, 1, -5] = true := by decide +kernel
theorem subd5_3_156 : subd5_3 [-1, 1, -4] = true := by decide +kernel
theorem subd5_3_157 : subd5_3 [-1, 1, -3] = true := by decide +kernel
theorem subd5_3_158 : subd5_3 [-1, 1, -2] = true := by decide +kernel
theorem subd5_3_159 : subd5_3 [-1, 1, -1] = true := by decide +kernel
theorem sbd5_3_4 : ∀ q ∈ blkd5_3_4, subd5_3 q = true := by
  unfold blkd5_3_4
  exact List.forall_mem_cons.2 ⟨subd5_3_128, List.forall_mem_cons.2 ⟨subd5_3_129, List.forall_mem_cons.2 ⟨subd5_3_130, List.forall_mem_cons.2 ⟨subd5_3_131, List.forall_mem_cons.2 ⟨subd5_3_132, List.forall_mem_cons.2 ⟨subd5_3_133, List.forall_mem_cons.2 ⟨subd5_3_134, List.forall_mem_cons.2 ⟨subd5_3_135, List.forall_mem_cons.2 ⟨subd5_3_136, List.forall_mem_cons.2 ⟨subd5_3_137, List.forall_mem_cons.2 ⟨subd5_3_138, List.forall_mem_cons.2 ⟨subd5_3_139, List.forall_mem_cons.2 ⟨subd5_3_140, List.forall_mem_cons.2 ⟨subd5_3_141, List.forall_mem_cons.2 ⟨subd5_3_142, List.forall_mem_cons.2 ⟨subd5_3_143, List.forall_mem_cons.2 ⟨subd5_3_144, List.forall_mem_cons.2 ⟨subd5_3_145, List.forall_mem_cons.2 ⟨subd5_3_146, List.forall_mem_cons.2 ⟨subd5_3_147, List.forall_mem_cons.2 ⟨subd5_3_148, List.forall_mem_cons.2 ⟨subd5_3_149, List.forall_mem_cons.2 ⟨subd5_3_150, List.forall_mem_cons.2 ⟨subd5_3_151, List.forall_mem_cons.2 ⟨subd5_3_152, List.forall_mem_cons.2 ⟨subd5_3_153, List.forall_mem_cons.2 ⟨subd5_3_154, List.forall_mem_cons.2 ⟨subd5_3_155, List.forall_mem_cons.2 ⟨subd5_3_156, List.forall_mem_cons.2 ⟨subd5_3_157, List.forall_mem_cons.2 ⟨subd5_3_158, List.forall_mem_cons.2 ⟨subd5_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_160 : subd5_3 [-1, 1, 0] = true := by decide +kernel
theorem subd5_3_161 : subd5_3 [-1, 1, 1] = true := by decide +kernel
theorem subd5_3_162 : subd5_3 [-1, 1, 2] = true := by decide +kernel
theorem subd5_3_163 : subd5_3 [-1, 1, 3] = true := by decide +kernel
theorem subd5_3_164 : subd5_3 [-1, 1, 4] = true := by decide +kernel
theorem subd5_3_165 : subd5_3 [-1, 1, 5] = true := by decide +kernel
theorem subd5_3_166 : subd5_3 [-1, 1, 6] = true := by decide +kernel
theorem subd5_3_167 : subd5_3 [-1, 1, 7] = true := by decide +kernel
theorem subd5_3_168 : subd5_3 [-1, 1, 8] = true := by decide +kernel
theorem subd5_3_169 : subd5_3 [-1, 2, -7] = true := by decide +kernel
theorem subd5_3_170 : subd5_3 [-1, 2, -6] = true := by decide +kernel
theorem subd5_3_171 : subd5_3 [-1, 2, -5] = true := by decide +kernel
theorem subd5_3_172 : subd5_3 [-1, 2, -4] = true := by decide +kernel
theorem subd5_3_173 : subd5_3 [-1, 2, -3] = true := by decide +kernel
theorem subd5_3_174 : subd5_3 [-1, 2, -2] = true := by decide +kernel
theorem subd5_3_175 : subd5_3 [-1, 2, -1] = true := by decide +kernel
theorem subd5_3_176 : subd5_3 [-1, 2, 0] = true := by decide +kernel
theorem subd5_3_177 : subd5_3 [-1, 2, 1] = true := by decide +kernel
theorem subd5_3_178 : subd5_3 [-1, 2, 2] = true := by decide +kernel
theorem subd5_3_179 : subd5_3 [-1, 2, 3] = true := by decide +kernel
theorem subd5_3_180 : subd5_3 [-1, 2, 4] = true := by decide +kernel
theorem subd5_3_181 : subd5_3 [-1, 2, 5] = true := by decide +kernel
theorem subd5_3_182 : subd5_3 [-1, 2, 6] = true := by decide +kernel
theorem subd5_3_183 : subd5_3 [-1, 2, 7] = true := by decide +kernel
theorem subd5_3_184 : subd5_3 [-1, 2, 8] = true := by decide +kernel
theorem subd5_3_185 : subd5_3 [-1, 3] = true := by decide +kernel
theorem subd5_3_186 : subd5_3 [-1, 4] = true := by decide +kernel
theorem subd5_3_187 : subd5_3 [0, -6] = true := by decide +kernel
theorem subd5_3_188 : subd5_3 [0, -5] = true := by decide +kernel
theorem subd5_3_189 : subd5_3 [0, -4] = true := by decide +kernel
theorem subd5_3_190 : subd5_3 [0, -3, -8] = true := by decide +kernel
theorem subd5_3_191 : subd5_3 [0, -3, -7] = true := by decide +kernel
theorem sbd5_3_5 : ∀ q ∈ blkd5_3_5, subd5_3 q = true := by
  unfold blkd5_3_5
  exact List.forall_mem_cons.2 ⟨subd5_3_160, List.forall_mem_cons.2 ⟨subd5_3_161, List.forall_mem_cons.2 ⟨subd5_3_162, List.forall_mem_cons.2 ⟨subd5_3_163, List.forall_mem_cons.2 ⟨subd5_3_164, List.forall_mem_cons.2 ⟨subd5_3_165, List.forall_mem_cons.2 ⟨subd5_3_166, List.forall_mem_cons.2 ⟨subd5_3_167, List.forall_mem_cons.2 ⟨subd5_3_168, List.forall_mem_cons.2 ⟨subd5_3_169, List.forall_mem_cons.2 ⟨subd5_3_170, List.forall_mem_cons.2 ⟨subd5_3_171, List.forall_mem_cons.2 ⟨subd5_3_172, List.forall_mem_cons.2 ⟨subd5_3_173, List.forall_mem_cons.2 ⟨subd5_3_174, List.forall_mem_cons.2 ⟨subd5_3_175, List.forall_mem_cons.2 ⟨subd5_3_176, List.forall_mem_cons.2 ⟨subd5_3_177, List.forall_mem_cons.2 ⟨subd5_3_178, List.forall_mem_cons.2 ⟨subd5_3_179, List.forall_mem_cons.2 ⟨subd5_3_180, List.forall_mem_cons.2 ⟨subd5_3_181, List.forall_mem_cons.2 ⟨subd5_3_182, List.forall_mem_cons.2 ⟨subd5_3_183, List.forall_mem_cons.2 ⟨subd5_3_184, List.forall_mem_cons.2 ⟨subd5_3_185, List.forall_mem_cons.2 ⟨subd5_3_186, List.forall_mem_cons.2 ⟨subd5_3_187, List.forall_mem_cons.2 ⟨subd5_3_188, List.forall_mem_cons.2 ⟨subd5_3_189, List.forall_mem_cons.2 ⟨subd5_3_190, List.forall_mem_cons.2 ⟨subd5_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_192 : subd5_3 [0, -3, -6] = true := by decide +kernel
theorem subd5_3_193 : subd5_3 [0, -3, -5] = true := by decide +kernel
theorem subd5_3_194 : subd5_3 [0, -3, -4] = true := by decide +kernel
theorem subd5_3_195 : subd5_3 [0, -3, -3] = true := by decide +kernel
theorem subd5_3_196 : subd5_3 [0, -3, -2] = true := by decide +kernel
theorem subd5_3_197 : subd5_3 [0, -3, -1] = true := by decide +kernel
theorem subd5_3_198 : subd5_3 [0, -3, 0] = true := by decide +kernel
theorem subd5_3_199 : subd5_3 [0, -3, 1] = true := by decide +kernel
theorem subd5_3_200 : subd5_3 [0, -3, 2] = true := by decide +kernel
theorem subd5_3_201 : subd5_3 [0, -3, 3] = true := by decide +kernel
theorem subd5_3_202 : subd5_3 [0, -3, 4] = true := by decide +kernel
theorem subd5_3_203 : subd5_3 [0, -3, 5] = true := by decide +kernel
theorem subd5_3_204 : subd5_3 [0, -2, -9] = true := by decide +kernel
theorem subd5_3_205 : subd5_3 [0, -2, -8] = true := by decide +kernel
theorem subd5_3_206 : subd5_3 [0, -2, -7] = true := by decide +kernel
theorem subd5_3_207 : subd5_3 [0, -2, -6] = true := by decide +kernel
theorem subd5_3_208 : subd5_3 [0, -2, -5] = true := by decide +kernel
theorem subd5_3_209 : subd5_3 [0, -2, -4] = true := by decide +kernel
theorem subd5_3_210 : subd5_3 [0, -2, -3] = true := by decide +kernel
theorem subd5_3_211 : subd5_3 [0, -2, -2] = true := by decide +kernel
theorem subd5_3_212 : subd5_3 [0, -2, -1] = true := by decide +kernel
theorem subd5_3_213 : subd5_3 [0, -2, 0] = true := by decide +kernel
theorem subd5_3_214 : subd5_3 [0, -2, 1] = true := by decide +kernel
theorem subd5_3_215 : subd5_3 [0, -2, 2] = true := by decide +kernel
theorem subd5_3_216 : subd5_3 [0, -2, 3] = true := by decide +kernel
theorem subd5_3_217 : subd5_3 [0, -2, 4] = true := by decide +kernel
theorem subd5_3_218 : subd5_3 [0, -2, 5] = true := by decide +kernel
theorem subd5_3_219 : subd5_3 [0, -2, 6] = true := by decide +kernel
theorem subd5_3_220 : subd5_3 [0, -2, 7] = true := by decide +kernel
theorem subd5_3_221 : subd5_3 [0, -1, -9] = true := by decide +kernel
theorem subd5_3_222 : subd5_3 [0, -1, -8] = true := by decide +kernel
theorem subd5_3_223 : subd5_3 [0, -1, -7] = true := by decide +kernel
theorem sbd5_3_6 : ∀ q ∈ blkd5_3_6, subd5_3 q = true := by
  unfold blkd5_3_6
  exact List.forall_mem_cons.2 ⟨subd5_3_192, List.forall_mem_cons.2 ⟨subd5_3_193, List.forall_mem_cons.2 ⟨subd5_3_194, List.forall_mem_cons.2 ⟨subd5_3_195, List.forall_mem_cons.2 ⟨subd5_3_196, List.forall_mem_cons.2 ⟨subd5_3_197, List.forall_mem_cons.2 ⟨subd5_3_198, List.forall_mem_cons.2 ⟨subd5_3_199, List.forall_mem_cons.2 ⟨subd5_3_200, List.forall_mem_cons.2 ⟨subd5_3_201, List.forall_mem_cons.2 ⟨subd5_3_202, List.forall_mem_cons.2 ⟨subd5_3_203, List.forall_mem_cons.2 ⟨subd5_3_204, List.forall_mem_cons.2 ⟨subd5_3_205, List.forall_mem_cons.2 ⟨subd5_3_206, List.forall_mem_cons.2 ⟨subd5_3_207, List.forall_mem_cons.2 ⟨subd5_3_208, List.forall_mem_cons.2 ⟨subd5_3_209, List.forall_mem_cons.2 ⟨subd5_3_210, List.forall_mem_cons.2 ⟨subd5_3_211, List.forall_mem_cons.2 ⟨subd5_3_212, List.forall_mem_cons.2 ⟨subd5_3_213, List.forall_mem_cons.2 ⟨subd5_3_214, List.forall_mem_cons.2 ⟨subd5_3_215, List.forall_mem_cons.2 ⟨subd5_3_216, List.forall_mem_cons.2 ⟨subd5_3_217, List.forall_mem_cons.2 ⟨subd5_3_218, List.forall_mem_cons.2 ⟨subd5_3_219, List.forall_mem_cons.2 ⟨subd5_3_220, List.forall_mem_cons.2 ⟨subd5_3_221, List.forall_mem_cons.2 ⟨subd5_3_222, List.forall_mem_cons.2 ⟨subd5_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_224 : subd5_3 [0, -1, -6] = true := by decide +kernel
theorem subd5_3_225 : subd5_3 [0, -1, -5] = true := by decide +kernel
theorem subd5_3_226 : subd5_3 [0, -1, -4] = true := by decide +kernel
theorem subd5_3_227 : subd5_3 [0, -1, -3] = true := by decide +kernel
theorem subd5_3_228 : subd5_3 [0, -1, -2] = true := by decide +kernel
theorem subd5_3_229 : subd5_3 [0, -1, -1] = true := by decide +kernel
theorem subd5_3_230 : subd5_3 [0, -1, 0] = true := by decide +kernel
theorem subd5_3_231 : subd5_3 [0, -1, 1] = true := by decide +kernel
theorem subd5_3_232 : subd5_3 [0, -1, 2] = true := by decide +kernel
theorem subd5_3_233 : subd5_3 [0, -1, 3] = true := by decide +kernel
theorem subd5_3_234 : subd5_3 [0, -1, 4] = true := by decide +kernel
theorem subd5_3_235 : subd5_3 [0, -1, 5] = true := by decide +kernel
theorem subd5_3_236 : subd5_3 [0, -1, 6] = true := by decide +kernel
theorem subd5_3_237 : subd5_3 [0, -1, 7] = true := by decide +kernel
theorem subd5_3_238 : subd5_3 [0, -1, 8] = true := by decide +kernel
theorem subd5_3_239 : subd5_3 [0, 0, -9] = true := by decide +kernel
theorem subd5_3_240 : subd5_3 [0, 0, -8] = true := by decide +kernel
theorem subd5_3_241 : subd5_3 [0, 0, -7] = true := by decide +kernel
theorem subd5_3_242 : subd5_3 [0, 0, -6] = true := by decide +kernel
theorem subd5_3_243 : subd5_3 [0, 0, -5] = true := by decide +kernel
theorem subd5_3_244 : subd5_3 [0, 0, -4] = true := by decide +kernel
theorem subd5_3_245 : subd5_3 [0, 0, -3] = true := by decide +kernel
theorem subd5_3_246 : subd5_3 [0, 0, -2] = true := by decide +kernel
theorem subd5_3_247 : subd5_3 [0, 0, -1] = true := by decide +kernel
theorem subd5_3_248 : subd5_3 [0, 0, 0] = true := by decide +kernel
theorem subd5_3_249 : subd5_3 [0, 0, 1] = true := by decide +kernel
theorem subd5_3_250 : subd5_3 [0, 0, 2] = true := by decide +kernel
theorem subd5_3_251 : subd5_3 [0, 0, 3] = true := by decide +kernel
theorem subd5_3_252 : subd5_3 [0, 0, 4] = true := by decide +kernel
theorem subd5_3_253 : subd5_3 [0, 0, 5] = true := by decide +kernel
theorem subd5_3_254 : subd5_3 [0, 0, 6] = true := by decide +kernel
theorem subd5_3_255 : subd5_3 [0, 0, 7] = true := by decide +kernel
theorem sbd5_3_7 : ∀ q ∈ blkd5_3_7, subd5_3 q = true := by
  unfold blkd5_3_7
  exact List.forall_mem_cons.2 ⟨subd5_3_224, List.forall_mem_cons.2 ⟨subd5_3_225, List.forall_mem_cons.2 ⟨subd5_3_226, List.forall_mem_cons.2 ⟨subd5_3_227, List.forall_mem_cons.2 ⟨subd5_3_228, List.forall_mem_cons.2 ⟨subd5_3_229, List.forall_mem_cons.2 ⟨subd5_3_230, List.forall_mem_cons.2 ⟨subd5_3_231, List.forall_mem_cons.2 ⟨subd5_3_232, List.forall_mem_cons.2 ⟨subd5_3_233, List.forall_mem_cons.2 ⟨subd5_3_234, List.forall_mem_cons.2 ⟨subd5_3_235, List.forall_mem_cons.2 ⟨subd5_3_236, List.forall_mem_cons.2 ⟨subd5_3_237, List.forall_mem_cons.2 ⟨subd5_3_238, List.forall_mem_cons.2 ⟨subd5_3_239, List.forall_mem_cons.2 ⟨subd5_3_240, List.forall_mem_cons.2 ⟨subd5_3_241, List.forall_mem_cons.2 ⟨subd5_3_242, List.forall_mem_cons.2 ⟨subd5_3_243, List.forall_mem_cons.2 ⟨subd5_3_244, List.forall_mem_cons.2 ⟨subd5_3_245, List.forall_mem_cons.2 ⟨subd5_3_246, List.forall_mem_cons.2 ⟨subd5_3_247, List.forall_mem_cons.2 ⟨subd5_3_248, List.forall_mem_cons.2 ⟨subd5_3_249, List.forall_mem_cons.2 ⟨subd5_3_250, List.forall_mem_cons.2 ⟨subd5_3_251, List.forall_mem_cons.2 ⟨subd5_3_252, List.forall_mem_cons.2 ⟨subd5_3_253, List.forall_mem_cons.2 ⟨subd5_3_254, List.forall_mem_cons.2 ⟨subd5_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_256 : subd5_3 [0, 0, 8] = true := by decide +kernel
theorem subd5_3_257 : subd5_3 [0, 1, -9] = true := by decide +kernel
theorem subd5_3_258 : subd5_3 [0, 1, -8] = true := by decide +kernel
theorem subd5_3_259 : subd5_3 [0, 1, -7] = true := by decide +kernel
theorem subd5_3_260 : subd5_3 [0, 1, -6] = true := by decide +kernel
theorem subd5_3_261 : subd5_3 [0, 1, -5] = true := by decide +kernel
theorem subd5_3_262 : subd5_3 [0, 1, -4] = true := by decide +kernel
theorem subd5_3_263 : subd5_3 [0, 1, -3] = true := by decide +kernel
theorem subd5_3_264 : subd5_3 [0, 1, -2] = true := by decide +kernel
theorem subd5_3_265 : subd5_3 [0, 1, -1] = true := by decide +kernel
theorem subd5_3_266 : subd5_3 [0, 1, 0] = true := by decide +kernel
theorem subd5_3_267 : subd5_3 [0, 1, 1] = true := by decide +kernel
theorem subd5_3_268 : subd5_3 [0, 1, 2] = true := by decide +kernel
theorem subd5_3_269 : subd5_3 [0, 1, 3] = true := by decide +kernel
theorem subd5_3_270 : subd5_3 [0, 1, 4] = true := by decide +kernel
theorem subd5_3_271 : subd5_3 [0, 1, 5] = true := by decide +kernel
theorem subd5_3_272 : subd5_3 [0, 1, 6] = true := by decide +kernel
theorem subd5_3_273 : subd5_3 [0, 1, 7] = true := by decide +kernel
theorem subd5_3_274 : subd5_3 [0, 1, 8] = true := by decide +kernel
theorem subd5_3_275 : subd5_3 [0, 2, -8] = true := by decide +kernel
theorem subd5_3_276 : subd5_3 [0, 2, -7] = true := by decide +kernel
theorem subd5_3_277 : subd5_3 [0, 2, -6] = true := by decide +kernel
theorem subd5_3_278 : subd5_3 [0, 2, -5] = true := by decide +kernel
theorem subd5_3_279 : subd5_3 [0, 2, -4] = true := by decide +kernel
theorem subd5_3_280 : subd5_3 [0, 2, -3] = true := by decide +kernel
theorem subd5_3_281 : subd5_3 [0, 2, -2] = true := by decide +kernel
theorem subd5_3_282 : subd5_3 [0, 2, -1] = true := by decide +kernel
theorem subd5_3_283 : subd5_3 [0, 2, 0] = true := by decide +kernel
theorem subd5_3_284 : subd5_3 [0, 2, 1] = true := by decide +kernel
theorem subd5_3_285 : subd5_3 [0, 2, 2] = true := by decide +kernel
theorem subd5_3_286 : subd5_3 [0, 2, 3] = true := by decide +kernel
theorem subd5_3_287 : subd5_3 [0, 2, 4] = true := by decide +kernel
theorem sbd5_3_8 : ∀ q ∈ blkd5_3_8, subd5_3 q = true := by
  unfold blkd5_3_8
  exact List.forall_mem_cons.2 ⟨subd5_3_256, List.forall_mem_cons.2 ⟨subd5_3_257, List.forall_mem_cons.2 ⟨subd5_3_258, List.forall_mem_cons.2 ⟨subd5_3_259, List.forall_mem_cons.2 ⟨subd5_3_260, List.forall_mem_cons.2 ⟨subd5_3_261, List.forall_mem_cons.2 ⟨subd5_3_262, List.forall_mem_cons.2 ⟨subd5_3_263, List.forall_mem_cons.2 ⟨subd5_3_264, List.forall_mem_cons.2 ⟨subd5_3_265, List.forall_mem_cons.2 ⟨subd5_3_266, List.forall_mem_cons.2 ⟨subd5_3_267, List.forall_mem_cons.2 ⟨subd5_3_268, List.forall_mem_cons.2 ⟨subd5_3_269, List.forall_mem_cons.2 ⟨subd5_3_270, List.forall_mem_cons.2 ⟨subd5_3_271, List.forall_mem_cons.2 ⟨subd5_3_272, List.forall_mem_cons.2 ⟨subd5_3_273, List.forall_mem_cons.2 ⟨subd5_3_274, List.forall_mem_cons.2 ⟨subd5_3_275, List.forall_mem_cons.2 ⟨subd5_3_276, List.forall_mem_cons.2 ⟨subd5_3_277, List.forall_mem_cons.2 ⟨subd5_3_278, List.forall_mem_cons.2 ⟨subd5_3_279, List.forall_mem_cons.2 ⟨subd5_3_280, List.forall_mem_cons.2 ⟨subd5_3_281, List.forall_mem_cons.2 ⟨subd5_3_282, List.forall_mem_cons.2 ⟨subd5_3_283, List.forall_mem_cons.2 ⟨subd5_3_284, List.forall_mem_cons.2 ⟨subd5_3_285, List.forall_mem_cons.2 ⟨subd5_3_286, List.forall_mem_cons.2 ⟨subd5_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_288 : subd5_3 [0, 2, 5] = true := by decide +kernel
theorem subd5_3_289 : subd5_3 [0, 2, 6] = true := by decide +kernel
theorem subd5_3_290 : subd5_3 [0, 2, 7] = true := by decide +kernel
theorem subd5_3_291 : subd5_3 [0, 2, 8] = true := by decide +kernel
theorem subd5_3_292 : subd5_3 [0, 3, -6] = true := by decide +kernel
theorem subd5_3_293 : subd5_3 [0, 3, -5] = true := by decide +kernel
theorem subd5_3_294 : subd5_3 [0, 3, -4] = true := by decide +kernel
theorem subd5_3_295 : subd5_3 [0, 3, -3] = true := by decide +kernel
theorem subd5_3_296 : subd5_3 [0, 3, -2] = true := by decide +kernel
theorem subd5_3_297 : subd5_3 [0, 3, -1] = true := by decide +kernel
theorem subd5_3_298 : subd5_3 [0, 3, 0] = true := by decide +kernel
theorem subd5_3_299 : subd5_3 [0, 3, 1] = true := by decide +kernel
theorem subd5_3_300 : subd5_3 [0, 3, 2] = true := by decide +kernel
theorem subd5_3_301 : subd5_3 [0, 3, 3] = true := by decide +kernel
theorem subd5_3_302 : subd5_3 [0, 3, 4] = true := by decide +kernel
theorem subd5_3_303 : subd5_3 [0, 3, 5] = true := by decide +kernel
theorem subd5_3_304 : subd5_3 [0, 3, 6] = true := by decide +kernel
theorem subd5_3_305 : subd5_3 [0, 3, 7] = true := by decide +kernel
theorem subd5_3_306 : subd5_3 [0, 4] = true := by decide +kernel
theorem subd5_3_307 : subd5_3 [0, 5] = true := by decide +kernel
theorem subd5_3_308 : subd5_3 [1, -5] = true := by decide +kernel
theorem subd5_3_309 : subd5_3 [1, -4] = true := by decide +kernel
theorem subd5_3_310 : subd5_3 [1, -3] = true := by decide +kernel
theorem subd5_3_311 : subd5_3 [1, -2, -9] = true := by decide +kernel
theorem subd5_3_312 : subd5_3 [1, -2, -8] = true := by decide +kernel
theorem subd5_3_313 : subd5_3 [1, -2, -7] = true := by decide +kernel
theorem subd5_3_314 : subd5_3 [1, -2, -6] = true := by decide +kernel
theorem subd5_3_315 : subd5_3 [1, -2, -5] = true := by decide +kernel
theorem subd5_3_316 : subd5_3 [1, -2, -4] = true := by decide +kernel
theorem subd5_3_317 : subd5_3 [1, -2, -3] = true := by decide +kernel
theorem subd5_3_318 : subd5_3 [1, -2, -2] = true := by decide +kernel
theorem subd5_3_319 : subd5_3 [1, -2, -1] = true := by decide +kernel
theorem sbd5_3_9 : ∀ q ∈ blkd5_3_9, subd5_3 q = true := by
  unfold blkd5_3_9
  exact List.forall_mem_cons.2 ⟨subd5_3_288, List.forall_mem_cons.2 ⟨subd5_3_289, List.forall_mem_cons.2 ⟨subd5_3_290, List.forall_mem_cons.2 ⟨subd5_3_291, List.forall_mem_cons.2 ⟨subd5_3_292, List.forall_mem_cons.2 ⟨subd5_3_293, List.forall_mem_cons.2 ⟨subd5_3_294, List.forall_mem_cons.2 ⟨subd5_3_295, List.forall_mem_cons.2 ⟨subd5_3_296, List.forall_mem_cons.2 ⟨subd5_3_297, List.forall_mem_cons.2 ⟨subd5_3_298, List.forall_mem_cons.2 ⟨subd5_3_299, List.forall_mem_cons.2 ⟨subd5_3_300, List.forall_mem_cons.2 ⟨subd5_3_301, List.forall_mem_cons.2 ⟨subd5_3_302, List.forall_mem_cons.2 ⟨subd5_3_303, List.forall_mem_cons.2 ⟨subd5_3_304, List.forall_mem_cons.2 ⟨subd5_3_305, List.forall_mem_cons.2 ⟨subd5_3_306, List.forall_mem_cons.2 ⟨subd5_3_307, List.forall_mem_cons.2 ⟨subd5_3_308, List.forall_mem_cons.2 ⟨subd5_3_309, List.forall_mem_cons.2 ⟨subd5_3_310, List.forall_mem_cons.2 ⟨subd5_3_311, List.forall_mem_cons.2 ⟨subd5_3_312, List.forall_mem_cons.2 ⟨subd5_3_313, List.forall_mem_cons.2 ⟨subd5_3_314, List.forall_mem_cons.2 ⟨subd5_3_315, List.forall_mem_cons.2 ⟨subd5_3_316, List.forall_mem_cons.2 ⟨subd5_3_317, List.forall_mem_cons.2 ⟨subd5_3_318, List.forall_mem_cons.2 ⟨subd5_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_320 : subd5_3 [1, -2, 0] = true := by decide +kernel
theorem subd5_3_321 : subd5_3 [1, -2, 1] = true := by decide +kernel
theorem subd5_3_322 : subd5_3 [1, -2, 2] = true := by decide +kernel
theorem subd5_3_323 : subd5_3 [1, -2, 3] = true := by decide +kernel
theorem subd5_3_324 : subd5_3 [1, -2, 4] = true := by decide +kernel
theorem subd5_3_325 : subd5_3 [1, -2, 5] = true := by decide +kernel
theorem subd5_3_326 : subd5_3 [1, -2, 6] = true := by decide +kernel
theorem subd5_3_327 : subd5_3 [1, -1, -9] = true := by decide +kernel
theorem subd5_3_328 : subd5_3 [1, -1, -8] = true := by decide +kernel
theorem subd5_3_329 : subd5_3 [1, -1, -7] = true := by decide +kernel
theorem subd5_3_330 : subd5_3 [1, -1, -6] = true := by decide +kernel
theorem subd5_3_331 : subd5_3 [1, -1, -5] = true := by decide +kernel
theorem subd5_3_332 : subd5_3 [1, -1, -4] = true := by decide +kernel
theorem subd5_3_333 : subd5_3 [1, -1, -3] = true := by decide +kernel
theorem subd5_3_334 : subd5_3 [1, -1, -2] = true := by decide +kernel
theorem subd5_3_335 : subd5_3 [1, -1, -1] = true := by decide +kernel
theorem subd5_3_336 : subd5_3 [1, -1, 0] = true := by decide +kernel
theorem subd5_3_337 : subd5_3 [1, -1, 1] = true := by decide +kernel
theorem subd5_3_338 : subd5_3 [1, -1, 2] = true := by decide +kernel
theorem subd5_3_339 : subd5_3 [1, -1, 3] = true := by decide +kernel
theorem subd5_3_340 : subd5_3 [1, -1, 4] = true := by decide +kernel
theorem subd5_3_341 : subd5_3 [1, -1, 5] = true := by decide +kernel
theorem subd5_3_342 : subd5_3 [1, -1, 6] = true := by decide +kernel
theorem subd5_3_343 : subd5_3 [1, -1, 7] = true := by decide +kernel
theorem subd5_3_344 : subd5_3 [1, 0, -9] = true := by decide +kernel
theorem subd5_3_345 : subd5_3 [1, 0, -8] = true := by decide +kernel
theorem subd5_3_346 : subd5_3 [1, 0, -7] = true := by decide +kernel
theorem subd5_3_347 : subd5_3 [1, 0, -6] = true := by decide +kernel
theorem subd5_3_348 : subd5_3 [1, 0, -5] = true := by decide +kernel
theorem subd5_3_349 : subd5_3 [1, 0, -4] = true := by decide +kernel
theorem subd5_3_350 : subd5_3 [1, 0, -3] = true := by decide +kernel
theorem subd5_3_351 : subd5_3 [1, 0, -2] = true := by decide +kernel
theorem sbd5_3_10 : ∀ q ∈ blkd5_3_10, subd5_3 q = true := by
  unfold blkd5_3_10
  exact List.forall_mem_cons.2 ⟨subd5_3_320, List.forall_mem_cons.2 ⟨subd5_3_321, List.forall_mem_cons.2 ⟨subd5_3_322, List.forall_mem_cons.2 ⟨subd5_3_323, List.forall_mem_cons.2 ⟨subd5_3_324, List.forall_mem_cons.2 ⟨subd5_3_325, List.forall_mem_cons.2 ⟨subd5_3_326, List.forall_mem_cons.2 ⟨subd5_3_327, List.forall_mem_cons.2 ⟨subd5_3_328, List.forall_mem_cons.2 ⟨subd5_3_329, List.forall_mem_cons.2 ⟨subd5_3_330, List.forall_mem_cons.2 ⟨subd5_3_331, List.forall_mem_cons.2 ⟨subd5_3_332, List.forall_mem_cons.2 ⟨subd5_3_333, List.forall_mem_cons.2 ⟨subd5_3_334, List.forall_mem_cons.2 ⟨subd5_3_335, List.forall_mem_cons.2 ⟨subd5_3_336, List.forall_mem_cons.2 ⟨subd5_3_337, List.forall_mem_cons.2 ⟨subd5_3_338, List.forall_mem_cons.2 ⟨subd5_3_339, List.forall_mem_cons.2 ⟨subd5_3_340, List.forall_mem_cons.2 ⟨subd5_3_341, List.forall_mem_cons.2 ⟨subd5_3_342, List.forall_mem_cons.2 ⟨subd5_3_343, List.forall_mem_cons.2 ⟨subd5_3_344, List.forall_mem_cons.2 ⟨subd5_3_345, List.forall_mem_cons.2 ⟨subd5_3_346, List.forall_mem_cons.2 ⟨subd5_3_347, List.forall_mem_cons.2 ⟨subd5_3_348, List.forall_mem_cons.2 ⟨subd5_3_349, List.forall_mem_cons.2 ⟨subd5_3_350, List.forall_mem_cons.2 ⟨subd5_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_352 : subd5_3 [1, 0, -1] = true := by decide +kernel
theorem subd5_3_353 : subd5_3 [1, 0, 0] = true := by decide +kernel
theorem subd5_3_354 : subd5_3 [1, 0, 1] = true := by decide +kernel
theorem subd5_3_355 : subd5_3 [1, 0, 2] = true := by decide +kernel
theorem subd5_3_356 : subd5_3 [1, 0, 3] = true := by decide +kernel
theorem subd5_3_357 : subd5_3 [1, 0, 4] = true := by decide +kernel
theorem subd5_3_358 : subd5_3 [1, 0, 5] = true := by decide +kernel
theorem subd5_3_359 : subd5_3 [1, 0, 6] = true := by decide +kernel
theorem subd5_3_360 : subd5_3 [1, 0, 7] = true := by decide +kernel
theorem subd5_3_361 : subd5_3 [1, 1, -9] = true := by decide +kernel
theorem subd5_3_362 : subd5_3 [1, 1, -8] = true := by decide +kernel
theorem subd5_3_363 : subd5_3 [1, 1, -7] = true := by decide +kernel
theorem subd5_3_364 : subd5_3 [1, 1, -6] = true := by decide +kernel
theorem subd5_3_365 : subd5_3 [1, 1, -5] = true := by decide +kernel
theorem subd5_3_366 : subd5_3 [1, 1, -4] = true := by decide +kernel
theorem subd5_3_367 : subd5_3 [1, 1, -3] = true := by decide +kernel
theorem subd5_3_368 : subd5_3 [1, 1, -2] = true := by decide +kernel
theorem subd5_3_369 : subd5_3 [1, 1, -1] = true := by decide +kernel
theorem subd5_3_370 : subd5_3 [1, 1, 0] = true := by decide +kernel
theorem subd5_3_371 : subd5_3 [1, 1, 1] = true := by decide +kernel
theorem subd5_3_372 : subd5_3 [1, 1, 2] = true := by decide +kernel
theorem subd5_3_373 : subd5_3 [1, 1, 3] = true := by decide +kernel
theorem subd5_3_374 : subd5_3 [1, 1, 4] = true := by decide +kernel
theorem subd5_3_375 : subd5_3 [1, 1, 5] = true := by decide +kernel
theorem subd5_3_376 : subd5_3 [1, 1, 6] = true := by decide +kernel
theorem subd5_3_377 : subd5_3 [1, 1, 7] = true := by decide +kernel
theorem subd5_3_378 : subd5_3 [1, 1, 8] = true := by decide +kernel
theorem subd5_3_379 : subd5_3 [1, 2, -8] = true := by decide +kernel
theorem subd5_3_380 : subd5_3 [1, 2, -7] = true := by decide +kernel
theorem subd5_3_381 : subd5_3 [1, 2, -6] = true := by decide +kernel
theorem subd5_3_382 : subd5_3 [1, 2, -5] = true := by decide +kernel
theorem subd5_3_383 : subd5_3 [1, 2, -4] = true := by decide +kernel
theorem sbd5_3_11 : ∀ q ∈ blkd5_3_11, subd5_3 q = true := by
  unfold blkd5_3_11
  exact List.forall_mem_cons.2 ⟨subd5_3_352, List.forall_mem_cons.2 ⟨subd5_3_353, List.forall_mem_cons.2 ⟨subd5_3_354, List.forall_mem_cons.2 ⟨subd5_3_355, List.forall_mem_cons.2 ⟨subd5_3_356, List.forall_mem_cons.2 ⟨subd5_3_357, List.forall_mem_cons.2 ⟨subd5_3_358, List.forall_mem_cons.2 ⟨subd5_3_359, List.forall_mem_cons.2 ⟨subd5_3_360, List.forall_mem_cons.2 ⟨subd5_3_361, List.forall_mem_cons.2 ⟨subd5_3_362, List.forall_mem_cons.2 ⟨subd5_3_363, List.forall_mem_cons.2 ⟨subd5_3_364, List.forall_mem_cons.2 ⟨subd5_3_365, List.forall_mem_cons.2 ⟨subd5_3_366, List.forall_mem_cons.2 ⟨subd5_3_367, List.forall_mem_cons.2 ⟨subd5_3_368, List.forall_mem_cons.2 ⟨subd5_3_369, List.forall_mem_cons.2 ⟨subd5_3_370, List.forall_mem_cons.2 ⟨subd5_3_371, List.forall_mem_cons.2 ⟨subd5_3_372, List.forall_mem_cons.2 ⟨subd5_3_373, List.forall_mem_cons.2 ⟨subd5_3_374, List.forall_mem_cons.2 ⟨subd5_3_375, List.forall_mem_cons.2 ⟨subd5_3_376, List.forall_mem_cons.2 ⟨subd5_3_377, List.forall_mem_cons.2 ⟨subd5_3_378, List.forall_mem_cons.2 ⟨subd5_3_379, List.forall_mem_cons.2 ⟨subd5_3_380, List.forall_mem_cons.2 ⟨subd5_3_381, List.forall_mem_cons.2 ⟨subd5_3_382, List.forall_mem_cons.2 ⟨subd5_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_384 : subd5_3 [1, 2, -3] = true := by decide +kernel
theorem subd5_3_385 : subd5_3 [1, 2, -2] = true := by decide +kernel
theorem subd5_3_386 : subd5_3 [1, 2, -1] = true := by decide +kernel
theorem subd5_3_387 : subd5_3 [1, 2, 0] = true := by decide +kernel
theorem subd5_3_388 : subd5_3 [1, 2, 1] = true := by decide +kernel
theorem subd5_3_389 : subd5_3 [1, 2, 2] = true := by decide +kernel
theorem subd5_3_390 : subd5_3 [1, 2, 3] = true := by decide +kernel
theorem subd5_3_391 : subd5_3 [1, 2, 4] = true := by decide +kernel
theorem subd5_3_392 : subd5_3 [1, 2, 5] = true := by decide +kernel
theorem subd5_3_393 : subd5_3 [1, 2, 6] = true := by decide +kernel
theorem subd5_3_394 : subd5_3 [1, 2, 7] = true := by decide +kernel
theorem subd5_3_395 : subd5_3 [1, 3, -7] = true := by decide +kernel
theorem subd5_3_396 : subd5_3 [1, 3, -6] = true := by decide +kernel
theorem subd5_3_397 : subd5_3 [1, 3, -5] = true := by decide +kernel
theorem subd5_3_398 : subd5_3 [1, 3, -4] = true := by decide +kernel
theorem subd5_3_399 : subd5_3 [1, 3, -3] = true := by decide +kernel
theorem subd5_3_400 : subd5_3 [1, 3, -2] = true := by decide +kernel
theorem subd5_3_401 : subd5_3 [1, 3, -1] = true := by decide +kernel
theorem subd5_3_402 : subd5_3 [1, 3, 0] = true := by decide +kernel
theorem subd5_3_403 : subd5_3 [1, 3, 1] = true := by decide +kernel
theorem subd5_3_404 : subd5_3 [1, 3, 2] = true := by decide +kernel
theorem subd5_3_405 : subd5_3 [1, 3, 3] = true := by decide +kernel
theorem subd5_3_406 : subd5_3 [1, 3, 4] = true := by decide +kernel
theorem subd5_3_407 : subd5_3 [1, 3, 5] = true := by decide +kernel
theorem subd5_3_408 : subd5_3 [1, 3, 6] = true := by decide +kernel
theorem subd5_3_409 : subd5_3 [1, 3, 7] = true := by decide +kernel
theorem subd5_3_410 : subd5_3 [1, 4] = true := by decide +kernel
theorem subd5_3_411 : subd5_3 [1, 5] = true := by decide +kernel
theorem subd5_3_412 : subd5_3 [2, -4] = true := by decide +kernel
theorem subd5_3_413 : subd5_3 [2, -3] = true := by decide +kernel
theorem subd5_3_414 : subd5_3 [2, -2] = true := by decide +kernel
theorem subd5_3_415 : subd5_3 [2, -1, -9] = true := by decide +kernel
theorem sbd5_3_12 : ∀ q ∈ blkd5_3_12, subd5_3 q = true := by
  unfold blkd5_3_12
  exact List.forall_mem_cons.2 ⟨subd5_3_384, List.forall_mem_cons.2 ⟨subd5_3_385, List.forall_mem_cons.2 ⟨subd5_3_386, List.forall_mem_cons.2 ⟨subd5_3_387, List.forall_mem_cons.2 ⟨subd5_3_388, List.forall_mem_cons.2 ⟨subd5_3_389, List.forall_mem_cons.2 ⟨subd5_3_390, List.forall_mem_cons.2 ⟨subd5_3_391, List.forall_mem_cons.2 ⟨subd5_3_392, List.forall_mem_cons.2 ⟨subd5_3_393, List.forall_mem_cons.2 ⟨subd5_3_394, List.forall_mem_cons.2 ⟨subd5_3_395, List.forall_mem_cons.2 ⟨subd5_3_396, List.forall_mem_cons.2 ⟨subd5_3_397, List.forall_mem_cons.2 ⟨subd5_3_398, List.forall_mem_cons.2 ⟨subd5_3_399, List.forall_mem_cons.2 ⟨subd5_3_400, List.forall_mem_cons.2 ⟨subd5_3_401, List.forall_mem_cons.2 ⟨subd5_3_402, List.forall_mem_cons.2 ⟨subd5_3_403, List.forall_mem_cons.2 ⟨subd5_3_404, List.forall_mem_cons.2 ⟨subd5_3_405, List.forall_mem_cons.2 ⟨subd5_3_406, List.forall_mem_cons.2 ⟨subd5_3_407, List.forall_mem_cons.2 ⟨subd5_3_408, List.forall_mem_cons.2 ⟨subd5_3_409, List.forall_mem_cons.2 ⟨subd5_3_410, List.forall_mem_cons.2 ⟨subd5_3_411, List.forall_mem_cons.2 ⟨subd5_3_412, List.forall_mem_cons.2 ⟨subd5_3_413, List.forall_mem_cons.2 ⟨subd5_3_414, List.forall_mem_cons.2 ⟨subd5_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_416 : subd5_3 [2, -1, -8] = true := by decide +kernel
theorem subd5_3_417 : subd5_3 [2, -1, -7] = true := by decide +kernel
theorem subd5_3_418 : subd5_3 [2, -1, -6] = true := by decide +kernel
theorem subd5_3_419 : subd5_3 [2, -1, -5] = true := by decide +kernel
theorem subd5_3_420 : subd5_3 [2, -1, -4] = true := by decide +kernel
theorem subd5_3_421 : subd5_3 [2, -1, -3] = true := by decide +kernel
theorem subd5_3_422 : subd5_3 [2, -1, -2] = true := by decide +kernel
theorem subd5_3_423 : subd5_3 [2, -1, -1] = true := by decide +kernel
theorem subd5_3_424 : subd5_3 [2, -1, 0] = true := by decide +kernel
theorem subd5_3_425 : subd5_3 [2, -1, 1] = true := by decide +kernel
theorem subd5_3_426 : subd5_3 [2, -1, 2] = true := by decide +kernel
theorem subd5_3_427 : subd5_3 [2, -1, 3] = true := by decide +kernel
theorem subd5_3_428 : subd5_3 [2, -1, 4] = true := by decide +kernel
theorem subd5_3_429 : subd5_3 [2, -1, 5] = true := by decide +kernel
theorem subd5_3_430 : subd5_3 [2, 0, -9] = true := by decide +kernel
theorem subd5_3_431 : subd5_3 [2, 0, -8] = true := by decide +kernel
theorem subd5_3_432 : subd5_3 [2, 0, -7] = true := by decide +kernel
theorem subd5_3_433 : subd5_3 [2, 0, -6] = true := by decide +kernel
theorem subd5_3_434 : subd5_3 [2, 0, -5] = true := by decide +kernel
theorem subd5_3_435 : subd5_3 [2, 0, -4] = true := by decide +kernel
theorem subd5_3_436 : subd5_3 [2, 0, -3] = true := by decide +kernel
theorem subd5_3_437 : subd5_3 [2, 0, -2] = true := by decide +kernel
theorem subd5_3_438 : subd5_3 [2, 0, -1] = true := by decide +kernel
theorem subd5_3_439 : subd5_3 [2, 0, 0] = true := by decide +kernel
theorem subd5_3_440 : subd5_3 [2, 0, 1] = true := by decide +kernel
theorem subd5_3_441 : subd5_3 [2, 0, 2] = true := by decide +kernel
theorem subd5_3_442 : subd5_3 [2, 0, 3] = true := by decide +kernel
theorem subd5_3_443 : subd5_3 [2, 0, 4] = true := by decide +kernel
theorem subd5_3_444 : subd5_3 [2, 0, 5] = true := by decide +kernel
theorem subd5_3_445 : subd5_3 [2, 0, 6] = true := by decide +kernel
theorem subd5_3_446 : subd5_3 [2, 1, -9] = true := by decide +kernel
theorem subd5_3_447 : subd5_3 [2, 1, -8] = true := by decide +kernel
theorem sbd5_3_13 : ∀ q ∈ blkd5_3_13, subd5_3 q = true := by
  unfold blkd5_3_13
  exact List.forall_mem_cons.2 ⟨subd5_3_416, List.forall_mem_cons.2 ⟨subd5_3_417, List.forall_mem_cons.2 ⟨subd5_3_418, List.forall_mem_cons.2 ⟨subd5_3_419, List.forall_mem_cons.2 ⟨subd5_3_420, List.forall_mem_cons.2 ⟨subd5_3_421, List.forall_mem_cons.2 ⟨subd5_3_422, List.forall_mem_cons.2 ⟨subd5_3_423, List.forall_mem_cons.2 ⟨subd5_3_424, List.forall_mem_cons.2 ⟨subd5_3_425, List.forall_mem_cons.2 ⟨subd5_3_426, List.forall_mem_cons.2 ⟨subd5_3_427, List.forall_mem_cons.2 ⟨subd5_3_428, List.forall_mem_cons.2 ⟨subd5_3_429, List.forall_mem_cons.2 ⟨subd5_3_430, List.forall_mem_cons.2 ⟨subd5_3_431, List.forall_mem_cons.2 ⟨subd5_3_432, List.forall_mem_cons.2 ⟨subd5_3_433, List.forall_mem_cons.2 ⟨subd5_3_434, List.forall_mem_cons.2 ⟨subd5_3_435, List.forall_mem_cons.2 ⟨subd5_3_436, List.forall_mem_cons.2 ⟨subd5_3_437, List.forall_mem_cons.2 ⟨subd5_3_438, List.forall_mem_cons.2 ⟨subd5_3_439, List.forall_mem_cons.2 ⟨subd5_3_440, List.forall_mem_cons.2 ⟨subd5_3_441, List.forall_mem_cons.2 ⟨subd5_3_442, List.forall_mem_cons.2 ⟨subd5_3_443, List.forall_mem_cons.2 ⟨subd5_3_444, List.forall_mem_cons.2 ⟨subd5_3_445, List.forall_mem_cons.2 ⟨subd5_3_446, List.forall_mem_cons.2 ⟨subd5_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_448 : subd5_3 [2, 1, -7] = true := by decide +kernel
theorem subd5_3_449 : subd5_3 [2, 1, -6] = true := by decide +kernel
theorem subd5_3_450 : subd5_3 [2, 1, -5] = true := by decide +kernel
theorem subd5_3_451 : subd5_3 [2, 1, -4] = true := by decide +kernel
theorem subd5_3_452 : subd5_3 [2, 1, -3] = true := by decide +kernel
theorem subd5_3_453 : subd5_3 [2, 1, -2] = true := by decide +kernel
theorem subd5_3_454 : subd5_3 [2, 1, -1] = true := by decide +kernel
theorem subd5_3_455 : subd5_3 [2, 1, 0] = true := by decide +kernel
theorem subd5_3_456 : subd5_3 [2, 1, 1] = true := by decide +kernel
theorem subd5_3_457 : subd5_3 [2, 1, 2] = true := by decide +kernel
theorem subd5_3_458 : subd5_3 [2, 1, 3] = true := by decide +kernel
theorem subd5_3_459 : subd5_3 [2, 1, 4] = true := by decide +kernel
theorem subd5_3_460 : subd5_3 [2, 1, 5] = true := by decide +kernel
theorem subd5_3_461 : subd5_3 [2, 1, 6] = true := by decide +kernel
theorem subd5_3_462 : subd5_3 [2, 2, -8] = true := by decide +kernel
theorem subd5_3_463 : subd5_3 [2, 2, -7] = true := by decide +kernel
theorem subd5_3_464 : subd5_3 [2, 2, -6] = true := by decide +kernel
theorem subd5_3_465 : subd5_3 [2, 2, -5] = true := by decide +kernel
theorem subd5_3_466 : subd5_3 [2, 2, -4] = true := by decide +kernel
theorem subd5_3_467 : subd5_3 [2, 2, -3] = true := by decide +kernel
theorem subd5_3_468 : subd5_3 [2, 2, -2] = true := by decide +kernel
theorem subd5_3_469 : subd5_3 [2, 2, -1] = true := by decide +kernel
theorem subd5_3_470 : subd5_3 [2, 2, 0] = true := by decide +kernel
theorem subd5_3_471 : subd5_3 [2, 2, 1] = true := by decide +kernel
theorem subd5_3_472 : subd5_3 [2, 2, 2] = true := by decide +kernel
theorem subd5_3_473 : subd5_3 [2, 2, 3] = true := by decide +kernel
theorem subd5_3_474 : subd5_3 [2, 2, 4] = true := by decide +kernel
theorem subd5_3_475 : subd5_3 [2, 2, 5] = true := by decide +kernel
theorem subd5_3_476 : subd5_3 [2, 2, 6] = true := by decide +kernel
theorem subd5_3_477 : subd5_3 [2, 3] = true := by decide +kernel
theorem subd5_3_478 : subd5_3 [2, 4] = true := by decide +kernel
theorem subd5_3_479 : subd5_3 [2, 5] = true := by decide +kernel
theorem sbd5_3_14 : ∀ q ∈ blkd5_3_14, subd5_3 q = true := by
  unfold blkd5_3_14
  exact List.forall_mem_cons.2 ⟨subd5_3_448, List.forall_mem_cons.2 ⟨subd5_3_449, List.forall_mem_cons.2 ⟨subd5_3_450, List.forall_mem_cons.2 ⟨subd5_3_451, List.forall_mem_cons.2 ⟨subd5_3_452, List.forall_mem_cons.2 ⟨subd5_3_453, List.forall_mem_cons.2 ⟨subd5_3_454, List.forall_mem_cons.2 ⟨subd5_3_455, List.forall_mem_cons.2 ⟨subd5_3_456, List.forall_mem_cons.2 ⟨subd5_3_457, List.forall_mem_cons.2 ⟨subd5_3_458, List.forall_mem_cons.2 ⟨subd5_3_459, List.forall_mem_cons.2 ⟨subd5_3_460, List.forall_mem_cons.2 ⟨subd5_3_461, List.forall_mem_cons.2 ⟨subd5_3_462, List.forall_mem_cons.2 ⟨subd5_3_463, List.forall_mem_cons.2 ⟨subd5_3_464, List.forall_mem_cons.2 ⟨subd5_3_465, List.forall_mem_cons.2 ⟨subd5_3_466, List.forall_mem_cons.2 ⟨subd5_3_467, List.forall_mem_cons.2 ⟨subd5_3_468, List.forall_mem_cons.2 ⟨subd5_3_469, List.forall_mem_cons.2 ⟨subd5_3_470, List.forall_mem_cons.2 ⟨subd5_3_471, List.forall_mem_cons.2 ⟨subd5_3_472, List.forall_mem_cons.2 ⟨subd5_3_473, List.forall_mem_cons.2 ⟨subd5_3_474, List.forall_mem_cons.2 ⟨subd5_3_475, List.forall_mem_cons.2 ⟨subd5_3_476, List.forall_mem_cons.2 ⟨subd5_3_477, List.forall_mem_cons.2 ⟨subd5_3_478, List.forall_mem_cons.2 ⟨subd5_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_480 : subd5_3 [3, -3] = true := by decide +kernel
theorem subd5_3_481 : subd5_3 [3, -2] = true := by decide +kernel
theorem subd5_3_482 : subd5_3 [3, -1] = true := by decide +kernel
theorem subd5_3_483 : subd5_3 [3, 0] = true := by decide +kernel
theorem subd5_3_484 : subd5_3 [3, 1] = true := by decide +kernel
theorem subd5_3_485 : subd5_3 [3, 2] = true := by decide +kernel
theorem subd5_3_486 : subd5_3 [3, 3] = true := by decide +kernel
theorem subd5_3_487 : subd5_3 [3, 4] = true := by decide +kernel
theorem subd5_3_488 : subd5_3 [3, 5] = true := by decide +kernel
theorem subd5_3_489 : subd5_3 [4, -1] = true := by decide +kernel
theorem subd5_3_490 : subd5_3 [4, 0] = true := by decide +kernel
theorem subd5_3_491 : subd5_3 [4, 1] = true := by decide +kernel
theorem subd5_3_492 : subd5_3 [4, 2] = true := by decide +kernel
theorem subd5_3_493 : subd5_3 [4, 3] = true := by decide +kernel
theorem subd5_3_494 : subd5_3 [4, 4] = true := by decide +kernel
theorem sbd5_3_15 : ∀ q ∈ blkd5_3_15, subd5_3 q = true := by
  unfold blkd5_3_15
  exact List.forall_mem_cons.2 ⟨subd5_3_480, List.forall_mem_cons.2 ⟨subd5_3_481, List.forall_mem_cons.2 ⟨subd5_3_482, List.forall_mem_cons.2 ⟨subd5_3_483, List.forall_mem_cons.2 ⟨subd5_3_484, List.forall_mem_cons.2 ⟨subd5_3_485, List.forall_mem_cons.2 ⟨subd5_3_486, List.forall_mem_cons.2 ⟨subd5_3_487, List.forall_mem_cons.2 ⟨subd5_3_488, List.forall_mem_cons.2 ⟨subd5_3_489, List.forall_mem_cons.2 ⟨subd5_3_490, List.forall_mem_cons.2 ⟨subd5_3_491, List.forall_mem_cons.2 ⟨subd5_3_492, List.forall_mem_cons.2 ⟨subd5_3_493, List.forall_mem_cons.2 ⟨subd5_3_494, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-3] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-2] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-1] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [0, -4] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [0, -1] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [0, 0] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [0, 3] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [1] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [2] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [3] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C111
