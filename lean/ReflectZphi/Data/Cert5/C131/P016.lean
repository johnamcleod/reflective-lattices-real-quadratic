import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_0_160 : subd11_0 [-5, 1, 0] = true := by decide +kernel
theorem subd11_0_161 : subd11_0 [-5, 1, 1] = true := by decide +kernel
theorem subd11_0_162 : subd11_0 [-5, 1, 2] = true := by decide +kernel
theorem subd11_0_163 : subd11_0 [-5, 1, 3] = true := by decide +kernel
theorem subd11_0_164 : subd11_0 [-5, 1, 4] = true := by decide +kernel
theorem subd11_0_165 : subd11_0 [-5, 1, 5] = true := by decide +kernel
theorem subd11_0_166 : subd11_0 [-5, 2] = true := by decide +kernel
theorem subd11_0_167 : subd11_0 [-5, 3] = true := by decide +kernel
theorem subd11_0_168 : subd11_0 [-5, 4] = true := by decide +kernel
theorem subd11_0_169 : subd11_0 [-5, 5] = true := by decide +kernel
theorem subd11_0_170 : subd11_0 [-4, -11] = true := by decide +kernel
theorem subd11_0_171 : subd11_0 [-4, -10] = true := by decide +kernel
theorem subd11_0_172 : subd11_0 [-4, -9] = true := by decide +kernel
theorem subd11_0_173 : subd11_0 [-4, -8] = true := by decide +kernel
theorem subd11_0_174 : subd11_0 [-4, -7] = true := by decide +kernel
theorem subd11_0_175 : subd11_0 [-4, -6, -8] = true := by decide +kernel
theorem subd11_0_176 : subd11_0 [-4, -6, -7] = true := by decide +kernel
theorem subd11_0_177 : subd11_0 [-4, -6, -6] = true := by decide +kernel
theorem subd11_0_178 : subd11_0 [-4, -6, -5] = true := by decide +kernel
theorem subd11_0_179 : subd11_0 [-4, -6, -4] = true := by decide +kernel
theorem subd11_0_180 : subd11_0 [-4, -6, -3] = true := by decide +kernel
theorem subd11_0_181 : subd11_0 [-4, -6, -2] = true := by decide +kernel
theorem subd11_0_182 : subd11_0 [-4, -6, -1] = true := by decide +kernel
theorem subd11_0_183 : subd11_0 [-4, -6, 0] = true := by decide +kernel
theorem subd11_0_184 : subd11_0 [-4, -6, 1] = true := by decide +kernel
theorem subd11_0_185 : subd11_0 [-4, -6, 2] = true := by decide +kernel
theorem subd11_0_186 : subd11_0 [-4, -6, 3] = true := by decide +kernel
theorem subd11_0_187 : subd11_0 [-4, -6, 4] = true := by decide +kernel
theorem subd11_0_188 : subd11_0 [-4, -6, 5] = true := by decide +kernel
theorem subd11_0_189 : subd11_0 [-4, -5, -8] = true := by decide +kernel
theorem subd11_0_190 : subd11_0 [-4, -5, -7] = true := by decide +kernel
theorem subd11_0_191 : subd11_0 [-4, -5, -6] = true := by decide +kernel
theorem sbd11_0_5 : ∀ q ∈ blkd11_0_5, subd11_0 q = true := by
  unfold blkd11_0_5
  exact List.forall_mem_cons.2 ⟨subd11_0_160, List.forall_mem_cons.2 ⟨subd11_0_161, List.forall_mem_cons.2 ⟨subd11_0_162, List.forall_mem_cons.2 ⟨subd11_0_163, List.forall_mem_cons.2 ⟨subd11_0_164, List.forall_mem_cons.2 ⟨subd11_0_165, List.forall_mem_cons.2 ⟨subd11_0_166, List.forall_mem_cons.2 ⟨subd11_0_167, List.forall_mem_cons.2 ⟨subd11_0_168, List.forall_mem_cons.2 ⟨subd11_0_169, List.forall_mem_cons.2 ⟨subd11_0_170, List.forall_mem_cons.2 ⟨subd11_0_171, List.forall_mem_cons.2 ⟨subd11_0_172, List.forall_mem_cons.2 ⟨subd11_0_173, List.forall_mem_cons.2 ⟨subd11_0_174, List.forall_mem_cons.2 ⟨subd11_0_175, List.forall_mem_cons.2 ⟨subd11_0_176, List.forall_mem_cons.2 ⟨subd11_0_177, List.forall_mem_cons.2 ⟨subd11_0_178, List.forall_mem_cons.2 ⟨subd11_0_179, List.forall_mem_cons.2 ⟨subd11_0_180, List.forall_mem_cons.2 ⟨subd11_0_181, List.forall_mem_cons.2 ⟨subd11_0_182, List.forall_mem_cons.2 ⟨subd11_0_183, List.forall_mem_cons.2 ⟨subd11_0_184, List.forall_mem_cons.2 ⟨subd11_0_185, List.forall_mem_cons.2 ⟨subd11_0_186, List.forall_mem_cons.2 ⟨subd11_0_187, List.forall_mem_cons.2 ⟨subd11_0_188, List.forall_mem_cons.2 ⟨subd11_0_189, List.forall_mem_cons.2 ⟨subd11_0_190, List.forall_mem_cons.2 ⟨subd11_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_192 : subd11_0 [-4, -5, -5] = true := by decide +kernel
theorem subd11_0_193 : subd11_0 [-4, -5, -4] = true := by decide +kernel
theorem subd11_0_194 : subd11_0 [-4, -5, -3] = true := by decide +kernel
theorem subd11_0_195 : subd11_0 [-4, -5, -2] = true := by decide +kernel
theorem subd11_0_196 : subd11_0 [-4, -5, -1] = true := by decide +kernel
theorem subd11_0_197 : subd11_0 [-4, -5, 0] = true := by decide +kernel
theorem subd11_0_198 : subd11_0 [-4, -5, 1] = true := by decide +kernel
theorem subd11_0_199 : subd11_0 [-4, -5, 2] = true := by decide +kernel
theorem subd11_0_200 : subd11_0 [-4, -5, 3] = true := by decide +kernel
theorem subd11_0_201 : subd11_0 [-4, -5, 4] = true := by decide +kernel
theorem subd11_0_202 : subd11_0 [-4, -5, 5] = true := by decide +kernel
theorem subd11_0_203 : subd11_0 [-4, -5, 6] = true := by decide +kernel
theorem subd11_0_204 : subd11_0 [-4, -4, -9] = true := by decide +kernel
theorem subd11_0_205 : subd11_0 [-4, -4, -8] = true := by decide +kernel
theorem subd11_0_206 : subd11_0 [-4, -4, -7] = true := by decide +kernel
theorem subd11_0_207 : subd11_0 [-4, -4, -6] = true := by decide +kernel
theorem subd11_0_208 : subd11_0 [-4, -4, -5] = true := by decide +kernel
theorem subd11_0_209 : subd11_0 [-4, -4, -4] = true := by decide +kernel
theorem subd11_0_210 : subd11_0 [-4, -4, -3] = true := by decide +kernel
theorem subd11_0_211 : subd11_0 [-4, -4, -2] = true := by decide +kernel
theorem subd11_0_212 : subd11_0 [-4, -4, -1] = true := by decide +kernel
theorem subd11_0_213 : subd11_0 [-4, -4, 0] = true := by decide +kernel
theorem subd11_0_214 : subd11_0 [-4, -4, 1] = true := by decide +kernel
theorem subd11_0_215 : subd11_0 [-4, -4, 2] = true := by decide +kernel
theorem subd11_0_216 : subd11_0 [-4, -4, 3] = true := by decide +kernel
theorem subd11_0_217 : subd11_0 [-4, -4, 4] = true := by decide +kernel
theorem subd11_0_218 : subd11_0 [-4, -4, 5] = true := by decide +kernel
theorem subd11_0_219 : subd11_0 [-4, -4, 6] = true := by decide +kernel
theorem subd11_0_220 : subd11_0 [-4, -3, -9] = true := by decide +kernel
theorem subd11_0_221 : subd11_0 [-4, -3, -8] = true := by decide +kernel
theorem subd11_0_222 : subd11_0 [-4, -3, -7] = true := by decide +kernel
theorem subd11_0_223 : subd11_0 [-4, -3, -6] = true := by decide +kernel
theorem sbd11_0_6 : ∀ q ∈ blkd11_0_6, subd11_0 q = true := by
  unfold blkd11_0_6
  exact List.forall_mem_cons.2 ⟨subd11_0_192, List.forall_mem_cons.2 ⟨subd11_0_193, List.forall_mem_cons.2 ⟨subd11_0_194, List.forall_mem_cons.2 ⟨subd11_0_195, List.forall_mem_cons.2 ⟨subd11_0_196, List.forall_mem_cons.2 ⟨subd11_0_197, List.forall_mem_cons.2 ⟨subd11_0_198, List.forall_mem_cons.2 ⟨subd11_0_199, List.forall_mem_cons.2 ⟨subd11_0_200, List.forall_mem_cons.2 ⟨subd11_0_201, List.forall_mem_cons.2 ⟨subd11_0_202, List.forall_mem_cons.2 ⟨subd11_0_203, List.forall_mem_cons.2 ⟨subd11_0_204, List.forall_mem_cons.2 ⟨subd11_0_205, List.forall_mem_cons.2 ⟨subd11_0_206, List.forall_mem_cons.2 ⟨subd11_0_207, List.forall_mem_cons.2 ⟨subd11_0_208, List.forall_mem_cons.2 ⟨subd11_0_209, List.forall_mem_cons.2 ⟨subd11_0_210, List.forall_mem_cons.2 ⟨subd11_0_211, List.forall_mem_cons.2 ⟨subd11_0_212, List.forall_mem_cons.2 ⟨subd11_0_213, List.forall_mem_cons.2 ⟨subd11_0_214, List.forall_mem_cons.2 ⟨subd11_0_215, List.forall_mem_cons.2 ⟨subd11_0_216, List.forall_mem_cons.2 ⟨subd11_0_217, List.forall_mem_cons.2 ⟨subd11_0_218, List.forall_mem_cons.2 ⟨subd11_0_219, List.forall_mem_cons.2 ⟨subd11_0_220, List.forall_mem_cons.2 ⟨subd11_0_221, List.forall_mem_cons.2 ⟨subd11_0_222, List.forall_mem_cons.2 ⟨subd11_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_224 : subd11_0 [-4, -3, -5] = true := by decide +kernel
theorem subd11_0_225 : subd11_0 [-4, -3, -4] = true := by decide +kernel
theorem subd11_0_226 : subd11_0 [-4, -3, -3] = true := by decide +kernel
theorem subd11_0_227 : subd11_0 [-4, -3, -2] = true := by decide +kernel
theorem subd11_0_228 : subd11_0 [-4, -3, -1] = true := by decide +kernel
theorem subd11_0_229 : subd11_0 [-4, -3, 0] = true := by decide +kernel
theorem subd11_0_230 : subd11_0 [-4, -3, 1] = true := by decide +kernel
theorem subd11_0_231 : subd11_0 [-4, -3, 2] = true := by decide +kernel
theorem subd11_0_232 : subd11_0 [-4, -3, 3] = true := by decide +kernel
theorem subd11_0_233 : subd11_0 [-4, -3, 4] = true := by decide +kernel
theorem subd11_0_234 : subd11_0 [-4, -3, 5] = true := by decide +kernel
theorem subd11_0_235 : subd11_0 [-4, -3, 6] = true := by decide +kernel
theorem subd11_0_236 : subd11_0 [-4, -2, -9] = true := by decide +kernel
theorem subd11_0_237 : subd11_0 [-4, -2, -8] = true := by decide +kernel
theorem subd11_0_238 : subd11_0 [-4, -2, -7] = true := by decide +kernel
theorem subd11_0_239 : subd11_0 [-4, -2, -6] = true := by decide +kernel
theorem subd11_0_240 : subd11_0 [-4, -2, -5] = true := by decide +kernel
theorem subd11_0_241 : subd11_0 [-4, -2, -4] = true := by decide +kernel
theorem subd11_0_242 : subd11_0 [-4, -2, -3] = true := by decide +kernel
theorem subd11_0_243 : subd11_0 [-4, -2, -2] = true := by decide +kernel
theorem subd11_0_244 : subd11_0 [-4, -2, -1] = true := by decide +kernel
theorem subd11_0_245 : subd11_0 [-4, -2, 0] = true := by decide +kernel
theorem subd11_0_246 : subd11_0 [-4, -2, 1] = true := by decide +kernel
theorem subd11_0_247 : subd11_0 [-4, -2, 2] = true := by decide +kernel
theorem subd11_0_248 : subd11_0 [-4, -2, 3] = true := by decide +kernel
theorem subd11_0_249 : subd11_0 [-4, -2, 4] = true := by decide +kernel
theorem subd11_0_250 : subd11_0 [-4, -2, 5] = true := by decide +kernel
theorem subd11_0_251 : subd11_0 [-4, -2, 6] = true := by decide +kernel
theorem subd11_0_252 : subd11_0 [-4, -1, -9] = true := by decide +kernel
theorem subd11_0_253 : subd11_0 [-4, -1, -8] = true := by decide +kernel
theorem subd11_0_254 : subd11_0 [-4, -1, -7] = true := by decide +kernel
theorem subd11_0_255 : subd11_0 [-4, -1, -6] = true := by decide +kernel
theorem sbd11_0_7 : ∀ q ∈ blkd11_0_7, subd11_0 q = true := by
  unfold blkd11_0_7
  exact List.forall_mem_cons.2 ⟨subd11_0_224, List.forall_mem_cons.2 ⟨subd11_0_225, List.forall_mem_cons.2 ⟨subd11_0_226, List.forall_mem_cons.2 ⟨subd11_0_227, List.forall_mem_cons.2 ⟨subd11_0_228, List.forall_mem_cons.2 ⟨subd11_0_229, List.forall_mem_cons.2 ⟨subd11_0_230, List.forall_mem_cons.2 ⟨subd11_0_231, List.forall_mem_cons.2 ⟨subd11_0_232, List.forall_mem_cons.2 ⟨subd11_0_233, List.forall_mem_cons.2 ⟨subd11_0_234, List.forall_mem_cons.2 ⟨subd11_0_235, List.forall_mem_cons.2 ⟨subd11_0_236, List.forall_mem_cons.2 ⟨subd11_0_237, List.forall_mem_cons.2 ⟨subd11_0_238, List.forall_mem_cons.2 ⟨subd11_0_239, List.forall_mem_cons.2 ⟨subd11_0_240, List.forall_mem_cons.2 ⟨subd11_0_241, List.forall_mem_cons.2 ⟨subd11_0_242, List.forall_mem_cons.2 ⟨subd11_0_243, List.forall_mem_cons.2 ⟨subd11_0_244, List.forall_mem_cons.2 ⟨subd11_0_245, List.forall_mem_cons.2 ⟨subd11_0_246, List.forall_mem_cons.2 ⟨subd11_0_247, List.forall_mem_cons.2 ⟨subd11_0_248, List.forall_mem_cons.2 ⟨subd11_0_249, List.forall_mem_cons.2 ⟨subd11_0_250, List.forall_mem_cons.2 ⟨subd11_0_251, List.forall_mem_cons.2 ⟨subd11_0_252, List.forall_mem_cons.2 ⟨subd11_0_253, List.forall_mem_cons.2 ⟨subd11_0_254, List.forall_mem_cons.2 ⟨subd11_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_256 : subd11_0 [-4, -1, -5] = true := by decide +kernel
theorem subd11_0_257 : subd11_0 [-4, -1, -4] = true := by decide +kernel
theorem subd11_0_258 : subd11_0 [-4, -1, -3] = true := by decide +kernel
theorem subd11_0_259 : subd11_0 [-4, -1, -2] = true := by decide +kernel
theorem subd11_0_260 : subd11_0 [-4, -1, -1] = true := by decide +kernel
theorem subd11_0_261 : subd11_0 [-4, -1, 0] = true := by decide +kernel
theorem subd11_0_262 : subd11_0 [-4, -1, 1] = true := by decide +kernel
theorem subd11_0_263 : subd11_0 [-4, -1, 2] = true := by decide +kernel
theorem subd11_0_264 : subd11_0 [-4, -1, 3] = true := by decide +kernel
theorem subd11_0_265 : subd11_0 [-4, -1, 4] = true := by decide +kernel
theorem subd11_0_266 : subd11_0 [-4, -1, 5] = true := by decide +kernel
theorem subd11_0_267 : subd11_0 [-4, -1, 6] = true := by decide +kernel
theorem subd11_0_268 : subd11_0 [-4, 0, -9] = true := by decide +kernel
theorem subd11_0_269 : subd11_0 [-4, 0, -8] = true := by decide +kernel
theorem subd11_0_270 : subd11_0 [-4, 0, -7] = true := by decide +kernel
theorem subd11_0_271 : subd11_0 [-4, 0, -6] = true := by decide +kernel
theorem subd11_0_272 : subd11_0 [-4, 0, -5] = true := by decide +kernel
theorem subd11_0_273 : subd11_0 [-4, 0, -4] = true := by decide +kernel
theorem subd11_0_274 : subd11_0 [-4, 0, -3] = true := by decide +kernel
theorem subd11_0_275 : subd11_0 [-4, 0, -2] = true := by decide +kernel
theorem subd11_0_276 : subd11_0 [-4, 0, -1] = true := by decide +kernel
theorem subd11_0_277 : subd11_0 [-4, 0, 0] = true := by decide +kernel
theorem subd11_0_278 : subd11_0 [-4, 0, 1] = true := by decide +kernel
theorem subd11_0_279 : subd11_0 [-4, 0, 2] = true := by decide +kernel
theorem subd11_0_280 : subd11_0 [-4, 0, 3] = true := by decide +kernel
theorem subd11_0_281 : subd11_0 [-4, 0, 4] = true := by decide +kernel
theorem subd11_0_282 : subd11_0 [-4, 0, 5] = true := by decide +kernel
theorem subd11_0_283 : subd11_0 [-4, 0, 6] = true := by decide +kernel
theorem subd11_0_284 : subd11_0 [-4, 1, -9] = true := by decide +kernel
theorem subd11_0_285 : subd11_0 [-4, 1, -8] = true := by decide +kernel
theorem subd11_0_286 : subd11_0 [-4, 1, -7] = true := by decide +kernel
theorem subd11_0_287 : subd11_0 [-4, 1, -6] = true := by decide +kernel
theorem sbd11_0_8 : ∀ q ∈ blkd11_0_8, subd11_0 q = true := by
  unfold blkd11_0_8
  exact List.forall_mem_cons.2 ⟨subd11_0_256, List.forall_mem_cons.2 ⟨subd11_0_257, List.forall_mem_cons.2 ⟨subd11_0_258, List.forall_mem_cons.2 ⟨subd11_0_259, List.forall_mem_cons.2 ⟨subd11_0_260, List.forall_mem_cons.2 ⟨subd11_0_261, List.forall_mem_cons.2 ⟨subd11_0_262, List.forall_mem_cons.2 ⟨subd11_0_263, List.forall_mem_cons.2 ⟨subd11_0_264, List.forall_mem_cons.2 ⟨subd11_0_265, List.forall_mem_cons.2 ⟨subd11_0_266, List.forall_mem_cons.2 ⟨subd11_0_267, List.forall_mem_cons.2 ⟨subd11_0_268, List.forall_mem_cons.2 ⟨subd11_0_269, List.forall_mem_cons.2 ⟨subd11_0_270, List.forall_mem_cons.2 ⟨subd11_0_271, List.forall_mem_cons.2 ⟨subd11_0_272, List.forall_mem_cons.2 ⟨subd11_0_273, List.forall_mem_cons.2 ⟨subd11_0_274, List.forall_mem_cons.2 ⟨subd11_0_275, List.forall_mem_cons.2 ⟨subd11_0_276, List.forall_mem_cons.2 ⟨subd11_0_277, List.forall_mem_cons.2 ⟨subd11_0_278, List.forall_mem_cons.2 ⟨subd11_0_279, List.forall_mem_cons.2 ⟨subd11_0_280, List.forall_mem_cons.2 ⟨subd11_0_281, List.forall_mem_cons.2 ⟨subd11_0_282, List.forall_mem_cons.2 ⟨subd11_0_283, List.forall_mem_cons.2 ⟨subd11_0_284, List.forall_mem_cons.2 ⟨subd11_0_285, List.forall_mem_cons.2 ⟨subd11_0_286, List.forall_mem_cons.2 ⟨subd11_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_288 : subd11_0 [-4, 1, -5] = true := by decide +kernel
theorem subd11_0_289 : subd11_0 [-4, 1, -4] = true := by decide +kernel
theorem subd11_0_290 : subd11_0 [-4, 1, -3] = true := by decide +kernel
theorem subd11_0_291 : subd11_0 [-4, 1, -2] = true := by decide +kernel
theorem subd11_0_292 : subd11_0 [-4, 1, -1] = true := by decide +kernel
theorem subd11_0_293 : subd11_0 [-4, 1, 0] = true := by decide +kernel
theorem subd11_0_294 : subd11_0 [-4, 1, 1] = true := by decide +kernel
theorem subd11_0_295 : subd11_0 [-4, 1, 2] = true := by decide +kernel
theorem subd11_0_296 : subd11_0 [-4, 1, 3] = true := by decide +kernel
theorem subd11_0_297 : subd11_0 [-4, 1, 4] = true := by decide +kernel
theorem subd11_0_298 : subd11_0 [-4, 1, 5] = true := by decide +kernel
theorem subd11_0_299 : subd11_0 [-4, 1, 6] = true := by decide +kernel
theorem subd11_0_300 : subd11_0 [-4, 2, -9] = true := by decide +kernel
theorem subd11_0_301 : subd11_0 [-4, 2, -8] = true := by decide +kernel
theorem subd11_0_302 : subd11_0 [-4, 2, -7] = true := by decide +kernel
theorem subd11_0_303 : subd11_0 [-4, 2, -6] = true := by decide +kernel
theorem subd11_0_304 : subd11_0 [-4, 2, -5] = true := by decide +kernel
theorem subd11_0_305 : subd11_0 [-4, 2, -4] = true := by decide +kernel
theorem subd11_0_306 : subd11_0 [-4, 2, -3] = true := by decide +kernel
theorem subd11_0_307 : subd11_0 [-4, 2, -2] = true := by decide +kernel
theorem subd11_0_308 : subd11_0 [-4, 2, -1] = true := by decide +kernel
theorem subd11_0_309 : subd11_0 [-4, 2, 0] = true := by decide +kernel
theorem subd11_0_310 : subd11_0 [-4, 2, 1] = true := by decide +kernel
theorem subd11_0_311 : subd11_0 [-4, 2, 2] = true := by decide +kernel
theorem subd11_0_312 : subd11_0 [-4, 2, 3] = true := by decide +kernel
theorem subd11_0_313 : subd11_0 [-4, 2, 4] = true := by decide +kernel
theorem subd11_0_314 : subd11_0 [-4, 2, 5] = true := by decide +kernel
theorem subd11_0_315 : subd11_0 [-4, 3, -8] = true := by decide +kernel
theorem subd11_0_316 : subd11_0 [-4, 3, -7] = true := by decide +kernel
theorem subd11_0_317 : subd11_0 [-4, 3, -6] = true := by decide +kernel
theorem subd11_0_318 : subd11_0 [-4, 3, -5] = true := by decide +kernel
theorem subd11_0_319 : subd11_0 [-4, 3, -4] = true := by decide +kernel
theorem sbd11_0_9 : ∀ q ∈ blkd11_0_9, subd11_0 q = true := by
  unfold blkd11_0_9
  exact List.forall_mem_cons.2 ⟨subd11_0_288, List.forall_mem_cons.2 ⟨subd11_0_289, List.forall_mem_cons.2 ⟨subd11_0_290, List.forall_mem_cons.2 ⟨subd11_0_291, List.forall_mem_cons.2 ⟨subd11_0_292, List.forall_mem_cons.2 ⟨subd11_0_293, List.forall_mem_cons.2 ⟨subd11_0_294, List.forall_mem_cons.2 ⟨subd11_0_295, List.forall_mem_cons.2 ⟨subd11_0_296, List.forall_mem_cons.2 ⟨subd11_0_297, List.forall_mem_cons.2 ⟨subd11_0_298, List.forall_mem_cons.2 ⟨subd11_0_299, List.forall_mem_cons.2 ⟨subd11_0_300, List.forall_mem_cons.2 ⟨subd11_0_301, List.forall_mem_cons.2 ⟨subd11_0_302, List.forall_mem_cons.2 ⟨subd11_0_303, List.forall_mem_cons.2 ⟨subd11_0_304, List.forall_mem_cons.2 ⟨subd11_0_305, List.forall_mem_cons.2 ⟨subd11_0_306, List.forall_mem_cons.2 ⟨subd11_0_307, List.forall_mem_cons.2 ⟨subd11_0_308, List.forall_mem_cons.2 ⟨subd11_0_309, List.forall_mem_cons.2 ⟨subd11_0_310, List.forall_mem_cons.2 ⟨subd11_0_311, List.forall_mem_cons.2 ⟨subd11_0_312, List.forall_mem_cons.2 ⟨subd11_0_313, List.forall_mem_cons.2 ⟨subd11_0_314, List.forall_mem_cons.2 ⟨subd11_0_315, List.forall_mem_cons.2 ⟨subd11_0_316, List.forall_mem_cons.2 ⟨subd11_0_317, List.forall_mem_cons.2 ⟨subd11_0_318, List.forall_mem_cons.2 ⟨subd11_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_320 : subd11_0 [-4, 3, -3] = true := by decide +kernel
theorem subd11_0_321 : subd11_0 [-4, 3, -2] = true := by decide +kernel
theorem subd11_0_322 : subd11_0 [-4, 3, -1] = true := by decide +kernel
theorem subd11_0_323 : subd11_0 [-4, 3, 0] = true := by decide +kernel
theorem subd11_0_324 : subd11_0 [-4, 3, 1] = true := by decide +kernel
theorem subd11_0_325 : subd11_0 [-4, 3, 2] = true := by decide +kernel
theorem subd11_0_326 : subd11_0 [-4, 3, 3] = true := by decide +kernel
theorem subd11_0_327 : subd11_0 [-4, 3, 4] = true := by decide +kernel
theorem subd11_0_328 : subd11_0 [-4, 3, 5] = true := by decide +kernel
theorem subd11_0_329 : subd11_0 [-4, 4] = true := by decide +kernel
theorem subd11_0_330 : subd11_0 [-4, 5] = true := by decide +kernel
theorem subd11_0_331 : subd11_0 [-4, 6] = true := by decide +kernel
theorem subd11_0_332 : subd11_0 [-3, -11] = true := by decide +kernel
theorem subd11_0_333 : subd11_0 [-3, -10] = true := by decide +kernel
theorem subd11_0_334 : subd11_0 [-3, -9] = true := by decide +kernel
theorem subd11_0_335 : subd11_0 [-3, -8] = true := by decide +kernel
theorem subd11_0_336 : subd11_0 [-3, -7, -7] = true := by decide +kernel
theorem subd11_0_337 : subd11_0 [-3, -7, -6] = true := by decide +kernel
theorem subd11_0_338 : subd11_0 [-3, -7, -5] = true := by decide +kernel
theorem subd11_0_339 : subd11_0 [-3, -7, -4] = true := by decide +kernel
theorem subd11_0_340 : subd11_0 [-3, -7, -3] = true := by decide +kernel
theorem subd11_0_341 : subd11_0 [-3, -7, -2] = true := by decide +kernel
theorem subd11_0_342 : subd11_0 [-3, -7, -1] = true := by decide +kernel
theorem subd11_0_343 : subd11_0 [-3, -7, 0] = true := by decide +kernel
theorem subd11_0_344 : subd11_0 [-3, -7, 1] = true := by decide +kernel
theorem subd11_0_345 : subd11_0 [-3, -7, 2] = true := by decide +kernel
theorem subd11_0_346 : subd11_0 [-3, -7, 3] = true := by decide +kernel
theorem subd11_0_347 : subd11_0 [-3, -7, 4] = true := by decide +kernel
theorem subd11_0_348 : subd11_0 [-3, -7, 5] = true := by decide +kernel
theorem subd11_0_349 : subd11_0 [-3, -6, -8] = true := by decide +kernel
theorem subd11_0_350 : subd11_0 [-3, -6, -7] = true := by decide +kernel
theorem subd11_0_351 : subd11_0 [-3, -6, -6] = true := by decide +kernel
theorem sbd11_0_10 : ∀ q ∈ blkd11_0_10, subd11_0 q = true := by
  unfold blkd11_0_10
  exact List.forall_mem_cons.2 ⟨subd11_0_320, List.forall_mem_cons.2 ⟨subd11_0_321, List.forall_mem_cons.2 ⟨subd11_0_322, List.forall_mem_cons.2 ⟨subd11_0_323, List.forall_mem_cons.2 ⟨subd11_0_324, List.forall_mem_cons.2 ⟨subd11_0_325, List.forall_mem_cons.2 ⟨subd11_0_326, List.forall_mem_cons.2 ⟨subd11_0_327, List.forall_mem_cons.2 ⟨subd11_0_328, List.forall_mem_cons.2 ⟨subd11_0_329, List.forall_mem_cons.2 ⟨subd11_0_330, List.forall_mem_cons.2 ⟨subd11_0_331, List.forall_mem_cons.2 ⟨subd11_0_332, List.forall_mem_cons.2 ⟨subd11_0_333, List.forall_mem_cons.2 ⟨subd11_0_334, List.forall_mem_cons.2 ⟨subd11_0_335, List.forall_mem_cons.2 ⟨subd11_0_336, List.forall_mem_cons.2 ⟨subd11_0_337, List.forall_mem_cons.2 ⟨subd11_0_338, List.forall_mem_cons.2 ⟨subd11_0_339, List.forall_mem_cons.2 ⟨subd11_0_340, List.forall_mem_cons.2 ⟨subd11_0_341, List.forall_mem_cons.2 ⟨subd11_0_342, List.forall_mem_cons.2 ⟨subd11_0_343, List.forall_mem_cons.2 ⟨subd11_0_344, List.forall_mem_cons.2 ⟨subd11_0_345, List.forall_mem_cons.2 ⟨subd11_0_346, List.forall_mem_cons.2 ⟨subd11_0_347, List.forall_mem_cons.2 ⟨subd11_0_348, List.forall_mem_cons.2 ⟨subd11_0_349, List.forall_mem_cons.2 ⟨subd11_0_350, List.forall_mem_cons.2 ⟨subd11_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_352 : subd11_0 [-3, -6, -5] = true := by decide +kernel
theorem subd11_0_353 : subd11_0 [-3, -6, -4] = true := by decide +kernel
theorem subd11_0_354 : subd11_0 [-3, -6, -3] = true := by decide +kernel
theorem subd11_0_355 : subd11_0 [-3, -6, -2] = true := by decide +kernel
theorem subd11_0_356 : subd11_0 [-3, -6, -1] = true := by decide +kernel
theorem subd11_0_357 : subd11_0 [-3, -6, 0] = true := by decide +kernel
theorem subd11_0_358 : subd11_0 [-3, -6, 1] = true := by decide +kernel
theorem subd11_0_359 : subd11_0 [-3, -6, 2] = true := by decide +kernel
theorem subd11_0_360 : subd11_0 [-3, -6, 3] = true := by decide +kernel
theorem subd11_0_361 : subd11_0 [-3, -6, 4] = true := by decide +kernel
theorem subd11_0_362 : subd11_0 [-3, -6, 5] = true := by decide +kernel
theorem subd11_0_363 : subd11_0 [-3, -6, 6] = true := by decide +kernel
theorem subd11_0_364 : subd11_0 [-3, -5, -8] = true := by decide +kernel
theorem subd11_0_365 : subd11_0 [-3, -5, -7] = true := by decide +kernel
theorem subd11_0_366 : subd11_0 [-3, -5, -6] = true := by decide +kernel
theorem subd11_0_367 : subd11_0 [-3, -5, -5] = true := by decide +kernel
theorem subd11_0_368 : subd11_0 [-3, -5, -4] = true := by decide +kernel
theorem subd11_0_369 : subd11_0 [-3, -5, -3] = true := by decide +kernel
theorem subd11_0_370 : subd11_0 [-3, -5, -2] = true := by decide +kernel
theorem subd11_0_371 : subd11_0 [-3, -5, -1] = true := by decide +kernel
theorem subd11_0_372 : subd11_0 [-3, -5, 0] = true := by decide +kernel
theorem subd11_0_373 : subd11_0 [-3, -5, 1] = true := by decide +kernel
theorem subd11_0_374 : subd11_0 [-3, -5, 2] = true := by decide +kernel
theorem subd11_0_375 : subd11_0 [-3, -5, 3] = true := by decide +kernel
theorem subd11_0_376 : subd11_0 [-3, -5, 4] = true := by decide +kernel
theorem subd11_0_377 : subd11_0 [-3, -5, 5] = true := by decide +kernel
theorem subd11_0_378 : subd11_0 [-3, -5, 6] = true := by decide +kernel
theorem subd11_0_379 : subd11_0 [-3, -4, -9] = true := by decide +kernel
theorem subd11_0_380 : subd11_0 [-3, -4, -8] = true := by decide +kernel
theorem subd11_0_381 : subd11_0 [-3, -4, -7] = true := by decide +kernel
theorem subd11_0_382 : subd11_0 [-3, -4, -6] = true := by decide +kernel
theorem subd11_0_383 : subd11_0 [-3, -4, -5] = true := by decide +kernel
theorem sbd11_0_11 : ∀ q ∈ blkd11_0_11, subd11_0 q = true := by
  unfold blkd11_0_11
  exact List.forall_mem_cons.2 ⟨subd11_0_352, List.forall_mem_cons.2 ⟨subd11_0_353, List.forall_mem_cons.2 ⟨subd11_0_354, List.forall_mem_cons.2 ⟨subd11_0_355, List.forall_mem_cons.2 ⟨subd11_0_356, List.forall_mem_cons.2 ⟨subd11_0_357, List.forall_mem_cons.2 ⟨subd11_0_358, List.forall_mem_cons.2 ⟨subd11_0_359, List.forall_mem_cons.2 ⟨subd11_0_360, List.forall_mem_cons.2 ⟨subd11_0_361, List.forall_mem_cons.2 ⟨subd11_0_362, List.forall_mem_cons.2 ⟨subd11_0_363, List.forall_mem_cons.2 ⟨subd11_0_364, List.forall_mem_cons.2 ⟨subd11_0_365, List.forall_mem_cons.2 ⟨subd11_0_366, List.forall_mem_cons.2 ⟨subd11_0_367, List.forall_mem_cons.2 ⟨subd11_0_368, List.forall_mem_cons.2 ⟨subd11_0_369, List.forall_mem_cons.2 ⟨subd11_0_370, List.forall_mem_cons.2 ⟨subd11_0_371, List.forall_mem_cons.2 ⟨subd11_0_372, List.forall_mem_cons.2 ⟨subd11_0_373, List.forall_mem_cons.2 ⟨subd11_0_374, List.forall_mem_cons.2 ⟨subd11_0_375, List.forall_mem_cons.2 ⟨subd11_0_376, List.forall_mem_cons.2 ⟨subd11_0_377, List.forall_mem_cons.2 ⟨subd11_0_378, List.forall_mem_cons.2 ⟨subd11_0_379, List.forall_mem_cons.2 ⟨subd11_0_380, List.forall_mem_cons.2 ⟨subd11_0_381, List.forall_mem_cons.2 ⟨subd11_0_382, List.forall_mem_cons.2 ⟨subd11_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_384 : subd11_0 [-3, -4, -4] = true := by decide +kernel
theorem subd11_0_385 : subd11_0 [-3, -4, -3] = true := by decide +kernel
theorem subd11_0_386 : subd11_0 [-3, -4, -2] = true := by decide +kernel
theorem subd11_0_387 : subd11_0 [-3, -4, -1] = true := by decide +kernel
theorem subd11_0_388 : subd11_0 [-3, -4, 0] = true := by decide +kernel
theorem subd11_0_389 : subd11_0 [-3, -4, 1] = true := by decide +kernel
theorem subd11_0_390 : subd11_0 [-3, -4, 2] = true := by decide +kernel
theorem subd11_0_391 : subd11_0 [-3, -4, 3] = true := by decide +kernel
theorem subd11_0_392 : subd11_0 [-3, -4, 4] = true := by decide +kernel
theorem subd11_0_393 : subd11_0 [-3, -4, 5] = true := by decide +kernel
theorem subd11_0_394 : subd11_0 [-3, -4, 6] = true := by decide +kernel
theorem subd11_0_395 : subd11_0 [-3, -4, 7] = true := by decide +kernel
theorem subd11_0_396 : subd11_0 [-3, -3, -9] = true := by decide +kernel
theorem subd11_0_397 : subd11_0 [-3, -3, -8] = true := by decide +kernel
theorem subd11_0_398 : subd11_0 [-3, -3, -7] = true := by decide +kernel
theorem subd11_0_399 : subd11_0 [-3, -3, -6] = true := by decide +kernel
theorem subd11_0_400 : subd11_0 [-3, -3, -5] = true := by decide +kernel
theorem subd11_0_401 : subd11_0 [-3, -3, -4] = true := by decide +kernel
theorem subd11_0_402 : subd11_0 [-3, -3, -3] = true := by decide +kernel
theorem subd11_0_403 : subd11_0 [-3, -3, -2] = true := by decide +kernel
theorem subd11_0_404 : subd11_0 [-3, -3, -1] = true := by decide +kernel
theorem subd11_0_405 : subd11_0 [-3, -3, 0] = true := by decide +kernel
theorem subd11_0_406 : subd11_0 [-3, -3, 1] = true := by decide +kernel
theorem subd11_0_407 : subd11_0 [-3, -3, 2] = true := by decide +kernel
theorem subd11_0_408 : subd11_0 [-3, -3, 3] = true := by decide +kernel
theorem subd11_0_409 : subd11_0 [-3, -3, 4] = true := by decide +kernel
theorem subd11_0_410 : subd11_0 [-3, -3, 5] = true := by decide +kernel
theorem subd11_0_411 : subd11_0 [-3, -3, 6] = true := by decide +kernel
theorem subd11_0_412 : subd11_0 [-3, -3, 7] = true := by decide +kernel
theorem subd11_0_413 : subd11_0 [-3, -2, -9] = true := by decide +kernel
theorem subd11_0_414 : subd11_0 [-3, -2, -8] = true := by decide +kernel
theorem subd11_0_415 : subd11_0 [-3, -2, -7] = true := by decide +kernel
theorem sbd11_0_12 : ∀ q ∈ blkd11_0_12, subd11_0 q = true := by
  unfold blkd11_0_12
  exact List.forall_mem_cons.2 ⟨subd11_0_384, List.forall_mem_cons.2 ⟨subd11_0_385, List.forall_mem_cons.2 ⟨subd11_0_386, List.forall_mem_cons.2 ⟨subd11_0_387, List.forall_mem_cons.2 ⟨subd11_0_388, List.forall_mem_cons.2 ⟨subd11_0_389, List.forall_mem_cons.2 ⟨subd11_0_390, List.forall_mem_cons.2 ⟨subd11_0_391, List.forall_mem_cons.2 ⟨subd11_0_392, List.forall_mem_cons.2 ⟨subd11_0_393, List.forall_mem_cons.2 ⟨subd11_0_394, List.forall_mem_cons.2 ⟨subd11_0_395, List.forall_mem_cons.2 ⟨subd11_0_396, List.forall_mem_cons.2 ⟨subd11_0_397, List.forall_mem_cons.2 ⟨subd11_0_398, List.forall_mem_cons.2 ⟨subd11_0_399, List.forall_mem_cons.2 ⟨subd11_0_400, List.forall_mem_cons.2 ⟨subd11_0_401, List.forall_mem_cons.2 ⟨subd11_0_402, List.forall_mem_cons.2 ⟨subd11_0_403, List.forall_mem_cons.2 ⟨subd11_0_404, List.forall_mem_cons.2 ⟨subd11_0_405, List.forall_mem_cons.2 ⟨subd11_0_406, List.forall_mem_cons.2 ⟨subd11_0_407, List.forall_mem_cons.2 ⟨subd11_0_408, List.forall_mem_cons.2 ⟨subd11_0_409, List.forall_mem_cons.2 ⟨subd11_0_410, List.forall_mem_cons.2 ⟨subd11_0_411, List.forall_mem_cons.2 ⟨subd11_0_412, List.forall_mem_cons.2 ⟨subd11_0_413, List.forall_mem_cons.2 ⟨subd11_0_414, List.forall_mem_cons.2 ⟨subd11_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_416 : subd11_0 [-3, -2, -6] = true := by decide +kernel
theorem subd11_0_417 : subd11_0 [-3, -2, -5] = true := by decide +kernel
theorem subd11_0_418 : subd11_0 [-3, -2, -4] = true := by decide +kernel
theorem subd11_0_419 : subd11_0 [-3, -2, -3] = true := by decide +kernel
theorem subd11_0_420 : subd11_0 [-3, -2, -2] = true := by decide +kernel
theorem subd11_0_421 : subd11_0 [-3, -2, -1] = true := by decide +kernel
theorem subd11_0_422 : subd11_0 [-3, -2, 0] = true := by decide +kernel
theorem subd11_0_423 : subd11_0 [-3, -2, 1] = true := by decide +kernel
theorem subd11_0_424 : subd11_0 [-3, -2, 2] = true := by decide +kernel
theorem subd11_0_425 : subd11_0 [-3, -2, 3] = true := by decide +kernel
theorem subd11_0_426 : subd11_0 [-3, -2, 4] = true := by decide +kernel
theorem subd11_0_427 : subd11_0 [-3, -2, 5] = true := by decide +kernel
theorem subd11_0_428 : subd11_0 [-3, -2, 6] = true := by decide +kernel
theorem subd11_0_429 : subd11_0 [-3, -2, 7] = true := by decide +kernel
theorem subd11_0_430 : subd11_0 [-3, -1, -9] = true := by decide +kernel
theorem subd11_0_431 : subd11_0 [-3, -1, -8] = true := by decide +kernel
theorem subd11_0_432 : subd11_0 [-3, -1, -7] = true := by decide +kernel
theorem subd11_0_433 : subd11_0 [-3, -1, -6] = true := by decide +kernel
theorem subd11_0_434 : subd11_0 [-3, -1, -5] = true := by decide +kernel
theorem subd11_0_435 : subd11_0 [-3, -1, -4] = true := by decide +kernel
theorem subd11_0_436 : subd11_0 [-3, -1, -3] = true := by decide +kernel
theorem subd11_0_437 : subd11_0 [-3, -1, -2] = true := by decide +kernel
theorem subd11_0_438 : subd11_0 [-3, -1, -1] = true := by decide +kernel
theorem subd11_0_439 : subd11_0 [-3, -1, 0] = true := by decide +kernel
theorem subd11_0_440 : subd11_0 [-3, -1, 1] = true := by decide +kernel
theorem subd11_0_441 : subd11_0 [-3, -1, 2] = true := by decide +kernel
theorem subd11_0_442 : subd11_0 [-3, -1, 3] = true := by decide +kernel
theorem subd11_0_443 : subd11_0 [-3, -1, 4] = true := by decide +kernel
theorem subd11_0_444 : subd11_0 [-3, -1, 5] = true := by decide +kernel
theorem subd11_0_445 : subd11_0 [-3, -1, 6] = true := by decide +kernel
theorem subd11_0_446 : subd11_0 [-3, -1, 7] = true := by decide +kernel
theorem subd11_0_447 : subd11_0 [-3, 0, -9] = true := by decide +kernel
theorem sbd11_0_13 : ∀ q ∈ blkd11_0_13, subd11_0 q = true := by
  unfold blkd11_0_13
  exact List.forall_mem_cons.2 ⟨subd11_0_416, List.forall_mem_cons.2 ⟨subd11_0_417, List.forall_mem_cons.2 ⟨subd11_0_418, List.forall_mem_cons.2 ⟨subd11_0_419, List.forall_mem_cons.2 ⟨subd11_0_420, List.forall_mem_cons.2 ⟨subd11_0_421, List.forall_mem_cons.2 ⟨subd11_0_422, List.forall_mem_cons.2 ⟨subd11_0_423, List.forall_mem_cons.2 ⟨subd11_0_424, List.forall_mem_cons.2 ⟨subd11_0_425, List.forall_mem_cons.2 ⟨subd11_0_426, List.forall_mem_cons.2 ⟨subd11_0_427, List.forall_mem_cons.2 ⟨subd11_0_428, List.forall_mem_cons.2 ⟨subd11_0_429, List.forall_mem_cons.2 ⟨subd11_0_430, List.forall_mem_cons.2 ⟨subd11_0_431, List.forall_mem_cons.2 ⟨subd11_0_432, List.forall_mem_cons.2 ⟨subd11_0_433, List.forall_mem_cons.2 ⟨subd11_0_434, List.forall_mem_cons.2 ⟨subd11_0_435, List.forall_mem_cons.2 ⟨subd11_0_436, List.forall_mem_cons.2 ⟨subd11_0_437, List.forall_mem_cons.2 ⟨subd11_0_438, List.forall_mem_cons.2 ⟨subd11_0_439, List.forall_mem_cons.2 ⟨subd11_0_440, List.forall_mem_cons.2 ⟨subd11_0_441, List.forall_mem_cons.2 ⟨subd11_0_442, List.forall_mem_cons.2 ⟨subd11_0_443, List.forall_mem_cons.2 ⟨subd11_0_444, List.forall_mem_cons.2 ⟨subd11_0_445, List.forall_mem_cons.2 ⟨subd11_0_446, List.forall_mem_cons.2 ⟨subd11_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_448 : subd11_0 [-3, 0, -8] = true := by decide +kernel
theorem subd11_0_449 : subd11_0 [-3, 0, -7] = true := by decide +kernel
theorem subd11_0_450 : subd11_0 [-3, 0, -6] = true := by decide +kernel
theorem subd11_0_451 : subd11_0 [-3, 0, -5] = true := by decide +kernel
theorem subd11_0_452 : subd11_0 [-3, 0, -4] = true := by decide +kernel
theorem subd11_0_453 : subd11_0 [-3, 0, -3] = true := by decide +kernel
theorem subd11_0_454 : subd11_0 [-3, 0, -2] = true := by decide +kernel
theorem subd11_0_455 : subd11_0 [-3, 0, -1] = true := by decide +kernel
theorem subd11_0_456 : subd11_0 [-3, 0, 0] = true := by decide +kernel
theorem subd11_0_457 : subd11_0 [-3, 0, 1] = true := by decide +kernel
theorem subd11_0_458 : subd11_0 [-3, 0, 2] = true := by decide +kernel
theorem subd11_0_459 : subd11_0 [-3, 0, 3] = true := by decide +kernel
theorem subd11_0_460 : subd11_0 [-3, 0, 4] = true := by decide +kernel
theorem subd11_0_461 : subd11_0 [-3, 0, 5] = true := by decide +kernel
theorem subd11_0_462 : subd11_0 [-3, 0, 6] = true := by decide +kernel
theorem subd11_0_463 : subd11_0 [-3, 0, 7] = true := by decide +kernel
theorem subd11_0_464 : subd11_0 [-3, 1, -9] = true := by decide +kernel
theorem subd11_0_465 : subd11_0 [-3, 1, -8] = true := by decide +kernel
theorem subd11_0_466 : subd11_0 [-3, 1, -7] = true := by decide +kernel
theorem subd11_0_467 : subd11_0 [-3, 1, -6] = true := by decide +kernel
theorem subd11_0_468 : subd11_0 [-3, 1, -5] = true := by decide +kernel
theorem subd11_0_469 : subd11_0 [-3, 1, -4] = true := by decide +kernel
theorem subd11_0_470 : subd11_0 [-3, 1, -3] = true := by decide +kernel
theorem subd11_0_471 : subd11_0 [-3, 1, -2] = true := by decide +kernel
theorem subd11_0_472 : subd11_0 [-3, 1, -1] = true := by decide +kernel
theorem subd11_0_473 : subd11_0 [-3, 1, 0] = true := by decide +kernel
theorem subd11_0_474 : subd11_0 [-3, 1, 1] = true := by decide +kernel
theorem subd11_0_475 : subd11_0 [-3, 1, 2] = true := by decide +kernel
theorem subd11_0_476 : subd11_0 [-3, 1, 3] = true := by decide +kernel
theorem subd11_0_477 : subd11_0 [-3, 1, 4] = true := by decide +kernel
theorem subd11_0_478 : subd11_0 [-3, 1, 5] = true := by decide +kernel
theorem subd11_0_479 : subd11_0 [-3, 1, 6] = true := by decide +kernel
theorem sbd11_0_14 : ∀ q ∈ blkd11_0_14, subd11_0 q = true := by
  unfold blkd11_0_14
  exact List.forall_mem_cons.2 ⟨subd11_0_448, List.forall_mem_cons.2 ⟨subd11_0_449, List.forall_mem_cons.2 ⟨subd11_0_450, List.forall_mem_cons.2 ⟨subd11_0_451, List.forall_mem_cons.2 ⟨subd11_0_452, List.forall_mem_cons.2 ⟨subd11_0_453, List.forall_mem_cons.2 ⟨subd11_0_454, List.forall_mem_cons.2 ⟨subd11_0_455, List.forall_mem_cons.2 ⟨subd11_0_456, List.forall_mem_cons.2 ⟨subd11_0_457, List.forall_mem_cons.2 ⟨subd11_0_458, List.forall_mem_cons.2 ⟨subd11_0_459, List.forall_mem_cons.2 ⟨subd11_0_460, List.forall_mem_cons.2 ⟨subd11_0_461, List.forall_mem_cons.2 ⟨subd11_0_462, List.forall_mem_cons.2 ⟨subd11_0_463, List.forall_mem_cons.2 ⟨subd11_0_464, List.forall_mem_cons.2 ⟨subd11_0_465, List.forall_mem_cons.2 ⟨subd11_0_466, List.forall_mem_cons.2 ⟨subd11_0_467, List.forall_mem_cons.2 ⟨subd11_0_468, List.forall_mem_cons.2 ⟨subd11_0_469, List.forall_mem_cons.2 ⟨subd11_0_470, List.forall_mem_cons.2 ⟨subd11_0_471, List.forall_mem_cons.2 ⟨subd11_0_472, List.forall_mem_cons.2 ⟨subd11_0_473, List.forall_mem_cons.2 ⟨subd11_0_474, List.forall_mem_cons.2 ⟨subd11_0_475, List.forall_mem_cons.2 ⟨subd11_0_476, List.forall_mem_cons.2 ⟨subd11_0_477, List.forall_mem_cons.2 ⟨subd11_0_478, List.forall_mem_cons.2 ⟨subd11_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_480 : subd11_0 [-3, 1, 7] = true := by decide +kernel
theorem subd11_0_481 : subd11_0 [-3, 2, -9] = true := by decide +kernel
theorem subd11_0_482 : subd11_0 [-3, 2, -8] = true := by decide +kernel
theorem subd11_0_483 : subd11_0 [-3, 2, -7] = true := by decide +kernel
theorem subd11_0_484 : subd11_0 [-3, 2, -6] = true := by decide +kernel
theorem subd11_0_485 : subd11_0 [-3, 2, -5] = true := by decide +kernel
theorem subd11_0_486 : subd11_0 [-3, 2, -4] = true := by decide +kernel
theorem subd11_0_487 : subd11_0 [-3, 2, -3] = true := by decide +kernel
theorem subd11_0_488 : subd11_0 [-3, 2, -2] = true := by decide +kernel
theorem subd11_0_489 : subd11_0 [-3, 2, -1] = true := by decide +kernel
theorem subd11_0_490 : subd11_0 [-3, 2, 0] = true := by decide +kernel
theorem subd11_0_491 : subd11_0 [-3, 2, 1] = true := by decide +kernel
theorem subd11_0_492 : subd11_0 [-3, 2, 2] = true := by decide +kernel
theorem subd11_0_493 : subd11_0 [-3, 2, 3] = true := by decide +kernel
theorem subd11_0_494 : subd11_0 [-3, 2, 4] = true := by decide +kernel
theorem subd11_0_495 : subd11_0 [-3, 2, 5] = true := by decide +kernel
theorem subd11_0_496 : subd11_0 [-3, 2, 6] = true := by decide +kernel
theorem subd11_0_497 : subd11_0 [-3, 3, -9] = true := by decide +kernel
theorem subd11_0_498 : subd11_0 [-3, 3, -8] = true := by decide +kernel
theorem subd11_0_499 : subd11_0 [-3, 3, -7] = true := by decide +kernel
theorem subd11_0_500 : subd11_0 [-3, 3, -6] = true := by decide +kernel
theorem subd11_0_501 : subd11_0 [-3, 3, -5] = true := by decide +kernel
theorem subd11_0_502 : subd11_0 [-3, 3, -4] = true := by decide +kernel
theorem subd11_0_503 : subd11_0 [-3, 3, -3] = true := by decide +kernel
theorem subd11_0_504 : subd11_0 [-3, 3, -2] = true := by decide +kernel
theorem subd11_0_505 : subd11_0 [-3, 3, -1] = true := by decide +kernel
theorem subd11_0_506 : subd11_0 [-3, 3, 0] = true := by decide +kernel
theorem subd11_0_507 : subd11_0 [-3, 3, 1] = true := by decide +kernel
theorem subd11_0_508 : subd11_0 [-3, 3, 2] = true := by decide +kernel
theorem subd11_0_509 : subd11_0 [-3, 3, 3] = true := by decide +kernel
theorem subd11_0_510 : subd11_0 [-3, 3, 4] = true := by decide +kernel
theorem subd11_0_511 : subd11_0 [-3, 3, 5] = true := by decide +kernel
theorem sbd11_0_15 : ∀ q ∈ blkd11_0_15, subd11_0 q = true := by
  unfold blkd11_0_15
  exact List.forall_mem_cons.2 ⟨subd11_0_480, List.forall_mem_cons.2 ⟨subd11_0_481, List.forall_mem_cons.2 ⟨subd11_0_482, List.forall_mem_cons.2 ⟨subd11_0_483, List.forall_mem_cons.2 ⟨subd11_0_484, List.forall_mem_cons.2 ⟨subd11_0_485, List.forall_mem_cons.2 ⟨subd11_0_486, List.forall_mem_cons.2 ⟨subd11_0_487, List.forall_mem_cons.2 ⟨subd11_0_488, List.forall_mem_cons.2 ⟨subd11_0_489, List.forall_mem_cons.2 ⟨subd11_0_490, List.forall_mem_cons.2 ⟨subd11_0_491, List.forall_mem_cons.2 ⟨subd11_0_492, List.forall_mem_cons.2 ⟨subd11_0_493, List.forall_mem_cons.2 ⟨subd11_0_494, List.forall_mem_cons.2 ⟨subd11_0_495, List.forall_mem_cons.2 ⟨subd11_0_496, List.forall_mem_cons.2 ⟨subd11_0_497, List.forall_mem_cons.2 ⟨subd11_0_498, List.forall_mem_cons.2 ⟨subd11_0_499, List.forall_mem_cons.2 ⟨subd11_0_500, List.forall_mem_cons.2 ⟨subd11_0_501, List.forall_mem_cons.2 ⟨subd11_0_502, List.forall_mem_cons.2 ⟨subd11_0_503, List.forall_mem_cons.2 ⟨subd11_0_504, List.forall_mem_cons.2 ⟨subd11_0_505, List.forall_mem_cons.2 ⟨subd11_0_506, List.forall_mem_cons.2 ⟨subd11_0_507, List.forall_mem_cons.2 ⟨subd11_0_508, List.forall_mem_cons.2 ⟨subd11_0_509, List.forall_mem_cons.2 ⟨subd11_0_510, List.forall_mem_cons.2 ⟨subd11_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_512 : subd11_0 [-3, 3, 6] = true := by decide +kernel
theorem subd11_0_513 : subd11_0 [-3, 4, -8] = true := by decide +kernel
theorem subd11_0_514 : subd11_0 [-3, 4, -7] = true := by decide +kernel
theorem subd11_0_515 : subd11_0 [-3, 4, -6] = true := by decide +kernel
theorem subd11_0_516 : subd11_0 [-3, 4, -5] = true := by decide +kernel
theorem subd11_0_517 : subd11_0 [-3, 4, -4] = true := by decide +kernel
theorem subd11_0_518 : subd11_0 [-3, 4, -3] = true := by decide +kernel
theorem subd11_0_519 : subd11_0 [-3, 4, -2] = true := by decide +kernel
theorem subd11_0_520 : subd11_0 [-3, 4, -1] = true := by decide +kernel
theorem subd11_0_521 : subd11_0 [-3, 4, 0] = true := by decide +kernel
theorem subd11_0_522 : subd11_0 [-3, 4, 1] = true := by decide +kernel
theorem subd11_0_523 : subd11_0 [-3, 4, 2] = true := by decide +kernel
theorem subd11_0_524 : subd11_0 [-3, 4, 3] = true := by decide +kernel
theorem subd11_0_525 : subd11_0 [-3, 4, 4] = true := by decide +kernel
theorem subd11_0_526 : subd11_0 [-3, 4, 5] = true := by decide +kernel
theorem subd11_0_527 : subd11_0 [-3, 5] = true := by decide +kernel
theorem subd11_0_528 : subd11_0 [-3, 6] = true := by decide +kernel
theorem subd11_0_529 : subd11_0 [-3, 7] = true := by decide +kernel
theorem subd11_0_530 : subd11_0 [-2, -11] = true := by decide +kernel
theorem subd11_0_531 : subd11_0 [-2, -10] = true := by decide +kernel
theorem subd11_0_532 : subd11_0 [-2, -9] = true := by decide +kernel
theorem subd11_0_533 : subd11_0 [-2, -8] = true := by decide +kernel
theorem subd11_0_534 : subd11_0 [-2, -7, -7] = true := by decide +kernel
theorem subd11_0_535 : subd11_0 [-2, -7, -6] = true := by decide +kernel
theorem subd11_0_536 : subd11_0 [-2, -7, -5] = true := by decide +kernel
theorem subd11_0_537 : subd11_0 [-2, -7, -4] = true := by decide +kernel
theorem subd11_0_538 : subd11_0 [-2, -7, -3] = true := by decide +kernel
theorem subd11_0_539 : subd11_0 [-2, -7, -2] = true := by decide +kernel
theorem subd11_0_540 : subd11_0 [-2, -7, -1] = true := by decide +kernel
theorem subd11_0_541 : subd11_0 [-2, -7, 0] = true := by decide +kernel
theorem subd11_0_542 : subd11_0 [-2, -7, 1] = true := by decide +kernel
theorem subd11_0_543 : subd11_0 [-2, -7, 2] = true := by decide +kernel
theorem sbd11_0_16 : ∀ q ∈ blkd11_0_16, subd11_0 q = true := by
  unfold blkd11_0_16
  exact List.forall_mem_cons.2 ⟨subd11_0_512, List.forall_mem_cons.2 ⟨subd11_0_513, List.forall_mem_cons.2 ⟨subd11_0_514, List.forall_mem_cons.2 ⟨subd11_0_515, List.forall_mem_cons.2 ⟨subd11_0_516, List.forall_mem_cons.2 ⟨subd11_0_517, List.forall_mem_cons.2 ⟨subd11_0_518, List.forall_mem_cons.2 ⟨subd11_0_519, List.forall_mem_cons.2 ⟨subd11_0_520, List.forall_mem_cons.2 ⟨subd11_0_521, List.forall_mem_cons.2 ⟨subd11_0_522, List.forall_mem_cons.2 ⟨subd11_0_523, List.forall_mem_cons.2 ⟨subd11_0_524, List.forall_mem_cons.2 ⟨subd11_0_525, List.forall_mem_cons.2 ⟨subd11_0_526, List.forall_mem_cons.2 ⟨subd11_0_527, List.forall_mem_cons.2 ⟨subd11_0_528, List.forall_mem_cons.2 ⟨subd11_0_529, List.forall_mem_cons.2 ⟨subd11_0_530, List.forall_mem_cons.2 ⟨subd11_0_531, List.forall_mem_cons.2 ⟨subd11_0_532, List.forall_mem_cons.2 ⟨subd11_0_533, List.forall_mem_cons.2 ⟨subd11_0_534, List.forall_mem_cons.2 ⟨subd11_0_535, List.forall_mem_cons.2 ⟨subd11_0_536, List.forall_mem_cons.2 ⟨subd11_0_537, List.forall_mem_cons.2 ⟨subd11_0_538, List.forall_mem_cons.2 ⟨subd11_0_539, List.forall_mem_cons.2 ⟨subd11_0_540, List.forall_mem_cons.2 ⟨subd11_0_541, List.forall_mem_cons.2 ⟨subd11_0_542, List.forall_mem_cons.2 ⟨subd11_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_544 : subd11_0 [-2, -7, 3] = true := by decide +kernel
theorem subd11_0_545 : subd11_0 [-2, -7, 4] = true := by decide +kernel
theorem subd11_0_546 : subd11_0 [-2, -7, 5] = true := by decide +kernel
theorem subd11_0_547 : subd11_0 [-2, -7, 6] = true := by decide +kernel
theorem subd11_0_548 : subd11_0 [-2, -6, -8] = true := by decide +kernel
theorem subd11_0_549 : subd11_0 [-2, -6, -7] = true := by decide +kernel
theorem subd11_0_550 : subd11_0 [-2, -6, -6] = true := by decide +kernel
theorem subd11_0_551 : subd11_0 [-2, -6, -5] = true := by decide +kernel
theorem subd11_0_552 : subd11_0 [-2, -6, -4] = true := by decide +kernel
theorem subd11_0_553 : subd11_0 [-2, -6, -3] = true := by decide +kernel
theorem subd11_0_554 : subd11_0 [-2, -6, -2] = true := by decide +kernel
theorem subd11_0_555 : subd11_0 [-2, -6, -1] = true := by decide +kernel
theorem subd11_0_556 : subd11_0 [-2, -6, 0] = true := by decide +kernel
theorem subd11_0_557 : subd11_0 [-2, -6, 1] = true := by decide +kernel
theorem subd11_0_558 : subd11_0 [-2, -6, 2] = true := by decide +kernel
theorem subd11_0_559 : subd11_0 [-2, -6, 3] = true := by decide +kernel
theorem subd11_0_560 : subd11_0 [-2, -6, 4] = true := by decide +kernel
theorem subd11_0_561 : subd11_0 [-2, -6, 5] = true := by decide +kernel
theorem subd11_0_562 : subd11_0 [-2, -6, 6] = true := by decide +kernel
theorem subd11_0_563 : subd11_0 [-2, -5, -8] = true := by decide +kernel
theorem subd11_0_564 : subd11_0 [-2, -5, -7] = true := by decide +kernel
theorem subd11_0_565 : subd11_0 [-2, -5, -6] = true := by decide +kernel
theorem subd11_0_566 : subd11_0 [-2, -5, -5] = true := by decide +kernel
theorem subd11_0_567 : subd11_0 [-2, -5, -4] = true := by decide +kernel
theorem subd11_0_568 : subd11_0 [-2, -5, -3] = true := by decide +kernel
theorem subd11_0_569 : subd11_0 [-2, -5, -2] = true := by decide +kernel
theorem subd11_0_570 : subd11_0 [-2, -5, -1] = true := by decide +kernel
theorem subd11_0_571 : subd11_0 [-2, -5, 0] = true := by decide +kernel
theorem subd11_0_572 : subd11_0 [-2, -5, 1] = true := by decide +kernel
theorem subd11_0_573 : subd11_0 [-2, -5, 2] = true := by decide +kernel
theorem subd11_0_574 : subd11_0 [-2, -5, 3] = true := by decide +kernel
theorem subd11_0_575 : subd11_0 [-2, -5, 4] = true := by decide +kernel
theorem sbd11_0_17 : ∀ q ∈ blkd11_0_17, subd11_0 q = true := by
  unfold blkd11_0_17
  exact List.forall_mem_cons.2 ⟨subd11_0_544, List.forall_mem_cons.2 ⟨subd11_0_545, List.forall_mem_cons.2 ⟨subd11_0_546, List.forall_mem_cons.2 ⟨subd11_0_547, List.forall_mem_cons.2 ⟨subd11_0_548, List.forall_mem_cons.2 ⟨subd11_0_549, List.forall_mem_cons.2 ⟨subd11_0_550, List.forall_mem_cons.2 ⟨subd11_0_551, List.forall_mem_cons.2 ⟨subd11_0_552, List.forall_mem_cons.2 ⟨subd11_0_553, List.forall_mem_cons.2 ⟨subd11_0_554, List.forall_mem_cons.2 ⟨subd11_0_555, List.forall_mem_cons.2 ⟨subd11_0_556, List.forall_mem_cons.2 ⟨subd11_0_557, List.forall_mem_cons.2 ⟨subd11_0_558, List.forall_mem_cons.2 ⟨subd11_0_559, List.forall_mem_cons.2 ⟨subd11_0_560, List.forall_mem_cons.2 ⟨subd11_0_561, List.forall_mem_cons.2 ⟨subd11_0_562, List.forall_mem_cons.2 ⟨subd11_0_563, List.forall_mem_cons.2 ⟨subd11_0_564, List.forall_mem_cons.2 ⟨subd11_0_565, List.forall_mem_cons.2 ⟨subd11_0_566, List.forall_mem_cons.2 ⟨subd11_0_567, List.forall_mem_cons.2 ⟨subd11_0_568, List.forall_mem_cons.2 ⟨subd11_0_569, List.forall_mem_cons.2 ⟨subd11_0_570, List.forall_mem_cons.2 ⟨subd11_0_571, List.forall_mem_cons.2 ⟨subd11_0_572, List.forall_mem_cons.2 ⟨subd11_0_573, List.forall_mem_cons.2 ⟨subd11_0_574, List.forall_mem_cons.2 ⟨subd11_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_576 : subd11_0 [-2, -5, 5] = true := by decide +kernel
theorem subd11_0_577 : subd11_0 [-2, -5, 6] = true := by decide +kernel
theorem subd11_0_578 : subd11_0 [-2, -5, 7] = true := by decide +kernel
theorem subd11_0_579 : subd11_0 [-2, -4, -9] = true := by decide +kernel
theorem subd11_0_580 : subd11_0 [-2, -4, -8] = true := by decide +kernel
theorem subd11_0_581 : subd11_0 [-2, -4, -7] = true := by decide +kernel
theorem subd11_0_582 : subd11_0 [-2, -4, -6] = true := by decide +kernel
theorem subd11_0_583 : subd11_0 [-2, -4, -5] = true := by decide +kernel
theorem subd11_0_584 : subd11_0 [-2, -4, -4] = true := by decide +kernel
theorem subd11_0_585 : subd11_0 [-2, -4, -3] = true := by decide +kernel
theorem subd11_0_586 : subd11_0 [-2, -4, -2] = true := by decide +kernel
theorem subd11_0_587 : subd11_0 [-2, -4, -1] = true := by decide +kernel
theorem subd11_0_588 : subd11_0 [-2, -4, 0] = true := by decide +kernel
theorem subd11_0_589 : subd11_0 [-2, -4, 1] = true := by decide +kernel
theorem subd11_0_590 : subd11_0 [-2, -4, 2] = true := by decide +kernel
theorem subd11_0_591 : subd11_0 [-2, -4, 3] = true := by decide +kernel
theorem subd11_0_592 : subd11_0 [-2, -4, 4] = true := by decide +kernel
theorem subd11_0_593 : subd11_0 [-2, -4, 5] = true := by decide +kernel
theorem subd11_0_594 : subd11_0 [-2, -4, 6] = true := by decide +kernel
theorem subd11_0_595 : subd11_0 [-2, -4, 7] = true := by decide +kernel
theorem subd11_0_596 : subd11_0 [-2, -3, -9] = true := by decide +kernel
theorem subd11_0_597 : subd11_0 [-2, -3, -8] = true := by decide +kernel
theorem subd11_0_598 : subd11_0 [-2, -3, -7] = true := by decide +kernel
theorem subd11_0_599 : subd11_0 [-2, -3, -6] = true := by decide +kernel
theorem subd11_0_600 : subd11_0 [-2, -3, -5] = true := by decide +kernel
theorem subd11_0_601 : subd11_0 [-2, -3, -4] = true := by decide +kernel
theorem subd11_0_602 : subd11_0 [-2, -3, -3] = true := by decide +kernel
theorem subd11_0_603 : subd11_0 [-2, -3, -2] = true := by decide +kernel
theorem subd11_0_604 : subd11_0 [-2, -3, -1] = true := by decide +kernel
theorem subd11_0_605 : subd11_0 [-2, -3, 0] = true := by decide +kernel
theorem subd11_0_606 : subd11_0 [-2, -3, 1] = true := by decide +kernel
theorem subd11_0_607 : subd11_0 [-2, -3, 2] = true := by decide +kernel
theorem sbd11_0_18 : ∀ q ∈ blkd11_0_18, subd11_0 q = true := by
  unfold blkd11_0_18
  exact List.forall_mem_cons.2 ⟨subd11_0_576, List.forall_mem_cons.2 ⟨subd11_0_577, List.forall_mem_cons.2 ⟨subd11_0_578, List.forall_mem_cons.2 ⟨subd11_0_579, List.forall_mem_cons.2 ⟨subd11_0_580, List.forall_mem_cons.2 ⟨subd11_0_581, List.forall_mem_cons.2 ⟨subd11_0_582, List.forall_mem_cons.2 ⟨subd11_0_583, List.forall_mem_cons.2 ⟨subd11_0_584, List.forall_mem_cons.2 ⟨subd11_0_585, List.forall_mem_cons.2 ⟨subd11_0_586, List.forall_mem_cons.2 ⟨subd11_0_587, List.forall_mem_cons.2 ⟨subd11_0_588, List.forall_mem_cons.2 ⟨subd11_0_589, List.forall_mem_cons.2 ⟨subd11_0_590, List.forall_mem_cons.2 ⟨subd11_0_591, List.forall_mem_cons.2 ⟨subd11_0_592, List.forall_mem_cons.2 ⟨subd11_0_593, List.forall_mem_cons.2 ⟨subd11_0_594, List.forall_mem_cons.2 ⟨subd11_0_595, List.forall_mem_cons.2 ⟨subd11_0_596, List.forall_mem_cons.2 ⟨subd11_0_597, List.forall_mem_cons.2 ⟨subd11_0_598, List.forall_mem_cons.2 ⟨subd11_0_599, List.forall_mem_cons.2 ⟨subd11_0_600, List.forall_mem_cons.2 ⟨subd11_0_601, List.forall_mem_cons.2 ⟨subd11_0_602, List.forall_mem_cons.2 ⟨subd11_0_603, List.forall_mem_cons.2 ⟨subd11_0_604, List.forall_mem_cons.2 ⟨subd11_0_605, List.forall_mem_cons.2 ⟨subd11_0_606, List.forall_mem_cons.2 ⟨subd11_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
