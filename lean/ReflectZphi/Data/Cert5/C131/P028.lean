import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_0_160 : subd13_0 [-1, 1, 3] = true := by decide +kernel
theorem subd13_0_161 : subd13_0 [-1, 1, 4] = true := by decide +kernel
theorem subd13_0_162 : subd13_0 [-1, 1, 5] = true := by decide +kernel
theorem subd13_0_163 : subd13_0 [-1, 1, 6] = true := by decide +kernel
theorem subd13_0_164 : subd13_0 [-1, 2, -7] = true := by decide +kernel
theorem subd13_0_165 : subd13_0 [-1, 2, -6] = true := by decide +kernel
theorem subd13_0_166 : subd13_0 [-1, 2, -5] = true := by decide +kernel
theorem subd13_0_167 : subd13_0 [-1, 2, -4] = true := by decide +kernel
theorem subd13_0_168 : subd13_0 [-1, 2, -3] = true := by decide +kernel
theorem subd13_0_169 : subd13_0 [-1, 2, -2] = true := by decide +kernel
theorem subd13_0_170 : subd13_0 [-1, 2, -1] = true := by decide +kernel
theorem subd13_0_171 : subd13_0 [-1, 2, 0] = true := by decide +kernel
theorem subd13_0_172 : subd13_0 [-1, 2, 1] = true := by decide +kernel
theorem subd13_0_173 : subd13_0 [-1, 2, 2] = true := by decide +kernel
theorem subd13_0_174 : subd13_0 [-1, 2, 3] = true := by decide +kernel
theorem subd13_0_175 : subd13_0 [-1, 2, 4] = true := by decide +kernel
theorem subd13_0_176 : subd13_0 [-1, 2, 5] = true := by decide +kernel
theorem subd13_0_177 : subd13_0 [-1, 2, 6] = true := by decide +kernel
theorem subd13_0_178 : subd13_0 [-1, 3] = true := by decide +kernel
theorem subd13_0_179 : subd13_0 [-1, 4] = true := by decide +kernel
theorem subd13_0_180 : subd13_0 [-1, 5] = true := by decide +kernel
theorem subd13_0_181 : subd13_0 [0, -6] = true := by decide +kernel
theorem subd13_0_182 : subd13_0 [0, -5] = true := by decide +kernel
theorem subd13_0_183 : subd13_0 [0, -4] = true := by decide +kernel
theorem subd13_0_184 : subd13_0 [0, -3] = true := by decide +kernel
theorem subd13_0_185 : subd13_0 [0, -2, -7] = true := by decide +kernel
theorem subd13_0_186 : subd13_0 [0, -2, -6] = true := by decide +kernel
theorem subd13_0_187 : subd13_0 [0, -2, -5] = true := by decide +kernel
theorem subd13_0_188 : subd13_0 [0, -2, -4] = true := by decide +kernel
theorem subd13_0_189 : subd13_0 [0, -2, -3] = true := by decide +kernel
theorem subd13_0_190 : subd13_0 [0, -2, -2] = true := by decide +kernel
theorem subd13_0_191 : subd13_0 [0, -2, -1] = true := by decide +kernel
theorem sbd13_0_5 : ∀ q ∈ blkd13_0_5, subd13_0 q = true := by
  unfold blkd13_0_5
  exact List.forall_mem_cons.2 ⟨subd13_0_160, List.forall_mem_cons.2 ⟨subd13_0_161, List.forall_mem_cons.2 ⟨subd13_0_162, List.forall_mem_cons.2 ⟨subd13_0_163, List.forall_mem_cons.2 ⟨subd13_0_164, List.forall_mem_cons.2 ⟨subd13_0_165, List.forall_mem_cons.2 ⟨subd13_0_166, List.forall_mem_cons.2 ⟨subd13_0_167, List.forall_mem_cons.2 ⟨subd13_0_168, List.forall_mem_cons.2 ⟨subd13_0_169, List.forall_mem_cons.2 ⟨subd13_0_170, List.forall_mem_cons.2 ⟨subd13_0_171, List.forall_mem_cons.2 ⟨subd13_0_172, List.forall_mem_cons.2 ⟨subd13_0_173, List.forall_mem_cons.2 ⟨subd13_0_174, List.forall_mem_cons.2 ⟨subd13_0_175, List.forall_mem_cons.2 ⟨subd13_0_176, List.forall_mem_cons.2 ⟨subd13_0_177, List.forall_mem_cons.2 ⟨subd13_0_178, List.forall_mem_cons.2 ⟨subd13_0_179, List.forall_mem_cons.2 ⟨subd13_0_180, List.forall_mem_cons.2 ⟨subd13_0_181, List.forall_mem_cons.2 ⟨subd13_0_182, List.forall_mem_cons.2 ⟨subd13_0_183, List.forall_mem_cons.2 ⟨subd13_0_184, List.forall_mem_cons.2 ⟨subd13_0_185, List.forall_mem_cons.2 ⟨subd13_0_186, List.forall_mem_cons.2 ⟨subd13_0_187, List.forall_mem_cons.2 ⟨subd13_0_188, List.forall_mem_cons.2 ⟨subd13_0_189, List.forall_mem_cons.2 ⟨subd13_0_190, List.forall_mem_cons.2 ⟨subd13_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_192 : subd13_0 [0, -2, 0] = true := by decide +kernel
theorem subd13_0_193 : subd13_0 [0, -2, 1] = true := by decide +kernel
theorem subd13_0_194 : subd13_0 [0, -2, 2] = true := by decide +kernel
theorem subd13_0_195 : subd13_0 [0, -2, 3] = true := by decide +kernel
theorem subd13_0_196 : subd13_0 [0, -2, 4] = true := by decide +kernel
theorem subd13_0_197 : subd13_0 [0, -2, 5] = true := by decide +kernel
theorem subd13_0_198 : subd13_0 [0, -2, 6] = true := by decide +kernel
theorem subd13_0_199 : subd13_0 [0, -1, -7] = true := by decide +kernel
theorem subd13_0_200 : subd13_0 [0, -1, -6] = true := by decide +kernel
theorem subd13_0_201 : subd13_0 [0, -1, -5] = true := by decide +kernel
theorem subd13_0_202 : subd13_0 [0, -1, -4] = true := by decide +kernel
theorem subd13_0_203 : subd13_0 [0, -1, -3] = true := by decide +kernel
theorem subd13_0_204 : subd13_0 [0, -1, -2] = true := by decide +kernel
theorem subd13_0_205 : subd13_0 [0, -1, -1] = true := by decide +kernel
theorem subd13_0_206 : subd13_0 [0, -1, 0] = true := by decide +kernel
theorem subd13_0_207 : subd13_0 [0, -1, 1] = true := by decide +kernel
theorem subd13_0_208 : subd13_0 [0, -1, 2] = true := by decide +kernel
theorem subd13_0_209 : subd13_0 [0, -1, 3] = true := by decide +kernel
theorem subd13_0_210 : subd13_0 [0, -1, 4] = true := by decide +kernel
theorem subd13_0_211 : subd13_0 [0, -1, 5] = true := by decide +kernel
theorem subd13_0_212 : subd13_0 [0, -1, 6] = true := by decide +kernel
theorem subd13_0_213 : subd13_0 [0, 0, -7] = true := by decide +kernel
theorem subd13_0_214 : subd13_0 [0, 0, -6] = true := by decide +kernel
theorem subd13_0_215 : subd13_0 [0, 0, -5] = true := by decide +kernel
theorem subd13_0_216 : subd13_0 [0, 0, -4] = true := by decide +kernel
theorem subd13_0_217 : subd13_0 [0, 0, -3] = true := by decide +kernel
theorem subd13_0_218 : subd13_0 [0, 0, -2] = true := by decide +kernel
theorem subd13_0_219 : subd13_0 [0, 0, -1] = true := by decide +kernel
theorem subd13_0_220 : subd13_0 [0, 0, 0] = true := by decide +kernel
theorem subd13_0_221 : subd13_0 [0, 0, 1] = true := by decide +kernel
theorem subd13_0_222 : subd13_0 [0, 0, 2] = true := by decide +kernel
theorem subd13_0_223 : subd13_0 [0, 0, 3] = true := by decide +kernel
theorem sbd13_0_6 : ∀ q ∈ blkd13_0_6, subd13_0 q = true := by
  unfold blkd13_0_6
  exact List.forall_mem_cons.2 ⟨subd13_0_192, List.forall_mem_cons.2 ⟨subd13_0_193, List.forall_mem_cons.2 ⟨subd13_0_194, List.forall_mem_cons.2 ⟨subd13_0_195, List.forall_mem_cons.2 ⟨subd13_0_196, List.forall_mem_cons.2 ⟨subd13_0_197, List.forall_mem_cons.2 ⟨subd13_0_198, List.forall_mem_cons.2 ⟨subd13_0_199, List.forall_mem_cons.2 ⟨subd13_0_200, List.forall_mem_cons.2 ⟨subd13_0_201, List.forall_mem_cons.2 ⟨subd13_0_202, List.forall_mem_cons.2 ⟨subd13_0_203, List.forall_mem_cons.2 ⟨subd13_0_204, List.forall_mem_cons.2 ⟨subd13_0_205, List.forall_mem_cons.2 ⟨subd13_0_206, List.forall_mem_cons.2 ⟨subd13_0_207, List.forall_mem_cons.2 ⟨subd13_0_208, List.forall_mem_cons.2 ⟨subd13_0_209, List.forall_mem_cons.2 ⟨subd13_0_210, List.forall_mem_cons.2 ⟨subd13_0_211, List.forall_mem_cons.2 ⟨subd13_0_212, List.forall_mem_cons.2 ⟨subd13_0_213, List.forall_mem_cons.2 ⟨subd13_0_214, List.forall_mem_cons.2 ⟨subd13_0_215, List.forall_mem_cons.2 ⟨subd13_0_216, List.forall_mem_cons.2 ⟨subd13_0_217, List.forall_mem_cons.2 ⟨subd13_0_218, List.forall_mem_cons.2 ⟨subd13_0_219, List.forall_mem_cons.2 ⟨subd13_0_220, List.forall_mem_cons.2 ⟨subd13_0_221, List.forall_mem_cons.2 ⟨subd13_0_222, List.forall_mem_cons.2 ⟨subd13_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_224 : subd13_0 [0, 0, 4] = true := by decide +kernel
theorem subd13_0_225 : subd13_0 [0, 0, 5] = true := by decide +kernel
theorem subd13_0_226 : subd13_0 [0, 0, 6] = true := by decide +kernel
theorem subd13_0_227 : subd13_0 [0, 1, -7] = true := by decide +kernel
theorem subd13_0_228 : subd13_0 [0, 1, -6] = true := by decide +kernel
theorem subd13_0_229 : subd13_0 [0, 1, -5] = true := by decide +kernel
theorem subd13_0_230 : subd13_0 [0, 1, -4] = true := by decide +kernel
theorem subd13_0_231 : subd13_0 [0, 1, -3] = true := by decide +kernel
theorem subd13_0_232 : subd13_0 [0, 1, -2] = true := by decide +kernel
theorem subd13_0_233 : subd13_0 [0, 1, -1] = true := by decide +kernel
theorem subd13_0_234 : subd13_0 [0, 1, 0] = true := by decide +kernel
theorem subd13_0_235 : subd13_0 [0, 1, 1] = true := by decide +kernel
theorem subd13_0_236 : subd13_0 [0, 1, 2] = true := by decide +kernel
theorem subd13_0_237 : subd13_0 [0, 1, 3] = true := by decide +kernel
theorem subd13_0_238 : subd13_0 [0, 1, 4] = true := by decide +kernel
theorem subd13_0_239 : subd13_0 [0, 1, 5] = true := by decide +kernel
theorem subd13_0_240 : subd13_0 [0, 1, 6] = true := by decide +kernel
theorem subd13_0_241 : subd13_0 [0, 2, -7] = true := by decide +kernel
theorem subd13_0_242 : subd13_0 [0, 2, -6] = true := by decide +kernel
theorem subd13_0_243 : subd13_0 [0, 2, -5] = true := by decide +kernel
theorem subd13_0_244 : subd13_0 [0, 2, -4] = true := by decide +kernel
theorem subd13_0_245 : subd13_0 [0, 2, -3] = true := by decide +kernel
theorem subd13_0_246 : subd13_0 [0, 2, -2] = true := by decide +kernel
theorem subd13_0_247 : subd13_0 [0, 2, -1] = true := by decide +kernel
theorem subd13_0_248 : subd13_0 [0, 2, 0] = true := by decide +kernel
theorem subd13_0_249 : subd13_0 [0, 2, 1] = true := by decide +kernel
theorem subd13_0_250 : subd13_0 [0, 2, 2] = true := by decide +kernel
theorem subd13_0_251 : subd13_0 [0, 2, 3] = true := by decide +kernel
theorem subd13_0_252 : subd13_0 [0, 2, 4] = true := by decide +kernel
theorem subd13_0_253 : subd13_0 [0, 2, 5] = true := by decide +kernel
theorem subd13_0_254 : subd13_0 [0, 2, 6] = true := by decide +kernel
theorem subd13_0_255 : subd13_0 [0, 3] = true := by decide +kernel
theorem sbd13_0_7 : ∀ q ∈ blkd13_0_7, subd13_0 q = true := by
  unfold blkd13_0_7
  exact List.forall_mem_cons.2 ⟨subd13_0_224, List.forall_mem_cons.2 ⟨subd13_0_225, List.forall_mem_cons.2 ⟨subd13_0_226, List.forall_mem_cons.2 ⟨subd13_0_227, List.forall_mem_cons.2 ⟨subd13_0_228, List.forall_mem_cons.2 ⟨subd13_0_229, List.forall_mem_cons.2 ⟨subd13_0_230, List.forall_mem_cons.2 ⟨subd13_0_231, List.forall_mem_cons.2 ⟨subd13_0_232, List.forall_mem_cons.2 ⟨subd13_0_233, List.forall_mem_cons.2 ⟨subd13_0_234, List.forall_mem_cons.2 ⟨subd13_0_235, List.forall_mem_cons.2 ⟨subd13_0_236, List.forall_mem_cons.2 ⟨subd13_0_237, List.forall_mem_cons.2 ⟨subd13_0_238, List.forall_mem_cons.2 ⟨subd13_0_239, List.forall_mem_cons.2 ⟨subd13_0_240, List.forall_mem_cons.2 ⟨subd13_0_241, List.forall_mem_cons.2 ⟨subd13_0_242, List.forall_mem_cons.2 ⟨subd13_0_243, List.forall_mem_cons.2 ⟨subd13_0_244, List.forall_mem_cons.2 ⟨subd13_0_245, List.forall_mem_cons.2 ⟨subd13_0_246, List.forall_mem_cons.2 ⟨subd13_0_247, List.forall_mem_cons.2 ⟨subd13_0_248, List.forall_mem_cons.2 ⟨subd13_0_249, List.forall_mem_cons.2 ⟨subd13_0_250, List.forall_mem_cons.2 ⟨subd13_0_251, List.forall_mem_cons.2 ⟨subd13_0_252, List.forall_mem_cons.2 ⟨subd13_0_253, List.forall_mem_cons.2 ⟨subd13_0_254, List.forall_mem_cons.2 ⟨subd13_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_256 : subd13_0 [0, 4] = true := by decide +kernel
theorem subd13_0_257 : subd13_0 [0, 5] = true := by decide +kernel
theorem subd13_0_258 : subd13_0 [1, -6] = true := by decide +kernel
theorem subd13_0_259 : subd13_0 [1, -5] = true := by decide +kernel
theorem subd13_0_260 : subd13_0 [1, -4] = true := by decide +kernel
theorem subd13_0_261 : subd13_0 [1, -3] = true := by decide +kernel
theorem subd13_0_262 : subd13_0 [1, -2, -7] = true := by decide +kernel
theorem subd13_0_263 : subd13_0 [1, -2, -6] = true := by decide +kernel
theorem subd13_0_264 : subd13_0 [1, -2, -5] = true := by decide +kernel
theorem subd13_0_265 : subd13_0 [1, -2, -4] = true := by decide +kernel
theorem subd13_0_266 : subd13_0 [1, -2, -3] = true := by decide +kernel
theorem subd13_0_267 : subd13_0 [1, -2, -2] = true := by decide +kernel
theorem subd13_0_268 : subd13_0 [1, -2, -1] = true := by decide +kernel
theorem subd13_0_269 : subd13_0 [1, -2, 0] = true := by decide +kernel
theorem subd13_0_270 : subd13_0 [1, -2, 1] = true := by decide +kernel
theorem subd13_0_271 : subd13_0 [1, -2, 2] = true := by decide +kernel
theorem subd13_0_272 : subd13_0 [1, -2, 3] = true := by decide +kernel
theorem subd13_0_273 : subd13_0 [1, -2, 4] = true := by decide +kernel
theorem subd13_0_274 : subd13_0 [1, -2, 5] = true := by decide +kernel
theorem subd13_0_275 : subd13_0 [1, -2, 6] = true := by decide +kernel
theorem subd13_0_276 : subd13_0 [1, -1, -7] = true := by decide +kernel
theorem subd13_0_277 : subd13_0 [1, -1, -6] = true := by decide +kernel
theorem subd13_0_278 : subd13_0 [1, -1, -5] = true := by decide +kernel
theorem subd13_0_279 : subd13_0 [1, -1, -4] = true := by decide +kernel
theorem subd13_0_280 : subd13_0 [1, -1, -3] = true := by decide +kernel
theorem subd13_0_281 : subd13_0 [1, -1, -2] = true := by decide +kernel
theorem subd13_0_282 : subd13_0 [1, -1, -1] = true := by decide +kernel
theorem subd13_0_283 : subd13_0 [1, -1, 0] = true := by decide +kernel
theorem subd13_0_284 : subd13_0 [1, -1, 1] = true := by decide +kernel
theorem subd13_0_285 : subd13_0 [1, -1, 2] = true := by decide +kernel
theorem subd13_0_286 : subd13_0 [1, -1, 3] = true := by decide +kernel
theorem subd13_0_287 : subd13_0 [1, -1, 4] = true := by decide +kernel
theorem sbd13_0_8 : ∀ q ∈ blkd13_0_8, subd13_0 q = true := by
  unfold blkd13_0_8
  exact List.forall_mem_cons.2 ⟨subd13_0_256, List.forall_mem_cons.2 ⟨subd13_0_257, List.forall_mem_cons.2 ⟨subd13_0_258, List.forall_mem_cons.2 ⟨subd13_0_259, List.forall_mem_cons.2 ⟨subd13_0_260, List.forall_mem_cons.2 ⟨subd13_0_261, List.forall_mem_cons.2 ⟨subd13_0_262, List.forall_mem_cons.2 ⟨subd13_0_263, List.forall_mem_cons.2 ⟨subd13_0_264, List.forall_mem_cons.2 ⟨subd13_0_265, List.forall_mem_cons.2 ⟨subd13_0_266, List.forall_mem_cons.2 ⟨subd13_0_267, List.forall_mem_cons.2 ⟨subd13_0_268, List.forall_mem_cons.2 ⟨subd13_0_269, List.forall_mem_cons.2 ⟨subd13_0_270, List.forall_mem_cons.2 ⟨subd13_0_271, List.forall_mem_cons.2 ⟨subd13_0_272, List.forall_mem_cons.2 ⟨subd13_0_273, List.forall_mem_cons.2 ⟨subd13_0_274, List.forall_mem_cons.2 ⟨subd13_0_275, List.forall_mem_cons.2 ⟨subd13_0_276, List.forall_mem_cons.2 ⟨subd13_0_277, List.forall_mem_cons.2 ⟨subd13_0_278, List.forall_mem_cons.2 ⟨subd13_0_279, List.forall_mem_cons.2 ⟨subd13_0_280, List.forall_mem_cons.2 ⟨subd13_0_281, List.forall_mem_cons.2 ⟨subd13_0_282, List.forall_mem_cons.2 ⟨subd13_0_283, List.forall_mem_cons.2 ⟨subd13_0_284, List.forall_mem_cons.2 ⟨subd13_0_285, List.forall_mem_cons.2 ⟨subd13_0_286, List.forall_mem_cons.2 ⟨subd13_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_288 : subd13_0 [1, -1, 5] = true := by decide +kernel
theorem subd13_0_289 : subd13_0 [1, -1, 6] = true := by decide +kernel
theorem subd13_0_290 : subd13_0 [1, 0, -8] = true := by decide +kernel
theorem subd13_0_291 : subd13_0 [1, 0, -7] = true := by decide +kernel
theorem subd13_0_292 : subd13_0 [1, 0, -6] = true := by decide +kernel
theorem subd13_0_293 : subd13_0 [1, 0, -5] = true := by decide +kernel
theorem subd13_0_294 : subd13_0 [1, 0, -4] = true := by decide +kernel
theorem subd13_0_295 : subd13_0 [1, 0, -3] = true := by decide +kernel
theorem subd13_0_296 : subd13_0 [1, 0, -2] = true := by decide +kernel
theorem subd13_0_297 : subd13_0 [1, 0, -1] = true := by decide +kernel
theorem subd13_0_298 : subd13_0 [1, 0, 0] = true := by decide +kernel
theorem subd13_0_299 : subd13_0 [1, 0, 1] = true := by decide +kernel
theorem subd13_0_300 : subd13_0 [1, 0, 2] = true := by decide +kernel
theorem subd13_0_301 : subd13_0 [1, 0, 3] = true := by decide +kernel
theorem subd13_0_302 : subd13_0 [1, 0, 4] = true := by decide +kernel
theorem subd13_0_303 : subd13_0 [1, 0, 5] = true := by decide +kernel
theorem subd13_0_304 : subd13_0 [1, 0, 6] = true := by decide +kernel
theorem subd13_0_305 : subd13_0 [1, 1, -8] = true := by decide +kernel
theorem subd13_0_306 : subd13_0 [1, 1, -7] = true := by decide +kernel
theorem subd13_0_307 : subd13_0 [1, 1, -6] = true := by decide +kernel
theorem subd13_0_308 : subd13_0 [1, 1, -5] = true := by decide +kernel
theorem subd13_0_309 : subd13_0 [1, 1, -4] = true := by decide +kernel
theorem subd13_0_310 : subd13_0 [1, 1, -3] = true := by decide +kernel
theorem subd13_0_311 : subd13_0 [1, 1, -2] = true := by decide +kernel
theorem subd13_0_312 : subd13_0 [1, 1, -1] = true := by decide +kernel
theorem subd13_0_313 : subd13_0 [1, 1, 0] = true := by decide +kernel
theorem subd13_0_314 : subd13_0 [1, 1, 1] = true := by decide +kernel
theorem subd13_0_315 : subd13_0 [1, 1, 2] = true := by decide +kernel
theorem subd13_0_316 : subd13_0 [1, 1, 3] = true := by decide +kernel
theorem subd13_0_317 : subd13_0 [1, 1, 4] = true := by decide +kernel
theorem subd13_0_318 : subd13_0 [1, 1, 5] = true := by decide +kernel
theorem subd13_0_319 : subd13_0 [1, 1, 6] = true := by decide +kernel
theorem sbd13_0_9 : ∀ q ∈ blkd13_0_9, subd13_0 q = true := by
  unfold blkd13_0_9
  exact List.forall_mem_cons.2 ⟨subd13_0_288, List.forall_mem_cons.2 ⟨subd13_0_289, List.forall_mem_cons.2 ⟨subd13_0_290, List.forall_mem_cons.2 ⟨subd13_0_291, List.forall_mem_cons.2 ⟨subd13_0_292, List.forall_mem_cons.2 ⟨subd13_0_293, List.forall_mem_cons.2 ⟨subd13_0_294, List.forall_mem_cons.2 ⟨subd13_0_295, List.forall_mem_cons.2 ⟨subd13_0_296, List.forall_mem_cons.2 ⟨subd13_0_297, List.forall_mem_cons.2 ⟨subd13_0_298, List.forall_mem_cons.2 ⟨subd13_0_299, List.forall_mem_cons.2 ⟨subd13_0_300, List.forall_mem_cons.2 ⟨subd13_0_301, List.forall_mem_cons.2 ⟨subd13_0_302, List.forall_mem_cons.2 ⟨subd13_0_303, List.forall_mem_cons.2 ⟨subd13_0_304, List.forall_mem_cons.2 ⟨subd13_0_305, List.forall_mem_cons.2 ⟨subd13_0_306, List.forall_mem_cons.2 ⟨subd13_0_307, List.forall_mem_cons.2 ⟨subd13_0_308, List.forall_mem_cons.2 ⟨subd13_0_309, List.forall_mem_cons.2 ⟨subd13_0_310, List.forall_mem_cons.2 ⟨subd13_0_311, List.forall_mem_cons.2 ⟨subd13_0_312, List.forall_mem_cons.2 ⟨subd13_0_313, List.forall_mem_cons.2 ⟨subd13_0_314, List.forall_mem_cons.2 ⟨subd13_0_315, List.forall_mem_cons.2 ⟨subd13_0_316, List.forall_mem_cons.2 ⟨subd13_0_317, List.forall_mem_cons.2 ⟨subd13_0_318, List.forall_mem_cons.2 ⟨subd13_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_320 : subd13_0 [1, 2, -8] = true := by decide +kernel
theorem subd13_0_321 : subd13_0 [1, 2, -7] = true := by decide +kernel
theorem subd13_0_322 : subd13_0 [1, 2, -6] = true := by decide +kernel
theorem subd13_0_323 : subd13_0 [1, 2, -5] = true := by decide +kernel
theorem subd13_0_324 : subd13_0 [1, 2, -4] = true := by decide +kernel
theorem subd13_0_325 : subd13_0 [1, 2, -3] = true := by decide +kernel
theorem subd13_0_326 : subd13_0 [1, 2, -2] = true := by decide +kernel
theorem subd13_0_327 : subd13_0 [1, 2, -1] = true := by decide +kernel
theorem subd13_0_328 : subd13_0 [1, 2, 0] = true := by decide +kernel
theorem subd13_0_329 : subd13_0 [1, 2, 1] = true := by decide +kernel
theorem subd13_0_330 : subd13_0 [1, 2, 2] = true := by decide +kernel
theorem subd13_0_331 : subd13_0 [1, 2, 3] = true := by decide +kernel
theorem subd13_0_332 : subd13_0 [1, 2, 4] = true := by decide +kernel
theorem subd13_0_333 : subd13_0 [1, 2, 5] = true := by decide +kernel
theorem subd13_0_334 : subd13_0 [1, 3] = true := by decide +kernel
theorem subd13_0_335 : subd13_0 [1, 4] = true := by decide +kernel
theorem subd13_0_336 : subd13_0 [1, 5] = true := by decide +kernel
theorem subd13_0_337 : subd13_0 [1, 6] = true := by decide +kernel
theorem subd13_0_338 : subd13_0 [2, -6] = true := by decide +kernel
theorem subd13_0_339 : subd13_0 [2, -5] = true := by decide +kernel
theorem subd13_0_340 : subd13_0 [2, -4] = true := by decide +kernel
theorem subd13_0_341 : subd13_0 [2, -3] = true := by decide +kernel
theorem subd13_0_342 : subd13_0 [2, -2] = true := by decide +kernel
theorem subd13_0_343 : subd13_0 [2, -1, -8] = true := by decide +kernel
theorem subd13_0_344 : subd13_0 [2, -1, -7] = true := by decide +kernel
theorem subd13_0_345 : subd13_0 [2, -1, -6] = true := by decide +kernel
theorem subd13_0_346 : subd13_0 [2, -1, -5] = true := by decide +kernel
theorem subd13_0_347 : subd13_0 [2, -1, -4] = true := by decide +kernel
theorem subd13_0_348 : subd13_0 [2, -1, -3] = true := by decide +kernel
theorem subd13_0_349 : subd13_0 [2, -1, -2] = true := by decide +kernel
theorem subd13_0_350 : subd13_0 [2, -1, -1] = true := by decide +kernel
theorem subd13_0_351 : subd13_0 [2, -1, 0] = true := by decide +kernel
theorem sbd13_0_10 : ∀ q ∈ blkd13_0_10, subd13_0 q = true := by
  unfold blkd13_0_10
  exact List.forall_mem_cons.2 ⟨subd13_0_320, List.forall_mem_cons.2 ⟨subd13_0_321, List.forall_mem_cons.2 ⟨subd13_0_322, List.forall_mem_cons.2 ⟨subd13_0_323, List.forall_mem_cons.2 ⟨subd13_0_324, List.forall_mem_cons.2 ⟨subd13_0_325, List.forall_mem_cons.2 ⟨subd13_0_326, List.forall_mem_cons.2 ⟨subd13_0_327, List.forall_mem_cons.2 ⟨subd13_0_328, List.forall_mem_cons.2 ⟨subd13_0_329, List.forall_mem_cons.2 ⟨subd13_0_330, List.forall_mem_cons.2 ⟨subd13_0_331, List.forall_mem_cons.2 ⟨subd13_0_332, List.forall_mem_cons.2 ⟨subd13_0_333, List.forall_mem_cons.2 ⟨subd13_0_334, List.forall_mem_cons.2 ⟨subd13_0_335, List.forall_mem_cons.2 ⟨subd13_0_336, List.forall_mem_cons.2 ⟨subd13_0_337, List.forall_mem_cons.2 ⟨subd13_0_338, List.forall_mem_cons.2 ⟨subd13_0_339, List.forall_mem_cons.2 ⟨subd13_0_340, List.forall_mem_cons.2 ⟨subd13_0_341, List.forall_mem_cons.2 ⟨subd13_0_342, List.forall_mem_cons.2 ⟨subd13_0_343, List.forall_mem_cons.2 ⟨subd13_0_344, List.forall_mem_cons.2 ⟨subd13_0_345, List.forall_mem_cons.2 ⟨subd13_0_346, List.forall_mem_cons.2 ⟨subd13_0_347, List.forall_mem_cons.2 ⟨subd13_0_348, List.forall_mem_cons.2 ⟨subd13_0_349, List.forall_mem_cons.2 ⟨subd13_0_350, List.forall_mem_cons.2 ⟨subd13_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_352 : subd13_0 [2, -1, 1] = true := by decide +kernel
theorem subd13_0_353 : subd13_0 [2, -1, 2] = true := by decide +kernel
theorem subd13_0_354 : subd13_0 [2, -1, 3] = true := by decide +kernel
theorem subd13_0_355 : subd13_0 [2, -1, 4] = true := by decide +kernel
theorem subd13_0_356 : subd13_0 [2, -1, 5] = true := by decide +kernel
theorem subd13_0_357 : subd13_0 [2, 0, -8] = true := by decide +kernel
theorem subd13_0_358 : subd13_0 [2, 0, -7] = true := by decide +kernel
theorem subd13_0_359 : subd13_0 [2, 0, -6] = true := by decide +kernel
theorem subd13_0_360 : subd13_0 [2, 0, -5] = true := by decide +kernel
theorem subd13_0_361 : subd13_0 [2, 0, -4] = true := by decide +kernel
theorem subd13_0_362 : subd13_0 [2, 0, -3] = true := by decide +kernel
theorem subd13_0_363 : subd13_0 [2, 0, -2] = true := by decide +kernel
theorem subd13_0_364 : subd13_0 [2, 0, -1] = true := by decide +kernel
theorem subd13_0_365 : subd13_0 [2, 0, 0] = true := by decide +kernel
theorem subd13_0_366 : subd13_0 [2, 0, 1] = true := by decide +kernel
theorem subd13_0_367 : subd13_0 [2, 0, 2] = true := by decide +kernel
theorem subd13_0_368 : subd13_0 [2, 0, 3] = true := by decide +kernel
theorem subd13_0_369 : subd13_0 [2, 0, 4] = true := by decide +kernel
theorem subd13_0_370 : subd13_0 [2, 0, 5] = true := by decide +kernel
theorem subd13_0_371 : subd13_0 [2, 1, -8] = true := by decide +kernel
theorem subd13_0_372 : subd13_0 [2, 1, -7] = true := by decide +kernel
theorem subd13_0_373 : subd13_0 [2, 1, -6] = true := by decide +kernel
theorem subd13_0_374 : subd13_0 [2, 1, -5] = true := by decide +kernel
theorem subd13_0_375 : subd13_0 [2, 1, -4] = true := by decide +kernel
theorem subd13_0_376 : subd13_0 [2, 1, -3] = true := by decide +kernel
theorem subd13_0_377 : subd13_0 [2, 1, -2] = true := by decide +kernel
theorem subd13_0_378 : subd13_0 [2, 1, -1] = true := by decide +kernel
theorem subd13_0_379 : subd13_0 [2, 1, 0] = true := by decide +kernel
theorem subd13_0_380 : subd13_0 [2, 1, 1] = true := by decide +kernel
theorem subd13_0_381 : subd13_0 [2, 1, 2] = true := by decide +kernel
theorem subd13_0_382 : subd13_0 [2, 1, 3] = true := by decide +kernel
theorem subd13_0_383 : subd13_0 [2, 1, 4] = true := by decide +kernel
theorem sbd13_0_11 : ∀ q ∈ blkd13_0_11, subd13_0 q = true := by
  unfold blkd13_0_11
  exact List.forall_mem_cons.2 ⟨subd13_0_352, List.forall_mem_cons.2 ⟨subd13_0_353, List.forall_mem_cons.2 ⟨subd13_0_354, List.forall_mem_cons.2 ⟨subd13_0_355, List.forall_mem_cons.2 ⟨subd13_0_356, List.forall_mem_cons.2 ⟨subd13_0_357, List.forall_mem_cons.2 ⟨subd13_0_358, List.forall_mem_cons.2 ⟨subd13_0_359, List.forall_mem_cons.2 ⟨subd13_0_360, List.forall_mem_cons.2 ⟨subd13_0_361, List.forall_mem_cons.2 ⟨subd13_0_362, List.forall_mem_cons.2 ⟨subd13_0_363, List.forall_mem_cons.2 ⟨subd13_0_364, List.forall_mem_cons.2 ⟨subd13_0_365, List.forall_mem_cons.2 ⟨subd13_0_366, List.forall_mem_cons.2 ⟨subd13_0_367, List.forall_mem_cons.2 ⟨subd13_0_368, List.forall_mem_cons.2 ⟨subd13_0_369, List.forall_mem_cons.2 ⟨subd13_0_370, List.forall_mem_cons.2 ⟨subd13_0_371, List.forall_mem_cons.2 ⟨subd13_0_372, List.forall_mem_cons.2 ⟨subd13_0_373, List.forall_mem_cons.2 ⟨subd13_0_374, List.forall_mem_cons.2 ⟨subd13_0_375, List.forall_mem_cons.2 ⟨subd13_0_376, List.forall_mem_cons.2 ⟨subd13_0_377, List.forall_mem_cons.2 ⟨subd13_0_378, List.forall_mem_cons.2 ⟨subd13_0_379, List.forall_mem_cons.2 ⟨subd13_0_380, List.forall_mem_cons.2 ⟨subd13_0_381, List.forall_mem_cons.2 ⟨subd13_0_382, List.forall_mem_cons.2 ⟨subd13_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_384 : subd13_0 [2, 1, 5] = true := by decide +kernel
theorem subd13_0_385 : subd13_0 [2, 2, -8] = true := by decide +kernel
theorem subd13_0_386 : subd13_0 [2, 2, -7] = true := by decide +kernel
theorem subd13_0_387 : subd13_0 [2, 2, -6] = true := by decide +kernel
theorem subd13_0_388 : subd13_0 [2, 2, -5] = true := by decide +kernel
theorem subd13_0_389 : subd13_0 [2, 2, -4] = true := by decide +kernel
theorem subd13_0_390 : subd13_0 [2, 2, -3] = true := by decide +kernel
theorem subd13_0_391 : subd13_0 [2, 2, -2] = true := by decide +kernel
theorem subd13_0_392 : subd13_0 [2, 2, -1] = true := by decide +kernel
theorem subd13_0_393 : subd13_0 [2, 2, 0] = true := by decide +kernel
theorem subd13_0_394 : subd13_0 [2, 2, 1] = true := by decide +kernel
theorem subd13_0_395 : subd13_0 [2, 2, 2] = true := by decide +kernel
theorem subd13_0_396 : subd13_0 [2, 2, 3] = true := by decide +kernel
theorem subd13_0_397 : subd13_0 [2, 2, 4] = true := by decide +kernel
theorem subd13_0_398 : subd13_0 [2, 3] = true := by decide +kernel
theorem subd13_0_399 : subd13_0 [2, 4] = true := by decide +kernel
theorem subd13_0_400 : subd13_0 [2, 5] = true := by decide +kernel
theorem subd13_0_401 : subd13_0 [2, 6] = true := by decide +kernel
theorem subd13_0_402 : subd13_0 [3, -5] = true := by decide +kernel
theorem subd13_0_403 : subd13_0 [3, -4] = true := by decide +kernel
theorem subd13_0_404 : subd13_0 [3, -3] = true := by decide +kernel
theorem subd13_0_405 : subd13_0 [3, -2] = true := by decide +kernel
theorem subd13_0_406 : subd13_0 [3, -1] = true := by decide +kernel
theorem subd13_0_407 : subd13_0 [3, 0] = true := by decide +kernel
theorem subd13_0_408 : subd13_0 [3, 1] = true := by decide +kernel
theorem subd13_0_409 : subd13_0 [3, 2] = true := by decide +kernel
theorem subd13_0_410 : subd13_0 [3, 3] = true := by decide +kernel
theorem subd13_0_411 : subd13_0 [3, 4] = true := by decide +kernel
theorem subd13_0_412 : subd13_0 [3, 5] = true := by decide +kernel
theorem subd13_0_413 : subd13_0 [4, -4] = true := by decide +kernel
theorem subd13_0_414 : subd13_0 [4, -3] = true := by decide +kernel
theorem subd13_0_415 : subd13_0 [4, -2] = true := by decide +kernel
theorem sbd13_0_12 : ∀ q ∈ blkd13_0_12, subd13_0 q = true := by
  unfold blkd13_0_12
  exact List.forall_mem_cons.2 ⟨subd13_0_384, List.forall_mem_cons.2 ⟨subd13_0_385, List.forall_mem_cons.2 ⟨subd13_0_386, List.forall_mem_cons.2 ⟨subd13_0_387, List.forall_mem_cons.2 ⟨subd13_0_388, List.forall_mem_cons.2 ⟨subd13_0_389, List.forall_mem_cons.2 ⟨subd13_0_390, List.forall_mem_cons.2 ⟨subd13_0_391, List.forall_mem_cons.2 ⟨subd13_0_392, List.forall_mem_cons.2 ⟨subd13_0_393, List.forall_mem_cons.2 ⟨subd13_0_394, List.forall_mem_cons.2 ⟨subd13_0_395, List.forall_mem_cons.2 ⟨subd13_0_396, List.forall_mem_cons.2 ⟨subd13_0_397, List.forall_mem_cons.2 ⟨subd13_0_398, List.forall_mem_cons.2 ⟨subd13_0_399, List.forall_mem_cons.2 ⟨subd13_0_400, List.forall_mem_cons.2 ⟨subd13_0_401, List.forall_mem_cons.2 ⟨subd13_0_402, List.forall_mem_cons.2 ⟨subd13_0_403, List.forall_mem_cons.2 ⟨subd13_0_404, List.forall_mem_cons.2 ⟨subd13_0_405, List.forall_mem_cons.2 ⟨subd13_0_406, List.forall_mem_cons.2 ⟨subd13_0_407, List.forall_mem_cons.2 ⟨subd13_0_408, List.forall_mem_cons.2 ⟨subd13_0_409, List.forall_mem_cons.2 ⟨subd13_0_410, List.forall_mem_cons.2 ⟨subd13_0_411, List.forall_mem_cons.2 ⟨subd13_0_412, List.forall_mem_cons.2 ⟨subd13_0_413, List.forall_mem_cons.2 ⟨subd13_0_414, List.forall_mem_cons.2 ⟨subd13_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_416 : subd13_0 [4, -1] = true := by decide +kernel
theorem subd13_0_417 : subd13_0 [4, 0] = true := by decide +kernel
theorem subd13_0_418 : subd13_0 [4, 1] = true := by decide +kernel
theorem subd13_0_419 : subd13_0 [4, 2] = true := by decide +kernel
theorem subd13_0_420 : subd13_0 [4, 3] = true := by decide +kernel
theorem subd13_0_421 : subd13_0 [4, 4] = true := by decide +kernel
theorem subd13_0_422 : subd13_0 [4, 5] = true := by decide +kernel
theorem subd13_0_423 : subd13_0 [5, -3] = true := by decide +kernel
theorem subd13_0_424 : subd13_0 [5, -2] = true := by decide +kernel
theorem subd13_0_425 : subd13_0 [5, -1] = true := by decide +kernel
theorem subd13_0_426 : subd13_0 [5, 0] = true := by decide +kernel
theorem subd13_0_427 : subd13_0 [5, 1] = true := by decide +kernel
theorem subd13_0_428 : subd13_0 [5, 2] = true := by decide +kernel
theorem subd13_0_429 : subd13_0 [5, 3] = true := by decide +kernel
theorem subd13_0_430 : subd13_0 [5, 4] = true := by decide +kernel
theorem subd13_0_431 : subd13_0 [5, 5] = true := by decide +kernel
theorem subd13_0_432 : subd13_0 [6, -2] = true := by decide +kernel
theorem subd13_0_433 : subd13_0 [6, -1] = true := by decide +kernel
theorem subd13_0_434 : subd13_0 [6, 0] = true := by decide +kernel
theorem subd13_0_435 : subd13_0 [6, 1] = true := by decide +kernel
theorem subd13_0_436 : subd13_0 [6, 2] = true := by decide +kernel
theorem subd13_0_437 : subd13_0 [6, 3] = true := by decide +kernel
theorem subd13_0_438 : subd13_0 [6, 4] = true := by decide +kernel
theorem sbd13_0_13 : ∀ q ∈ blkd13_0_13, subd13_0 q = true := by
  unfold blkd13_0_13
  exact List.forall_mem_cons.2 ⟨subd13_0_416, List.forall_mem_cons.2 ⟨subd13_0_417, List.forall_mem_cons.2 ⟨subd13_0_418, List.forall_mem_cons.2 ⟨subd13_0_419, List.forall_mem_cons.2 ⟨subd13_0_420, List.forall_mem_cons.2 ⟨subd13_0_421, List.forall_mem_cons.2 ⟨subd13_0_422, List.forall_mem_cons.2 ⟨subd13_0_423, List.forall_mem_cons.2 ⟨subd13_0_424, List.forall_mem_cons.2 ⟨subd13_0_425, List.forall_mem_cons.2 ⟨subd13_0_426, List.forall_mem_cons.2 ⟨subd13_0_427, List.forall_mem_cons.2 ⟨subd13_0_428, List.forall_mem_cons.2 ⟨subd13_0_429, List.forall_mem_cons.2 ⟨subd13_0_430, List.forall_mem_cons.2 ⟨subd13_0_431, List.forall_mem_cons.2 ⟨subd13_0_432, List.forall_mem_cons.2 ⟨subd13_0_433, List.forall_mem_cons.2 ⟨subd13_0_434, List.forall_mem_cons.2 ⟨subd13_0_435, List.forall_mem_cons.2 ⟨subd13_0_436, List.forall_mem_cons.2 ⟨subd13_0_437, List.forall_mem_cons.2 ⟨subd13_0_438, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
