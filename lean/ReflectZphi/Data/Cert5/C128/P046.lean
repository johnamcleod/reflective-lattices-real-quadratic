import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_5_160 : subd7_5 [0, -2, -7] = true := by decide +kernel
theorem subd7_5_161 : subd7_5 [0, -2, -6] = true := by decide +kernel
theorem subd7_5_162 : subd7_5 [0, -2, -5] = true := by decide +kernel
theorem subd7_5_163 : subd7_5 [0, -2, -4] = true := by decide +kernel
theorem subd7_5_164 : subd7_5 [0, -2, -3] = true := by decide +kernel
theorem subd7_5_165 : subd7_5 [0, -2, -2] = true := by decide +kernel
theorem subd7_5_166 : subd7_5 [0, -2, -1] = true := by decide +kernel
theorem subd7_5_167 : subd7_5 [0, -2, 0] = true := by decide +kernel
theorem subd7_5_168 : subd7_5 [0, -2, 1] = true := by decide +kernel
theorem subd7_5_169 : subd7_5 [0, -2, 2] = true := by decide +kernel
theorem subd7_5_170 : subd7_5 [0, -2, 3] = true := by decide +kernel
theorem subd7_5_171 : subd7_5 [0, -2, 4] = true := by decide +kernel
theorem subd7_5_172 : subd7_5 [0, -2, 5] = true := by decide +kernel
theorem subd7_5_173 : subd7_5 [0, -2, 6] = true := by decide +kernel
theorem subd7_5_174 : subd7_5 [0, -1, -7] = true := by decide +kernel
theorem subd7_5_175 : subd7_5 [0, -1, -6] = true := by decide +kernel
theorem subd7_5_176 : subd7_5 [0, -1, -5] = true := by decide +kernel
theorem subd7_5_177 : subd7_5 [0, -1, -4] = true := by decide +kernel
theorem subd7_5_178 : subd7_5 [0, -1, -3] = true := by decide +kernel
theorem subd7_5_179 : subd7_5 [0, -1, -2] = true := by decide +kernel
theorem subd7_5_180 : subd7_5 [0, -1, -1] = true := by decide +kernel
theorem subd7_5_181 : subd7_5 [0, -1, 0] = true := by decide +kernel
theorem subd7_5_182 : subd7_5 [0, -1, 1] = true := by decide +kernel
theorem subd7_5_183 : subd7_5 [0, -1, 2] = true := by decide +kernel
theorem subd7_5_184 : subd7_5 [0, -1, 3] = true := by decide +kernel
theorem subd7_5_185 : subd7_5 [0, -1, 4] = true := by decide +kernel
theorem subd7_5_186 : subd7_5 [0, -1, 5] = true := by decide +kernel
theorem subd7_5_187 : subd7_5 [0, -1, 6] = true := by decide +kernel
theorem subd7_5_188 : subd7_5 [0, 0, -7] = true := by decide +kernel
theorem subd7_5_189 : subd7_5 [0, 0, -6] = true := by decide +kernel
theorem subd7_5_190 : subd7_5 [0, 0, -5] = true := by decide +kernel
theorem subd7_5_191 : subd7_5 [0, 0, -4] = true := by decide +kernel
theorem sbd7_5_5 : ∀ q ∈ blkd7_5_5, subd7_5 q = true := by
  unfold blkd7_5_5
  exact List.forall_mem_cons.2 ⟨subd7_5_160, List.forall_mem_cons.2 ⟨subd7_5_161, List.forall_mem_cons.2 ⟨subd7_5_162, List.forall_mem_cons.2 ⟨subd7_5_163, List.forall_mem_cons.2 ⟨subd7_5_164, List.forall_mem_cons.2 ⟨subd7_5_165, List.forall_mem_cons.2 ⟨subd7_5_166, List.forall_mem_cons.2 ⟨subd7_5_167, List.forall_mem_cons.2 ⟨subd7_5_168, List.forall_mem_cons.2 ⟨subd7_5_169, List.forall_mem_cons.2 ⟨subd7_5_170, List.forall_mem_cons.2 ⟨subd7_5_171, List.forall_mem_cons.2 ⟨subd7_5_172, List.forall_mem_cons.2 ⟨subd7_5_173, List.forall_mem_cons.2 ⟨subd7_5_174, List.forall_mem_cons.2 ⟨subd7_5_175, List.forall_mem_cons.2 ⟨subd7_5_176, List.forall_mem_cons.2 ⟨subd7_5_177, List.forall_mem_cons.2 ⟨subd7_5_178, List.forall_mem_cons.2 ⟨subd7_5_179, List.forall_mem_cons.2 ⟨subd7_5_180, List.forall_mem_cons.2 ⟨subd7_5_181, List.forall_mem_cons.2 ⟨subd7_5_182, List.forall_mem_cons.2 ⟨subd7_5_183, List.forall_mem_cons.2 ⟨subd7_5_184, List.forall_mem_cons.2 ⟨subd7_5_185, List.forall_mem_cons.2 ⟨subd7_5_186, List.forall_mem_cons.2 ⟨subd7_5_187, List.forall_mem_cons.2 ⟨subd7_5_188, List.forall_mem_cons.2 ⟨subd7_5_189, List.forall_mem_cons.2 ⟨subd7_5_190, List.forall_mem_cons.2 ⟨subd7_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_192 : subd7_5 [0, 0, -3] = true := by decide +kernel
theorem subd7_5_193 : subd7_5 [0, 0, -2] = true := by decide +kernel
theorem subd7_5_194 : subd7_5 [0, 0, -1] = true := by decide +kernel
theorem subd7_5_195 : subd7_5 [0, 0, 0] = true := by decide +kernel
theorem subd7_5_196 : subd7_5 [0, 0, 1] = true := by decide +kernel
theorem subd7_5_197 : subd7_5 [0, 0, 2] = true := by decide +kernel
theorem subd7_5_198 : subd7_5 [0, 0, 3] = true := by decide +kernel
theorem subd7_5_199 : subd7_5 [0, 0, 4] = true := by decide +kernel
theorem subd7_5_200 : subd7_5 [0, 0, 5] = true := by decide +kernel
theorem subd7_5_201 : subd7_5 [0, 0, 6] = true := by decide +kernel
theorem subd7_5_202 : subd7_5 [0, 1, -7] = true := by decide +kernel
theorem subd7_5_203 : subd7_5 [0, 1, -6] = true := by decide +kernel
theorem subd7_5_204 : subd7_5 [0, 1, -5] = true := by decide +kernel
theorem subd7_5_205 : subd7_5 [0, 1, -4] = true := by decide +kernel
theorem subd7_5_206 : subd7_5 [0, 1, -3] = true := by decide +kernel
theorem subd7_5_207 : subd7_5 [0, 1, -2] = true := by decide +kernel
theorem subd7_5_208 : subd7_5 [0, 1, -1] = true := by decide +kernel
theorem subd7_5_209 : subd7_5 [0, 1, 0] = true := by decide +kernel
theorem subd7_5_210 : subd7_5 [0, 1, 1] = true := by decide +kernel
theorem subd7_5_211 : subd7_5 [0, 1, 2] = true := by decide +kernel
theorem subd7_5_212 : subd7_5 [0, 1, 3] = true := by decide +kernel
theorem subd7_5_213 : subd7_5 [0, 1, 4] = true := by decide +kernel
theorem subd7_5_214 : subd7_5 [0, 1, 5] = true := by decide +kernel
theorem subd7_5_215 : subd7_5 [0, 1, 6] = true := by decide +kernel
theorem subd7_5_216 : subd7_5 [0, 2, -7] = true := by decide +kernel
theorem subd7_5_217 : subd7_5 [0, 2, -6] = true := by decide +kernel
theorem subd7_5_218 : subd7_5 [0, 2, -5] = true := by decide +kernel
theorem subd7_5_219 : subd7_5 [0, 2, -4] = true := by decide +kernel
theorem subd7_5_220 : subd7_5 [0, 2, -3] = true := by decide +kernel
theorem subd7_5_221 : subd7_5 [0, 2, -2] = true := by decide +kernel
theorem subd7_5_222 : subd7_5 [0, 2, -1] = true := by decide +kernel
theorem subd7_5_223 : subd7_5 [0, 2, 0] = true := by decide +kernel
theorem sbd7_5_6 : ∀ q ∈ blkd7_5_6, subd7_5 q = true := by
  unfold blkd7_5_6
  exact List.forall_mem_cons.2 ⟨subd7_5_192, List.forall_mem_cons.2 ⟨subd7_5_193, List.forall_mem_cons.2 ⟨subd7_5_194, List.forall_mem_cons.2 ⟨subd7_5_195, List.forall_mem_cons.2 ⟨subd7_5_196, List.forall_mem_cons.2 ⟨subd7_5_197, List.forall_mem_cons.2 ⟨subd7_5_198, List.forall_mem_cons.2 ⟨subd7_5_199, List.forall_mem_cons.2 ⟨subd7_5_200, List.forall_mem_cons.2 ⟨subd7_5_201, List.forall_mem_cons.2 ⟨subd7_5_202, List.forall_mem_cons.2 ⟨subd7_5_203, List.forall_mem_cons.2 ⟨subd7_5_204, List.forall_mem_cons.2 ⟨subd7_5_205, List.forall_mem_cons.2 ⟨subd7_5_206, List.forall_mem_cons.2 ⟨subd7_5_207, List.forall_mem_cons.2 ⟨subd7_5_208, List.forall_mem_cons.2 ⟨subd7_5_209, List.forall_mem_cons.2 ⟨subd7_5_210, List.forall_mem_cons.2 ⟨subd7_5_211, List.forall_mem_cons.2 ⟨subd7_5_212, List.forall_mem_cons.2 ⟨subd7_5_213, List.forall_mem_cons.2 ⟨subd7_5_214, List.forall_mem_cons.2 ⟨subd7_5_215, List.forall_mem_cons.2 ⟨subd7_5_216, List.forall_mem_cons.2 ⟨subd7_5_217, List.forall_mem_cons.2 ⟨subd7_5_218, List.forall_mem_cons.2 ⟨subd7_5_219, List.forall_mem_cons.2 ⟨subd7_5_220, List.forall_mem_cons.2 ⟨subd7_5_221, List.forall_mem_cons.2 ⟨subd7_5_222, List.forall_mem_cons.2 ⟨subd7_5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_224 : subd7_5 [0, 2, 1] = true := by decide +kernel
theorem subd7_5_225 : subd7_5 [0, 2, 2] = true := by decide +kernel
theorem subd7_5_226 : subd7_5 [0, 2, 3] = true := by decide +kernel
theorem subd7_5_227 : subd7_5 [0, 2, 4] = true := by decide +kernel
theorem subd7_5_228 : subd7_5 [0, 2, 5] = true := by decide +kernel
theorem subd7_5_229 : subd7_5 [0, 2, 6] = true := by decide +kernel
theorem subd7_5_230 : subd7_5 [0, 3] = true := by decide +kernel
theorem subd7_5_231 : subd7_5 [0, 4] = true := by decide +kernel
theorem subd7_5_232 : subd7_5 [0, 5] = true := by decide +kernel
theorem subd7_5_233 : subd7_5 [1, -6] = true := by decide +kernel
theorem subd7_5_234 : subd7_5 [1, -5] = true := by decide +kernel
theorem subd7_5_235 : subd7_5 [1, -4] = true := by decide +kernel
theorem subd7_5_236 : subd7_5 [1, -3] = true := by decide +kernel
theorem subd7_5_237 : subd7_5 [1, -2, -7] = true := by decide +kernel
theorem subd7_5_238 : subd7_5 [1, -2, -6] = true := by decide +kernel
theorem subd7_5_239 : subd7_5 [1, -2, -5] = true := by decide +kernel
theorem subd7_5_240 : subd7_5 [1, -2, -4] = true := by decide +kernel
theorem subd7_5_241 : subd7_5 [1, -2, -3] = true := by decide +kernel
theorem subd7_5_242 : subd7_5 [1, -2, -2] = true := by decide +kernel
theorem subd7_5_243 : subd7_5 [1, -2, -1] = true := by decide +kernel
theorem subd7_5_244 : subd7_5 [1, -2, 0] = true := by decide +kernel
theorem subd7_5_245 : subd7_5 [1, -2, 1] = true := by decide +kernel
theorem subd7_5_246 : subd7_5 [1, -2, 2] = true := by decide +kernel
theorem subd7_5_247 : subd7_5 [1, -2, 3] = true := by decide +kernel
theorem subd7_5_248 : subd7_5 [1, -2, 4] = true := by decide +kernel
theorem subd7_5_249 : subd7_5 [1, -2, 5] = true := by decide +kernel
theorem subd7_5_250 : subd7_5 [1, -2, 6] = true := by decide +kernel
theorem subd7_5_251 : subd7_5 [1, -1, -7] = true := by decide +kernel
theorem subd7_5_252 : subd7_5 [1, -1, -6] = true := by decide +kernel
theorem subd7_5_253 : subd7_5 [1, -1, -5] = true := by decide +kernel
theorem subd7_5_254 : subd7_5 [1, -1, -4] = true := by decide +kernel
theorem subd7_5_255 : subd7_5 [1, -1, -3] = true := by decide +kernel
theorem sbd7_5_7 : ∀ q ∈ blkd7_5_7, subd7_5 q = true := by
  unfold blkd7_5_7
  exact List.forall_mem_cons.2 ⟨subd7_5_224, List.forall_mem_cons.2 ⟨subd7_5_225, List.forall_mem_cons.2 ⟨subd7_5_226, List.forall_mem_cons.2 ⟨subd7_5_227, List.forall_mem_cons.2 ⟨subd7_5_228, List.forall_mem_cons.2 ⟨subd7_5_229, List.forall_mem_cons.2 ⟨subd7_5_230, List.forall_mem_cons.2 ⟨subd7_5_231, List.forall_mem_cons.2 ⟨subd7_5_232, List.forall_mem_cons.2 ⟨subd7_5_233, List.forall_mem_cons.2 ⟨subd7_5_234, List.forall_mem_cons.2 ⟨subd7_5_235, List.forall_mem_cons.2 ⟨subd7_5_236, List.forall_mem_cons.2 ⟨subd7_5_237, List.forall_mem_cons.2 ⟨subd7_5_238, List.forall_mem_cons.2 ⟨subd7_5_239, List.forall_mem_cons.2 ⟨subd7_5_240, List.forall_mem_cons.2 ⟨subd7_5_241, List.forall_mem_cons.2 ⟨subd7_5_242, List.forall_mem_cons.2 ⟨subd7_5_243, List.forall_mem_cons.2 ⟨subd7_5_244, List.forall_mem_cons.2 ⟨subd7_5_245, List.forall_mem_cons.2 ⟨subd7_5_246, List.forall_mem_cons.2 ⟨subd7_5_247, List.forall_mem_cons.2 ⟨subd7_5_248, List.forall_mem_cons.2 ⟨subd7_5_249, List.forall_mem_cons.2 ⟨subd7_5_250, List.forall_mem_cons.2 ⟨subd7_5_251, List.forall_mem_cons.2 ⟨subd7_5_252, List.forall_mem_cons.2 ⟨subd7_5_253, List.forall_mem_cons.2 ⟨subd7_5_254, List.forall_mem_cons.2 ⟨subd7_5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_256 : subd7_5 [1, -1, -2] = true := by decide +kernel
theorem subd7_5_257 : subd7_5 [1, -1, -1] = true := by decide +kernel
theorem subd7_5_258 : subd7_5 [1, -1, 0] = true := by decide +kernel
theorem subd7_5_259 : subd7_5 [1, -1, 1] = true := by decide +kernel
theorem subd7_5_260 : subd7_5 [1, -1, 2] = true := by decide +kernel
theorem subd7_5_261 : subd7_5 [1, -1, 3] = true := by decide +kernel
theorem subd7_5_262 : subd7_5 [1, -1, 4] = true := by decide +kernel
theorem subd7_5_263 : subd7_5 [1, -1, 5] = true := by decide +kernel
theorem subd7_5_264 : subd7_5 [1, -1, 6] = true := by decide +kernel
theorem subd7_5_265 : subd7_5 [1, 0, -7] = true := by decide +kernel
theorem subd7_5_266 : subd7_5 [1, 0, -6] = true := by decide +kernel
theorem subd7_5_267 : subd7_5 [1, 0, -5] = true := by decide +kernel
theorem subd7_5_268 : subd7_5 [1, 0, -4] = true := by decide +kernel
theorem subd7_5_269 : subd7_5 [1, 0, -3] = true := by decide +kernel
theorem subd7_5_270 : subd7_5 [1, 0, -2] = true := by decide +kernel
theorem subd7_5_271 : subd7_5 [1, 0, -1] = true := by decide +kernel
theorem subd7_5_272 : subd7_5 [1, 0, 0] = true := by decide +kernel
theorem subd7_5_273 : subd7_5 [1, 0, 1] = true := by decide +kernel
theorem subd7_5_274 : subd7_5 [1, 0, 2] = true := by decide +kernel
theorem subd7_5_275 : subd7_5 [1, 0, 3] = true := by decide +kernel
theorem subd7_5_276 : subd7_5 [1, 0, 4] = true := by decide +kernel
theorem subd7_5_277 : subd7_5 [1, 0, 5] = true := by decide +kernel
theorem subd7_5_278 : subd7_5 [1, 0, 6] = true := by decide +kernel
theorem subd7_5_279 : subd7_5 [1, 0, 7] = true := by decide +kernel
theorem subd7_5_280 : subd7_5 [1, 1, -7] = true := by decide +kernel
theorem subd7_5_281 : subd7_5 [1, 1, -6] = true := by decide +kernel
theorem subd7_5_282 : subd7_5 [1, 1, -5] = true := by decide +kernel
theorem subd7_5_283 : subd7_5 [1, 1, -4] = true := by decide +kernel
theorem subd7_5_284 : subd7_5 [1, 1, -3] = true := by decide +kernel
theorem subd7_5_285 : subd7_5 [1, 1, -2] = true := by decide +kernel
theorem subd7_5_286 : subd7_5 [1, 1, -1] = true := by decide +kernel
theorem subd7_5_287 : subd7_5 [1, 1, 0] = true := by decide +kernel
theorem sbd7_5_8 : ∀ q ∈ blkd7_5_8, subd7_5 q = true := by
  unfold blkd7_5_8
  exact List.forall_mem_cons.2 ⟨subd7_5_256, List.forall_mem_cons.2 ⟨subd7_5_257, List.forall_mem_cons.2 ⟨subd7_5_258, List.forall_mem_cons.2 ⟨subd7_5_259, List.forall_mem_cons.2 ⟨subd7_5_260, List.forall_mem_cons.2 ⟨subd7_5_261, List.forall_mem_cons.2 ⟨subd7_5_262, List.forall_mem_cons.2 ⟨subd7_5_263, List.forall_mem_cons.2 ⟨subd7_5_264, List.forall_mem_cons.2 ⟨subd7_5_265, List.forall_mem_cons.2 ⟨subd7_5_266, List.forall_mem_cons.2 ⟨subd7_5_267, List.forall_mem_cons.2 ⟨subd7_5_268, List.forall_mem_cons.2 ⟨subd7_5_269, List.forall_mem_cons.2 ⟨subd7_5_270, List.forall_mem_cons.2 ⟨subd7_5_271, List.forall_mem_cons.2 ⟨subd7_5_272, List.forall_mem_cons.2 ⟨subd7_5_273, List.forall_mem_cons.2 ⟨subd7_5_274, List.forall_mem_cons.2 ⟨subd7_5_275, List.forall_mem_cons.2 ⟨subd7_5_276, List.forall_mem_cons.2 ⟨subd7_5_277, List.forall_mem_cons.2 ⟨subd7_5_278, List.forall_mem_cons.2 ⟨subd7_5_279, List.forall_mem_cons.2 ⟨subd7_5_280, List.forall_mem_cons.2 ⟨subd7_5_281, List.forall_mem_cons.2 ⟨subd7_5_282, List.forall_mem_cons.2 ⟨subd7_5_283, List.forall_mem_cons.2 ⟨subd7_5_284, List.forall_mem_cons.2 ⟨subd7_5_285, List.forall_mem_cons.2 ⟨subd7_5_286, List.forall_mem_cons.2 ⟨subd7_5_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_288 : subd7_5 [1, 1, 1] = true := by decide +kernel
theorem subd7_5_289 : subd7_5 [1, 1, 2] = true := by decide +kernel
theorem subd7_5_290 : subd7_5 [1, 1, 3] = true := by decide +kernel
theorem subd7_5_291 : subd7_5 [1, 1, 4] = true := by decide +kernel
theorem subd7_5_292 : subd7_5 [1, 1, 5] = true := by decide +kernel
theorem subd7_5_293 : subd7_5 [1, 1, 6] = true := by decide +kernel
theorem subd7_5_294 : subd7_5 [1, 1, 7] = true := by decide +kernel
theorem subd7_5_295 : subd7_5 [1, 2, -6] = true := by decide +kernel
theorem subd7_5_296 : subd7_5 [1, 2, -5] = true := by decide +kernel
theorem subd7_5_297 : subd7_5 [1, 2, -4] = true := by decide +kernel
theorem subd7_5_298 : subd7_5 [1, 2, -3] = true := by decide +kernel
theorem subd7_5_299 : subd7_5 [1, 2, -2] = true := by decide +kernel
theorem subd7_5_300 : subd7_5 [1, 2, -1] = true := by decide +kernel
theorem subd7_5_301 : subd7_5 [1, 2, 0] = true := by decide +kernel
theorem subd7_5_302 : subd7_5 [1, 2, 1] = true := by decide +kernel
theorem subd7_5_303 : subd7_5 [1, 2, 2] = true := by decide +kernel
theorem subd7_5_304 : subd7_5 [1, 2, 3] = true := by decide +kernel
theorem subd7_5_305 : subd7_5 [1, 2, 4] = true := by decide +kernel
theorem subd7_5_306 : subd7_5 [1, 2, 5] = true := by decide +kernel
theorem subd7_5_307 : subd7_5 [1, 2, 6] = true := by decide +kernel
theorem subd7_5_308 : subd7_5 [1, 3] = true := by decide +kernel
theorem subd7_5_309 : subd7_5 [1, 4] = true := by decide +kernel
theorem subd7_5_310 : subd7_5 [1, 5] = true := by decide +kernel
theorem subd7_5_311 : subd7_5 [2, -6] = true := by decide +kernel
theorem subd7_5_312 : subd7_5 [2, -5] = true := by decide +kernel
theorem subd7_5_313 : subd7_5 [2, -4] = true := by decide +kernel
theorem subd7_5_314 : subd7_5 [2, -3] = true := by decide +kernel
theorem subd7_5_315 : subd7_5 [2, -2] = true := by decide +kernel
theorem subd7_5_316 : subd7_5 [2, -1, -7] = true := by decide +kernel
theorem subd7_5_317 : subd7_5 [2, -1, -6] = true := by decide +kernel
theorem subd7_5_318 : subd7_5 [2, -1, -5] = true := by decide +kernel
theorem subd7_5_319 : subd7_5 [2, -1, -4] = true := by decide +kernel
theorem sbd7_5_9 : ∀ q ∈ blkd7_5_9, subd7_5 q = true := by
  unfold blkd7_5_9
  exact List.forall_mem_cons.2 ⟨subd7_5_288, List.forall_mem_cons.2 ⟨subd7_5_289, List.forall_mem_cons.2 ⟨subd7_5_290, List.forall_mem_cons.2 ⟨subd7_5_291, List.forall_mem_cons.2 ⟨subd7_5_292, List.forall_mem_cons.2 ⟨subd7_5_293, List.forall_mem_cons.2 ⟨subd7_5_294, List.forall_mem_cons.2 ⟨subd7_5_295, List.forall_mem_cons.2 ⟨subd7_5_296, List.forall_mem_cons.2 ⟨subd7_5_297, List.forall_mem_cons.2 ⟨subd7_5_298, List.forall_mem_cons.2 ⟨subd7_5_299, List.forall_mem_cons.2 ⟨subd7_5_300, List.forall_mem_cons.2 ⟨subd7_5_301, List.forall_mem_cons.2 ⟨subd7_5_302, List.forall_mem_cons.2 ⟨subd7_5_303, List.forall_mem_cons.2 ⟨subd7_5_304, List.forall_mem_cons.2 ⟨subd7_5_305, List.forall_mem_cons.2 ⟨subd7_5_306, List.forall_mem_cons.2 ⟨subd7_5_307, List.forall_mem_cons.2 ⟨subd7_5_308, List.forall_mem_cons.2 ⟨subd7_5_309, List.forall_mem_cons.2 ⟨subd7_5_310, List.forall_mem_cons.2 ⟨subd7_5_311, List.forall_mem_cons.2 ⟨subd7_5_312, List.forall_mem_cons.2 ⟨subd7_5_313, List.forall_mem_cons.2 ⟨subd7_5_314, List.forall_mem_cons.2 ⟨subd7_5_315, List.forall_mem_cons.2 ⟨subd7_5_316, List.forall_mem_cons.2 ⟨subd7_5_317, List.forall_mem_cons.2 ⟨subd7_5_318, List.forall_mem_cons.2 ⟨subd7_5_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_320 : subd7_5 [2, -1, -3] = true := by decide +kernel
theorem subd7_5_321 : subd7_5 [2, -1, -2] = true := by decide +kernel
theorem subd7_5_322 : subd7_5 [2, -1, -1] = true := by decide +kernel
theorem subd7_5_323 : subd7_5 [2, -1, 0] = true := by decide +kernel
theorem subd7_5_324 : subd7_5 [2, -1, 1] = true := by decide +kernel
theorem subd7_5_325 : subd7_5 [2, -1, 2] = true := by decide +kernel
theorem subd7_5_326 : subd7_5 [2, -1, 3] = true := by decide +kernel
theorem subd7_5_327 : subd7_5 [2, -1, 4] = true := by decide +kernel
theorem subd7_5_328 : subd7_5 [2, -1, 5] = true := by decide +kernel
theorem subd7_5_329 : subd7_5 [2, -1, 6] = true := by decide +kernel
theorem subd7_5_330 : subd7_5 [2, 0, -7] = true := by decide +kernel
theorem subd7_5_331 : subd7_5 [2, 0, -6] = true := by decide +kernel
theorem subd7_5_332 : subd7_5 [2, 0, -5] = true := by decide +kernel
theorem subd7_5_333 : subd7_5 [2, 0, -4] = true := by decide +kernel
theorem subd7_5_334 : subd7_5 [2, 0, -3] = true := by decide +kernel
theorem subd7_5_335 : subd7_5 [2, 0, -2] = true := by decide +kernel
theorem subd7_5_336 : subd7_5 [2, 0, -1] = true := by decide +kernel
theorem subd7_5_337 : subd7_5 [2, 0, 0] = true := by decide +kernel
theorem subd7_5_338 : subd7_5 [2, 0, 1] = true := by decide +kernel
theorem subd7_5_339 : subd7_5 [2, 0, 2] = true := by decide +kernel
theorem subd7_5_340 : subd7_5 [2, 0, 3] = true := by decide +kernel
theorem subd7_5_341 : subd7_5 [2, 0, 4] = true := by decide +kernel
theorem subd7_5_342 : subd7_5 [2, 0, 5] = true := by decide +kernel
theorem subd7_5_343 : subd7_5 [2, 0, 6] = true := by decide +kernel
theorem subd7_5_344 : subd7_5 [2, 1, -6] = true := by decide +kernel
theorem subd7_5_345 : subd7_5 [2, 1, -5] = true := by decide +kernel
theorem subd7_5_346 : subd7_5 [2, 1, -4] = true := by decide +kernel
theorem subd7_5_347 : subd7_5 [2, 1, -3] = true := by decide +kernel
theorem subd7_5_348 : subd7_5 [2, 1, -2] = true := by decide +kernel
theorem subd7_5_349 : subd7_5 [2, 1, -1] = true := by decide +kernel
theorem subd7_5_350 : subd7_5 [2, 1, 0] = true := by decide +kernel
theorem subd7_5_351 : subd7_5 [2, 1, 1] = true := by decide +kernel
theorem sbd7_5_10 : ∀ q ∈ blkd7_5_10, subd7_5 q = true := by
  unfold blkd7_5_10
  exact List.forall_mem_cons.2 ⟨subd7_5_320, List.forall_mem_cons.2 ⟨subd7_5_321, List.forall_mem_cons.2 ⟨subd7_5_322, List.forall_mem_cons.2 ⟨subd7_5_323, List.forall_mem_cons.2 ⟨subd7_5_324, List.forall_mem_cons.2 ⟨subd7_5_325, List.forall_mem_cons.2 ⟨subd7_5_326, List.forall_mem_cons.2 ⟨subd7_5_327, List.forall_mem_cons.2 ⟨subd7_5_328, List.forall_mem_cons.2 ⟨subd7_5_329, List.forall_mem_cons.2 ⟨subd7_5_330, List.forall_mem_cons.2 ⟨subd7_5_331, List.forall_mem_cons.2 ⟨subd7_5_332, List.forall_mem_cons.2 ⟨subd7_5_333, List.forall_mem_cons.2 ⟨subd7_5_334, List.forall_mem_cons.2 ⟨subd7_5_335, List.forall_mem_cons.2 ⟨subd7_5_336, List.forall_mem_cons.2 ⟨subd7_5_337, List.forall_mem_cons.2 ⟨subd7_5_338, List.forall_mem_cons.2 ⟨subd7_5_339, List.forall_mem_cons.2 ⟨subd7_5_340, List.forall_mem_cons.2 ⟨subd7_5_341, List.forall_mem_cons.2 ⟨subd7_5_342, List.forall_mem_cons.2 ⟨subd7_5_343, List.forall_mem_cons.2 ⟨subd7_5_344, List.forall_mem_cons.2 ⟨subd7_5_345, List.forall_mem_cons.2 ⟨subd7_5_346, List.forall_mem_cons.2 ⟨subd7_5_347, List.forall_mem_cons.2 ⟨subd7_5_348, List.forall_mem_cons.2 ⟨subd7_5_349, List.forall_mem_cons.2 ⟨subd7_5_350, List.forall_mem_cons.2 ⟨subd7_5_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_352 : subd7_5 [2, 1, 2] = true := by decide +kernel
theorem subd7_5_353 : subd7_5 [2, 1, 3] = true := by decide +kernel
theorem subd7_5_354 : subd7_5 [2, 1, 4] = true := by decide +kernel
theorem subd7_5_355 : subd7_5 [2, 1, 5] = true := by decide +kernel
theorem subd7_5_356 : subd7_5 [2, 1, 6] = true := by decide +kernel
theorem subd7_5_357 : subd7_5 [2, 2] = true := by decide +kernel
theorem subd7_5_358 : subd7_5 [2, 3] = true := by decide +kernel
theorem subd7_5_359 : subd7_5 [2, 4] = true := by decide +kernel
theorem subd7_5_360 : subd7_5 [2, 5] = true := by decide +kernel
theorem subd7_5_361 : subd7_5 [3, -5] = true := by decide +kernel
theorem subd7_5_362 : subd7_5 [3, -4] = true := by decide +kernel
theorem subd7_5_363 : subd7_5 [3, -3] = true := by decide +kernel
theorem subd7_5_364 : subd7_5 [3, -2] = true := by decide +kernel
theorem subd7_5_365 : subd7_5 [3, -1] = true := by decide +kernel
theorem subd7_5_366 : subd7_5 [3, 0] = true := by decide +kernel
theorem subd7_5_367 : subd7_5 [3, 1] = true := by decide +kernel
theorem subd7_5_368 : subd7_5 [3, 2] = true := by decide +kernel
theorem subd7_5_369 : subd7_5 [3, 3] = true := by decide +kernel
theorem subd7_5_370 : subd7_5 [3, 4] = true := by decide +kernel
theorem subd7_5_371 : subd7_5 [3, 5] = true := by decide +kernel
theorem subd7_5_372 : subd7_5 [4, -5] = true := by decide +kernel
theorem subd7_5_373 : subd7_5 [4, -4] = true := by decide +kernel
theorem subd7_5_374 : subd7_5 [4, -3] = true := by decide +kernel
theorem subd7_5_375 : subd7_5 [4, -2] = true := by decide +kernel
theorem subd7_5_376 : subd7_5 [4, -1] = true := by decide +kernel
theorem subd7_5_377 : subd7_5 [4, 0] = true := by decide +kernel
theorem subd7_5_378 : subd7_5 [4, 1] = true := by decide +kernel
theorem subd7_5_379 : subd7_5 [4, 2] = true := by decide +kernel
theorem subd7_5_380 : subd7_5 [4, 3] = true := by decide +kernel
theorem subd7_5_381 : subd7_5 [4, 4] = true := by decide +kernel
theorem subd7_5_382 : subd7_5 [5, -3] = true := by decide +kernel
theorem subd7_5_383 : subd7_5 [5, -2] = true := by decide +kernel
theorem sbd7_5_11 : ∀ q ∈ blkd7_5_11, subd7_5 q = true := by
  unfold blkd7_5_11
  exact List.forall_mem_cons.2 ⟨subd7_5_352, List.forall_mem_cons.2 ⟨subd7_5_353, List.forall_mem_cons.2 ⟨subd7_5_354, List.forall_mem_cons.2 ⟨subd7_5_355, List.forall_mem_cons.2 ⟨subd7_5_356, List.forall_mem_cons.2 ⟨subd7_5_357, List.forall_mem_cons.2 ⟨subd7_5_358, List.forall_mem_cons.2 ⟨subd7_5_359, List.forall_mem_cons.2 ⟨subd7_5_360, List.forall_mem_cons.2 ⟨subd7_5_361, List.forall_mem_cons.2 ⟨subd7_5_362, List.forall_mem_cons.2 ⟨subd7_5_363, List.forall_mem_cons.2 ⟨subd7_5_364, List.forall_mem_cons.2 ⟨subd7_5_365, List.forall_mem_cons.2 ⟨subd7_5_366, List.forall_mem_cons.2 ⟨subd7_5_367, List.forall_mem_cons.2 ⟨subd7_5_368, List.forall_mem_cons.2 ⟨subd7_5_369, List.forall_mem_cons.2 ⟨subd7_5_370, List.forall_mem_cons.2 ⟨subd7_5_371, List.forall_mem_cons.2 ⟨subd7_5_372, List.forall_mem_cons.2 ⟨subd7_5_373, List.forall_mem_cons.2 ⟨subd7_5_374, List.forall_mem_cons.2 ⟨subd7_5_375, List.forall_mem_cons.2 ⟨subd7_5_376, List.forall_mem_cons.2 ⟨subd7_5_377, List.forall_mem_cons.2 ⟨subd7_5_378, List.forall_mem_cons.2 ⟨subd7_5_379, List.forall_mem_cons.2 ⟨subd7_5_380, List.forall_mem_cons.2 ⟨subd7_5_381, List.forall_mem_cons.2 ⟨subd7_5_382, List.forall_mem_cons.2 ⟨subd7_5_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_384 : subd7_5 [5, -1] = true := by decide +kernel
theorem subd7_5_385 : subd7_5 [5, 0] = true := by decide +kernel
theorem subd7_5_386 : subd7_5 [5, 1] = true := by decide +kernel
theorem subd7_5_387 : subd7_5 [5, 2] = true := by decide +kernel
theorem subd7_5_388 : subd7_5 [5, 3] = true := by decide +kernel
theorem sbd7_5_12 : ∀ q ∈ blkd7_5_12, subd7_5 q = true := by
  unfold blkd7_5_12
  exact List.forall_mem_cons.2 ⟨subd7_5_384, List.forall_mem_cons.2 ⟨subd7_5_385, List.forall_mem_cons.2 ⟨subd7_5_386, List.forall_mem_cons.2 ⟨subd7_5_387, List.forall_mem_cons.2 ⟨subd7_5_388, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd7_6 : ldCheck G d7_6.U d7_6.ms ldd7_6 = true := by decide +kernel
theorem pre_okd7_6 : subPre G cell7 d7_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
