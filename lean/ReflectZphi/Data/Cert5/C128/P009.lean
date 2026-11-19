import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_6_160 : subd3_6 [0, -2, 0] = true := by decide +kernel
theorem subd3_6_161 : subd3_6 [0, -2, 1] = true := by decide +kernel
theorem subd3_6_162 : subd3_6 [0, -2, 2] = true := by decide +kernel
theorem subd3_6_163 : subd3_6 [0, -2, 3] = true := by decide +kernel
theorem subd3_6_164 : subd3_6 [0, -2, 4] = true := by decide +kernel
theorem subd3_6_165 : subd3_6 [0, -2, 5] = true := by decide +kernel
theorem subd3_6_166 : subd3_6 [0, -2, 6] = true := by decide +kernel
theorem subd3_6_167 : subd3_6 [0, -2, 7] = true := by decide +kernel
theorem subd3_6_168 : subd3_6 [0, -1, -10] = true := by decide +kernel
theorem subd3_6_169 : subd3_6 [0, -1, -9] = true := by decide +kernel
theorem subd3_6_170 : subd3_6 [0, -1, -8] = true := by decide +kernel
theorem subd3_6_171 : subd3_6 [0, -1, -7] = true := by decide +kernel
theorem subd3_6_172 : subd3_6 [0, -1, -6] = true := by decide +kernel
theorem subd3_6_173 : subd3_6 [0, -1, -5] = true := by decide +kernel
theorem subd3_6_174 : subd3_6 [0, -1, -4] = true := by decide +kernel
theorem subd3_6_175 : subd3_6 [0, -1, -3] = true := by decide +kernel
theorem subd3_6_176 : subd3_6 [0, -1, -2] = true := by decide +kernel
theorem subd3_6_177 : subd3_6 [0, -1, -1] = true := by decide +kernel
theorem subd3_6_178 : subd3_6 [0, -1, 0] = true := by decide +kernel
theorem subd3_6_179 : subd3_6 [0, -1, 1] = true := by decide +kernel
theorem subd3_6_180 : subd3_6 [0, -1, 2] = true := by decide +kernel
theorem subd3_6_181 : subd3_6 [0, -1, 3] = true := by decide +kernel
theorem subd3_6_182 : subd3_6 [0, -1, 4] = true := by decide +kernel
theorem subd3_6_183 : subd3_6 [0, -1, 5] = true := by decide +kernel
theorem subd3_6_184 : subd3_6 [0, -1, 6] = true := by decide +kernel
theorem subd3_6_185 : subd3_6 [0, -1, 7] = true := by decide +kernel
theorem subd3_6_186 : subd3_6 [0, -1, 8] = true := by decide +kernel
theorem subd3_6_187 : subd3_6 [0, 0, -10] = true := by decide +kernel
theorem subd3_6_188 : subd3_6 [0, 0, -9] = true := by decide +kernel
theorem subd3_6_189 : subd3_6 [0, 0, -8] = true := by decide +kernel
theorem subd3_6_190 : subd3_6 [0, 0, -7] = true := by decide +kernel
theorem subd3_6_191 : subd3_6 [0, 0, -6] = true := by decide +kernel
theorem sbd3_6_5 : ∀ q ∈ blkd3_6_5, subd3_6 q = true := by
  unfold blkd3_6_5
  exact List.forall_mem_cons.2 ⟨subd3_6_160, List.forall_mem_cons.2 ⟨subd3_6_161, List.forall_mem_cons.2 ⟨subd3_6_162, List.forall_mem_cons.2 ⟨subd3_6_163, List.forall_mem_cons.2 ⟨subd3_6_164, List.forall_mem_cons.2 ⟨subd3_6_165, List.forall_mem_cons.2 ⟨subd3_6_166, List.forall_mem_cons.2 ⟨subd3_6_167, List.forall_mem_cons.2 ⟨subd3_6_168, List.forall_mem_cons.2 ⟨subd3_6_169, List.forall_mem_cons.2 ⟨subd3_6_170, List.forall_mem_cons.2 ⟨subd3_6_171, List.forall_mem_cons.2 ⟨subd3_6_172, List.forall_mem_cons.2 ⟨subd3_6_173, List.forall_mem_cons.2 ⟨subd3_6_174, List.forall_mem_cons.2 ⟨subd3_6_175, List.forall_mem_cons.2 ⟨subd3_6_176, List.forall_mem_cons.2 ⟨subd3_6_177, List.forall_mem_cons.2 ⟨subd3_6_178, List.forall_mem_cons.2 ⟨subd3_6_179, List.forall_mem_cons.2 ⟨subd3_6_180, List.forall_mem_cons.2 ⟨subd3_6_181, List.forall_mem_cons.2 ⟨subd3_6_182, List.forall_mem_cons.2 ⟨subd3_6_183, List.forall_mem_cons.2 ⟨subd3_6_184, List.forall_mem_cons.2 ⟨subd3_6_185, List.forall_mem_cons.2 ⟨subd3_6_186, List.forall_mem_cons.2 ⟨subd3_6_187, List.forall_mem_cons.2 ⟨subd3_6_188, List.forall_mem_cons.2 ⟨subd3_6_189, List.forall_mem_cons.2 ⟨subd3_6_190, List.forall_mem_cons.2 ⟨subd3_6_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_192 : subd3_6 [0, 0, -5] = true := by decide +kernel
theorem subd3_6_193 : subd3_6 [0, 0, -4] = true := by decide +kernel
theorem subd3_6_194 : subd3_6 [0, 0, -3] = true := by decide +kernel
theorem subd3_6_195 : subd3_6 [0, 0, -2] = true := by decide +kernel
theorem subd3_6_196 : subd3_6 [0, 0, -1] = true := by decide +kernel
theorem subd3_6_197 : subd3_6 [0, 0, 0] = true := by decide +kernel
theorem subd3_6_198 : subd3_6 [0, 0, 1] = true := by decide +kernel
theorem subd3_6_199 : subd3_6 [0, 0, 2] = true := by decide +kernel
theorem subd3_6_200 : subd3_6 [0, 0, 3] = true := by decide +kernel
theorem subd3_6_201 : subd3_6 [0, 0, 4] = true := by decide +kernel
theorem subd3_6_202 : subd3_6 [0, 0, 5] = true := by decide +kernel
theorem subd3_6_203 : subd3_6 [0, 0, 6] = true := by decide +kernel
theorem subd3_6_204 : subd3_6 [0, 0, 7] = true := by decide +kernel
theorem subd3_6_205 : subd3_6 [0, 0, 8] = true := by decide +kernel
theorem subd3_6_206 : subd3_6 [0, 0, 9] = true := by decide +kernel
theorem subd3_6_207 : subd3_6 [0, 1, -9] = true := by decide +kernel
theorem subd3_6_208 : subd3_6 [0, 1, -8] = true := by decide +kernel
theorem subd3_6_209 : subd3_6 [0, 1, -7] = true := by decide +kernel
theorem subd3_6_210 : subd3_6 [0, 1, -6] = true := by decide +kernel
theorem subd3_6_211 : subd3_6 [0, 1, -5] = true := by decide +kernel
theorem subd3_6_212 : subd3_6 [0, 1, -4] = true := by decide +kernel
theorem subd3_6_213 : subd3_6 [0, 1, -3] = true := by decide +kernel
theorem subd3_6_214 : subd3_6 [0, 1, -2] = true := by decide +kernel
theorem subd3_6_215 : subd3_6 [0, 1, -1] = true := by decide +kernel
theorem subd3_6_216 : subd3_6 [0, 1, 0] = true := by decide +kernel
theorem subd3_6_217 : subd3_6 [0, 1, 1] = true := by decide +kernel
theorem subd3_6_218 : subd3_6 [0, 1, 2] = true := by decide +kernel
theorem subd3_6_219 : subd3_6 [0, 1, 3] = true := by decide +kernel
theorem subd3_6_220 : subd3_6 [0, 1, 4] = true := by decide +kernel
theorem subd3_6_221 : subd3_6 [0, 1, 5] = true := by decide +kernel
theorem subd3_6_222 : subd3_6 [0, 1, 6] = true := by decide +kernel
theorem subd3_6_223 : subd3_6 [0, 1, 7] = true := by decide +kernel
theorem sbd3_6_6 : ∀ q ∈ blkd3_6_6, subd3_6 q = true := by
  unfold blkd3_6_6
  exact List.forall_mem_cons.2 ⟨subd3_6_192, List.forall_mem_cons.2 ⟨subd3_6_193, List.forall_mem_cons.2 ⟨subd3_6_194, List.forall_mem_cons.2 ⟨subd3_6_195, List.forall_mem_cons.2 ⟨subd3_6_196, List.forall_mem_cons.2 ⟨subd3_6_197, List.forall_mem_cons.2 ⟨subd3_6_198, List.forall_mem_cons.2 ⟨subd3_6_199, List.forall_mem_cons.2 ⟨subd3_6_200, List.forall_mem_cons.2 ⟨subd3_6_201, List.forall_mem_cons.2 ⟨subd3_6_202, List.forall_mem_cons.2 ⟨subd3_6_203, List.forall_mem_cons.2 ⟨subd3_6_204, List.forall_mem_cons.2 ⟨subd3_6_205, List.forall_mem_cons.2 ⟨subd3_6_206, List.forall_mem_cons.2 ⟨subd3_6_207, List.forall_mem_cons.2 ⟨subd3_6_208, List.forall_mem_cons.2 ⟨subd3_6_209, List.forall_mem_cons.2 ⟨subd3_6_210, List.forall_mem_cons.2 ⟨subd3_6_211, List.forall_mem_cons.2 ⟨subd3_6_212, List.forall_mem_cons.2 ⟨subd3_6_213, List.forall_mem_cons.2 ⟨subd3_6_214, List.forall_mem_cons.2 ⟨subd3_6_215, List.forall_mem_cons.2 ⟨subd3_6_216, List.forall_mem_cons.2 ⟨subd3_6_217, List.forall_mem_cons.2 ⟨subd3_6_218, List.forall_mem_cons.2 ⟨subd3_6_219, List.forall_mem_cons.2 ⟨subd3_6_220, List.forall_mem_cons.2 ⟨subd3_6_221, List.forall_mem_cons.2 ⟨subd3_6_222, List.forall_mem_cons.2 ⟨subd3_6_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_224 : subd3_6 [0, 1, 8] = true := by decide +kernel
theorem subd3_6_225 : subd3_6 [0, 1, 9] = true := by decide +kernel
theorem subd3_6_226 : subd3_6 [0, 2, -8] = true := by decide +kernel
theorem subd3_6_227 : subd3_6 [0, 2, -7] = true := by decide +kernel
theorem subd3_6_228 : subd3_6 [0, 2, -6] = true := by decide +kernel
theorem subd3_6_229 : subd3_6 [0, 2, -5] = true := by decide +kernel
theorem subd3_6_230 : subd3_6 [0, 2, -4] = true := by decide +kernel
theorem subd3_6_231 : subd3_6 [0, 2, -3] = true := by decide +kernel
theorem subd3_6_232 : subd3_6 [0, 2, -2] = true := by decide +kernel
theorem subd3_6_233 : subd3_6 [0, 2, -1] = true := by decide +kernel
theorem subd3_6_234 : subd3_6 [0, 2, 0] = true := by decide +kernel
theorem subd3_6_235 : subd3_6 [0, 2, 1] = true := by decide +kernel
theorem subd3_6_236 : subd3_6 [0, 2, 2] = true := by decide +kernel
theorem subd3_6_237 : subd3_6 [0, 2, 3] = true := by decide +kernel
theorem subd3_6_238 : subd3_6 [0, 2, 4] = true := by decide +kernel
theorem subd3_6_239 : subd3_6 [0, 2, 5] = true := by decide +kernel
theorem subd3_6_240 : subd3_6 [0, 2, 6] = true := by decide +kernel
theorem subd3_6_241 : subd3_6 [0, 2, 7] = true := by decide +kernel
theorem subd3_6_242 : subd3_6 [0, 2, 8] = true := by decide +kernel
theorem subd3_6_243 : subd3_6 [0, 3] = true := by decide +kernel
theorem subd3_6_244 : subd3_6 [1, -4] = true := by decide +kernel
theorem subd3_6_245 : subd3_6 [1, -3] = true := by decide +kernel
theorem subd3_6_246 : subd3_6 [1, -2, -9] = true := by decide +kernel
theorem subd3_6_247 : subd3_6 [1, -2, -8] = true := by decide +kernel
theorem subd3_6_248 : subd3_6 [1, -2, -7] = true := by decide +kernel
theorem subd3_6_249 : subd3_6 [1, -2, -6] = true := by decide +kernel
theorem subd3_6_250 : subd3_6 [1, -2, -5] = true := by decide +kernel
theorem subd3_6_251 : subd3_6 [1, -2, -4] = true := by decide +kernel
theorem subd3_6_252 : subd3_6 [1, -2, -3] = true := by decide +kernel
theorem subd3_6_253 : subd3_6 [1, -2, -2] = true := by decide +kernel
theorem subd3_6_254 : subd3_6 [1, -2, -1] = true := by decide +kernel
theorem subd3_6_255 : subd3_6 [1, -2, 0] = true := by decide +kernel
theorem sbd3_6_7 : ∀ q ∈ blkd3_6_7, subd3_6 q = true := by
  unfold blkd3_6_7
  exact List.forall_mem_cons.2 ⟨subd3_6_224, List.forall_mem_cons.2 ⟨subd3_6_225, List.forall_mem_cons.2 ⟨subd3_6_226, List.forall_mem_cons.2 ⟨subd3_6_227, List.forall_mem_cons.2 ⟨subd3_6_228, List.forall_mem_cons.2 ⟨subd3_6_229, List.forall_mem_cons.2 ⟨subd3_6_230, List.forall_mem_cons.2 ⟨subd3_6_231, List.forall_mem_cons.2 ⟨subd3_6_232, List.forall_mem_cons.2 ⟨subd3_6_233, List.forall_mem_cons.2 ⟨subd3_6_234, List.forall_mem_cons.2 ⟨subd3_6_235, List.forall_mem_cons.2 ⟨subd3_6_236, List.forall_mem_cons.2 ⟨subd3_6_237, List.forall_mem_cons.2 ⟨subd3_6_238, List.forall_mem_cons.2 ⟨subd3_6_239, List.forall_mem_cons.2 ⟨subd3_6_240, List.forall_mem_cons.2 ⟨subd3_6_241, List.forall_mem_cons.2 ⟨subd3_6_242, List.forall_mem_cons.2 ⟨subd3_6_243, List.forall_mem_cons.2 ⟨subd3_6_244, List.forall_mem_cons.2 ⟨subd3_6_245, List.forall_mem_cons.2 ⟨subd3_6_246, List.forall_mem_cons.2 ⟨subd3_6_247, List.forall_mem_cons.2 ⟨subd3_6_248, List.forall_mem_cons.2 ⟨subd3_6_249, List.forall_mem_cons.2 ⟨subd3_6_250, List.forall_mem_cons.2 ⟨subd3_6_251, List.forall_mem_cons.2 ⟨subd3_6_252, List.forall_mem_cons.2 ⟨subd3_6_253, List.forall_mem_cons.2 ⟨subd3_6_254, List.forall_mem_cons.2 ⟨subd3_6_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_256 : subd3_6 [1, -2, 1] = true := by decide +kernel
theorem subd3_6_257 : subd3_6 [1, -2, 2] = true := by decide +kernel
theorem subd3_6_258 : subd3_6 [1, -2, 3] = true := by decide +kernel
theorem subd3_6_259 : subd3_6 [1, -2, 4] = true := by decide +kernel
theorem subd3_6_260 : subd3_6 [1, -2, 5] = true := by decide +kernel
theorem subd3_6_261 : subd3_6 [1, -2, 6] = true := by decide +kernel
theorem subd3_6_262 : subd3_6 [1, -2, 7] = true := by decide +kernel
theorem subd3_6_263 : subd3_6 [1, -1, -9] = true := by decide +kernel
theorem subd3_6_264 : subd3_6 [1, -1, -8] = true := by decide +kernel
theorem subd3_6_265 : subd3_6 [1, -1, -7] = true := by decide +kernel
theorem subd3_6_266 : subd3_6 [1, -1, -6] = true := by decide +kernel
theorem subd3_6_267 : subd3_6 [1, -1, -5] = true := by decide +kernel
theorem subd3_6_268 : subd3_6 [1, -1, -4] = true := by decide +kernel
theorem subd3_6_269 : subd3_6 [1, -1, -3] = true := by decide +kernel
theorem subd3_6_270 : subd3_6 [1, -1, -2] = true := by decide +kernel
theorem subd3_6_271 : subd3_6 [1, -1, -1] = true := by decide +kernel
theorem subd3_6_272 : subd3_6 [1, -1, 0] = true := by decide +kernel
theorem subd3_6_273 : subd3_6 [1, -1, 1] = true := by decide +kernel
theorem subd3_6_274 : subd3_6 [1, -1, 2] = true := by decide +kernel
theorem subd3_6_275 : subd3_6 [1, -1, 3] = true := by decide +kernel
theorem subd3_6_276 : subd3_6 [1, -1, 4] = true := by decide +kernel
theorem subd3_6_277 : subd3_6 [1, -1, 5] = true := by decide +kernel
theorem subd3_6_278 : subd3_6 [1, -1, 6] = true := by decide +kernel
theorem subd3_6_279 : subd3_6 [1, -1, 7] = true := by decide +kernel
theorem subd3_6_280 : subd3_6 [1, -1, 8] = true := by decide +kernel
theorem subd3_6_281 : subd3_6 [1, 0, -9] = true := by decide +kernel
theorem subd3_6_282 : subd3_6 [1, 0, -8] = true := by decide +kernel
theorem subd3_6_283 : subd3_6 [1, 0, -7] = true := by decide +kernel
theorem subd3_6_284 : subd3_6 [1, 0, -6] = true := by decide +kernel
theorem subd3_6_285 : subd3_6 [1, 0, -5] = true := by decide +kernel
theorem subd3_6_286 : subd3_6 [1, 0, -4] = true := by decide +kernel
theorem subd3_6_287 : subd3_6 [1, 0, -3] = true := by decide +kernel
theorem sbd3_6_8 : ∀ q ∈ blkd3_6_8, subd3_6 q = true := by
  unfold blkd3_6_8
  exact List.forall_mem_cons.2 ⟨subd3_6_256, List.forall_mem_cons.2 ⟨subd3_6_257, List.forall_mem_cons.2 ⟨subd3_6_258, List.forall_mem_cons.2 ⟨subd3_6_259, List.forall_mem_cons.2 ⟨subd3_6_260, List.forall_mem_cons.2 ⟨subd3_6_261, List.forall_mem_cons.2 ⟨subd3_6_262, List.forall_mem_cons.2 ⟨subd3_6_263, List.forall_mem_cons.2 ⟨subd3_6_264, List.forall_mem_cons.2 ⟨subd3_6_265, List.forall_mem_cons.2 ⟨subd3_6_266, List.forall_mem_cons.2 ⟨subd3_6_267, List.forall_mem_cons.2 ⟨subd3_6_268, List.forall_mem_cons.2 ⟨subd3_6_269, List.forall_mem_cons.2 ⟨subd3_6_270, List.forall_mem_cons.2 ⟨subd3_6_271, List.forall_mem_cons.2 ⟨subd3_6_272, List.forall_mem_cons.2 ⟨subd3_6_273, List.forall_mem_cons.2 ⟨subd3_6_274, List.forall_mem_cons.2 ⟨subd3_6_275, List.forall_mem_cons.2 ⟨subd3_6_276, List.forall_mem_cons.2 ⟨subd3_6_277, List.forall_mem_cons.2 ⟨subd3_6_278, List.forall_mem_cons.2 ⟨subd3_6_279, List.forall_mem_cons.2 ⟨subd3_6_280, List.forall_mem_cons.2 ⟨subd3_6_281, List.forall_mem_cons.2 ⟨subd3_6_282, List.forall_mem_cons.2 ⟨subd3_6_283, List.forall_mem_cons.2 ⟨subd3_6_284, List.forall_mem_cons.2 ⟨subd3_6_285, List.forall_mem_cons.2 ⟨subd3_6_286, List.forall_mem_cons.2 ⟨subd3_6_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_288 : subd3_6 [1, 0, -2] = true := by decide +kernel
theorem subd3_6_289 : subd3_6 [1, 0, -1] = true := by decide +kernel
theorem subd3_6_290 : subd3_6 [1, 0, 0] = true := by decide +kernel
theorem subd3_6_291 : subd3_6 [1, 0, 1] = true := by decide +kernel
theorem subd3_6_292 : subd3_6 [1, 0, 2] = true := by decide +kernel
theorem subd3_6_293 : subd3_6 [1, 0, 3] = true := by decide +kernel
theorem subd3_6_294 : subd3_6 [1, 0, 4] = true := by decide +kernel
theorem subd3_6_295 : subd3_6 [1, 0, 5] = true := by decide +kernel
theorem subd3_6_296 : subd3_6 [1, 0, 6] = true := by decide +kernel
theorem subd3_6_297 : subd3_6 [1, 0, 7] = true := by decide +kernel
theorem subd3_6_298 : subd3_6 [1, 0, 8] = true := by decide +kernel
theorem subd3_6_299 : subd3_6 [1, 0, 9] = true := by decide +kernel
theorem subd3_6_300 : subd3_6 [1, 1, -9] = true := by decide +kernel
theorem subd3_6_301 : subd3_6 [1, 1, -8] = true := by decide +kernel
theorem subd3_6_302 : subd3_6 [1, 1, -7] = true := by decide +kernel
theorem subd3_6_303 : subd3_6 [1, 1, -6] = true := by decide +kernel
theorem subd3_6_304 : subd3_6 [1, 1, -5] = true := by decide +kernel
theorem subd3_6_305 : subd3_6 [1, 1, -4] = true := by decide +kernel
theorem subd3_6_306 : subd3_6 [1, 1, -3] = true := by decide +kernel
theorem subd3_6_307 : subd3_6 [1, 1, -2] = true := by decide +kernel
theorem subd3_6_308 : subd3_6 [1, 1, -1] = true := by decide +kernel
theorem subd3_6_309 : subd3_6 [1, 1, 0] = true := by decide +kernel
theorem subd3_6_310 : subd3_6 [1, 1, 1] = true := by decide +kernel
theorem subd3_6_311 : subd3_6 [1, 1, 2] = true := by decide +kernel
theorem subd3_6_312 : subd3_6 [1, 1, 3] = true := by decide +kernel
theorem subd3_6_313 : subd3_6 [1, 1, 4] = true := by decide +kernel
theorem subd3_6_314 : subd3_6 [1, 1, 5] = true := by decide +kernel
theorem subd3_6_315 : subd3_6 [1, 1, 6] = true := by decide +kernel
theorem subd3_6_316 : subd3_6 [1, 1, 7] = true := by decide +kernel
theorem subd3_6_317 : subd3_6 [1, 1, 8] = true := by decide +kernel
theorem subd3_6_318 : subd3_6 [1, 1, 9] = true := by decide +kernel
theorem subd3_6_319 : subd3_6 [1, 2, -7] = true := by decide +kernel
theorem sbd3_6_9 : ∀ q ∈ blkd3_6_9, subd3_6 q = true := by
  unfold blkd3_6_9
  exact List.forall_mem_cons.2 ⟨subd3_6_288, List.forall_mem_cons.2 ⟨subd3_6_289, List.forall_mem_cons.2 ⟨subd3_6_290, List.forall_mem_cons.2 ⟨subd3_6_291, List.forall_mem_cons.2 ⟨subd3_6_292, List.forall_mem_cons.2 ⟨subd3_6_293, List.forall_mem_cons.2 ⟨subd3_6_294, List.forall_mem_cons.2 ⟨subd3_6_295, List.forall_mem_cons.2 ⟨subd3_6_296, List.forall_mem_cons.2 ⟨subd3_6_297, List.forall_mem_cons.2 ⟨subd3_6_298, List.forall_mem_cons.2 ⟨subd3_6_299, List.forall_mem_cons.2 ⟨subd3_6_300, List.forall_mem_cons.2 ⟨subd3_6_301, List.forall_mem_cons.2 ⟨subd3_6_302, List.forall_mem_cons.2 ⟨subd3_6_303, List.forall_mem_cons.2 ⟨subd3_6_304, List.forall_mem_cons.2 ⟨subd3_6_305, List.forall_mem_cons.2 ⟨subd3_6_306, List.forall_mem_cons.2 ⟨subd3_6_307, List.forall_mem_cons.2 ⟨subd3_6_308, List.forall_mem_cons.2 ⟨subd3_6_309, List.forall_mem_cons.2 ⟨subd3_6_310, List.forall_mem_cons.2 ⟨subd3_6_311, List.forall_mem_cons.2 ⟨subd3_6_312, List.forall_mem_cons.2 ⟨subd3_6_313, List.forall_mem_cons.2 ⟨subd3_6_314, List.forall_mem_cons.2 ⟨subd3_6_315, List.forall_mem_cons.2 ⟨subd3_6_316, List.forall_mem_cons.2 ⟨subd3_6_317, List.forall_mem_cons.2 ⟨subd3_6_318, List.forall_mem_cons.2 ⟨subd3_6_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_320 : subd3_6 [1, 2, -6] = true := by decide +kernel
theorem subd3_6_321 : subd3_6 [1, 2, -5] = true := by decide +kernel
theorem subd3_6_322 : subd3_6 [1, 2, -4] = true := by decide +kernel
theorem subd3_6_323 : subd3_6 [1, 2, -3] = true := by decide +kernel
theorem subd3_6_324 : subd3_6 [1, 2, -2] = true := by decide +kernel
theorem subd3_6_325 : subd3_6 [1, 2, -1] = true := by decide +kernel
theorem subd3_6_326 : subd3_6 [1, 2, 0] = true := by decide +kernel
theorem subd3_6_327 : subd3_6 [1, 2, 1] = true := by decide +kernel
theorem subd3_6_328 : subd3_6 [1, 2, 2] = true := by decide +kernel
theorem subd3_6_329 : subd3_6 [1, 2, 3] = true := by decide +kernel
theorem subd3_6_330 : subd3_6 [1, 2, 4] = true := by decide +kernel
theorem subd3_6_331 : subd3_6 [1, 2, 5] = true := by decide +kernel
theorem subd3_6_332 : subd3_6 [1, 2, 6] = true := by decide +kernel
theorem subd3_6_333 : subd3_6 [1, 2, 7] = true := by decide +kernel
theorem subd3_6_334 : subd3_6 [1, 2, 8] = true := by decide +kernel
theorem subd3_6_335 : subd3_6 [1, 3] = true := by decide +kernel
theorem subd3_6_336 : subd3_6 [2, -4] = true := by decide +kernel
theorem subd3_6_337 : subd3_6 [2, -3] = true := by decide +kernel
theorem subd3_6_338 : subd3_6 [2, -2] = true := by decide +kernel
theorem subd3_6_339 : subd3_6 [2, -1, -8] = true := by decide +kernel
theorem subd3_6_340 : subd3_6 [2, -1, -7] = true := by decide +kernel
theorem subd3_6_341 : subd3_6 [2, -1, -6] = true := by decide +kernel
theorem subd3_6_342 : subd3_6 [2, -1, -5] = true := by decide +kernel
theorem subd3_6_343 : subd3_6 [2, -1, -4] = true := by decide +kernel
theorem subd3_6_344 : subd3_6 [2, -1, -3] = true := by decide +kernel
theorem subd3_6_345 : subd3_6 [2, -1, -2] = true := by decide +kernel
theorem subd3_6_346 : subd3_6 [2, -1, -1] = true := by decide +kernel
theorem subd3_6_347 : subd3_6 [2, -1, 0] = true := by decide +kernel
theorem subd3_6_348 : subd3_6 [2, -1, 1] = true := by decide +kernel
theorem subd3_6_349 : subd3_6 [2, -1, 2] = true := by decide +kernel
theorem subd3_6_350 : subd3_6 [2, -1, 3] = true := by decide +kernel
theorem subd3_6_351 : subd3_6 [2, -1, 4] = true := by decide +kernel
theorem sbd3_6_10 : ∀ q ∈ blkd3_6_10, subd3_6 q = true := by
  unfold blkd3_6_10
  exact List.forall_mem_cons.2 ⟨subd3_6_320, List.forall_mem_cons.2 ⟨subd3_6_321, List.forall_mem_cons.2 ⟨subd3_6_322, List.forall_mem_cons.2 ⟨subd3_6_323, List.forall_mem_cons.2 ⟨subd3_6_324, List.forall_mem_cons.2 ⟨subd3_6_325, List.forall_mem_cons.2 ⟨subd3_6_326, List.forall_mem_cons.2 ⟨subd3_6_327, List.forall_mem_cons.2 ⟨subd3_6_328, List.forall_mem_cons.2 ⟨subd3_6_329, List.forall_mem_cons.2 ⟨subd3_6_330, List.forall_mem_cons.2 ⟨subd3_6_331, List.forall_mem_cons.2 ⟨subd3_6_332, List.forall_mem_cons.2 ⟨subd3_6_333, List.forall_mem_cons.2 ⟨subd3_6_334, List.forall_mem_cons.2 ⟨subd3_6_335, List.forall_mem_cons.2 ⟨subd3_6_336, List.forall_mem_cons.2 ⟨subd3_6_337, List.forall_mem_cons.2 ⟨subd3_6_338, List.forall_mem_cons.2 ⟨subd3_6_339, List.forall_mem_cons.2 ⟨subd3_6_340, List.forall_mem_cons.2 ⟨subd3_6_341, List.forall_mem_cons.2 ⟨subd3_6_342, List.forall_mem_cons.2 ⟨subd3_6_343, List.forall_mem_cons.2 ⟨subd3_6_344, List.forall_mem_cons.2 ⟨subd3_6_345, List.forall_mem_cons.2 ⟨subd3_6_346, List.forall_mem_cons.2 ⟨subd3_6_347, List.forall_mem_cons.2 ⟨subd3_6_348, List.forall_mem_cons.2 ⟨subd3_6_349, List.forall_mem_cons.2 ⟨subd3_6_350, List.forall_mem_cons.2 ⟨subd3_6_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_352 : subd3_6 [2, -1, 5] = true := by decide +kernel
theorem subd3_6_353 : subd3_6 [2, -1, 6] = true := by decide +kernel
theorem subd3_6_354 : subd3_6 [2, -1, 7] = true := by decide +kernel
theorem subd3_6_355 : subd3_6 [2, 0, -8] = true := by decide +kernel
theorem subd3_6_356 : subd3_6 [2, 0, -7] = true := by decide +kernel
theorem subd3_6_357 : subd3_6 [2, 0, -6] = true := by decide +kernel
theorem subd3_6_358 : subd3_6 [2, 0, -5] = true := by decide +kernel
theorem subd3_6_359 : subd3_6 [2, 0, -4] = true := by decide +kernel
theorem subd3_6_360 : subd3_6 [2, 0, -3] = true := by decide +kernel
theorem subd3_6_361 : subd3_6 [2, 0, -2] = true := by decide +kernel
theorem subd3_6_362 : subd3_6 [2, 0, -1] = true := by decide +kernel
theorem subd3_6_363 : subd3_6 [2, 0, 0] = true := by decide +kernel
theorem subd3_6_364 : subd3_6 [2, 0, 1] = true := by decide +kernel
theorem subd3_6_365 : subd3_6 [2, 0, 2] = true := by decide +kernel
theorem subd3_6_366 : subd3_6 [2, 0, 3] = true := by decide +kernel
theorem subd3_6_367 : subd3_6 [2, 0, 4] = true := by decide +kernel
theorem subd3_6_368 : subd3_6 [2, 0, 5] = true := by decide +kernel
theorem subd3_6_369 : subd3_6 [2, 0, 6] = true := by decide +kernel
theorem subd3_6_370 : subd3_6 [2, 0, 7] = true := by decide +kernel
theorem subd3_6_371 : subd3_6 [2, 0, 8] = true := by decide +kernel
theorem subd3_6_372 : subd3_6 [2, 1, -7] = true := by decide +kernel
theorem subd3_6_373 : subd3_6 [2, 1, -6] = true := by decide +kernel
theorem subd3_6_374 : subd3_6 [2, 1, -5] = true := by decide +kernel
theorem subd3_6_375 : subd3_6 [2, 1, -4] = true := by decide +kernel
theorem subd3_6_376 : subd3_6 [2, 1, -3] = true := by decide +kernel
theorem subd3_6_377 : subd3_6 [2, 1, -2] = true := by decide +kernel
theorem subd3_6_378 : subd3_6 [2, 1, -1] = true := by decide +kernel
theorem subd3_6_379 : subd3_6 [2, 1, 0] = true := by decide +kernel
theorem subd3_6_380 : subd3_6 [2, 1, 1] = true := by decide +kernel
theorem subd3_6_381 : subd3_6 [2, 1, 2] = true := by decide +kernel
theorem subd3_6_382 : subd3_6 [2, 1, 3] = true := by decide +kernel
theorem subd3_6_383 : subd3_6 [2, 1, 4] = true := by decide +kernel
theorem sbd3_6_11 : ∀ q ∈ blkd3_6_11, subd3_6 q = true := by
  unfold blkd3_6_11
  exact List.forall_mem_cons.2 ⟨subd3_6_352, List.forall_mem_cons.2 ⟨subd3_6_353, List.forall_mem_cons.2 ⟨subd3_6_354, List.forall_mem_cons.2 ⟨subd3_6_355, List.forall_mem_cons.2 ⟨subd3_6_356, List.forall_mem_cons.2 ⟨subd3_6_357, List.forall_mem_cons.2 ⟨subd3_6_358, List.forall_mem_cons.2 ⟨subd3_6_359, List.forall_mem_cons.2 ⟨subd3_6_360, List.forall_mem_cons.2 ⟨subd3_6_361, List.forall_mem_cons.2 ⟨subd3_6_362, List.forall_mem_cons.2 ⟨subd3_6_363, List.forall_mem_cons.2 ⟨subd3_6_364, List.forall_mem_cons.2 ⟨subd3_6_365, List.forall_mem_cons.2 ⟨subd3_6_366, List.forall_mem_cons.2 ⟨subd3_6_367, List.forall_mem_cons.2 ⟨subd3_6_368, List.forall_mem_cons.2 ⟨subd3_6_369, List.forall_mem_cons.2 ⟨subd3_6_370, List.forall_mem_cons.2 ⟨subd3_6_371, List.forall_mem_cons.2 ⟨subd3_6_372, List.forall_mem_cons.2 ⟨subd3_6_373, List.forall_mem_cons.2 ⟨subd3_6_374, List.forall_mem_cons.2 ⟨subd3_6_375, List.forall_mem_cons.2 ⟨subd3_6_376, List.forall_mem_cons.2 ⟨subd3_6_377, List.forall_mem_cons.2 ⟨subd3_6_378, List.forall_mem_cons.2 ⟨subd3_6_379, List.forall_mem_cons.2 ⟨subd3_6_380, List.forall_mem_cons.2 ⟨subd3_6_381, List.forall_mem_cons.2 ⟨subd3_6_382, List.forall_mem_cons.2 ⟨subd3_6_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_384 : subd3_6 [2, 1, 5] = true := by decide +kernel
theorem subd3_6_385 : subd3_6 [2, 1, 6] = true := by decide +kernel
theorem subd3_6_386 : subd3_6 [2, 1, 7] = true := by decide +kernel
theorem subd3_6_387 : subd3_6 [2, 2] = true := by decide +kernel
theorem subd3_6_388 : subd3_6 [3, -3] = true := by decide +kernel
theorem subd3_6_389 : subd3_6 [3, -2] = true := by decide +kernel
theorem subd3_6_390 : subd3_6 [3, -1] = true := by decide +kernel
theorem subd3_6_391 : subd3_6 [3, 0] = true := by decide +kernel
theorem subd3_6_392 : subd3_6 [3, 1] = true := by decide +kernel
theorem sbd3_6_12 : ∀ q ∈ blkd3_6_12, subd3_6 q = true := by
  unfold blkd3_6_12
  exact List.forall_mem_cons.2 ⟨subd3_6_384, List.forall_mem_cons.2 ⟨subd3_6_385, List.forall_mem_cons.2 ⟨subd3_6_386, List.forall_mem_cons.2 ⟨subd3_6_387, List.forall_mem_cons.2 ⟨subd3_6_388, List.forall_mem_cons.2 ⟨subd3_6_389, List.forall_mem_cons.2 ⟨subd3_6_390, List.forall_mem_cons.2 ⟨subd3_6_391, List.forall_mem_cons.2 ⟨subd3_6_392, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_7 : ldCheck G d3_7.U d3_7.ms ldd3_7 = true := by decide +kernel
theorem pre_okd3_7 : subPre G cell3 d3_7 = true := by decide +kernel
theorem subd3_7_0 : subd3_7 [-5] = true := by decide +kernel
theorem subd3_7_1 : subd3_7 [-4, -5] = true := by decide +kernel
theorem subd3_7_2 : subd3_7 [-4, -4] = true := by decide +kernel
theorem subd3_7_3 : subd3_7 [-4, -3] = true := by decide +kernel
theorem subd3_7_4 : subd3_7 [-4, -2] = true := by decide +kernel
theorem subd3_7_5 : subd3_7 [-4, -1] = true := by decide +kernel
theorem subd3_7_6 : subd3_7 [-4, 0] = true := by decide +kernel
theorem subd3_7_7 : subd3_7 [-4, 1] = true := by decide +kernel
theorem subd3_7_8 : subd3_7 [-4, 2] = true := by decide +kernel
theorem subd3_7_9 : subd3_7 [-3, -6] = true := by decide +kernel
theorem subd3_7_10 : subd3_7 [-3, -5] = true := by decide +kernel
theorem subd3_7_11 : subd3_7 [-3, -4] = true := by decide +kernel
theorem subd3_7_12 : subd3_7 [-3, -3] = true := by decide +kernel
theorem subd3_7_13 : subd3_7 [-3, -2] = true := by decide +kernel
theorem subd3_7_14 : subd3_7 [-3, -1] = true := by decide +kernel
theorem subd3_7_15 : subd3_7 [-3, 0] = true := by decide +kernel
theorem subd3_7_16 : subd3_7 [-3, 1] = true := by decide +kernel
theorem subd3_7_17 : subd3_7 [-3, 2] = true := by decide +kernel
theorem subd3_7_18 : subd3_7 [-3, 3] = true := by decide +kernel
theorem subd3_7_19 : subd3_7 [-2, -6] = true := by decide +kernel
theorem subd3_7_20 : subd3_7 [-2, -5] = true := by decide +kernel
theorem subd3_7_21 : subd3_7 [-2, -4] = true := by decide +kernel
theorem subd3_7_22 : subd3_7 [-2, -3] = true := by decide +kernel
theorem subd3_7_23 : subd3_7 [-2, -2] = true := by decide +kernel
theorem subd3_7_24 : subd3_7 [-2, -1] = true := by decide +kernel
theorem subd3_7_25 : subd3_7 [-2, 0] = true := by decide +kernel
theorem subd3_7_26 : subd3_7 [-2, 1] = true := by decide +kernel
theorem subd3_7_27 : subd3_7 [-2, 2] = true := by decide +kernel
theorem subd3_7_28 : subd3_7 [-2, 3] = true := by decide +kernel
theorem subd3_7_29 : subd3_7 [-2, 4] = true := by decide +kernel
theorem subd3_7_30 : subd3_7 [-1, -6] = true := by decide +kernel
theorem subd3_7_31 : subd3_7 [-1, -5] = true := by decide +kernel
theorem sbd3_7_0 : ∀ q ∈ blkd3_7_0, subd3_7 q = true := by
  unfold blkd3_7_0
  exact List.forall_mem_cons.2 ⟨subd3_7_0, List.forall_mem_cons.2 ⟨subd3_7_1, List.forall_mem_cons.2 ⟨subd3_7_2, List.forall_mem_cons.2 ⟨subd3_7_3, List.forall_mem_cons.2 ⟨subd3_7_4, List.forall_mem_cons.2 ⟨subd3_7_5, List.forall_mem_cons.2 ⟨subd3_7_6, List.forall_mem_cons.2 ⟨subd3_7_7, List.forall_mem_cons.2 ⟨subd3_7_8, List.forall_mem_cons.2 ⟨subd3_7_9, List.forall_mem_cons.2 ⟨subd3_7_10, List.forall_mem_cons.2 ⟨subd3_7_11, List.forall_mem_cons.2 ⟨subd3_7_12, List.forall_mem_cons.2 ⟨subd3_7_13, List.forall_mem_cons.2 ⟨subd3_7_14, List.forall_mem_cons.2 ⟨subd3_7_15, List.forall_mem_cons.2 ⟨subd3_7_16, List.forall_mem_cons.2 ⟨subd3_7_17, List.forall_mem_cons.2 ⟨subd3_7_18, List.forall_mem_cons.2 ⟨subd3_7_19, List.forall_mem_cons.2 ⟨subd3_7_20, List.forall_mem_cons.2 ⟨subd3_7_21, List.forall_mem_cons.2 ⟨subd3_7_22, List.forall_mem_cons.2 ⟨subd3_7_23, List.forall_mem_cons.2 ⟨subd3_7_24, List.forall_mem_cons.2 ⟨subd3_7_25, List.forall_mem_cons.2 ⟨subd3_7_26, List.forall_mem_cons.2 ⟨subd3_7_27, List.forall_mem_cons.2 ⟨subd3_7_28, List.forall_mem_cons.2 ⟨subd3_7_29, List.forall_mem_cons.2 ⟨subd3_7_30, List.forall_mem_cons.2 ⟨subd3_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
