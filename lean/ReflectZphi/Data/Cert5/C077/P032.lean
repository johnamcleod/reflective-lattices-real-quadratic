import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_3_192 : subd12_3 [-1, -3, 1] = true := by decide +kernel
theorem subd12_3_193 : subd12_3 [-1, -3, 2] = true := by decide +kernel
theorem subd12_3_194 : subd12_3 [-1, -3, 3] = true := by decide +kernel
theorem subd12_3_195 : subd12_3 [-1, -3, 4] = true := by decide +kernel
theorem subd12_3_196 : subd12_3 [-1, -3, 5] = true := by decide +kernel
theorem subd12_3_197 : subd12_3 [-1, -3, 6] = true := by decide +kernel
theorem subd12_3_198 : subd12_3 [-1, -3, 7] = true := by decide +kernel
theorem subd12_3_199 : subd12_3 [-1, -2, -9] = true := by decide +kernel
theorem subd12_3_200 : subd12_3 [-1, -2, -8] = true := by decide +kernel
theorem subd12_3_201 : subd12_3 [-1, -2, -7] = true := by decide +kernel
theorem subd12_3_202 : subd12_3 [-1, -2, -6] = true := by decide +kernel
theorem subd12_3_203 : subd12_3 [-1, -2, -5] = true := by decide +kernel
theorem subd12_3_204 : subd12_3 [-1, -2, -4] = true := by decide +kernel
theorem subd12_3_205 : subd12_3 [-1, -2, -3] = true := by decide +kernel
theorem subd12_3_206 : subd12_3 [-1, -2, -2] = true := by decide +kernel
theorem subd12_3_207 : subd12_3 [-1, -2, -1] = true := by decide +kernel
theorem subd12_3_208 : subd12_3 [-1, -2, 0] = true := by decide +kernel
theorem subd12_3_209 : subd12_3 [-1, -2, 1] = true := by decide +kernel
theorem subd12_3_210 : subd12_3 [-1, -2, 2] = true := by decide +kernel
theorem subd12_3_211 : subd12_3 [-1, -2, 3] = true := by decide +kernel
theorem subd12_3_212 : subd12_3 [-1, -2, 4] = true := by decide +kernel
theorem subd12_3_213 : subd12_3 [-1, -2, 5] = true := by decide +kernel
theorem subd12_3_214 : subd12_3 [-1, -2, 6] = true := by decide +kernel
theorem subd12_3_215 : subd12_3 [-1, -2, 7] = true := by decide +kernel
theorem subd12_3_216 : subd12_3 [-1, -2, 8] = true := by decide +kernel
theorem subd12_3_217 : subd12_3 [-1, -1, -10] = true := by decide +kernel
theorem subd12_3_218 : subd12_3 [-1, -1, -9] = true := by decide +kernel
theorem subd12_3_219 : subd12_3 [-1, -1, -8] = true := by decide +kernel
theorem subd12_3_220 : subd12_3 [-1, -1, -7] = true := by decide +kernel
theorem subd12_3_221 : subd12_3 [-1, -1, -6] = true := by decide +kernel
theorem subd12_3_222 : subd12_3 [-1, -1, -5] = true := by decide +kernel
theorem subd12_3_223 : subd12_3 [-1, -1, -4] = true := by decide +kernel
theorem sbd12_3_6 : ∀ q ∈ blkd12_3_6, subd12_3 q = true := by
  unfold blkd12_3_6
  exact List.forall_mem_cons.2 ⟨subd12_3_192, List.forall_mem_cons.2 ⟨subd12_3_193, List.forall_mem_cons.2 ⟨subd12_3_194, List.forall_mem_cons.2 ⟨subd12_3_195, List.forall_mem_cons.2 ⟨subd12_3_196, List.forall_mem_cons.2 ⟨subd12_3_197, List.forall_mem_cons.2 ⟨subd12_3_198, List.forall_mem_cons.2 ⟨subd12_3_199, List.forall_mem_cons.2 ⟨subd12_3_200, List.forall_mem_cons.2 ⟨subd12_3_201, List.forall_mem_cons.2 ⟨subd12_3_202, List.forall_mem_cons.2 ⟨subd12_3_203, List.forall_mem_cons.2 ⟨subd12_3_204, List.forall_mem_cons.2 ⟨subd12_3_205, List.forall_mem_cons.2 ⟨subd12_3_206, List.forall_mem_cons.2 ⟨subd12_3_207, List.forall_mem_cons.2 ⟨subd12_3_208, List.forall_mem_cons.2 ⟨subd12_3_209, List.forall_mem_cons.2 ⟨subd12_3_210, List.forall_mem_cons.2 ⟨subd12_3_211, List.forall_mem_cons.2 ⟨subd12_3_212, List.forall_mem_cons.2 ⟨subd12_3_213, List.forall_mem_cons.2 ⟨subd12_3_214, List.forall_mem_cons.2 ⟨subd12_3_215, List.forall_mem_cons.2 ⟨subd12_3_216, List.forall_mem_cons.2 ⟨subd12_3_217, List.forall_mem_cons.2 ⟨subd12_3_218, List.forall_mem_cons.2 ⟨subd12_3_219, List.forall_mem_cons.2 ⟨subd12_3_220, List.forall_mem_cons.2 ⟨subd12_3_221, List.forall_mem_cons.2 ⟨subd12_3_222, List.forall_mem_cons.2 ⟨subd12_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_224 : subd12_3 [-1, -1, -3] = true := by decide +kernel
theorem subd12_3_225 : subd12_3 [-1, -1, -2] = true := by decide +kernel
theorem subd12_3_226 : subd12_3 [-1, -1, -1] = true := by decide +kernel
theorem subd12_3_227 : subd12_3 [-1, -1, 0] = true := by decide +kernel
theorem subd12_3_228 : subd12_3 [-1, -1, 1] = true := by decide +kernel
theorem subd12_3_229 : subd12_3 [-1, -1, 2] = true := by decide +kernel
theorem subd12_3_230 : subd12_3 [-1, -1, 3] = true := by decide +kernel
theorem subd12_3_231 : subd12_3 [-1, -1, 4] = true := by decide +kernel
theorem subd12_3_232 : subd12_3 [-1, -1, 5] = true := by decide +kernel
theorem subd12_3_233 : subd12_3 [-1, -1, 6] = true := by decide +kernel
theorem subd12_3_234 : subd12_3 [-1, -1, 7] = true := by decide +kernel
theorem subd12_3_235 : subd12_3 [-1, -1, 8] = true := by decide +kernel
theorem subd12_3_236 : subd12_3 [-1, 0, -10] = true := by decide +kernel
theorem subd12_3_237 : subd12_3 [-1, 0, -9] = true := by decide +kernel
theorem subd12_3_238 : subd12_3 [-1, 0, -8] = true := by decide +kernel
theorem subd12_3_239 : subd12_3 [-1, 0, -7] = true := by decide +kernel
theorem subd12_3_240 : subd12_3 [-1, 0, -6] = true := by decide +kernel
theorem subd12_3_241 : subd12_3 [-1, 0, -5] = true := by decide +kernel
theorem subd12_3_242 : subd12_3 [-1, 0, -4] = true := by decide +kernel
theorem subd12_3_243 : subd12_3 [-1, 0, -3] = true := by decide +kernel
theorem subd12_3_244 : subd12_3 [-1, 0, -2] = true := by decide +kernel
theorem subd12_3_245 : subd12_3 [-1, 0, -1] = true := by decide +kernel
theorem subd12_3_246 : subd12_3 [-1, 0, 0] = true := by decide +kernel
theorem subd12_3_247 : subd12_3 [-1, 0, 1] = true := by decide +kernel
theorem subd12_3_248 : subd12_3 [-1, 0, 2] = true := by decide +kernel
theorem subd12_3_249 : subd12_3 [-1, 0, 3] = true := by decide +kernel
theorem subd12_3_250 : subd12_3 [-1, 0, 4] = true := by decide +kernel
theorem subd12_3_251 : subd12_3 [-1, 0, 5] = true := by decide +kernel
theorem subd12_3_252 : subd12_3 [-1, 0, 6] = true := by decide +kernel
theorem subd12_3_253 : subd12_3 [-1, 0, 7] = true := by decide +kernel
theorem subd12_3_254 : subd12_3 [-1, 0, 8] = true := by decide +kernel
theorem subd12_3_255 : subd12_3 [-1, 1, -10] = true := by decide +kernel
theorem sbd12_3_7 : ∀ q ∈ blkd12_3_7, subd12_3 q = true := by
  unfold blkd12_3_7
  exact List.forall_mem_cons.2 ⟨subd12_3_224, List.forall_mem_cons.2 ⟨subd12_3_225, List.forall_mem_cons.2 ⟨subd12_3_226, List.forall_mem_cons.2 ⟨subd12_3_227, List.forall_mem_cons.2 ⟨subd12_3_228, List.forall_mem_cons.2 ⟨subd12_3_229, List.forall_mem_cons.2 ⟨subd12_3_230, List.forall_mem_cons.2 ⟨subd12_3_231, List.forall_mem_cons.2 ⟨subd12_3_232, List.forall_mem_cons.2 ⟨subd12_3_233, List.forall_mem_cons.2 ⟨subd12_3_234, List.forall_mem_cons.2 ⟨subd12_3_235, List.forall_mem_cons.2 ⟨subd12_3_236, List.forall_mem_cons.2 ⟨subd12_3_237, List.forall_mem_cons.2 ⟨subd12_3_238, List.forall_mem_cons.2 ⟨subd12_3_239, List.forall_mem_cons.2 ⟨subd12_3_240, List.forall_mem_cons.2 ⟨subd12_3_241, List.forall_mem_cons.2 ⟨subd12_3_242, List.forall_mem_cons.2 ⟨subd12_3_243, List.forall_mem_cons.2 ⟨subd12_3_244, List.forall_mem_cons.2 ⟨subd12_3_245, List.forall_mem_cons.2 ⟨subd12_3_246, List.forall_mem_cons.2 ⟨subd12_3_247, List.forall_mem_cons.2 ⟨subd12_3_248, List.forall_mem_cons.2 ⟨subd12_3_249, List.forall_mem_cons.2 ⟨subd12_3_250, List.forall_mem_cons.2 ⟨subd12_3_251, List.forall_mem_cons.2 ⟨subd12_3_252, List.forall_mem_cons.2 ⟨subd12_3_253, List.forall_mem_cons.2 ⟨subd12_3_254, List.forall_mem_cons.2 ⟨subd12_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_256 : subd12_3 [-1, 1, -9] = true := by decide +kernel
theorem subd12_3_257 : subd12_3 [-1, 1, -8] = true := by decide +kernel
theorem subd12_3_258 : subd12_3 [-1, 1, -7] = true := by decide +kernel
theorem subd12_3_259 : subd12_3 [-1, 1, -6] = true := by decide +kernel
theorem subd12_3_260 : subd12_3 [-1, 1, -5] = true := by decide +kernel
theorem subd12_3_261 : subd12_3 [-1, 1, -4] = true := by decide +kernel
theorem subd12_3_262 : subd12_3 [-1, 1, -3] = true := by decide +kernel
theorem subd12_3_263 : subd12_3 [-1, 1, -2] = true := by decide +kernel
theorem subd12_3_264 : subd12_3 [-1, 1, -1] = true := by decide +kernel
theorem subd12_3_265 : subd12_3 [-1, 1, 0] = true := by decide +kernel
theorem subd12_3_266 : subd12_3 [-1, 1, 1] = true := by decide +kernel
theorem subd12_3_267 : subd12_3 [-1, 1, 2] = true := by decide +kernel
theorem subd12_3_268 : subd12_3 [-1, 1, 3] = true := by decide +kernel
theorem subd12_3_269 : subd12_3 [-1, 1, 4] = true := by decide +kernel
theorem subd12_3_270 : subd12_3 [-1, 1, 5] = true := by decide +kernel
theorem subd12_3_271 : subd12_3 [-1, 1, 6] = true := by decide +kernel
theorem subd12_3_272 : subd12_3 [-1, 1, 7] = true := by decide +kernel
theorem subd12_3_273 : subd12_3 [-1, 2, -9] = true := by decide +kernel
theorem subd12_3_274 : subd12_3 [-1, 2, -8] = true := by decide +kernel
theorem subd12_3_275 : subd12_3 [-1, 2, -7] = true := by decide +kernel
theorem subd12_3_276 : subd12_3 [-1, 2, -6] = true := by decide +kernel
theorem subd12_3_277 : subd12_3 [-1, 2, -5] = true := by decide +kernel
theorem subd12_3_278 : subd12_3 [-1, 2, -4] = true := by decide +kernel
theorem subd12_3_279 : subd12_3 [-1, 2, -3] = true := by decide +kernel
theorem subd12_3_280 : subd12_3 [-1, 2, -2] = true := by decide +kernel
theorem subd12_3_281 : subd12_3 [-1, 2, -1] = true := by decide +kernel
theorem subd12_3_282 : subd12_3 [-1, 2, 0] = true := by decide +kernel
theorem subd12_3_283 : subd12_3 [-1, 2, 1] = true := by decide +kernel
theorem subd12_3_284 : subd12_3 [-1, 2, 2] = true := by decide +kernel
theorem subd12_3_285 : subd12_3 [-1, 2, 3] = true := by decide +kernel
theorem subd12_3_286 : subd12_3 [-1, 2, 4] = true := by decide +kernel
theorem subd12_3_287 : subd12_3 [-1, 2, 5] = true := by decide +kernel
theorem sbd12_3_8 : ∀ q ∈ blkd12_3_8, subd12_3 q = true := by
  unfold blkd12_3_8
  exact List.forall_mem_cons.2 ⟨subd12_3_256, List.forall_mem_cons.2 ⟨subd12_3_257, List.forall_mem_cons.2 ⟨subd12_3_258, List.forall_mem_cons.2 ⟨subd12_3_259, List.forall_mem_cons.2 ⟨subd12_3_260, List.forall_mem_cons.2 ⟨subd12_3_261, List.forall_mem_cons.2 ⟨subd12_3_262, List.forall_mem_cons.2 ⟨subd12_3_263, List.forall_mem_cons.2 ⟨subd12_3_264, List.forall_mem_cons.2 ⟨subd12_3_265, List.forall_mem_cons.2 ⟨subd12_3_266, List.forall_mem_cons.2 ⟨subd12_3_267, List.forall_mem_cons.2 ⟨subd12_3_268, List.forall_mem_cons.2 ⟨subd12_3_269, List.forall_mem_cons.2 ⟨subd12_3_270, List.forall_mem_cons.2 ⟨subd12_3_271, List.forall_mem_cons.2 ⟨subd12_3_272, List.forall_mem_cons.2 ⟨subd12_3_273, List.forall_mem_cons.2 ⟨subd12_3_274, List.forall_mem_cons.2 ⟨subd12_3_275, List.forall_mem_cons.2 ⟨subd12_3_276, List.forall_mem_cons.2 ⟨subd12_3_277, List.forall_mem_cons.2 ⟨subd12_3_278, List.forall_mem_cons.2 ⟨subd12_3_279, List.forall_mem_cons.2 ⟨subd12_3_280, List.forall_mem_cons.2 ⟨subd12_3_281, List.forall_mem_cons.2 ⟨subd12_3_282, List.forall_mem_cons.2 ⟨subd12_3_283, List.forall_mem_cons.2 ⟨subd12_3_284, List.forall_mem_cons.2 ⟨subd12_3_285, List.forall_mem_cons.2 ⟨subd12_3_286, List.forall_mem_cons.2 ⟨subd12_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_288 : subd12_3 [-1, 2, 6] = true := by decide +kernel
theorem subd12_3_289 : subd12_3 [-1, 3, -8] = true := by decide +kernel
theorem subd12_3_290 : subd12_3 [-1, 3, -7] = true := by decide +kernel
theorem subd12_3_291 : subd12_3 [-1, 3, -6] = true := by decide +kernel
theorem subd12_3_292 : subd12_3 [-1, 3, -5] = true := by decide +kernel
theorem subd12_3_293 : subd12_3 [-1, 3, -4] = true := by decide +kernel
theorem subd12_3_294 : subd12_3 [-1, 3, -3] = true := by decide +kernel
theorem subd12_3_295 : subd12_3 [-1, 3, -2] = true := by decide +kernel
theorem subd12_3_296 : subd12_3 [-1, 3, -1] = true := by decide +kernel
theorem subd12_3_297 : subd12_3 [-1, 3, 0] = true := by decide +kernel
theorem subd12_3_298 : subd12_3 [-1, 3, 1] = true := by decide +kernel
theorem subd12_3_299 : subd12_3 [-1, 3, 2] = true := by decide +kernel
theorem subd12_3_300 : subd12_3 [-1, 3, 3] = true := by decide +kernel
theorem subd12_3_301 : subd12_3 [-1, 3, 4] = true := by decide +kernel
theorem subd12_3_302 : subd12_3 [-1, 3, 5] = true := by decide +kernel
theorem subd12_3_303 : subd12_3 [-1, 4] = true := by decide +kernel
theorem subd12_3_304 : subd12_3 [0, -6] = true := by decide +kernel
theorem subd12_3_305 : subd12_3 [0, -5] = true := by decide +kernel
theorem subd12_3_306 : subd12_3 [0, -4] = true := by decide +kernel
theorem subd12_3_307 : subd12_3 [0, -3, -7] = true := by decide +kernel
theorem subd12_3_308 : subd12_3 [0, -3, -6] = true := by decide +kernel
theorem subd12_3_309 : subd12_3 [0, -3, -5] = true := by decide +kernel
theorem subd12_3_310 : subd12_3 [0, -3, -4] = true := by decide +kernel
theorem subd12_3_311 : subd12_3 [0, -3, -3] = true := by decide +kernel
theorem subd12_3_312 : subd12_3 [0, -3, -2] = true := by decide +kernel
theorem subd12_3_313 : subd12_3 [0, -3, -1] = true := by decide +kernel
theorem subd12_3_314 : subd12_3 [0, -3, 0] = true := by decide +kernel
theorem subd12_3_315 : subd12_3 [0, -3, 1] = true := by decide +kernel
theorem subd12_3_316 : subd12_3 [0, -3, 2] = true := by decide +kernel
theorem subd12_3_317 : subd12_3 [0, -3, 3] = true := by decide +kernel
theorem subd12_3_318 : subd12_3 [0, -3, 4] = true := by decide +kernel
theorem subd12_3_319 : subd12_3 [0, -3, 5] = true := by decide +kernel
theorem sbd12_3_9 : ∀ q ∈ blkd12_3_9, subd12_3 q = true := by
  unfold blkd12_3_9
  exact List.forall_mem_cons.2 ⟨subd12_3_288, List.forall_mem_cons.2 ⟨subd12_3_289, List.forall_mem_cons.2 ⟨subd12_3_290, List.forall_mem_cons.2 ⟨subd12_3_291, List.forall_mem_cons.2 ⟨subd12_3_292, List.forall_mem_cons.2 ⟨subd12_3_293, List.forall_mem_cons.2 ⟨subd12_3_294, List.forall_mem_cons.2 ⟨subd12_3_295, List.forall_mem_cons.2 ⟨subd12_3_296, List.forall_mem_cons.2 ⟨subd12_3_297, List.forall_mem_cons.2 ⟨subd12_3_298, List.forall_mem_cons.2 ⟨subd12_3_299, List.forall_mem_cons.2 ⟨subd12_3_300, List.forall_mem_cons.2 ⟨subd12_3_301, List.forall_mem_cons.2 ⟨subd12_3_302, List.forall_mem_cons.2 ⟨subd12_3_303, List.forall_mem_cons.2 ⟨subd12_3_304, List.forall_mem_cons.2 ⟨subd12_3_305, List.forall_mem_cons.2 ⟨subd12_3_306, List.forall_mem_cons.2 ⟨subd12_3_307, List.forall_mem_cons.2 ⟨subd12_3_308, List.forall_mem_cons.2 ⟨subd12_3_309, List.forall_mem_cons.2 ⟨subd12_3_310, List.forall_mem_cons.2 ⟨subd12_3_311, List.forall_mem_cons.2 ⟨subd12_3_312, List.forall_mem_cons.2 ⟨subd12_3_313, List.forall_mem_cons.2 ⟨subd12_3_314, List.forall_mem_cons.2 ⟨subd12_3_315, List.forall_mem_cons.2 ⟨subd12_3_316, List.forall_mem_cons.2 ⟨subd12_3_317, List.forall_mem_cons.2 ⟨subd12_3_318, List.forall_mem_cons.2 ⟨subd12_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_320 : subd12_3 [0, -3, 6] = true := by decide +kernel
theorem subd12_3_321 : subd12_3 [0, -3, 7] = true := by decide +kernel
theorem subd12_3_322 : subd12_3 [0, -3, 8] = true := by decide +kernel
theorem subd12_3_323 : subd12_3 [0, -2, -8] = true := by decide +kernel
theorem subd12_3_324 : subd12_3 [0, -2, -7] = true := by decide +kernel
theorem subd12_3_325 : subd12_3 [0, -2, -6] = true := by decide +kernel
theorem subd12_3_326 : subd12_3 [0, -2, -5] = true := by decide +kernel
theorem subd12_3_327 : subd12_3 [0, -2, -4] = true := by decide +kernel
theorem subd12_3_328 : subd12_3 [0, -2, -3] = true := by decide +kernel
theorem subd12_3_329 : subd12_3 [0, -2, -2] = true := by decide +kernel
theorem subd12_3_330 : subd12_3 [0, -2, -1] = true := by decide +kernel
theorem subd12_3_331 : subd12_3 [0, -2, 0] = true := by decide +kernel
theorem subd12_3_332 : subd12_3 [0, -2, 1] = true := by decide +kernel
theorem subd12_3_333 : subd12_3 [0, -2, 2] = true := by decide +kernel
theorem subd12_3_334 : subd12_3 [0, -2, 3] = true := by decide +kernel
theorem subd12_3_335 : subd12_3 [0, -2, 4] = true := by decide +kernel
theorem subd12_3_336 : subd12_3 [0, -2, 5] = true := by decide +kernel
theorem subd12_3_337 : subd12_3 [0, -2, 6] = true := by decide +kernel
theorem subd12_3_338 : subd12_3 [0, -2, 7] = true := by decide +kernel
theorem subd12_3_339 : subd12_3 [0, -2, 8] = true := by decide +kernel
theorem subd12_3_340 : subd12_3 [0, -1, -9] = true := by decide +kernel
theorem subd12_3_341 : subd12_3 [0, -1, -8] = true := by decide +kernel
theorem subd12_3_342 : subd12_3 [0, -1, -7] = true := by decide +kernel
theorem subd12_3_343 : subd12_3 [0, -1, -6] = true := by decide +kernel
theorem subd12_3_344 : subd12_3 [0, -1, -5] = true := by decide +kernel
theorem subd12_3_345 : subd12_3 [0, -1, -4] = true := by decide +kernel
theorem subd12_3_346 : subd12_3 [0, -1, -3] = true := by decide +kernel
theorem subd12_3_347 : subd12_3 [0, -1, -2] = true := by decide +kernel
theorem subd12_3_348 : subd12_3 [0, -1, -1] = true := by decide +kernel
theorem subd12_3_349 : subd12_3 [0, -1, 0] = true := by decide +kernel
theorem subd12_3_350 : subd12_3 [0, -1, 1] = true := by decide +kernel
theorem subd12_3_351 : subd12_3 [0, -1, 2] = true := by decide +kernel
theorem sbd12_3_10 : ∀ q ∈ blkd12_3_10, subd12_3 q = true := by
  unfold blkd12_3_10
  exact List.forall_mem_cons.2 ⟨subd12_3_320, List.forall_mem_cons.2 ⟨subd12_3_321, List.forall_mem_cons.2 ⟨subd12_3_322, List.forall_mem_cons.2 ⟨subd12_3_323, List.forall_mem_cons.2 ⟨subd12_3_324, List.forall_mem_cons.2 ⟨subd12_3_325, List.forall_mem_cons.2 ⟨subd12_3_326, List.forall_mem_cons.2 ⟨subd12_3_327, List.forall_mem_cons.2 ⟨subd12_3_328, List.forall_mem_cons.2 ⟨subd12_3_329, List.forall_mem_cons.2 ⟨subd12_3_330, List.forall_mem_cons.2 ⟨subd12_3_331, List.forall_mem_cons.2 ⟨subd12_3_332, List.forall_mem_cons.2 ⟨subd12_3_333, List.forall_mem_cons.2 ⟨subd12_3_334, List.forall_mem_cons.2 ⟨subd12_3_335, List.forall_mem_cons.2 ⟨subd12_3_336, List.forall_mem_cons.2 ⟨subd12_3_337, List.forall_mem_cons.2 ⟨subd12_3_338, List.forall_mem_cons.2 ⟨subd12_3_339, List.forall_mem_cons.2 ⟨subd12_3_340, List.forall_mem_cons.2 ⟨subd12_3_341, List.forall_mem_cons.2 ⟨subd12_3_342, List.forall_mem_cons.2 ⟨subd12_3_343, List.forall_mem_cons.2 ⟨subd12_3_344, List.forall_mem_cons.2 ⟨subd12_3_345, List.forall_mem_cons.2 ⟨subd12_3_346, List.forall_mem_cons.2 ⟨subd12_3_347, List.forall_mem_cons.2 ⟨subd12_3_348, List.forall_mem_cons.2 ⟨subd12_3_349, List.forall_mem_cons.2 ⟨subd12_3_350, List.forall_mem_cons.2 ⟨subd12_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_352 : subd12_3 [0, -1, 3] = true := by decide +kernel
theorem subd12_3_353 : subd12_3 [0, -1, 4] = true := by decide +kernel
theorem subd12_3_354 : subd12_3 [0, -1, 5] = true := by decide +kernel
theorem subd12_3_355 : subd12_3 [0, -1, 6] = true := by decide +kernel
theorem subd12_3_356 : subd12_3 [0, -1, 7] = true := by decide +kernel
theorem subd12_3_357 : subd12_3 [0, -1, 8] = true := by decide +kernel
theorem subd12_3_358 : subd12_3 [0, -1, 9] = true := by decide +kernel
theorem subd12_3_359 : subd12_3 [0, 0, -10] = true := by decide +kernel
theorem subd12_3_360 : subd12_3 [0, 0, -9] = true := by decide +kernel
theorem subd12_3_361 : subd12_3 [0, 0, -8] = true := by decide +kernel
theorem subd12_3_362 : subd12_3 [0, 0, -7] = true := by decide +kernel
theorem subd12_3_363 : subd12_3 [0, 0, -6] = true := by decide +kernel
theorem subd12_3_364 : subd12_3 [0, 0, -5] = true := by decide +kernel
theorem subd12_3_365 : subd12_3 [0, 0, -4] = true := by decide +kernel
theorem subd12_3_366 : subd12_3 [0, 0, -3] = true := by decide +kernel
theorem subd12_3_367 : subd12_3 [0, 0, -2] = true := by decide +kernel
theorem subd12_3_368 : subd12_3 [0, 0, -1] = true := by decide +kernel
theorem subd12_3_369 : subd12_3 [0, 0, 0] = true := by decide +kernel
theorem subd12_3_370 : subd12_3 [0, 0, 1] = true := by decide +kernel
theorem subd12_3_371 : subd12_3 [0, 0, 2] = true := by decide +kernel
theorem subd12_3_372 : subd12_3 [0, 0, 3] = true := by decide +kernel
theorem subd12_3_373 : subd12_3 [0, 0, 4] = true := by decide +kernel
theorem subd12_3_374 : subd12_3 [0, 0, 5] = true := by decide +kernel
theorem subd12_3_375 : subd12_3 [0, 0, 6] = true := by decide +kernel
theorem subd12_3_376 : subd12_3 [0, 0, 7] = true := by decide +kernel
theorem subd12_3_377 : subd12_3 [0, 0, 8] = true := by decide +kernel
theorem subd12_3_378 : subd12_3 [0, 0, 9] = true := by decide +kernel
theorem subd12_3_379 : subd12_3 [0, 1, -10] = true := by decide +kernel
theorem subd12_3_380 : subd12_3 [0, 1, -9] = true := by decide +kernel
theorem subd12_3_381 : subd12_3 [0, 1, -8] = true := by decide +kernel
theorem subd12_3_382 : subd12_3 [0, 1, -7] = true := by decide +kernel
theorem subd12_3_383 : subd12_3 [0, 1, -6] = true := by decide +kernel
theorem sbd12_3_11 : ∀ q ∈ blkd12_3_11, subd12_3 q = true := by
  unfold blkd12_3_11
  exact List.forall_mem_cons.2 ⟨subd12_3_352, List.forall_mem_cons.2 ⟨subd12_3_353, List.forall_mem_cons.2 ⟨subd12_3_354, List.forall_mem_cons.2 ⟨subd12_3_355, List.forall_mem_cons.2 ⟨subd12_3_356, List.forall_mem_cons.2 ⟨subd12_3_357, List.forall_mem_cons.2 ⟨subd12_3_358, List.forall_mem_cons.2 ⟨subd12_3_359, List.forall_mem_cons.2 ⟨subd12_3_360, List.forall_mem_cons.2 ⟨subd12_3_361, List.forall_mem_cons.2 ⟨subd12_3_362, List.forall_mem_cons.2 ⟨subd12_3_363, List.forall_mem_cons.2 ⟨subd12_3_364, List.forall_mem_cons.2 ⟨subd12_3_365, List.forall_mem_cons.2 ⟨subd12_3_366, List.forall_mem_cons.2 ⟨subd12_3_367, List.forall_mem_cons.2 ⟨subd12_3_368, List.forall_mem_cons.2 ⟨subd12_3_369, List.forall_mem_cons.2 ⟨subd12_3_370, List.forall_mem_cons.2 ⟨subd12_3_371, List.forall_mem_cons.2 ⟨subd12_3_372, List.forall_mem_cons.2 ⟨subd12_3_373, List.forall_mem_cons.2 ⟨subd12_3_374, List.forall_mem_cons.2 ⟨subd12_3_375, List.forall_mem_cons.2 ⟨subd12_3_376, List.forall_mem_cons.2 ⟨subd12_3_377, List.forall_mem_cons.2 ⟨subd12_3_378, List.forall_mem_cons.2 ⟨subd12_3_379, List.forall_mem_cons.2 ⟨subd12_3_380, List.forall_mem_cons.2 ⟨subd12_3_381, List.forall_mem_cons.2 ⟨subd12_3_382, List.forall_mem_cons.2 ⟨subd12_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_384 : subd12_3 [0, 1, -5] = true := by decide +kernel
theorem subd12_3_385 : subd12_3 [0, 1, -4] = true := by decide +kernel
theorem subd12_3_386 : subd12_3 [0, 1, -3] = true := by decide +kernel
theorem subd12_3_387 : subd12_3 [0, 1, -2] = true := by decide +kernel
theorem subd12_3_388 : subd12_3 [0, 1, -1] = true := by decide +kernel
theorem subd12_3_389 : subd12_3 [0, 1, 0] = true := by decide +kernel
theorem subd12_3_390 : subd12_3 [0, 1, 1] = true := by decide +kernel
theorem subd12_3_391 : subd12_3 [0, 1, 2] = true := by decide +kernel
theorem subd12_3_392 : subd12_3 [0, 1, 3] = true := by decide +kernel
theorem subd12_3_393 : subd12_3 [0, 1, 4] = true := by decide +kernel
theorem subd12_3_394 : subd12_3 [0, 1, 5] = true := by decide +kernel
theorem subd12_3_395 : subd12_3 [0, 1, 6] = true := by decide +kernel
theorem subd12_3_396 : subd12_3 [0, 1, 7] = true := by decide +kernel
theorem subd12_3_397 : subd12_3 [0, 1, 8] = true := by decide +kernel
theorem subd12_3_398 : subd12_3 [0, 2, -9] = true := by decide +kernel
theorem subd12_3_399 : subd12_3 [0, 2, -8] = true := by decide +kernel
theorem subd12_3_400 : subd12_3 [0, 2, -7] = true := by decide +kernel
theorem subd12_3_401 : subd12_3 [0, 2, -6] = true := by decide +kernel
theorem subd12_3_402 : subd12_3 [0, 2, -5] = true := by decide +kernel
theorem subd12_3_403 : subd12_3 [0, 2, -4] = true := by decide +kernel
theorem subd12_3_404 : subd12_3 [0, 2, -3] = true := by decide +kernel
theorem subd12_3_405 : subd12_3 [0, 2, -2] = true := by decide +kernel
theorem subd12_3_406 : subd12_3 [0, 2, -1] = true := by decide +kernel
theorem subd12_3_407 : subd12_3 [0, 2, 0] = true := by decide +kernel
theorem subd12_3_408 : subd12_3 [0, 2, 1] = true := by decide +kernel
theorem subd12_3_409 : subd12_3 [0, 2, 2] = true := by decide +kernel
theorem subd12_3_410 : subd12_3 [0, 2, 3] = true := by decide +kernel
theorem subd12_3_411 : subd12_3 [0, 2, 4] = true := by decide +kernel
theorem subd12_3_412 : subd12_3 [0, 2, 5] = true := by decide +kernel
theorem subd12_3_413 : subd12_3 [0, 2, 6] = true := by decide +kernel
theorem subd12_3_414 : subd12_3 [0, 2, 7] = true := by decide +kernel
theorem subd12_3_415 : subd12_3 [0, 3, -9] = true := by decide +kernel
theorem sbd12_3_12 : ∀ q ∈ blkd12_3_12, subd12_3 q = true := by
  unfold blkd12_3_12
  exact List.forall_mem_cons.2 ⟨subd12_3_384, List.forall_mem_cons.2 ⟨subd12_3_385, List.forall_mem_cons.2 ⟨subd12_3_386, List.forall_mem_cons.2 ⟨subd12_3_387, List.forall_mem_cons.2 ⟨subd12_3_388, List.forall_mem_cons.2 ⟨subd12_3_389, List.forall_mem_cons.2 ⟨subd12_3_390, List.forall_mem_cons.2 ⟨subd12_3_391, List.forall_mem_cons.2 ⟨subd12_3_392, List.forall_mem_cons.2 ⟨subd12_3_393, List.forall_mem_cons.2 ⟨subd12_3_394, List.forall_mem_cons.2 ⟨subd12_3_395, List.forall_mem_cons.2 ⟨subd12_3_396, List.forall_mem_cons.2 ⟨subd12_3_397, List.forall_mem_cons.2 ⟨subd12_3_398, List.forall_mem_cons.2 ⟨subd12_3_399, List.forall_mem_cons.2 ⟨subd12_3_400, List.forall_mem_cons.2 ⟨subd12_3_401, List.forall_mem_cons.2 ⟨subd12_3_402, List.forall_mem_cons.2 ⟨subd12_3_403, List.forall_mem_cons.2 ⟨subd12_3_404, List.forall_mem_cons.2 ⟨subd12_3_405, List.forall_mem_cons.2 ⟨subd12_3_406, List.forall_mem_cons.2 ⟨subd12_3_407, List.forall_mem_cons.2 ⟨subd12_3_408, List.forall_mem_cons.2 ⟨subd12_3_409, List.forall_mem_cons.2 ⟨subd12_3_410, List.forall_mem_cons.2 ⟨subd12_3_411, List.forall_mem_cons.2 ⟨subd12_3_412, List.forall_mem_cons.2 ⟨subd12_3_413, List.forall_mem_cons.2 ⟨subd12_3_414, List.forall_mem_cons.2 ⟨subd12_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_416 : subd12_3 [0, 3, -8] = true := by decide +kernel
theorem subd12_3_417 : subd12_3 [0, 3, -7] = true := by decide +kernel
theorem subd12_3_418 : subd12_3 [0, 3, -6] = true := by decide +kernel
theorem subd12_3_419 : subd12_3 [0, 3, -5] = true := by decide +kernel
theorem subd12_3_420 : subd12_3 [0, 3, -4] = true := by decide +kernel
theorem subd12_3_421 : subd12_3 [0, 3, -3] = true := by decide +kernel
theorem subd12_3_422 : subd12_3 [0, 3, -2] = true := by decide +kernel
theorem subd12_3_423 : subd12_3 [0, 3, -1] = true := by decide +kernel
theorem subd12_3_424 : subd12_3 [0, 3, 0] = true := by decide +kernel
theorem subd12_3_425 : subd12_3 [0, 3, 1] = true := by decide +kernel
theorem subd12_3_426 : subd12_3 [0, 3, 2] = true := by decide +kernel
theorem subd12_3_427 : subd12_3 [0, 3, 3] = true := by decide +kernel
theorem subd12_3_428 : subd12_3 [0, 3, 4] = true := by decide +kernel
theorem subd12_3_429 : subd12_3 [0, 3, 5] = true := by decide +kernel
theorem subd12_3_430 : subd12_3 [0, 3, 6] = true := by decide +kernel
theorem subd12_3_431 : subd12_3 [0, 4] = true := by decide +kernel
theorem subd12_3_432 : subd12_3 [0, 5] = true := by decide +kernel
theorem subd12_3_433 : subd12_3 [1, -5] = true := by decide +kernel
theorem subd12_3_434 : subd12_3 [1, -4] = true := by decide +kernel
theorem subd12_3_435 : subd12_3 [1, -3, -6] = true := by decide +kernel
theorem subd12_3_436 : subd12_3 [1, -3, -5] = true := by decide +kernel
theorem subd12_3_437 : subd12_3 [1, -3, -4] = true := by decide +kernel
theorem subd12_3_438 : subd12_3 [1, -3, -3] = true := by decide +kernel
theorem subd12_3_439 : subd12_3 [1, -3, -2] = true := by decide +kernel
theorem subd12_3_440 : subd12_3 [1, -3, -1] = true := by decide +kernel
theorem subd12_3_441 : subd12_3 [1, -3, 0] = true := by decide +kernel
theorem subd12_3_442 : subd12_3 [1, -3, 1] = true := by decide +kernel
theorem subd12_3_443 : subd12_3 [1, -3, 2] = true := by decide +kernel
theorem subd12_3_444 : subd12_3 [1, -3, 3] = true := by decide +kernel
theorem subd12_3_445 : subd12_3 [1, -3, 4] = true := by decide +kernel
theorem subd12_3_446 : subd12_3 [1, -3, 5] = true := by decide +kernel
theorem subd12_3_447 : subd12_3 [1, -3, 6] = true := by decide +kernel
theorem sbd12_3_13 : ∀ q ∈ blkd12_3_13, subd12_3 q = true := by
  unfold blkd12_3_13
  exact List.forall_mem_cons.2 ⟨subd12_3_416, List.forall_mem_cons.2 ⟨subd12_3_417, List.forall_mem_cons.2 ⟨subd12_3_418, List.forall_mem_cons.2 ⟨subd12_3_419, List.forall_mem_cons.2 ⟨subd12_3_420, List.forall_mem_cons.2 ⟨subd12_3_421, List.forall_mem_cons.2 ⟨subd12_3_422, List.forall_mem_cons.2 ⟨subd12_3_423, List.forall_mem_cons.2 ⟨subd12_3_424, List.forall_mem_cons.2 ⟨subd12_3_425, List.forall_mem_cons.2 ⟨subd12_3_426, List.forall_mem_cons.2 ⟨subd12_3_427, List.forall_mem_cons.2 ⟨subd12_3_428, List.forall_mem_cons.2 ⟨subd12_3_429, List.forall_mem_cons.2 ⟨subd12_3_430, List.forall_mem_cons.2 ⟨subd12_3_431, List.forall_mem_cons.2 ⟨subd12_3_432, List.forall_mem_cons.2 ⟨subd12_3_433, List.forall_mem_cons.2 ⟨subd12_3_434, List.forall_mem_cons.2 ⟨subd12_3_435, List.forall_mem_cons.2 ⟨subd12_3_436, List.forall_mem_cons.2 ⟨subd12_3_437, List.forall_mem_cons.2 ⟨subd12_3_438, List.forall_mem_cons.2 ⟨subd12_3_439, List.forall_mem_cons.2 ⟨subd12_3_440, List.forall_mem_cons.2 ⟨subd12_3_441, List.forall_mem_cons.2 ⟨subd12_3_442, List.forall_mem_cons.2 ⟨subd12_3_443, List.forall_mem_cons.2 ⟨subd12_3_444, List.forall_mem_cons.2 ⟨subd12_3_445, List.forall_mem_cons.2 ⟨subd12_3_446, List.forall_mem_cons.2 ⟨subd12_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_448 : subd12_3 [1, -3, 7] = true := by decide +kernel
theorem subd12_3_449 : subd12_3 [1, -2, -7] = true := by decide +kernel
theorem subd12_3_450 : subd12_3 [1, -2, -6] = true := by decide +kernel
theorem subd12_3_451 : subd12_3 [1, -2, -5] = true := by decide +kernel
theorem subd12_3_452 : subd12_3 [1, -2, -4] = true := by decide +kernel
theorem subd12_3_453 : subd12_3 [1, -2, -3] = true := by decide +kernel
theorem subd12_3_454 : subd12_3 [1, -2, -2] = true := by decide +kernel
theorem subd12_3_455 : subd12_3 [1, -2, -1] = true := by decide +kernel
theorem subd12_3_456 : subd12_3 [1, -2, 0] = true := by decide +kernel
theorem subd12_3_457 : subd12_3 [1, -2, 1] = true := by decide +kernel
theorem subd12_3_458 : subd12_3 [1, -2, 2] = true := by decide +kernel
theorem subd12_3_459 : subd12_3 [1, -2, 3] = true := by decide +kernel
theorem subd12_3_460 : subd12_3 [1, -2, 4] = true := by decide +kernel
theorem subd12_3_461 : subd12_3 [1, -2, 5] = true := by decide +kernel
theorem subd12_3_462 : subd12_3 [1, -2, 6] = true := by decide +kernel
theorem subd12_3_463 : subd12_3 [1, -2, 7] = true := by decide +kernel
theorem subd12_3_464 : subd12_3 [1, -2, 8] = true := by decide +kernel
theorem subd12_3_465 : subd12_3 [1, -1, -8] = true := by decide +kernel
theorem subd12_3_466 : subd12_3 [1, -1, -7] = true := by decide +kernel
theorem subd12_3_467 : subd12_3 [1, -1, -6] = true := by decide +kernel
theorem subd12_3_468 : subd12_3 [1, -1, -5] = true := by decide +kernel
theorem subd12_3_469 : subd12_3 [1, -1, -4] = true := by decide +kernel
theorem subd12_3_470 : subd12_3 [1, -1, -3] = true := by decide +kernel
theorem subd12_3_471 : subd12_3 [1, -1, -2] = true := by decide +kernel
theorem subd12_3_472 : subd12_3 [1, -1, -1] = true := by decide +kernel
theorem subd12_3_473 : subd12_3 [1, -1, 0] = true := by decide +kernel
theorem subd12_3_474 : subd12_3 [1, -1, 1] = true := by decide +kernel
theorem subd12_3_475 : subd12_3 [1, -1, 2] = true := by decide +kernel
theorem subd12_3_476 : subd12_3 [1, -1, 3] = true := by decide +kernel
theorem subd12_3_477 : subd12_3 [1, -1, 4] = true := by decide +kernel
theorem subd12_3_478 : subd12_3 [1, -1, 5] = true := by decide +kernel
theorem subd12_3_479 : subd12_3 [1, -1, 6] = true := by decide +kernel
theorem sbd12_3_14 : ∀ q ∈ blkd12_3_14, subd12_3 q = true := by
  unfold blkd12_3_14
  exact List.forall_mem_cons.2 ⟨subd12_3_448, List.forall_mem_cons.2 ⟨subd12_3_449, List.forall_mem_cons.2 ⟨subd12_3_450, List.forall_mem_cons.2 ⟨subd12_3_451, List.forall_mem_cons.2 ⟨subd12_3_452, List.forall_mem_cons.2 ⟨subd12_3_453, List.forall_mem_cons.2 ⟨subd12_3_454, List.forall_mem_cons.2 ⟨subd12_3_455, List.forall_mem_cons.2 ⟨subd12_3_456, List.forall_mem_cons.2 ⟨subd12_3_457, List.forall_mem_cons.2 ⟨subd12_3_458, List.forall_mem_cons.2 ⟨subd12_3_459, List.forall_mem_cons.2 ⟨subd12_3_460, List.forall_mem_cons.2 ⟨subd12_3_461, List.forall_mem_cons.2 ⟨subd12_3_462, List.forall_mem_cons.2 ⟨subd12_3_463, List.forall_mem_cons.2 ⟨subd12_3_464, List.forall_mem_cons.2 ⟨subd12_3_465, List.forall_mem_cons.2 ⟨subd12_3_466, List.forall_mem_cons.2 ⟨subd12_3_467, List.forall_mem_cons.2 ⟨subd12_3_468, List.forall_mem_cons.2 ⟨subd12_3_469, List.forall_mem_cons.2 ⟨subd12_3_470, List.forall_mem_cons.2 ⟨subd12_3_471, List.forall_mem_cons.2 ⟨subd12_3_472, List.forall_mem_cons.2 ⟨subd12_3_473, List.forall_mem_cons.2 ⟨subd12_3_474, List.forall_mem_cons.2 ⟨subd12_3_475, List.forall_mem_cons.2 ⟨subd12_3_476, List.forall_mem_cons.2 ⟨subd12_3_477, List.forall_mem_cons.2 ⟨subd12_3_478, List.forall_mem_cons.2 ⟨subd12_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_480 : subd12_3 [1, -1, 7] = true := by decide +kernel
theorem subd12_3_481 : subd12_3 [1, -1, 8] = true := by decide +kernel
theorem subd12_3_482 : subd12_3 [1, -1, 9] = true := by decide +kernel
theorem subd12_3_483 : subd12_3 [1, 0, -9] = true := by decide +kernel
theorem subd12_3_484 : subd12_3 [1, 0, -8] = true := by decide +kernel
theorem subd12_3_485 : subd12_3 [1, 0, -7] = true := by decide +kernel
theorem subd12_3_486 : subd12_3 [1, 0, -6] = true := by decide +kernel
theorem subd12_3_487 : subd12_3 [1, 0, -5] = true := by decide +kernel
theorem subd12_3_488 : subd12_3 [1, 0, -4] = true := by decide +kernel
theorem subd12_3_489 : subd12_3 [1, 0, -3] = true := by decide +kernel
theorem subd12_3_490 : subd12_3 [1, 0, -2] = true := by decide +kernel
theorem subd12_3_491 : subd12_3 [1, 0, -1] = true := by decide +kernel
theorem subd12_3_492 : subd12_3 [1, 0, 0] = true := by decide +kernel
theorem subd12_3_493 : subd12_3 [1, 0, 1] = true := by decide +kernel
theorem subd12_3_494 : subd12_3 [1, 0, 2] = true := by decide +kernel
theorem subd12_3_495 : subd12_3 [1, 0, 3] = true := by decide +kernel
theorem subd12_3_496 : subd12_3 [1, 0, 4] = true := by decide +kernel
theorem subd12_3_497 : subd12_3 [1, 0, 5] = true := by decide +kernel
theorem subd12_3_498 : subd12_3 [1, 0, 6] = true := by decide +kernel
theorem subd12_3_499 : subd12_3 [1, 0, 7] = true := by decide +kernel
theorem subd12_3_500 : subd12_3 [1, 0, 8] = true := by decide +kernel
theorem subd12_3_501 : subd12_3 [1, 0, 9] = true := by decide +kernel
theorem subd12_3_502 : subd12_3 [1, 1, -9] = true := by decide +kernel
theorem subd12_3_503 : subd12_3 [1, 1, -8] = true := by decide +kernel
theorem subd12_3_504 : subd12_3 [1, 1, -7] = true := by decide +kernel
theorem subd12_3_505 : subd12_3 [1, 1, -6] = true := by decide +kernel
theorem subd12_3_506 : subd12_3 [1, 1, -5] = true := by decide +kernel
theorem subd12_3_507 : subd12_3 [1, 1, -4] = true := by decide +kernel
theorem subd12_3_508 : subd12_3 [1, 1, -3] = true := by decide +kernel
theorem subd12_3_509 : subd12_3 [1, 1, -2] = true := by decide +kernel
theorem subd12_3_510 : subd12_3 [1, 1, -1] = true := by decide +kernel
theorem subd12_3_511 : subd12_3 [1, 1, 0] = true := by decide +kernel
theorem sbd12_3_15 : ∀ q ∈ blkd12_3_15, subd12_3 q = true := by
  unfold blkd12_3_15
  exact List.forall_mem_cons.2 ⟨subd12_3_480, List.forall_mem_cons.2 ⟨subd12_3_481, List.forall_mem_cons.2 ⟨subd12_3_482, List.forall_mem_cons.2 ⟨subd12_3_483, List.forall_mem_cons.2 ⟨subd12_3_484, List.forall_mem_cons.2 ⟨subd12_3_485, List.forall_mem_cons.2 ⟨subd12_3_486, List.forall_mem_cons.2 ⟨subd12_3_487, List.forall_mem_cons.2 ⟨subd12_3_488, List.forall_mem_cons.2 ⟨subd12_3_489, List.forall_mem_cons.2 ⟨subd12_3_490, List.forall_mem_cons.2 ⟨subd12_3_491, List.forall_mem_cons.2 ⟨subd12_3_492, List.forall_mem_cons.2 ⟨subd12_3_493, List.forall_mem_cons.2 ⟨subd12_3_494, List.forall_mem_cons.2 ⟨subd12_3_495, List.forall_mem_cons.2 ⟨subd12_3_496, List.forall_mem_cons.2 ⟨subd12_3_497, List.forall_mem_cons.2 ⟨subd12_3_498, List.forall_mem_cons.2 ⟨subd12_3_499, List.forall_mem_cons.2 ⟨subd12_3_500, List.forall_mem_cons.2 ⟨subd12_3_501, List.forall_mem_cons.2 ⟨subd12_3_502, List.forall_mem_cons.2 ⟨subd12_3_503, List.forall_mem_cons.2 ⟨subd12_3_504, List.forall_mem_cons.2 ⟨subd12_3_505, List.forall_mem_cons.2 ⟨subd12_3_506, List.forall_mem_cons.2 ⟨subd12_3_507, List.forall_mem_cons.2 ⟨subd12_3_508, List.forall_mem_cons.2 ⟨subd12_3_509, List.forall_mem_cons.2 ⟨subd12_3_510, List.forall_mem_cons.2 ⟨subd12_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_512 : subd12_3 [1, 1, 1] = true := by decide +kernel
theorem subd12_3_513 : subd12_3 [1, 1, 2] = true := by decide +kernel
theorem subd12_3_514 : subd12_3 [1, 1, 3] = true := by decide +kernel
theorem subd12_3_515 : subd12_3 [1, 1, 4] = true := by decide +kernel
theorem subd12_3_516 : subd12_3 [1, 1, 5] = true := by decide +kernel
theorem subd12_3_517 : subd12_3 [1, 1, 6] = true := by decide +kernel
theorem subd12_3_518 : subd12_3 [1, 1, 7] = true := by decide +kernel
theorem subd12_3_519 : subd12_3 [1, 1, 8] = true := by decide +kernel
theorem subd12_3_520 : subd12_3 [1, 1, 9] = true := by decide +kernel
theorem subd12_3_521 : subd12_3 [1, 2, -9] = true := by decide +kernel
theorem subd12_3_522 : subd12_3 [1, 2, -8] = true := by decide +kernel
theorem subd12_3_523 : subd12_3 [1, 2, -7] = true := by decide +kernel
theorem subd12_3_524 : subd12_3 [1, 2, -6] = true := by decide +kernel
theorem subd12_3_525 : subd12_3 [1, 2, -5] = true := by decide +kernel
theorem subd12_3_526 : subd12_3 [1, 2, -4] = true := by decide +kernel
theorem subd12_3_527 : subd12_3 [1, 2, -3] = true := by decide +kernel
theorem subd12_3_528 : subd12_3 [1, 2, -2] = true := by decide +kernel
theorem subd12_3_529 : subd12_3 [1, 2, -1] = true := by decide +kernel
theorem subd12_3_530 : subd12_3 [1, 2, 0] = true := by decide +kernel
theorem subd12_3_531 : subd12_3 [1, 2, 1] = true := by decide +kernel
theorem subd12_3_532 : subd12_3 [1, 2, 2] = true := by decide +kernel
theorem subd12_3_533 : subd12_3 [1, 2, 3] = true := by decide +kernel
theorem subd12_3_534 : subd12_3 [1, 2, 4] = true := by decide +kernel
theorem subd12_3_535 : subd12_3 [1, 2, 5] = true := by decide +kernel
theorem subd12_3_536 : subd12_3 [1, 2, 6] = true := by decide +kernel
theorem subd12_3_537 : subd12_3 [1, 2, 7] = true := by decide +kernel
theorem subd12_3_538 : subd12_3 [1, 2, 8] = true := by decide +kernel
theorem subd12_3_539 : subd12_3 [1, 3, -8] = true := by decide +kernel
theorem subd12_3_540 : subd12_3 [1, 3, -7] = true := by decide +kernel
theorem subd12_3_541 : subd12_3 [1, 3, -6] = true := by decide +kernel
theorem subd12_3_542 : subd12_3 [1, 3, -5] = true := by decide +kernel
theorem subd12_3_543 : subd12_3 [1, 3, -4] = true := by decide +kernel
theorem sbd12_3_16 : ∀ q ∈ blkd12_3_16, subd12_3 q = true := by
  unfold blkd12_3_16
  exact List.forall_mem_cons.2 ⟨subd12_3_512, List.forall_mem_cons.2 ⟨subd12_3_513, List.forall_mem_cons.2 ⟨subd12_3_514, List.forall_mem_cons.2 ⟨subd12_3_515, List.forall_mem_cons.2 ⟨subd12_3_516, List.forall_mem_cons.2 ⟨subd12_3_517, List.forall_mem_cons.2 ⟨subd12_3_518, List.forall_mem_cons.2 ⟨subd12_3_519, List.forall_mem_cons.2 ⟨subd12_3_520, List.forall_mem_cons.2 ⟨subd12_3_521, List.forall_mem_cons.2 ⟨subd12_3_522, List.forall_mem_cons.2 ⟨subd12_3_523, List.forall_mem_cons.2 ⟨subd12_3_524, List.forall_mem_cons.2 ⟨subd12_3_525, List.forall_mem_cons.2 ⟨subd12_3_526, List.forall_mem_cons.2 ⟨subd12_3_527, List.forall_mem_cons.2 ⟨subd12_3_528, List.forall_mem_cons.2 ⟨subd12_3_529, List.forall_mem_cons.2 ⟨subd12_3_530, List.forall_mem_cons.2 ⟨subd12_3_531, List.forall_mem_cons.2 ⟨subd12_3_532, List.forall_mem_cons.2 ⟨subd12_3_533, List.forall_mem_cons.2 ⟨subd12_3_534, List.forall_mem_cons.2 ⟨subd12_3_535, List.forall_mem_cons.2 ⟨subd12_3_536, List.forall_mem_cons.2 ⟨subd12_3_537, List.forall_mem_cons.2 ⟨subd12_3_538, List.forall_mem_cons.2 ⟨subd12_3_539, List.forall_mem_cons.2 ⟨subd12_3_540, List.forall_mem_cons.2 ⟨subd12_3_541, List.forall_mem_cons.2 ⟨subd12_3_542, List.forall_mem_cons.2 ⟨subd12_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_544 : subd12_3 [1, 3, -3] = true := by decide +kernel
theorem subd12_3_545 : subd12_3 [1, 3, -2] = true := by decide +kernel
theorem subd12_3_546 : subd12_3 [1, 3, -1] = true := by decide +kernel
theorem subd12_3_547 : subd12_3 [1, 3, 0] = true := by decide +kernel
theorem subd12_3_548 : subd12_3 [1, 3, 1] = true := by decide +kernel
theorem subd12_3_549 : subd12_3 [1, 3, 2] = true := by decide +kernel
theorem subd12_3_550 : subd12_3 [1, 3, 3] = true := by decide +kernel
theorem subd12_3_551 : subd12_3 [1, 3, 4] = true := by decide +kernel
theorem subd12_3_552 : subd12_3 [1, 3, 5] = true := by decide +kernel
theorem subd12_3_553 : subd12_3 [1, 3, 6] = true := by decide +kernel
theorem subd12_3_554 : subd12_3 [1, 3, 7] = true := by decide +kernel
theorem subd12_3_555 : subd12_3 [1, 4, -7] = true := by decide +kernel
theorem subd12_3_556 : subd12_3 [1, 4, -6] = true := by decide +kernel
theorem subd12_3_557 : subd12_3 [1, 4, -5] = true := by decide +kernel
theorem subd12_3_558 : subd12_3 [1, 4, -4] = true := by decide +kernel
theorem subd12_3_559 : subd12_3 [1, 4, -3] = true := by decide +kernel
theorem subd12_3_560 : subd12_3 [1, 4, -2] = true := by decide +kernel
theorem subd12_3_561 : subd12_3 [1, 4, -1] = true := by decide +kernel
theorem subd12_3_562 : subd12_3 [1, 4, 0] = true := by decide +kernel
theorem subd12_3_563 : subd12_3 [1, 4, 1] = true := by decide +kernel
theorem subd12_3_564 : subd12_3 [1, 4, 2] = true := by decide +kernel
theorem subd12_3_565 : subd12_3 [1, 4, 3] = true := by decide +kernel
theorem subd12_3_566 : subd12_3 [1, 4, 4] = true := by decide +kernel
theorem subd12_3_567 : subd12_3 [1, 4, 5] = true := by decide +kernel
theorem subd12_3_568 : subd12_3 [1, 5] = true := by decide +kernel
theorem subd12_3_569 : subd12_3 [2, -4] = true := by decide +kernel
theorem subd12_3_570 : subd12_3 [2, -3] = true := by decide +kernel
theorem subd12_3_571 : subd12_3 [2, -2, -5] = true := by decide +kernel
theorem subd12_3_572 : subd12_3 [2, -2, -4] = true := by decide +kernel
theorem subd12_3_573 : subd12_3 [2, -2, -3] = true := by decide +kernel
theorem subd12_3_574 : subd12_3 [2, -2, -2] = true := by decide +kernel
theorem subd12_3_575 : subd12_3 [2, -2, -1] = true := by decide +kernel
theorem sbd12_3_17 : ∀ q ∈ blkd12_3_17, subd12_3 q = true := by
  unfold blkd12_3_17
  exact List.forall_mem_cons.2 ⟨subd12_3_544, List.forall_mem_cons.2 ⟨subd12_3_545, List.forall_mem_cons.2 ⟨subd12_3_546, List.forall_mem_cons.2 ⟨subd12_3_547, List.forall_mem_cons.2 ⟨subd12_3_548, List.forall_mem_cons.2 ⟨subd12_3_549, List.forall_mem_cons.2 ⟨subd12_3_550, List.forall_mem_cons.2 ⟨subd12_3_551, List.forall_mem_cons.2 ⟨subd12_3_552, List.forall_mem_cons.2 ⟨subd12_3_553, List.forall_mem_cons.2 ⟨subd12_3_554, List.forall_mem_cons.2 ⟨subd12_3_555, List.forall_mem_cons.2 ⟨subd12_3_556, List.forall_mem_cons.2 ⟨subd12_3_557, List.forall_mem_cons.2 ⟨subd12_3_558, List.forall_mem_cons.2 ⟨subd12_3_559, List.forall_mem_cons.2 ⟨subd12_3_560, List.forall_mem_cons.2 ⟨subd12_3_561, List.forall_mem_cons.2 ⟨subd12_3_562, List.forall_mem_cons.2 ⟨subd12_3_563, List.forall_mem_cons.2 ⟨subd12_3_564, List.forall_mem_cons.2 ⟨subd12_3_565, List.forall_mem_cons.2 ⟨subd12_3_566, List.forall_mem_cons.2 ⟨subd12_3_567, List.forall_mem_cons.2 ⟨subd12_3_568, List.forall_mem_cons.2 ⟨subd12_3_569, List.forall_mem_cons.2 ⟨subd12_3_570, List.forall_mem_cons.2 ⟨subd12_3_571, List.forall_mem_cons.2 ⟨subd12_3_572, List.forall_mem_cons.2 ⟨subd12_3_573, List.forall_mem_cons.2 ⟨subd12_3_574, List.forall_mem_cons.2 ⟨subd12_3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_576 : subd12_3 [2, -2, 0] = true := by decide +kernel
theorem subd12_3_577 : subd12_3 [2, -2, 1] = true := by decide +kernel
theorem subd12_3_578 : subd12_3 [2, -2, 2] = true := by decide +kernel
theorem subd12_3_579 : subd12_3 [2, -2, 3] = true := by decide +kernel
theorem subd12_3_580 : subd12_3 [2, -2, 4] = true := by decide +kernel
theorem subd12_3_581 : subd12_3 [2, -2, 5] = true := by decide +kernel
theorem subd12_3_582 : subd12_3 [2, -2, 6] = true := by decide +kernel
theorem subd12_3_583 : subd12_3 [2, -2, 7] = true := by decide +kernel
theorem subd12_3_584 : subd12_3 [2, -1, -7] = true := by decide +kernel
theorem subd12_3_585 : subd12_3 [2, -1, -6] = true := by decide +kernel
theorem subd12_3_586 : subd12_3 [2, -1, -5] = true := by decide +kernel
theorem subd12_3_587 : subd12_3 [2, -1, -4] = true := by decide +kernel
theorem subd12_3_588 : subd12_3 [2, -1, -3] = true := by decide +kernel
theorem subd12_3_589 : subd12_3 [2, -1, -2] = true := by decide +kernel
theorem subd12_3_590 : subd12_3 [2, -1, -1] = true := by decide +kernel
theorem subd12_3_591 : subd12_3 [2, -1, 0] = true := by decide +kernel
theorem subd12_3_592 : subd12_3 [2, -1, 1] = true := by decide +kernel
theorem subd12_3_593 : subd12_3 [2, -1, 2] = true := by decide +kernel
theorem subd12_3_594 : subd12_3 [2, -1, 3] = true := by decide +kernel
theorem subd12_3_595 : subd12_3 [2, -1, 4] = true := by decide +kernel
theorem subd12_3_596 : subd12_3 [2, -1, 5] = true := by decide +kernel
theorem subd12_3_597 : subd12_3 [2, -1, 6] = true := by decide +kernel
theorem subd12_3_598 : subd12_3 [2, -1, 7] = true := by decide +kernel
theorem subd12_3_599 : subd12_3 [2, -1, 8] = true := by decide +kernel
theorem subd12_3_600 : subd12_3 [2, 0, -8] = true := by decide +kernel
theorem subd12_3_601 : subd12_3 [2, 0, -7] = true := by decide +kernel
theorem subd12_3_602 : subd12_3 [2, 0, -6] = true := by decide +kernel
theorem subd12_3_603 : subd12_3 [2, 0, -5] = true := by decide +kernel
theorem subd12_3_604 : subd12_3 [2, 0, -4] = true := by decide +kernel
theorem subd12_3_605 : subd12_3 [2, 0, -3] = true := by decide +kernel
theorem subd12_3_606 : subd12_3 [2, 0, -2] = true := by decide +kernel
theorem subd12_3_607 : subd12_3 [2, 0, -1] = true := by decide +kernel
theorem sbd12_3_18 : ∀ q ∈ blkd12_3_18, subd12_3 q = true := by
  unfold blkd12_3_18
  exact List.forall_mem_cons.2 ⟨subd12_3_576, List.forall_mem_cons.2 ⟨subd12_3_577, List.forall_mem_cons.2 ⟨subd12_3_578, List.forall_mem_cons.2 ⟨subd12_3_579, List.forall_mem_cons.2 ⟨subd12_3_580, List.forall_mem_cons.2 ⟨subd12_3_581, List.forall_mem_cons.2 ⟨subd12_3_582, List.forall_mem_cons.2 ⟨subd12_3_583, List.forall_mem_cons.2 ⟨subd12_3_584, List.forall_mem_cons.2 ⟨subd12_3_585, List.forall_mem_cons.2 ⟨subd12_3_586, List.forall_mem_cons.2 ⟨subd12_3_587, List.forall_mem_cons.2 ⟨subd12_3_588, List.forall_mem_cons.2 ⟨subd12_3_589, List.forall_mem_cons.2 ⟨subd12_3_590, List.forall_mem_cons.2 ⟨subd12_3_591, List.forall_mem_cons.2 ⟨subd12_3_592, List.forall_mem_cons.2 ⟨subd12_3_593, List.forall_mem_cons.2 ⟨subd12_3_594, List.forall_mem_cons.2 ⟨subd12_3_595, List.forall_mem_cons.2 ⟨subd12_3_596, List.forall_mem_cons.2 ⟨subd12_3_597, List.forall_mem_cons.2 ⟨subd12_3_598, List.forall_mem_cons.2 ⟨subd12_3_599, List.forall_mem_cons.2 ⟨subd12_3_600, List.forall_mem_cons.2 ⟨subd12_3_601, List.forall_mem_cons.2 ⟨subd12_3_602, List.forall_mem_cons.2 ⟨subd12_3_603, List.forall_mem_cons.2 ⟨subd12_3_604, List.forall_mem_cons.2 ⟨subd12_3_605, List.forall_mem_cons.2 ⟨subd12_3_606, List.forall_mem_cons.2 ⟨subd12_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_608 : subd12_3 [2, 0, 0] = true := by decide +kernel
theorem subd12_3_609 : subd12_3 [2, 0, 1] = true := by decide +kernel
theorem subd12_3_610 : subd12_3 [2, 0, 2] = true := by decide +kernel
theorem subd12_3_611 : subd12_3 [2, 0, 3] = true := by decide +kernel
theorem subd12_3_612 : subd12_3 [2, 0, 4] = true := by decide +kernel
theorem subd12_3_613 : subd12_3 [2, 0, 5] = true := by decide +kernel
theorem subd12_3_614 : subd12_3 [2, 0, 6] = true := by decide +kernel
theorem subd12_3_615 : subd12_3 [2, 0, 7] = true := by decide +kernel
theorem subd12_3_616 : subd12_3 [2, 0, 8] = true := by decide +kernel
theorem subd12_3_617 : subd12_3 [2, 0, 9] = true := by decide +kernel
theorem subd12_3_618 : subd12_3 [2, 1, -8] = true := by decide +kernel
theorem subd12_3_619 : subd12_3 [2, 1, -7] = true := by decide +kernel
theorem subd12_3_620 : subd12_3 [2, 1, -6] = true := by decide +kernel
theorem subd12_3_621 : subd12_3 [2, 1, -5] = true := by decide +kernel
theorem subd12_3_622 : subd12_3 [2, 1, -4] = true := by decide +kernel
theorem subd12_3_623 : subd12_3 [2, 1, -3] = true := by decide +kernel
theorem subd12_3_624 : subd12_3 [2, 1, -2] = true := by decide +kernel
theorem subd12_3_625 : subd12_3 [2, 1, -1] = true := by decide +kernel
theorem subd12_3_626 : subd12_3 [2, 1, 0] = true := by decide +kernel
theorem subd12_3_627 : subd12_3 [2, 1, 1] = true := by decide +kernel
theorem subd12_3_628 : subd12_3 [2, 1, 2] = true := by decide +kernel
theorem subd12_3_629 : subd12_3 [2, 1, 3] = true := by decide +kernel
theorem subd12_3_630 : subd12_3 [2, 1, 4] = true := by decide +kernel
theorem subd12_3_631 : subd12_3 [2, 1, 5] = true := by decide +kernel
theorem subd12_3_632 : subd12_3 [2, 1, 6] = true := by decide +kernel
theorem subd12_3_633 : subd12_3 [2, 1, 7] = true := by decide +kernel
theorem subd12_3_634 : subd12_3 [2, 1, 8] = true := by decide +kernel
theorem subd12_3_635 : subd12_3 [2, 2, -8] = true := by decide +kernel
theorem subd12_3_636 : subd12_3 [2, 2, -7] = true := by decide +kernel
theorem subd12_3_637 : subd12_3 [2, 2, -6] = true := by decide +kernel
theorem subd12_3_638 : subd12_3 [2, 2, -5] = true := by decide +kernel
theorem subd12_3_639 : subd12_3 [2, 2, -4] = true := by decide +kernel
theorem sbd12_3_19 : ∀ q ∈ blkd12_3_19, subd12_3 q = true := by
  unfold blkd12_3_19
  exact List.forall_mem_cons.2 ⟨subd12_3_608, List.forall_mem_cons.2 ⟨subd12_3_609, List.forall_mem_cons.2 ⟨subd12_3_610, List.forall_mem_cons.2 ⟨subd12_3_611, List.forall_mem_cons.2 ⟨subd12_3_612, List.forall_mem_cons.2 ⟨subd12_3_613, List.forall_mem_cons.2 ⟨subd12_3_614, List.forall_mem_cons.2 ⟨subd12_3_615, List.forall_mem_cons.2 ⟨subd12_3_616, List.forall_mem_cons.2 ⟨subd12_3_617, List.forall_mem_cons.2 ⟨subd12_3_618, List.forall_mem_cons.2 ⟨subd12_3_619, List.forall_mem_cons.2 ⟨subd12_3_620, List.forall_mem_cons.2 ⟨subd12_3_621, List.forall_mem_cons.2 ⟨subd12_3_622, List.forall_mem_cons.2 ⟨subd12_3_623, List.forall_mem_cons.2 ⟨subd12_3_624, List.forall_mem_cons.2 ⟨subd12_3_625, List.forall_mem_cons.2 ⟨subd12_3_626, List.forall_mem_cons.2 ⟨subd12_3_627, List.forall_mem_cons.2 ⟨subd12_3_628, List.forall_mem_cons.2 ⟨subd12_3_629, List.forall_mem_cons.2 ⟨subd12_3_630, List.forall_mem_cons.2 ⟨subd12_3_631, List.forall_mem_cons.2 ⟨subd12_3_632, List.forall_mem_cons.2 ⟨subd12_3_633, List.forall_mem_cons.2 ⟨subd12_3_634, List.forall_mem_cons.2 ⟨subd12_3_635, List.forall_mem_cons.2 ⟨subd12_3_636, List.forall_mem_cons.2 ⟨subd12_3_637, List.forall_mem_cons.2 ⟨subd12_3_638, List.forall_mem_cons.2 ⟨subd12_3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_640 : subd12_3 [2, 2, -3] = true := by decide +kernel
theorem subd12_3_641 : subd12_3 [2, 2, -2] = true := by decide +kernel
theorem subd12_3_642 : subd12_3 [2, 2, -1] = true := by decide +kernel
theorem subd12_3_643 : subd12_3 [2, 2, 0] = true := by decide +kernel
theorem subd12_3_644 : subd12_3 [2, 2, 1] = true := by decide +kernel
theorem subd12_3_645 : subd12_3 [2, 2, 2] = true := by decide +kernel
theorem subd12_3_646 : subd12_3 [2, 2, 3] = true := by decide +kernel
theorem subd12_3_647 : subd12_3 [2, 2, 4] = true := by decide +kernel
theorem subd12_3_648 : subd12_3 [2, 2, 5] = true := by decide +kernel
theorem subd12_3_649 : subd12_3 [2, 2, 6] = true := by decide +kernel
theorem subd12_3_650 : subd12_3 [2, 2, 7] = true := by decide +kernel
theorem subd12_3_651 : subd12_3 [2, 2, 8] = true := by decide +kernel
theorem subd12_3_652 : subd12_3 [2, 3, -8] = true := by decide +kernel
theorem subd12_3_653 : subd12_3 [2, 3, -7] = true := by decide +kernel
theorem subd12_3_654 : subd12_3 [2, 3, -6] = true := by decide +kernel
theorem subd12_3_655 : subd12_3 [2, 3, -5] = true := by decide +kernel
theorem subd12_3_656 : subd12_3 [2, 3, -4] = true := by decide +kernel
theorem subd12_3_657 : subd12_3 [2, 3, -3] = true := by decide +kernel
theorem subd12_3_658 : subd12_3 [2, 3, -2] = true := by decide +kernel
theorem subd12_3_659 : subd12_3 [2, 3, -1] = true := by decide +kernel
theorem subd12_3_660 : subd12_3 [2, 3, 0] = true := by decide +kernel
theorem subd12_3_661 : subd12_3 [2, 3, 1] = true := by decide +kernel
theorem subd12_3_662 : subd12_3 [2, 3, 2] = true := by decide +kernel
theorem subd12_3_663 : subd12_3 [2, 3, 3] = true := by decide +kernel
theorem subd12_3_664 : subd12_3 [2, 3, 4] = true := by decide +kernel
theorem subd12_3_665 : subd12_3 [2, 3, 5] = true := by decide +kernel
theorem subd12_3_666 : subd12_3 [2, 3, 6] = true := by decide +kernel
theorem subd12_3_667 : subd12_3 [2, 3, 7] = true := by decide +kernel
theorem subd12_3_668 : subd12_3 [2, 4] = true := by decide +kernel
theorem subd12_3_669 : subd12_3 [2, 5] = true := by decide +kernel
theorem subd12_3_670 : subd12_3 [3, -3] = true := by decide +kernel
theorem subd12_3_671 : subd12_3 [3, -2] = true := by decide +kernel
theorem sbd12_3_20 : ∀ q ∈ blkd12_3_20, subd12_3 q = true := by
  unfold blkd12_3_20
  exact List.forall_mem_cons.2 ⟨subd12_3_640, List.forall_mem_cons.2 ⟨subd12_3_641, List.forall_mem_cons.2 ⟨subd12_3_642, List.forall_mem_cons.2 ⟨subd12_3_643, List.forall_mem_cons.2 ⟨subd12_3_644, List.forall_mem_cons.2 ⟨subd12_3_645, List.forall_mem_cons.2 ⟨subd12_3_646, List.forall_mem_cons.2 ⟨subd12_3_647, List.forall_mem_cons.2 ⟨subd12_3_648, List.forall_mem_cons.2 ⟨subd12_3_649, List.forall_mem_cons.2 ⟨subd12_3_650, List.forall_mem_cons.2 ⟨subd12_3_651, List.forall_mem_cons.2 ⟨subd12_3_652, List.forall_mem_cons.2 ⟨subd12_3_653, List.forall_mem_cons.2 ⟨subd12_3_654, List.forall_mem_cons.2 ⟨subd12_3_655, List.forall_mem_cons.2 ⟨subd12_3_656, List.forall_mem_cons.2 ⟨subd12_3_657, List.forall_mem_cons.2 ⟨subd12_3_658, List.forall_mem_cons.2 ⟨subd12_3_659, List.forall_mem_cons.2 ⟨subd12_3_660, List.forall_mem_cons.2 ⟨subd12_3_661, List.forall_mem_cons.2 ⟨subd12_3_662, List.forall_mem_cons.2 ⟨subd12_3_663, List.forall_mem_cons.2 ⟨subd12_3_664, List.forall_mem_cons.2 ⟨subd12_3_665, List.forall_mem_cons.2 ⟨subd12_3_666, List.forall_mem_cons.2 ⟨subd12_3_667, List.forall_mem_cons.2 ⟨subd12_3_668, List.forall_mem_cons.2 ⟨subd12_3_669, List.forall_mem_cons.2 ⟨subd12_3_670, List.forall_mem_cons.2 ⟨subd12_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
