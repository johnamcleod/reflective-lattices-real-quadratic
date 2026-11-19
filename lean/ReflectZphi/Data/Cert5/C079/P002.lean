import ReflectZphi.Data.Cert5.C079.Base

namespace ReflectZphi.Data.Cert5.C079
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_192 : sub3 [0, 2, -7] = true := by decide +kernel
theorem sub3_193 : sub3 [0, 2, -6] = true := by decide +kernel
theorem sub3_194 : sub3 [0, 2, -5] = true := by decide +kernel
theorem sub3_195 : sub3 [0, 2, -4] = true := by decide +kernel
theorem sub3_196 : sub3 [0, 2, -3] = true := by decide +kernel
theorem sub3_197 : sub3 [0, 2, -2] = true := by decide +kernel
theorem sub3_198 : sub3 [0, 2, -1] = true := by decide +kernel
theorem sub3_199 : sub3 [0, 2, 0] = true := by decide +kernel
theorem sub3_200 : sub3 [0, 2, 1] = true := by decide +kernel
theorem sub3_201 : sub3 [0, 2, 2] = true := by decide +kernel
theorem sub3_202 : sub3 [0, 2, 3] = true := by decide +kernel
theorem sub3_203 : sub3 [0, 2, 4] = true := by decide +kernel
theorem sub3_204 : sub3 [0, 2, 5] = true := by decide +kernel
theorem sub3_205 : sub3 [0, 3] = true := by decide +kernel
theorem sub3_206 : sub3 [0, 4] = true := by decide +kernel
theorem sub3_207 : sub3 [0, 5] = true := by decide +kernel
theorem sub3_208 : sub3 [0, 6] = true := by decide +kernel
theorem sub3_209 : sub3 [1, -7] = true := by decide +kernel
theorem sub3_210 : sub3 [1, -6] = true := by decide +kernel
theorem sub3_211 : sub3 [1, -5] = true := by decide +kernel
theorem sub3_212 : sub3 [1, -4] = true := by decide +kernel
theorem sub3_213 : sub3 [1, -3] = true := by decide +kernel
theorem sub3_214 : sub3 [1, -2] = true := by decide +kernel
theorem sub3_215 : sub3 [1, -1, -6] = true := by decide +kernel
theorem sub3_216 : sub3 [1, -1, -5] = true := by decide +kernel
theorem sub3_217 : sub3 [1, -1, -4] = true := by decide +kernel
theorem sub3_218 : sub3 [1, -1, -3] = true := by decide +kernel
theorem sub3_219 : sub3 [1, -1, -2] = true := by decide +kernel
theorem sub3_220 : sub3 [1, -1, -1] = true := by decide +kernel
theorem sub3_221 : sub3 [1, -1, 0] = true := by decide +kernel
theorem sub3_222 : sub3 [1, -1, 1] = true := by decide +kernel
theorem sub3_223 : sub3 [1, -1, 2] = true := by decide +kernel
theorem sb3_6 : ∀ q ∈ blk3_6, sub3 q = true := by
  unfold blk3_6
  exact List.forall_mem_cons.2 ⟨sub3_192, List.forall_mem_cons.2 ⟨sub3_193, List.forall_mem_cons.2 ⟨sub3_194, List.forall_mem_cons.2 ⟨sub3_195, List.forall_mem_cons.2 ⟨sub3_196, List.forall_mem_cons.2 ⟨sub3_197, List.forall_mem_cons.2 ⟨sub3_198, List.forall_mem_cons.2 ⟨sub3_199, List.forall_mem_cons.2 ⟨sub3_200, List.forall_mem_cons.2 ⟨sub3_201, List.forall_mem_cons.2 ⟨sub3_202, List.forall_mem_cons.2 ⟨sub3_203, List.forall_mem_cons.2 ⟨sub3_204, List.forall_mem_cons.2 ⟨sub3_205, List.forall_mem_cons.2 ⟨sub3_206, List.forall_mem_cons.2 ⟨sub3_207, List.forall_mem_cons.2 ⟨sub3_208, List.forall_mem_cons.2 ⟨sub3_209, List.forall_mem_cons.2 ⟨sub3_210, List.forall_mem_cons.2 ⟨sub3_211, List.forall_mem_cons.2 ⟨sub3_212, List.forall_mem_cons.2 ⟨sub3_213, List.forall_mem_cons.2 ⟨sub3_214, List.forall_mem_cons.2 ⟨sub3_215, List.forall_mem_cons.2 ⟨sub3_216, List.forall_mem_cons.2 ⟨sub3_217, List.forall_mem_cons.2 ⟨sub3_218, List.forall_mem_cons.2 ⟨sub3_219, List.forall_mem_cons.2 ⟨sub3_220, List.forall_mem_cons.2 ⟨sub3_221, List.forall_mem_cons.2 ⟨sub3_222, List.forall_mem_cons.2 ⟨sub3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_224 : sub3 [1, -1, 3] = true := by decide +kernel
theorem sub3_225 : sub3 [1, -1, 4] = true := by decide +kernel
theorem sub3_226 : sub3 [1, -1, 5] = true := by decide +kernel
theorem sub3_227 : sub3 [1, -1, 6] = true := by decide +kernel
theorem sub3_228 : sub3 [1, 0, -7] = true := by decide +kernel
theorem sub3_229 : sub3 [1, 0, -6] = true := by decide +kernel
theorem sub3_230 : sub3 [1, 0, -5] = true := by decide +kernel
theorem sub3_231 : sub3 [1, 0, -4] = true := by decide +kernel
theorem sub3_232 : sub3 [1, 0, -3] = true := by decide +kernel
theorem sub3_233 : sub3 [1, 0, -2] = true := by decide +kernel
theorem sub3_234 : sub3 [1, 0, -1] = true := by decide +kernel
theorem sub3_235 : sub3 [1, 0, 0] = true := by decide +kernel
theorem sub3_236 : sub3 [1, 0, 1] = true := by decide +kernel
theorem sub3_237 : sub3 [1, 0, 2] = true := by decide +kernel
theorem sub3_238 : sub3 [1, 0, 3] = true := by decide +kernel
theorem sub3_239 : sub3 [1, 0, 4] = true := by decide +kernel
theorem sub3_240 : sub3 [1, 0, 5] = true := by decide +kernel
theorem sub3_241 : sub3 [1, 0, 6] = true := by decide +kernel
theorem sub3_242 : sub3 [1, 1, -7] = true := by decide +kernel
theorem sub3_243 : sub3 [1, 1, -6] = true := by decide +kernel
theorem sub3_244 : sub3 [1, 1, -5] = true := by decide +kernel
theorem sub3_245 : sub3 [1, 1, -4] = true := by decide +kernel
theorem sub3_246 : sub3 [1, 1, -3] = true := by decide +kernel
theorem sub3_247 : sub3 [1, 1, -2] = true := by decide +kernel
theorem sub3_248 : sub3 [1, 1, -1] = true := by decide +kernel
theorem sub3_249 : sub3 [1, 1, 0] = true := by decide +kernel
theorem sub3_250 : sub3 [1, 1, 1] = true := by decide +kernel
theorem sub3_251 : sub3 [1, 1, 2] = true := by decide +kernel
theorem sub3_252 : sub3 [1, 1, 3] = true := by decide +kernel
theorem sub3_253 : sub3 [1, 1, 4] = true := by decide +kernel
theorem sub3_254 : sub3 [1, 1, 5] = true := by decide +kernel
theorem sub3_255 : sub3 [1, 1, 6] = true := by decide +kernel
theorem sb3_7 : ∀ q ∈ blk3_7, sub3 q = true := by
  unfold blk3_7
  exact List.forall_mem_cons.2 ⟨sub3_224, List.forall_mem_cons.2 ⟨sub3_225, List.forall_mem_cons.2 ⟨sub3_226, List.forall_mem_cons.2 ⟨sub3_227, List.forall_mem_cons.2 ⟨sub3_228, List.forall_mem_cons.2 ⟨sub3_229, List.forall_mem_cons.2 ⟨sub3_230, List.forall_mem_cons.2 ⟨sub3_231, List.forall_mem_cons.2 ⟨sub3_232, List.forall_mem_cons.2 ⟨sub3_233, List.forall_mem_cons.2 ⟨sub3_234, List.forall_mem_cons.2 ⟨sub3_235, List.forall_mem_cons.2 ⟨sub3_236, List.forall_mem_cons.2 ⟨sub3_237, List.forall_mem_cons.2 ⟨sub3_238, List.forall_mem_cons.2 ⟨sub3_239, List.forall_mem_cons.2 ⟨sub3_240, List.forall_mem_cons.2 ⟨sub3_241, List.forall_mem_cons.2 ⟨sub3_242, List.forall_mem_cons.2 ⟨sub3_243, List.forall_mem_cons.2 ⟨sub3_244, List.forall_mem_cons.2 ⟨sub3_245, List.forall_mem_cons.2 ⟨sub3_246, List.forall_mem_cons.2 ⟨sub3_247, List.forall_mem_cons.2 ⟨sub3_248, List.forall_mem_cons.2 ⟨sub3_249, List.forall_mem_cons.2 ⟨sub3_250, List.forall_mem_cons.2 ⟨sub3_251, List.forall_mem_cons.2 ⟨sub3_252, List.forall_mem_cons.2 ⟨sub3_253, List.forall_mem_cons.2 ⟨sub3_254, List.forall_mem_cons.2 ⟨sub3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_256 : sub3 [1, 2] = true := by decide +kernel
theorem sub3_257 : sub3 [1, 3] = true := by decide +kernel
theorem sub3_258 : sub3 [1, 4] = true := by decide +kernel
theorem sub3_259 : sub3 [1, 5] = true := by decide +kernel
theorem sub3_260 : sub3 [1, 6] = true := by decide +kernel
theorem sub3_261 : sub3 [2, -7] = true := by decide +kernel
theorem sub3_262 : sub3 [2, -6] = true := by decide +kernel
theorem sub3_263 : sub3 [2, -5] = true := by decide +kernel
theorem sub3_264 : sub3 [2, -4] = true := by decide +kernel
theorem sub3_265 : sub3 [2, -3] = true := by decide +kernel
theorem sub3_266 : sub3 [2, -2] = true := by decide +kernel
theorem sub3_267 : sub3 [2, -1, -6] = true := by decide +kernel
theorem sub3_268 : sub3 [2, -1, -5] = true := by decide +kernel
theorem sub3_269 : sub3 [2, -1, -4] = true := by decide +kernel
theorem sub3_270 : sub3 [2, -1, -3] = true := by decide +kernel
theorem sub3_271 : sub3 [2, -1, -2] = true := by decide +kernel
theorem sub3_272 : sub3 [2, -1, -1] = true := by decide +kernel
theorem sub3_273 : sub3 [2, -1, 0] = true := by decide +kernel
theorem sub3_274 : sub3 [2, -1, 1] = true := by decide +kernel
theorem sub3_275 : sub3 [2, -1, 2] = true := by decide +kernel
theorem sub3_276 : sub3 [2, -1, 3] = true := by decide +kernel
theorem sub3_277 : sub3 [2, -1, 4] = true := by decide +kernel
theorem sub3_278 : sub3 [2, -1, 5] = true := by decide +kernel
theorem sub3_279 : sub3 [2, -1, 6] = true := by decide +kernel
theorem sub3_280 : sub3 [2, -1, 7] = true := by decide +kernel
theorem sub3_281 : sub3 [2, 0, -6] = true := by decide +kernel
theorem sub3_282 : sub3 [2, 0, -5] = true := by decide +kernel
theorem sub3_283 : sub3 [2, 0, -4] = true := by decide +kernel
theorem sub3_284 : sub3 [2, 0, -3] = true := by decide +kernel
theorem sub3_285 : sub3 [2, 0, -2] = true := by decide +kernel
theorem sub3_286 : sub3 [2, 0, -1] = true := by decide +kernel
theorem sub3_287 : sub3 [2, 0, 0] = true := by decide +kernel
theorem sb3_8 : ∀ q ∈ blk3_8, sub3 q = true := by
  unfold blk3_8
  exact List.forall_mem_cons.2 ⟨sub3_256, List.forall_mem_cons.2 ⟨sub3_257, List.forall_mem_cons.2 ⟨sub3_258, List.forall_mem_cons.2 ⟨sub3_259, List.forall_mem_cons.2 ⟨sub3_260, List.forall_mem_cons.2 ⟨sub3_261, List.forall_mem_cons.2 ⟨sub3_262, List.forall_mem_cons.2 ⟨sub3_263, List.forall_mem_cons.2 ⟨sub3_264, List.forall_mem_cons.2 ⟨sub3_265, List.forall_mem_cons.2 ⟨sub3_266, List.forall_mem_cons.2 ⟨sub3_267, List.forall_mem_cons.2 ⟨sub3_268, List.forall_mem_cons.2 ⟨sub3_269, List.forall_mem_cons.2 ⟨sub3_270, List.forall_mem_cons.2 ⟨sub3_271, List.forall_mem_cons.2 ⟨sub3_272, List.forall_mem_cons.2 ⟨sub3_273, List.forall_mem_cons.2 ⟨sub3_274, List.forall_mem_cons.2 ⟨sub3_275, List.forall_mem_cons.2 ⟨sub3_276, List.forall_mem_cons.2 ⟨sub3_277, List.forall_mem_cons.2 ⟨sub3_278, List.forall_mem_cons.2 ⟨sub3_279, List.forall_mem_cons.2 ⟨sub3_280, List.forall_mem_cons.2 ⟨sub3_281, List.forall_mem_cons.2 ⟨sub3_282, List.forall_mem_cons.2 ⟨sub3_283, List.forall_mem_cons.2 ⟨sub3_284, List.forall_mem_cons.2 ⟨sub3_285, List.forall_mem_cons.2 ⟨sub3_286, List.forall_mem_cons.2 ⟨sub3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_288 : sub3 [2, 0, 1] = true := by decide +kernel
theorem sub3_289 : sub3 [2, 0, 2] = true := by decide +kernel
theorem sub3_290 : sub3 [2, 0, 3] = true := by decide +kernel
theorem sub3_291 : sub3 [2, 0, 4] = true := by decide +kernel
theorem sub3_292 : sub3 [2, 0, 5] = true := by decide +kernel
theorem sub3_293 : sub3 [2, 0, 6] = true := by decide +kernel
theorem sub3_294 : sub3 [2, 1] = true := by decide +kernel
theorem sub3_295 : sub3 [2, 2] = true := by decide +kernel
theorem sub3_296 : sub3 [2, 3] = true := by decide +kernel
theorem sub3_297 : sub3 [2, 4] = true := by decide +kernel
theorem sub3_298 : sub3 [2, 5] = true := by decide +kernel
theorem sub3_299 : sub3 [3, -7] = true := by decide +kernel
theorem sub3_300 : sub3 [3, -6] = true := by decide +kernel
theorem sub3_301 : sub3 [3, -5] = true := by decide +kernel
theorem sub3_302 : sub3 [3, -4] = true := by decide +kernel
theorem sub3_303 : sub3 [3, -3] = true := by decide +kernel
theorem sub3_304 : sub3 [3, -2] = true := by decide +kernel
theorem sub3_305 : sub3 [3, -1] = true := by decide +kernel
theorem sub3_306 : sub3 [3, 0] = true := by decide +kernel
theorem sub3_307 : sub3 [3, 1] = true := by decide +kernel
theorem sub3_308 : sub3 [3, 2] = true := by decide +kernel
theorem sub3_309 : sub3 [3, 3] = true := by decide +kernel
theorem sub3_310 : sub3 [3, 4] = true := by decide +kernel
theorem sub3_311 : sub3 [3, 5] = true := by decide +kernel
theorem sub3_312 : sub3 [4, -6] = true := by decide +kernel
theorem sub3_313 : sub3 [4, -5] = true := by decide +kernel
theorem sub3_314 : sub3 [4, -4] = true := by decide +kernel
theorem sub3_315 : sub3 [4, -3] = true := by decide +kernel
theorem sub3_316 : sub3 [4, -2] = true := by decide +kernel
theorem sub3_317 : sub3 [4, -1] = true := by decide +kernel
theorem sub3_318 : sub3 [4, 0] = true := by decide +kernel
theorem sub3_319 : sub3 [4, 1] = true := by decide +kernel
theorem sb3_9 : ∀ q ∈ blk3_9, sub3 q = true := by
  unfold blk3_9
  exact List.forall_mem_cons.2 ⟨sub3_288, List.forall_mem_cons.2 ⟨sub3_289, List.forall_mem_cons.2 ⟨sub3_290, List.forall_mem_cons.2 ⟨sub3_291, List.forall_mem_cons.2 ⟨sub3_292, List.forall_mem_cons.2 ⟨sub3_293, List.forall_mem_cons.2 ⟨sub3_294, List.forall_mem_cons.2 ⟨sub3_295, List.forall_mem_cons.2 ⟨sub3_296, List.forall_mem_cons.2 ⟨sub3_297, List.forall_mem_cons.2 ⟨sub3_298, List.forall_mem_cons.2 ⟨sub3_299, List.forall_mem_cons.2 ⟨sub3_300, List.forall_mem_cons.2 ⟨sub3_301, List.forall_mem_cons.2 ⟨sub3_302, List.forall_mem_cons.2 ⟨sub3_303, List.forall_mem_cons.2 ⟨sub3_304, List.forall_mem_cons.2 ⟨sub3_305, List.forall_mem_cons.2 ⟨sub3_306, List.forall_mem_cons.2 ⟨sub3_307, List.forall_mem_cons.2 ⟨sub3_308, List.forall_mem_cons.2 ⟨sub3_309, List.forall_mem_cons.2 ⟨sub3_310, List.forall_mem_cons.2 ⟨sub3_311, List.forall_mem_cons.2 ⟨sub3_312, List.forall_mem_cons.2 ⟨sub3_313, List.forall_mem_cons.2 ⟨sub3_314, List.forall_mem_cons.2 ⟨sub3_315, List.forall_mem_cons.2 ⟨sub3_316, List.forall_mem_cons.2 ⟨sub3_317, List.forall_mem_cons.2 ⟨sub3_318, List.forall_mem_cons.2 ⟨sub3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_320 : sub3 [4, 2] = true := by decide +kernel
theorem sub3_321 : sub3 [4, 3] = true := by decide +kernel
theorem sub3_322 : sub3 [4, 4] = true := by decide +kernel
theorem sub3_323 : sub3 [5, -6] = true := by decide +kernel
theorem sub3_324 : sub3 [5, -5] = true := by decide +kernel
theorem sub3_325 : sub3 [5, -4] = true := by decide +kernel
theorem sub3_326 : sub3 [5, -3] = true := by decide +kernel
theorem sub3_327 : sub3 [5, -2] = true := by decide +kernel
theorem sub3_328 : sub3 [5, -1] = true := by decide +kernel
theorem sub3_329 : sub3 [5, 0] = true := by decide +kernel
theorem sub3_330 : sub3 [5, 1] = true := by decide +kernel
theorem sub3_331 : sub3 [5, 2] = true := by decide +kernel
theorem sub3_332 : sub3 [5, 3] = true := by decide +kernel
theorem sub3_333 : sub3 [6, -5] = true := by decide +kernel
theorem sub3_334 : sub3 [6, -4] = true := by decide +kernel
theorem sub3_335 : sub3 [6, -3] = true := by decide +kernel
theorem sub3_336 : sub3 [6, -2] = true := by decide +kernel
theorem sub3_337 : sub3 [6, -1] = true := by decide +kernel
theorem sub3_338 : sub3 [6, 0] = true := by decide +kernel
theorem sub3_339 : sub3 [6, 1] = true := by decide +kernel
theorem sub3_340 : sub3 [6, 2] = true := by decide +kernel
theorem sb3_10 : ∀ q ∈ blk3_10, sub3 q = true := by
  unfold blk3_10
  exact List.forall_mem_cons.2 ⟨sub3_320, List.forall_mem_cons.2 ⟨sub3_321, List.forall_mem_cons.2 ⟨sub3_322, List.forall_mem_cons.2 ⟨sub3_323, List.forall_mem_cons.2 ⟨sub3_324, List.forall_mem_cons.2 ⟨sub3_325, List.forall_mem_cons.2 ⟨sub3_326, List.forall_mem_cons.2 ⟨sub3_327, List.forall_mem_cons.2 ⟨sub3_328, List.forall_mem_cons.2 ⟨sub3_329, List.forall_mem_cons.2 ⟨sub3_330, List.forall_mem_cons.2 ⟨sub3_331, List.forall_mem_cons.2 ⟨sub3_332, List.forall_mem_cons.2 ⟨sub3_333, List.forall_mem_cons.2 ⟨sub3_334, List.forall_mem_cons.2 ⟨sub3_335, List.forall_mem_cons.2 ⟨sub3_336, List.forall_mem_cons.2 ⟨sub3_337, List.forall_mem_cons.2 ⟨sub3_338, List.forall_mem_cons.2 ⟨sub3_339, List.forall_mem_cons.2 ⟨sub3_340, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_0 : sub4 [-6, -2] = true := by decide +kernel
theorem sub4_1 : sub4 [-6, -1] = true := by decide +kernel
theorem sub4_2 : sub4 [-6, 0] = true := by decide +kernel
theorem sub4_3 : sub4 [-6, 1] = true := by decide +kernel
theorem sub4_4 : sub4 [-6, 2] = true := by decide +kernel
theorem sub4_5 : sub4 [-6, 3] = true := by decide +kernel
theorem sub4_6 : sub4 [-6, 4] = true := by decide +kernel
theorem sub4_7 : sub4 [-5, -4] = true := by decide +kernel
theorem sub4_8 : sub4 [-5, -3] = true := by decide +kernel
theorem sub4_9 : sub4 [-5, -2] = true := by decide +kernel
theorem sub4_10 : sub4 [-5, -1, -9] = true := by decide +kernel
theorem sub4_11 : sub4 [-5, -1, -8] = true := by decide +kernel
theorem sub4_12 : sub4 [-5, -1, -7] = true := by decide +kernel
theorem sub4_13 : sub4 [-5, -1, -6] = true := by decide +kernel
theorem sub4_14 : sub4 [-5, -1, -5] = true := by decide +kernel
theorem sub4_15 : sub4 [-5, -1, -4] = true := by decide +kernel
theorem sub4_16 : sub4 [-5, -1, -3] = true := by decide +kernel
theorem sub4_17 : sub4 [-5, -1, -2] = true := by decide +kernel
theorem sub4_18 : sub4 [-5, -1, -1] = true := by decide +kernel
theorem sub4_19 : sub4 [-5, -1, 0] = true := by decide +kernel
theorem sub4_20 : sub4 [-5, -1, 1] = true := by decide +kernel
theorem sub4_21 : sub4 [-5, -1, 2] = true := by decide +kernel
theorem sub4_22 : sub4 [-5, -1, 3] = true := by decide +kernel
theorem sub4_23 : sub4 [-5, -1, 4] = true := by decide +kernel
theorem sub4_24 : sub4 [-5, 0, -9] = true := by decide +kernel
theorem sub4_25 : sub4 [-5, 0, -8] = true := by decide +kernel
theorem sub4_26 : sub4 [-5, 0, -7] = true := by decide +kernel
theorem sub4_27 : sub4 [-5, 0, -6] = true := by decide +kernel
theorem sub4_28 : sub4 [-5, 0, -5] = true := by decide +kernel
theorem sub4_29 : sub4 [-5, 0, -4] = true := by decide +kernel
theorem sub4_30 : sub4 [-5, 0, -3] = true := by decide +kernel
theorem sub4_31 : sub4 [-5, 0, -2] = true := by decide +kernel
theorem sb4_0 : ∀ q ∈ blk4_0, sub4 q = true := by
  unfold blk4_0
  exact List.forall_mem_cons.2 ⟨sub4_0, List.forall_mem_cons.2 ⟨sub4_1, List.forall_mem_cons.2 ⟨sub4_2, List.forall_mem_cons.2 ⟨sub4_3, List.forall_mem_cons.2 ⟨sub4_4, List.forall_mem_cons.2 ⟨sub4_5, List.forall_mem_cons.2 ⟨sub4_6, List.forall_mem_cons.2 ⟨sub4_7, List.forall_mem_cons.2 ⟨sub4_8, List.forall_mem_cons.2 ⟨sub4_9, List.forall_mem_cons.2 ⟨sub4_10, List.forall_mem_cons.2 ⟨sub4_11, List.forall_mem_cons.2 ⟨sub4_12, List.forall_mem_cons.2 ⟨sub4_13, List.forall_mem_cons.2 ⟨sub4_14, List.forall_mem_cons.2 ⟨sub4_15, List.forall_mem_cons.2 ⟨sub4_16, List.forall_mem_cons.2 ⟨sub4_17, List.forall_mem_cons.2 ⟨sub4_18, List.forall_mem_cons.2 ⟨sub4_19, List.forall_mem_cons.2 ⟨sub4_20, List.forall_mem_cons.2 ⟨sub4_21, List.forall_mem_cons.2 ⟨sub4_22, List.forall_mem_cons.2 ⟨sub4_23, List.forall_mem_cons.2 ⟨sub4_24, List.forall_mem_cons.2 ⟨sub4_25, List.forall_mem_cons.2 ⟨sub4_26, List.forall_mem_cons.2 ⟨sub4_27, List.forall_mem_cons.2 ⟨sub4_28, List.forall_mem_cons.2 ⟨sub4_29, List.forall_mem_cons.2 ⟨sub4_30, List.forall_mem_cons.2 ⟨sub4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_32 : sub4 [-5, 0, -1] = true := by decide +kernel
theorem sub4_33 : sub4 [-5, 0, 0] = true := by decide +kernel
theorem sub4_34 : sub4 [-5, 0, 1] = true := by decide +kernel
theorem sub4_35 : sub4 [-5, 0, 2] = true := by decide +kernel
theorem sub4_36 : sub4 [-5, 0, 3] = true := by decide +kernel
theorem sub4_37 : sub4 [-5, 0, 4] = true := by decide +kernel
theorem sub4_38 : sub4 [-5, 1, -10] = true := by decide +kernel
theorem sub4_39 : sub4 [-5, 1, -9] = true := by decide +kernel
theorem sub4_40 : sub4 [-5, 1, -8] = true := by decide +kernel
theorem sub4_41 : sub4 [-5, 1, -7] = true := by decide +kernel
theorem sub4_42 : sub4 [-5, 1, -6] = true := by decide +kernel
theorem sub4_43 : sub4 [-5, 1, -5] = true := by decide +kernel
theorem sub4_44 : sub4 [-5, 1, -4] = true := by decide +kernel
theorem sub4_45 : sub4 [-5, 1, -3] = true := by decide +kernel
theorem sub4_46 : sub4 [-5, 1, -2] = true := by decide +kernel
theorem sub4_47 : sub4 [-5, 1, -1] = true := by decide +kernel
theorem sub4_48 : sub4 [-5, 1, 0] = true := by decide +kernel
theorem sub4_49 : sub4 [-5, 1, 1] = true := by decide +kernel
theorem sub4_50 : sub4 [-5, 1, 2] = true := by decide +kernel
theorem sub4_51 : sub4 [-5, 1, 3] = true := by decide +kernel
theorem sub4_52 : sub4 [-5, 1, 4] = true := by decide +kernel
theorem sub4_53 : sub4 [-5, 1, 5] = true := by decide +kernel
theorem sub4_54 : sub4 [-5, 2, -9] = true := by decide +kernel
theorem sub4_55 : sub4 [-5, 2, -8] = true := by decide +kernel
theorem sub4_56 : sub4 [-5, 2, -7] = true := by decide +kernel
theorem sub4_57 : sub4 [-5, 2, -6] = true := by decide +kernel
theorem sub4_58 : sub4 [-5, 2, -5] = true := by decide +kernel
theorem sub4_59 : sub4 [-5, 2, -4] = true := by decide +kernel
theorem sub4_60 : sub4 [-5, 2, -3] = true := by decide +kernel
theorem sub4_61 : sub4 [-5, 2, -2] = true := by decide +kernel
theorem sub4_62 : sub4 [-5, 2, -1] = true := by decide +kernel
theorem sub4_63 : sub4 [-5, 2, 0] = true := by decide +kernel
theorem sb4_1 : ∀ q ∈ blk4_1, sub4 q = true := by
  unfold blk4_1
  exact List.forall_mem_cons.2 ⟨sub4_32, List.forall_mem_cons.2 ⟨sub4_33, List.forall_mem_cons.2 ⟨sub4_34, List.forall_mem_cons.2 ⟨sub4_35, List.forall_mem_cons.2 ⟨sub4_36, List.forall_mem_cons.2 ⟨sub4_37, List.forall_mem_cons.2 ⟨sub4_38, List.forall_mem_cons.2 ⟨sub4_39, List.forall_mem_cons.2 ⟨sub4_40, List.forall_mem_cons.2 ⟨sub4_41, List.forall_mem_cons.2 ⟨sub4_42, List.forall_mem_cons.2 ⟨sub4_43, List.forall_mem_cons.2 ⟨sub4_44, List.forall_mem_cons.2 ⟨sub4_45, List.forall_mem_cons.2 ⟨sub4_46, List.forall_mem_cons.2 ⟨sub4_47, List.forall_mem_cons.2 ⟨sub4_48, List.forall_mem_cons.2 ⟨sub4_49, List.forall_mem_cons.2 ⟨sub4_50, List.forall_mem_cons.2 ⟨sub4_51, List.forall_mem_cons.2 ⟨sub4_52, List.forall_mem_cons.2 ⟨sub4_53, List.forall_mem_cons.2 ⟨sub4_54, List.forall_mem_cons.2 ⟨sub4_55, List.forall_mem_cons.2 ⟨sub4_56, List.forall_mem_cons.2 ⟨sub4_57, List.forall_mem_cons.2 ⟨sub4_58, List.forall_mem_cons.2 ⟨sub4_59, List.forall_mem_cons.2 ⟨sub4_60, List.forall_mem_cons.2 ⟨sub4_61, List.forall_mem_cons.2 ⟨sub4_62, List.forall_mem_cons.2 ⟨sub4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C079
