import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_6_192 : subd4_6 [1, -6] = true := by decide +kernel
theorem subd4_6_193 : subd4_6 [1, -5] = true := by decide +kernel
theorem subd4_6_194 : subd4_6 [1, -4] = true := by decide +kernel
theorem subd4_6_195 : subd4_6 [1, -3] = true := by decide +kernel
theorem subd4_6_196 : subd4_6 [1, -2, -7] = true := by decide +kernel
theorem subd4_6_197 : subd4_6 [1, -2, -6] = true := by decide +kernel
theorem subd4_6_198 : subd4_6 [1, -2, -5] = true := by decide +kernel
theorem subd4_6_199 : subd4_6 [1, -2, -4] = true := by decide +kernel
theorem subd4_6_200 : subd4_6 [1, -2, -3] = true := by decide +kernel
theorem subd4_6_201 : subd4_6 [1, -2, -2] = true := by decide +kernel
theorem subd4_6_202 : subd4_6 [1, -2, -1] = true := by decide +kernel
theorem subd4_6_203 : subd4_6 [1, -2, 0] = true := by decide +kernel
theorem subd4_6_204 : subd4_6 [1, -2, 1] = true := by decide +kernel
theorem subd4_6_205 : subd4_6 [1, -2, 2] = true := by decide +kernel
theorem subd4_6_206 : subd4_6 [1, -2, 3] = true := by decide +kernel
theorem subd4_6_207 : subd4_6 [1, -2, 4] = true := by decide +kernel
theorem subd4_6_208 : subd4_6 [1, -2, 5] = true := by decide +kernel
theorem subd4_6_209 : subd4_6 [1, -1, -7] = true := by decide +kernel
theorem subd4_6_210 : subd4_6 [1, -1, -6] = true := by decide +kernel
theorem subd4_6_211 : subd4_6 [1, -1, -5] = true := by decide +kernel
theorem subd4_6_212 : subd4_6 [1, -1, -4] = true := by decide +kernel
theorem subd4_6_213 : subd4_6 [1, -1, -3] = true := by decide +kernel
theorem subd4_6_214 : subd4_6 [1, -1, -2] = true := by decide +kernel
theorem subd4_6_215 : subd4_6 [1, -1, -1] = true := by decide +kernel
theorem subd4_6_216 : subd4_6 [1, -1, 0] = true := by decide +kernel
theorem subd4_6_217 : subd4_6 [1, -1, 1] = true := by decide +kernel
theorem subd4_6_218 : subd4_6 [1, -1, 2] = true := by decide +kernel
theorem subd4_6_219 : subd4_6 [1, -1, 3] = true := by decide +kernel
theorem subd4_6_220 : subd4_6 [1, -1, 4] = true := by decide +kernel
theorem subd4_6_221 : subd4_6 [1, -1, 5] = true := by decide +kernel
theorem subd4_6_222 : subd4_6 [1, -1, 6] = true := by decide +kernel
theorem subd4_6_223 : subd4_6 [1, 0, -7] = true := by decide +kernel
theorem sbd4_6_6 : ∀ q ∈ blkd4_6_6, subd4_6 q = true := by
  unfold blkd4_6_6
  exact List.forall_mem_cons.2 ⟨subd4_6_192, List.forall_mem_cons.2 ⟨subd4_6_193, List.forall_mem_cons.2 ⟨subd4_6_194, List.forall_mem_cons.2 ⟨subd4_6_195, List.forall_mem_cons.2 ⟨subd4_6_196, List.forall_mem_cons.2 ⟨subd4_6_197, List.forall_mem_cons.2 ⟨subd4_6_198, List.forall_mem_cons.2 ⟨subd4_6_199, List.forall_mem_cons.2 ⟨subd4_6_200, List.forall_mem_cons.2 ⟨subd4_6_201, List.forall_mem_cons.2 ⟨subd4_6_202, List.forall_mem_cons.2 ⟨subd4_6_203, List.forall_mem_cons.2 ⟨subd4_6_204, List.forall_mem_cons.2 ⟨subd4_6_205, List.forall_mem_cons.2 ⟨subd4_6_206, List.forall_mem_cons.2 ⟨subd4_6_207, List.forall_mem_cons.2 ⟨subd4_6_208, List.forall_mem_cons.2 ⟨subd4_6_209, List.forall_mem_cons.2 ⟨subd4_6_210, List.forall_mem_cons.2 ⟨subd4_6_211, List.forall_mem_cons.2 ⟨subd4_6_212, List.forall_mem_cons.2 ⟨subd4_6_213, List.forall_mem_cons.2 ⟨subd4_6_214, List.forall_mem_cons.2 ⟨subd4_6_215, List.forall_mem_cons.2 ⟨subd4_6_216, List.forall_mem_cons.2 ⟨subd4_6_217, List.forall_mem_cons.2 ⟨subd4_6_218, List.forall_mem_cons.2 ⟨subd4_6_219, List.forall_mem_cons.2 ⟨subd4_6_220, List.forall_mem_cons.2 ⟨subd4_6_221, List.forall_mem_cons.2 ⟨subd4_6_222, List.forall_mem_cons.2 ⟨subd4_6_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_224 : subd4_6 [1, 0, -6] = true := by decide +kernel
theorem subd4_6_225 : subd4_6 [1, 0, -5] = true := by decide +kernel
theorem subd4_6_226 : subd4_6 [1, 0, -4] = true := by decide +kernel
theorem subd4_6_227 : subd4_6 [1, 0, -3] = true := by decide +kernel
theorem subd4_6_228 : subd4_6 [1, 0, -2] = true := by decide +kernel
theorem subd4_6_229 : subd4_6 [1, 0, -1] = true := by decide +kernel
theorem subd4_6_230 : subd4_6 [1, 0, 0] = true := by decide +kernel
theorem subd4_6_231 : subd4_6 [1, 0, 1] = true := by decide +kernel
theorem subd4_6_232 : subd4_6 [1, 0, 2] = true := by decide +kernel
theorem subd4_6_233 : subd4_6 [1, 0, 3] = true := by decide +kernel
theorem subd4_6_234 : subd4_6 [1, 0, 4] = true := by decide +kernel
theorem subd4_6_235 : subd4_6 [1, 0, 5] = true := by decide +kernel
theorem subd4_6_236 : subd4_6 [1, 0, 6] = true := by decide +kernel
theorem subd4_6_237 : subd4_6 [1, 1, -7] = true := by decide +kernel
theorem subd4_6_238 : subd4_6 [1, 1, -6] = true := by decide +kernel
theorem subd4_6_239 : subd4_6 [1, 1, -5] = true := by decide +kernel
theorem subd4_6_240 : subd4_6 [1, 1, -4] = true := by decide +kernel
theorem subd4_6_241 : subd4_6 [1, 1, -3] = true := by decide +kernel
theorem subd4_6_242 : subd4_6 [1, 1, -2] = true := by decide +kernel
theorem subd4_6_243 : subd4_6 [1, 1, -1] = true := by decide +kernel
theorem subd4_6_244 : subd4_6 [1, 1, 0] = true := by decide +kernel
theorem subd4_6_245 : subd4_6 [1, 1, 1] = true := by decide +kernel
theorem subd4_6_246 : subd4_6 [1, 1, 2] = true := by decide +kernel
theorem subd4_6_247 : subd4_6 [1, 1, 3] = true := by decide +kernel
theorem subd4_6_248 : subd4_6 [1, 1, 4] = true := by decide +kernel
theorem subd4_6_249 : subd4_6 [1, 1, 5] = true := by decide +kernel
theorem subd4_6_250 : subd4_6 [1, 1, 6] = true := by decide +kernel
theorem subd4_6_251 : subd4_6 [1, 2] = true := by decide +kernel
theorem subd4_6_252 : subd4_6 [1, 3] = true := by decide +kernel
theorem subd4_6_253 : subd4_6 [1, 4] = true := by decide +kernel
theorem subd4_6_254 : subd4_6 [1, 5] = true := by decide +kernel
theorem subd4_6_255 : subd4_6 [2, -6] = true := by decide +kernel
theorem sbd4_6_7 : ∀ q ∈ blkd4_6_7, subd4_6 q = true := by
  unfold blkd4_6_7
  exact List.forall_mem_cons.2 ⟨subd4_6_224, List.forall_mem_cons.2 ⟨subd4_6_225, List.forall_mem_cons.2 ⟨subd4_6_226, List.forall_mem_cons.2 ⟨subd4_6_227, List.forall_mem_cons.2 ⟨subd4_6_228, List.forall_mem_cons.2 ⟨subd4_6_229, List.forall_mem_cons.2 ⟨subd4_6_230, List.forall_mem_cons.2 ⟨subd4_6_231, List.forall_mem_cons.2 ⟨subd4_6_232, List.forall_mem_cons.2 ⟨subd4_6_233, List.forall_mem_cons.2 ⟨subd4_6_234, List.forall_mem_cons.2 ⟨subd4_6_235, List.forall_mem_cons.2 ⟨subd4_6_236, List.forall_mem_cons.2 ⟨subd4_6_237, List.forall_mem_cons.2 ⟨subd4_6_238, List.forall_mem_cons.2 ⟨subd4_6_239, List.forall_mem_cons.2 ⟨subd4_6_240, List.forall_mem_cons.2 ⟨subd4_6_241, List.forall_mem_cons.2 ⟨subd4_6_242, List.forall_mem_cons.2 ⟨subd4_6_243, List.forall_mem_cons.2 ⟨subd4_6_244, List.forall_mem_cons.2 ⟨subd4_6_245, List.forall_mem_cons.2 ⟨subd4_6_246, List.forall_mem_cons.2 ⟨subd4_6_247, List.forall_mem_cons.2 ⟨subd4_6_248, List.forall_mem_cons.2 ⟨subd4_6_249, List.forall_mem_cons.2 ⟨subd4_6_250, List.forall_mem_cons.2 ⟨subd4_6_251, List.forall_mem_cons.2 ⟨subd4_6_252, List.forall_mem_cons.2 ⟨subd4_6_253, List.forall_mem_cons.2 ⟨subd4_6_254, List.forall_mem_cons.2 ⟨subd4_6_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_256 : subd4_6 [2, -5] = true := by decide +kernel
theorem subd4_6_257 : subd4_6 [2, -4] = true := by decide +kernel
theorem subd4_6_258 : subd4_6 [2, -3] = true := by decide +kernel
theorem subd4_6_259 : subd4_6 [2, -2] = true := by decide +kernel
theorem subd4_6_260 : subd4_6 [2, -1, -7] = true := by decide +kernel
theorem subd4_6_261 : subd4_6 [2, -1, -6] = true := by decide +kernel
theorem subd4_6_262 : subd4_6 [2, -1, -5] = true := by decide +kernel
theorem subd4_6_263 : subd4_6 [2, -1, -4] = true := by decide +kernel
theorem subd4_6_264 : subd4_6 [2, -1, -3] = true := by decide +kernel
theorem subd4_6_265 : subd4_6 [2, -1, -2] = true := by decide +kernel
theorem subd4_6_266 : subd4_6 [2, -1, -1] = true := by decide +kernel
theorem subd4_6_267 : subd4_6 [2, -1, 0] = true := by decide +kernel
theorem subd4_6_268 : subd4_6 [2, -1, 1] = true := by decide +kernel
theorem subd4_6_269 : subd4_6 [2, -1, 2] = true := by decide +kernel
theorem subd4_6_270 : subd4_6 [2, -1, 3] = true := by decide +kernel
theorem subd4_6_271 : subd4_6 [2, -1, 4] = true := by decide +kernel
theorem subd4_6_272 : subd4_6 [2, -1, 5] = true := by decide +kernel
theorem subd4_6_273 : subd4_6 [2, -1, 6] = true := by decide +kernel
theorem subd4_6_274 : subd4_6 [2, 0, -7] = true := by decide +kernel
theorem subd4_6_275 : subd4_6 [2, 0, -6] = true := by decide +kernel
theorem subd4_6_276 : subd4_6 [2, 0, -5] = true := by decide +kernel
theorem subd4_6_277 : subd4_6 [2, 0, -4] = true := by decide +kernel
theorem subd4_6_278 : subd4_6 [2, 0, -3] = true := by decide +kernel
theorem subd4_6_279 : subd4_6 [2, 0, -2] = true := by decide +kernel
theorem subd4_6_280 : subd4_6 [2, 0, -1] = true := by decide +kernel
theorem subd4_6_281 : subd4_6 [2, 0, 0] = true := by decide +kernel
theorem subd4_6_282 : subd4_6 [2, 0, 1] = true := by decide +kernel
theorem subd4_6_283 : subd4_6 [2, 0, 2] = true := by decide +kernel
theorem subd4_6_284 : subd4_6 [2, 0, 3] = true := by decide +kernel
theorem subd4_6_285 : subd4_6 [2, 0, 4] = true := by decide +kernel
theorem subd4_6_286 : subd4_6 [2, 0, 5] = true := by decide +kernel
theorem subd4_6_287 : subd4_6 [2, 0, 6] = true := by decide +kernel
theorem sbd4_6_8 : ∀ q ∈ blkd4_6_8, subd4_6 q = true := by
  unfold blkd4_6_8
  exact List.forall_mem_cons.2 ⟨subd4_6_256, List.forall_mem_cons.2 ⟨subd4_6_257, List.forall_mem_cons.2 ⟨subd4_6_258, List.forall_mem_cons.2 ⟨subd4_6_259, List.forall_mem_cons.2 ⟨subd4_6_260, List.forall_mem_cons.2 ⟨subd4_6_261, List.forall_mem_cons.2 ⟨subd4_6_262, List.forall_mem_cons.2 ⟨subd4_6_263, List.forall_mem_cons.2 ⟨subd4_6_264, List.forall_mem_cons.2 ⟨subd4_6_265, List.forall_mem_cons.2 ⟨subd4_6_266, List.forall_mem_cons.2 ⟨subd4_6_267, List.forall_mem_cons.2 ⟨subd4_6_268, List.forall_mem_cons.2 ⟨subd4_6_269, List.forall_mem_cons.2 ⟨subd4_6_270, List.forall_mem_cons.2 ⟨subd4_6_271, List.forall_mem_cons.2 ⟨subd4_6_272, List.forall_mem_cons.2 ⟨subd4_6_273, List.forall_mem_cons.2 ⟨subd4_6_274, List.forall_mem_cons.2 ⟨subd4_6_275, List.forall_mem_cons.2 ⟨subd4_6_276, List.forall_mem_cons.2 ⟨subd4_6_277, List.forall_mem_cons.2 ⟨subd4_6_278, List.forall_mem_cons.2 ⟨subd4_6_279, List.forall_mem_cons.2 ⟨subd4_6_280, List.forall_mem_cons.2 ⟨subd4_6_281, List.forall_mem_cons.2 ⟨subd4_6_282, List.forall_mem_cons.2 ⟨subd4_6_283, List.forall_mem_cons.2 ⟨subd4_6_284, List.forall_mem_cons.2 ⟨subd4_6_285, List.forall_mem_cons.2 ⟨subd4_6_286, List.forall_mem_cons.2 ⟨subd4_6_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_288 : subd4_6 [2, 1] = true := by decide +kernel
theorem subd4_6_289 : subd4_6 [2, 2] = true := by decide +kernel
theorem subd4_6_290 : subd4_6 [2, 3] = true := by decide +kernel
theorem subd4_6_291 : subd4_6 [2, 4] = true := by decide +kernel
theorem subd4_6_292 : subd4_6 [3, -5] = true := by decide +kernel
theorem subd4_6_293 : subd4_6 [3, -4] = true := by decide +kernel
theorem subd4_6_294 : subd4_6 [3, -3] = true := by decide +kernel
theorem subd4_6_295 : subd4_6 [3, -2] = true := by decide +kernel
theorem subd4_6_296 : subd4_6 [3, -1] = true := by decide +kernel
theorem subd4_6_297 : subd4_6 [3, 0] = true := by decide +kernel
theorem subd4_6_298 : subd4_6 [3, 1] = true := by decide +kernel
theorem subd4_6_299 : subd4_6 [3, 2] = true := by decide +kernel
theorem subd4_6_300 : subd4_6 [3, 3] = true := by decide +kernel
theorem subd4_6_301 : subd4_6 [4, -4] = true := by decide +kernel
theorem subd4_6_302 : subd4_6 [4, -3] = true := by decide +kernel
theorem subd4_6_303 : subd4_6 [4, -2] = true := by decide +kernel
theorem subd4_6_304 : subd4_6 [4, -1] = true := by decide +kernel
theorem subd4_6_305 : subd4_6 [4, 0] = true := by decide +kernel
theorem subd4_6_306 : subd4_6 [4, 1] = true := by decide +kernel
theorem subd4_6_307 : subd4_6 [4, 2] = true := by decide +kernel
theorem subd4_6_308 : subd4_6 [5] = true := by decide +kernel
theorem sbd4_6_9 : ∀ q ∈ blkd4_6_9, subd4_6 q = true := by
  unfold blkd4_6_9
  exact List.forall_mem_cons.2 ⟨subd4_6_288, List.forall_mem_cons.2 ⟨subd4_6_289, List.forall_mem_cons.2 ⟨subd4_6_290, List.forall_mem_cons.2 ⟨subd4_6_291, List.forall_mem_cons.2 ⟨subd4_6_292, List.forall_mem_cons.2 ⟨subd4_6_293, List.forall_mem_cons.2 ⟨subd4_6_294, List.forall_mem_cons.2 ⟨subd4_6_295, List.forall_mem_cons.2 ⟨subd4_6_296, List.forall_mem_cons.2 ⟨subd4_6_297, List.forall_mem_cons.2 ⟨subd4_6_298, List.forall_mem_cons.2 ⟨subd4_6_299, List.forall_mem_cons.2 ⟨subd4_6_300, List.forall_mem_cons.2 ⟨subd4_6_301, List.forall_mem_cons.2 ⟨subd4_6_302, List.forall_mem_cons.2 ⟨subd4_6_303, List.forall_mem_cons.2 ⟨subd4_6_304, List.forall_mem_cons.2 ⟨subd4_6_305, List.forall_mem_cons.2 ⟨subd4_6_306, List.forall_mem_cons.2 ⟨subd4_6_307, List.forall_mem_cons.2 ⟨subd4_6_308, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_7 : ldCheck G d4_7.U d4_7.ms ldd4_7 = true := by decide +kernel
theorem pre_okd4_7 : subPre G cell4 d4_7 = true := by decide +kernel
theorem subd4_7_0 : subd4_7 [-4] = true := by decide +kernel
theorem subd4_7_1 : subd4_7 [-3, -3] = true := by decide +kernel
theorem subd4_7_2 : subd4_7 [-3, -2] = true := by decide +kernel
theorem subd4_7_3 : subd4_7 [-3, -1] = true := by decide +kernel
theorem subd4_7_4 : subd4_7 [-3, 0] = true := by decide +kernel
theorem subd4_7_5 : subd4_7 [-3, 1] = true := by decide +kernel
theorem subd4_7_6 : subd4_7 [-3, 2] = true := by decide +kernel
theorem subd4_7_7 : subd4_7 [-3, 3] = true := by decide +kernel
theorem subd4_7_8 : subd4_7 [-3, 4] = true := by decide +kernel
theorem subd4_7_9 : subd4_7 [-2, -4] = true := by decide +kernel
theorem subd4_7_10 : subd4_7 [-2, -3] = true := by decide +kernel
theorem subd4_7_11 : subd4_7 [-2, -2] = true := by decide +kernel
theorem subd4_7_12 : subd4_7 [-2, -1] = true := by decide +kernel
theorem subd4_7_13 : subd4_7 [-2, 0] = true := by decide +kernel
theorem subd4_7_14 : subd4_7 [-2, 1] = true := by decide +kernel
theorem subd4_7_15 : subd4_7 [-2, 2] = true := by decide +kernel
theorem subd4_7_16 : subd4_7 [-2, 3] = true := by decide +kernel
theorem subd4_7_17 : subd4_7 [-2, 4] = true := by decide +kernel
theorem subd4_7_18 : subd4_7 [-1, -5] = true := by decide +kernel
theorem subd4_7_19 : subd4_7 [-1, -4] = true := by decide +kernel
theorem subd4_7_20 : subd4_7 [-1, -3] = true := by decide +kernel
theorem subd4_7_21 : subd4_7 [-1, -2] = true := by decide +kernel
theorem subd4_7_22 : subd4_7 [-1, -1, -8] = true := by decide +kernel
theorem subd4_7_23 : subd4_7 [-1, -1, -7] = true := by decide +kernel
theorem subd4_7_24 : subd4_7 [-1, -1, -6] = true := by decide +kernel
theorem subd4_7_25 : subd4_7 [-1, -1, -5] = true := by decide +kernel
theorem subd4_7_26 : subd4_7 [-1, -1, -4] = true := by decide +kernel
theorem subd4_7_27 : subd4_7 [-1, -1, -3] = true := by decide +kernel
theorem subd4_7_28 : subd4_7 [-1, -1, -2] = true := by decide +kernel
theorem subd4_7_29 : subd4_7 [-1, -1, -1] = true := by decide +kernel
theorem subd4_7_30 : subd4_7 [-1, -1, 0] = true := by decide +kernel
theorem subd4_7_31 : subd4_7 [-1, -1, 1] = true := by decide +kernel
theorem sbd4_7_0 : ∀ q ∈ blkd4_7_0, subd4_7 q = true := by
  unfold blkd4_7_0
  exact List.forall_mem_cons.2 ⟨subd4_7_0, List.forall_mem_cons.2 ⟨subd4_7_1, List.forall_mem_cons.2 ⟨subd4_7_2, List.forall_mem_cons.2 ⟨subd4_7_3, List.forall_mem_cons.2 ⟨subd4_7_4, List.forall_mem_cons.2 ⟨subd4_7_5, List.forall_mem_cons.2 ⟨subd4_7_6, List.forall_mem_cons.2 ⟨subd4_7_7, List.forall_mem_cons.2 ⟨subd4_7_8, List.forall_mem_cons.2 ⟨subd4_7_9, List.forall_mem_cons.2 ⟨subd4_7_10, List.forall_mem_cons.2 ⟨subd4_7_11, List.forall_mem_cons.2 ⟨subd4_7_12, List.forall_mem_cons.2 ⟨subd4_7_13, List.forall_mem_cons.2 ⟨subd4_7_14, List.forall_mem_cons.2 ⟨subd4_7_15, List.forall_mem_cons.2 ⟨subd4_7_16, List.forall_mem_cons.2 ⟨subd4_7_17, List.forall_mem_cons.2 ⟨subd4_7_18, List.forall_mem_cons.2 ⟨subd4_7_19, List.forall_mem_cons.2 ⟨subd4_7_20, List.forall_mem_cons.2 ⟨subd4_7_21, List.forall_mem_cons.2 ⟨subd4_7_22, List.forall_mem_cons.2 ⟨subd4_7_23, List.forall_mem_cons.2 ⟨subd4_7_24, List.forall_mem_cons.2 ⟨subd4_7_25, List.forall_mem_cons.2 ⟨subd4_7_26, List.forall_mem_cons.2 ⟨subd4_7_27, List.forall_mem_cons.2 ⟨subd4_7_28, List.forall_mem_cons.2 ⟨subd4_7_29, List.forall_mem_cons.2 ⟨subd4_7_30, List.forall_mem_cons.2 ⟨subd4_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_32 : subd4_7 [-1, -1, 2] = true := by decide +kernel
theorem subd4_7_33 : subd4_7 [-1, -1, 3] = true := by decide +kernel
theorem subd4_7_34 : subd4_7 [-1, -1, 4] = true := by decide +kernel
theorem subd4_7_35 : subd4_7 [-1, -1, 5] = true := by decide +kernel
theorem subd4_7_36 : subd4_7 [-1, -1, 6] = true := by decide +kernel
theorem subd4_7_37 : subd4_7 [-1, 0, -8] = true := by decide +kernel
theorem subd4_7_38 : subd4_7 [-1, 0, -7] = true := by decide +kernel
theorem subd4_7_39 : subd4_7 [-1, 0, -6] = true := by decide +kernel
theorem subd4_7_40 : subd4_7 [-1, 0, -5] = true := by decide +kernel
theorem subd4_7_41 : subd4_7 [-1, 0, -4] = true := by decide +kernel
theorem subd4_7_42 : subd4_7 [-1, 0, -3] = true := by decide +kernel
theorem subd4_7_43 : subd4_7 [-1, 0, -2] = true := by decide +kernel
theorem subd4_7_44 : subd4_7 [-1, 0, -1] = true := by decide +kernel
theorem subd4_7_45 : subd4_7 [-1, 0, 0] = true := by decide +kernel
theorem subd4_7_46 : subd4_7 [-1, 0, 1] = true := by decide +kernel
theorem subd4_7_47 : subd4_7 [-1, 0, 2] = true := by decide +kernel
theorem subd4_7_48 : subd4_7 [-1, 0, 3] = true := by decide +kernel
theorem subd4_7_49 : subd4_7 [-1, 0, 4] = true := by decide +kernel
theorem subd4_7_50 : subd4_7 [-1, 0, 5] = true := by decide +kernel
theorem subd4_7_51 : subd4_7 [-1, 0, 6] = true := by decide +kernel
theorem subd4_7_52 : subd4_7 [-1, 0, 7] = true := by decide +kernel
theorem subd4_7_53 : subd4_7 [-1, 1, -8] = true := by decide +kernel
theorem subd4_7_54 : subd4_7 [-1, 1, -7] = true := by decide +kernel
theorem subd4_7_55 : subd4_7 [-1, 1, -6] = true := by decide +kernel
theorem subd4_7_56 : subd4_7 [-1, 1, -5] = true := by decide +kernel
theorem subd4_7_57 : subd4_7 [-1, 1, -4] = true := by decide +kernel
theorem subd4_7_58 : subd4_7 [-1, 1, -3] = true := by decide +kernel
theorem subd4_7_59 : subd4_7 [-1, 1, -2] = true := by decide +kernel
theorem subd4_7_60 : subd4_7 [-1, 1, -1] = true := by decide +kernel
theorem subd4_7_61 : subd4_7 [-1, 1, 0] = true := by decide +kernel
theorem subd4_7_62 : subd4_7 [-1, 1, 1] = true := by decide +kernel
theorem subd4_7_63 : subd4_7 [-1, 1, 2] = true := by decide +kernel
theorem sbd4_7_1 : ∀ q ∈ blkd4_7_1, subd4_7 q = true := by
  unfold blkd4_7_1
  exact List.forall_mem_cons.2 ⟨subd4_7_32, List.forall_mem_cons.2 ⟨subd4_7_33, List.forall_mem_cons.2 ⟨subd4_7_34, List.forall_mem_cons.2 ⟨subd4_7_35, List.forall_mem_cons.2 ⟨subd4_7_36, List.forall_mem_cons.2 ⟨subd4_7_37, List.forall_mem_cons.2 ⟨subd4_7_38, List.forall_mem_cons.2 ⟨subd4_7_39, List.forall_mem_cons.2 ⟨subd4_7_40, List.forall_mem_cons.2 ⟨subd4_7_41, List.forall_mem_cons.2 ⟨subd4_7_42, List.forall_mem_cons.2 ⟨subd4_7_43, List.forall_mem_cons.2 ⟨subd4_7_44, List.forall_mem_cons.2 ⟨subd4_7_45, List.forall_mem_cons.2 ⟨subd4_7_46, List.forall_mem_cons.2 ⟨subd4_7_47, List.forall_mem_cons.2 ⟨subd4_7_48, List.forall_mem_cons.2 ⟨subd4_7_49, List.forall_mem_cons.2 ⟨subd4_7_50, List.forall_mem_cons.2 ⟨subd4_7_51, List.forall_mem_cons.2 ⟨subd4_7_52, List.forall_mem_cons.2 ⟨subd4_7_53, List.forall_mem_cons.2 ⟨subd4_7_54, List.forall_mem_cons.2 ⟨subd4_7_55, List.forall_mem_cons.2 ⟨subd4_7_56, List.forall_mem_cons.2 ⟨subd4_7_57, List.forall_mem_cons.2 ⟨subd4_7_58, List.forall_mem_cons.2 ⟨subd4_7_59, List.forall_mem_cons.2 ⟨subd4_7_60, List.forall_mem_cons.2 ⟨subd4_7_61, List.forall_mem_cons.2 ⟨subd4_7_62, List.forall_mem_cons.2 ⟨subd4_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_64 : subd4_7 [-1, 1, 3] = true := by decide +kernel
theorem subd4_7_65 : subd4_7 [-1, 1, 4] = true := by decide +kernel
theorem subd4_7_66 : subd4_7 [-1, 1, 5] = true := by decide +kernel
theorem subd4_7_67 : subd4_7 [-1, 1, 6] = true := by decide +kernel
theorem subd4_7_68 : subd4_7 [-1, 1, 7] = true := by decide +kernel
theorem subd4_7_69 : subd4_7 [-1, 1, 8] = true := by decide +kernel
theorem subd4_7_70 : subd4_7 [-1, 2, -7] = true := by decide +kernel
theorem subd4_7_71 : subd4_7 [-1, 2, -6] = true := by decide +kernel
theorem subd4_7_72 : subd4_7 [-1, 2, -5] = true := by decide +kernel
theorem subd4_7_73 : subd4_7 [-1, 2, -4] = true := by decide +kernel
theorem subd4_7_74 : subd4_7 [-1, 2, -3] = true := by decide +kernel
theorem subd4_7_75 : subd4_7 [-1, 2, -2] = true := by decide +kernel
theorem subd4_7_76 : subd4_7 [-1, 2, -1] = true := by decide +kernel
theorem subd4_7_77 : subd4_7 [-1, 2, 0] = true := by decide +kernel
theorem subd4_7_78 : subd4_7 [-1, 2, 1] = true := by decide +kernel
theorem subd4_7_79 : subd4_7 [-1, 2, 2] = true := by decide +kernel
theorem subd4_7_80 : subd4_7 [-1, 2, 3] = true := by decide +kernel
theorem subd4_7_81 : subd4_7 [-1, 2, 4] = true := by decide +kernel
theorem subd4_7_82 : subd4_7 [-1, 2, 5] = true := by decide +kernel
theorem subd4_7_83 : subd4_7 [-1, 2, 6] = true := by decide +kernel
theorem subd4_7_84 : subd4_7 [-1, 2, 7] = true := by decide +kernel
theorem subd4_7_85 : subd4_7 [-1, 2, 8] = true := by decide +kernel
theorem subd4_7_86 : subd4_7 [-1, 3] = true := by decide +kernel
theorem subd4_7_87 : subd4_7 [-1, 4] = true := by decide +kernel
theorem subd4_7_88 : subd4_7 [0, -5] = true := by decide +kernel
theorem subd4_7_89 : subd4_7 [0, -4] = true := by decide +kernel
theorem subd4_7_90 : subd4_7 [0, -3] = true := by decide +kernel
theorem subd4_7_91 : subd4_7 [0, -2, -9] = true := by decide +kernel
theorem subd4_7_92 : subd4_7 [0, -2, -8] = true := by decide +kernel
theorem subd4_7_93 : subd4_7 [0, -2, -7] = true := by decide +kernel
theorem subd4_7_94 : subd4_7 [0, -2, -6] = true := by decide +kernel
theorem subd4_7_95 : subd4_7 [0, -2, -5] = true := by decide +kernel
theorem sbd4_7_2 : ∀ q ∈ blkd4_7_2, subd4_7 q = true := by
  unfold blkd4_7_2
  exact List.forall_mem_cons.2 ⟨subd4_7_64, List.forall_mem_cons.2 ⟨subd4_7_65, List.forall_mem_cons.2 ⟨subd4_7_66, List.forall_mem_cons.2 ⟨subd4_7_67, List.forall_mem_cons.2 ⟨subd4_7_68, List.forall_mem_cons.2 ⟨subd4_7_69, List.forall_mem_cons.2 ⟨subd4_7_70, List.forall_mem_cons.2 ⟨subd4_7_71, List.forall_mem_cons.2 ⟨subd4_7_72, List.forall_mem_cons.2 ⟨subd4_7_73, List.forall_mem_cons.2 ⟨subd4_7_74, List.forall_mem_cons.2 ⟨subd4_7_75, List.forall_mem_cons.2 ⟨subd4_7_76, List.forall_mem_cons.2 ⟨subd4_7_77, List.forall_mem_cons.2 ⟨subd4_7_78, List.forall_mem_cons.2 ⟨subd4_7_79, List.forall_mem_cons.2 ⟨subd4_7_80, List.forall_mem_cons.2 ⟨subd4_7_81, List.forall_mem_cons.2 ⟨subd4_7_82, List.forall_mem_cons.2 ⟨subd4_7_83, List.forall_mem_cons.2 ⟨subd4_7_84, List.forall_mem_cons.2 ⟨subd4_7_85, List.forall_mem_cons.2 ⟨subd4_7_86, List.forall_mem_cons.2 ⟨subd4_7_87, List.forall_mem_cons.2 ⟨subd4_7_88, List.forall_mem_cons.2 ⟨subd4_7_89, List.forall_mem_cons.2 ⟨subd4_7_90, List.forall_mem_cons.2 ⟨subd4_7_91, List.forall_mem_cons.2 ⟨subd4_7_92, List.forall_mem_cons.2 ⟨subd4_7_93, List.forall_mem_cons.2 ⟨subd4_7_94, List.forall_mem_cons.2 ⟨subd4_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_96 : subd4_7 [0, -2, -4] = true := by decide +kernel
theorem subd4_7_97 : subd4_7 [0, -2, -3] = true := by decide +kernel
theorem subd4_7_98 : subd4_7 [0, -2, -2] = true := by decide +kernel
theorem subd4_7_99 : subd4_7 [0, -2, -1] = true := by decide +kernel
theorem subd4_7_100 : subd4_7 [0, -2, 0] = true := by decide +kernel
theorem subd4_7_101 : subd4_7 [0, -2, 1] = true := by decide +kernel
theorem subd4_7_102 : subd4_7 [0, -2, 2] = true := by decide +kernel
theorem subd4_7_103 : subd4_7 [0, -2, 3] = true := by decide +kernel
theorem subd4_7_104 : subd4_7 [0, -2, 4] = true := by decide +kernel
theorem subd4_7_105 : subd4_7 [0, -2, 5] = true := by decide +kernel
theorem subd4_7_106 : subd4_7 [0, -2, 6] = true := by decide +kernel
theorem subd4_7_107 : subd4_7 [0, -1, -9] = true := by decide +kernel
theorem subd4_7_108 : subd4_7 [0, -1, -8] = true := by decide +kernel
theorem subd4_7_109 : subd4_7 [0, -1, -7] = true := by decide +kernel
theorem subd4_7_110 : subd4_7 [0, -1, -6] = true := by decide +kernel
theorem subd4_7_111 : subd4_7 [0, -1, -5] = true := by decide +kernel
theorem subd4_7_112 : subd4_7 [0, -1, -4] = true := by decide +kernel
theorem subd4_7_113 : subd4_7 [0, -1, -3] = true := by decide +kernel
theorem subd4_7_114 : subd4_7 [0, -1, -2] = true := by decide +kernel
theorem subd4_7_115 : subd4_7 [0, -1, -1] = true := by decide +kernel
theorem subd4_7_116 : subd4_7 [0, -1, 0] = true := by decide +kernel
theorem subd4_7_117 : subd4_7 [0, -1, 1] = true := by decide +kernel
theorem subd4_7_118 : subd4_7 [0, -1, 2] = true := by decide +kernel
theorem subd4_7_119 : subd4_7 [0, -1, 3] = true := by decide +kernel
theorem subd4_7_120 : subd4_7 [0, -1, 4] = true := by decide +kernel
theorem subd4_7_121 : subd4_7 [0, -1, 5] = true := by decide +kernel
theorem subd4_7_122 : subd4_7 [0, -1, 6] = true := by decide +kernel
theorem subd4_7_123 : subd4_7 [0, -1, 7] = true := by decide +kernel
theorem subd4_7_124 : subd4_7 [0, 0, -8] = true := by decide +kernel
theorem subd4_7_125 : subd4_7 [0, 0, -7] = true := by decide +kernel
theorem subd4_7_126 : subd4_7 [0, 0, -6] = true := by decide +kernel
theorem subd4_7_127 : subd4_7 [0, 0, -5] = true := by decide +kernel
theorem sbd4_7_3 : ∀ q ∈ blkd4_7_3, subd4_7 q = true := by
  unfold blkd4_7_3
  exact List.forall_mem_cons.2 ⟨subd4_7_96, List.forall_mem_cons.2 ⟨subd4_7_97, List.forall_mem_cons.2 ⟨subd4_7_98, List.forall_mem_cons.2 ⟨subd4_7_99, List.forall_mem_cons.2 ⟨subd4_7_100, List.forall_mem_cons.2 ⟨subd4_7_101, List.forall_mem_cons.2 ⟨subd4_7_102, List.forall_mem_cons.2 ⟨subd4_7_103, List.forall_mem_cons.2 ⟨subd4_7_104, List.forall_mem_cons.2 ⟨subd4_7_105, List.forall_mem_cons.2 ⟨subd4_7_106, List.forall_mem_cons.2 ⟨subd4_7_107, List.forall_mem_cons.2 ⟨subd4_7_108, List.forall_mem_cons.2 ⟨subd4_7_109, List.forall_mem_cons.2 ⟨subd4_7_110, List.forall_mem_cons.2 ⟨subd4_7_111, List.forall_mem_cons.2 ⟨subd4_7_112, List.forall_mem_cons.2 ⟨subd4_7_113, List.forall_mem_cons.2 ⟨subd4_7_114, List.forall_mem_cons.2 ⟨subd4_7_115, List.forall_mem_cons.2 ⟨subd4_7_116, List.forall_mem_cons.2 ⟨subd4_7_117, List.forall_mem_cons.2 ⟨subd4_7_118, List.forall_mem_cons.2 ⟨subd4_7_119, List.forall_mem_cons.2 ⟨subd4_7_120, List.forall_mem_cons.2 ⟨subd4_7_121, List.forall_mem_cons.2 ⟨subd4_7_122, List.forall_mem_cons.2 ⟨subd4_7_123, List.forall_mem_cons.2 ⟨subd4_7_124, List.forall_mem_cons.2 ⟨subd4_7_125, List.forall_mem_cons.2 ⟨subd4_7_126, List.forall_mem_cons.2 ⟨subd4_7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_128 : subd4_7 [0, 0, -4] = true := by decide +kernel
theorem subd4_7_129 : subd4_7 [0, 0, -3] = true := by decide +kernel
theorem subd4_7_130 : subd4_7 [0, 0, -2] = true := by decide +kernel
theorem subd4_7_131 : subd4_7 [0, 0, -1] = true := by decide +kernel
theorem subd4_7_132 : subd4_7 [0, 0, 0] = true := by decide +kernel
theorem subd4_7_133 : subd4_7 [0, 0, 1] = true := by decide +kernel
theorem subd4_7_134 : subd4_7 [0, 0, 2] = true := by decide +kernel
theorem subd4_7_135 : subd4_7 [0, 0, 3] = true := by decide +kernel
theorem subd4_7_136 : subd4_7 [0, 0, 4] = true := by decide +kernel
theorem subd4_7_137 : subd4_7 [0, 0, 5] = true := by decide +kernel
theorem subd4_7_138 : subd4_7 [0, 0, 6] = true := by decide +kernel
theorem subd4_7_139 : subd4_7 [0, 0, 7] = true := by decide +kernel
theorem subd4_7_140 : subd4_7 [0, 1, -8] = true := by decide +kernel
theorem subd4_7_141 : subd4_7 [0, 1, -7] = true := by decide +kernel
theorem subd4_7_142 : subd4_7 [0, 1, -6] = true := by decide +kernel
theorem subd4_7_143 : subd4_7 [0, 1, -5] = true := by decide +kernel
theorem subd4_7_144 : subd4_7 [0, 1, -4] = true := by decide +kernel
theorem subd4_7_145 : subd4_7 [0, 1, -3] = true := by decide +kernel
theorem subd4_7_146 : subd4_7 [0, 1, -2] = true := by decide +kernel
theorem subd4_7_147 : subd4_7 [0, 1, -1] = true := by decide +kernel
theorem subd4_7_148 : subd4_7 [0, 1, 0] = true := by decide +kernel
theorem subd4_7_149 : subd4_7 [0, 1, 1] = true := by decide +kernel
theorem subd4_7_150 : subd4_7 [0, 1, 2] = true := by decide +kernel
theorem subd4_7_151 : subd4_7 [0, 1, 3] = true := by decide +kernel
theorem subd4_7_152 : subd4_7 [0, 1, 4] = true := by decide +kernel
theorem subd4_7_153 : subd4_7 [0, 1, 5] = true := by decide +kernel
theorem subd4_7_154 : subd4_7 [0, 1, 6] = true := by decide +kernel
theorem subd4_7_155 : subd4_7 [0, 1, 7] = true := by decide +kernel
theorem subd4_7_156 : subd4_7 [0, 1, 8] = true := by decide +kernel
theorem subd4_7_157 : subd4_7 [0, 2, -7] = true := by decide +kernel
theorem subd4_7_158 : subd4_7 [0, 2, -6] = true := by decide +kernel
theorem subd4_7_159 : subd4_7 [0, 2, -5] = true := by decide +kernel
theorem sbd4_7_4 : ∀ q ∈ blkd4_7_4, subd4_7 q = true := by
  unfold blkd4_7_4
  exact List.forall_mem_cons.2 ⟨subd4_7_128, List.forall_mem_cons.2 ⟨subd4_7_129, List.forall_mem_cons.2 ⟨subd4_7_130, List.forall_mem_cons.2 ⟨subd4_7_131, List.forall_mem_cons.2 ⟨subd4_7_132, List.forall_mem_cons.2 ⟨subd4_7_133, List.forall_mem_cons.2 ⟨subd4_7_134, List.forall_mem_cons.2 ⟨subd4_7_135, List.forall_mem_cons.2 ⟨subd4_7_136, List.forall_mem_cons.2 ⟨subd4_7_137, List.forall_mem_cons.2 ⟨subd4_7_138, List.forall_mem_cons.2 ⟨subd4_7_139, List.forall_mem_cons.2 ⟨subd4_7_140, List.forall_mem_cons.2 ⟨subd4_7_141, List.forall_mem_cons.2 ⟨subd4_7_142, List.forall_mem_cons.2 ⟨subd4_7_143, List.forall_mem_cons.2 ⟨subd4_7_144, List.forall_mem_cons.2 ⟨subd4_7_145, List.forall_mem_cons.2 ⟨subd4_7_146, List.forall_mem_cons.2 ⟨subd4_7_147, List.forall_mem_cons.2 ⟨subd4_7_148, List.forall_mem_cons.2 ⟨subd4_7_149, List.forall_mem_cons.2 ⟨subd4_7_150, List.forall_mem_cons.2 ⟨subd4_7_151, List.forall_mem_cons.2 ⟨subd4_7_152, List.forall_mem_cons.2 ⟨subd4_7_153, List.forall_mem_cons.2 ⟨subd4_7_154, List.forall_mem_cons.2 ⟨subd4_7_155, List.forall_mem_cons.2 ⟨subd4_7_156, List.forall_mem_cons.2 ⟨subd4_7_157, List.forall_mem_cons.2 ⟨subd4_7_158, List.forall_mem_cons.2 ⟨subd4_7_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
