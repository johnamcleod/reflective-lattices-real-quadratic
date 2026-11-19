import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_4_224 : subd8_4 [1, 2, -1] = true := by decide +kernel
theorem subd8_4_225 : subd8_4 [1, 2, 0] = true := by decide +kernel
theorem subd8_4_226 : subd8_4 [1, 2, 1] = true := by decide +kernel
theorem subd8_4_227 : subd8_4 [1, 2, 2] = true := by decide +kernel
theorem subd8_4_228 : subd8_4 [1, 2, 3] = true := by decide +kernel
theorem subd8_4_229 : subd8_4 [1, 2, 4] = true := by decide +kernel
theorem subd8_4_230 : subd8_4 [1, 2, 5] = true := by decide +kernel
theorem subd8_4_231 : subd8_4 [1, 2, 6] = true := by decide +kernel
theorem subd8_4_232 : subd8_4 [1, 3] = true := by decide +kernel
theorem subd8_4_233 : subd8_4 [1, 4] = true := by decide +kernel
theorem subd8_4_234 : subd8_4 [1, 5] = true := by decide +kernel
theorem subd8_4_235 : subd8_4 [1, 6] = true := by decide +kernel
theorem subd8_4_236 : subd8_4 [2, -6] = true := by decide +kernel
theorem subd8_4_237 : subd8_4 [2, -5] = true := by decide +kernel
theorem subd8_4_238 : subd8_4 [2, -4] = true := by decide +kernel
theorem subd8_4_239 : subd8_4 [2, -3] = true := by decide +kernel
theorem subd8_4_240 : subd8_4 [2, -2] = true := by decide +kernel
theorem subd8_4_241 : subd8_4 [2, -1] = true := by decide +kernel
theorem subd8_4_242 : subd8_4 [2, 0] = true := by decide +kernel
theorem subd8_4_243 : subd8_4 [2, 1, -6] = true := by decide +kernel
theorem subd8_4_244 : subd8_4 [2, 1, -5] = true := by decide +kernel
theorem subd8_4_245 : subd8_4 [2, 1, -4] = true := by decide +kernel
theorem subd8_4_246 : subd8_4 [2, 1, -3] = true := by decide +kernel
theorem subd8_4_247 : subd8_4 [2, 1, -2] = true := by decide +kernel
theorem subd8_4_248 : subd8_4 [2, 1, -1] = true := by decide +kernel
theorem subd8_4_249 : subd8_4 [2, 1, 0] = true := by decide +kernel
theorem subd8_4_250 : subd8_4 [2, 1, 1] = true := by decide +kernel
theorem subd8_4_251 : subd8_4 [2, 1, 2] = true := by decide +kernel
theorem subd8_4_252 : subd8_4 [2, 1, 3] = true := by decide +kernel
theorem subd8_4_253 : subd8_4 [2, 1, 4] = true := by decide +kernel
theorem subd8_4_254 : subd8_4 [2, 1, 5] = true := by decide +kernel
theorem subd8_4_255 : subd8_4 [2, 1, 6] = true := by decide +kernel
theorem sbd8_4_7 : ∀ q ∈ blkd8_4_7, subd8_4 q = true := by
  unfold blkd8_4_7
  exact List.forall_mem_cons.2 ⟨subd8_4_224, List.forall_mem_cons.2 ⟨subd8_4_225, List.forall_mem_cons.2 ⟨subd8_4_226, List.forall_mem_cons.2 ⟨subd8_4_227, List.forall_mem_cons.2 ⟨subd8_4_228, List.forall_mem_cons.2 ⟨subd8_4_229, List.forall_mem_cons.2 ⟨subd8_4_230, List.forall_mem_cons.2 ⟨subd8_4_231, List.forall_mem_cons.2 ⟨subd8_4_232, List.forall_mem_cons.2 ⟨subd8_4_233, List.forall_mem_cons.2 ⟨subd8_4_234, List.forall_mem_cons.2 ⟨subd8_4_235, List.forall_mem_cons.2 ⟨subd8_4_236, List.forall_mem_cons.2 ⟨subd8_4_237, List.forall_mem_cons.2 ⟨subd8_4_238, List.forall_mem_cons.2 ⟨subd8_4_239, List.forall_mem_cons.2 ⟨subd8_4_240, List.forall_mem_cons.2 ⟨subd8_4_241, List.forall_mem_cons.2 ⟨subd8_4_242, List.forall_mem_cons.2 ⟨subd8_4_243, List.forall_mem_cons.2 ⟨subd8_4_244, List.forall_mem_cons.2 ⟨subd8_4_245, List.forall_mem_cons.2 ⟨subd8_4_246, List.forall_mem_cons.2 ⟨subd8_4_247, List.forall_mem_cons.2 ⟨subd8_4_248, List.forall_mem_cons.2 ⟨subd8_4_249, List.forall_mem_cons.2 ⟨subd8_4_250, List.forall_mem_cons.2 ⟨subd8_4_251, List.forall_mem_cons.2 ⟨subd8_4_252, List.forall_mem_cons.2 ⟨subd8_4_253, List.forall_mem_cons.2 ⟨subd8_4_254, List.forall_mem_cons.2 ⟨subd8_4_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_256 : subd8_4 [2, 2] = true := by decide +kernel
theorem subd8_4_257 : subd8_4 [2, 3] = true := by decide +kernel
theorem subd8_4_258 : subd8_4 [2, 4] = true := by decide +kernel
theorem subd8_4_259 : subd8_4 [2, 5] = true := by decide +kernel
theorem subd8_4_260 : subd8_4 [2, 6] = true := by decide +kernel
theorem subd8_4_261 : subd8_4 [2, 7] = true := by decide +kernel
theorem subd8_4_262 : subd8_4 [3, -5] = true := by decide +kernel
theorem subd8_4_263 : subd8_4 [3, -4] = true := by decide +kernel
theorem subd8_4_264 : subd8_4 [3, -3] = true := by decide +kernel
theorem subd8_4_265 : subd8_4 [3, -2] = true := by decide +kernel
theorem subd8_4_266 : subd8_4 [3, -1] = true := by decide +kernel
theorem subd8_4_267 : subd8_4 [3, 0] = true := by decide +kernel
theorem subd8_4_268 : subd8_4 [3, 1] = true := by decide +kernel
theorem subd8_4_269 : subd8_4 [3, 2] = true := by decide +kernel
theorem subd8_4_270 : subd8_4 [3, 3] = true := by decide +kernel
theorem subd8_4_271 : subd8_4 [3, 4] = true := by decide +kernel
theorem subd8_4_272 : subd8_4 [3, 5] = true := by decide +kernel
theorem subd8_4_273 : subd8_4 [3, 6] = true := by decide +kernel
theorem subd8_4_274 : subd8_4 [4, -4] = true := by decide +kernel
theorem subd8_4_275 : subd8_4 [4, -3] = true := by decide +kernel
theorem subd8_4_276 : subd8_4 [4, -2] = true := by decide +kernel
theorem subd8_4_277 : subd8_4 [4, -1] = true := by decide +kernel
theorem subd8_4_278 : subd8_4 [4, 0] = true := by decide +kernel
theorem subd8_4_279 : subd8_4 [4, 1] = true := by decide +kernel
theorem subd8_4_280 : subd8_4 [4, 2] = true := by decide +kernel
theorem subd8_4_281 : subd8_4 [4, 3] = true := by decide +kernel
theorem subd8_4_282 : subd8_4 [4, 4] = true := by decide +kernel
theorem subd8_4_283 : subd8_4 [4, 5] = true := by decide +kernel
theorem subd8_4_284 : subd8_4 [4, 6] = true := by decide +kernel
theorem subd8_4_285 : subd8_4 [5, -2] = true := by decide +kernel
theorem subd8_4_286 : subd8_4 [5, -1] = true := by decide +kernel
theorem subd8_4_287 : subd8_4 [5, 0] = true := by decide +kernel
theorem sbd8_4_8 : ∀ q ∈ blkd8_4_8, subd8_4 q = true := by
  unfold blkd8_4_8
  exact List.forall_mem_cons.2 ⟨subd8_4_256, List.forall_mem_cons.2 ⟨subd8_4_257, List.forall_mem_cons.2 ⟨subd8_4_258, List.forall_mem_cons.2 ⟨subd8_4_259, List.forall_mem_cons.2 ⟨subd8_4_260, List.forall_mem_cons.2 ⟨subd8_4_261, List.forall_mem_cons.2 ⟨subd8_4_262, List.forall_mem_cons.2 ⟨subd8_4_263, List.forall_mem_cons.2 ⟨subd8_4_264, List.forall_mem_cons.2 ⟨subd8_4_265, List.forall_mem_cons.2 ⟨subd8_4_266, List.forall_mem_cons.2 ⟨subd8_4_267, List.forall_mem_cons.2 ⟨subd8_4_268, List.forall_mem_cons.2 ⟨subd8_4_269, List.forall_mem_cons.2 ⟨subd8_4_270, List.forall_mem_cons.2 ⟨subd8_4_271, List.forall_mem_cons.2 ⟨subd8_4_272, List.forall_mem_cons.2 ⟨subd8_4_273, List.forall_mem_cons.2 ⟨subd8_4_274, List.forall_mem_cons.2 ⟨subd8_4_275, List.forall_mem_cons.2 ⟨subd8_4_276, List.forall_mem_cons.2 ⟨subd8_4_277, List.forall_mem_cons.2 ⟨subd8_4_278, List.forall_mem_cons.2 ⟨subd8_4_279, List.forall_mem_cons.2 ⟨subd8_4_280, List.forall_mem_cons.2 ⟨subd8_4_281, List.forall_mem_cons.2 ⟨subd8_4_282, List.forall_mem_cons.2 ⟨subd8_4_283, List.forall_mem_cons.2 ⟨subd8_4_284, List.forall_mem_cons.2 ⟨subd8_4_285, List.forall_mem_cons.2 ⟨subd8_4_286, List.forall_mem_cons.2 ⟨subd8_4_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_288 : subd8_4 [5, 1] = true := by decide +kernel
theorem subd8_4_289 : subd8_4 [5, 2] = true := by decide +kernel
theorem subd8_4_290 : subd8_4 [5, 3] = true := by decide +kernel
theorem subd8_4_291 : subd8_4 [5, 4] = true := by decide +kernel
theorem subd8_4_292 : subd8_4 [5, 5] = true := by decide +kernel
theorem sbd8_4_9 : ∀ q ∈ blkd8_4_9, subd8_4 q = true := by
  unfold blkd8_4_9
  exact List.forall_mem_cons.2 ⟨subd8_4_288, List.forall_mem_cons.2 ⟨subd8_4_289, List.forall_mem_cons.2 ⟨subd8_4_290, List.forall_mem_cons.2 ⟨subd8_4_291, List.forall_mem_cons.2 ⟨subd8_4_292, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_5 : ldCheck G d8_5.U d8_5.ms ldd8_5 = true := by decide +kernel
theorem pre_okd8_5 : subPre G cell8 d8_5 = true := by decide +kernel
theorem subd8_5_0 : subd8_5 [-1, -2] = true := by decide +kernel
theorem subd8_5_1 : subd8_5 [-1, -1, -8] = true := by decide +kernel
theorem subd8_5_2 : subd8_5 [-1, -1, -7] = true := by decide +kernel
theorem subd8_5_3 : subd8_5 [-1, -1, -6] = true := by decide +kernel
theorem subd8_5_4 : subd8_5 [-1, -1, -5] = true := by decide +kernel
theorem subd8_5_5 : subd8_5 [-1, -1, -4] = true := by decide +kernel
theorem subd8_5_6 : subd8_5 [-1, -1, -3] = true := by decide +kernel
theorem subd8_5_7 : subd8_5 [-1, -1, -2] = true := by decide +kernel
theorem subd8_5_8 : subd8_5 [-1, -1, -1] = true := by decide +kernel
theorem subd8_5_9 : subd8_5 [-1, -1, 0] = true := by decide +kernel
theorem subd8_5_10 : subd8_5 [-1, -1, 1] = true := by decide +kernel
theorem subd8_5_11 : subd8_5 [-1, -1, 2] = true := by decide +kernel
theorem subd8_5_12 : subd8_5 [-1, -1, 3] = true := by decide +kernel
theorem subd8_5_13 : subd8_5 [-1, -1, 4] = true := by decide +kernel
theorem subd8_5_14 : subd8_5 [-1, -1, 5] = true := by decide +kernel
theorem subd8_5_15 : subd8_5 [-1, -1, 6] = true := by decide +kernel
theorem subd8_5_16 : subd8_5 [-1, -1, 7] = true := by decide +kernel
theorem subd8_5_17 : subd8_5 [-1, -1, 8] = true := by decide +kernel
theorem subd8_5_18 : subd8_5 [-1, 0, -15] = true := by decide +kernel
theorem subd8_5_19 : subd8_5 [-1, 0, -14] = true := by decide +kernel
theorem subd8_5_20 : subd8_5 [-1, 0, -13] = true := by decide +kernel
theorem subd8_5_21 : subd8_5 [-1, 0, -12] = true := by decide +kernel
theorem subd8_5_22 : subd8_5 [-1, 0, -11] = true := by decide +kernel
theorem subd8_5_23 : subd8_5 [-1, 0, -10] = true := by decide +kernel
theorem subd8_5_24 : subd8_5 [-1, 0, -9] = true := by decide +kernel
theorem subd8_5_25 : subd8_5 [-1, 0, -8] = true := by decide +kernel
theorem subd8_5_26 : subd8_5 [-1, 0, -7] = true := by decide +kernel
theorem subd8_5_27 : subd8_5 [-1, 0, -6] = true := by decide +kernel
theorem subd8_5_28 : subd8_5 [-1, 0, -5] = true := by decide +kernel
theorem subd8_5_29 : subd8_5 [-1, 0, -4] = true := by decide +kernel
theorem subd8_5_30 : subd8_5 [-1, 0, -3] = true := by decide +kernel
theorem subd8_5_31 : subd8_5 [-1, 0, -2] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_cons.2 ⟨subd8_5_1, List.forall_mem_cons.2 ⟨subd8_5_2, List.forall_mem_cons.2 ⟨subd8_5_3, List.forall_mem_cons.2 ⟨subd8_5_4, List.forall_mem_cons.2 ⟨subd8_5_5, List.forall_mem_cons.2 ⟨subd8_5_6, List.forall_mem_cons.2 ⟨subd8_5_7, List.forall_mem_cons.2 ⟨subd8_5_8, List.forall_mem_cons.2 ⟨subd8_5_9, List.forall_mem_cons.2 ⟨subd8_5_10, List.forall_mem_cons.2 ⟨subd8_5_11, List.forall_mem_cons.2 ⟨subd8_5_12, List.forall_mem_cons.2 ⟨subd8_5_13, List.forall_mem_cons.2 ⟨subd8_5_14, List.forall_mem_cons.2 ⟨subd8_5_15, List.forall_mem_cons.2 ⟨subd8_5_16, List.forall_mem_cons.2 ⟨subd8_5_17, List.forall_mem_cons.2 ⟨subd8_5_18, List.forall_mem_cons.2 ⟨subd8_5_19, List.forall_mem_cons.2 ⟨subd8_5_20, List.forall_mem_cons.2 ⟨subd8_5_21, List.forall_mem_cons.2 ⟨subd8_5_22, List.forall_mem_cons.2 ⟨subd8_5_23, List.forall_mem_cons.2 ⟨subd8_5_24, List.forall_mem_cons.2 ⟨subd8_5_25, List.forall_mem_cons.2 ⟨subd8_5_26, List.forall_mem_cons.2 ⟨subd8_5_27, List.forall_mem_cons.2 ⟨subd8_5_28, List.forall_mem_cons.2 ⟨subd8_5_29, List.forall_mem_cons.2 ⟨subd8_5_30, List.forall_mem_cons.2 ⟨subd8_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_32 : subd8_5 [-1, 0, -1] = true := by decide +kernel
theorem subd8_5_33 : subd8_5 [-1, 0, 0] = true := by decide +kernel
theorem subd8_5_34 : subd8_5 [-1, 0, 1] = true := by decide +kernel
theorem subd8_5_35 : subd8_5 [-1, 0, 2] = true := by decide +kernel
theorem subd8_5_36 : subd8_5 [-1, 0, 3] = true := by decide +kernel
theorem subd8_5_37 : subd8_5 [-1, 0, 4] = true := by decide +kernel
theorem subd8_5_38 : subd8_5 [-1, 0, 5] = true := by decide +kernel
theorem subd8_5_39 : subd8_5 [-1, 0, 6] = true := by decide +kernel
theorem subd8_5_40 : subd8_5 [-1, 0, 7] = true := by decide +kernel
theorem subd8_5_41 : subd8_5 [-1, 0, 8] = true := by decide +kernel
theorem subd8_5_42 : subd8_5 [-1, 0, 9] = true := by decide +kernel
theorem subd8_5_43 : subd8_5 [-1, 0, 10] = true := by decide +kernel
theorem subd8_5_44 : subd8_5 [-1, 0, 11] = true := by decide +kernel
theorem subd8_5_45 : subd8_5 [-1, 0, 12] = true := by decide +kernel
theorem subd8_5_46 : subd8_5 [-1, 0, 13] = true := by decide +kernel
theorem subd8_5_47 : subd8_5 [-1, 0, 14] = true := by decide +kernel
theorem subd8_5_48 : subd8_5 [-1, 1, -14] = true := by decide +kernel
theorem subd8_5_49 : subd8_5 [-1, 1, -13] = true := by decide +kernel
theorem subd8_5_50 : subd8_5 [-1, 1, -12] = true := by decide +kernel
theorem subd8_5_51 : subd8_5 [-1, 1, -11] = true := by decide +kernel
theorem subd8_5_52 : subd8_5 [-1, 1, -10] = true := by decide +kernel
theorem subd8_5_53 : subd8_5 [-1, 1, -9] = true := by decide +kernel
theorem subd8_5_54 : subd8_5 [-1, 1, -8] = true := by decide +kernel
theorem subd8_5_55 : subd8_5 [-1, 1, -7] = true := by decide +kernel
theorem subd8_5_56 : subd8_5 [-1, 1, -6] = true := by decide +kernel
theorem subd8_5_57 : subd8_5 [-1, 1, -5] = true := by decide +kernel
theorem subd8_5_58 : subd8_5 [-1, 1, -4] = true := by decide +kernel
theorem subd8_5_59 : subd8_5 [-1, 1, -3] = true := by decide +kernel
theorem subd8_5_60 : subd8_5 [-1, 1, -2] = true := by decide +kernel
theorem subd8_5_61 : subd8_5 [-1, 1, -1] = true := by decide +kernel
theorem subd8_5_62 : subd8_5 [-1, 1, 0] = true := by decide +kernel
theorem subd8_5_63 : subd8_5 [-1, 1, 1] = true := by decide +kernel
theorem sbd8_5_1 : ∀ q ∈ blkd8_5_1, subd8_5 q = true := by
  unfold blkd8_5_1
  exact List.forall_mem_cons.2 ⟨subd8_5_32, List.forall_mem_cons.2 ⟨subd8_5_33, List.forall_mem_cons.2 ⟨subd8_5_34, List.forall_mem_cons.2 ⟨subd8_5_35, List.forall_mem_cons.2 ⟨subd8_5_36, List.forall_mem_cons.2 ⟨subd8_5_37, List.forall_mem_cons.2 ⟨subd8_5_38, List.forall_mem_cons.2 ⟨subd8_5_39, List.forall_mem_cons.2 ⟨subd8_5_40, List.forall_mem_cons.2 ⟨subd8_5_41, List.forall_mem_cons.2 ⟨subd8_5_42, List.forall_mem_cons.2 ⟨subd8_5_43, List.forall_mem_cons.2 ⟨subd8_5_44, List.forall_mem_cons.2 ⟨subd8_5_45, List.forall_mem_cons.2 ⟨subd8_5_46, List.forall_mem_cons.2 ⟨subd8_5_47, List.forall_mem_cons.2 ⟨subd8_5_48, List.forall_mem_cons.2 ⟨subd8_5_49, List.forall_mem_cons.2 ⟨subd8_5_50, List.forall_mem_cons.2 ⟨subd8_5_51, List.forall_mem_cons.2 ⟨subd8_5_52, List.forall_mem_cons.2 ⟨subd8_5_53, List.forall_mem_cons.2 ⟨subd8_5_54, List.forall_mem_cons.2 ⟨subd8_5_55, List.forall_mem_cons.2 ⟨subd8_5_56, List.forall_mem_cons.2 ⟨subd8_5_57, List.forall_mem_cons.2 ⟨subd8_5_58, List.forall_mem_cons.2 ⟨subd8_5_59, List.forall_mem_cons.2 ⟨subd8_5_60, List.forall_mem_cons.2 ⟨subd8_5_61, List.forall_mem_cons.2 ⟨subd8_5_62, List.forall_mem_cons.2 ⟨subd8_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_64 : subd8_5 [-1, 1, 2] = true := by decide +kernel
theorem subd8_5_65 : subd8_5 [-1, 1, 3] = true := by decide +kernel
theorem subd8_5_66 : subd8_5 [-1, 1, 4] = true := by decide +kernel
theorem subd8_5_67 : subd8_5 [-1, 1, 5] = true := by decide +kernel
theorem subd8_5_68 : subd8_5 [-1, 1, 6] = true := by decide +kernel
theorem subd8_5_69 : subd8_5 [-1, 1, 7] = true := by decide +kernel
theorem subd8_5_70 : subd8_5 [-1, 1, 8] = true := by decide +kernel
theorem subd8_5_71 : subd8_5 [-1, 1, 9] = true := by decide +kernel
theorem subd8_5_72 : subd8_5 [-1, 1, 10] = true := by decide +kernel
theorem subd8_5_73 : subd8_5 [-1, 1, 11] = true := by decide +kernel
theorem subd8_5_74 : subd8_5 [-1, 1, 12] = true := by decide +kernel
theorem subd8_5_75 : subd8_5 [-1, 1, 13] = true := by decide +kernel
theorem subd8_5_76 : subd8_5 [0, -2] = true := by decide +kernel
theorem subd8_5_77 : subd8_5 [0, -1, -16] = true := by decide +kernel
theorem subd8_5_78 : subd8_5 [0, -1, -15] = true := by decide +kernel
theorem subd8_5_79 : subd8_5 [0, -1, -14] = true := by decide +kernel
theorem subd8_5_80 : subd8_5 [0, -1, -13] = true := by decide +kernel
theorem subd8_5_81 : subd8_5 [0, -1, -12] = true := by decide +kernel
theorem subd8_5_82 : subd8_5 [0, -1, -11] = true := by decide +kernel
theorem subd8_5_83 : subd8_5 [0, -1, -10] = true := by decide +kernel
theorem subd8_5_84 : subd8_5 [0, -1, -9] = true := by decide +kernel
theorem subd8_5_85 : subd8_5 [0, -1, -8] = true := by decide +kernel
theorem subd8_5_86 : subd8_5 [0, -1, -7] = true := by decide +kernel
theorem subd8_5_87 : subd8_5 [0, -1, -6] = true := by decide +kernel
theorem subd8_5_88 : subd8_5 [0, -1, -5] = true := by decide +kernel
theorem subd8_5_89 : subd8_5 [0, -1, -4] = true := by decide +kernel
theorem subd8_5_90 : subd8_5 [0, -1, -3] = true := by decide +kernel
theorem subd8_5_91 : subd8_5 [0, -1, -2] = true := by decide +kernel
theorem subd8_5_92 : subd8_5 [0, -1, -1] = true := by decide +kernel
theorem subd8_5_93 : subd8_5 [0, -1, 0] = true := by decide +kernel
theorem subd8_5_94 : subd8_5 [0, -1, 1] = true := by decide +kernel
theorem subd8_5_95 : subd8_5 [0, -1, 2] = true := by decide +kernel
theorem sbd8_5_2 : ∀ q ∈ blkd8_5_2, subd8_5 q = true := by
  unfold blkd8_5_2
  exact List.forall_mem_cons.2 ⟨subd8_5_64, List.forall_mem_cons.2 ⟨subd8_5_65, List.forall_mem_cons.2 ⟨subd8_5_66, List.forall_mem_cons.2 ⟨subd8_5_67, List.forall_mem_cons.2 ⟨subd8_5_68, List.forall_mem_cons.2 ⟨subd8_5_69, List.forall_mem_cons.2 ⟨subd8_5_70, List.forall_mem_cons.2 ⟨subd8_5_71, List.forall_mem_cons.2 ⟨subd8_5_72, List.forall_mem_cons.2 ⟨subd8_5_73, List.forall_mem_cons.2 ⟨subd8_5_74, List.forall_mem_cons.2 ⟨subd8_5_75, List.forall_mem_cons.2 ⟨subd8_5_76, List.forall_mem_cons.2 ⟨subd8_5_77, List.forall_mem_cons.2 ⟨subd8_5_78, List.forall_mem_cons.2 ⟨subd8_5_79, List.forall_mem_cons.2 ⟨subd8_5_80, List.forall_mem_cons.2 ⟨subd8_5_81, List.forall_mem_cons.2 ⟨subd8_5_82, List.forall_mem_cons.2 ⟨subd8_5_83, List.forall_mem_cons.2 ⟨subd8_5_84, List.forall_mem_cons.2 ⟨subd8_5_85, List.forall_mem_cons.2 ⟨subd8_5_86, List.forall_mem_cons.2 ⟨subd8_5_87, List.forall_mem_cons.2 ⟨subd8_5_88, List.forall_mem_cons.2 ⟨subd8_5_89, List.forall_mem_cons.2 ⟨subd8_5_90, List.forall_mem_cons.2 ⟨subd8_5_91, List.forall_mem_cons.2 ⟨subd8_5_92, List.forall_mem_cons.2 ⟨subd8_5_93, List.forall_mem_cons.2 ⟨subd8_5_94, List.forall_mem_cons.2 ⟨subd8_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_96 : subd8_5 [0, -1, 3] = true := by decide +kernel
theorem subd8_5_97 : subd8_5 [0, -1, 4] = true := by decide +kernel
theorem subd8_5_98 : subd8_5 [0, -1, 5] = true := by decide +kernel
theorem subd8_5_99 : subd8_5 [0, -1, 6] = true := by decide +kernel
theorem subd8_5_100 : subd8_5 [0, -1, 7] = true := by decide +kernel
theorem subd8_5_101 : subd8_5 [0, -1, 8] = true := by decide +kernel
theorem subd8_5_102 : subd8_5 [0, -1, 9] = true := by decide +kernel
theorem subd8_5_103 : subd8_5 [0, -1, 10] = true := by decide +kernel
theorem subd8_5_104 : subd8_5 [0, -1, 11] = true := by decide +kernel
theorem subd8_5_105 : subd8_5 [0, -1, 12] = true := by decide +kernel
theorem subd8_5_106 : subd8_5 [0, -1, 13] = true := by decide +kernel
theorem subd8_5_107 : subd8_5 [0, -1, 14] = true := by decide +kernel
theorem subd8_5_108 : subd8_5 [0, -1, 15] = true := by decide +kernel
theorem subd8_5_109 : subd8_5 [0, 0, -18] = true := by decide +kernel
theorem subd8_5_110 : subd8_5 [0, 0, -17] = true := by decide +kernel
theorem subd8_5_111 : subd8_5 [0, 0, -16] = true := by decide +kernel
theorem subd8_5_112 : subd8_5 [0, 0, -15] = true := by decide +kernel
theorem subd8_5_113 : subd8_5 [0, 0, -14] = true := by decide +kernel
theorem subd8_5_114 : subd8_5 [0, 0, -13] = true := by decide +kernel
theorem subd8_5_115 : subd8_5 [0, 0, -12] = true := by decide +kernel
theorem subd8_5_116 : subd8_5 [0, 0, -11] = true := by decide +kernel
theorem subd8_5_117 : subd8_5 [0, 0, -10] = true := by decide +kernel
theorem subd8_5_118 : subd8_5 [0, 0, -9] = true := by decide +kernel
theorem subd8_5_119 : subd8_5 [0, 0, -8] = true := by decide +kernel
theorem subd8_5_120 : subd8_5 [0, 0, -7] = true := by decide +kernel
theorem subd8_5_121 : subd8_5 [0, 0, -6] = true := by decide +kernel
theorem subd8_5_122 : subd8_5 [0, 0, -5] = true := by decide +kernel
theorem subd8_5_123 : subd8_5 [0, 0, -4] = true := by decide +kernel
theorem subd8_5_124 : subd8_5 [0, 0, -3] = true := by decide +kernel
theorem subd8_5_125 : subd8_5 [0, 0, -2] = true := by decide +kernel
theorem subd8_5_126 : subd8_5 [0, 0, -1] = true := by decide +kernel
theorem subd8_5_127 : subd8_5 [0, 0, 0] = true := by decide +kernel
theorem sbd8_5_3 : ∀ q ∈ blkd8_5_3, subd8_5 q = true := by
  unfold blkd8_5_3
  exact List.forall_mem_cons.2 ⟨subd8_5_96, List.forall_mem_cons.2 ⟨subd8_5_97, List.forall_mem_cons.2 ⟨subd8_5_98, List.forall_mem_cons.2 ⟨subd8_5_99, List.forall_mem_cons.2 ⟨subd8_5_100, List.forall_mem_cons.2 ⟨subd8_5_101, List.forall_mem_cons.2 ⟨subd8_5_102, List.forall_mem_cons.2 ⟨subd8_5_103, List.forall_mem_cons.2 ⟨subd8_5_104, List.forall_mem_cons.2 ⟨subd8_5_105, List.forall_mem_cons.2 ⟨subd8_5_106, List.forall_mem_cons.2 ⟨subd8_5_107, List.forall_mem_cons.2 ⟨subd8_5_108, List.forall_mem_cons.2 ⟨subd8_5_109, List.forall_mem_cons.2 ⟨subd8_5_110, List.forall_mem_cons.2 ⟨subd8_5_111, List.forall_mem_cons.2 ⟨subd8_5_112, List.forall_mem_cons.2 ⟨subd8_5_113, List.forall_mem_cons.2 ⟨subd8_5_114, List.forall_mem_cons.2 ⟨subd8_5_115, List.forall_mem_cons.2 ⟨subd8_5_116, List.forall_mem_cons.2 ⟨subd8_5_117, List.forall_mem_cons.2 ⟨subd8_5_118, List.forall_mem_cons.2 ⟨subd8_5_119, List.forall_mem_cons.2 ⟨subd8_5_120, List.forall_mem_cons.2 ⟨subd8_5_121, List.forall_mem_cons.2 ⟨subd8_5_122, List.forall_mem_cons.2 ⟨subd8_5_123, List.forall_mem_cons.2 ⟨subd8_5_124, List.forall_mem_cons.2 ⟨subd8_5_125, List.forall_mem_cons.2 ⟨subd8_5_126, List.forall_mem_cons.2 ⟨subd8_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
