import ReflectZphi.Data.Cert5.C076.Base

namespace ReflectZphi.Data.Cert5.C076
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_256 : sub7 [1, 2, -5] = true := by decide +kernel
theorem sub7_257 : sub7 [1, 2, -4] = true := by decide +kernel
theorem sub7_258 : sub7 [1, 2, -3] = true := by decide +kernel
theorem sub7_259 : sub7 [1, 2, -2] = true := by decide +kernel
theorem sub7_260 : sub7 [1, 2, -1] = true := by decide +kernel
theorem sub7_261 : sub7 [1, 2, 0] = true := by decide +kernel
theorem sub7_262 : sub7 [1, 2, 1] = true := by decide +kernel
theorem sub7_263 : sub7 [1, 2, 2] = true := by decide +kernel
theorem sub7_264 : sub7 [1, 2, 3] = true := by decide +kernel
theorem sub7_265 : sub7 [1, 2, 4] = true := by decide +kernel
theorem sub7_266 : sub7 [1, 2, 5] = true := by decide +kernel
theorem sub7_267 : sub7 [1, 2, 6] = true := by decide +kernel
theorem sub7_268 : sub7 [1, 2, 7] = true := by decide +kernel
theorem sub7_269 : sub7 [1, 3] = true := by decide +kernel
theorem sub7_270 : sub7 [1, 4] = true := by decide +kernel
theorem sub7_271 : sub7 [1, 5] = true := by decide +kernel
theorem sub7_272 : sub7 [2, -4] = true := by decide +kernel
theorem sub7_273 : sub7 [2, -3] = true := by decide +kernel
theorem sub7_274 : sub7 [2, -2] = true := by decide +kernel
theorem sub7_275 : sub7 [2, -1] = true := by decide +kernel
theorem sub7_276 : sub7 [2, 0, -6] = true := by decide +kernel
theorem sub7_277 : sub7 [2, 0, -5] = true := by decide +kernel
theorem sub7_278 : sub7 [2, 0, -4] = true := by decide +kernel
theorem sub7_279 : sub7 [2, 0, -3] = true := by decide +kernel
theorem sub7_280 : sub7 [2, 0, -2] = true := by decide +kernel
theorem sub7_281 : sub7 [2, 0, -1] = true := by decide +kernel
theorem sub7_282 : sub7 [2, 0, 0] = true := by decide +kernel
theorem sub7_283 : sub7 [2, 0, 1] = true := by decide +kernel
theorem sub7_284 : sub7 [2, 0, 2] = true := by decide +kernel
theorem sub7_285 : sub7 [2, 0, 3] = true := by decide +kernel
theorem sub7_286 : sub7 [2, 0, 4] = true := by decide +kernel
theorem sub7_287 : sub7 [2, 0, 5] = true := by decide +kernel
theorem sb7_8 : ∀ q ∈ blk7_8, sub7 q = true := by
  unfold blk7_8
  exact List.forall_mem_cons.2 ⟨sub7_256, List.forall_mem_cons.2 ⟨sub7_257, List.forall_mem_cons.2 ⟨sub7_258, List.forall_mem_cons.2 ⟨sub7_259, List.forall_mem_cons.2 ⟨sub7_260, List.forall_mem_cons.2 ⟨sub7_261, List.forall_mem_cons.2 ⟨sub7_262, List.forall_mem_cons.2 ⟨sub7_263, List.forall_mem_cons.2 ⟨sub7_264, List.forall_mem_cons.2 ⟨sub7_265, List.forall_mem_cons.2 ⟨sub7_266, List.forall_mem_cons.2 ⟨sub7_267, List.forall_mem_cons.2 ⟨sub7_268, List.forall_mem_cons.2 ⟨sub7_269, List.forall_mem_cons.2 ⟨sub7_270, List.forall_mem_cons.2 ⟨sub7_271, List.forall_mem_cons.2 ⟨sub7_272, List.forall_mem_cons.2 ⟨sub7_273, List.forall_mem_cons.2 ⟨sub7_274, List.forall_mem_cons.2 ⟨sub7_275, List.forall_mem_cons.2 ⟨sub7_276, List.forall_mem_cons.2 ⟨sub7_277, List.forall_mem_cons.2 ⟨sub7_278, List.forall_mem_cons.2 ⟨sub7_279, List.forall_mem_cons.2 ⟨sub7_280, List.forall_mem_cons.2 ⟨sub7_281, List.forall_mem_cons.2 ⟨sub7_282, List.forall_mem_cons.2 ⟨sub7_283, List.forall_mem_cons.2 ⟨sub7_284, List.forall_mem_cons.2 ⟨sub7_285, List.forall_mem_cons.2 ⟨sub7_286, List.forall_mem_cons.2 ⟨sub7_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_288 : sub7 [2, 0, 6] = true := by decide +kernel
theorem sub7_289 : sub7 [2, 0, 7] = true := by decide +kernel
theorem sub7_290 : sub7 [2, 1, -6] = true := by decide +kernel
theorem sub7_291 : sub7 [2, 1, -5] = true := by decide +kernel
theorem sub7_292 : sub7 [2, 1, -4] = true := by decide +kernel
theorem sub7_293 : sub7 [2, 1, -3] = true := by decide +kernel
theorem sub7_294 : sub7 [2, 1, -2] = true := by decide +kernel
theorem sub7_295 : sub7 [2, 1, -1] = true := by decide +kernel
theorem sub7_296 : sub7 [2, 1, 0] = true := by decide +kernel
theorem sub7_297 : sub7 [2, 1, 1] = true := by decide +kernel
theorem sub7_298 : sub7 [2, 1, 2] = true := by decide +kernel
theorem sub7_299 : sub7 [2, 1, 3] = true := by decide +kernel
theorem sub7_300 : sub7 [2, 1, 4] = true := by decide +kernel
theorem sub7_301 : sub7 [2, 1, 5] = true := by decide +kernel
theorem sub7_302 : sub7 [2, 1, 6] = true := by decide +kernel
theorem sub7_303 : sub7 [2, 1, 7] = true := by decide +kernel
theorem sub7_304 : sub7 [2, 2, -6] = true := by decide +kernel
theorem sub7_305 : sub7 [2, 2, -5] = true := by decide +kernel
theorem sub7_306 : sub7 [2, 2, -4] = true := by decide +kernel
theorem sub7_307 : sub7 [2, 2, -3] = true := by decide +kernel
theorem sub7_308 : sub7 [2, 2, -2] = true := by decide +kernel
theorem sub7_309 : sub7 [2, 2, -1] = true := by decide +kernel
theorem sub7_310 : sub7 [2, 2, 0] = true := by decide +kernel
theorem sub7_311 : sub7 [2, 2, 1] = true := by decide +kernel
theorem sub7_312 : sub7 [2, 2, 2] = true := by decide +kernel
theorem sub7_313 : sub7 [2, 2, 3] = true := by decide +kernel
theorem sub7_314 : sub7 [2, 2, 4] = true := by decide +kernel
theorem sub7_315 : sub7 [2, 2, 5] = true := by decide +kernel
theorem sub7_316 : sub7 [2, 2, 6] = true := by decide +kernel
theorem sub7_317 : sub7 [2, 2, 7] = true := by decide +kernel
theorem sub7_318 : sub7 [2, 3] = true := by decide +kernel
theorem sub7_319 : sub7 [2, 4] = true := by decide +kernel
theorem sb7_9 : ∀ q ∈ blk7_9, sub7 q = true := by
  unfold blk7_9
  exact List.forall_mem_cons.2 ⟨sub7_288, List.forall_mem_cons.2 ⟨sub7_289, List.forall_mem_cons.2 ⟨sub7_290, List.forall_mem_cons.2 ⟨sub7_291, List.forall_mem_cons.2 ⟨sub7_292, List.forall_mem_cons.2 ⟨sub7_293, List.forall_mem_cons.2 ⟨sub7_294, List.forall_mem_cons.2 ⟨sub7_295, List.forall_mem_cons.2 ⟨sub7_296, List.forall_mem_cons.2 ⟨sub7_297, List.forall_mem_cons.2 ⟨sub7_298, List.forall_mem_cons.2 ⟨sub7_299, List.forall_mem_cons.2 ⟨sub7_300, List.forall_mem_cons.2 ⟨sub7_301, List.forall_mem_cons.2 ⟨sub7_302, List.forall_mem_cons.2 ⟨sub7_303, List.forall_mem_cons.2 ⟨sub7_304, List.forall_mem_cons.2 ⟨sub7_305, List.forall_mem_cons.2 ⟨sub7_306, List.forall_mem_cons.2 ⟨sub7_307, List.forall_mem_cons.2 ⟨sub7_308, List.forall_mem_cons.2 ⟨sub7_309, List.forall_mem_cons.2 ⟨sub7_310, List.forall_mem_cons.2 ⟨sub7_311, List.forall_mem_cons.2 ⟨sub7_312, List.forall_mem_cons.2 ⟨sub7_313, List.forall_mem_cons.2 ⟨sub7_314, List.forall_mem_cons.2 ⟨sub7_315, List.forall_mem_cons.2 ⟨sub7_316, List.forall_mem_cons.2 ⟨sub7_317, List.forall_mem_cons.2 ⟨sub7_318, List.forall_mem_cons.2 ⟨sub7_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_320 : sub7 [2, 5] = true := by decide +kernel
theorem sub7_321 : sub7 [3, -2] = true := by decide +kernel
theorem sub7_322 : sub7 [3, -1] = true := by decide +kernel
theorem sub7_323 : sub7 [3, 0] = true := by decide +kernel
theorem sub7_324 : sub7 [3, 1] = true := by decide +kernel
theorem sub7_325 : sub7 [3, 2] = true := by decide +kernel
theorem sub7_326 : sub7 [3, 3] = true := by decide +kernel
theorem sub7_327 : sub7 [3, 4] = true := by decide +kernel
theorem sub7_328 : sub7 [4] = true := by decide +kernel
theorem sb7_10 : ∀ q ∈ blk7_10, sub7 q = true := by
  unfold blk7_10
  exact List.forall_mem_cons.2 ⟨sub7_320, List.forall_mem_cons.2 ⟨sub7_321, List.forall_mem_cons.2 ⟨sub7_322, List.forall_mem_cons.2 ⟨sub7_323, List.forall_mem_cons.2 ⟨sub7_324, List.forall_mem_cons.2 ⟨sub7_325, List.forall_mem_cons.2 ⟨sub7_326, List.forall_mem_cons.2 ⟨sub7_327, List.forall_mem_cons.2 ⟨sub7_328, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_0 : sub8 [-4] = true := by decide +kernel
theorem sub8_1 : sub8 [-3, -5] = true := by decide +kernel
theorem sub8_2 : sub8 [-3, -4] = true := by decide +kernel
theorem sub8_3 : sub8 [-3, -3] = true := by decide +kernel
theorem sub8_4 : sub8 [-3, -2] = true := by decide +kernel
theorem sub8_5 : sub8 [-3, -1] = true := by decide +kernel
theorem sub8_6 : sub8 [-3, 0] = true := by decide +kernel
theorem sub8_7 : sub8 [-3, 1] = true := by decide +kernel
theorem sub8_8 : sub8 [-2, -5] = true := by decide +kernel
theorem sub8_9 : sub8 [-2, -4] = true := by decide +kernel
theorem sub8_10 : sub8 [-2, -3] = true := by decide +kernel
theorem sub8_11 : sub8 [-2, -2, -9] = true := by decide +kernel
theorem sub8_12 : sub8 [-2, -2, -8] = true := by decide +kernel
theorem sub8_13 : sub8 [-2, -2, -7] = true := by decide +kernel
theorem sub8_14 : sub8 [-2, -2, -6] = true := by decide +kernel
theorem sub8_15 : sub8 [-2, -2, -5] = true := by decide +kernel
theorem sub8_16 : sub8 [-2, -2, -4] = true := by decide +kernel
theorem sub8_17 : sub8 [-2, -2, -3] = true := by decide +kernel
theorem sub8_18 : sub8 [-2, -2, -2] = true := by decide +kernel
theorem sub8_19 : sub8 [-2, -2, -1] = true := by decide +kernel
theorem sub8_20 : sub8 [-2, -2, 0] = true := by decide +kernel
theorem sub8_21 : sub8 [-2, -2, 1] = true := by decide +kernel
theorem sub8_22 : sub8 [-2, -2, 2] = true := by decide +kernel
theorem sub8_23 : sub8 [-2, -2, 3] = true := by decide +kernel
theorem sub8_24 : sub8 [-2, -2, 4] = true := by decide +kernel
theorem sub8_25 : sub8 [-2, -1, -9] = true := by decide +kernel
theorem sub8_26 : sub8 [-2, -1, -8] = true := by decide +kernel
theorem sub8_27 : sub8 [-2, -1, -7] = true := by decide +kernel
theorem sub8_28 : sub8 [-2, -1, -6] = true := by decide +kernel
theorem sub8_29 : sub8 [-2, -1, -5] = true := by decide +kernel
theorem sub8_30 : sub8 [-2, -1, -4] = true := by decide +kernel
theorem sub8_31 : sub8 [-2, -1, -3] = true := by decide +kernel
theorem sb8_0 : ∀ q ∈ blk8_0, sub8 q = true := by
  unfold blk8_0
  exact List.forall_mem_cons.2 ⟨sub8_0, List.forall_mem_cons.2 ⟨sub8_1, List.forall_mem_cons.2 ⟨sub8_2, List.forall_mem_cons.2 ⟨sub8_3, List.forall_mem_cons.2 ⟨sub8_4, List.forall_mem_cons.2 ⟨sub8_5, List.forall_mem_cons.2 ⟨sub8_6, List.forall_mem_cons.2 ⟨sub8_7, List.forall_mem_cons.2 ⟨sub8_8, List.forall_mem_cons.2 ⟨sub8_9, List.forall_mem_cons.2 ⟨sub8_10, List.forall_mem_cons.2 ⟨sub8_11, List.forall_mem_cons.2 ⟨sub8_12, List.forall_mem_cons.2 ⟨sub8_13, List.forall_mem_cons.2 ⟨sub8_14, List.forall_mem_cons.2 ⟨sub8_15, List.forall_mem_cons.2 ⟨sub8_16, List.forall_mem_cons.2 ⟨sub8_17, List.forall_mem_cons.2 ⟨sub8_18, List.forall_mem_cons.2 ⟨sub8_19, List.forall_mem_cons.2 ⟨sub8_20, List.forall_mem_cons.2 ⟨sub8_21, List.forall_mem_cons.2 ⟨sub8_22, List.forall_mem_cons.2 ⟨sub8_23, List.forall_mem_cons.2 ⟨sub8_24, List.forall_mem_cons.2 ⟨sub8_25, List.forall_mem_cons.2 ⟨sub8_26, List.forall_mem_cons.2 ⟨sub8_27, List.forall_mem_cons.2 ⟨sub8_28, List.forall_mem_cons.2 ⟨sub8_29, List.forall_mem_cons.2 ⟨sub8_30, List.forall_mem_cons.2 ⟨sub8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_32 : sub8 [-2, -1, -2] = true := by decide +kernel
theorem sub8_33 : sub8 [-2, -1, -1] = true := by decide +kernel
theorem sub8_34 : sub8 [-2, -1, 0] = true := by decide +kernel
theorem sub8_35 : sub8 [-2, -1, 1] = true := by decide +kernel
theorem sub8_36 : sub8 [-2, -1, 2] = true := by decide +kernel
theorem sub8_37 : sub8 [-2, -1, 3] = true := by decide +kernel
theorem sub8_38 : sub8 [-2, -1, 4] = true := by decide +kernel
theorem sub8_39 : sub8 [-2, -1, 5] = true := by decide +kernel
theorem sub8_40 : sub8 [-2, 0, -8] = true := by decide +kernel
theorem sub8_41 : sub8 [-2, 0, -7] = true := by decide +kernel
theorem sub8_42 : sub8 [-2, 0, -6] = true := by decide +kernel
theorem sub8_43 : sub8 [-2, 0, -5] = true := by decide +kernel
theorem sub8_44 : sub8 [-2, 0, -4] = true := by decide +kernel
theorem sub8_45 : sub8 [-2, 0, -3] = true := by decide +kernel
theorem sub8_46 : sub8 [-2, 0, -2] = true := by decide +kernel
theorem sub8_47 : sub8 [-2, 0, -1] = true := by decide +kernel
theorem sub8_48 : sub8 [-2, 0, 0] = true := by decide +kernel
theorem sub8_49 : sub8 [-2, 0, 1] = true := by decide +kernel
theorem sub8_50 : sub8 [-2, 0, 2] = true := by decide +kernel
theorem sub8_51 : sub8 [-2, 0, 3] = true := by decide +kernel
theorem sub8_52 : sub8 [-2, 0, 4] = true := by decide +kernel
theorem sub8_53 : sub8 [-2, 0, 5] = true := by decide +kernel
theorem sub8_54 : sub8 [-2, 1] = true := by decide +kernel
theorem sub8_55 : sub8 [-2, 2] = true := by decide +kernel
theorem sub8_56 : sub8 [-2, 3] = true := by decide +kernel
theorem sub8_57 : sub8 [-1, -5] = true := by decide +kernel
theorem sub8_58 : sub8 [-1, -4] = true := by decide +kernel
theorem sub8_59 : sub8 [-1, -3] = true := by decide +kernel
theorem sub8_60 : sub8 [-1, -2, -9] = true := by decide +kernel
theorem sub8_61 : sub8 [-1, -2, -8] = true := by decide +kernel
theorem sub8_62 : sub8 [-1, -2, -7] = true := by decide +kernel
theorem sub8_63 : sub8 [-1, -2, -6] = true := by decide +kernel
theorem sb8_1 : ∀ q ∈ blk8_1, sub8 q = true := by
  unfold blk8_1
  exact List.forall_mem_cons.2 ⟨sub8_32, List.forall_mem_cons.2 ⟨sub8_33, List.forall_mem_cons.2 ⟨sub8_34, List.forall_mem_cons.2 ⟨sub8_35, List.forall_mem_cons.2 ⟨sub8_36, List.forall_mem_cons.2 ⟨sub8_37, List.forall_mem_cons.2 ⟨sub8_38, List.forall_mem_cons.2 ⟨sub8_39, List.forall_mem_cons.2 ⟨sub8_40, List.forall_mem_cons.2 ⟨sub8_41, List.forall_mem_cons.2 ⟨sub8_42, List.forall_mem_cons.2 ⟨sub8_43, List.forall_mem_cons.2 ⟨sub8_44, List.forall_mem_cons.2 ⟨sub8_45, List.forall_mem_cons.2 ⟨sub8_46, List.forall_mem_cons.2 ⟨sub8_47, List.forall_mem_cons.2 ⟨sub8_48, List.forall_mem_cons.2 ⟨sub8_49, List.forall_mem_cons.2 ⟨sub8_50, List.forall_mem_cons.2 ⟨sub8_51, List.forall_mem_cons.2 ⟨sub8_52, List.forall_mem_cons.2 ⟨sub8_53, List.forall_mem_cons.2 ⟨sub8_54, List.forall_mem_cons.2 ⟨sub8_55, List.forall_mem_cons.2 ⟨sub8_56, List.forall_mem_cons.2 ⟨sub8_57, List.forall_mem_cons.2 ⟨sub8_58, List.forall_mem_cons.2 ⟨sub8_59, List.forall_mem_cons.2 ⟨sub8_60, List.forall_mem_cons.2 ⟨sub8_61, List.forall_mem_cons.2 ⟨sub8_62, List.forall_mem_cons.2 ⟨sub8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_64 : sub8 [-1, -2, -5] = true := by decide +kernel
theorem sub8_65 : sub8 [-1, -2, -4] = true := by decide +kernel
theorem sub8_66 : sub8 [-1, -2, -3] = true := by decide +kernel
theorem sub8_67 : sub8 [-1, -2, -2] = true := by decide +kernel
theorem sub8_68 : sub8 [-1, -2, -1] = true := by decide +kernel
theorem sub8_69 : sub8 [-1, -2, 0] = true := by decide +kernel
theorem sub8_70 : sub8 [-1, -2, 1] = true := by decide +kernel
theorem sub8_71 : sub8 [-1, -2, 2] = true := by decide +kernel
theorem sub8_72 : sub8 [-1, -2, 3] = true := by decide +kernel
theorem sub8_73 : sub8 [-1, -2, 4] = true := by decide +kernel
theorem sub8_74 : sub8 [-1, -2, 5] = true := by decide +kernel
theorem sub8_75 : sub8 [-1, -1, -9] = true := by decide +kernel
theorem sub8_76 : sub8 [-1, -1, -8] = true := by decide +kernel
theorem sub8_77 : sub8 [-1, -1, -7] = true := by decide +kernel
theorem sub8_78 : sub8 [-1, -1, -6] = true := by decide +kernel
theorem sub8_79 : sub8 [-1, -1, -5] = true := by decide +kernel
theorem sub8_80 : sub8 [-1, -1, -4] = true := by decide +kernel
theorem sub8_81 : sub8 [-1, -1, -3] = true := by decide +kernel
theorem sub8_82 : sub8 [-1, -1, -2] = true := by decide +kernel
theorem sub8_83 : sub8 [-1, -1, -1] = true := by decide +kernel
theorem sub8_84 : sub8 [-1, -1, 0] = true := by decide +kernel
theorem sub8_85 : sub8 [-1, -1, 1] = true := by decide +kernel
theorem sub8_86 : sub8 [-1, -1, 2] = true := by decide +kernel
theorem sub8_87 : sub8 [-1, -1, 3] = true := by decide +kernel
theorem sub8_88 : sub8 [-1, -1, 4] = true := by decide +kernel
theorem sub8_89 : sub8 [-1, -1, 5] = true := by decide +kernel
theorem sub8_90 : sub8 [-1, -1, 6] = true := by decide +kernel
theorem sub8_91 : sub8 [-1, 0, -8] = true := by decide +kernel
theorem sub8_92 : sub8 [-1, 0, -7] = true := by decide +kernel
theorem sub8_93 : sub8 [-1, 0, -6] = true := by decide +kernel
theorem sub8_94 : sub8 [-1, 0, -5] = true := by decide +kernel
theorem sub8_95 : sub8 [-1, 0, -4] = true := by decide +kernel
theorem sb8_2 : ∀ q ∈ blk8_2, sub8 q = true := by
  unfold blk8_2
  exact List.forall_mem_cons.2 ⟨sub8_64, List.forall_mem_cons.2 ⟨sub8_65, List.forall_mem_cons.2 ⟨sub8_66, List.forall_mem_cons.2 ⟨sub8_67, List.forall_mem_cons.2 ⟨sub8_68, List.forall_mem_cons.2 ⟨sub8_69, List.forall_mem_cons.2 ⟨sub8_70, List.forall_mem_cons.2 ⟨sub8_71, List.forall_mem_cons.2 ⟨sub8_72, List.forall_mem_cons.2 ⟨sub8_73, List.forall_mem_cons.2 ⟨sub8_74, List.forall_mem_cons.2 ⟨sub8_75, List.forall_mem_cons.2 ⟨sub8_76, List.forall_mem_cons.2 ⟨sub8_77, List.forall_mem_cons.2 ⟨sub8_78, List.forall_mem_cons.2 ⟨sub8_79, List.forall_mem_cons.2 ⟨sub8_80, List.forall_mem_cons.2 ⟨sub8_81, List.forall_mem_cons.2 ⟨sub8_82, List.forall_mem_cons.2 ⟨sub8_83, List.forall_mem_cons.2 ⟨sub8_84, List.forall_mem_cons.2 ⟨sub8_85, List.forall_mem_cons.2 ⟨sub8_86, List.forall_mem_cons.2 ⟨sub8_87, List.forall_mem_cons.2 ⟨sub8_88, List.forall_mem_cons.2 ⟨sub8_89, List.forall_mem_cons.2 ⟨sub8_90, List.forall_mem_cons.2 ⟨sub8_91, List.forall_mem_cons.2 ⟨sub8_92, List.forall_mem_cons.2 ⟨sub8_93, List.forall_mem_cons.2 ⟨sub8_94, List.forall_mem_cons.2 ⟨sub8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_96 : sub8 [-1, 0, -3] = true := by decide +kernel
theorem sub8_97 : sub8 [-1, 0, -2] = true := by decide +kernel
theorem sub8_98 : sub8 [-1, 0, -1] = true := by decide +kernel
theorem sub8_99 : sub8 [-1, 0, 0] = true := by decide +kernel
theorem sub8_100 : sub8 [-1, 0, 1] = true := by decide +kernel
theorem sub8_101 : sub8 [-1, 0, 2] = true := by decide +kernel
theorem sub8_102 : sub8 [-1, 0, 3] = true := by decide +kernel
theorem sub8_103 : sub8 [-1, 0, 4] = true := by decide +kernel
theorem sub8_104 : sub8 [-1, 0, 5] = true := by decide +kernel
theorem sub8_105 : sub8 [-1, 0, 6] = true := by decide +kernel
theorem sub8_106 : sub8 [-1, 0, 7] = true := by decide +kernel
theorem sub8_107 : sub8 [-1, 1, -8] = true := by decide +kernel
theorem sub8_108 : sub8 [-1, 1, -7] = true := by decide +kernel
theorem sub8_109 : sub8 [-1, 1, -6] = true := by decide +kernel
theorem sub8_110 : sub8 [-1, 1, -5] = true := by decide +kernel
theorem sub8_111 : sub8 [-1, 1, -4] = true := by decide +kernel
theorem sub8_112 : sub8 [-1, 1, -3] = true := by decide +kernel
theorem sub8_113 : sub8 [-1, 1, -2] = true := by decide +kernel
theorem sub8_114 : sub8 [-1, 1, -1] = true := by decide +kernel
theorem sub8_115 : sub8 [-1, 1, 0] = true := by decide +kernel
theorem sub8_116 : sub8 [-1, 1, 1] = true := by decide +kernel
theorem sub8_117 : sub8 [-1, 1, 2] = true := by decide +kernel
theorem sub8_118 : sub8 [-1, 1, 3] = true := by decide +kernel
theorem sub8_119 : sub8 [-1, 1, 4] = true := by decide +kernel
theorem sub8_120 : sub8 [-1, 1, 5] = true := by decide +kernel
theorem sub8_121 : sub8 [-1, 1, 6] = true := by decide +kernel
theorem sub8_122 : sub8 [-1, 1, 7] = true := by decide +kernel
theorem sub8_123 : sub8 [-1, 2, -6] = true := by decide +kernel
theorem sub8_124 : sub8 [-1, 2, -5] = true := by decide +kernel
theorem sub8_125 : sub8 [-1, 2, -4] = true := by decide +kernel
theorem sub8_126 : sub8 [-1, 2, -3] = true := by decide +kernel
theorem sub8_127 : sub8 [-1, 2, -2] = true := by decide +kernel
theorem sb8_3 : ∀ q ∈ blk8_3, sub8 q = true := by
  unfold blk8_3
  exact List.forall_mem_cons.2 ⟨sub8_96, List.forall_mem_cons.2 ⟨sub8_97, List.forall_mem_cons.2 ⟨sub8_98, List.forall_mem_cons.2 ⟨sub8_99, List.forall_mem_cons.2 ⟨sub8_100, List.forall_mem_cons.2 ⟨sub8_101, List.forall_mem_cons.2 ⟨sub8_102, List.forall_mem_cons.2 ⟨sub8_103, List.forall_mem_cons.2 ⟨sub8_104, List.forall_mem_cons.2 ⟨sub8_105, List.forall_mem_cons.2 ⟨sub8_106, List.forall_mem_cons.2 ⟨sub8_107, List.forall_mem_cons.2 ⟨sub8_108, List.forall_mem_cons.2 ⟨sub8_109, List.forall_mem_cons.2 ⟨sub8_110, List.forall_mem_cons.2 ⟨sub8_111, List.forall_mem_cons.2 ⟨sub8_112, List.forall_mem_cons.2 ⟨sub8_113, List.forall_mem_cons.2 ⟨sub8_114, List.forall_mem_cons.2 ⟨sub8_115, List.forall_mem_cons.2 ⟨sub8_116, List.forall_mem_cons.2 ⟨sub8_117, List.forall_mem_cons.2 ⟨sub8_118, List.forall_mem_cons.2 ⟨sub8_119, List.forall_mem_cons.2 ⟨sub8_120, List.forall_mem_cons.2 ⟨sub8_121, List.forall_mem_cons.2 ⟨sub8_122, List.forall_mem_cons.2 ⟨sub8_123, List.forall_mem_cons.2 ⟨sub8_124, List.forall_mem_cons.2 ⟨sub8_125, List.forall_mem_cons.2 ⟨sub8_126, List.forall_mem_cons.2 ⟨sub8_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_128 : sub8 [-1, 2, -1] = true := by decide +kernel
theorem sub8_129 : sub8 [-1, 2, 0] = true := by decide +kernel
theorem sub8_130 : sub8 [-1, 2, 1] = true := by decide +kernel
theorem sub8_131 : sub8 [-1, 2, 2] = true := by decide +kernel
theorem sub8_132 : sub8 [-1, 2, 3] = true := by decide +kernel
theorem sub8_133 : sub8 [-1, 2, 4] = true := by decide +kernel
theorem sub8_134 : sub8 [-1, 2, 5] = true := by decide +kernel
theorem sub8_135 : sub8 [-1, 2, 6] = true := by decide +kernel
theorem sub8_136 : sub8 [-1, 3] = true := by decide +kernel
theorem sub8_137 : sub8 [0, -5] = true := by decide +kernel
theorem sub8_138 : sub8 [0, -4] = true := by decide +kernel
theorem sub8_139 : sub8 [0, -3] = true := by decide +kernel
theorem sub8_140 : sub8 [0, -2, -9] = true := by decide +kernel
theorem sub8_141 : sub8 [0, -2, -8] = true := by decide +kernel
theorem sub8_142 : sub8 [0, -2, -7] = true := by decide +kernel
theorem sub8_143 : sub8 [0, -2, -6] = true := by decide +kernel
theorem sub8_144 : sub8 [0, -2, -5] = true := by decide +kernel
theorem sub8_145 : sub8 [0, -2, -4] = true := by decide +kernel
theorem sub8_146 : sub8 [0, -2, -3] = true := by decide +kernel
theorem sub8_147 : sub8 [0, -2, -2] = true := by decide +kernel
theorem sub8_148 : sub8 [0, -2, -1] = true := by decide +kernel
theorem sub8_149 : sub8 [0, -2, 0] = true := by decide +kernel
theorem sub8_150 : sub8 [0, -2, 1] = true := by decide +kernel
theorem sub8_151 : sub8 [0, -2, 2] = true := by decide +kernel
theorem sub8_152 : sub8 [0, -2, 3] = true := by decide +kernel
theorem sub8_153 : sub8 [0, -2, 4] = true := by decide +kernel
theorem sub8_154 : sub8 [0, -2, 5] = true := by decide +kernel
theorem sub8_155 : sub8 [0, -2, 6] = true := by decide +kernel
theorem sub8_156 : sub8 [0, -1, -9] = true := by decide +kernel
theorem sub8_157 : sub8 [0, -1, -8] = true := by decide +kernel
theorem sub8_158 : sub8 [0, -1, -7] = true := by decide +kernel
theorem sub8_159 : sub8 [0, -1, -6] = true := by decide +kernel
theorem sb8_4 : ∀ q ∈ blk8_4, sub8 q = true := by
  unfold blk8_4
  exact List.forall_mem_cons.2 ⟨sub8_128, List.forall_mem_cons.2 ⟨sub8_129, List.forall_mem_cons.2 ⟨sub8_130, List.forall_mem_cons.2 ⟨sub8_131, List.forall_mem_cons.2 ⟨sub8_132, List.forall_mem_cons.2 ⟨sub8_133, List.forall_mem_cons.2 ⟨sub8_134, List.forall_mem_cons.2 ⟨sub8_135, List.forall_mem_cons.2 ⟨sub8_136, List.forall_mem_cons.2 ⟨sub8_137, List.forall_mem_cons.2 ⟨sub8_138, List.forall_mem_cons.2 ⟨sub8_139, List.forall_mem_cons.2 ⟨sub8_140, List.forall_mem_cons.2 ⟨sub8_141, List.forall_mem_cons.2 ⟨sub8_142, List.forall_mem_cons.2 ⟨sub8_143, List.forall_mem_cons.2 ⟨sub8_144, List.forall_mem_cons.2 ⟨sub8_145, List.forall_mem_cons.2 ⟨sub8_146, List.forall_mem_cons.2 ⟨sub8_147, List.forall_mem_cons.2 ⟨sub8_148, List.forall_mem_cons.2 ⟨sub8_149, List.forall_mem_cons.2 ⟨sub8_150, List.forall_mem_cons.2 ⟨sub8_151, List.forall_mem_cons.2 ⟨sub8_152, List.forall_mem_cons.2 ⟨sub8_153, List.forall_mem_cons.2 ⟨sub8_154, List.forall_mem_cons.2 ⟨sub8_155, List.forall_mem_cons.2 ⟨sub8_156, List.forall_mem_cons.2 ⟨sub8_157, List.forall_mem_cons.2 ⟨sub8_158, List.forall_mem_cons.2 ⟨sub8_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_160 : sub8 [0, -1, -5] = true := by decide +kernel
theorem sub8_161 : sub8 [0, -1, -4] = true := by decide +kernel
theorem sub8_162 : sub8 [0, -1, -3] = true := by decide +kernel
theorem sub8_163 : sub8 [0, -1, -2] = true := by decide +kernel
theorem sub8_164 : sub8 [0, -1, -1] = true := by decide +kernel
theorem sub8_165 : sub8 [0, -1, 0] = true := by decide +kernel
theorem sub8_166 : sub8 [0, -1, 1] = true := by decide +kernel
theorem sub8_167 : sub8 [0, -1, 2] = true := by decide +kernel
theorem sub8_168 : sub8 [0, -1, 3] = true := by decide +kernel
theorem sub8_169 : sub8 [0, -1, 4] = true := by decide +kernel
theorem sub8_170 : sub8 [0, -1, 5] = true := by decide +kernel
theorem sub8_171 : sub8 [0, -1, 6] = true := by decide +kernel
theorem sub8_172 : sub8 [0, -1, 7] = true := by decide +kernel
theorem sub8_173 : sub8 [0, 0, -8] = true := by decide +kernel
theorem sub8_174 : sub8 [0, 0, -7] = true := by decide +kernel
theorem sub8_175 : sub8 [0, 0, -6] = true := by decide +kernel
theorem sub8_176 : sub8 [0, 0, -5] = true := by decide +kernel
theorem sub8_177 : sub8 [0, 0, -4] = true := by decide +kernel
theorem sub8_178 : sub8 [0, 0, -3] = true := by decide +kernel
theorem sub8_179 : sub8 [0, 0, -2] = true := by decide +kernel
theorem sub8_180 : sub8 [0, 0, -1] = true := by decide +kernel
theorem sub8_181 : sub8 [0, 0, 0] = true := by decide +kernel
theorem sub8_182 : sub8 [0, 0, 1] = true := by decide +kernel
theorem sub8_183 : sub8 [0, 0, 2] = true := by decide +kernel
theorem sub8_184 : sub8 [0, 0, 3] = true := by decide +kernel
theorem sub8_185 : sub8 [0, 0, 4] = true := by decide +kernel
theorem sub8_186 : sub8 [0, 0, 5] = true := by decide +kernel
theorem sub8_187 : sub8 [0, 0, 6] = true := by decide +kernel
theorem sub8_188 : sub8 [0, 0, 7] = true := by decide +kernel
theorem sub8_189 : sub8 [0, 1, -8] = true := by decide +kernel
theorem sub8_190 : sub8 [0, 1, -7] = true := by decide +kernel
theorem sub8_191 : sub8 [0, 1, -6] = true := by decide +kernel
theorem sb8_5 : ∀ q ∈ blk8_5, sub8 q = true := by
  unfold blk8_5
  exact List.forall_mem_cons.2 ⟨sub8_160, List.forall_mem_cons.2 ⟨sub8_161, List.forall_mem_cons.2 ⟨sub8_162, List.forall_mem_cons.2 ⟨sub8_163, List.forall_mem_cons.2 ⟨sub8_164, List.forall_mem_cons.2 ⟨sub8_165, List.forall_mem_cons.2 ⟨sub8_166, List.forall_mem_cons.2 ⟨sub8_167, List.forall_mem_cons.2 ⟨sub8_168, List.forall_mem_cons.2 ⟨sub8_169, List.forall_mem_cons.2 ⟨sub8_170, List.forall_mem_cons.2 ⟨sub8_171, List.forall_mem_cons.2 ⟨sub8_172, List.forall_mem_cons.2 ⟨sub8_173, List.forall_mem_cons.2 ⟨sub8_174, List.forall_mem_cons.2 ⟨sub8_175, List.forall_mem_cons.2 ⟨sub8_176, List.forall_mem_cons.2 ⟨sub8_177, List.forall_mem_cons.2 ⟨sub8_178, List.forall_mem_cons.2 ⟨sub8_179, List.forall_mem_cons.2 ⟨sub8_180, List.forall_mem_cons.2 ⟨sub8_181, List.forall_mem_cons.2 ⟨sub8_182, List.forall_mem_cons.2 ⟨sub8_183, List.forall_mem_cons.2 ⟨sub8_184, List.forall_mem_cons.2 ⟨sub8_185, List.forall_mem_cons.2 ⟨sub8_186, List.forall_mem_cons.2 ⟨sub8_187, List.forall_mem_cons.2 ⟨sub8_188, List.forall_mem_cons.2 ⟨sub8_189, List.forall_mem_cons.2 ⟨sub8_190, List.forall_mem_cons.2 ⟨sub8_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_192 : sub8 [0, 1, -5] = true := by decide +kernel
theorem sub8_193 : sub8 [0, 1, -4] = true := by decide +kernel
theorem sub8_194 : sub8 [0, 1, -3] = true := by decide +kernel
theorem sub8_195 : sub8 [0, 1, -2] = true := by decide +kernel
theorem sub8_196 : sub8 [0, 1, -1] = true := by decide +kernel
theorem sub8_197 : sub8 [0, 1, 0] = true := by decide +kernel
theorem sub8_198 : sub8 [0, 1, 1] = true := by decide +kernel
theorem sub8_199 : sub8 [0, 1, 2] = true := by decide +kernel
theorem sub8_200 : sub8 [0, 1, 3] = true := by decide +kernel
theorem sub8_201 : sub8 [0, 1, 4] = true := by decide +kernel
theorem sub8_202 : sub8 [0, 1, 5] = true := by decide +kernel
theorem sub8_203 : sub8 [0, 1, 6] = true := by decide +kernel
theorem sub8_204 : sub8 [0, 1, 7] = true := by decide +kernel
theorem sub8_205 : sub8 [0, 1, 8] = true := by decide +kernel
theorem sub8_206 : sub8 [0, 2, -7] = true := by decide +kernel
theorem sub8_207 : sub8 [0, 2, -6] = true := by decide +kernel
theorem sub8_208 : sub8 [0, 2, -5] = true := by decide +kernel
theorem sub8_209 : sub8 [0, 2, -4] = true := by decide +kernel
theorem sub8_210 : sub8 [0, 2, -3] = true := by decide +kernel
theorem sub8_211 : sub8 [0, 2, -2] = true := by decide +kernel
theorem sub8_212 : sub8 [0, 2, -1] = true := by decide +kernel
theorem sub8_213 : sub8 [0, 2, 0] = true := by decide +kernel
theorem sub8_214 : sub8 [0, 2, 1] = true := by decide +kernel
theorem sub8_215 : sub8 [0, 2, 2] = true := by decide +kernel
theorem sub8_216 : sub8 [0, 2, 3] = true := by decide +kernel
theorem sub8_217 : sub8 [0, 2, 4] = true := by decide +kernel
theorem sub8_218 : sub8 [0, 2, 5] = true := by decide +kernel
theorem sub8_219 : sub8 [0, 2, 6] = true := by decide +kernel
theorem sub8_220 : sub8 [0, 2, 7] = true := by decide +kernel
theorem sub8_221 : sub8 [0, 2, 8] = true := by decide +kernel
theorem sub8_222 : sub8 [0, 3] = true := by decide +kernel
theorem sub8_223 : sub8 [0, 4] = true := by decide +kernel
theorem sb8_6 : ∀ q ∈ blk8_6, sub8 q = true := by
  unfold blk8_6
  exact List.forall_mem_cons.2 ⟨sub8_192, List.forall_mem_cons.2 ⟨sub8_193, List.forall_mem_cons.2 ⟨sub8_194, List.forall_mem_cons.2 ⟨sub8_195, List.forall_mem_cons.2 ⟨sub8_196, List.forall_mem_cons.2 ⟨sub8_197, List.forall_mem_cons.2 ⟨sub8_198, List.forall_mem_cons.2 ⟨sub8_199, List.forall_mem_cons.2 ⟨sub8_200, List.forall_mem_cons.2 ⟨sub8_201, List.forall_mem_cons.2 ⟨sub8_202, List.forall_mem_cons.2 ⟨sub8_203, List.forall_mem_cons.2 ⟨sub8_204, List.forall_mem_cons.2 ⟨sub8_205, List.forall_mem_cons.2 ⟨sub8_206, List.forall_mem_cons.2 ⟨sub8_207, List.forall_mem_cons.2 ⟨sub8_208, List.forall_mem_cons.2 ⟨sub8_209, List.forall_mem_cons.2 ⟨sub8_210, List.forall_mem_cons.2 ⟨sub8_211, List.forall_mem_cons.2 ⟨sub8_212, List.forall_mem_cons.2 ⟨sub8_213, List.forall_mem_cons.2 ⟨sub8_214, List.forall_mem_cons.2 ⟨sub8_215, List.forall_mem_cons.2 ⟨sub8_216, List.forall_mem_cons.2 ⟨sub8_217, List.forall_mem_cons.2 ⟨sub8_218, List.forall_mem_cons.2 ⟨sub8_219, List.forall_mem_cons.2 ⟨sub8_220, List.forall_mem_cons.2 ⟨sub8_221, List.forall_mem_cons.2 ⟨sub8_222, List.forall_mem_cons.2 ⟨sub8_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_224 : sub8 [1, -4] = true := by decide +kernel
theorem sub8_225 : sub8 [1, -3] = true := by decide +kernel
theorem sub8_226 : sub8 [1, -2, -7] = true := by decide +kernel
theorem sub8_227 : sub8 [1, -2, -6] = true := by decide +kernel
theorem sub8_228 : sub8 [1, -2, -5] = true := by decide +kernel
theorem sub8_229 : sub8 [1, -2, -4] = true := by decide +kernel
theorem sub8_230 : sub8 [1, -2, -3] = true := by decide +kernel
theorem sub8_231 : sub8 [1, -2, -2] = true := by decide +kernel
theorem sub8_232 : sub8 [1, -2, -1] = true := by decide +kernel
theorem sub8_233 : sub8 [1, -2, 0] = true := by decide +kernel
theorem sub8_234 : sub8 [1, -2, 1] = true := by decide +kernel
theorem sub8_235 : sub8 [1, -2, 2] = true := by decide +kernel
theorem sub8_236 : sub8 [1, -2, 3] = true := by decide +kernel
theorem sub8_237 : sub8 [1, -2, 4] = true := by decide +kernel
theorem sub8_238 : sub8 [1, -2, 5] = true := by decide +kernel
theorem sub8_239 : sub8 [1, -1, -8] = true := by decide +kernel
theorem sub8_240 : sub8 [1, -1, -7] = true := by decide +kernel
theorem sub8_241 : sub8 [1, -1, -6] = true := by decide +kernel
theorem sub8_242 : sub8 [1, -1, -5] = true := by decide +kernel
theorem sub8_243 : sub8 [1, -1, -4] = true := by decide +kernel
theorem sub8_244 : sub8 [1, -1, -3] = true := by decide +kernel
theorem sub8_245 : sub8 [1, -1, -2] = true := by decide +kernel
theorem sub8_246 : sub8 [1, -1, -1] = true := by decide +kernel
theorem sub8_247 : sub8 [1, -1, 0] = true := by decide +kernel
theorem sub8_248 : sub8 [1, -1, 1] = true := by decide +kernel
theorem sub8_249 : sub8 [1, -1, 2] = true := by decide +kernel
theorem sub8_250 : sub8 [1, -1, 3] = true := by decide +kernel
theorem sub8_251 : sub8 [1, -1, 4] = true := by decide +kernel
theorem sub8_252 : sub8 [1, -1, 5] = true := by decide +kernel
theorem sub8_253 : sub8 [1, -1, 6] = true := by decide +kernel
theorem sub8_254 : sub8 [1, -1, 7] = true := by decide +kernel
theorem sub8_255 : sub8 [1, 0, -8] = true := by decide +kernel
theorem sb8_7 : ∀ q ∈ blk8_7, sub8 q = true := by
  unfold blk8_7
  exact List.forall_mem_cons.2 ⟨sub8_224, List.forall_mem_cons.2 ⟨sub8_225, List.forall_mem_cons.2 ⟨sub8_226, List.forall_mem_cons.2 ⟨sub8_227, List.forall_mem_cons.2 ⟨sub8_228, List.forall_mem_cons.2 ⟨sub8_229, List.forall_mem_cons.2 ⟨sub8_230, List.forall_mem_cons.2 ⟨sub8_231, List.forall_mem_cons.2 ⟨sub8_232, List.forall_mem_cons.2 ⟨sub8_233, List.forall_mem_cons.2 ⟨sub8_234, List.forall_mem_cons.2 ⟨sub8_235, List.forall_mem_cons.2 ⟨sub8_236, List.forall_mem_cons.2 ⟨sub8_237, List.forall_mem_cons.2 ⟨sub8_238, List.forall_mem_cons.2 ⟨sub8_239, List.forall_mem_cons.2 ⟨sub8_240, List.forall_mem_cons.2 ⟨sub8_241, List.forall_mem_cons.2 ⟨sub8_242, List.forall_mem_cons.2 ⟨sub8_243, List.forall_mem_cons.2 ⟨sub8_244, List.forall_mem_cons.2 ⟨sub8_245, List.forall_mem_cons.2 ⟨sub8_246, List.forall_mem_cons.2 ⟨sub8_247, List.forall_mem_cons.2 ⟨sub8_248, List.forall_mem_cons.2 ⟨sub8_249, List.forall_mem_cons.2 ⟨sub8_250, List.forall_mem_cons.2 ⟨sub8_251, List.forall_mem_cons.2 ⟨sub8_252, List.forall_mem_cons.2 ⟨sub8_253, List.forall_mem_cons.2 ⟨sub8_254, List.forall_mem_cons.2 ⟨sub8_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_256 : sub8 [1, 0, -7] = true := by decide +kernel
theorem sub8_257 : sub8 [1, 0, -6] = true := by decide +kernel
theorem sub8_258 : sub8 [1, 0, -5] = true := by decide +kernel
theorem sub8_259 : sub8 [1, 0, -4] = true := by decide +kernel
theorem sub8_260 : sub8 [1, 0, -3] = true := by decide +kernel
theorem sub8_261 : sub8 [1, 0, -2] = true := by decide +kernel
theorem sub8_262 : sub8 [1, 0, -1] = true := by decide +kernel
theorem sub8_263 : sub8 [1, 0, 0] = true := by decide +kernel
theorem sub8_264 : sub8 [1, 0, 1] = true := by decide +kernel
theorem sub8_265 : sub8 [1, 0, 2] = true := by decide +kernel
theorem sub8_266 : sub8 [1, 0, 3] = true := by decide +kernel
theorem sub8_267 : sub8 [1, 0, 4] = true := by decide +kernel
theorem sub8_268 : sub8 [1, 0, 5] = true := by decide +kernel
theorem sub8_269 : sub8 [1, 0, 6] = true := by decide +kernel
theorem sub8_270 : sub8 [1, 0, 7] = true := by decide +kernel
theorem sub8_271 : sub8 [1, 1, -7] = true := by decide +kernel
theorem sub8_272 : sub8 [1, 1, -6] = true := by decide +kernel
theorem sub8_273 : sub8 [1, 1, -5] = true := by decide +kernel
theorem sub8_274 : sub8 [1, 1, -4] = true := by decide +kernel
theorem sub8_275 : sub8 [1, 1, -3] = true := by decide +kernel
theorem sub8_276 : sub8 [1, 1, -2] = true := by decide +kernel
theorem sub8_277 : sub8 [1, 1, -1] = true := by decide +kernel
theorem sub8_278 : sub8 [1, 1, 0] = true := by decide +kernel
theorem sub8_279 : sub8 [1, 1, 1] = true := by decide +kernel
theorem sub8_280 : sub8 [1, 1, 2] = true := by decide +kernel
theorem sub8_281 : sub8 [1, 1, 3] = true := by decide +kernel
theorem sub8_282 : sub8 [1, 1, 4] = true := by decide +kernel
theorem sub8_283 : sub8 [1, 1, 5] = true := by decide +kernel
theorem sub8_284 : sub8 [1, 1, 6] = true := by decide +kernel
theorem sub8_285 : sub8 [1, 1, 7] = true := by decide +kernel
theorem sub8_286 : sub8 [1, 1, 8] = true := by decide +kernel
theorem sub8_287 : sub8 [1, 2, -6] = true := by decide +kernel
theorem sb8_8 : ∀ q ∈ blk8_8, sub8 q = true := by
  unfold blk8_8
  exact List.forall_mem_cons.2 ⟨sub8_256, List.forall_mem_cons.2 ⟨sub8_257, List.forall_mem_cons.2 ⟨sub8_258, List.forall_mem_cons.2 ⟨sub8_259, List.forall_mem_cons.2 ⟨sub8_260, List.forall_mem_cons.2 ⟨sub8_261, List.forall_mem_cons.2 ⟨sub8_262, List.forall_mem_cons.2 ⟨sub8_263, List.forall_mem_cons.2 ⟨sub8_264, List.forall_mem_cons.2 ⟨sub8_265, List.forall_mem_cons.2 ⟨sub8_266, List.forall_mem_cons.2 ⟨sub8_267, List.forall_mem_cons.2 ⟨sub8_268, List.forall_mem_cons.2 ⟨sub8_269, List.forall_mem_cons.2 ⟨sub8_270, List.forall_mem_cons.2 ⟨sub8_271, List.forall_mem_cons.2 ⟨sub8_272, List.forall_mem_cons.2 ⟨sub8_273, List.forall_mem_cons.2 ⟨sub8_274, List.forall_mem_cons.2 ⟨sub8_275, List.forall_mem_cons.2 ⟨sub8_276, List.forall_mem_cons.2 ⟨sub8_277, List.forall_mem_cons.2 ⟨sub8_278, List.forall_mem_cons.2 ⟨sub8_279, List.forall_mem_cons.2 ⟨sub8_280, List.forall_mem_cons.2 ⟨sub8_281, List.forall_mem_cons.2 ⟨sub8_282, List.forall_mem_cons.2 ⟨sub8_283, List.forall_mem_cons.2 ⟨sub8_284, List.forall_mem_cons.2 ⟨sub8_285, List.forall_mem_cons.2 ⟨sub8_286, List.forall_mem_cons.2 ⟨sub8_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C076
