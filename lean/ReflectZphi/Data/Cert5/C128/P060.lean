import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_7_256 : subd8_7 [2, 1, -5] = true := by decide +kernel
theorem subd8_7_257 : subd8_7 [2, 1, -4] = true := by decide +kernel
theorem subd8_7_258 : subd8_7 [2, 1, -3] = true := by decide +kernel
theorem subd8_7_259 : subd8_7 [2, 1, -2] = true := by decide +kernel
theorem subd8_7_260 : subd8_7 [2, 1, -1] = true := by decide +kernel
theorem subd8_7_261 : subd8_7 [2, 1, 0] = true := by decide +kernel
theorem subd8_7_262 : subd8_7 [2, 1, 1] = true := by decide +kernel
theorem subd8_7_263 : subd8_7 [2, 1, 2] = true := by decide +kernel
theorem subd8_7_264 : subd8_7 [2, 1, 3] = true := by decide +kernel
theorem subd8_7_265 : subd8_7 [2, 1, 4] = true := by decide +kernel
theorem subd8_7_266 : subd8_7 [2, 1, 5] = true := by decide +kernel
theorem subd8_7_267 : subd8_7 [2, 1, 6] = true := by decide +kernel
theorem subd8_7_268 : subd8_7 [2, 2] = true := by decide +kernel
theorem subd8_7_269 : subd8_7 [2, 3] = true := by decide +kernel
theorem subd8_7_270 : subd8_7 [2, 4] = true := by decide +kernel
theorem subd8_7_271 : subd8_7 [2, 5] = true := by decide +kernel
theorem subd8_7_272 : subd8_7 [3, -4] = true := by decide +kernel
theorem subd8_7_273 : subd8_7 [3, -3] = true := by decide +kernel
theorem subd8_7_274 : subd8_7 [3, -2] = true := by decide +kernel
theorem subd8_7_275 : subd8_7 [3, -1] = true := by decide +kernel
theorem subd8_7_276 : subd8_7 [3, 0] = true := by decide +kernel
theorem subd8_7_277 : subd8_7 [3, 1] = true := by decide +kernel
theorem subd8_7_278 : subd8_7 [3, 2] = true := by decide +kernel
theorem subd8_7_279 : subd8_7 [3, 3] = true := by decide +kernel
theorem subd8_7_280 : subd8_7 [3, 4] = true := by decide +kernel
theorem subd8_7_281 : subd8_7 [3, 5] = true := by decide +kernel
theorem subd8_7_282 : subd8_7 [4, -2] = true := by decide +kernel
theorem subd8_7_283 : subd8_7 [4, -1] = true := by decide +kernel
theorem subd8_7_284 : subd8_7 [4, 0] = true := by decide +kernel
theorem subd8_7_285 : subd8_7 [4, 1] = true := by decide +kernel
theorem subd8_7_286 : subd8_7 [4, 2] = true := by decide +kernel
theorem subd8_7_287 : subd8_7 [4, 3] = true := by decide +kernel
theorem sbd8_7_8 : ∀ q ∈ blkd8_7_8, subd8_7 q = true := by
  unfold blkd8_7_8
  exact List.forall_mem_cons.2 ⟨subd8_7_256, List.forall_mem_cons.2 ⟨subd8_7_257, List.forall_mem_cons.2 ⟨subd8_7_258, List.forall_mem_cons.2 ⟨subd8_7_259, List.forall_mem_cons.2 ⟨subd8_7_260, List.forall_mem_cons.2 ⟨subd8_7_261, List.forall_mem_cons.2 ⟨subd8_7_262, List.forall_mem_cons.2 ⟨subd8_7_263, List.forall_mem_cons.2 ⟨subd8_7_264, List.forall_mem_cons.2 ⟨subd8_7_265, List.forall_mem_cons.2 ⟨subd8_7_266, List.forall_mem_cons.2 ⟨subd8_7_267, List.forall_mem_cons.2 ⟨subd8_7_268, List.forall_mem_cons.2 ⟨subd8_7_269, List.forall_mem_cons.2 ⟨subd8_7_270, List.forall_mem_cons.2 ⟨subd8_7_271, List.forall_mem_cons.2 ⟨subd8_7_272, List.forall_mem_cons.2 ⟨subd8_7_273, List.forall_mem_cons.2 ⟨subd8_7_274, List.forall_mem_cons.2 ⟨subd8_7_275, List.forall_mem_cons.2 ⟨subd8_7_276, List.forall_mem_cons.2 ⟨subd8_7_277, List.forall_mem_cons.2 ⟨subd8_7_278, List.forall_mem_cons.2 ⟨subd8_7_279, List.forall_mem_cons.2 ⟨subd8_7_280, List.forall_mem_cons.2 ⟨subd8_7_281, List.forall_mem_cons.2 ⟨subd8_7_282, List.forall_mem_cons.2 ⟨subd8_7_283, List.forall_mem_cons.2 ⟨subd8_7_284, List.forall_mem_cons.2 ⟨subd8_7_285, List.forall_mem_cons.2 ⟨subd8_7_286, List.forall_mem_cons.2 ⟨subd8_7_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_7_288 : subd8_7 [4, 4] = true := by decide +kernel
theorem sbd8_7_9 : ∀ q ∈ blkd8_7_9, subd8_7 q = true := by
  unfold blkd8_7_9
  exact List.forall_mem_cons.2 ⟨subd8_7_288, List.forall_mem_nil _⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [-3] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [-2, -3] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [-2, -2] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [-2, -1] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [-2, 0] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [-2, 1] = true := by decide +kernel
theorem subd9_0_6 : subd9_0 [-2, 2] = true := by decide +kernel
theorem subd9_0_7 : subd9_0 [-2, 3] = true := by decide +kernel
theorem subd9_0_8 : subd9_0 [-1, -4] = true := by decide +kernel
theorem subd9_0_9 : subd9_0 [-1, -3] = true := by decide +kernel
theorem subd9_0_10 : subd9_0 [-1, -2] = true := by decide +kernel
theorem subd9_0_11 : subd9_0 [-1, -1] = true := by decide +kernel
theorem subd9_0_12 : subd9_0 [-1, 0] = true := by decide +kernel
theorem subd9_0_13 : subd9_0 [-1, 1] = true := by decide +kernel
theorem subd9_0_14 : subd9_0 [-1, 2] = true := by decide +kernel
theorem subd9_0_15 : subd9_0 [-1, 3] = true := by decide +kernel
theorem subd9_0_16 : subd9_0 [0, -4] = true := by decide +kernel
theorem subd9_0_17 : subd9_0 [0, -3] = true := by decide +kernel
theorem subd9_0_18 : subd9_0 [0, -2] = true := by decide +kernel
theorem subd9_0_19 : subd9_0 [0, -1] = true := by decide +kernel
theorem subd9_0_20 : subd9_0 [0, 0] = true := by decide +kernel
theorem subd9_0_21 : subd9_0 [0, 1] = true := by decide +kernel
theorem subd9_0_22 : subd9_0 [0, 2] = true := by decide +kernel
theorem subd9_0_23 : subd9_0 [0, 3] = true := by decide +kernel
theorem subd9_0_24 : subd9_0 [1, -4] = true := by decide +kernel
theorem subd9_0_25 : subd9_0 [1, -3] = true := by decide +kernel
theorem subd9_0_26 : subd9_0 [1, -2] = true := by decide +kernel
theorem subd9_0_27 : subd9_0 [1, -1] = true := by decide +kernel
theorem subd9_0_28 : subd9_0 [1, 0] = true := by decide +kernel
theorem subd9_0_29 : subd9_0 [1, 1] = true := by decide +kernel
theorem subd9_0_30 : subd9_0 [1, 2] = true := by decide +kernel
theorem subd9_0_31 : subd9_0 [1, 3] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_cons.2 ⟨subd9_0_6, List.forall_mem_cons.2 ⟨subd9_0_7, List.forall_mem_cons.2 ⟨subd9_0_8, List.forall_mem_cons.2 ⟨subd9_0_9, List.forall_mem_cons.2 ⟨subd9_0_10, List.forall_mem_cons.2 ⟨subd9_0_11, List.forall_mem_cons.2 ⟨subd9_0_12, List.forall_mem_cons.2 ⟨subd9_0_13, List.forall_mem_cons.2 ⟨subd9_0_14, List.forall_mem_cons.2 ⟨subd9_0_15, List.forall_mem_cons.2 ⟨subd9_0_16, List.forall_mem_cons.2 ⟨subd9_0_17, List.forall_mem_cons.2 ⟨subd9_0_18, List.forall_mem_cons.2 ⟨subd9_0_19, List.forall_mem_cons.2 ⟨subd9_0_20, List.forall_mem_cons.2 ⟨subd9_0_21, List.forall_mem_cons.2 ⟨subd9_0_22, List.forall_mem_cons.2 ⟨subd9_0_23, List.forall_mem_cons.2 ⟨subd9_0_24, List.forall_mem_cons.2 ⟨subd9_0_25, List.forall_mem_cons.2 ⟨subd9_0_26, List.forall_mem_cons.2 ⟨subd9_0_27, List.forall_mem_cons.2 ⟨subd9_0_28, List.forall_mem_cons.2 ⟨subd9_0_29, List.forall_mem_cons.2 ⟨subd9_0_30, List.forall_mem_cons.2 ⟨subd9_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_32 : subd9_0 [2, -4] = true := by decide +kernel
theorem subd9_0_33 : subd9_0 [2, -3] = true := by decide +kernel
theorem subd9_0_34 : subd9_0 [2, -2] = true := by decide +kernel
theorem subd9_0_35 : subd9_0 [2, -1] = true := by decide +kernel
theorem subd9_0_36 : subd9_0 [2, 0] = true := by decide +kernel
theorem subd9_0_37 : subd9_0 [2, 1] = true := by decide +kernel
theorem subd9_0_38 : subd9_0 [2, 2] = true := by decide +kernel
theorem subd9_0_39 : subd9_0 [3] = true := by decide +kernel
theorem sbd9_0_1 : ∀ q ∈ blkd9_0_1, subd9_0 q = true := by
  unfold blkd9_0_1
  exact List.forall_mem_cons.2 ⟨subd9_0_32, List.forall_mem_cons.2 ⟨subd9_0_33, List.forall_mem_cons.2 ⟨subd9_0_34, List.forall_mem_cons.2 ⟨subd9_0_35, List.forall_mem_cons.2 ⟨subd9_0_36, List.forall_mem_cons.2 ⟨subd9_0_37, List.forall_mem_cons.2 ⟨subd9_0_38, List.forall_mem_cons.2 ⟨subd9_0_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [-6, -5] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-6, -4] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [-6, -3] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [-6, -2] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [-6, -1] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [-6, 0] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [-6, 1] = true := by decide +kernel
theorem subd9_1_7 : subd9_1 [-6, 2] = true := by decide +kernel
theorem subd9_1_8 : subd9_1 [-6, 3] = true := by decide +kernel
theorem subd9_1_9 : subd9_1 [-5, -6] = true := by decide +kernel
theorem subd9_1_10 : subd9_1 [-5, -5] = true := by decide +kernel
theorem subd9_1_11 : subd9_1 [-5, -4] = true := by decide +kernel
theorem subd9_1_12 : subd9_1 [-5, -3] = true := by decide +kernel
theorem subd9_1_13 : subd9_1 [-5, -2] = true := by decide +kernel
theorem subd9_1_14 : subd9_1 [-5, -1] = true := by decide +kernel
theorem subd9_1_15 : subd9_1 [-5, 0] = true := by decide +kernel
theorem subd9_1_16 : subd9_1 [-5, 1] = true := by decide +kernel
theorem subd9_1_17 : subd9_1 [-5, 2] = true := by decide +kernel
theorem subd9_1_18 : subd9_1 [-5, 3] = true := by decide +kernel
theorem subd9_1_19 : subd9_1 [-5, 4] = true := by decide +kernel
theorem subd9_1_20 : subd9_1 [-4, -7] = true := by decide +kernel
theorem subd9_1_21 : subd9_1 [-4, -6] = true := by decide +kernel
theorem subd9_1_22 : subd9_1 [-4, -5] = true := by decide +kernel
theorem subd9_1_23 : subd9_1 [-4, -4] = true := by decide +kernel
theorem subd9_1_24 : subd9_1 [-4, -3] = true := by decide +kernel
theorem subd9_1_25 : subd9_1 [-4, -2] = true := by decide +kernel
theorem subd9_1_26 : subd9_1 [-4, -1] = true := by decide +kernel
theorem subd9_1_27 : subd9_1 [-4, 0] = true := by decide +kernel
theorem subd9_1_28 : subd9_1 [-4, 1] = true := by decide +kernel
theorem subd9_1_29 : subd9_1 [-4, 2] = true := by decide +kernel
theorem subd9_1_30 : subd9_1 [-4, 3] = true := by decide +kernel
theorem subd9_1_31 : subd9_1 [-4, 4] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_cons.2 ⟨subd9_1_7, List.forall_mem_cons.2 ⟨subd9_1_8, List.forall_mem_cons.2 ⟨subd9_1_9, List.forall_mem_cons.2 ⟨subd9_1_10, List.forall_mem_cons.2 ⟨subd9_1_11, List.forall_mem_cons.2 ⟨subd9_1_12, List.forall_mem_cons.2 ⟨subd9_1_13, List.forall_mem_cons.2 ⟨subd9_1_14, List.forall_mem_cons.2 ⟨subd9_1_15, List.forall_mem_cons.2 ⟨subd9_1_16, List.forall_mem_cons.2 ⟨subd9_1_17, List.forall_mem_cons.2 ⟨subd9_1_18, List.forall_mem_cons.2 ⟨subd9_1_19, List.forall_mem_cons.2 ⟨subd9_1_20, List.forall_mem_cons.2 ⟨subd9_1_21, List.forall_mem_cons.2 ⟨subd9_1_22, List.forall_mem_cons.2 ⟨subd9_1_23, List.forall_mem_cons.2 ⟨subd9_1_24, List.forall_mem_cons.2 ⟨subd9_1_25, List.forall_mem_cons.2 ⟨subd9_1_26, List.forall_mem_cons.2 ⟨subd9_1_27, List.forall_mem_cons.2 ⟨subd9_1_28, List.forall_mem_cons.2 ⟨subd9_1_29, List.forall_mem_cons.2 ⟨subd9_1_30, List.forall_mem_cons.2 ⟨subd9_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_32 : subd9_1 [-4, 5] = true := by decide +kernel
theorem subd9_1_33 : subd9_1 [-3, -7] = true := by decide +kernel
theorem subd9_1_34 : subd9_1 [-3, -6] = true := by decide +kernel
theorem subd9_1_35 : subd9_1 [-3, -5] = true := by decide +kernel
theorem subd9_1_36 : subd9_1 [-3, -4] = true := by decide +kernel
theorem subd9_1_37 : subd9_1 [-3, -3] = true := by decide +kernel
theorem subd9_1_38 : subd9_1 [-3, -2, -6] = true := by decide +kernel
theorem subd9_1_39 : subd9_1 [-3, -2, -5] = true := by decide +kernel
theorem subd9_1_40 : subd9_1 [-3, -2, -4] = true := by decide +kernel
theorem subd9_1_41 : subd9_1 [-3, -2, -3] = true := by decide +kernel
theorem subd9_1_42 : subd9_1 [-3, -2, -2] = true := by decide +kernel
theorem subd9_1_43 : subd9_1 [-3, -2, -1] = true := by decide +kernel
theorem subd9_1_44 : subd9_1 [-3, -2, 0] = true := by decide +kernel
theorem subd9_1_45 : subd9_1 [-3, -2, 1] = true := by decide +kernel
theorem subd9_1_46 : subd9_1 [-3, -2, 2] = true := by decide +kernel
theorem subd9_1_47 : subd9_1 [-3, -2, 3] = true := by decide +kernel
theorem subd9_1_48 : subd9_1 [-3, -2, 4] = true := by decide +kernel
theorem subd9_1_49 : subd9_1 [-3, -2, 5] = true := by decide +kernel
theorem subd9_1_50 : subd9_1 [-3, -2, 6] = true := by decide +kernel
theorem subd9_1_51 : subd9_1 [-3, -2, 7] = true := by decide +kernel
theorem subd9_1_52 : subd9_1 [-3, -1, -7] = true := by decide +kernel
theorem subd9_1_53 : subd9_1 [-3, -1, -6] = true := by decide +kernel
theorem subd9_1_54 : subd9_1 [-3, -1, -5] = true := by decide +kernel
theorem subd9_1_55 : subd9_1 [-3, -1, -4] = true := by decide +kernel
theorem subd9_1_56 : subd9_1 [-3, -1, -3] = true := by decide +kernel
theorem subd9_1_57 : subd9_1 [-3, -1, -2] = true := by decide +kernel
theorem subd9_1_58 : subd9_1 [-3, -1, -1] = true := by decide +kernel
theorem subd9_1_59 : subd9_1 [-3, -1, 0] = true := by decide +kernel
theorem subd9_1_60 : subd9_1 [-3, -1, 1] = true := by decide +kernel
theorem subd9_1_61 : subd9_1 [-3, -1, 2] = true := by decide +kernel
theorem subd9_1_62 : subd9_1 [-3, -1, 3] = true := by decide +kernel
theorem subd9_1_63 : subd9_1 [-3, -1, 4] = true := by decide +kernel
theorem sbd9_1_1 : ∀ q ∈ blkd9_1_1, subd9_1 q = true := by
  unfold blkd9_1_1
  exact List.forall_mem_cons.2 ⟨subd9_1_32, List.forall_mem_cons.2 ⟨subd9_1_33, List.forall_mem_cons.2 ⟨subd9_1_34, List.forall_mem_cons.2 ⟨subd9_1_35, List.forall_mem_cons.2 ⟨subd9_1_36, List.forall_mem_cons.2 ⟨subd9_1_37, List.forall_mem_cons.2 ⟨subd9_1_38, List.forall_mem_cons.2 ⟨subd9_1_39, List.forall_mem_cons.2 ⟨subd9_1_40, List.forall_mem_cons.2 ⟨subd9_1_41, List.forall_mem_cons.2 ⟨subd9_1_42, List.forall_mem_cons.2 ⟨subd9_1_43, List.forall_mem_cons.2 ⟨subd9_1_44, List.forall_mem_cons.2 ⟨subd9_1_45, List.forall_mem_cons.2 ⟨subd9_1_46, List.forall_mem_cons.2 ⟨subd9_1_47, List.forall_mem_cons.2 ⟨subd9_1_48, List.forall_mem_cons.2 ⟨subd9_1_49, List.forall_mem_cons.2 ⟨subd9_1_50, List.forall_mem_cons.2 ⟨subd9_1_51, List.forall_mem_cons.2 ⟨subd9_1_52, List.forall_mem_cons.2 ⟨subd9_1_53, List.forall_mem_cons.2 ⟨subd9_1_54, List.forall_mem_cons.2 ⟨subd9_1_55, List.forall_mem_cons.2 ⟨subd9_1_56, List.forall_mem_cons.2 ⟨subd9_1_57, List.forall_mem_cons.2 ⟨subd9_1_58, List.forall_mem_cons.2 ⟨subd9_1_59, List.forall_mem_cons.2 ⟨subd9_1_60, List.forall_mem_cons.2 ⟨subd9_1_61, List.forall_mem_cons.2 ⟨subd9_1_62, List.forall_mem_cons.2 ⟨subd9_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
