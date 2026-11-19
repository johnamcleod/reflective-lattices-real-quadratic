import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_3_256 : subd11_3 [2, 0, 2] = true := by decide +kernel
theorem subd11_3_257 : subd11_3 [2, 0, 3] = true := by decide +kernel
theorem subd11_3_258 : subd11_3 [2, 0, 4] = true := by decide +kernel
theorem subd11_3_259 : subd11_3 [2, 0, 5] = true := by decide +kernel
theorem subd11_3_260 : subd11_3 [2, 0, 6] = true := by decide +kernel
theorem subd11_3_261 : subd11_3 [2, 1] = true := by decide +kernel
theorem subd11_3_262 : subd11_3 [2, 2] = true := by decide +kernel
theorem subd11_3_263 : subd11_3 [2, 3] = true := by decide +kernel
theorem subd11_3_264 : subd11_3 [2, 4] = true := by decide +kernel
theorem subd11_3_265 : subd11_3 [2, 5] = true := by decide +kernel
theorem subd11_3_266 : subd11_3 [3, -5] = true := by decide +kernel
theorem subd11_3_267 : subd11_3 [3, -4] = true := by decide +kernel
theorem subd11_3_268 : subd11_3 [3, -3] = true := by decide +kernel
theorem subd11_3_269 : subd11_3 [3, -2] = true := by decide +kernel
theorem subd11_3_270 : subd11_3 [3, -1] = true := by decide +kernel
theorem subd11_3_271 : subd11_3 [3, 0] = true := by decide +kernel
theorem subd11_3_272 : subd11_3 [3, 1] = true := by decide +kernel
theorem subd11_3_273 : subd11_3 [3, 2] = true := by decide +kernel
theorem subd11_3_274 : subd11_3 [3, 3] = true := by decide +kernel
theorem subd11_3_275 : subd11_3 [3, 4] = true := by decide +kernel
theorem subd11_3_276 : subd11_3 [3, 5] = true := by decide +kernel
theorem subd11_3_277 : subd11_3 [4, -4] = true := by decide +kernel
theorem subd11_3_278 : subd11_3 [4, -3] = true := by decide +kernel
theorem subd11_3_279 : subd11_3 [4, -2] = true := by decide +kernel
theorem subd11_3_280 : subd11_3 [4, -1] = true := by decide +kernel
theorem subd11_3_281 : subd11_3 [4, 0] = true := by decide +kernel
theorem subd11_3_282 : subd11_3 [4, 1] = true := by decide +kernel
theorem subd11_3_283 : subd11_3 [4, 2] = true := by decide +kernel
theorem subd11_3_284 : subd11_3 [4, 3] = true := by decide +kernel
theorem subd11_3_285 : subd11_3 [4, 4] = true := by decide +kernel
theorem subd11_3_286 : subd11_3 [5, -3] = true := by decide +kernel
theorem subd11_3_287 : subd11_3 [5, -2] = true := by decide +kernel
theorem sbd11_3_8 : ∀ q ∈ blkd11_3_8, subd11_3 q = true := by
  unfold blkd11_3_8
  exact List.forall_mem_cons.2 ⟨subd11_3_256, List.forall_mem_cons.2 ⟨subd11_3_257, List.forall_mem_cons.2 ⟨subd11_3_258, List.forall_mem_cons.2 ⟨subd11_3_259, List.forall_mem_cons.2 ⟨subd11_3_260, List.forall_mem_cons.2 ⟨subd11_3_261, List.forall_mem_cons.2 ⟨subd11_3_262, List.forall_mem_cons.2 ⟨subd11_3_263, List.forall_mem_cons.2 ⟨subd11_3_264, List.forall_mem_cons.2 ⟨subd11_3_265, List.forall_mem_cons.2 ⟨subd11_3_266, List.forall_mem_cons.2 ⟨subd11_3_267, List.forall_mem_cons.2 ⟨subd11_3_268, List.forall_mem_cons.2 ⟨subd11_3_269, List.forall_mem_cons.2 ⟨subd11_3_270, List.forall_mem_cons.2 ⟨subd11_3_271, List.forall_mem_cons.2 ⟨subd11_3_272, List.forall_mem_cons.2 ⟨subd11_3_273, List.forall_mem_cons.2 ⟨subd11_3_274, List.forall_mem_cons.2 ⟨subd11_3_275, List.forall_mem_cons.2 ⟨subd11_3_276, List.forall_mem_cons.2 ⟨subd11_3_277, List.forall_mem_cons.2 ⟨subd11_3_278, List.forall_mem_cons.2 ⟨subd11_3_279, List.forall_mem_cons.2 ⟨subd11_3_280, List.forall_mem_cons.2 ⟨subd11_3_281, List.forall_mem_cons.2 ⟨subd11_3_282, List.forall_mem_cons.2 ⟨subd11_3_283, List.forall_mem_cons.2 ⟨subd11_3_284, List.forall_mem_cons.2 ⟨subd11_3_285, List.forall_mem_cons.2 ⟨subd11_3_286, List.forall_mem_cons.2 ⟨subd11_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_288 : subd11_3 [5, -1] = true := by decide +kernel
theorem subd11_3_289 : subd11_3 [5, 0] = true := by decide +kernel
theorem subd11_3_290 : subd11_3 [5, 1] = true := by decide +kernel
theorem subd11_3_291 : subd11_3 [5, 2] = true := by decide +kernel
theorem subd11_3_292 : subd11_3 [5, 3] = true := by decide +kernel
theorem sbd11_3_9 : ∀ q ∈ blkd11_3_9, subd11_3 q = true := by
  unfold blkd11_3_9
  exact List.forall_mem_cons.2 ⟨subd11_3_288, List.forall_mem_cons.2 ⟨subd11_3_289, List.forall_mem_cons.2 ⟨subd11_3_290, List.forall_mem_cons.2 ⟨subd11_3_291, List.forall_mem_cons.2 ⟨subd11_3_292, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_4 : ldCheck G d11_4.U d11_4.ms ldd11_4 = true := by decide +kernel
theorem pre_okd11_4 : subPre G cell11 d11_4 = true := by decide +kernel
theorem subd11_4_0 : subd11_4 [-4] = true := by decide +kernel
theorem subd11_4_1 : subd11_4 [-3, -3] = true := by decide +kernel
theorem subd11_4_2 : subd11_4 [-3, -2] = true := by decide +kernel
theorem subd11_4_3 : subd11_4 [-3, -1] = true := by decide +kernel
theorem subd11_4_4 : subd11_4 [-3, 0] = true := by decide +kernel
theorem subd11_4_5 : subd11_4 [-3, 1] = true := by decide +kernel
theorem subd11_4_6 : subd11_4 [-3, 2] = true := by decide +kernel
theorem subd11_4_7 : subd11_4 [-2, -4] = true := by decide +kernel
theorem subd11_4_8 : subd11_4 [-2, -3] = true := by decide +kernel
theorem subd11_4_9 : subd11_4 [-2, -2] = true := by decide +kernel
theorem subd11_4_10 : subd11_4 [-2, -1] = true := by decide +kernel
theorem subd11_4_11 : subd11_4 [-2, 0] = true := by decide +kernel
theorem subd11_4_12 : subd11_4 [-2, 1] = true := by decide +kernel
theorem subd11_4_13 : subd11_4 [-2, 2] = true := by decide +kernel
theorem subd11_4_14 : subd11_4 [-2, 3] = true := by decide +kernel
theorem subd11_4_15 : subd11_4 [-1, -4] = true := by decide +kernel
theorem subd11_4_16 : subd11_4 [-1, -3] = true := by decide +kernel
theorem subd11_4_17 : subd11_4 [-1, -2] = true := by decide +kernel
theorem subd11_4_18 : subd11_4 [-1, -1, -6] = true := by decide +kernel
theorem subd11_4_19 : subd11_4 [-1, -1, -5] = true := by decide +kernel
theorem subd11_4_20 : subd11_4 [-1, -1, -4] = true := by decide +kernel
theorem subd11_4_21 : subd11_4 [-1, -1, -3] = true := by decide +kernel
theorem subd11_4_22 : subd11_4 [-1, -1, -2] = true := by decide +kernel
theorem subd11_4_23 : subd11_4 [-1, -1, -1] = true := by decide +kernel
theorem subd11_4_24 : subd11_4 [-1, -1, 0] = true := by decide +kernel
theorem subd11_4_25 : subd11_4 [-1, -1, 1] = true := by decide +kernel
theorem subd11_4_26 : subd11_4 [-1, -1, 2] = true := by decide +kernel
theorem subd11_4_27 : subd11_4 [-1, -1, 3] = true := by decide +kernel
theorem subd11_4_28 : subd11_4 [-1, -1, 4] = true := by decide +kernel
theorem subd11_4_29 : subd11_4 [-1, -1, 5] = true := by decide +kernel
theorem subd11_4_30 : subd11_4 [-1, -1, 6] = true := by decide +kernel
theorem subd11_4_31 : subd11_4 [-1, -1, 7] = true := by decide +kernel
theorem sbd11_4_0 : ∀ q ∈ blkd11_4_0, subd11_4 q = true := by
  unfold blkd11_4_0
  exact List.forall_mem_cons.2 ⟨subd11_4_0, List.forall_mem_cons.2 ⟨subd11_4_1, List.forall_mem_cons.2 ⟨subd11_4_2, List.forall_mem_cons.2 ⟨subd11_4_3, List.forall_mem_cons.2 ⟨subd11_4_4, List.forall_mem_cons.2 ⟨subd11_4_5, List.forall_mem_cons.2 ⟨subd11_4_6, List.forall_mem_cons.2 ⟨subd11_4_7, List.forall_mem_cons.2 ⟨subd11_4_8, List.forall_mem_cons.2 ⟨subd11_4_9, List.forall_mem_cons.2 ⟨subd11_4_10, List.forall_mem_cons.2 ⟨subd11_4_11, List.forall_mem_cons.2 ⟨subd11_4_12, List.forall_mem_cons.2 ⟨subd11_4_13, List.forall_mem_cons.2 ⟨subd11_4_14, List.forall_mem_cons.2 ⟨subd11_4_15, List.forall_mem_cons.2 ⟨subd11_4_16, List.forall_mem_cons.2 ⟨subd11_4_17, List.forall_mem_cons.2 ⟨subd11_4_18, List.forall_mem_cons.2 ⟨subd11_4_19, List.forall_mem_cons.2 ⟨subd11_4_20, List.forall_mem_cons.2 ⟨subd11_4_21, List.forall_mem_cons.2 ⟨subd11_4_22, List.forall_mem_cons.2 ⟨subd11_4_23, List.forall_mem_cons.2 ⟨subd11_4_24, List.forall_mem_cons.2 ⟨subd11_4_25, List.forall_mem_cons.2 ⟨subd11_4_26, List.forall_mem_cons.2 ⟨subd11_4_27, List.forall_mem_cons.2 ⟨subd11_4_28, List.forall_mem_cons.2 ⟨subd11_4_29, List.forall_mem_cons.2 ⟨subd11_4_30, List.forall_mem_cons.2 ⟨subd11_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_4_32 : subd11_4 [-1, 0, -7] = true := by decide +kernel
theorem subd11_4_33 : subd11_4 [-1, 0, -6] = true := by decide +kernel
theorem subd11_4_34 : subd11_4 [-1, 0, -5] = true := by decide +kernel
theorem subd11_4_35 : subd11_4 [-1, 0, -4] = true := by decide +kernel
theorem subd11_4_36 : subd11_4 [-1, 0, -3] = true := by decide +kernel
theorem subd11_4_37 : subd11_4 [-1, 0, -2] = true := by decide +kernel
theorem subd11_4_38 : subd11_4 [-1, 0, -1] = true := by decide +kernel
theorem subd11_4_39 : subd11_4 [-1, 0, 0] = true := by decide +kernel
theorem subd11_4_40 : subd11_4 [-1, 0, 1] = true := by decide +kernel
theorem subd11_4_41 : subd11_4 [-1, 0, 2] = true := by decide +kernel
theorem subd11_4_42 : subd11_4 [-1, 0, 3] = true := by decide +kernel
theorem subd11_4_43 : subd11_4 [-1, 0, 4] = true := by decide +kernel
theorem subd11_4_44 : subd11_4 [-1, 0, 5] = true := by decide +kernel
theorem subd11_4_45 : subd11_4 [-1, 0, 6] = true := by decide +kernel
theorem subd11_4_46 : subd11_4 [-1, 0, 7] = true := by decide +kernel
theorem subd11_4_47 : subd11_4 [-1, 1, -7] = true := by decide +kernel
theorem subd11_4_48 : subd11_4 [-1, 1, -6] = true := by decide +kernel
theorem subd11_4_49 : subd11_4 [-1, 1, -5] = true := by decide +kernel
theorem subd11_4_50 : subd11_4 [-1, 1, -4] = true := by decide +kernel
theorem subd11_4_51 : subd11_4 [-1, 1, -3] = true := by decide +kernel
theorem subd11_4_52 : subd11_4 [-1, 1, -2] = true := by decide +kernel
theorem subd11_4_53 : subd11_4 [-1, 1, -1] = true := by decide +kernel
theorem subd11_4_54 : subd11_4 [-1, 1, 0] = true := by decide +kernel
theorem subd11_4_55 : subd11_4 [-1, 1, 1] = true := by decide +kernel
theorem subd11_4_56 : subd11_4 [-1, 1, 2] = true := by decide +kernel
theorem subd11_4_57 : subd11_4 [-1, 1, 3] = true := by decide +kernel
theorem subd11_4_58 : subd11_4 [-1, 1, 4] = true := by decide +kernel
theorem subd11_4_59 : subd11_4 [-1, 1, 5] = true := by decide +kernel
theorem subd11_4_60 : subd11_4 [-1, 1, 6] = true := by decide +kernel
theorem subd11_4_61 : subd11_4 [-1, 2] = true := by decide +kernel
theorem subd11_4_62 : subd11_4 [-1, 3] = true := by decide +kernel
theorem subd11_4_63 : subd11_4 [0, -4] = true := by decide +kernel
theorem sbd11_4_1 : ∀ q ∈ blkd11_4_1, subd11_4 q = true := by
  unfold blkd11_4_1
  exact List.forall_mem_cons.2 ⟨subd11_4_32, List.forall_mem_cons.2 ⟨subd11_4_33, List.forall_mem_cons.2 ⟨subd11_4_34, List.forall_mem_cons.2 ⟨subd11_4_35, List.forall_mem_cons.2 ⟨subd11_4_36, List.forall_mem_cons.2 ⟨subd11_4_37, List.forall_mem_cons.2 ⟨subd11_4_38, List.forall_mem_cons.2 ⟨subd11_4_39, List.forall_mem_cons.2 ⟨subd11_4_40, List.forall_mem_cons.2 ⟨subd11_4_41, List.forall_mem_cons.2 ⟨subd11_4_42, List.forall_mem_cons.2 ⟨subd11_4_43, List.forall_mem_cons.2 ⟨subd11_4_44, List.forall_mem_cons.2 ⟨subd11_4_45, List.forall_mem_cons.2 ⟨subd11_4_46, List.forall_mem_cons.2 ⟨subd11_4_47, List.forall_mem_cons.2 ⟨subd11_4_48, List.forall_mem_cons.2 ⟨subd11_4_49, List.forall_mem_cons.2 ⟨subd11_4_50, List.forall_mem_cons.2 ⟨subd11_4_51, List.forall_mem_cons.2 ⟨subd11_4_52, List.forall_mem_cons.2 ⟨subd11_4_53, List.forall_mem_cons.2 ⟨subd11_4_54, List.forall_mem_cons.2 ⟨subd11_4_55, List.forall_mem_cons.2 ⟨subd11_4_56, List.forall_mem_cons.2 ⟨subd11_4_57, List.forall_mem_cons.2 ⟨subd11_4_58, List.forall_mem_cons.2 ⟨subd11_4_59, List.forall_mem_cons.2 ⟨subd11_4_60, List.forall_mem_cons.2 ⟨subd11_4_61, List.forall_mem_cons.2 ⟨subd11_4_62, List.forall_mem_cons.2 ⟨subd11_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_4_64 : subd11_4 [0, -3] = true := by decide +kernel
theorem subd11_4_65 : subd11_4 [0, -2] = true := by decide +kernel
theorem subd11_4_66 : subd11_4 [0, -1, -7] = true := by decide +kernel
theorem subd11_4_67 : subd11_4 [0, -1, -6] = true := by decide +kernel
theorem subd11_4_68 : subd11_4 [0, -1, -5] = true := by decide +kernel
theorem subd11_4_69 : subd11_4 [0, -1, -4] = true := by decide +kernel
theorem subd11_4_70 : subd11_4 [0, -1, -3] = true := by decide +kernel
theorem subd11_4_71 : subd11_4 [0, -1, -2] = true := by decide +kernel
theorem subd11_4_72 : subd11_4 [0, -1, -1] = true := by decide +kernel
theorem subd11_4_73 : subd11_4 [0, -1, 0] = true := by decide +kernel
theorem subd11_4_74 : subd11_4 [0, -1, 1] = true := by decide +kernel
theorem subd11_4_75 : subd11_4 [0, -1, 2] = true := by decide +kernel
theorem subd11_4_76 : subd11_4 [0, -1, 3] = true := by decide +kernel
theorem subd11_4_77 : subd11_4 [0, -1, 4] = true := by decide +kernel
theorem subd11_4_78 : subd11_4 [0, -1, 5] = true := by decide +kernel
theorem subd11_4_79 : subd11_4 [0, -1, 6] = true := by decide +kernel
theorem subd11_4_80 : subd11_4 [0, -1, 7] = true := by decide +kernel
theorem subd11_4_81 : subd11_4 [0, 0, -8] = true := by decide +kernel
theorem subd11_4_82 : subd11_4 [0, 0, -7] = true := by decide +kernel
theorem subd11_4_83 : subd11_4 [0, 0, -6] = true := by decide +kernel
theorem subd11_4_84 : subd11_4 [0, 0, -5] = true := by decide +kernel
theorem subd11_4_85 : subd11_4 [0, 0, -4] = true := by decide +kernel
theorem subd11_4_86 : subd11_4 [0, 0, -3] = true := by decide +kernel
theorem subd11_4_87 : subd11_4 [0, 0, -2] = true := by decide +kernel
theorem subd11_4_88 : subd11_4 [0, 0, -1] = true := by decide +kernel
theorem subd11_4_89 : subd11_4 [0, 0, 0] = true := by decide +kernel
theorem subd11_4_90 : subd11_4 [0, 0, 1] = true := by decide +kernel
theorem subd11_4_91 : subd11_4 [0, 0, 2] = true := by decide +kernel
theorem subd11_4_92 : subd11_4 [0, 0, 3] = true := by decide +kernel
theorem subd11_4_93 : subd11_4 [0, 0, 4] = true := by decide +kernel
theorem subd11_4_94 : subd11_4 [0, 0, 5] = true := by decide +kernel
theorem subd11_4_95 : subd11_4 [0, 0, 6] = true := by decide +kernel
theorem sbd11_4_2 : ∀ q ∈ blkd11_4_2, subd11_4 q = true := by
  unfold blkd11_4_2
  exact List.forall_mem_cons.2 ⟨subd11_4_64, List.forall_mem_cons.2 ⟨subd11_4_65, List.forall_mem_cons.2 ⟨subd11_4_66, List.forall_mem_cons.2 ⟨subd11_4_67, List.forall_mem_cons.2 ⟨subd11_4_68, List.forall_mem_cons.2 ⟨subd11_4_69, List.forall_mem_cons.2 ⟨subd11_4_70, List.forall_mem_cons.2 ⟨subd11_4_71, List.forall_mem_cons.2 ⟨subd11_4_72, List.forall_mem_cons.2 ⟨subd11_4_73, List.forall_mem_cons.2 ⟨subd11_4_74, List.forall_mem_cons.2 ⟨subd11_4_75, List.forall_mem_cons.2 ⟨subd11_4_76, List.forall_mem_cons.2 ⟨subd11_4_77, List.forall_mem_cons.2 ⟨subd11_4_78, List.forall_mem_cons.2 ⟨subd11_4_79, List.forall_mem_cons.2 ⟨subd11_4_80, List.forall_mem_cons.2 ⟨subd11_4_81, List.forall_mem_cons.2 ⟨subd11_4_82, List.forall_mem_cons.2 ⟨subd11_4_83, List.forall_mem_cons.2 ⟨subd11_4_84, List.forall_mem_cons.2 ⟨subd11_4_85, List.forall_mem_cons.2 ⟨subd11_4_86, List.forall_mem_cons.2 ⟨subd11_4_87, List.forall_mem_cons.2 ⟨subd11_4_88, List.forall_mem_cons.2 ⟨subd11_4_89, List.forall_mem_cons.2 ⟨subd11_4_90, List.forall_mem_cons.2 ⟨subd11_4_91, List.forall_mem_cons.2 ⟨subd11_4_92, List.forall_mem_cons.2 ⟨subd11_4_93, List.forall_mem_cons.2 ⟨subd11_4_94, List.forall_mem_cons.2 ⟨subd11_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_4_96 : subd11_4 [0, 0, 7] = true := by decide +kernel
theorem subd11_4_97 : subd11_4 [0, 1, -8] = true := by decide +kernel
theorem subd11_4_98 : subd11_4 [0, 1, -7] = true := by decide +kernel
theorem subd11_4_99 : subd11_4 [0, 1, -6] = true := by decide +kernel
theorem subd11_4_100 : subd11_4 [0, 1, -5] = true := by decide +kernel
theorem subd11_4_101 : subd11_4 [0, 1, -4] = true := by decide +kernel
theorem subd11_4_102 : subd11_4 [0, 1, -3] = true := by decide +kernel
theorem subd11_4_103 : subd11_4 [0, 1, -2] = true := by decide +kernel
theorem subd11_4_104 : subd11_4 [0, 1, -1] = true := by decide +kernel
theorem subd11_4_105 : subd11_4 [0, 1, 0] = true := by decide +kernel
theorem subd11_4_106 : subd11_4 [0, 1, 1] = true := by decide +kernel
theorem subd11_4_107 : subd11_4 [0, 1, 2] = true := by decide +kernel
theorem subd11_4_108 : subd11_4 [0, 1, 3] = true := by decide +kernel
theorem subd11_4_109 : subd11_4 [0, 1, 4] = true := by decide +kernel
theorem subd11_4_110 : subd11_4 [0, 1, 5] = true := by decide +kernel
theorem subd11_4_111 : subd11_4 [0, 1, 6] = true := by decide +kernel
theorem subd11_4_112 : subd11_4 [0, 2] = true := by decide +kernel
theorem subd11_4_113 : subd11_4 [0, 3] = true := by decide +kernel
theorem subd11_4_114 : subd11_4 [1, -4] = true := by decide +kernel
theorem subd11_4_115 : subd11_4 [1, -3] = true := by decide +kernel
theorem subd11_4_116 : subd11_4 [1, -2] = true := by decide +kernel
theorem subd11_4_117 : subd11_4 [1, -1, -7] = true := by decide +kernel
theorem subd11_4_118 : subd11_4 [1, -1, -6] = true := by decide +kernel
theorem subd11_4_119 : subd11_4 [1, -1, -5] = true := by decide +kernel
theorem subd11_4_120 : subd11_4 [1, -1, -4] = true := by decide +kernel
theorem subd11_4_121 : subd11_4 [1, -1, -3] = true := by decide +kernel
theorem subd11_4_122 : subd11_4 [1, -1, -2] = true := by decide +kernel
theorem subd11_4_123 : subd11_4 [1, -1, -1] = true := by decide +kernel
theorem subd11_4_124 : subd11_4 [1, -1, 0] = true := by decide +kernel
theorem subd11_4_125 : subd11_4 [1, -1, 1] = true := by decide +kernel
theorem subd11_4_126 : subd11_4 [1, -1, 2] = true := by decide +kernel
theorem subd11_4_127 : subd11_4 [1, -1, 3] = true := by decide +kernel
theorem sbd11_4_3 : ∀ q ∈ blkd11_4_3, subd11_4 q = true := by
  unfold blkd11_4_3
  exact List.forall_mem_cons.2 ⟨subd11_4_96, List.forall_mem_cons.2 ⟨subd11_4_97, List.forall_mem_cons.2 ⟨subd11_4_98, List.forall_mem_cons.2 ⟨subd11_4_99, List.forall_mem_cons.2 ⟨subd11_4_100, List.forall_mem_cons.2 ⟨subd11_4_101, List.forall_mem_cons.2 ⟨subd11_4_102, List.forall_mem_cons.2 ⟨subd11_4_103, List.forall_mem_cons.2 ⟨subd11_4_104, List.forall_mem_cons.2 ⟨subd11_4_105, List.forall_mem_cons.2 ⟨subd11_4_106, List.forall_mem_cons.2 ⟨subd11_4_107, List.forall_mem_cons.2 ⟨subd11_4_108, List.forall_mem_cons.2 ⟨subd11_4_109, List.forall_mem_cons.2 ⟨subd11_4_110, List.forall_mem_cons.2 ⟨subd11_4_111, List.forall_mem_cons.2 ⟨subd11_4_112, List.forall_mem_cons.2 ⟨subd11_4_113, List.forall_mem_cons.2 ⟨subd11_4_114, List.forall_mem_cons.2 ⟨subd11_4_115, List.forall_mem_cons.2 ⟨subd11_4_116, List.forall_mem_cons.2 ⟨subd11_4_117, List.forall_mem_cons.2 ⟨subd11_4_118, List.forall_mem_cons.2 ⟨subd11_4_119, List.forall_mem_cons.2 ⟨subd11_4_120, List.forall_mem_cons.2 ⟨subd11_4_121, List.forall_mem_cons.2 ⟨subd11_4_122, List.forall_mem_cons.2 ⟨subd11_4_123, List.forall_mem_cons.2 ⟨subd11_4_124, List.forall_mem_cons.2 ⟨subd11_4_125, List.forall_mem_cons.2 ⟨subd11_4_126, List.forall_mem_cons.2 ⟨subd11_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_4_128 : subd11_4 [1, -1, 4] = true := by decide +kernel
theorem subd11_4_129 : subd11_4 [1, -1, 5] = true := by decide +kernel
theorem subd11_4_130 : subd11_4 [1, -1, 6] = true := by decide +kernel
theorem subd11_4_131 : subd11_4 [1, 0, -8] = true := by decide +kernel
theorem subd11_4_132 : subd11_4 [1, 0, -7] = true := by decide +kernel
theorem subd11_4_133 : subd11_4 [1, 0, -6] = true := by decide +kernel
theorem subd11_4_134 : subd11_4 [1, 0, -5] = true := by decide +kernel
theorem subd11_4_135 : subd11_4 [1, 0, -4] = true := by decide +kernel
theorem subd11_4_136 : subd11_4 [1, 0, -3] = true := by decide +kernel
theorem subd11_4_137 : subd11_4 [1, 0, -2] = true := by decide +kernel
theorem subd11_4_138 : subd11_4 [1, 0, -1] = true := by decide +kernel
theorem subd11_4_139 : subd11_4 [1, 0, 0] = true := by decide +kernel
theorem subd11_4_140 : subd11_4 [1, 0, 1] = true := by decide +kernel
theorem subd11_4_141 : subd11_4 [1, 0, 2] = true := by decide +kernel
theorem subd11_4_142 : subd11_4 [1, 0, 3] = true := by decide +kernel
theorem subd11_4_143 : subd11_4 [1, 0, 4] = true := by decide +kernel
theorem subd11_4_144 : subd11_4 [1, 0, 5] = true := by decide +kernel
theorem subd11_4_145 : subd11_4 [1, 0, 6] = true := by decide +kernel
theorem subd11_4_146 : subd11_4 [1, 1, -8] = true := by decide +kernel
theorem subd11_4_147 : subd11_4 [1, 1, -7] = true := by decide +kernel
theorem subd11_4_148 : subd11_4 [1, 1, -6] = true := by decide +kernel
theorem subd11_4_149 : subd11_4 [1, 1, -5] = true := by decide +kernel
theorem subd11_4_150 : subd11_4 [1, 1, -4] = true := by decide +kernel
theorem subd11_4_151 : subd11_4 [1, 1, -3] = true := by decide +kernel
theorem subd11_4_152 : subd11_4 [1, 1, -2] = true := by decide +kernel
theorem subd11_4_153 : subd11_4 [1, 1, -1] = true := by decide +kernel
theorem subd11_4_154 : subd11_4 [1, 1, 0] = true := by decide +kernel
theorem subd11_4_155 : subd11_4 [1, 1, 1] = true := by decide +kernel
theorem subd11_4_156 : subd11_4 [1, 1, 2] = true := by decide +kernel
theorem subd11_4_157 : subd11_4 [1, 1, 3] = true := by decide +kernel
theorem subd11_4_158 : subd11_4 [1, 1, 4] = true := by decide +kernel
theorem subd11_4_159 : subd11_4 [1, 1, 5] = true := by decide +kernel
theorem sbd11_4_4 : ∀ q ∈ blkd11_4_4, subd11_4 q = true := by
  unfold blkd11_4_4
  exact List.forall_mem_cons.2 ⟨subd11_4_128, List.forall_mem_cons.2 ⟨subd11_4_129, List.forall_mem_cons.2 ⟨subd11_4_130, List.forall_mem_cons.2 ⟨subd11_4_131, List.forall_mem_cons.2 ⟨subd11_4_132, List.forall_mem_cons.2 ⟨subd11_4_133, List.forall_mem_cons.2 ⟨subd11_4_134, List.forall_mem_cons.2 ⟨subd11_4_135, List.forall_mem_cons.2 ⟨subd11_4_136, List.forall_mem_cons.2 ⟨subd11_4_137, List.forall_mem_cons.2 ⟨subd11_4_138, List.forall_mem_cons.2 ⟨subd11_4_139, List.forall_mem_cons.2 ⟨subd11_4_140, List.forall_mem_cons.2 ⟨subd11_4_141, List.forall_mem_cons.2 ⟨subd11_4_142, List.forall_mem_cons.2 ⟨subd11_4_143, List.forall_mem_cons.2 ⟨subd11_4_144, List.forall_mem_cons.2 ⟨subd11_4_145, List.forall_mem_cons.2 ⟨subd11_4_146, List.forall_mem_cons.2 ⟨subd11_4_147, List.forall_mem_cons.2 ⟨subd11_4_148, List.forall_mem_cons.2 ⟨subd11_4_149, List.forall_mem_cons.2 ⟨subd11_4_150, List.forall_mem_cons.2 ⟨subd11_4_151, List.forall_mem_cons.2 ⟨subd11_4_152, List.forall_mem_cons.2 ⟨subd11_4_153, List.forall_mem_cons.2 ⟨subd11_4_154, List.forall_mem_cons.2 ⟨subd11_4_155, List.forall_mem_cons.2 ⟨subd11_4_156, List.forall_mem_cons.2 ⟨subd11_4_157, List.forall_mem_cons.2 ⟨subd11_4_158, List.forall_mem_cons.2 ⟨subd11_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
