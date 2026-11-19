import ReflectZphi.Data.Cert5.C133.Base

namespace ReflectZphi.Data.Cert5.C133

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_3_288 : subd8_3 [1, 1, 0] = true := by decide +kernel
theorem subd8_3_289 : subd8_3 [1, 1, 1] = true := by decide +kernel
theorem subd8_3_290 : subd8_3 [1, 1, 2] = true := by decide +kernel
theorem subd8_3_291 : subd8_3 [1, 1, 3] = true := by decide +kernel
theorem subd8_3_292 : subd8_3 [1, 1, 4] = true := by decide +kernel
theorem subd8_3_293 : subd8_3 [1, 1, 5] = true := by decide +kernel
theorem subd8_3_294 : subd8_3 [1, 1, 6] = true := by decide +kernel
theorem subd8_3_295 : subd8_3 [1, 1, 7] = true := by decide +kernel
theorem subd8_3_296 : subd8_3 [1, 1, 8] = true := by decide +kernel
theorem subd8_3_297 : subd8_3 [1, 1, 9] = true := by decide +kernel
theorem subd8_3_298 : subd8_3 [1, 1, 10] = true := by decide +kernel
theorem subd8_3_299 : subd8_3 [1, 1, 11] = true := by decide +kernel
theorem subd8_3_300 : subd8_3 [1, 1, 12] = true := by decide +kernel
theorem subd8_3_301 : subd8_3 [1, 2, -9] = true := by decide +kernel
theorem subd8_3_302 : subd8_3 [1, 2, -8] = true := by decide +kernel
theorem subd8_3_303 : subd8_3 [1, 2, -7] = true := by decide +kernel
theorem subd8_3_304 : subd8_3 [1, 2, -6] = true := by decide +kernel
theorem subd8_3_305 : subd8_3 [1, 2, -5] = true := by decide +kernel
theorem subd8_3_306 : subd8_3 [1, 2, -4] = true := by decide +kernel
theorem subd8_3_307 : subd8_3 [1, 2, -3] = true := by decide +kernel
theorem subd8_3_308 : subd8_3 [1, 2, -2] = true := by decide +kernel
theorem subd8_3_309 : subd8_3 [1, 2, -1] = true := by decide +kernel
theorem subd8_3_310 : subd8_3 [1, 2, 0] = true := by decide +kernel
theorem subd8_3_311 : subd8_3 [1, 2, 1] = true := by decide +kernel
theorem subd8_3_312 : subd8_3 [1, 2, 2] = true := by decide +kernel
theorem subd8_3_313 : subd8_3 [1, 2, 3] = true := by decide +kernel
theorem subd8_3_314 : subd8_3 [1, 2, 4] = true := by decide +kernel
theorem subd8_3_315 : subd8_3 [1, 2, 5] = true := by decide +kernel
theorem subd8_3_316 : subd8_3 [1, 2, 6] = true := by decide +kernel
theorem subd8_3_317 : subd8_3 [1, 2, 7] = true := by decide +kernel
theorem subd8_3_318 : subd8_3 [1, 2, 8] = true := by decide +kernel
theorem subd8_3_319 : subd8_3 [1, 2, 9] = true := by decide +kernel
theorem sbd8_3_9 : ∀ q ∈ blkd8_3_9, subd8_3 q = true := by
  unfold blkd8_3_9
  exact List.forall_mem_cons.2 ⟨subd8_3_288, List.forall_mem_cons.2 ⟨subd8_3_289, List.forall_mem_cons.2 ⟨subd8_3_290, List.forall_mem_cons.2 ⟨subd8_3_291, List.forall_mem_cons.2 ⟨subd8_3_292, List.forall_mem_cons.2 ⟨subd8_3_293, List.forall_mem_cons.2 ⟨subd8_3_294, List.forall_mem_cons.2 ⟨subd8_3_295, List.forall_mem_cons.2 ⟨subd8_3_296, List.forall_mem_cons.2 ⟨subd8_3_297, List.forall_mem_cons.2 ⟨subd8_3_298, List.forall_mem_cons.2 ⟨subd8_3_299, List.forall_mem_cons.2 ⟨subd8_3_300, List.forall_mem_cons.2 ⟨subd8_3_301, List.forall_mem_cons.2 ⟨subd8_3_302, List.forall_mem_cons.2 ⟨subd8_3_303, List.forall_mem_cons.2 ⟨subd8_3_304, List.forall_mem_cons.2 ⟨subd8_3_305, List.forall_mem_cons.2 ⟨subd8_3_306, List.forall_mem_cons.2 ⟨subd8_3_307, List.forall_mem_cons.2 ⟨subd8_3_308, List.forall_mem_cons.2 ⟨subd8_3_309, List.forall_mem_cons.2 ⟨subd8_3_310, List.forall_mem_cons.2 ⟨subd8_3_311, List.forall_mem_cons.2 ⟨subd8_3_312, List.forall_mem_cons.2 ⟨subd8_3_313, List.forall_mem_cons.2 ⟨subd8_3_314, List.forall_mem_cons.2 ⟨subd8_3_315, List.forall_mem_cons.2 ⟨subd8_3_316, List.forall_mem_cons.2 ⟨subd8_3_317, List.forall_mem_cons.2 ⟨subd8_3_318, List.forall_mem_cons.2 ⟨subd8_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_320 : subd8_3 [2, -1] = true := by decide +kernel
theorem subd8_3_321 : subd8_3 [2, 0] = true := by decide +kernel
theorem subd8_3_322 : subd8_3 [2, 1] = true := by decide +kernel
theorem sbd8_3_10 : ∀ q ∈ blkd8_3_10, subd8_3 q = true := by
  unfold blkd8_3_10
  exact List.forall_mem_cons.2 ⟨subd8_3_320, List.forall_mem_cons.2 ⟨subd8_3_321, List.forall_mem_cons.2 ⟨subd8_3_322, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [-3] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [-2] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [-1, -4] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [-1, -3] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [-1, -2] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [-1, -1] = true := by decide +kernel
theorem subd9_0_6 : subd9_0 [-1, 0] = true := by decide +kernel
theorem subd9_0_7 : subd9_0 [-1, 1] = true := by decide +kernel
theorem subd9_0_8 : subd9_0 [-1, 2] = true := by decide +kernel
theorem subd9_0_9 : subd9_0 [-1, 3] = true := by decide +kernel
theorem subd9_0_10 : subd9_0 [0, -4] = true := by decide +kernel
theorem subd9_0_11 : subd9_0 [0, -3] = true := by decide +kernel
theorem subd9_0_12 : subd9_0 [0, -2] = true := by decide +kernel
theorem subd9_0_13 : subd9_0 [0, -1] = true := by decide +kernel
theorem subd9_0_14 : subd9_0 [0, 0] = true := by decide +kernel
theorem subd9_0_15 : subd9_0 [0, 1] = true := by decide +kernel
theorem subd9_0_16 : subd9_0 [0, 2] = true := by decide +kernel
theorem subd9_0_17 : subd9_0 [0, 3] = true := by decide +kernel
theorem subd9_0_18 : subd9_0 [1, -4] = true := by decide +kernel
theorem subd9_0_19 : subd9_0 [1, -3] = true := by decide +kernel
theorem subd9_0_20 : subd9_0 [1, -2] = true := by decide +kernel
theorem subd9_0_21 : subd9_0 [1, -1] = true := by decide +kernel
theorem subd9_0_22 : subd9_0 [1, 0] = true := by decide +kernel
theorem subd9_0_23 : subd9_0 [1, 1] = true := by decide +kernel
theorem subd9_0_24 : subd9_0 [1, 2] = true := by decide +kernel
theorem subd9_0_25 : subd9_0 [1, 3] = true := by decide +kernel
theorem subd9_0_26 : subd9_0 [2] = true := by decide +kernel
theorem subd9_0_27 : subd9_0 [3] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_cons.2 ⟨subd9_0_6, List.forall_mem_cons.2 ⟨subd9_0_7, List.forall_mem_cons.2 ⟨subd9_0_8, List.forall_mem_cons.2 ⟨subd9_0_9, List.forall_mem_cons.2 ⟨subd9_0_10, List.forall_mem_cons.2 ⟨subd9_0_11, List.forall_mem_cons.2 ⟨subd9_0_12, List.forall_mem_cons.2 ⟨subd9_0_13, List.forall_mem_cons.2 ⟨subd9_0_14, List.forall_mem_cons.2 ⟨subd9_0_15, List.forall_mem_cons.2 ⟨subd9_0_16, List.forall_mem_cons.2 ⟨subd9_0_17, List.forall_mem_cons.2 ⟨subd9_0_18, List.forall_mem_cons.2 ⟨subd9_0_19, List.forall_mem_cons.2 ⟨subd9_0_20, List.forall_mem_cons.2 ⟨subd9_0_21, List.forall_mem_cons.2 ⟨subd9_0_22, List.forall_mem_cons.2 ⟨subd9_0_23, List.forall_mem_cons.2 ⟨subd9_0_24, List.forall_mem_cons.2 ⟨subd9_0_25, List.forall_mem_cons.2 ⟨subd9_0_26, List.forall_mem_cons.2 ⟨subd9_0_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [-2] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-1, -3] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [-1, -2] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [-1, -1] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [-1, 0] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [-1, 1] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [-1, 2] = true := by decide +kernel
theorem subd9_1_7 : subd9_1 [0, -3] = true := by decide +kernel
theorem subd9_1_8 : subd9_1 [0, -2] = true := by decide +kernel
theorem subd9_1_9 : subd9_1 [0, -1] = true := by decide +kernel
theorem subd9_1_10 : subd9_1 [0, 0] = true := by decide +kernel
theorem subd9_1_11 : subd9_1 [0, 1] = true := by decide +kernel
theorem subd9_1_12 : subd9_1 [0, 2] = true := by decide +kernel
theorem subd9_1_13 : subd9_1 [1, -3] = true := by decide +kernel
theorem subd9_1_14 : subd9_1 [1, -2] = true := by decide +kernel
theorem subd9_1_15 : subd9_1 [1, -1] = true := by decide +kernel
theorem subd9_1_16 : subd9_1 [1, 0] = true := by decide +kernel
theorem subd9_1_17 : subd9_1 [1, 1] = true := by decide +kernel
theorem subd9_1_18 : subd9_1 [1, 2] = true := by decide +kernel
theorem subd9_1_19 : subd9_1 [2] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_cons.2 ⟨subd9_1_7, List.forall_mem_cons.2 ⟨subd9_1_8, List.forall_mem_cons.2 ⟨subd9_1_9, List.forall_mem_cons.2 ⟨subd9_1_10, List.forall_mem_cons.2 ⟨subd9_1_11, List.forall_mem_cons.2 ⟨subd9_1_12, List.forall_mem_cons.2 ⟨subd9_1_13, List.forall_mem_cons.2 ⟨subd9_1_14, List.forall_mem_cons.2 ⟨subd9_1_15, List.forall_mem_cons.2 ⟨subd9_1_16, List.forall_mem_cons.2 ⟨subd9_1_17, List.forall_mem_cons.2 ⟨subd9_1_18, List.forall_mem_cons.2 ⟨subd9_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel
theorem subd9_2_0 : subd9_2 [-5] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-4, -4] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [-4, -3] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [-4, -2] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [-4, -1] = true := by decide +kernel
theorem subd9_2_5 : subd9_2 [-4, 0] = true := by decide +kernel
theorem subd9_2_6 : subd9_2 [-4, 1] = true := by decide +kernel
theorem subd9_2_7 : subd9_2 [-4, 2] = true := by decide +kernel
theorem subd9_2_8 : subd9_2 [-4, 3] = true := by decide +kernel
theorem subd9_2_9 : subd9_2 [-3, -5] = true := by decide +kernel
theorem subd9_2_10 : subd9_2 [-3, -4] = true := by decide +kernel
theorem subd9_2_11 : subd9_2 [-3, -3] = true := by decide +kernel
theorem subd9_2_12 : subd9_2 [-3, -2] = true := by decide +kernel
theorem subd9_2_13 : subd9_2 [-3, -1] = true := by decide +kernel
theorem subd9_2_14 : subd9_2 [-3, 0] = true := by decide +kernel
theorem subd9_2_15 : subd9_2 [-3, 1] = true := by decide +kernel
theorem subd9_2_16 : subd9_2 [-3, 2] = true := by decide +kernel
theorem subd9_2_17 : subd9_2 [-3, 3] = true := by decide +kernel
theorem subd9_2_18 : subd9_2 [-3, 4] = true := by decide +kernel
theorem subd9_2_19 : subd9_2 [-2, -5] = true := by decide +kernel
theorem subd9_2_20 : subd9_2 [-2, -4] = true := by decide +kernel
theorem subd9_2_21 : subd9_2 [-2, -3] = true := by decide +kernel
theorem subd9_2_22 : subd9_2 [-2, -2, -7] = true := by decide +kernel
theorem subd9_2_23 : subd9_2 [-2, -2, -6] = true := by decide +kernel
theorem subd9_2_24 : subd9_2 [-2, -2, -5] = true := by decide +kernel
theorem subd9_2_25 : subd9_2 [-2, -2, -4] = true := by decide +kernel
theorem subd9_2_26 : subd9_2 [-2, -2, -3] = true := by decide +kernel
theorem subd9_2_27 : subd9_2 [-2, -2, -2] = true := by decide +kernel
theorem subd9_2_28 : subd9_2 [-2, -2, -1] = true := by decide +kernel
theorem subd9_2_29 : subd9_2 [-2, -2, 0] = true := by decide +kernel
theorem subd9_2_30 : subd9_2 [-2, -2, 1] = true := by decide +kernel
theorem subd9_2_31 : subd9_2 [-2, -2, 2] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_cons.2 ⟨subd9_2_5, List.forall_mem_cons.2 ⟨subd9_2_6, List.forall_mem_cons.2 ⟨subd9_2_7, List.forall_mem_cons.2 ⟨subd9_2_8, List.forall_mem_cons.2 ⟨subd9_2_9, List.forall_mem_cons.2 ⟨subd9_2_10, List.forall_mem_cons.2 ⟨subd9_2_11, List.forall_mem_cons.2 ⟨subd9_2_12, List.forall_mem_cons.2 ⟨subd9_2_13, List.forall_mem_cons.2 ⟨subd9_2_14, List.forall_mem_cons.2 ⟨subd9_2_15, List.forall_mem_cons.2 ⟨subd9_2_16, List.forall_mem_cons.2 ⟨subd9_2_17, List.forall_mem_cons.2 ⟨subd9_2_18, List.forall_mem_cons.2 ⟨subd9_2_19, List.forall_mem_cons.2 ⟨subd9_2_20, List.forall_mem_cons.2 ⟨subd9_2_21, List.forall_mem_cons.2 ⟨subd9_2_22, List.forall_mem_cons.2 ⟨subd9_2_23, List.forall_mem_cons.2 ⟨subd9_2_24, List.forall_mem_cons.2 ⟨subd9_2_25, List.forall_mem_cons.2 ⟨subd9_2_26, List.forall_mem_cons.2 ⟨subd9_2_27, List.forall_mem_cons.2 ⟨subd9_2_28, List.forall_mem_cons.2 ⟨subd9_2_29, List.forall_mem_cons.2 ⟨subd9_2_30, List.forall_mem_cons.2 ⟨subd9_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_32 : subd9_2 [-2, -2, 3] = true := by decide +kernel
theorem subd9_2_33 : subd9_2 [-2, -2, 4] = true := by decide +kernel
theorem subd9_2_34 : subd9_2 [-2, -2, 5] = true := by decide +kernel
theorem subd9_2_35 : subd9_2 [-2, -2, 6] = true := by decide +kernel
theorem subd9_2_36 : subd9_2 [-2, -1, -8] = true := by decide +kernel
theorem subd9_2_37 : subd9_2 [-2, -1, -7] = true := by decide +kernel
theorem subd9_2_38 : subd9_2 [-2, -1, -6] = true := by decide +kernel
theorem subd9_2_39 : subd9_2 [-2, -1, -5] = true := by decide +kernel
theorem subd9_2_40 : subd9_2 [-2, -1, -4] = true := by decide +kernel
theorem subd9_2_41 : subd9_2 [-2, -1, -3] = true := by decide +kernel
theorem subd9_2_42 : subd9_2 [-2, -1, -2] = true := by decide +kernel
theorem subd9_2_43 : subd9_2 [-2, -1, -1] = true := by decide +kernel
theorem subd9_2_44 : subd9_2 [-2, -1, 0] = true := by decide +kernel
theorem subd9_2_45 : subd9_2 [-2, -1, 1] = true := by decide +kernel
theorem subd9_2_46 : subd9_2 [-2, -1, 2] = true := by decide +kernel
theorem subd9_2_47 : subd9_2 [-2, -1, 3] = true := by decide +kernel
theorem subd9_2_48 : subd9_2 [-2, -1, 4] = true := by decide +kernel
theorem subd9_2_49 : subd9_2 [-2, -1, 5] = true := by decide +kernel
theorem subd9_2_50 : subd9_2 [-2, -1, 6] = true := by decide +kernel
theorem subd9_2_51 : subd9_2 [-2, 0, -9] = true := by decide +kernel
theorem subd9_2_52 : subd9_2 [-2, 0, -8] = true := by decide +kernel
theorem subd9_2_53 : subd9_2 [-2, 0, -7] = true := by decide +kernel
theorem subd9_2_54 : subd9_2 [-2, 0, -6] = true := by decide +kernel
theorem subd9_2_55 : subd9_2 [-2, 0, -5] = true := by decide +kernel
theorem subd9_2_56 : subd9_2 [-2, 0, -4] = true := by decide +kernel
theorem subd9_2_57 : subd9_2 [-2, 0, -3] = true := by decide +kernel
theorem subd9_2_58 : subd9_2 [-2, 0, -2] = true := by decide +kernel
theorem subd9_2_59 : subd9_2 [-2, 0, -1] = true := by decide +kernel
theorem subd9_2_60 : subd9_2 [-2, 0, 0] = true := by decide +kernel
theorem subd9_2_61 : subd9_2 [-2, 0, 1] = true := by decide +kernel
theorem subd9_2_62 : subd9_2 [-2, 0, 2] = true := by decide +kernel
theorem subd9_2_63 : subd9_2 [-2, 0, 3] = true := by decide +kernel
theorem sbd9_2_1 : ∀ q ∈ blkd9_2_1, subd9_2 q = true := by
  unfold blkd9_2_1
  exact List.forall_mem_cons.2 ⟨subd9_2_32, List.forall_mem_cons.2 ⟨subd9_2_33, List.forall_mem_cons.2 ⟨subd9_2_34, List.forall_mem_cons.2 ⟨subd9_2_35, List.forall_mem_cons.2 ⟨subd9_2_36, List.forall_mem_cons.2 ⟨subd9_2_37, List.forall_mem_cons.2 ⟨subd9_2_38, List.forall_mem_cons.2 ⟨subd9_2_39, List.forall_mem_cons.2 ⟨subd9_2_40, List.forall_mem_cons.2 ⟨subd9_2_41, List.forall_mem_cons.2 ⟨subd9_2_42, List.forall_mem_cons.2 ⟨subd9_2_43, List.forall_mem_cons.2 ⟨subd9_2_44, List.forall_mem_cons.2 ⟨subd9_2_45, List.forall_mem_cons.2 ⟨subd9_2_46, List.forall_mem_cons.2 ⟨subd9_2_47, List.forall_mem_cons.2 ⟨subd9_2_48, List.forall_mem_cons.2 ⟨subd9_2_49, List.forall_mem_cons.2 ⟨subd9_2_50, List.forall_mem_cons.2 ⟨subd9_2_51, List.forall_mem_cons.2 ⟨subd9_2_52, List.forall_mem_cons.2 ⟨subd9_2_53, List.forall_mem_cons.2 ⟨subd9_2_54, List.forall_mem_cons.2 ⟨subd9_2_55, List.forall_mem_cons.2 ⟨subd9_2_56, List.forall_mem_cons.2 ⟨subd9_2_57, List.forall_mem_cons.2 ⟨subd9_2_58, List.forall_mem_cons.2 ⟨subd9_2_59, List.forall_mem_cons.2 ⟨subd9_2_60, List.forall_mem_cons.2 ⟨subd9_2_61, List.forall_mem_cons.2 ⟨subd9_2_62, List.forall_mem_cons.2 ⟨subd9_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_64 : subd9_2 [-2, 0, 4] = true := by decide +kernel
theorem subd9_2_65 : subd9_2 [-2, 0, 5] = true := by decide +kernel
theorem subd9_2_66 : subd9_2 [-2, 0, 6] = true := by decide +kernel
theorem subd9_2_67 : subd9_2 [-2, 1, -9] = true := by decide +kernel
theorem subd9_2_68 : subd9_2 [-2, 1, -8] = true := by decide +kernel
theorem subd9_2_69 : subd9_2 [-2, 1, -7] = true := by decide +kernel
theorem subd9_2_70 : subd9_2 [-2, 1, -6] = true := by decide +kernel
theorem subd9_2_71 : subd9_2 [-2, 1, -5] = true := by decide +kernel
theorem subd9_2_72 : subd9_2 [-2, 1, -4] = true := by decide +kernel
theorem subd9_2_73 : subd9_2 [-2, 1, -3] = true := by decide +kernel
theorem subd9_2_74 : subd9_2 [-2, 1, -2] = true := by decide +kernel
theorem subd9_2_75 : subd9_2 [-2, 1, -1] = true := by decide +kernel
theorem subd9_2_76 : subd9_2 [-2, 1, 0] = true := by decide +kernel
theorem subd9_2_77 : subd9_2 [-2, 1, 1] = true := by decide +kernel
theorem subd9_2_78 : subd9_2 [-2, 1, 2] = true := by decide +kernel
theorem subd9_2_79 : subd9_2 [-2, 1, 3] = true := by decide +kernel
theorem subd9_2_80 : subd9_2 [-2, 1, 4] = true := by decide +kernel
theorem subd9_2_81 : subd9_2 [-2, 1, 5] = true := by decide +kernel
theorem subd9_2_82 : subd9_2 [-2, 1, 6] = true := by decide +kernel
theorem subd9_2_83 : subd9_2 [-2, 2, -9] = true := by decide +kernel
theorem subd9_2_84 : subd9_2 [-2, 2, -8] = true := by decide +kernel
theorem subd9_2_85 : subd9_2 [-2, 2, -7] = true := by decide +kernel
theorem subd9_2_86 : subd9_2 [-2, 2, -6] = true := by decide +kernel
theorem subd9_2_87 : subd9_2 [-2, 2, -5] = true := by decide +kernel
theorem subd9_2_88 : subd9_2 [-2, 2, -4] = true := by decide +kernel
theorem subd9_2_89 : subd9_2 [-2, 2, -3] = true := by decide +kernel
theorem subd9_2_90 : subd9_2 [-2, 2, -2] = true := by decide +kernel
theorem subd9_2_91 : subd9_2 [-2, 2, -1] = true := by decide +kernel
theorem subd9_2_92 : subd9_2 [-2, 2, 0] = true := by decide +kernel
theorem subd9_2_93 : subd9_2 [-2, 2, 1] = true := by decide +kernel
theorem subd9_2_94 : subd9_2 [-2, 2, 2] = true := by decide +kernel
theorem subd9_2_95 : subd9_2 [-2, 2, 3] = true := by decide +kernel
theorem sbd9_2_2 : ∀ q ∈ blkd9_2_2, subd9_2 q = true := by
  unfold blkd9_2_2
  exact List.forall_mem_cons.2 ⟨subd9_2_64, List.forall_mem_cons.2 ⟨subd9_2_65, List.forall_mem_cons.2 ⟨subd9_2_66, List.forall_mem_cons.2 ⟨subd9_2_67, List.forall_mem_cons.2 ⟨subd9_2_68, List.forall_mem_cons.2 ⟨subd9_2_69, List.forall_mem_cons.2 ⟨subd9_2_70, List.forall_mem_cons.2 ⟨subd9_2_71, List.forall_mem_cons.2 ⟨subd9_2_72, List.forall_mem_cons.2 ⟨subd9_2_73, List.forall_mem_cons.2 ⟨subd9_2_74, List.forall_mem_cons.2 ⟨subd9_2_75, List.forall_mem_cons.2 ⟨subd9_2_76, List.forall_mem_cons.2 ⟨subd9_2_77, List.forall_mem_cons.2 ⟨subd9_2_78, List.forall_mem_cons.2 ⟨subd9_2_79, List.forall_mem_cons.2 ⟨subd9_2_80, List.forall_mem_cons.2 ⟨subd9_2_81, List.forall_mem_cons.2 ⟨subd9_2_82, List.forall_mem_cons.2 ⟨subd9_2_83, List.forall_mem_cons.2 ⟨subd9_2_84, List.forall_mem_cons.2 ⟨subd9_2_85, List.forall_mem_cons.2 ⟨subd9_2_86, List.forall_mem_cons.2 ⟨subd9_2_87, List.forall_mem_cons.2 ⟨subd9_2_88, List.forall_mem_cons.2 ⟨subd9_2_89, List.forall_mem_cons.2 ⟨subd9_2_90, List.forall_mem_cons.2 ⟨subd9_2_91, List.forall_mem_cons.2 ⟨subd9_2_92, List.forall_mem_cons.2 ⟨subd9_2_93, List.forall_mem_cons.2 ⟨subd9_2_94, List.forall_mem_cons.2 ⟨subd9_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C133
