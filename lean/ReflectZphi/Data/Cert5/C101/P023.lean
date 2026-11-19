import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_1_288 : subd14_1 [1, 0, 13] = true := by decide +kernel
theorem subd14_1_289 : subd14_1 [1, 0, 14] = true := by decide +kernel
theorem subd14_1_290 : subd14_1 [1, 0, 15] = true := by decide +kernel
theorem subd14_1_291 : subd14_1 [1, 0, 16] = true := by decide +kernel
theorem subd14_1_292 : subd14_1 [1, 0, 17] = true := by decide +kernel
theorem subd14_1_293 : subd14_1 [1, 0, 18] = true := by decide +kernel
theorem subd14_1_294 : subd14_1 [1, 0, 19] = true := by decide +kernel
theorem subd14_1_295 : subd14_1 [1, 1, -14] = true := by decide +kernel
theorem subd14_1_296 : subd14_1 [1, 1, -13] = true := by decide +kernel
theorem subd14_1_297 : subd14_1 [1, 1, -12] = true := by decide +kernel
theorem subd14_1_298 : subd14_1 [1, 1, -11] = true := by decide +kernel
theorem subd14_1_299 : subd14_1 [1, 1, -10] = true := by decide +kernel
theorem subd14_1_300 : subd14_1 [1, 1, -9] = true := by decide +kernel
theorem subd14_1_301 : subd14_1 [1, 1, -8] = true := by decide +kernel
theorem subd14_1_302 : subd14_1 [1, 1, -7] = true := by decide +kernel
theorem subd14_1_303 : subd14_1 [1, 1, -6] = true := by decide +kernel
theorem subd14_1_304 : subd14_1 [1, 1, -5] = true := by decide +kernel
theorem subd14_1_305 : subd14_1 [1, 1, -4] = true := by decide +kernel
theorem subd14_1_306 : subd14_1 [1, 1, -3] = true := by decide +kernel
theorem subd14_1_307 : subd14_1 [1, 1, -2] = true := by decide +kernel
theorem subd14_1_308 : subd14_1 [1, 1, -1] = true := by decide +kernel
theorem subd14_1_309 : subd14_1 [1, 1, 0] = true := by decide +kernel
theorem subd14_1_310 : subd14_1 [1, 1, 1] = true := by decide +kernel
theorem subd14_1_311 : subd14_1 [1, 1, 2] = true := by decide +kernel
theorem subd14_1_312 : subd14_1 [1, 1, 3] = true := by decide +kernel
theorem subd14_1_313 : subd14_1 [1, 1, 4] = true := by decide +kernel
theorem subd14_1_314 : subd14_1 [1, 1, 5] = true := by decide +kernel
theorem subd14_1_315 : subd14_1 [1, 1, 6] = true := by decide +kernel
theorem subd14_1_316 : subd14_1 [1, 1, 7] = true := by decide +kernel
theorem subd14_1_317 : subd14_1 [1, 1, 8] = true := by decide +kernel
theorem subd14_1_318 : subd14_1 [1, 1, 9] = true := by decide +kernel
theorem subd14_1_319 : subd14_1 [1, 1, 10] = true := by decide +kernel
theorem sbd14_1_9 : ∀ q ∈ blkd14_1_9, subd14_1 q = true := by
  unfold blkd14_1_9
  exact List.forall_mem_cons.2 ⟨subd14_1_288, List.forall_mem_cons.2 ⟨subd14_1_289, List.forall_mem_cons.2 ⟨subd14_1_290, List.forall_mem_cons.2 ⟨subd14_1_291, List.forall_mem_cons.2 ⟨subd14_1_292, List.forall_mem_cons.2 ⟨subd14_1_293, List.forall_mem_cons.2 ⟨subd14_1_294, List.forall_mem_cons.2 ⟨subd14_1_295, List.forall_mem_cons.2 ⟨subd14_1_296, List.forall_mem_cons.2 ⟨subd14_1_297, List.forall_mem_cons.2 ⟨subd14_1_298, List.forall_mem_cons.2 ⟨subd14_1_299, List.forall_mem_cons.2 ⟨subd14_1_300, List.forall_mem_cons.2 ⟨subd14_1_301, List.forall_mem_cons.2 ⟨subd14_1_302, List.forall_mem_cons.2 ⟨subd14_1_303, List.forall_mem_cons.2 ⟨subd14_1_304, List.forall_mem_cons.2 ⟨subd14_1_305, List.forall_mem_cons.2 ⟨subd14_1_306, List.forall_mem_cons.2 ⟨subd14_1_307, List.forall_mem_cons.2 ⟨subd14_1_308, List.forall_mem_cons.2 ⟨subd14_1_309, List.forall_mem_cons.2 ⟨subd14_1_310, List.forall_mem_cons.2 ⟨subd14_1_311, List.forall_mem_cons.2 ⟨subd14_1_312, List.forall_mem_cons.2 ⟨subd14_1_313, List.forall_mem_cons.2 ⟨subd14_1_314, List.forall_mem_cons.2 ⟨subd14_1_315, List.forall_mem_cons.2 ⟨subd14_1_316, List.forall_mem_cons.2 ⟨subd14_1_317, List.forall_mem_cons.2 ⟨subd14_1_318, List.forall_mem_cons.2 ⟨subd14_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_320 : subd14_1 [1, 1, 11] = true := by decide +kernel
theorem subd14_1_321 : subd14_1 [1, 1, 12] = true := by decide +kernel
theorem subd14_1_322 : subd14_1 [1, 1, 13] = true := by decide +kernel
theorem sbd14_1_10 : ∀ q ∈ blkd14_1_10, subd14_1 q = true := by
  unfold blkd14_1_10
  exact List.forall_mem_cons.2 ⟨subd14_1_320, List.forall_mem_cons.2 ⟨subd14_1_321, List.forall_mem_cons.2 ⟨subd14_1_322, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel
theorem subd15_0_0 : subd15_0 [-4] = true := by decide +kernel
theorem subd15_0_1 : subd15_0 [-3, -4] = true := by decide +kernel
theorem subd15_0_2 : subd15_0 [-3, -3] = true := by decide +kernel
theorem subd15_0_3 : subd15_0 [-3, -2] = true := by decide +kernel
theorem subd15_0_4 : subd15_0 [-3, -1] = true := by decide +kernel
theorem subd15_0_5 : subd15_0 [-3, 0] = true := by decide +kernel
theorem subd15_0_6 : subd15_0 [-3, 1] = true := by decide +kernel
theorem subd15_0_7 : subd15_0 [-3, 2] = true := by decide +kernel
theorem subd15_0_8 : subd15_0 [-3, 3] = true := by decide +kernel
theorem subd15_0_9 : subd15_0 [-2, -5] = true := by decide +kernel
theorem subd15_0_10 : subd15_0 [-2, -4] = true := by decide +kernel
theorem subd15_0_11 : subd15_0 [-2, -3] = true := by decide +kernel
theorem subd15_0_12 : subd15_0 [-2, -2] = true := by decide +kernel
theorem subd15_0_13 : subd15_0 [-2, -1] = true := by decide +kernel
theorem subd15_0_14 : subd15_0 [-2, 0] = true := by decide +kernel
theorem subd15_0_15 : subd15_0 [-2, 1] = true := by decide +kernel
theorem subd15_0_16 : subd15_0 [-2, 2] = true := by decide +kernel
theorem subd15_0_17 : subd15_0 [-2, 3] = true := by decide +kernel
theorem subd15_0_18 : subd15_0 [-1, -5] = true := by decide +kernel
theorem subd15_0_19 : subd15_0 [-1, -4] = true := by decide +kernel
theorem subd15_0_20 : subd15_0 [-1, -3] = true := by decide +kernel
theorem subd15_0_21 : subd15_0 [-1, -2] = true := by decide +kernel
theorem subd15_0_22 : subd15_0 [-1, -1] = true := by decide +kernel
theorem subd15_0_23 : subd15_0 [-1, 0] = true := by decide +kernel
theorem subd15_0_24 : subd15_0 [-1, 1] = true := by decide +kernel
theorem subd15_0_25 : subd15_0 [-1, 2] = true := by decide +kernel
theorem subd15_0_26 : subd15_0 [-1, 3] = true := by decide +kernel
theorem subd15_0_27 : subd15_0 [-1, 4] = true := by decide +kernel
theorem subd15_0_28 : subd15_0 [0, -5] = true := by decide +kernel
theorem subd15_0_29 : subd15_0 [0, -4] = true := by decide +kernel
theorem subd15_0_30 : subd15_0 [0, -3] = true := by decide +kernel
theorem subd15_0_31 : subd15_0 [0, -2] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_cons.2 ⟨subd15_0_1, List.forall_mem_cons.2 ⟨subd15_0_2, List.forall_mem_cons.2 ⟨subd15_0_3, List.forall_mem_cons.2 ⟨subd15_0_4, List.forall_mem_cons.2 ⟨subd15_0_5, List.forall_mem_cons.2 ⟨subd15_0_6, List.forall_mem_cons.2 ⟨subd15_0_7, List.forall_mem_cons.2 ⟨subd15_0_8, List.forall_mem_cons.2 ⟨subd15_0_9, List.forall_mem_cons.2 ⟨subd15_0_10, List.forall_mem_cons.2 ⟨subd15_0_11, List.forall_mem_cons.2 ⟨subd15_0_12, List.forall_mem_cons.2 ⟨subd15_0_13, List.forall_mem_cons.2 ⟨subd15_0_14, List.forall_mem_cons.2 ⟨subd15_0_15, List.forall_mem_cons.2 ⟨subd15_0_16, List.forall_mem_cons.2 ⟨subd15_0_17, List.forall_mem_cons.2 ⟨subd15_0_18, List.forall_mem_cons.2 ⟨subd15_0_19, List.forall_mem_cons.2 ⟨subd15_0_20, List.forall_mem_cons.2 ⟨subd15_0_21, List.forall_mem_cons.2 ⟨subd15_0_22, List.forall_mem_cons.2 ⟨subd15_0_23, List.forall_mem_cons.2 ⟨subd15_0_24, List.forall_mem_cons.2 ⟨subd15_0_25, List.forall_mem_cons.2 ⟨subd15_0_26, List.forall_mem_cons.2 ⟨subd15_0_27, List.forall_mem_cons.2 ⟨subd15_0_28, List.forall_mem_cons.2 ⟨subd15_0_29, List.forall_mem_cons.2 ⟨subd15_0_30, List.forall_mem_cons.2 ⟨subd15_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_32 : subd15_0 [0, -1] = true := by decide +kernel
theorem subd15_0_33 : subd15_0 [0, 0] = true := by decide +kernel
theorem subd15_0_34 : subd15_0 [0, 1] = true := by decide +kernel
theorem subd15_0_35 : subd15_0 [0, 2] = true := by decide +kernel
theorem subd15_0_36 : subd15_0 [0, 3] = true := by decide +kernel
theorem subd15_0_37 : subd15_0 [0, 4] = true := by decide +kernel
theorem subd15_0_38 : subd15_0 [1, -5] = true := by decide +kernel
theorem subd15_0_39 : subd15_0 [1, -4] = true := by decide +kernel
theorem subd15_0_40 : subd15_0 [1, -3] = true := by decide +kernel
theorem subd15_0_41 : subd15_0 [1, -2] = true := by decide +kernel
theorem subd15_0_42 : subd15_0 [1, -1] = true := by decide +kernel
theorem subd15_0_43 : subd15_0 [1, 0] = true := by decide +kernel
theorem subd15_0_44 : subd15_0 [1, 1] = true := by decide +kernel
theorem subd15_0_45 : subd15_0 [1, 2] = true := by decide +kernel
theorem subd15_0_46 : subd15_0 [1, 3] = true := by decide +kernel
theorem subd15_0_47 : subd15_0 [1, 4] = true := by decide +kernel
theorem subd15_0_48 : subd15_0 [2, -4] = true := by decide +kernel
theorem subd15_0_49 : subd15_0 [2, -3] = true := by decide +kernel
theorem subd15_0_50 : subd15_0 [2, -2] = true := by decide +kernel
theorem subd15_0_51 : subd15_0 [2, -1] = true := by decide +kernel
theorem subd15_0_52 : subd15_0 [2, 0] = true := by decide +kernel
theorem subd15_0_53 : subd15_0 [2, 1] = true := by decide +kernel
theorem subd15_0_54 : subd15_0 [2, 2] = true := by decide +kernel
theorem subd15_0_55 : subd15_0 [2, 3] = true := by decide +kernel
theorem subd15_0_56 : subd15_0 [2, 4] = true := by decide +kernel
theorem subd15_0_57 : subd15_0 [3, -4] = true := by decide +kernel
theorem subd15_0_58 : subd15_0 [3, -3] = true := by decide +kernel
theorem subd15_0_59 : subd15_0 [3, -2] = true := by decide +kernel
theorem subd15_0_60 : subd15_0 [3, -1] = true := by decide +kernel
theorem subd15_0_61 : subd15_0 [3, 0] = true := by decide +kernel
theorem subd15_0_62 : subd15_0 [3, 1] = true := by decide +kernel
theorem subd15_0_63 : subd15_0 [3, 2] = true := by decide +kernel
theorem sbd15_0_1 : ∀ q ∈ blkd15_0_1, subd15_0 q = true := by
  unfold blkd15_0_1
  exact List.forall_mem_cons.2 ⟨subd15_0_32, List.forall_mem_cons.2 ⟨subd15_0_33, List.forall_mem_cons.2 ⟨subd15_0_34, List.forall_mem_cons.2 ⟨subd15_0_35, List.forall_mem_cons.2 ⟨subd15_0_36, List.forall_mem_cons.2 ⟨subd15_0_37, List.forall_mem_cons.2 ⟨subd15_0_38, List.forall_mem_cons.2 ⟨subd15_0_39, List.forall_mem_cons.2 ⟨subd15_0_40, List.forall_mem_cons.2 ⟨subd15_0_41, List.forall_mem_cons.2 ⟨subd15_0_42, List.forall_mem_cons.2 ⟨subd15_0_43, List.forall_mem_cons.2 ⟨subd15_0_44, List.forall_mem_cons.2 ⟨subd15_0_45, List.forall_mem_cons.2 ⟨subd15_0_46, List.forall_mem_cons.2 ⟨subd15_0_47, List.forall_mem_cons.2 ⟨subd15_0_48, List.forall_mem_cons.2 ⟨subd15_0_49, List.forall_mem_cons.2 ⟨subd15_0_50, List.forall_mem_cons.2 ⟨subd15_0_51, List.forall_mem_cons.2 ⟨subd15_0_52, List.forall_mem_cons.2 ⟨subd15_0_53, List.forall_mem_cons.2 ⟨subd15_0_54, List.forall_mem_cons.2 ⟨subd15_0_55, List.forall_mem_cons.2 ⟨subd15_0_56, List.forall_mem_cons.2 ⟨subd15_0_57, List.forall_mem_cons.2 ⟨subd15_0_58, List.forall_mem_cons.2 ⟨subd15_0_59, List.forall_mem_cons.2 ⟨subd15_0_60, List.forall_mem_cons.2 ⟨subd15_0_61, List.forall_mem_cons.2 ⟨subd15_0_62, List.forall_mem_cons.2 ⟨subd15_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_64 : subd15_0 [3, 3] = true := by decide +kernel
theorem subd15_0_65 : subd15_0 [4] = true := by decide +kernel
theorem sbd15_0_2 : ∀ q ∈ blkd15_0_2, subd15_0 q = true := by
  unfold blkd15_0_2
  exact List.forall_mem_cons.2 ⟨subd15_0_64, List.forall_mem_cons.2 ⟨subd15_0_65, List.forall_mem_nil _⟩⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel
theorem subd15_1_0 : subd15_1 [-1, -2] = true := by decide +kernel
theorem subd15_1_1 : subd15_1 [-1, -1, -7] = true := by decide +kernel
theorem subd15_1_2 : subd15_1 [-1, -1, -6] = true := by decide +kernel
theorem subd15_1_3 : subd15_1 [-1, -1, -5] = true := by decide +kernel
theorem subd15_1_4 : subd15_1 [-1, -1, -4] = true := by decide +kernel
theorem subd15_1_5 : subd15_1 [-1, -1, -3] = true := by decide +kernel
theorem subd15_1_6 : subd15_1 [-1, -1, -2] = true := by decide +kernel
theorem subd15_1_7 : subd15_1 [-1, -1, -1] = true := by decide +kernel
theorem subd15_1_8 : subd15_1 [-1, -1, 0] = true := by decide +kernel
theorem subd15_1_9 : subd15_1 [-1, -1, 1] = true := by decide +kernel
theorem subd15_1_10 : subd15_1 [-1, -1, 2] = true := by decide +kernel
theorem subd15_1_11 : subd15_1 [-1, -1, 3] = true := by decide +kernel
theorem subd15_1_12 : subd15_1 [-1, -1, 4] = true := by decide +kernel
theorem subd15_1_13 : subd15_1 [-1, -1, 5] = true := by decide +kernel
theorem subd15_1_14 : subd15_1 [-1, -1, 6] = true := by decide +kernel
theorem subd15_1_15 : subd15_1 [-1, -1, 7] = true := by decide +kernel
theorem subd15_1_16 : subd15_1 [-1, 0, -10] = true := by decide +kernel
theorem subd15_1_17 : subd15_1 [-1, 0, -9] = true := by decide +kernel
theorem subd15_1_18 : subd15_1 [-1, 0, -8] = true := by decide +kernel
theorem subd15_1_19 : subd15_1 [-1, 0, -7] = true := by decide +kernel
theorem subd15_1_20 : subd15_1 [-1, 0, -6] = true := by decide +kernel
theorem subd15_1_21 : subd15_1 [-1, 0, -5] = true := by decide +kernel
theorem subd15_1_22 : subd15_1 [-1, 0, -4] = true := by decide +kernel
theorem subd15_1_23 : subd15_1 [-1, 0, -3] = true := by decide +kernel
theorem subd15_1_24 : subd15_1 [-1, 0, -2] = true := by decide +kernel
theorem subd15_1_25 : subd15_1 [-1, 0, -1] = true := by decide +kernel
theorem subd15_1_26 : subd15_1 [-1, 0, 0] = true := by decide +kernel
theorem subd15_1_27 : subd15_1 [-1, 0, 1] = true := by decide +kernel
theorem subd15_1_28 : subd15_1 [-1, 0, 2] = true := by decide +kernel
theorem subd15_1_29 : subd15_1 [-1, 0, 3] = true := by decide +kernel
theorem subd15_1_30 : subd15_1 [-1, 0, 4] = true := by decide +kernel
theorem subd15_1_31 : subd15_1 [-1, 0, 5] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_cons.2 ⟨subd15_1_1, List.forall_mem_cons.2 ⟨subd15_1_2, List.forall_mem_cons.2 ⟨subd15_1_3, List.forall_mem_cons.2 ⟨subd15_1_4, List.forall_mem_cons.2 ⟨subd15_1_5, List.forall_mem_cons.2 ⟨subd15_1_6, List.forall_mem_cons.2 ⟨subd15_1_7, List.forall_mem_cons.2 ⟨subd15_1_8, List.forall_mem_cons.2 ⟨subd15_1_9, List.forall_mem_cons.2 ⟨subd15_1_10, List.forall_mem_cons.2 ⟨subd15_1_11, List.forall_mem_cons.2 ⟨subd15_1_12, List.forall_mem_cons.2 ⟨subd15_1_13, List.forall_mem_cons.2 ⟨subd15_1_14, List.forall_mem_cons.2 ⟨subd15_1_15, List.forall_mem_cons.2 ⟨subd15_1_16, List.forall_mem_cons.2 ⟨subd15_1_17, List.forall_mem_cons.2 ⟨subd15_1_18, List.forall_mem_cons.2 ⟨subd15_1_19, List.forall_mem_cons.2 ⟨subd15_1_20, List.forall_mem_cons.2 ⟨subd15_1_21, List.forall_mem_cons.2 ⟨subd15_1_22, List.forall_mem_cons.2 ⟨subd15_1_23, List.forall_mem_cons.2 ⟨subd15_1_24, List.forall_mem_cons.2 ⟨subd15_1_25, List.forall_mem_cons.2 ⟨subd15_1_26, List.forall_mem_cons.2 ⟨subd15_1_27, List.forall_mem_cons.2 ⟨subd15_1_28, List.forall_mem_cons.2 ⟨subd15_1_29, List.forall_mem_cons.2 ⟨subd15_1_30, List.forall_mem_cons.2 ⟨subd15_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_32 : subd15_1 [-1, 0, 6] = true := by decide +kernel
theorem subd15_1_33 : subd15_1 [-1, 0, 7] = true := by decide +kernel
theorem subd15_1_34 : subd15_1 [-1, 0, 8] = true := by decide +kernel
theorem subd15_1_35 : subd15_1 [-1, 0, 9] = true := by decide +kernel
theorem subd15_1_36 : subd15_1 [-1, 1] = true := by decide +kernel
theorem subd15_1_37 : subd15_1 [0, -2] = true := by decide +kernel
theorem subd15_1_38 : subd15_1 [0, -1, -10] = true := by decide +kernel
theorem subd15_1_39 : subd15_1 [0, -1, -9] = true := by decide +kernel
theorem subd15_1_40 : subd15_1 [0, -1, -8] = true := by decide +kernel
theorem subd15_1_41 : subd15_1 [0, -1, -7] = true := by decide +kernel
theorem subd15_1_42 : subd15_1 [0, -1, -6] = true := by decide +kernel
theorem subd15_1_43 : subd15_1 [0, -1, -5] = true := by decide +kernel
theorem subd15_1_44 : subd15_1 [0, -1, -4] = true := by decide +kernel
theorem subd15_1_45 : subd15_1 [0, -1, -3] = true := by decide +kernel
theorem subd15_1_46 : subd15_1 [0, -1, -2] = true := by decide +kernel
theorem subd15_1_47 : subd15_1 [0, -1, -1] = true := by decide +kernel
theorem subd15_1_48 : subd15_1 [0, -1, 0] = true := by decide +kernel
theorem subd15_1_49 : subd15_1 [0, -1, 1] = true := by decide +kernel
theorem subd15_1_50 : subd15_1 [0, -1, 2] = true := by decide +kernel
theorem subd15_1_51 : subd15_1 [0, -1, 3] = true := by decide +kernel
theorem subd15_1_52 : subd15_1 [0, -1, 4] = true := by decide +kernel
theorem subd15_1_53 : subd15_1 [0, -1, 5] = true := by decide +kernel
theorem subd15_1_54 : subd15_1 [0, -1, 6] = true := by decide +kernel
theorem subd15_1_55 : subd15_1 [0, -1, 7] = true := by decide +kernel
theorem subd15_1_56 : subd15_1 [0, -1, 8] = true := by decide +kernel
theorem subd15_1_57 : subd15_1 [0, -1, 9] = true := by decide +kernel
theorem subd15_1_58 : subd15_1 [0, -1, 10] = true := by decide +kernel
theorem subd15_1_59 : subd15_1 [0, 0, -13] = true := by decide +kernel
theorem subd15_1_60 : subd15_1 [0, 0, -12] = true := by decide +kernel
theorem subd15_1_61 : subd15_1 [0, 0, -11] = true := by decide +kernel
theorem subd15_1_62 : subd15_1 [0, 0, -10] = true := by decide +kernel
theorem subd15_1_63 : subd15_1 [0, 0, -9] = true := by decide +kernel
theorem sbd15_1_1 : ∀ q ∈ blkd15_1_1, subd15_1 q = true := by
  unfold blkd15_1_1
  exact List.forall_mem_cons.2 ⟨subd15_1_32, List.forall_mem_cons.2 ⟨subd15_1_33, List.forall_mem_cons.2 ⟨subd15_1_34, List.forall_mem_cons.2 ⟨subd15_1_35, List.forall_mem_cons.2 ⟨subd15_1_36, List.forall_mem_cons.2 ⟨subd15_1_37, List.forall_mem_cons.2 ⟨subd15_1_38, List.forall_mem_cons.2 ⟨subd15_1_39, List.forall_mem_cons.2 ⟨subd15_1_40, List.forall_mem_cons.2 ⟨subd15_1_41, List.forall_mem_cons.2 ⟨subd15_1_42, List.forall_mem_cons.2 ⟨subd15_1_43, List.forall_mem_cons.2 ⟨subd15_1_44, List.forall_mem_cons.2 ⟨subd15_1_45, List.forall_mem_cons.2 ⟨subd15_1_46, List.forall_mem_cons.2 ⟨subd15_1_47, List.forall_mem_cons.2 ⟨subd15_1_48, List.forall_mem_cons.2 ⟨subd15_1_49, List.forall_mem_cons.2 ⟨subd15_1_50, List.forall_mem_cons.2 ⟨subd15_1_51, List.forall_mem_cons.2 ⟨subd15_1_52, List.forall_mem_cons.2 ⟨subd15_1_53, List.forall_mem_cons.2 ⟨subd15_1_54, List.forall_mem_cons.2 ⟨subd15_1_55, List.forall_mem_cons.2 ⟨subd15_1_56, List.forall_mem_cons.2 ⟨subd15_1_57, List.forall_mem_cons.2 ⟨subd15_1_58, List.forall_mem_cons.2 ⟨subd15_1_59, List.forall_mem_cons.2 ⟨subd15_1_60, List.forall_mem_cons.2 ⟨subd15_1_61, List.forall_mem_cons.2 ⟨subd15_1_62, List.forall_mem_cons.2 ⟨subd15_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_64 : subd15_1 [0, 0, -8] = true := by decide +kernel
theorem subd15_1_65 : subd15_1 [0, 0, -7] = true := by decide +kernel
theorem subd15_1_66 : subd15_1 [0, 0, -6] = true := by decide +kernel
theorem subd15_1_67 : subd15_1 [0, 0, -5] = true := by decide +kernel
theorem subd15_1_68 : subd15_1 [0, 0, -4] = true := by decide +kernel
theorem subd15_1_69 : subd15_1 [0, 0, -3] = true := by decide +kernel
theorem subd15_1_70 : subd15_1 [0, 0, -2] = true := by decide +kernel
theorem subd15_1_71 : subd15_1 [0, 0, -1] = true := by decide +kernel
theorem subd15_1_72 : subd15_1 [0, 0, 0] = true := by decide +kernel
theorem subd15_1_73 : subd15_1 [0, 0, 1] = true := by decide +kernel
theorem subd15_1_74 : subd15_1 [0, 0, 2] = true := by decide +kernel
theorem subd15_1_75 : subd15_1 [0, 0, 3] = true := by decide +kernel
theorem subd15_1_76 : subd15_1 [0, 0, 4] = true := by decide +kernel
theorem subd15_1_77 : subd15_1 [0, 0, 5] = true := by decide +kernel
theorem subd15_1_78 : subd15_1 [0, 0, 6] = true := by decide +kernel
theorem subd15_1_79 : subd15_1 [0, 0, 7] = true := by decide +kernel
theorem subd15_1_80 : subd15_1 [0, 0, 8] = true := by decide +kernel
theorem subd15_1_81 : subd15_1 [0, 0, 9] = true := by decide +kernel
theorem subd15_1_82 : subd15_1 [0, 0, 10] = true := by decide +kernel
theorem subd15_1_83 : subd15_1 [0, 0, 11] = true := by decide +kernel
theorem subd15_1_84 : subd15_1 [0, 0, 12] = true := by decide +kernel
theorem subd15_1_85 : subd15_1 [0, 1, -11] = true := by decide +kernel
theorem subd15_1_86 : subd15_1 [0, 1, -10] = true := by decide +kernel
theorem subd15_1_87 : subd15_1 [0, 1, -9] = true := by decide +kernel
theorem subd15_1_88 : subd15_1 [0, 1, -8] = true := by decide +kernel
theorem subd15_1_89 : subd15_1 [0, 1, -7] = true := by decide +kernel
theorem subd15_1_90 : subd15_1 [0, 1, -6] = true := by decide +kernel
theorem subd15_1_91 : subd15_1 [0, 1, -5] = true := by decide +kernel
theorem subd15_1_92 : subd15_1 [0, 1, -4] = true := by decide +kernel
theorem subd15_1_93 : subd15_1 [0, 1, -3] = true := by decide +kernel
theorem subd15_1_94 : subd15_1 [0, 1, -2] = true := by decide +kernel
theorem subd15_1_95 : subd15_1 [0, 1, -1] = true := by decide +kernel
theorem sbd15_1_2 : ∀ q ∈ blkd15_1_2, subd15_1 q = true := by
  unfold blkd15_1_2
  exact List.forall_mem_cons.2 ⟨subd15_1_64, List.forall_mem_cons.2 ⟨subd15_1_65, List.forall_mem_cons.2 ⟨subd15_1_66, List.forall_mem_cons.2 ⟨subd15_1_67, List.forall_mem_cons.2 ⟨subd15_1_68, List.forall_mem_cons.2 ⟨subd15_1_69, List.forall_mem_cons.2 ⟨subd15_1_70, List.forall_mem_cons.2 ⟨subd15_1_71, List.forall_mem_cons.2 ⟨subd15_1_72, List.forall_mem_cons.2 ⟨subd15_1_73, List.forall_mem_cons.2 ⟨subd15_1_74, List.forall_mem_cons.2 ⟨subd15_1_75, List.forall_mem_cons.2 ⟨subd15_1_76, List.forall_mem_cons.2 ⟨subd15_1_77, List.forall_mem_cons.2 ⟨subd15_1_78, List.forall_mem_cons.2 ⟨subd15_1_79, List.forall_mem_cons.2 ⟨subd15_1_80, List.forall_mem_cons.2 ⟨subd15_1_81, List.forall_mem_cons.2 ⟨subd15_1_82, List.forall_mem_cons.2 ⟨subd15_1_83, List.forall_mem_cons.2 ⟨subd15_1_84, List.forall_mem_cons.2 ⟨subd15_1_85, List.forall_mem_cons.2 ⟨subd15_1_86, List.forall_mem_cons.2 ⟨subd15_1_87, List.forall_mem_cons.2 ⟨subd15_1_88, List.forall_mem_cons.2 ⟨subd15_1_89, List.forall_mem_cons.2 ⟨subd15_1_90, List.forall_mem_cons.2 ⟨subd15_1_91, List.forall_mem_cons.2 ⟨subd15_1_92, List.forall_mem_cons.2 ⟨subd15_1_93, List.forall_mem_cons.2 ⟨subd15_1_94, List.forall_mem_cons.2 ⟨subd15_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_96 : subd15_1 [0, 1, 0] = true := by decide +kernel
theorem subd15_1_97 : subd15_1 [0, 1, 1] = true := by decide +kernel
theorem subd15_1_98 : subd15_1 [0, 1, 2] = true := by decide +kernel
theorem subd15_1_99 : subd15_1 [0, 1, 3] = true := by decide +kernel
theorem subd15_1_100 : subd15_1 [0, 1, 4] = true := by decide +kernel
theorem subd15_1_101 : subd15_1 [0, 1, 5] = true := by decide +kernel
theorem subd15_1_102 : subd15_1 [0, 1, 6] = true := by decide +kernel
theorem subd15_1_103 : subd15_1 [0, 1, 7] = true := by decide +kernel
theorem subd15_1_104 : subd15_1 [0, 1, 8] = true := by decide +kernel
theorem subd15_1_105 : subd15_1 [0, 1, 9] = true := by decide +kernel
theorem subd15_1_106 : subd15_1 [1, -2] = true := by decide +kernel
theorem subd15_1_107 : subd15_1 [1, -1] = true := by decide +kernel
theorem subd15_1_108 : subd15_1 [1, 0, -10] = true := by decide +kernel
theorem subd15_1_109 : subd15_1 [1, 0, -9] = true := by decide +kernel
theorem subd15_1_110 : subd15_1 [1, 0, -8] = true := by decide +kernel
theorem subd15_1_111 : subd15_1 [1, 0, -7] = true := by decide +kernel
theorem subd15_1_112 : subd15_1 [1, 0, -6] = true := by decide +kernel
theorem subd15_1_113 : subd15_1 [1, 0, -5] = true := by decide +kernel
theorem subd15_1_114 : subd15_1 [1, 0, -4] = true := by decide +kernel
theorem subd15_1_115 : subd15_1 [1, 0, -3] = true := by decide +kernel
theorem subd15_1_116 : subd15_1 [1, 0, -2] = true := by decide +kernel
theorem subd15_1_117 : subd15_1 [1, 0, -1] = true := by decide +kernel
theorem subd15_1_118 : subd15_1 [1, 0, 0] = true := by decide +kernel
theorem subd15_1_119 : subd15_1 [1, 0, 1] = true := by decide +kernel
theorem subd15_1_120 : subd15_1 [1, 0, 2] = true := by decide +kernel
theorem subd15_1_121 : subd15_1 [1, 0, 3] = true := by decide +kernel
theorem subd15_1_122 : subd15_1 [1, 0, 4] = true := by decide +kernel
theorem subd15_1_123 : subd15_1 [1, 0, 5] = true := by decide +kernel
theorem subd15_1_124 : subd15_1 [1, 0, 6] = true := by decide +kernel
theorem subd15_1_125 : subd15_1 [1, 0, 7] = true := by decide +kernel
theorem subd15_1_126 : subd15_1 [1, 0, 8] = true := by decide +kernel
theorem subd15_1_127 : subd15_1 [1, 0, 9] = true := by decide +kernel
theorem sbd15_1_3 : ∀ q ∈ blkd15_1_3, subd15_1 q = true := by
  unfold blkd15_1_3
  exact List.forall_mem_cons.2 ⟨subd15_1_96, List.forall_mem_cons.2 ⟨subd15_1_97, List.forall_mem_cons.2 ⟨subd15_1_98, List.forall_mem_cons.2 ⟨subd15_1_99, List.forall_mem_cons.2 ⟨subd15_1_100, List.forall_mem_cons.2 ⟨subd15_1_101, List.forall_mem_cons.2 ⟨subd15_1_102, List.forall_mem_cons.2 ⟨subd15_1_103, List.forall_mem_cons.2 ⟨subd15_1_104, List.forall_mem_cons.2 ⟨subd15_1_105, List.forall_mem_cons.2 ⟨subd15_1_106, List.forall_mem_cons.2 ⟨subd15_1_107, List.forall_mem_cons.2 ⟨subd15_1_108, List.forall_mem_cons.2 ⟨subd15_1_109, List.forall_mem_cons.2 ⟨subd15_1_110, List.forall_mem_cons.2 ⟨subd15_1_111, List.forall_mem_cons.2 ⟨subd15_1_112, List.forall_mem_cons.2 ⟨subd15_1_113, List.forall_mem_cons.2 ⟨subd15_1_114, List.forall_mem_cons.2 ⟨subd15_1_115, List.forall_mem_cons.2 ⟨subd15_1_116, List.forall_mem_cons.2 ⟨subd15_1_117, List.forall_mem_cons.2 ⟨subd15_1_118, List.forall_mem_cons.2 ⟨subd15_1_119, List.forall_mem_cons.2 ⟨subd15_1_120, List.forall_mem_cons.2 ⟨subd15_1_121, List.forall_mem_cons.2 ⟨subd15_1_122, List.forall_mem_cons.2 ⟨subd15_1_123, List.forall_mem_cons.2 ⟨subd15_1_124, List.forall_mem_cons.2 ⟨subd15_1_125, List.forall_mem_cons.2 ⟨subd15_1_126, List.forall_mem_cons.2 ⟨subd15_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_128 : subd15_1 [1, 1, -8] = true := by decide +kernel
theorem subd15_1_129 : subd15_1 [1, 1, -7] = true := by decide +kernel
theorem subd15_1_130 : subd15_1 [1, 1, -6] = true := by decide +kernel
theorem subd15_1_131 : subd15_1 [1, 1, -5] = true := by decide +kernel
theorem subd15_1_132 : subd15_1 [1, 1, -4] = true := by decide +kernel
theorem subd15_1_133 : subd15_1 [1, 1, -3] = true := by decide +kernel
theorem subd15_1_134 : subd15_1 [1, 1, -2] = true := by decide +kernel
theorem subd15_1_135 : subd15_1 [1, 1, -1] = true := by decide +kernel
theorem subd15_1_136 : subd15_1 [1, 1, 0] = true := by decide +kernel
theorem subd15_1_137 : subd15_1 [1, 1, 1] = true := by decide +kernel
theorem subd15_1_138 : subd15_1 [1, 1, 2] = true := by decide +kernel
theorem subd15_1_139 : subd15_1 [1, 1, 3] = true := by decide +kernel
theorem subd15_1_140 : subd15_1 [1, 1, 4] = true := by decide +kernel
theorem subd15_1_141 : subd15_1 [1, 1, 5] = true := by decide +kernel
theorem subd15_1_142 : subd15_1 [1, 1, 6] = true := by decide +kernel
theorem sbd15_1_4 : ∀ q ∈ blkd15_1_4, subd15_1 q = true := by
  unfold blkd15_1_4
  exact List.forall_mem_cons.2 ⟨subd15_1_128, List.forall_mem_cons.2 ⟨subd15_1_129, List.forall_mem_cons.2 ⟨subd15_1_130, List.forall_mem_cons.2 ⟨subd15_1_131, List.forall_mem_cons.2 ⟨subd15_1_132, List.forall_mem_cons.2 ⟨subd15_1_133, List.forall_mem_cons.2 ⟨subd15_1_134, List.forall_mem_cons.2 ⟨subd15_1_135, List.forall_mem_cons.2 ⟨subd15_1_136, List.forall_mem_cons.2 ⟨subd15_1_137, List.forall_mem_cons.2 ⟨subd15_1_138, List.forall_mem_cons.2 ⟨subd15_1_139, List.forall_mem_cons.2 ⟨subd15_1_140, List.forall_mem_cons.2 ⟨subd15_1_141, List.forall_mem_cons.2 ⟨subd15_1_142, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
