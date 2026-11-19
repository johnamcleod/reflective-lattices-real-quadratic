import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_5_288 : subd8_5 [2, 0, -4] = true := by decide +kernel
theorem subd8_5_289 : subd8_5 [2, 0, -3] = true := by decide +kernel
theorem subd8_5_290 : subd8_5 [2, 0, -2] = true := by decide +kernel
theorem subd8_5_291 : subd8_5 [2, 0, -1] = true := by decide +kernel
theorem subd8_5_292 : subd8_5 [2, 0, 0] = true := by decide +kernel
theorem subd8_5_293 : subd8_5 [2, 0, 1] = true := by decide +kernel
theorem subd8_5_294 : subd8_5 [2, 0, 2] = true := by decide +kernel
theorem subd8_5_295 : subd8_5 [2, 0, 3] = true := by decide +kernel
theorem subd8_5_296 : subd8_5 [2, 0, 4] = true := by decide +kernel
theorem subd8_5_297 : subd8_5 [2, 0, 5] = true := by decide +kernel
theorem subd8_5_298 : subd8_5 [2, 1, -8] = true := by decide +kernel
theorem subd8_5_299 : subd8_5 [2, 1, -7] = true := by decide +kernel
theorem subd8_5_300 : subd8_5 [2, 1, -6] = true := by decide +kernel
theorem subd8_5_301 : subd8_5 [2, 1, -5] = true := by decide +kernel
theorem subd8_5_302 : subd8_5 [2, 1, -4] = true := by decide +kernel
theorem subd8_5_303 : subd8_5 [2, 1, -3] = true := by decide +kernel
theorem subd8_5_304 : subd8_5 [2, 1, -2] = true := by decide +kernel
theorem subd8_5_305 : subd8_5 [2, 1, -1] = true := by decide +kernel
theorem subd8_5_306 : subd8_5 [2, 1, 0] = true := by decide +kernel
theorem subd8_5_307 : subd8_5 [2, 1, 1] = true := by decide +kernel
theorem subd8_5_308 : subd8_5 [2, 1, 2] = true := by decide +kernel
theorem subd8_5_309 : subd8_5 [2, 1, 3] = true := by decide +kernel
theorem subd8_5_310 : subd8_5 [2, 1, 4] = true := by decide +kernel
theorem subd8_5_311 : subd8_5 [2, 1, 5] = true := by decide +kernel
theorem subd8_5_312 : subd8_5 [2, 2] = true := by decide +kernel
theorem subd8_5_313 : subd8_5 [2, 3] = true := by decide +kernel
theorem subd8_5_314 : subd8_5 [2, 4] = true := by decide +kernel
theorem subd8_5_315 : subd8_5 [3, -4] = true := by decide +kernel
theorem subd8_5_316 : subd8_5 [3, -3] = true := by decide +kernel
theorem subd8_5_317 : subd8_5 [3, -2] = true := by decide +kernel
theorem subd8_5_318 : subd8_5 [3, -1] = true := by decide +kernel
theorem subd8_5_319 : subd8_5 [3, 0] = true := by decide +kernel
theorem sbd8_5_9 : ∀ q ∈ blkd8_5_9, subd8_5 q = true := by
  unfold blkd8_5_9
  exact List.forall_mem_cons.2 ⟨subd8_5_288, List.forall_mem_cons.2 ⟨subd8_5_289, List.forall_mem_cons.2 ⟨subd8_5_290, List.forall_mem_cons.2 ⟨subd8_5_291, List.forall_mem_cons.2 ⟨subd8_5_292, List.forall_mem_cons.2 ⟨subd8_5_293, List.forall_mem_cons.2 ⟨subd8_5_294, List.forall_mem_cons.2 ⟨subd8_5_295, List.forall_mem_cons.2 ⟨subd8_5_296, List.forall_mem_cons.2 ⟨subd8_5_297, List.forall_mem_cons.2 ⟨subd8_5_298, List.forall_mem_cons.2 ⟨subd8_5_299, List.forall_mem_cons.2 ⟨subd8_5_300, List.forall_mem_cons.2 ⟨subd8_5_301, List.forall_mem_cons.2 ⟨subd8_5_302, List.forall_mem_cons.2 ⟨subd8_5_303, List.forall_mem_cons.2 ⟨subd8_5_304, List.forall_mem_cons.2 ⟨subd8_5_305, List.forall_mem_cons.2 ⟨subd8_5_306, List.forall_mem_cons.2 ⟨subd8_5_307, List.forall_mem_cons.2 ⟨subd8_5_308, List.forall_mem_cons.2 ⟨subd8_5_309, List.forall_mem_cons.2 ⟨subd8_5_310, List.forall_mem_cons.2 ⟨subd8_5_311, List.forall_mem_cons.2 ⟨subd8_5_312, List.forall_mem_cons.2 ⟨subd8_5_313, List.forall_mem_cons.2 ⟨subd8_5_314, List.forall_mem_cons.2 ⟨subd8_5_315, List.forall_mem_cons.2 ⟨subd8_5_316, List.forall_mem_cons.2 ⟨subd8_5_317, List.forall_mem_cons.2 ⟨subd8_5_318, List.forall_mem_cons.2 ⟨subd8_5_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_320 : subd8_5 [3, 1] = true := by decide +kernel
theorem subd8_5_321 : subd8_5 [3, 2] = true := by decide +kernel
theorem subd8_5_322 : subd8_5 [3, 3] = true := by decide +kernel
theorem subd8_5_323 : subd8_5 [3, 4] = true := by decide +kernel
theorem subd8_5_324 : subd8_5 [4, -3] = true := by decide +kernel
theorem subd8_5_325 : subd8_5 [4, -2] = true := by decide +kernel
theorem subd8_5_326 : subd8_5 [4, -1] = true := by decide +kernel
theorem subd8_5_327 : subd8_5 [4, 0] = true := by decide +kernel
theorem subd8_5_328 : subd8_5 [4, 1] = true := by decide +kernel
theorem subd8_5_329 : subd8_5 [4, 2] = true := by decide +kernel
theorem subd8_5_330 : subd8_5 [4, 3] = true := by decide +kernel
theorem subd8_5_331 : subd8_5 [4, 4] = true := by decide +kernel
theorem subd8_5_332 : subd8_5 [5] = true := by decide +kernel
theorem sbd8_5_10 : ∀ q ∈ blkd8_5_10, subd8_5 q = true := by
  unfold blkd8_5_10
  exact List.forall_mem_cons.2 ⟨subd8_5_320, List.forall_mem_cons.2 ⟨subd8_5_321, List.forall_mem_cons.2 ⟨subd8_5_322, List.forall_mem_cons.2 ⟨subd8_5_323, List.forall_mem_cons.2 ⟨subd8_5_324, List.forall_mem_cons.2 ⟨subd8_5_325, List.forall_mem_cons.2 ⟨subd8_5_326, List.forall_mem_cons.2 ⟨subd8_5_327, List.forall_mem_cons.2 ⟨subd8_5_328, List.forall_mem_cons.2 ⟨subd8_5_329, List.forall_mem_cons.2 ⟨subd8_5_330, List.forall_mem_cons.2 ⟨subd8_5_331, List.forall_mem_cons.2 ⟨subd8_5_332, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_6 : ldCheck G d8_6.U d8_6.ms ldd8_6 = true := by decide +kernel
theorem pre_okd8_6 : subPre G cell8 d8_6 = true := by decide +kernel
theorem subd8_6_0 : subd8_6 [-6] = true := by decide +kernel
theorem subd8_6_1 : subd8_6 [-5, -3] = true := by decide +kernel
theorem subd8_6_2 : subd8_6 [-5, -2] = true := by decide +kernel
theorem subd8_6_3 : subd8_6 [-5, -1] = true := by decide +kernel
theorem subd8_6_4 : subd8_6 [-5, 0] = true := by decide +kernel
theorem subd8_6_5 : subd8_6 [-5, 1] = true := by decide +kernel
theorem subd8_6_6 : subd8_6 [-5, 2] = true := by decide +kernel
theorem subd8_6_7 : subd8_6 [-5, 3] = true := by decide +kernel
theorem subd8_6_8 : subd8_6 [-5, 4] = true := by decide +kernel
theorem subd8_6_9 : subd8_6 [-5, 5] = true := by decide +kernel
theorem subd8_6_10 : subd8_6 [-4, -5] = true := by decide +kernel
theorem subd8_6_11 : subd8_6 [-4, -4] = true := by decide +kernel
theorem subd8_6_12 : subd8_6 [-4, -3] = true := by decide +kernel
theorem subd8_6_13 : subd8_6 [-4, -2] = true := by decide +kernel
theorem subd8_6_14 : subd8_6 [-4, -1] = true := by decide +kernel
theorem subd8_6_15 : subd8_6 [-4, 0] = true := by decide +kernel
theorem subd8_6_16 : subd8_6 [-4, 1] = true := by decide +kernel
theorem subd8_6_17 : subd8_6 [-4, 2] = true := by decide +kernel
theorem subd8_6_18 : subd8_6 [-4, 3] = true := by decide +kernel
theorem subd8_6_19 : subd8_6 [-4, 4] = true := by decide +kernel
theorem subd8_6_20 : subd8_6 [-4, 5] = true := by decide +kernel
theorem subd8_6_21 : subd8_6 [-4, 6] = true := by decide +kernel
theorem subd8_6_22 : subd8_6 [-3, -6] = true := by decide +kernel
theorem subd8_6_23 : subd8_6 [-3, -5] = true := by decide +kernel
theorem subd8_6_24 : subd8_6 [-3, -4] = true := by decide +kernel
theorem subd8_6_25 : subd8_6 [-3, -3] = true := by decide +kernel
theorem subd8_6_26 : subd8_6 [-3, -2] = true := by decide +kernel
theorem subd8_6_27 : subd8_6 [-3, -1] = true := by decide +kernel
theorem subd8_6_28 : subd8_6 [-3, 0] = true := by decide +kernel
theorem subd8_6_29 : subd8_6 [-3, 1] = true := by decide +kernel
theorem subd8_6_30 : subd8_6 [-3, 2] = true := by decide +kernel
theorem subd8_6_31 : subd8_6 [-3, 3] = true := by decide +kernel
theorem sbd8_6_0 : ∀ q ∈ blkd8_6_0, subd8_6 q = true := by
  unfold blkd8_6_0
  exact List.forall_mem_cons.2 ⟨subd8_6_0, List.forall_mem_cons.2 ⟨subd8_6_1, List.forall_mem_cons.2 ⟨subd8_6_2, List.forall_mem_cons.2 ⟨subd8_6_3, List.forall_mem_cons.2 ⟨subd8_6_4, List.forall_mem_cons.2 ⟨subd8_6_5, List.forall_mem_cons.2 ⟨subd8_6_6, List.forall_mem_cons.2 ⟨subd8_6_7, List.forall_mem_cons.2 ⟨subd8_6_8, List.forall_mem_cons.2 ⟨subd8_6_9, List.forall_mem_cons.2 ⟨subd8_6_10, List.forall_mem_cons.2 ⟨subd8_6_11, List.forall_mem_cons.2 ⟨subd8_6_12, List.forall_mem_cons.2 ⟨subd8_6_13, List.forall_mem_cons.2 ⟨subd8_6_14, List.forall_mem_cons.2 ⟨subd8_6_15, List.forall_mem_cons.2 ⟨subd8_6_16, List.forall_mem_cons.2 ⟨subd8_6_17, List.forall_mem_cons.2 ⟨subd8_6_18, List.forall_mem_cons.2 ⟨subd8_6_19, List.forall_mem_cons.2 ⟨subd8_6_20, List.forall_mem_cons.2 ⟨subd8_6_21, List.forall_mem_cons.2 ⟨subd8_6_22, List.forall_mem_cons.2 ⟨subd8_6_23, List.forall_mem_cons.2 ⟨subd8_6_24, List.forall_mem_cons.2 ⟨subd8_6_25, List.forall_mem_cons.2 ⟨subd8_6_26, List.forall_mem_cons.2 ⟨subd8_6_27, List.forall_mem_cons.2 ⟨subd8_6_28, List.forall_mem_cons.2 ⟨subd8_6_29, List.forall_mem_cons.2 ⟨subd8_6_30, List.forall_mem_cons.2 ⟨subd8_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_6_32 : subd8_6 [-3, 4] = true := by decide +kernel
theorem subd8_6_33 : subd8_6 [-3, 5] = true := by decide +kernel
theorem subd8_6_34 : subd8_6 [-3, 6] = true := by decide +kernel
theorem subd8_6_35 : subd8_6 [-2, -6] = true := by decide +kernel
theorem subd8_6_36 : subd8_6 [-2, -5] = true := by decide +kernel
theorem subd8_6_37 : subd8_6 [-2, -4] = true := by decide +kernel
theorem subd8_6_38 : subd8_6 [-2, -3] = true := by decide +kernel
theorem subd8_6_39 : subd8_6 [-2, -2] = true := by decide +kernel
theorem subd8_6_40 : subd8_6 [-2, -1] = true := by decide +kernel
theorem subd8_6_41 : subd8_6 [-2, 0] = true := by decide +kernel
theorem subd8_6_42 : subd8_6 [-2, 1] = true := by decide +kernel
theorem subd8_6_43 : subd8_6 [-2, 2] = true := by decide +kernel
theorem subd8_6_44 : subd8_6 [-2, 3] = true := by decide +kernel
theorem subd8_6_45 : subd8_6 [-2, 4] = true := by decide +kernel
theorem subd8_6_46 : subd8_6 [-2, 5] = true := by decide +kernel
theorem subd8_6_47 : subd8_6 [-2, 6] = true := by decide +kernel
theorem subd8_6_48 : subd8_6 [-2, 7] = true := by decide +kernel
theorem subd8_6_49 : subd8_6 [-1, -7] = true := by decide +kernel
theorem subd8_6_50 : subd8_6 [-1, -6] = true := by decide +kernel
theorem subd8_6_51 : subd8_6 [-1, -5] = true := by decide +kernel
theorem subd8_6_52 : subd8_6 [-1, -4] = true := by decide +kernel
theorem subd8_6_53 : subd8_6 [-1, -3] = true := by decide +kernel
theorem subd8_6_54 : subd8_6 [-1, -2] = true := by decide +kernel
theorem subd8_6_55 : subd8_6 [-1, -1] = true := by decide +kernel
theorem subd8_6_56 : subd8_6 [-1, 0] = true := by decide +kernel
theorem subd8_6_57 : subd8_6 [-1, 1, -7] = true := by decide +kernel
theorem subd8_6_58 : subd8_6 [-1, 1, -6] = true := by decide +kernel
theorem subd8_6_59 : subd8_6 [-1, 1, -5] = true := by decide +kernel
theorem subd8_6_60 : subd8_6 [-1, 1, -4] = true := by decide +kernel
theorem subd8_6_61 : subd8_6 [-1, 1, -3] = true := by decide +kernel
theorem subd8_6_62 : subd8_6 [-1, 1, -2] = true := by decide +kernel
theorem subd8_6_63 : subd8_6 [-1, 1, -1] = true := by decide +kernel
theorem sbd8_6_1 : ∀ q ∈ blkd8_6_1, subd8_6 q = true := by
  unfold blkd8_6_1
  exact List.forall_mem_cons.2 ⟨subd8_6_32, List.forall_mem_cons.2 ⟨subd8_6_33, List.forall_mem_cons.2 ⟨subd8_6_34, List.forall_mem_cons.2 ⟨subd8_6_35, List.forall_mem_cons.2 ⟨subd8_6_36, List.forall_mem_cons.2 ⟨subd8_6_37, List.forall_mem_cons.2 ⟨subd8_6_38, List.forall_mem_cons.2 ⟨subd8_6_39, List.forall_mem_cons.2 ⟨subd8_6_40, List.forall_mem_cons.2 ⟨subd8_6_41, List.forall_mem_cons.2 ⟨subd8_6_42, List.forall_mem_cons.2 ⟨subd8_6_43, List.forall_mem_cons.2 ⟨subd8_6_44, List.forall_mem_cons.2 ⟨subd8_6_45, List.forall_mem_cons.2 ⟨subd8_6_46, List.forall_mem_cons.2 ⟨subd8_6_47, List.forall_mem_cons.2 ⟨subd8_6_48, List.forall_mem_cons.2 ⟨subd8_6_49, List.forall_mem_cons.2 ⟨subd8_6_50, List.forall_mem_cons.2 ⟨subd8_6_51, List.forall_mem_cons.2 ⟨subd8_6_52, List.forall_mem_cons.2 ⟨subd8_6_53, List.forall_mem_cons.2 ⟨subd8_6_54, List.forall_mem_cons.2 ⟨subd8_6_55, List.forall_mem_cons.2 ⟨subd8_6_56, List.forall_mem_cons.2 ⟨subd8_6_57, List.forall_mem_cons.2 ⟨subd8_6_58, List.forall_mem_cons.2 ⟨subd8_6_59, List.forall_mem_cons.2 ⟨subd8_6_60, List.forall_mem_cons.2 ⟨subd8_6_61, List.forall_mem_cons.2 ⟨subd8_6_62, List.forall_mem_cons.2 ⟨subd8_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
