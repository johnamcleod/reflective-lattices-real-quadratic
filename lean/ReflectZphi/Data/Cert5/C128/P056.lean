import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_4_352 : subd8_4 [2, 0, -6] = true := by decide +kernel
theorem subd8_4_353 : subd8_4 [2, 0, -5] = true := by decide +kernel
theorem subd8_4_354 : subd8_4 [2, 0, -4] = true := by decide +kernel
theorem subd8_4_355 : subd8_4 [2, 0, -3] = true := by decide +kernel
theorem subd8_4_356 : subd8_4 [2, 0, -2] = true := by decide +kernel
theorem subd8_4_357 : subd8_4 [2, 0, -1] = true := by decide +kernel
theorem subd8_4_358 : subd8_4 [2, 0, 0] = true := by decide +kernel
theorem subd8_4_359 : subd8_4 [2, 0, 1] = true := by decide +kernel
theorem subd8_4_360 : subd8_4 [2, 0, 2] = true := by decide +kernel
theorem subd8_4_361 : subd8_4 [2, 0, 3] = true := by decide +kernel
theorem subd8_4_362 : subd8_4 [2, 0, 4] = true := by decide +kernel
theorem subd8_4_363 : subd8_4 [2, 0, 5] = true := by decide +kernel
theorem subd8_4_364 : subd8_4 [2, 0, 6] = true := by decide +kernel
theorem subd8_4_365 : subd8_4 [2, 0, 7] = true := by decide +kernel
theorem subd8_4_366 : subd8_4 [2, 1, -8] = true := by decide +kernel
theorem subd8_4_367 : subd8_4 [2, 1, -7] = true := by decide +kernel
theorem subd8_4_368 : subd8_4 [2, 1, -6] = true := by decide +kernel
theorem subd8_4_369 : subd8_4 [2, 1, -5] = true := by decide +kernel
theorem subd8_4_370 : subd8_4 [2, 1, -4] = true := by decide +kernel
theorem subd8_4_371 : subd8_4 [2, 1, -3] = true := by decide +kernel
theorem subd8_4_372 : subd8_4 [2, 1, -2] = true := by decide +kernel
theorem subd8_4_373 : subd8_4 [2, 1, -1] = true := by decide +kernel
theorem subd8_4_374 : subd8_4 [2, 1, 0] = true := by decide +kernel
theorem subd8_4_375 : subd8_4 [2, 1, 1] = true := by decide +kernel
theorem subd8_4_376 : subd8_4 [2, 1, 2] = true := by decide +kernel
theorem subd8_4_377 : subd8_4 [2, 1, 3] = true := by decide +kernel
theorem subd8_4_378 : subd8_4 [2, 1, 4] = true := by decide +kernel
theorem subd8_4_379 : subd8_4 [2, 1, 5] = true := by decide +kernel
theorem subd8_4_380 : subd8_4 [2, 1, 6] = true := by decide +kernel
theorem subd8_4_381 : subd8_4 [2, 1, 7] = true := by decide +kernel
theorem subd8_4_382 : subd8_4 [2, 1, 8] = true := by decide +kernel
theorem subd8_4_383 : subd8_4 [2, 2, -7] = true := by decide +kernel
theorem sbd8_4_11 : ∀ q ∈ blkd8_4_11, subd8_4 q = true := by
  unfold blkd8_4_11
  exact List.forall_mem_cons.2 ⟨subd8_4_352, List.forall_mem_cons.2 ⟨subd8_4_353, List.forall_mem_cons.2 ⟨subd8_4_354, List.forall_mem_cons.2 ⟨subd8_4_355, List.forall_mem_cons.2 ⟨subd8_4_356, List.forall_mem_cons.2 ⟨subd8_4_357, List.forall_mem_cons.2 ⟨subd8_4_358, List.forall_mem_cons.2 ⟨subd8_4_359, List.forall_mem_cons.2 ⟨subd8_4_360, List.forall_mem_cons.2 ⟨subd8_4_361, List.forall_mem_cons.2 ⟨subd8_4_362, List.forall_mem_cons.2 ⟨subd8_4_363, List.forall_mem_cons.2 ⟨subd8_4_364, List.forall_mem_cons.2 ⟨subd8_4_365, List.forall_mem_cons.2 ⟨subd8_4_366, List.forall_mem_cons.2 ⟨subd8_4_367, List.forall_mem_cons.2 ⟨subd8_4_368, List.forall_mem_cons.2 ⟨subd8_4_369, List.forall_mem_cons.2 ⟨subd8_4_370, List.forall_mem_cons.2 ⟨subd8_4_371, List.forall_mem_cons.2 ⟨subd8_4_372, List.forall_mem_cons.2 ⟨subd8_4_373, List.forall_mem_cons.2 ⟨subd8_4_374, List.forall_mem_cons.2 ⟨subd8_4_375, List.forall_mem_cons.2 ⟨subd8_4_376, List.forall_mem_cons.2 ⟨subd8_4_377, List.forall_mem_cons.2 ⟨subd8_4_378, List.forall_mem_cons.2 ⟨subd8_4_379, List.forall_mem_cons.2 ⟨subd8_4_380, List.forall_mem_cons.2 ⟨subd8_4_381, List.forall_mem_cons.2 ⟨subd8_4_382, List.forall_mem_cons.2 ⟨subd8_4_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_384 : subd8_4 [2, 2, -6] = true := by decide +kernel
theorem subd8_4_385 : subd8_4 [2, 2, -5] = true := by decide +kernel
theorem subd8_4_386 : subd8_4 [2, 2, -4] = true := by decide +kernel
theorem subd8_4_387 : subd8_4 [2, 2, -3] = true := by decide +kernel
theorem subd8_4_388 : subd8_4 [2, 2, -2] = true := by decide +kernel
theorem subd8_4_389 : subd8_4 [2, 2, -1] = true := by decide +kernel
theorem subd8_4_390 : subd8_4 [2, 2, 0] = true := by decide +kernel
theorem subd8_4_391 : subd8_4 [2, 2, 1] = true := by decide +kernel
theorem subd8_4_392 : subd8_4 [2, 2, 2] = true := by decide +kernel
theorem subd8_4_393 : subd8_4 [2, 2, 3] = true := by decide +kernel
theorem subd8_4_394 : subd8_4 [2, 2, 4] = true := by decide +kernel
theorem subd8_4_395 : subd8_4 [2, 2, 5] = true := by decide +kernel
theorem subd8_4_396 : subd8_4 [2, 2, 6] = true := by decide +kernel
theorem subd8_4_397 : subd8_4 [2, 2, 7] = true := by decide +kernel
theorem subd8_4_398 : subd8_4 [2, 3] = true := by decide +kernel
theorem sbd8_4_12 : ∀ q ∈ blkd8_4_12, subd8_4 q = true := by
  unfold blkd8_4_12
  exact List.forall_mem_cons.2 ⟨subd8_4_384, List.forall_mem_cons.2 ⟨subd8_4_385, List.forall_mem_cons.2 ⟨subd8_4_386, List.forall_mem_cons.2 ⟨subd8_4_387, List.forall_mem_cons.2 ⟨subd8_4_388, List.forall_mem_cons.2 ⟨subd8_4_389, List.forall_mem_cons.2 ⟨subd8_4_390, List.forall_mem_cons.2 ⟨subd8_4_391, List.forall_mem_cons.2 ⟨subd8_4_392, List.forall_mem_cons.2 ⟨subd8_4_393, List.forall_mem_cons.2 ⟨subd8_4_394, List.forall_mem_cons.2 ⟨subd8_4_395, List.forall_mem_cons.2 ⟨subd8_4_396, List.forall_mem_cons.2 ⟨subd8_4_397, List.forall_mem_cons.2 ⟨subd8_4_398, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_5 : ldCheck G d8_5.U d8_5.ms ldd8_5 = true := by decide +kernel
theorem pre_okd8_5 : subPre G cell8 d8_5 = true := by decide +kernel
theorem subd8_5_0 : subd8_5 [-5] = true := by decide +kernel
theorem subd8_5_1 : subd8_5 [-4, -5] = true := by decide +kernel
theorem subd8_5_2 : subd8_5 [-4, -4] = true := by decide +kernel
theorem subd8_5_3 : subd8_5 [-4, -3] = true := by decide +kernel
theorem subd8_5_4 : subd8_5 [-4, -2] = true := by decide +kernel
theorem subd8_5_5 : subd8_5 [-4, -1] = true := by decide +kernel
theorem subd8_5_6 : subd8_5 [-4, 0] = true := by decide +kernel
theorem subd8_5_7 : subd8_5 [-4, 1] = true := by decide +kernel
theorem subd8_5_8 : subd8_5 [-4, 2] = true := by decide +kernel
theorem subd8_5_9 : subd8_5 [-3, -5] = true := by decide +kernel
theorem subd8_5_10 : subd8_5 [-3, -4] = true := by decide +kernel
theorem subd8_5_11 : subd8_5 [-3, -3] = true := by decide +kernel
theorem subd8_5_12 : subd8_5 [-3, -2] = true := by decide +kernel
theorem subd8_5_13 : subd8_5 [-3, -1] = true := by decide +kernel
theorem subd8_5_14 : subd8_5 [-3, 0] = true := by decide +kernel
theorem subd8_5_15 : subd8_5 [-3, 1] = true := by decide +kernel
theorem subd8_5_16 : subd8_5 [-3, 2] = true := by decide +kernel
theorem subd8_5_17 : subd8_5 [-3, 3] = true := by decide +kernel
theorem subd8_5_18 : subd8_5 [-2, -5] = true := by decide +kernel
theorem subd8_5_19 : subd8_5 [-2, -4] = true := by decide +kernel
theorem subd8_5_20 : subd8_5 [-2, -3] = true := by decide +kernel
theorem subd8_5_21 : subd8_5 [-2, -2] = true := by decide +kernel
theorem subd8_5_22 : subd8_5 [-2, -1, -6] = true := by decide +kernel
theorem subd8_5_23 : subd8_5 [-2, -1, -5] = true := by decide +kernel
theorem subd8_5_24 : subd8_5 [-2, -1, -4] = true := by decide +kernel
theorem subd8_5_25 : subd8_5 [-2, -1, -3] = true := by decide +kernel
theorem subd8_5_26 : subd8_5 [-2, -1, -2] = true := by decide +kernel
theorem subd8_5_27 : subd8_5 [-2, -1, -1] = true := by decide +kernel
theorem subd8_5_28 : subd8_5 [-2, -1, 0] = true := by decide +kernel
theorem subd8_5_29 : subd8_5 [-2, -1, 1] = true := by decide +kernel
theorem subd8_5_30 : subd8_5 [-2, -1, 2] = true := by decide +kernel
theorem subd8_5_31 : subd8_5 [-2, -1, 3] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_cons.2 ⟨subd8_5_1, List.forall_mem_cons.2 ⟨subd8_5_2, List.forall_mem_cons.2 ⟨subd8_5_3, List.forall_mem_cons.2 ⟨subd8_5_4, List.forall_mem_cons.2 ⟨subd8_5_5, List.forall_mem_cons.2 ⟨subd8_5_6, List.forall_mem_cons.2 ⟨subd8_5_7, List.forall_mem_cons.2 ⟨subd8_5_8, List.forall_mem_cons.2 ⟨subd8_5_9, List.forall_mem_cons.2 ⟨subd8_5_10, List.forall_mem_cons.2 ⟨subd8_5_11, List.forall_mem_cons.2 ⟨subd8_5_12, List.forall_mem_cons.2 ⟨subd8_5_13, List.forall_mem_cons.2 ⟨subd8_5_14, List.forall_mem_cons.2 ⟨subd8_5_15, List.forall_mem_cons.2 ⟨subd8_5_16, List.forall_mem_cons.2 ⟨subd8_5_17, List.forall_mem_cons.2 ⟨subd8_5_18, List.forall_mem_cons.2 ⟨subd8_5_19, List.forall_mem_cons.2 ⟨subd8_5_20, List.forall_mem_cons.2 ⟨subd8_5_21, List.forall_mem_cons.2 ⟨subd8_5_22, List.forall_mem_cons.2 ⟨subd8_5_23, List.forall_mem_cons.2 ⟨subd8_5_24, List.forall_mem_cons.2 ⟨subd8_5_25, List.forall_mem_cons.2 ⟨subd8_5_26, List.forall_mem_cons.2 ⟨subd8_5_27, List.forall_mem_cons.2 ⟨subd8_5_28, List.forall_mem_cons.2 ⟨subd8_5_29, List.forall_mem_cons.2 ⟨subd8_5_30, List.forall_mem_cons.2 ⟨subd8_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_32 : subd8_5 [-2, -1, 4] = true := by decide +kernel
theorem subd8_5_33 : subd8_5 [-2, -1, 5] = true := by decide +kernel
theorem subd8_5_34 : subd8_5 [-2, -1, 6] = true := by decide +kernel
theorem subd8_5_35 : subd8_5 [-2, -1, 7] = true := by decide +kernel
theorem subd8_5_36 : subd8_5 [-2, 0, -6] = true := by decide +kernel
theorem subd8_5_37 : subd8_5 [-2, 0, -5] = true := by decide +kernel
theorem subd8_5_38 : subd8_5 [-2, 0, -4] = true := by decide +kernel
theorem subd8_5_39 : subd8_5 [-2, 0, -3] = true := by decide +kernel
theorem subd8_5_40 : subd8_5 [-2, 0, -2] = true := by decide +kernel
theorem subd8_5_41 : subd8_5 [-2, 0, -1] = true := by decide +kernel
theorem subd8_5_42 : subd8_5 [-2, 0, 0] = true := by decide +kernel
theorem subd8_5_43 : subd8_5 [-2, 0, 1] = true := by decide +kernel
theorem subd8_5_44 : subd8_5 [-2, 0, 2] = true := by decide +kernel
theorem subd8_5_45 : subd8_5 [-2, 0, 3] = true := by decide +kernel
theorem subd8_5_46 : subd8_5 [-2, 0, 4] = true := by decide +kernel
theorem subd8_5_47 : subd8_5 [-2, 0, 5] = true := by decide +kernel
theorem subd8_5_48 : subd8_5 [-2, 0, 6] = true := by decide +kernel
theorem subd8_5_49 : subd8_5 [-2, 1, -7] = true := by decide +kernel
theorem subd8_5_50 : subd8_5 [-2, 1, -6] = true := by decide +kernel
theorem subd8_5_51 : subd8_5 [-2, 1, -5] = true := by decide +kernel
theorem subd8_5_52 : subd8_5 [-2, 1, -4] = true := by decide +kernel
theorem subd8_5_53 : subd8_5 [-2, 1, -3] = true := by decide +kernel
theorem subd8_5_54 : subd8_5 [-2, 1, -2] = true := by decide +kernel
theorem subd8_5_55 : subd8_5 [-2, 1, -1] = true := by decide +kernel
theorem subd8_5_56 : subd8_5 [-2, 1, 0] = true := by decide +kernel
theorem subd8_5_57 : subd8_5 [-2, 1, 1] = true := by decide +kernel
theorem subd8_5_58 : subd8_5 [-2, 1, 2] = true := by decide +kernel
theorem subd8_5_59 : subd8_5 [-2, 1, 3] = true := by decide +kernel
theorem subd8_5_60 : subd8_5 [-2, 1, 4] = true := by decide +kernel
theorem subd8_5_61 : subd8_5 [-2, 1, 5] = true := by decide +kernel
theorem subd8_5_62 : subd8_5 [-2, 1, 6] = true := by decide +kernel
theorem subd8_5_63 : subd8_5 [-2, 2] = true := by decide +kernel
theorem sbd8_5_1 : ∀ q ∈ blkd8_5_1, subd8_5 q = true := by
  unfold blkd8_5_1
  exact List.forall_mem_cons.2 ⟨subd8_5_32, List.forall_mem_cons.2 ⟨subd8_5_33, List.forall_mem_cons.2 ⟨subd8_5_34, List.forall_mem_cons.2 ⟨subd8_5_35, List.forall_mem_cons.2 ⟨subd8_5_36, List.forall_mem_cons.2 ⟨subd8_5_37, List.forall_mem_cons.2 ⟨subd8_5_38, List.forall_mem_cons.2 ⟨subd8_5_39, List.forall_mem_cons.2 ⟨subd8_5_40, List.forall_mem_cons.2 ⟨subd8_5_41, List.forall_mem_cons.2 ⟨subd8_5_42, List.forall_mem_cons.2 ⟨subd8_5_43, List.forall_mem_cons.2 ⟨subd8_5_44, List.forall_mem_cons.2 ⟨subd8_5_45, List.forall_mem_cons.2 ⟨subd8_5_46, List.forall_mem_cons.2 ⟨subd8_5_47, List.forall_mem_cons.2 ⟨subd8_5_48, List.forall_mem_cons.2 ⟨subd8_5_49, List.forall_mem_cons.2 ⟨subd8_5_50, List.forall_mem_cons.2 ⟨subd8_5_51, List.forall_mem_cons.2 ⟨subd8_5_52, List.forall_mem_cons.2 ⟨subd8_5_53, List.forall_mem_cons.2 ⟨subd8_5_54, List.forall_mem_cons.2 ⟨subd8_5_55, List.forall_mem_cons.2 ⟨subd8_5_56, List.forall_mem_cons.2 ⟨subd8_5_57, List.forall_mem_cons.2 ⟨subd8_5_58, List.forall_mem_cons.2 ⟨subd8_5_59, List.forall_mem_cons.2 ⟨subd8_5_60, List.forall_mem_cons.2 ⟨subd8_5_61, List.forall_mem_cons.2 ⟨subd8_5_62, List.forall_mem_cons.2 ⟨subd8_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_64 : subd8_5 [-2, 3] = true := by decide +kernel
theorem subd8_5_65 : subd8_5 [-2, 4] = true := by decide +kernel
theorem subd8_5_66 : subd8_5 [-1, -5] = true := by decide +kernel
theorem subd8_5_67 : subd8_5 [-1, -4] = true := by decide +kernel
theorem subd8_5_68 : subd8_5 [-1, -3] = true := by decide +kernel
theorem subd8_5_69 : subd8_5 [-1, -2, -6] = true := by decide +kernel
theorem subd8_5_70 : subd8_5 [-1, -2, -5] = true := by decide +kernel
theorem subd8_5_71 : subd8_5 [-1, -2, -4] = true := by decide +kernel
theorem subd8_5_72 : subd8_5 [-1, -2, -3] = true := by decide +kernel
theorem subd8_5_73 : subd8_5 [-1, -2, -2] = true := by decide +kernel
theorem subd8_5_74 : subd8_5 [-1, -2, -1] = true := by decide +kernel
theorem subd8_5_75 : subd8_5 [-1, -2, 0] = true := by decide +kernel
theorem subd8_5_76 : subd8_5 [-1, -2, 1] = true := by decide +kernel
theorem subd8_5_77 : subd8_5 [-1, -2, 2] = true := by decide +kernel
theorem subd8_5_78 : subd8_5 [-1, -2, 3] = true := by decide +kernel
theorem subd8_5_79 : subd8_5 [-1, -2, 4] = true := by decide +kernel
theorem subd8_5_80 : subd8_5 [-1, -2, 5] = true := by decide +kernel
theorem subd8_5_81 : subd8_5 [-1, -2, 6] = true := by decide +kernel
theorem subd8_5_82 : subd8_5 [-1, -2, 7] = true := by decide +kernel
theorem subd8_5_83 : subd8_5 [-1, -1, -6] = true := by decide +kernel
theorem subd8_5_84 : subd8_5 [-1, -1, -5] = true := by decide +kernel
theorem subd8_5_85 : subd8_5 [-1, -1, -4] = true := by decide +kernel
theorem subd8_5_86 : subd8_5 [-1, -1, -3] = true := by decide +kernel
theorem subd8_5_87 : subd8_5 [-1, -1, -2] = true := by decide +kernel
theorem subd8_5_88 : subd8_5 [-1, -1, -1] = true := by decide +kernel
theorem subd8_5_89 : subd8_5 [-1, -1, 0] = true := by decide +kernel
theorem subd8_5_90 : subd8_5 [-1, -1, 1] = true := by decide +kernel
theorem subd8_5_91 : subd8_5 [-1, -1, 2] = true := by decide +kernel
theorem subd8_5_92 : subd8_5 [-1, -1, 3] = true := by decide +kernel
theorem subd8_5_93 : subd8_5 [-1, -1, 4] = true := by decide +kernel
theorem subd8_5_94 : subd8_5 [-1, -1, 5] = true := by decide +kernel
theorem subd8_5_95 : subd8_5 [-1, -1, 6] = true := by decide +kernel
theorem sbd8_5_2 : ∀ q ∈ blkd8_5_2, subd8_5 q = true := by
  unfold blkd8_5_2
  exact List.forall_mem_cons.2 ⟨subd8_5_64, List.forall_mem_cons.2 ⟨subd8_5_65, List.forall_mem_cons.2 ⟨subd8_5_66, List.forall_mem_cons.2 ⟨subd8_5_67, List.forall_mem_cons.2 ⟨subd8_5_68, List.forall_mem_cons.2 ⟨subd8_5_69, List.forall_mem_cons.2 ⟨subd8_5_70, List.forall_mem_cons.2 ⟨subd8_5_71, List.forall_mem_cons.2 ⟨subd8_5_72, List.forall_mem_cons.2 ⟨subd8_5_73, List.forall_mem_cons.2 ⟨subd8_5_74, List.forall_mem_cons.2 ⟨subd8_5_75, List.forall_mem_cons.2 ⟨subd8_5_76, List.forall_mem_cons.2 ⟨subd8_5_77, List.forall_mem_cons.2 ⟨subd8_5_78, List.forall_mem_cons.2 ⟨subd8_5_79, List.forall_mem_cons.2 ⟨subd8_5_80, List.forall_mem_cons.2 ⟨subd8_5_81, List.forall_mem_cons.2 ⟨subd8_5_82, List.forall_mem_cons.2 ⟨subd8_5_83, List.forall_mem_cons.2 ⟨subd8_5_84, List.forall_mem_cons.2 ⟨subd8_5_85, List.forall_mem_cons.2 ⟨subd8_5_86, List.forall_mem_cons.2 ⟨subd8_5_87, List.forall_mem_cons.2 ⟨subd8_5_88, List.forall_mem_cons.2 ⟨subd8_5_89, List.forall_mem_cons.2 ⟨subd8_5_90, List.forall_mem_cons.2 ⟨subd8_5_91, List.forall_mem_cons.2 ⟨subd8_5_92, List.forall_mem_cons.2 ⟨subd8_5_93, List.forall_mem_cons.2 ⟨subd8_5_94, List.forall_mem_cons.2 ⟨subd8_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_96 : subd8_5 [-1, -1, 7] = true := by decide +kernel
theorem subd8_5_97 : subd8_5 [-1, 0, -7] = true := by decide +kernel
theorem subd8_5_98 : subd8_5 [-1, 0, -6] = true := by decide +kernel
theorem subd8_5_99 : subd8_5 [-1, 0, -5] = true := by decide +kernel
theorem subd8_5_100 : subd8_5 [-1, 0, -4] = true := by decide +kernel
theorem subd8_5_101 : subd8_5 [-1, 0, -3] = true := by decide +kernel
theorem subd8_5_102 : subd8_5 [-1, 0, -2] = true := by decide +kernel
theorem subd8_5_103 : subd8_5 [-1, 0, -1] = true := by decide +kernel
theorem subd8_5_104 : subd8_5 [-1, 0, 0] = true := by decide +kernel
theorem subd8_5_105 : subd8_5 [-1, 0, 1] = true := by decide +kernel
theorem subd8_5_106 : subd8_5 [-1, 0, 2] = true := by decide +kernel
theorem subd8_5_107 : subd8_5 [-1, 0, 3] = true := by decide +kernel
theorem subd8_5_108 : subd8_5 [-1, 0, 4] = true := by decide +kernel
theorem subd8_5_109 : subd8_5 [-1, 0, 5] = true := by decide +kernel
theorem subd8_5_110 : subd8_5 [-1, 0, 6] = true := by decide +kernel
theorem subd8_5_111 : subd8_5 [-1, 1, -7] = true := by decide +kernel
theorem subd8_5_112 : subd8_5 [-1, 1, -6] = true := by decide +kernel
theorem subd8_5_113 : subd8_5 [-1, 1, -5] = true := by decide +kernel
theorem subd8_5_114 : subd8_5 [-1, 1, -4] = true := by decide +kernel
theorem subd8_5_115 : subd8_5 [-1, 1, -3] = true := by decide +kernel
theorem subd8_5_116 : subd8_5 [-1, 1, -2] = true := by decide +kernel
theorem subd8_5_117 : subd8_5 [-1, 1, -1] = true := by decide +kernel
theorem subd8_5_118 : subd8_5 [-1, 1, 0] = true := by decide +kernel
theorem subd8_5_119 : subd8_5 [-1, 1, 1] = true := by decide +kernel
theorem subd8_5_120 : subd8_5 [-1, 1, 2] = true := by decide +kernel
theorem subd8_5_121 : subd8_5 [-1, 1, 3] = true := by decide +kernel
theorem subd8_5_122 : subd8_5 [-1, 1, 4] = true := by decide +kernel
theorem subd8_5_123 : subd8_5 [-1, 1, 5] = true := by decide +kernel
theorem subd8_5_124 : subd8_5 [-1, 1, 6] = true := by decide +kernel
theorem subd8_5_125 : subd8_5 [-1, 2] = true := by decide +kernel
theorem subd8_5_126 : subd8_5 [-1, 3] = true := by decide +kernel
theorem subd8_5_127 : subd8_5 [-1, 4] = true := by decide +kernel
theorem sbd8_5_3 : ∀ q ∈ blkd8_5_3, subd8_5 q = true := by
  unfold blkd8_5_3
  exact List.forall_mem_cons.2 ⟨subd8_5_96, List.forall_mem_cons.2 ⟨subd8_5_97, List.forall_mem_cons.2 ⟨subd8_5_98, List.forall_mem_cons.2 ⟨subd8_5_99, List.forall_mem_cons.2 ⟨subd8_5_100, List.forall_mem_cons.2 ⟨subd8_5_101, List.forall_mem_cons.2 ⟨subd8_5_102, List.forall_mem_cons.2 ⟨subd8_5_103, List.forall_mem_cons.2 ⟨subd8_5_104, List.forall_mem_cons.2 ⟨subd8_5_105, List.forall_mem_cons.2 ⟨subd8_5_106, List.forall_mem_cons.2 ⟨subd8_5_107, List.forall_mem_cons.2 ⟨subd8_5_108, List.forall_mem_cons.2 ⟨subd8_5_109, List.forall_mem_cons.2 ⟨subd8_5_110, List.forall_mem_cons.2 ⟨subd8_5_111, List.forall_mem_cons.2 ⟨subd8_5_112, List.forall_mem_cons.2 ⟨subd8_5_113, List.forall_mem_cons.2 ⟨subd8_5_114, List.forall_mem_cons.2 ⟨subd8_5_115, List.forall_mem_cons.2 ⟨subd8_5_116, List.forall_mem_cons.2 ⟨subd8_5_117, List.forall_mem_cons.2 ⟨subd8_5_118, List.forall_mem_cons.2 ⟨subd8_5_119, List.forall_mem_cons.2 ⟨subd8_5_120, List.forall_mem_cons.2 ⟨subd8_5_121, List.forall_mem_cons.2 ⟨subd8_5_122, List.forall_mem_cons.2 ⟨subd8_5_123, List.forall_mem_cons.2 ⟨subd8_5_124, List.forall_mem_cons.2 ⟨subd8_5_125, List.forall_mem_cons.2 ⟨subd8_5_126, List.forall_mem_cons.2 ⟨subd8_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_128 : subd8_5 [0, -5] = true := by decide +kernel
theorem subd8_5_129 : subd8_5 [0, -4] = true := by decide +kernel
theorem subd8_5_130 : subd8_5 [0, -3] = true := by decide +kernel
theorem subd8_5_131 : subd8_5 [0, -2, -6] = true := by decide +kernel
theorem subd8_5_132 : subd8_5 [0, -2, -5] = true := by decide +kernel
theorem subd8_5_133 : subd8_5 [0, -2, -4] = true := by decide +kernel
theorem subd8_5_134 : subd8_5 [0, -2, -3] = true := by decide +kernel
theorem subd8_5_135 : subd8_5 [0, -2, -2] = true := by decide +kernel
theorem subd8_5_136 : subd8_5 [0, -2, -1] = true := by decide +kernel
theorem subd8_5_137 : subd8_5 [0, -2, 0] = true := by decide +kernel
theorem subd8_5_138 : subd8_5 [0, -2, 1] = true := by decide +kernel
theorem subd8_5_139 : subd8_5 [0, -2, 2] = true := by decide +kernel
theorem subd8_5_140 : subd8_5 [0, -2, 3] = true := by decide +kernel
theorem subd8_5_141 : subd8_5 [0, -2, 4] = true := by decide +kernel
theorem subd8_5_142 : subd8_5 [0, -2, 5] = true := by decide +kernel
theorem subd8_5_143 : subd8_5 [0, -2, 6] = true := by decide +kernel
theorem subd8_5_144 : subd8_5 [0, -2, 7] = true := by decide +kernel
theorem subd8_5_145 : subd8_5 [0, -1, -7] = true := by decide +kernel
theorem subd8_5_146 : subd8_5 [0, -1, -6] = true := by decide +kernel
theorem subd8_5_147 : subd8_5 [0, -1, -5] = true := by decide +kernel
theorem subd8_5_148 : subd8_5 [0, -1, -4] = true := by decide +kernel
theorem subd8_5_149 : subd8_5 [0, -1, -3] = true := by decide +kernel
theorem subd8_5_150 : subd8_5 [0, -1, -2] = true := by decide +kernel
theorem subd8_5_151 : subd8_5 [0, -1, -1] = true := by decide +kernel
theorem subd8_5_152 : subd8_5 [0, -1, 0] = true := by decide +kernel
theorem subd8_5_153 : subd8_5 [0, -1, 1] = true := by decide +kernel
theorem subd8_5_154 : subd8_5 [0, -1, 2] = true := by decide +kernel
theorem subd8_5_155 : subd8_5 [0, -1, 3] = true := by decide +kernel
theorem subd8_5_156 : subd8_5 [0, -1, 4] = true := by decide +kernel
theorem subd8_5_157 : subd8_5 [0, -1, 5] = true := by decide +kernel
theorem subd8_5_158 : subd8_5 [0, -1, 6] = true := by decide +kernel
theorem subd8_5_159 : subd8_5 [0, -1, 7] = true := by decide +kernel
theorem sbd8_5_4 : ∀ q ∈ blkd8_5_4, subd8_5 q = true := by
  unfold blkd8_5_4
  exact List.forall_mem_cons.2 ⟨subd8_5_128, List.forall_mem_cons.2 ⟨subd8_5_129, List.forall_mem_cons.2 ⟨subd8_5_130, List.forall_mem_cons.2 ⟨subd8_5_131, List.forall_mem_cons.2 ⟨subd8_5_132, List.forall_mem_cons.2 ⟨subd8_5_133, List.forall_mem_cons.2 ⟨subd8_5_134, List.forall_mem_cons.2 ⟨subd8_5_135, List.forall_mem_cons.2 ⟨subd8_5_136, List.forall_mem_cons.2 ⟨subd8_5_137, List.forall_mem_cons.2 ⟨subd8_5_138, List.forall_mem_cons.2 ⟨subd8_5_139, List.forall_mem_cons.2 ⟨subd8_5_140, List.forall_mem_cons.2 ⟨subd8_5_141, List.forall_mem_cons.2 ⟨subd8_5_142, List.forall_mem_cons.2 ⟨subd8_5_143, List.forall_mem_cons.2 ⟨subd8_5_144, List.forall_mem_cons.2 ⟨subd8_5_145, List.forall_mem_cons.2 ⟨subd8_5_146, List.forall_mem_cons.2 ⟨subd8_5_147, List.forall_mem_cons.2 ⟨subd8_5_148, List.forall_mem_cons.2 ⟨subd8_5_149, List.forall_mem_cons.2 ⟨subd8_5_150, List.forall_mem_cons.2 ⟨subd8_5_151, List.forall_mem_cons.2 ⟨subd8_5_152, List.forall_mem_cons.2 ⟨subd8_5_153, List.forall_mem_cons.2 ⟨subd8_5_154, List.forall_mem_cons.2 ⟨subd8_5_155, List.forall_mem_cons.2 ⟨subd8_5_156, List.forall_mem_cons.2 ⟨subd8_5_157, List.forall_mem_cons.2 ⟨subd8_5_158, List.forall_mem_cons.2 ⟨subd8_5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_160 : subd8_5 [0, 0, -7] = true := by decide +kernel
theorem subd8_5_161 : subd8_5 [0, 0, -6] = true := by decide +kernel
theorem subd8_5_162 : subd8_5 [0, 0, -5] = true := by decide +kernel
theorem subd8_5_163 : subd8_5 [0, 0, -4] = true := by decide +kernel
theorem subd8_5_164 : subd8_5 [0, 0, -3] = true := by decide +kernel
theorem subd8_5_165 : subd8_5 [0, 0, -2] = true := by decide +kernel
theorem subd8_5_166 : subd8_5 [0, 0, -1] = true := by decide +kernel
theorem subd8_5_167 : subd8_5 [0, 0, 0] = true := by decide +kernel
theorem subd8_5_168 : subd8_5 [0, 0, 1] = true := by decide +kernel
theorem subd8_5_169 : subd8_5 [0, 0, 2] = true := by decide +kernel
theorem subd8_5_170 : subd8_5 [0, 0, 3] = true := by decide +kernel
theorem subd8_5_171 : subd8_5 [0, 0, 4] = true := by decide +kernel
theorem subd8_5_172 : subd8_5 [0, 0, 5] = true := by decide +kernel
theorem subd8_5_173 : subd8_5 [0, 0, 6] = true := by decide +kernel
theorem subd8_5_174 : subd8_5 [0, 1, -8] = true := by decide +kernel
theorem subd8_5_175 : subd8_5 [0, 1, -7] = true := by decide +kernel
theorem subd8_5_176 : subd8_5 [0, 1, -6] = true := by decide +kernel
theorem subd8_5_177 : subd8_5 [0, 1, -5] = true := by decide +kernel
theorem subd8_5_178 : subd8_5 [0, 1, -4] = true := by decide +kernel
theorem subd8_5_179 : subd8_5 [0, 1, -3] = true := by decide +kernel
theorem subd8_5_180 : subd8_5 [0, 1, -2] = true := by decide +kernel
theorem subd8_5_181 : subd8_5 [0, 1, -1] = true := by decide +kernel
theorem subd8_5_182 : subd8_5 [0, 1, 0] = true := by decide +kernel
theorem subd8_5_183 : subd8_5 [0, 1, 1] = true := by decide +kernel
theorem subd8_5_184 : subd8_5 [0, 1, 2] = true := by decide +kernel
theorem subd8_5_185 : subd8_5 [0, 1, 3] = true := by decide +kernel
theorem subd8_5_186 : subd8_5 [0, 1, 4] = true := by decide +kernel
theorem subd8_5_187 : subd8_5 [0, 1, 5] = true := by decide +kernel
theorem subd8_5_188 : subd8_5 [0, 1, 6] = true := by decide +kernel
theorem subd8_5_189 : subd8_5 [0, 2, -8] = true := by decide +kernel
theorem subd8_5_190 : subd8_5 [0, 2, -7] = true := by decide +kernel
theorem subd8_5_191 : subd8_5 [0, 2, -6] = true := by decide +kernel
theorem sbd8_5_5 : ∀ q ∈ blkd8_5_5, subd8_5 q = true := by
  unfold blkd8_5_5
  exact List.forall_mem_cons.2 ⟨subd8_5_160, List.forall_mem_cons.2 ⟨subd8_5_161, List.forall_mem_cons.2 ⟨subd8_5_162, List.forall_mem_cons.2 ⟨subd8_5_163, List.forall_mem_cons.2 ⟨subd8_5_164, List.forall_mem_cons.2 ⟨subd8_5_165, List.forall_mem_cons.2 ⟨subd8_5_166, List.forall_mem_cons.2 ⟨subd8_5_167, List.forall_mem_cons.2 ⟨subd8_5_168, List.forall_mem_cons.2 ⟨subd8_5_169, List.forall_mem_cons.2 ⟨subd8_5_170, List.forall_mem_cons.2 ⟨subd8_5_171, List.forall_mem_cons.2 ⟨subd8_5_172, List.forall_mem_cons.2 ⟨subd8_5_173, List.forall_mem_cons.2 ⟨subd8_5_174, List.forall_mem_cons.2 ⟨subd8_5_175, List.forall_mem_cons.2 ⟨subd8_5_176, List.forall_mem_cons.2 ⟨subd8_5_177, List.forall_mem_cons.2 ⟨subd8_5_178, List.forall_mem_cons.2 ⟨subd8_5_179, List.forall_mem_cons.2 ⟨subd8_5_180, List.forall_mem_cons.2 ⟨subd8_5_181, List.forall_mem_cons.2 ⟨subd8_5_182, List.forall_mem_cons.2 ⟨subd8_5_183, List.forall_mem_cons.2 ⟨subd8_5_184, List.forall_mem_cons.2 ⟨subd8_5_185, List.forall_mem_cons.2 ⟨subd8_5_186, List.forall_mem_cons.2 ⟨subd8_5_187, List.forall_mem_cons.2 ⟨subd8_5_188, List.forall_mem_cons.2 ⟨subd8_5_189, List.forall_mem_cons.2 ⟨subd8_5_190, List.forall_mem_cons.2 ⟨subd8_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_192 : subd8_5 [0, 2, -5] = true := by decide +kernel
theorem subd8_5_193 : subd8_5 [0, 2, -4] = true := by decide +kernel
theorem subd8_5_194 : subd8_5 [0, 2, -3] = true := by decide +kernel
theorem subd8_5_195 : subd8_5 [0, 2, -2] = true := by decide +kernel
theorem subd8_5_196 : subd8_5 [0, 2, -1] = true := by decide +kernel
theorem subd8_5_197 : subd8_5 [0, 2, 0] = true := by decide +kernel
theorem subd8_5_198 : subd8_5 [0, 2, 1] = true := by decide +kernel
theorem subd8_5_199 : subd8_5 [0, 2, 2] = true := by decide +kernel
theorem subd8_5_200 : subd8_5 [0, 2, 3] = true := by decide +kernel
theorem subd8_5_201 : subd8_5 [0, 2, 4] = true := by decide +kernel
theorem subd8_5_202 : subd8_5 [0, 2, 5] = true := by decide +kernel
theorem subd8_5_203 : subd8_5 [0, 3] = true := by decide +kernel
theorem subd8_5_204 : subd8_5 [0, 4] = true := by decide +kernel
theorem subd8_5_205 : subd8_5 [1, -5] = true := by decide +kernel
theorem subd8_5_206 : subd8_5 [1, -4] = true := by decide +kernel
theorem subd8_5_207 : subd8_5 [1, -3] = true := by decide +kernel
theorem subd8_5_208 : subd8_5 [1, -2] = true := by decide +kernel
theorem subd8_5_209 : subd8_5 [1, -1, -7] = true := by decide +kernel
theorem subd8_5_210 : subd8_5 [1, -1, -6] = true := by decide +kernel
theorem subd8_5_211 : subd8_5 [1, -1, -5] = true := by decide +kernel
theorem subd8_5_212 : subd8_5 [1, -1, -4] = true := by decide +kernel
theorem subd8_5_213 : subd8_5 [1, -1, -3] = true := by decide +kernel
theorem subd8_5_214 : subd8_5 [1, -1, -2] = true := by decide +kernel
theorem subd8_5_215 : subd8_5 [1, -1, -1] = true := by decide +kernel
theorem subd8_5_216 : subd8_5 [1, -1, 0] = true := by decide +kernel
theorem subd8_5_217 : subd8_5 [1, -1, 1] = true := by decide +kernel
theorem subd8_5_218 : subd8_5 [1, -1, 2] = true := by decide +kernel
theorem subd8_5_219 : subd8_5 [1, -1, 3] = true := by decide +kernel
theorem subd8_5_220 : subd8_5 [1, -1, 4] = true := by decide +kernel
theorem subd8_5_221 : subd8_5 [1, -1, 5] = true := by decide +kernel
theorem subd8_5_222 : subd8_5 [1, -1, 6] = true := by decide +kernel
theorem subd8_5_223 : subd8_5 [1, 0, -7] = true := by decide +kernel
theorem sbd8_5_6 : ∀ q ∈ blkd8_5_6, subd8_5 q = true := by
  unfold blkd8_5_6
  exact List.forall_mem_cons.2 ⟨subd8_5_192, List.forall_mem_cons.2 ⟨subd8_5_193, List.forall_mem_cons.2 ⟨subd8_5_194, List.forall_mem_cons.2 ⟨subd8_5_195, List.forall_mem_cons.2 ⟨subd8_5_196, List.forall_mem_cons.2 ⟨subd8_5_197, List.forall_mem_cons.2 ⟨subd8_5_198, List.forall_mem_cons.2 ⟨subd8_5_199, List.forall_mem_cons.2 ⟨subd8_5_200, List.forall_mem_cons.2 ⟨subd8_5_201, List.forall_mem_cons.2 ⟨subd8_5_202, List.forall_mem_cons.2 ⟨subd8_5_203, List.forall_mem_cons.2 ⟨subd8_5_204, List.forall_mem_cons.2 ⟨subd8_5_205, List.forall_mem_cons.2 ⟨subd8_5_206, List.forall_mem_cons.2 ⟨subd8_5_207, List.forall_mem_cons.2 ⟨subd8_5_208, List.forall_mem_cons.2 ⟨subd8_5_209, List.forall_mem_cons.2 ⟨subd8_5_210, List.forall_mem_cons.2 ⟨subd8_5_211, List.forall_mem_cons.2 ⟨subd8_5_212, List.forall_mem_cons.2 ⟨subd8_5_213, List.forall_mem_cons.2 ⟨subd8_5_214, List.forall_mem_cons.2 ⟨subd8_5_215, List.forall_mem_cons.2 ⟨subd8_5_216, List.forall_mem_cons.2 ⟨subd8_5_217, List.forall_mem_cons.2 ⟨subd8_5_218, List.forall_mem_cons.2 ⟨subd8_5_219, List.forall_mem_cons.2 ⟨subd8_5_220, List.forall_mem_cons.2 ⟨subd8_5_221, List.forall_mem_cons.2 ⟨subd8_5_222, List.forall_mem_cons.2 ⟨subd8_5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_224 : subd8_5 [1, 0, -6] = true := by decide +kernel
theorem subd8_5_225 : subd8_5 [1, 0, -5] = true := by decide +kernel
theorem subd8_5_226 : subd8_5 [1, 0, -4] = true := by decide +kernel
theorem subd8_5_227 : subd8_5 [1, 0, -3] = true := by decide +kernel
theorem subd8_5_228 : subd8_5 [1, 0, -2] = true := by decide +kernel
theorem subd8_5_229 : subd8_5 [1, 0, -1] = true := by decide +kernel
theorem subd8_5_230 : subd8_5 [1, 0, 0] = true := by decide +kernel
theorem subd8_5_231 : subd8_5 [1, 0, 1] = true := by decide +kernel
theorem subd8_5_232 : subd8_5 [1, 0, 2] = true := by decide +kernel
theorem subd8_5_233 : subd8_5 [1, 0, 3] = true := by decide +kernel
theorem subd8_5_234 : subd8_5 [1, 0, 4] = true := by decide +kernel
theorem subd8_5_235 : subd8_5 [1, 0, 5] = true := by decide +kernel
theorem subd8_5_236 : subd8_5 [1, 0, 6] = true := by decide +kernel
theorem subd8_5_237 : subd8_5 [1, 1, -8] = true := by decide +kernel
theorem subd8_5_238 : subd8_5 [1, 1, -7] = true := by decide +kernel
theorem subd8_5_239 : subd8_5 [1, 1, -6] = true := by decide +kernel
theorem subd8_5_240 : subd8_5 [1, 1, -5] = true := by decide +kernel
theorem subd8_5_241 : subd8_5 [1, 1, -4] = true := by decide +kernel
theorem subd8_5_242 : subd8_5 [1, 1, -3] = true := by decide +kernel
theorem subd8_5_243 : subd8_5 [1, 1, -2] = true := by decide +kernel
theorem subd8_5_244 : subd8_5 [1, 1, -1] = true := by decide +kernel
theorem subd8_5_245 : subd8_5 [1, 1, 0] = true := by decide +kernel
theorem subd8_5_246 : subd8_5 [1, 1, 1] = true := by decide +kernel
theorem subd8_5_247 : subd8_5 [1, 1, 2] = true := by decide +kernel
theorem subd8_5_248 : subd8_5 [1, 1, 3] = true := by decide +kernel
theorem subd8_5_249 : subd8_5 [1, 1, 4] = true := by decide +kernel
theorem subd8_5_250 : subd8_5 [1, 1, 5] = true := by decide +kernel
theorem subd8_5_251 : subd8_5 [1, 2, -8] = true := by decide +kernel
theorem subd8_5_252 : subd8_5 [1, 2, -7] = true := by decide +kernel
theorem subd8_5_253 : subd8_5 [1, 2, -6] = true := by decide +kernel
theorem subd8_5_254 : subd8_5 [1, 2, -5] = true := by decide +kernel
theorem subd8_5_255 : subd8_5 [1, 2, -4] = true := by decide +kernel
theorem sbd8_5_7 : ∀ q ∈ blkd8_5_7, subd8_5 q = true := by
  unfold blkd8_5_7
  exact List.forall_mem_cons.2 ⟨subd8_5_224, List.forall_mem_cons.2 ⟨subd8_5_225, List.forall_mem_cons.2 ⟨subd8_5_226, List.forall_mem_cons.2 ⟨subd8_5_227, List.forall_mem_cons.2 ⟨subd8_5_228, List.forall_mem_cons.2 ⟨subd8_5_229, List.forall_mem_cons.2 ⟨subd8_5_230, List.forall_mem_cons.2 ⟨subd8_5_231, List.forall_mem_cons.2 ⟨subd8_5_232, List.forall_mem_cons.2 ⟨subd8_5_233, List.forall_mem_cons.2 ⟨subd8_5_234, List.forall_mem_cons.2 ⟨subd8_5_235, List.forall_mem_cons.2 ⟨subd8_5_236, List.forall_mem_cons.2 ⟨subd8_5_237, List.forall_mem_cons.2 ⟨subd8_5_238, List.forall_mem_cons.2 ⟨subd8_5_239, List.forall_mem_cons.2 ⟨subd8_5_240, List.forall_mem_cons.2 ⟨subd8_5_241, List.forall_mem_cons.2 ⟨subd8_5_242, List.forall_mem_cons.2 ⟨subd8_5_243, List.forall_mem_cons.2 ⟨subd8_5_244, List.forall_mem_cons.2 ⟨subd8_5_245, List.forall_mem_cons.2 ⟨subd8_5_246, List.forall_mem_cons.2 ⟨subd8_5_247, List.forall_mem_cons.2 ⟨subd8_5_248, List.forall_mem_cons.2 ⟨subd8_5_249, List.forall_mem_cons.2 ⟨subd8_5_250, List.forall_mem_cons.2 ⟨subd8_5_251, List.forall_mem_cons.2 ⟨subd8_5_252, List.forall_mem_cons.2 ⟨subd8_5_253, List.forall_mem_cons.2 ⟨subd8_5_254, List.forall_mem_cons.2 ⟨subd8_5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_256 : subd8_5 [1, 2, -3] = true := by decide +kernel
theorem subd8_5_257 : subd8_5 [1, 2, -2] = true := by decide +kernel
theorem subd8_5_258 : subd8_5 [1, 2, -1] = true := by decide +kernel
theorem subd8_5_259 : subd8_5 [1, 2, 0] = true := by decide +kernel
theorem subd8_5_260 : subd8_5 [1, 2, 1] = true := by decide +kernel
theorem subd8_5_261 : subd8_5 [1, 2, 2] = true := by decide +kernel
theorem subd8_5_262 : subd8_5 [1, 2, 3] = true := by decide +kernel
theorem subd8_5_263 : subd8_5 [1, 2, 4] = true := by decide +kernel
theorem subd8_5_264 : subd8_5 [1, 2, 5] = true := by decide +kernel
theorem subd8_5_265 : subd8_5 [1, 3] = true := by decide +kernel
theorem subd8_5_266 : subd8_5 [1, 4] = true := by decide +kernel
theorem subd8_5_267 : subd8_5 [2, -5] = true := by decide +kernel
theorem subd8_5_268 : subd8_5 [2, -4] = true := by decide +kernel
theorem subd8_5_269 : subd8_5 [2, -3] = true := by decide +kernel
theorem subd8_5_270 : subd8_5 [2, -2] = true := by decide +kernel
theorem subd8_5_271 : subd8_5 [2, -1, -7] = true := by decide +kernel
theorem subd8_5_272 : subd8_5 [2, -1, -6] = true := by decide +kernel
theorem subd8_5_273 : subd8_5 [2, -1, -5] = true := by decide +kernel
theorem subd8_5_274 : subd8_5 [2, -1, -4] = true := by decide +kernel
theorem subd8_5_275 : subd8_5 [2, -1, -3] = true := by decide +kernel
theorem subd8_5_276 : subd8_5 [2, -1, -2] = true := by decide +kernel
theorem subd8_5_277 : subd8_5 [2, -1, -1] = true := by decide +kernel
theorem subd8_5_278 : subd8_5 [2, -1, 0] = true := by decide +kernel
theorem subd8_5_279 : subd8_5 [2, -1, 1] = true := by decide +kernel
theorem subd8_5_280 : subd8_5 [2, -1, 2] = true := by decide +kernel
theorem subd8_5_281 : subd8_5 [2, -1, 3] = true := by decide +kernel
theorem subd8_5_282 : subd8_5 [2, -1, 4] = true := by decide +kernel
theorem subd8_5_283 : subd8_5 [2, -1, 5] = true := by decide +kernel
theorem subd8_5_284 : subd8_5 [2, -1, 6] = true := by decide +kernel
theorem subd8_5_285 : subd8_5 [2, 0, -7] = true := by decide +kernel
theorem subd8_5_286 : subd8_5 [2, 0, -6] = true := by decide +kernel
theorem subd8_5_287 : subd8_5 [2, 0, -5] = true := by decide +kernel
theorem sbd8_5_8 : ∀ q ∈ blkd8_5_8, subd8_5 q = true := by
  unfold blkd8_5_8
  exact List.forall_mem_cons.2 ⟨subd8_5_256, List.forall_mem_cons.2 ⟨subd8_5_257, List.forall_mem_cons.2 ⟨subd8_5_258, List.forall_mem_cons.2 ⟨subd8_5_259, List.forall_mem_cons.2 ⟨subd8_5_260, List.forall_mem_cons.2 ⟨subd8_5_261, List.forall_mem_cons.2 ⟨subd8_5_262, List.forall_mem_cons.2 ⟨subd8_5_263, List.forall_mem_cons.2 ⟨subd8_5_264, List.forall_mem_cons.2 ⟨subd8_5_265, List.forall_mem_cons.2 ⟨subd8_5_266, List.forall_mem_cons.2 ⟨subd8_5_267, List.forall_mem_cons.2 ⟨subd8_5_268, List.forall_mem_cons.2 ⟨subd8_5_269, List.forall_mem_cons.2 ⟨subd8_5_270, List.forall_mem_cons.2 ⟨subd8_5_271, List.forall_mem_cons.2 ⟨subd8_5_272, List.forall_mem_cons.2 ⟨subd8_5_273, List.forall_mem_cons.2 ⟨subd8_5_274, List.forall_mem_cons.2 ⟨subd8_5_275, List.forall_mem_cons.2 ⟨subd8_5_276, List.forall_mem_cons.2 ⟨subd8_5_277, List.forall_mem_cons.2 ⟨subd8_5_278, List.forall_mem_cons.2 ⟨subd8_5_279, List.forall_mem_cons.2 ⟨subd8_5_280, List.forall_mem_cons.2 ⟨subd8_5_281, List.forall_mem_cons.2 ⟨subd8_5_282, List.forall_mem_cons.2 ⟨subd8_5_283, List.forall_mem_cons.2 ⟨subd8_5_284, List.forall_mem_cons.2 ⟨subd8_5_285, List.forall_mem_cons.2 ⟨subd8_5_286, List.forall_mem_cons.2 ⟨subd8_5_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
