import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_416 : subd8_1 [2, 2, 6] = true := by decide +kernel
theorem subd8_1_417 : subd8_1 [2, 3] = true := by decide +kernel
theorem subd8_1_418 : subd8_1 [2, 4] = true := by decide +kernel
theorem subd8_1_419 : subd8_1 [2, 5] = true := by decide +kernel
theorem subd8_1_420 : subd8_1 [2, 6] = true := by decide +kernel
theorem subd8_1_421 : subd8_1 [3, -5] = true := by decide +kernel
theorem subd8_1_422 : subd8_1 [3, -4] = true := by decide +kernel
theorem subd8_1_423 : subd8_1 [3, -3] = true := by decide +kernel
theorem subd8_1_424 : subd8_1 [3, -2] = true := by decide +kernel
theorem subd8_1_425 : subd8_1 [3, -1] = true := by decide +kernel
theorem subd8_1_426 : subd8_1 [3, 0] = true := by decide +kernel
theorem subd8_1_427 : subd8_1 [3, 1] = true := by decide +kernel
theorem subd8_1_428 : subd8_1 [3, 2] = true := by decide +kernel
theorem subd8_1_429 : subd8_1 [3, 3] = true := by decide +kernel
theorem subd8_1_430 : subd8_1 [3, 4] = true := by decide +kernel
theorem subd8_1_431 : subd8_1 [3, 5] = true := by decide +kernel
theorem subd8_1_432 : subd8_1 [3, 6] = true := by decide +kernel
theorem subd8_1_433 : subd8_1 [4, -3] = true := by decide +kernel
theorem subd8_1_434 : subd8_1 [4, -2] = true := by decide +kernel
theorem subd8_1_435 : subd8_1 [4, -1] = true := by decide +kernel
theorem subd8_1_436 : subd8_1 [4, 0] = true := by decide +kernel
theorem subd8_1_437 : subd8_1 [4, 1] = true := by decide +kernel
theorem subd8_1_438 : subd8_1 [4, 2] = true := by decide +kernel
theorem subd8_1_439 : subd8_1 [4, 3] = true := by decide +kernel
theorem subd8_1_440 : subd8_1 [4, 4] = true := by decide +kernel
theorem subd8_1_441 : subd8_1 [4, 5] = true := by decide +kernel
theorem subd8_1_442 : subd8_1 [4, 6] = true := by decide +kernel
theorem subd8_1_443 : subd8_1 [5, -2] = true := by decide +kernel
theorem subd8_1_444 : subd8_1 [5, -1] = true := by decide +kernel
theorem subd8_1_445 : subd8_1 [5, 0] = true := by decide +kernel
theorem subd8_1_446 : subd8_1 [5, 1] = true := by decide +kernel
theorem subd8_1_447 : subd8_1 [5, 2] = true := by decide +kernel
theorem sbd8_1_13 : ∀ q ∈ blkd8_1_13, subd8_1 q = true := by
  unfold blkd8_1_13
  exact List.forall_mem_cons.2 ⟨subd8_1_416, List.forall_mem_cons.2 ⟨subd8_1_417, List.forall_mem_cons.2 ⟨subd8_1_418, List.forall_mem_cons.2 ⟨subd8_1_419, List.forall_mem_cons.2 ⟨subd8_1_420, List.forall_mem_cons.2 ⟨subd8_1_421, List.forall_mem_cons.2 ⟨subd8_1_422, List.forall_mem_cons.2 ⟨subd8_1_423, List.forall_mem_cons.2 ⟨subd8_1_424, List.forall_mem_cons.2 ⟨subd8_1_425, List.forall_mem_cons.2 ⟨subd8_1_426, List.forall_mem_cons.2 ⟨subd8_1_427, List.forall_mem_cons.2 ⟨subd8_1_428, List.forall_mem_cons.2 ⟨subd8_1_429, List.forall_mem_cons.2 ⟨subd8_1_430, List.forall_mem_cons.2 ⟨subd8_1_431, List.forall_mem_cons.2 ⟨subd8_1_432, List.forall_mem_cons.2 ⟨subd8_1_433, List.forall_mem_cons.2 ⟨subd8_1_434, List.forall_mem_cons.2 ⟨subd8_1_435, List.forall_mem_cons.2 ⟨subd8_1_436, List.forall_mem_cons.2 ⟨subd8_1_437, List.forall_mem_cons.2 ⟨subd8_1_438, List.forall_mem_cons.2 ⟨subd8_1_439, List.forall_mem_cons.2 ⟨subd8_1_440, List.forall_mem_cons.2 ⟨subd8_1_441, List.forall_mem_cons.2 ⟨subd8_1_442, List.forall_mem_cons.2 ⟨subd8_1_443, List.forall_mem_cons.2 ⟨subd8_1_444, List.forall_mem_cons.2 ⟨subd8_1_445, List.forall_mem_cons.2 ⟨subd8_1_446, List.forall_mem_cons.2 ⟨subd8_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_448 : subd8_1 [5, 3] = true := by decide +kernel
theorem subd8_1_449 : subd8_1 [5, 4] = true := by decide +kernel
theorem subd8_1_450 : subd8_1 [5, 5] = true := by decide +kernel
theorem sbd8_1_14 : ∀ q ∈ blkd8_1_14, subd8_1 q = true := by
  unfold blkd8_1_14
  exact List.forall_mem_cons.2 ⟨subd8_1_448, List.forall_mem_cons.2 ⟨subd8_1_449, List.forall_mem_cons.2 ⟨subd8_1_450, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-7, -2] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-7, -1] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-7, 0] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-7, 1] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-7, 2] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-7, 3] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [-7, 4] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [-7, 5] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [-6, -3] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [-6, -2] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [-6, -1] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [-6, 0] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [-6, 1] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [-6, 2] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [-6, 3] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [-6, 4] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [-6, 5] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [-6, 6] = true := by decide +kernel
theorem subd8_2_18 : subd8_2 [-5, -4] = true := by decide +kernel
theorem subd8_2_19 : subd8_2 [-5, -3] = true := by decide +kernel
theorem subd8_2_20 : subd8_2 [-5, -2] = true := by decide +kernel
theorem subd8_2_21 : subd8_2 [-5, -1] = true := by decide +kernel
theorem subd8_2_22 : subd8_2 [-5, 0] = true := by decide +kernel
theorem subd8_2_23 : subd8_2 [-5, 1] = true := by decide +kernel
theorem subd8_2_24 : subd8_2 [-5, 2] = true := by decide +kernel
theorem subd8_2_25 : subd8_2 [-5, 3] = true := by decide +kernel
theorem subd8_2_26 : subd8_2 [-5, 4] = true := by decide +kernel
theorem subd8_2_27 : subd8_2 [-5, 5] = true := by decide +kernel
theorem subd8_2_28 : subd8_2 [-5, 6] = true := by decide +kernel
theorem subd8_2_29 : subd8_2 [-4, -5] = true := by decide +kernel
theorem subd8_2_30 : subd8_2 [-4, -4] = true := by decide +kernel
theorem subd8_2_31 : subd8_2 [-4, -3] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_cons.2 ⟨subd8_2_18, List.forall_mem_cons.2 ⟨subd8_2_19, List.forall_mem_cons.2 ⟨subd8_2_20, List.forall_mem_cons.2 ⟨subd8_2_21, List.forall_mem_cons.2 ⟨subd8_2_22, List.forall_mem_cons.2 ⟨subd8_2_23, List.forall_mem_cons.2 ⟨subd8_2_24, List.forall_mem_cons.2 ⟨subd8_2_25, List.forall_mem_cons.2 ⟨subd8_2_26, List.forall_mem_cons.2 ⟨subd8_2_27, List.forall_mem_cons.2 ⟨subd8_2_28, List.forall_mem_cons.2 ⟨subd8_2_29, List.forall_mem_cons.2 ⟨subd8_2_30, List.forall_mem_cons.2 ⟨subd8_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_32 : subd8_2 [-4, -2] = true := by decide +kernel
theorem subd8_2_33 : subd8_2 [-4, -1] = true := by decide +kernel
theorem subd8_2_34 : subd8_2 [-4, 0] = true := by decide +kernel
theorem subd8_2_35 : subd8_2 [-4, 1] = true := by decide +kernel
theorem subd8_2_36 : subd8_2 [-4, 2] = true := by decide +kernel
theorem subd8_2_37 : subd8_2 [-4, 3] = true := by decide +kernel
theorem subd8_2_38 : subd8_2 [-4, 4] = true := by decide +kernel
theorem subd8_2_39 : subd8_2 [-4, 5] = true := by decide +kernel
theorem subd8_2_40 : subd8_2 [-4, 6] = true := by decide +kernel
theorem subd8_2_41 : subd8_2 [-3, -6] = true := by decide +kernel
theorem subd8_2_42 : subd8_2 [-3, -5] = true := by decide +kernel
theorem subd8_2_43 : subd8_2 [-3, -4] = true := by decide +kernel
theorem subd8_2_44 : subd8_2 [-3, -3] = true := by decide +kernel
theorem subd8_2_45 : subd8_2 [-3, -2] = true := by decide +kernel
theorem subd8_2_46 : subd8_2 [-3, -1] = true := by decide +kernel
theorem subd8_2_47 : subd8_2 [-3, 0, -6] = true := by decide +kernel
theorem subd8_2_48 : subd8_2 [-3, 0, -5] = true := by decide +kernel
theorem subd8_2_49 : subd8_2 [-3, 0, -4] = true := by decide +kernel
theorem subd8_2_50 : subd8_2 [-3, 0, -3] = true := by decide +kernel
theorem subd8_2_51 : subd8_2 [-3, 0, -2] = true := by decide +kernel
theorem subd8_2_52 : subd8_2 [-3, 0, -1] = true := by decide +kernel
theorem subd8_2_53 : subd8_2 [-3, 0, 0] = true := by decide +kernel
theorem subd8_2_54 : subd8_2 [-3, 0, 1] = true := by decide +kernel
theorem subd8_2_55 : subd8_2 [-3, 0, 2] = true := by decide +kernel
theorem subd8_2_56 : subd8_2 [-3, 0, 3] = true := by decide +kernel
theorem subd8_2_57 : subd8_2 [-3, 0, 4] = true := by decide +kernel
theorem subd8_2_58 : subd8_2 [-3, 0, 5] = true := by decide +kernel
theorem subd8_2_59 : subd8_2 [-3, 0, 6] = true := by decide +kernel
theorem subd8_2_60 : subd8_2 [-3, 0, 7] = true := by decide +kernel
theorem subd8_2_61 : subd8_2 [-3, 1, -6] = true := by decide +kernel
theorem subd8_2_62 : subd8_2 [-3, 1, -5] = true := by decide +kernel
theorem subd8_2_63 : subd8_2 [-3, 1, -4] = true := by decide +kernel
theorem sbd8_2_1 : ∀ q ∈ blkd8_2_1, subd8_2 q = true := by
  unfold blkd8_2_1
  exact List.forall_mem_cons.2 ⟨subd8_2_32, List.forall_mem_cons.2 ⟨subd8_2_33, List.forall_mem_cons.2 ⟨subd8_2_34, List.forall_mem_cons.2 ⟨subd8_2_35, List.forall_mem_cons.2 ⟨subd8_2_36, List.forall_mem_cons.2 ⟨subd8_2_37, List.forall_mem_cons.2 ⟨subd8_2_38, List.forall_mem_cons.2 ⟨subd8_2_39, List.forall_mem_cons.2 ⟨subd8_2_40, List.forall_mem_cons.2 ⟨subd8_2_41, List.forall_mem_cons.2 ⟨subd8_2_42, List.forall_mem_cons.2 ⟨subd8_2_43, List.forall_mem_cons.2 ⟨subd8_2_44, List.forall_mem_cons.2 ⟨subd8_2_45, List.forall_mem_cons.2 ⟨subd8_2_46, List.forall_mem_cons.2 ⟨subd8_2_47, List.forall_mem_cons.2 ⟨subd8_2_48, List.forall_mem_cons.2 ⟨subd8_2_49, List.forall_mem_cons.2 ⟨subd8_2_50, List.forall_mem_cons.2 ⟨subd8_2_51, List.forall_mem_cons.2 ⟨subd8_2_52, List.forall_mem_cons.2 ⟨subd8_2_53, List.forall_mem_cons.2 ⟨subd8_2_54, List.forall_mem_cons.2 ⟨subd8_2_55, List.forall_mem_cons.2 ⟨subd8_2_56, List.forall_mem_cons.2 ⟨subd8_2_57, List.forall_mem_cons.2 ⟨subd8_2_58, List.forall_mem_cons.2 ⟨subd8_2_59, List.forall_mem_cons.2 ⟨subd8_2_60, List.forall_mem_cons.2 ⟨subd8_2_61, List.forall_mem_cons.2 ⟨subd8_2_62, List.forall_mem_cons.2 ⟨subd8_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_64 : subd8_2 [-3, 1, -3] = true := by decide +kernel
theorem subd8_2_65 : subd8_2 [-3, 1, -2] = true := by decide +kernel
theorem subd8_2_66 : subd8_2 [-3, 1, -1] = true := by decide +kernel
theorem subd8_2_67 : subd8_2 [-3, 1, 0] = true := by decide +kernel
theorem subd8_2_68 : subd8_2 [-3, 1, 1] = true := by decide +kernel
theorem subd8_2_69 : subd8_2 [-3, 1, 2] = true := by decide +kernel
theorem subd8_2_70 : subd8_2 [-3, 1, 3] = true := by decide +kernel
theorem subd8_2_71 : subd8_2 [-3, 1, 4] = true := by decide +kernel
theorem subd8_2_72 : subd8_2 [-3, 1, 5] = true := by decide +kernel
theorem subd8_2_73 : subd8_2 [-3, 1, 6] = true := by decide +kernel
theorem subd8_2_74 : subd8_2 [-3, 1, 7] = true := by decide +kernel
theorem subd8_2_75 : subd8_2 [-3, 2, -6] = true := by decide +kernel
theorem subd8_2_76 : subd8_2 [-3, 2, -5] = true := by decide +kernel
theorem subd8_2_77 : subd8_2 [-3, 2, -4] = true := by decide +kernel
theorem subd8_2_78 : subd8_2 [-3, 2, -3] = true := by decide +kernel
theorem subd8_2_79 : subd8_2 [-3, 2, -2] = true := by decide +kernel
theorem subd8_2_80 : subd8_2 [-3, 2, -1] = true := by decide +kernel
theorem subd8_2_81 : subd8_2 [-3, 2, 0] = true := by decide +kernel
theorem subd8_2_82 : subd8_2 [-3, 2, 1] = true := by decide +kernel
theorem subd8_2_83 : subd8_2 [-3, 2, 2] = true := by decide +kernel
theorem subd8_2_84 : subd8_2 [-3, 2, 3] = true := by decide +kernel
theorem subd8_2_85 : subd8_2 [-3, 2, 4] = true := by decide +kernel
theorem subd8_2_86 : subd8_2 [-3, 2, 5] = true := by decide +kernel
theorem subd8_2_87 : subd8_2 [-3, 2, 6] = true := by decide +kernel
theorem subd8_2_88 : subd8_2 [-3, 2, 7] = true := by decide +kernel
theorem subd8_2_89 : subd8_2 [-3, 3] = true := by decide +kernel
theorem subd8_2_90 : subd8_2 [-3, 4] = true := by decide +kernel
theorem subd8_2_91 : subd8_2 [-3, 5] = true := by decide +kernel
theorem subd8_2_92 : subd8_2 [-3, 6] = true := by decide +kernel
theorem subd8_2_93 : subd8_2 [-3, 7] = true := by decide +kernel
theorem subd8_2_94 : subd8_2 [-2, -6] = true := by decide +kernel
theorem subd8_2_95 : subd8_2 [-2, -5] = true := by decide +kernel
theorem sbd8_2_2 : ∀ q ∈ blkd8_2_2, subd8_2 q = true := by
  unfold blkd8_2_2
  exact List.forall_mem_cons.2 ⟨subd8_2_64, List.forall_mem_cons.2 ⟨subd8_2_65, List.forall_mem_cons.2 ⟨subd8_2_66, List.forall_mem_cons.2 ⟨subd8_2_67, List.forall_mem_cons.2 ⟨subd8_2_68, List.forall_mem_cons.2 ⟨subd8_2_69, List.forall_mem_cons.2 ⟨subd8_2_70, List.forall_mem_cons.2 ⟨subd8_2_71, List.forall_mem_cons.2 ⟨subd8_2_72, List.forall_mem_cons.2 ⟨subd8_2_73, List.forall_mem_cons.2 ⟨subd8_2_74, List.forall_mem_cons.2 ⟨subd8_2_75, List.forall_mem_cons.2 ⟨subd8_2_76, List.forall_mem_cons.2 ⟨subd8_2_77, List.forall_mem_cons.2 ⟨subd8_2_78, List.forall_mem_cons.2 ⟨subd8_2_79, List.forall_mem_cons.2 ⟨subd8_2_80, List.forall_mem_cons.2 ⟨subd8_2_81, List.forall_mem_cons.2 ⟨subd8_2_82, List.forall_mem_cons.2 ⟨subd8_2_83, List.forall_mem_cons.2 ⟨subd8_2_84, List.forall_mem_cons.2 ⟨subd8_2_85, List.forall_mem_cons.2 ⟨subd8_2_86, List.forall_mem_cons.2 ⟨subd8_2_87, List.forall_mem_cons.2 ⟨subd8_2_88, List.forall_mem_cons.2 ⟨subd8_2_89, List.forall_mem_cons.2 ⟨subd8_2_90, List.forall_mem_cons.2 ⟨subd8_2_91, List.forall_mem_cons.2 ⟨subd8_2_92, List.forall_mem_cons.2 ⟨subd8_2_93, List.forall_mem_cons.2 ⟨subd8_2_94, List.forall_mem_cons.2 ⟨subd8_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
