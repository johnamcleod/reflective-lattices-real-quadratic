import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_2_512 : subd6_2 [2, 0, -2] = true := by decide +kernel
theorem subd6_2_513 : subd6_2 [2, 0, -1] = true := by decide +kernel
theorem subd6_2_514 : subd6_2 [2, 0, 0] = true := by decide +kernel
theorem subd6_2_515 : subd6_2 [2, 0, 1] = true := by decide +kernel
theorem subd6_2_516 : subd6_2 [2, 0, 2] = true := by decide +kernel
theorem subd6_2_517 : subd6_2 [2, 0, 3] = true := by decide +kernel
theorem subd6_2_518 : subd6_2 [2, 0, 4] = true := by decide +kernel
theorem subd6_2_519 : subd6_2 [2, 0, 5] = true := by decide +kernel
theorem subd6_2_520 : subd6_2 [2, 0, 6] = true := by decide +kernel
theorem subd6_2_521 : subd6_2 [2, 0, 7] = true := by decide +kernel
theorem subd6_2_522 : subd6_2 [2, 0, 8] = true := by decide +kernel
theorem subd6_2_523 : subd6_2 [2, 0, 9] = true := by decide +kernel
theorem subd6_2_524 : subd6_2 [2, 0, 10] = true := by decide +kernel
theorem subd6_2_525 : subd6_2 [2, 1, -10] = true := by decide +kernel
theorem subd6_2_526 : subd6_2 [2, 1, -9] = true := by decide +kernel
theorem subd6_2_527 : subd6_2 [2, 1, -8] = true := by decide +kernel
theorem subd6_2_528 : subd6_2 [2, 1, -7] = true := by decide +kernel
theorem subd6_2_529 : subd6_2 [2, 1, -6] = true := by decide +kernel
theorem subd6_2_530 : subd6_2 [2, 1, -5] = true := by decide +kernel
theorem subd6_2_531 : subd6_2 [2, 1, -4] = true := by decide +kernel
theorem subd6_2_532 : subd6_2 [2, 1, -3] = true := by decide +kernel
theorem subd6_2_533 : subd6_2 [2, 1, -2] = true := by decide +kernel
theorem subd6_2_534 : subd6_2 [2, 1, -1] = true := by decide +kernel
theorem subd6_2_535 : subd6_2 [2, 1, 0] = true := by decide +kernel
theorem subd6_2_536 : subd6_2 [2, 1, 1] = true := by decide +kernel
theorem subd6_2_537 : subd6_2 [2, 1, 2] = true := by decide +kernel
theorem subd6_2_538 : subd6_2 [2, 1, 3] = true := by decide +kernel
theorem subd6_2_539 : subd6_2 [2, 1, 4] = true := by decide +kernel
theorem subd6_2_540 : subd6_2 [2, 1, 5] = true := by decide +kernel
theorem subd6_2_541 : subd6_2 [2, 1, 6] = true := by decide +kernel
theorem subd6_2_542 : subd6_2 [2, 1, 7] = true := by decide +kernel
theorem subd6_2_543 : subd6_2 [2, 1, 8] = true := by decide +kernel
theorem sbd6_2_16 : ∀ q ∈ blkd6_2_16, subd6_2 q = true := by
  unfold blkd6_2_16
  exact List.forall_mem_cons.2 ⟨subd6_2_512, List.forall_mem_cons.2 ⟨subd6_2_513, List.forall_mem_cons.2 ⟨subd6_2_514, List.forall_mem_cons.2 ⟨subd6_2_515, List.forall_mem_cons.2 ⟨subd6_2_516, List.forall_mem_cons.2 ⟨subd6_2_517, List.forall_mem_cons.2 ⟨subd6_2_518, List.forall_mem_cons.2 ⟨subd6_2_519, List.forall_mem_cons.2 ⟨subd6_2_520, List.forall_mem_cons.2 ⟨subd6_2_521, List.forall_mem_cons.2 ⟨subd6_2_522, List.forall_mem_cons.2 ⟨subd6_2_523, List.forall_mem_cons.2 ⟨subd6_2_524, List.forall_mem_cons.2 ⟨subd6_2_525, List.forall_mem_cons.2 ⟨subd6_2_526, List.forall_mem_cons.2 ⟨subd6_2_527, List.forall_mem_cons.2 ⟨subd6_2_528, List.forall_mem_cons.2 ⟨subd6_2_529, List.forall_mem_cons.2 ⟨subd6_2_530, List.forall_mem_cons.2 ⟨subd6_2_531, List.forall_mem_cons.2 ⟨subd6_2_532, List.forall_mem_cons.2 ⟨subd6_2_533, List.forall_mem_cons.2 ⟨subd6_2_534, List.forall_mem_cons.2 ⟨subd6_2_535, List.forall_mem_cons.2 ⟨subd6_2_536, List.forall_mem_cons.2 ⟨subd6_2_537, List.forall_mem_cons.2 ⟨subd6_2_538, List.forall_mem_cons.2 ⟨subd6_2_539, List.forall_mem_cons.2 ⟨subd6_2_540, List.forall_mem_cons.2 ⟨subd6_2_541, List.forall_mem_cons.2 ⟨subd6_2_542, List.forall_mem_cons.2 ⟨subd6_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_544 : subd6_2 [3] = true := by decide +kernel
theorem sbd6_2_17 : ∀ q ∈ blkd6_2_17, subd6_2 q = true := by
  unfold blkd6_2_17
  exact List.forall_mem_cons.2 ⟨subd6_2_544, List.forall_mem_nil _⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [-5, -4] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-5, -3] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [-5, -2] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [-5, -1] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [-5, 0] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [-5, 1] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [-5, 2] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [-4, -5] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [-4, -4] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [-4, -3] = true := by decide +kernel
theorem subd6_3_10 : subd6_3 [-4, -2] = true := by decide +kernel
theorem subd6_3_11 : subd6_3 [-4, -1, -7] = true := by decide +kernel
theorem subd6_3_12 : subd6_3 [-4, -1, -6] = true := by decide +kernel
theorem subd6_3_13 : subd6_3 [-4, -1, -5] = true := by decide +kernel
theorem subd6_3_14 : subd6_3 [-4, -1, -4] = true := by decide +kernel
theorem subd6_3_15 : subd6_3 [-4, -1, -3] = true := by decide +kernel
theorem subd6_3_16 : subd6_3 [-4, -1, -2] = true := by decide +kernel
theorem subd6_3_17 : subd6_3 [-4, -1, -1] = true := by decide +kernel
theorem subd6_3_18 : subd6_3 [-4, -1, 0] = true := by decide +kernel
theorem subd6_3_19 : subd6_3 [-4, -1, 1] = true := by decide +kernel
theorem subd6_3_20 : subd6_3 [-4, -1, 2] = true := by decide +kernel
theorem subd6_3_21 : subd6_3 [-4, -1, 3] = true := by decide +kernel
theorem subd6_3_22 : subd6_3 [-4, -1, 4] = true := by decide +kernel
theorem subd6_3_23 : subd6_3 [-4, -1, 5] = true := by decide +kernel
theorem subd6_3_24 : subd6_3 [-4, -1, 6] = true := by decide +kernel
theorem subd6_3_25 : subd6_3 [-4, 0, -8] = true := by decide +kernel
theorem subd6_3_26 : subd6_3 [-4, 0, -7] = true := by decide +kernel
theorem subd6_3_27 : subd6_3 [-4, 0, -6] = true := by decide +kernel
theorem subd6_3_28 : subd6_3 [-4, 0, -5] = true := by decide +kernel
theorem subd6_3_29 : subd6_3 [-4, 0, -4] = true := by decide +kernel
theorem subd6_3_30 : subd6_3 [-4, 0, -3] = true := by decide +kernel
theorem subd6_3_31 : subd6_3 [-4, 0, -2] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_cons.2 ⟨subd6_3_10, List.forall_mem_cons.2 ⟨subd6_3_11, List.forall_mem_cons.2 ⟨subd6_3_12, List.forall_mem_cons.2 ⟨subd6_3_13, List.forall_mem_cons.2 ⟨subd6_3_14, List.forall_mem_cons.2 ⟨subd6_3_15, List.forall_mem_cons.2 ⟨subd6_3_16, List.forall_mem_cons.2 ⟨subd6_3_17, List.forall_mem_cons.2 ⟨subd6_3_18, List.forall_mem_cons.2 ⟨subd6_3_19, List.forall_mem_cons.2 ⟨subd6_3_20, List.forall_mem_cons.2 ⟨subd6_3_21, List.forall_mem_cons.2 ⟨subd6_3_22, List.forall_mem_cons.2 ⟨subd6_3_23, List.forall_mem_cons.2 ⟨subd6_3_24, List.forall_mem_cons.2 ⟨subd6_3_25, List.forall_mem_cons.2 ⟨subd6_3_26, List.forall_mem_cons.2 ⟨subd6_3_27, List.forall_mem_cons.2 ⟨subd6_3_28, List.forall_mem_cons.2 ⟨subd6_3_29, List.forall_mem_cons.2 ⟨subd6_3_30, List.forall_mem_cons.2 ⟨subd6_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_32 : subd6_3 [-4, 0, -1] = true := by decide +kernel
theorem subd6_3_33 : subd6_3 [-4, 0, 0] = true := by decide +kernel
theorem subd6_3_34 : subd6_3 [-4, 0, 1] = true := by decide +kernel
theorem subd6_3_35 : subd6_3 [-4, 0, 2] = true := by decide +kernel
theorem subd6_3_36 : subd6_3 [-4, 0, 3] = true := by decide +kernel
theorem subd6_3_37 : subd6_3 [-4, 0, 4] = true := by decide +kernel
theorem subd6_3_38 : subd6_3 [-4, 0, 5] = true := by decide +kernel
theorem subd6_3_39 : subd6_3 [-4, 1] = true := by decide +kernel
theorem subd6_3_40 : subd6_3 [-4, 2] = true := by decide +kernel
theorem subd6_3_41 : subd6_3 [-4, 3] = true := by decide +kernel
theorem subd6_3_42 : subd6_3 [-3, -6] = true := by decide +kernel
theorem subd6_3_43 : subd6_3 [-3, -5] = true := by decide +kernel
theorem subd6_3_44 : subd6_3 [-3, -4] = true := by decide +kernel
theorem subd6_3_45 : subd6_3 [-3, -3, -7] = true := by decide +kernel
theorem subd6_3_46 : subd6_3 [-3, -3, -6] = true := by decide +kernel
theorem subd6_3_47 : subd6_3 [-3, -3, -5] = true := by decide +kernel
theorem subd6_3_48 : subd6_3 [-3, -3, -4] = true := by decide +kernel
theorem subd6_3_49 : subd6_3 [-3, -3, -3] = true := by decide +kernel
theorem subd6_3_50 : subd6_3 [-3, -3, -2] = true := by decide +kernel
theorem subd6_3_51 : subd6_3 [-3, -3, -1] = true := by decide +kernel
theorem subd6_3_52 : subd6_3 [-3, -3, 0] = true := by decide +kernel
theorem subd6_3_53 : subd6_3 [-3, -3, 1] = true := by decide +kernel
theorem subd6_3_54 : subd6_3 [-3, -3, 2] = true := by decide +kernel
theorem subd6_3_55 : subd6_3 [-3, -3, 3] = true := by decide +kernel
theorem subd6_3_56 : subd6_3 [-3, -3, 4] = true := by decide +kernel
theorem subd6_3_57 : subd6_3 [-3, -3, 5] = true := by decide +kernel
theorem subd6_3_58 : subd6_3 [-3, -3, 6] = true := by decide +kernel
theorem subd6_3_59 : subd6_3 [-3, -3, 7] = true := by decide +kernel
theorem subd6_3_60 : subd6_3 [-3, -2, -8] = true := by decide +kernel
theorem subd6_3_61 : subd6_3 [-3, -2, -7] = true := by decide +kernel
theorem subd6_3_62 : subd6_3 [-3, -2, -6] = true := by decide +kernel
theorem subd6_3_63 : subd6_3 [-3, -2, -5] = true := by decide +kernel
theorem sbd6_3_1 : ∀ q ∈ blkd6_3_1, subd6_3 q = true := by
  unfold blkd6_3_1
  exact List.forall_mem_cons.2 ⟨subd6_3_32, List.forall_mem_cons.2 ⟨subd6_3_33, List.forall_mem_cons.2 ⟨subd6_3_34, List.forall_mem_cons.2 ⟨subd6_3_35, List.forall_mem_cons.2 ⟨subd6_3_36, List.forall_mem_cons.2 ⟨subd6_3_37, List.forall_mem_cons.2 ⟨subd6_3_38, List.forall_mem_cons.2 ⟨subd6_3_39, List.forall_mem_cons.2 ⟨subd6_3_40, List.forall_mem_cons.2 ⟨subd6_3_41, List.forall_mem_cons.2 ⟨subd6_3_42, List.forall_mem_cons.2 ⟨subd6_3_43, List.forall_mem_cons.2 ⟨subd6_3_44, List.forall_mem_cons.2 ⟨subd6_3_45, List.forall_mem_cons.2 ⟨subd6_3_46, List.forall_mem_cons.2 ⟨subd6_3_47, List.forall_mem_cons.2 ⟨subd6_3_48, List.forall_mem_cons.2 ⟨subd6_3_49, List.forall_mem_cons.2 ⟨subd6_3_50, List.forall_mem_cons.2 ⟨subd6_3_51, List.forall_mem_cons.2 ⟨subd6_3_52, List.forall_mem_cons.2 ⟨subd6_3_53, List.forall_mem_cons.2 ⟨subd6_3_54, List.forall_mem_cons.2 ⟨subd6_3_55, List.forall_mem_cons.2 ⟨subd6_3_56, List.forall_mem_cons.2 ⟨subd6_3_57, List.forall_mem_cons.2 ⟨subd6_3_58, List.forall_mem_cons.2 ⟨subd6_3_59, List.forall_mem_cons.2 ⟨subd6_3_60, List.forall_mem_cons.2 ⟨subd6_3_61, List.forall_mem_cons.2 ⟨subd6_3_62, List.forall_mem_cons.2 ⟨subd6_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_64 : subd6_3 [-3, -2, -4] = true := by decide +kernel
theorem subd6_3_65 : subd6_3 [-3, -2, -3] = true := by decide +kernel
theorem subd6_3_66 : subd6_3 [-3, -2, -2] = true := by decide +kernel
theorem subd6_3_67 : subd6_3 [-3, -2, -1] = true := by decide +kernel
theorem subd6_3_68 : subd6_3 [-3, -2, 0] = true := by decide +kernel
theorem subd6_3_69 : subd6_3 [-3, -2, 1] = true := by decide +kernel
theorem subd6_3_70 : subd6_3 [-3, -2, 2] = true := by decide +kernel
theorem subd6_3_71 : subd6_3 [-3, -2, 3] = true := by decide +kernel
theorem subd6_3_72 : subd6_3 [-3, -2, 4] = true := by decide +kernel
theorem subd6_3_73 : subd6_3 [-3, -2, 5] = true := by decide +kernel
theorem subd6_3_74 : subd6_3 [-3, -2, 6] = true := by decide +kernel
theorem subd6_3_75 : subd6_3 [-3, -2, 7] = true := by decide +kernel
theorem subd6_3_76 : subd6_3 [-3, -1, -8] = true := by decide +kernel
theorem subd6_3_77 : subd6_3 [-3, -1, -7] = true := by decide +kernel
theorem subd6_3_78 : subd6_3 [-3, -1, -6] = true := by decide +kernel
theorem subd6_3_79 : subd6_3 [-3, -1, -5] = true := by decide +kernel
theorem subd6_3_80 : subd6_3 [-3, -1, -4] = true := by decide +kernel
theorem subd6_3_81 : subd6_3 [-3, -1, -3] = true := by decide +kernel
theorem subd6_3_82 : subd6_3 [-3, -1, -2] = true := by decide +kernel
theorem subd6_3_83 : subd6_3 [-3, -1, -1] = true := by decide +kernel
theorem subd6_3_84 : subd6_3 [-3, -1, 0] = true := by decide +kernel
theorem subd6_3_85 : subd6_3 [-3, -1, 1] = true := by decide +kernel
theorem subd6_3_86 : subd6_3 [-3, -1, 2] = true := by decide +kernel
theorem subd6_3_87 : subd6_3 [-3, -1, 3] = true := by decide +kernel
theorem subd6_3_88 : subd6_3 [-3, -1, 4] = true := by decide +kernel
theorem subd6_3_89 : subd6_3 [-3, -1, 5] = true := by decide +kernel
theorem subd6_3_90 : subd6_3 [-3, -1, 6] = true := by decide +kernel
theorem subd6_3_91 : subd6_3 [-3, -1, 7] = true := by decide +kernel
theorem subd6_3_92 : subd6_3 [-3, 0, -9] = true := by decide +kernel
theorem subd6_3_93 : subd6_3 [-3, 0, -8] = true := by decide +kernel
theorem subd6_3_94 : subd6_3 [-3, 0, -7] = true := by decide +kernel
theorem subd6_3_95 : subd6_3 [-3, 0, -6] = true := by decide +kernel
theorem sbd6_3_2 : ∀ q ∈ blkd6_3_2, subd6_3 q = true := by
  unfold blkd6_3_2
  exact List.forall_mem_cons.2 ⟨subd6_3_64, List.forall_mem_cons.2 ⟨subd6_3_65, List.forall_mem_cons.2 ⟨subd6_3_66, List.forall_mem_cons.2 ⟨subd6_3_67, List.forall_mem_cons.2 ⟨subd6_3_68, List.forall_mem_cons.2 ⟨subd6_3_69, List.forall_mem_cons.2 ⟨subd6_3_70, List.forall_mem_cons.2 ⟨subd6_3_71, List.forall_mem_cons.2 ⟨subd6_3_72, List.forall_mem_cons.2 ⟨subd6_3_73, List.forall_mem_cons.2 ⟨subd6_3_74, List.forall_mem_cons.2 ⟨subd6_3_75, List.forall_mem_cons.2 ⟨subd6_3_76, List.forall_mem_cons.2 ⟨subd6_3_77, List.forall_mem_cons.2 ⟨subd6_3_78, List.forall_mem_cons.2 ⟨subd6_3_79, List.forall_mem_cons.2 ⟨subd6_3_80, List.forall_mem_cons.2 ⟨subd6_3_81, List.forall_mem_cons.2 ⟨subd6_3_82, List.forall_mem_cons.2 ⟨subd6_3_83, List.forall_mem_cons.2 ⟨subd6_3_84, List.forall_mem_cons.2 ⟨subd6_3_85, List.forall_mem_cons.2 ⟨subd6_3_86, List.forall_mem_cons.2 ⟨subd6_3_87, List.forall_mem_cons.2 ⟨subd6_3_88, List.forall_mem_cons.2 ⟨subd6_3_89, List.forall_mem_cons.2 ⟨subd6_3_90, List.forall_mem_cons.2 ⟨subd6_3_91, List.forall_mem_cons.2 ⟨subd6_3_92, List.forall_mem_cons.2 ⟨subd6_3_93, List.forall_mem_cons.2 ⟨subd6_3_94, List.forall_mem_cons.2 ⟨subd6_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_96 : subd6_3 [-3, 0, -5] = true := by decide +kernel
theorem subd6_3_97 : subd6_3 [-3, 0, -4] = true := by decide +kernel
theorem subd6_3_98 : subd6_3 [-3, 0, -3] = true := by decide +kernel
theorem subd6_3_99 : subd6_3 [-3, 0, -2] = true := by decide +kernel
theorem subd6_3_100 : subd6_3 [-3, 0, -1] = true := by decide +kernel
theorem subd6_3_101 : subd6_3 [-3, 0, 0] = true := by decide +kernel
theorem subd6_3_102 : subd6_3 [-3, 0, 1] = true := by decide +kernel
theorem subd6_3_103 : subd6_3 [-3, 0, 2] = true := by decide +kernel
theorem subd6_3_104 : subd6_3 [-3, 0, 3] = true := by decide +kernel
theorem subd6_3_105 : subd6_3 [-3, 0, 4] = true := by decide +kernel
theorem subd6_3_106 : subd6_3 [-3, 0, 5] = true := by decide +kernel
theorem subd6_3_107 : subd6_3 [-3, 0, 6] = true := by decide +kernel
theorem subd6_3_108 : subd6_3 [-3, 0, 7] = true := by decide +kernel
theorem subd6_3_109 : subd6_3 [-3, 1, -9] = true := by decide +kernel
theorem subd6_3_110 : subd6_3 [-3, 1, -8] = true := by decide +kernel
theorem subd6_3_111 : subd6_3 [-3, 1, -7] = true := by decide +kernel
theorem subd6_3_112 : subd6_3 [-3, 1, -6] = true := by decide +kernel
theorem subd6_3_113 : subd6_3 [-3, 1, -5] = true := by decide +kernel
theorem subd6_3_114 : subd6_3 [-3, 1, -4] = true := by decide +kernel
theorem subd6_3_115 : subd6_3 [-3, 1, -3] = true := by decide +kernel
theorem subd6_3_116 : subd6_3 [-3, 1, -2] = true := by decide +kernel
theorem subd6_3_117 : subd6_3 [-3, 1, -1] = true := by decide +kernel
theorem subd6_3_118 : subd6_3 [-3, 1, 0] = true := by decide +kernel
theorem subd6_3_119 : subd6_3 [-3, 1, 1] = true := by decide +kernel
theorem subd6_3_120 : subd6_3 [-3, 1, 2] = true := by decide +kernel
theorem subd6_3_121 : subd6_3 [-3, 1, 3] = true := by decide +kernel
theorem subd6_3_122 : subd6_3 [-3, 1, 4] = true := by decide +kernel
theorem subd6_3_123 : subd6_3 [-3, 1, 5] = true := by decide +kernel
theorem subd6_3_124 : subd6_3 [-3, 1, 6] = true := by decide +kernel
theorem subd6_3_125 : subd6_3 [-3, 2, -8] = true := by decide +kernel
theorem subd6_3_126 : subd6_3 [-3, 2, -7] = true := by decide +kernel
theorem subd6_3_127 : subd6_3 [-3, 2, -6] = true := by decide +kernel
theorem sbd6_3_3 : ∀ q ∈ blkd6_3_3, subd6_3 q = true := by
  unfold blkd6_3_3
  exact List.forall_mem_cons.2 ⟨subd6_3_96, List.forall_mem_cons.2 ⟨subd6_3_97, List.forall_mem_cons.2 ⟨subd6_3_98, List.forall_mem_cons.2 ⟨subd6_3_99, List.forall_mem_cons.2 ⟨subd6_3_100, List.forall_mem_cons.2 ⟨subd6_3_101, List.forall_mem_cons.2 ⟨subd6_3_102, List.forall_mem_cons.2 ⟨subd6_3_103, List.forall_mem_cons.2 ⟨subd6_3_104, List.forall_mem_cons.2 ⟨subd6_3_105, List.forall_mem_cons.2 ⟨subd6_3_106, List.forall_mem_cons.2 ⟨subd6_3_107, List.forall_mem_cons.2 ⟨subd6_3_108, List.forall_mem_cons.2 ⟨subd6_3_109, List.forall_mem_cons.2 ⟨subd6_3_110, List.forall_mem_cons.2 ⟨subd6_3_111, List.forall_mem_cons.2 ⟨subd6_3_112, List.forall_mem_cons.2 ⟨subd6_3_113, List.forall_mem_cons.2 ⟨subd6_3_114, List.forall_mem_cons.2 ⟨subd6_3_115, List.forall_mem_cons.2 ⟨subd6_3_116, List.forall_mem_cons.2 ⟨subd6_3_117, List.forall_mem_cons.2 ⟨subd6_3_118, List.forall_mem_cons.2 ⟨subd6_3_119, List.forall_mem_cons.2 ⟨subd6_3_120, List.forall_mem_cons.2 ⟨subd6_3_121, List.forall_mem_cons.2 ⟨subd6_3_122, List.forall_mem_cons.2 ⟨subd6_3_123, List.forall_mem_cons.2 ⟨subd6_3_124, List.forall_mem_cons.2 ⟨subd6_3_125, List.forall_mem_cons.2 ⟨subd6_3_126, List.forall_mem_cons.2 ⟨subd6_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_128 : subd6_3 [-3, 2, -5] = true := by decide +kernel
theorem subd6_3_129 : subd6_3 [-3, 2, -4] = true := by decide +kernel
theorem subd6_3_130 : subd6_3 [-3, 2, -3] = true := by decide +kernel
theorem subd6_3_131 : subd6_3 [-3, 2, -2] = true := by decide +kernel
theorem subd6_3_132 : subd6_3 [-3, 2, -1] = true := by decide +kernel
theorem subd6_3_133 : subd6_3 [-3, 2, 0] = true := by decide +kernel
theorem subd6_3_134 : subd6_3 [-3, 2, 1] = true := by decide +kernel
theorem subd6_3_135 : subd6_3 [-3, 2, 2] = true := by decide +kernel
theorem subd6_3_136 : subd6_3 [-3, 2, 3] = true := by decide +kernel
theorem subd6_3_137 : subd6_3 [-3, 2, 4] = true := by decide +kernel
theorem subd6_3_138 : subd6_3 [-3, 2, 5] = true := by decide +kernel
theorem subd6_3_139 : subd6_3 [-3, 3] = true := by decide +kernel
theorem subd6_3_140 : subd6_3 [-3, 4] = true := by decide +kernel
theorem subd6_3_141 : subd6_3 [-2, -6] = true := by decide +kernel
theorem subd6_3_142 : subd6_3 [-2, -5] = true := by decide +kernel
theorem subd6_3_143 : subd6_3 [-2, -4, -6] = true := by decide +kernel
theorem subd6_3_144 : subd6_3 [-2, -4, -5] = true := by decide +kernel
theorem subd6_3_145 : subd6_3 [-2, -4, -4] = true := by decide +kernel
theorem subd6_3_146 : subd6_3 [-2, -4, -3] = true := by decide +kernel
theorem subd6_3_147 : subd6_3 [-2, -4, -2] = true := by decide +kernel
theorem subd6_3_148 : subd6_3 [-2, -4, -1] = true := by decide +kernel
theorem subd6_3_149 : subd6_3 [-2, -4, 0] = true := by decide +kernel
theorem subd6_3_150 : subd6_3 [-2, -4, 1] = true := by decide +kernel
theorem subd6_3_151 : subd6_3 [-2, -4, 2] = true := by decide +kernel
theorem subd6_3_152 : subd6_3 [-2, -4, 3] = true := by decide +kernel
theorem subd6_3_153 : subd6_3 [-2, -4, 4] = true := by decide +kernel
theorem subd6_3_154 : subd6_3 [-2, -4, 5] = true := by decide +kernel
theorem subd6_3_155 : subd6_3 [-2, -4, 6] = true := by decide +kernel
theorem subd6_3_156 : subd6_3 [-2, -4, 7] = true := by decide +kernel
theorem subd6_3_157 : subd6_3 [-2, -3, -7] = true := by decide +kernel
theorem subd6_3_158 : subd6_3 [-2, -3, -6] = true := by decide +kernel
theorem subd6_3_159 : subd6_3 [-2, -3, -5] = true := by decide +kernel
theorem sbd6_3_4 : ∀ q ∈ blkd6_3_4, subd6_3 q = true := by
  unfold blkd6_3_4
  exact List.forall_mem_cons.2 ⟨subd6_3_128, List.forall_mem_cons.2 ⟨subd6_3_129, List.forall_mem_cons.2 ⟨subd6_3_130, List.forall_mem_cons.2 ⟨subd6_3_131, List.forall_mem_cons.2 ⟨subd6_3_132, List.forall_mem_cons.2 ⟨subd6_3_133, List.forall_mem_cons.2 ⟨subd6_3_134, List.forall_mem_cons.2 ⟨subd6_3_135, List.forall_mem_cons.2 ⟨subd6_3_136, List.forall_mem_cons.2 ⟨subd6_3_137, List.forall_mem_cons.2 ⟨subd6_3_138, List.forall_mem_cons.2 ⟨subd6_3_139, List.forall_mem_cons.2 ⟨subd6_3_140, List.forall_mem_cons.2 ⟨subd6_3_141, List.forall_mem_cons.2 ⟨subd6_3_142, List.forall_mem_cons.2 ⟨subd6_3_143, List.forall_mem_cons.2 ⟨subd6_3_144, List.forall_mem_cons.2 ⟨subd6_3_145, List.forall_mem_cons.2 ⟨subd6_3_146, List.forall_mem_cons.2 ⟨subd6_3_147, List.forall_mem_cons.2 ⟨subd6_3_148, List.forall_mem_cons.2 ⟨subd6_3_149, List.forall_mem_cons.2 ⟨subd6_3_150, List.forall_mem_cons.2 ⟨subd6_3_151, List.forall_mem_cons.2 ⟨subd6_3_152, List.forall_mem_cons.2 ⟨subd6_3_153, List.forall_mem_cons.2 ⟨subd6_3_154, List.forall_mem_cons.2 ⟨subd6_3_155, List.forall_mem_cons.2 ⟨subd6_3_156, List.forall_mem_cons.2 ⟨subd6_3_157, List.forall_mem_cons.2 ⟨subd6_3_158, List.forall_mem_cons.2 ⟨subd6_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_160 : subd6_3 [-2, -3, -4] = true := by decide +kernel
theorem subd6_3_161 : subd6_3 [-2, -3, -3] = true := by decide +kernel
theorem subd6_3_162 : subd6_3 [-2, -3, -2] = true := by decide +kernel
theorem subd6_3_163 : subd6_3 [-2, -3, -1] = true := by decide +kernel
theorem subd6_3_164 : subd6_3 [-2, -3, 0] = true := by decide +kernel
theorem subd6_3_165 : subd6_3 [-2, -3, 1] = true := by decide +kernel
theorem subd6_3_166 : subd6_3 [-2, -3, 2] = true := by decide +kernel
theorem subd6_3_167 : subd6_3 [-2, -3, 3] = true := by decide +kernel
theorem subd6_3_168 : subd6_3 [-2, -3, 4] = true := by decide +kernel
theorem subd6_3_169 : subd6_3 [-2, -3, 5] = true := by decide +kernel
theorem subd6_3_170 : subd6_3 [-2, -3, 6] = true := by decide +kernel
theorem subd6_3_171 : subd6_3 [-2, -3, 7] = true := by decide +kernel
theorem subd6_3_172 : subd6_3 [-2, -3, 8] = true := by decide +kernel
theorem subd6_3_173 : subd6_3 [-2, -2, -8] = true := by decide +kernel
theorem subd6_3_174 : subd6_3 [-2, -2, -7] = true := by decide +kernel
theorem subd6_3_175 : subd6_3 [-2, -2, -6] = true := by decide +kernel
theorem subd6_3_176 : subd6_3 [-2, -2, -5] = true := by decide +kernel
theorem subd6_3_177 : subd6_3 [-2, -2, -4] = true := by decide +kernel
theorem subd6_3_178 : subd6_3 [-2, -2, -3] = true := by decide +kernel
theorem subd6_3_179 : subd6_3 [-2, -2, -2] = true := by decide +kernel
theorem subd6_3_180 : subd6_3 [-2, -2, -1] = true := by decide +kernel
theorem subd6_3_181 : subd6_3 [-2, -2, 0] = true := by decide +kernel
theorem subd6_3_182 : subd6_3 [-2, -2, 1] = true := by decide +kernel
theorem subd6_3_183 : subd6_3 [-2, -2, 2] = true := by decide +kernel
theorem subd6_3_184 : subd6_3 [-2, -2, 3] = true := by decide +kernel
theorem subd6_3_185 : subd6_3 [-2, -2, 4] = true := by decide +kernel
theorem subd6_3_186 : subd6_3 [-2, -2, 5] = true := by decide +kernel
theorem subd6_3_187 : subd6_3 [-2, -2, 6] = true := by decide +kernel
theorem subd6_3_188 : subd6_3 [-2, -2, 7] = true := by decide +kernel
theorem subd6_3_189 : subd6_3 [-2, -2, 8] = true := by decide +kernel
theorem subd6_3_190 : subd6_3 [-2, -1, -9] = true := by decide +kernel
theorem subd6_3_191 : subd6_3 [-2, -1, -8] = true := by decide +kernel
theorem sbd6_3_5 : ∀ q ∈ blkd6_3_5, subd6_3 q = true := by
  unfold blkd6_3_5
  exact List.forall_mem_cons.2 ⟨subd6_3_160, List.forall_mem_cons.2 ⟨subd6_3_161, List.forall_mem_cons.2 ⟨subd6_3_162, List.forall_mem_cons.2 ⟨subd6_3_163, List.forall_mem_cons.2 ⟨subd6_3_164, List.forall_mem_cons.2 ⟨subd6_3_165, List.forall_mem_cons.2 ⟨subd6_3_166, List.forall_mem_cons.2 ⟨subd6_3_167, List.forall_mem_cons.2 ⟨subd6_3_168, List.forall_mem_cons.2 ⟨subd6_3_169, List.forall_mem_cons.2 ⟨subd6_3_170, List.forall_mem_cons.2 ⟨subd6_3_171, List.forall_mem_cons.2 ⟨subd6_3_172, List.forall_mem_cons.2 ⟨subd6_3_173, List.forall_mem_cons.2 ⟨subd6_3_174, List.forall_mem_cons.2 ⟨subd6_3_175, List.forall_mem_cons.2 ⟨subd6_3_176, List.forall_mem_cons.2 ⟨subd6_3_177, List.forall_mem_cons.2 ⟨subd6_3_178, List.forall_mem_cons.2 ⟨subd6_3_179, List.forall_mem_cons.2 ⟨subd6_3_180, List.forall_mem_cons.2 ⟨subd6_3_181, List.forall_mem_cons.2 ⟨subd6_3_182, List.forall_mem_cons.2 ⟨subd6_3_183, List.forall_mem_cons.2 ⟨subd6_3_184, List.forall_mem_cons.2 ⟨subd6_3_185, List.forall_mem_cons.2 ⟨subd6_3_186, List.forall_mem_cons.2 ⟨subd6_3_187, List.forall_mem_cons.2 ⟨subd6_3_188, List.forall_mem_cons.2 ⟨subd6_3_189, List.forall_mem_cons.2 ⟨subd6_3_190, List.forall_mem_cons.2 ⟨subd6_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_192 : subd6_3 [-2, -1, -7] = true := by decide +kernel
theorem subd6_3_193 : subd6_3 [-2, -1, -6] = true := by decide +kernel
theorem subd6_3_194 : subd6_3 [-2, -1, -5] = true := by decide +kernel
theorem subd6_3_195 : subd6_3 [-2, -1, -4] = true := by decide +kernel
theorem subd6_3_196 : subd6_3 [-2, -1, -3] = true := by decide +kernel
theorem subd6_3_197 : subd6_3 [-2, -1, -2] = true := by decide +kernel
theorem subd6_3_198 : subd6_3 [-2, -1, -1] = true := by decide +kernel
theorem subd6_3_199 : subd6_3 [-2, -1, 0] = true := by decide +kernel
theorem subd6_3_200 : subd6_3 [-2, -1, 1] = true := by decide +kernel
theorem subd6_3_201 : subd6_3 [-2, -1, 2] = true := by decide +kernel
theorem subd6_3_202 : subd6_3 [-2, -1, 3] = true := by decide +kernel
theorem subd6_3_203 : subd6_3 [-2, -1, 4] = true := by decide +kernel
theorem subd6_3_204 : subd6_3 [-2, -1, 5] = true := by decide +kernel
theorem subd6_3_205 : subd6_3 [-2, -1, 6] = true := by decide +kernel
theorem subd6_3_206 : subd6_3 [-2, -1, 7] = true := by decide +kernel
theorem subd6_3_207 : subd6_3 [-2, -1, 8] = true := by decide +kernel
theorem subd6_3_208 : subd6_3 [-2, 0, -9] = true := by decide +kernel
theorem subd6_3_209 : subd6_3 [-2, 0, -8] = true := by decide +kernel
theorem subd6_3_210 : subd6_3 [-2, 0, -7] = true := by decide +kernel
theorem subd6_3_211 : subd6_3 [-2, 0, -6] = true := by decide +kernel
theorem subd6_3_212 : subd6_3 [-2, 0, -5] = true := by decide +kernel
theorem subd6_3_213 : subd6_3 [-2, 0, -4] = true := by decide +kernel
theorem subd6_3_214 : subd6_3 [-2, 0, -3] = true := by decide +kernel
theorem subd6_3_215 : subd6_3 [-2, 0, -2] = true := by decide +kernel
theorem subd6_3_216 : subd6_3 [-2, 0, -1] = true := by decide +kernel
theorem subd6_3_217 : subd6_3 [-2, 0, 0] = true := by decide +kernel
theorem subd6_3_218 : subd6_3 [-2, 0, 1] = true := by decide +kernel
theorem subd6_3_219 : subd6_3 [-2, 0, 2] = true := by decide +kernel
theorem subd6_3_220 : subd6_3 [-2, 0, 3] = true := by decide +kernel
theorem subd6_3_221 : subd6_3 [-2, 0, 4] = true := by decide +kernel
theorem subd6_3_222 : subd6_3 [-2, 0, 5] = true := by decide +kernel
theorem subd6_3_223 : subd6_3 [-2, 0, 6] = true := by decide +kernel
theorem sbd6_3_6 : ∀ q ∈ blkd6_3_6, subd6_3 q = true := by
  unfold blkd6_3_6
  exact List.forall_mem_cons.2 ⟨subd6_3_192, List.forall_mem_cons.2 ⟨subd6_3_193, List.forall_mem_cons.2 ⟨subd6_3_194, List.forall_mem_cons.2 ⟨subd6_3_195, List.forall_mem_cons.2 ⟨subd6_3_196, List.forall_mem_cons.2 ⟨subd6_3_197, List.forall_mem_cons.2 ⟨subd6_3_198, List.forall_mem_cons.2 ⟨subd6_3_199, List.forall_mem_cons.2 ⟨subd6_3_200, List.forall_mem_cons.2 ⟨subd6_3_201, List.forall_mem_cons.2 ⟨subd6_3_202, List.forall_mem_cons.2 ⟨subd6_3_203, List.forall_mem_cons.2 ⟨subd6_3_204, List.forall_mem_cons.2 ⟨subd6_3_205, List.forall_mem_cons.2 ⟨subd6_3_206, List.forall_mem_cons.2 ⟨subd6_3_207, List.forall_mem_cons.2 ⟨subd6_3_208, List.forall_mem_cons.2 ⟨subd6_3_209, List.forall_mem_cons.2 ⟨subd6_3_210, List.forall_mem_cons.2 ⟨subd6_3_211, List.forall_mem_cons.2 ⟨subd6_3_212, List.forall_mem_cons.2 ⟨subd6_3_213, List.forall_mem_cons.2 ⟨subd6_3_214, List.forall_mem_cons.2 ⟨subd6_3_215, List.forall_mem_cons.2 ⟨subd6_3_216, List.forall_mem_cons.2 ⟨subd6_3_217, List.forall_mem_cons.2 ⟨subd6_3_218, List.forall_mem_cons.2 ⟨subd6_3_219, List.forall_mem_cons.2 ⟨subd6_3_220, List.forall_mem_cons.2 ⟨subd6_3_221, List.forall_mem_cons.2 ⟨subd6_3_222, List.forall_mem_cons.2 ⟨subd6_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_224 : subd6_3 [-2, 0, 7] = true := by decide +kernel
theorem subd6_3_225 : subd6_3 [-2, 0, 8] = true := by decide +kernel
theorem subd6_3_226 : subd6_3 [-2, 1, -9] = true := by decide +kernel
theorem subd6_3_227 : subd6_3 [-2, 1, -8] = true := by decide +kernel
theorem subd6_3_228 : subd6_3 [-2, 1, -7] = true := by decide +kernel
theorem subd6_3_229 : subd6_3 [-2, 1, -6] = true := by decide +kernel
theorem subd6_3_230 : subd6_3 [-2, 1, -5] = true := by decide +kernel
theorem subd6_3_231 : subd6_3 [-2, 1, -4] = true := by decide +kernel
theorem subd6_3_232 : subd6_3 [-2, 1, -3] = true := by decide +kernel
theorem subd6_3_233 : subd6_3 [-2, 1, -2] = true := by decide +kernel
theorem subd6_3_234 : subd6_3 [-2, 1, -1] = true := by decide +kernel
theorem subd6_3_235 : subd6_3 [-2, 1, 0] = true := by decide +kernel
theorem subd6_3_236 : subd6_3 [-2, 1, 1] = true := by decide +kernel
theorem subd6_3_237 : subd6_3 [-2, 1, 2] = true := by decide +kernel
theorem subd6_3_238 : subd6_3 [-2, 1, 3] = true := by decide +kernel
theorem subd6_3_239 : subd6_3 [-2, 1, 4] = true := by decide +kernel
theorem subd6_3_240 : subd6_3 [-2, 1, 5] = true := by decide +kernel
theorem subd6_3_241 : subd6_3 [-2, 1, 6] = true := by decide +kernel
theorem subd6_3_242 : subd6_3 [-2, 1, 7] = true := by decide +kernel
theorem subd6_3_243 : subd6_3 [-2, 2, -9] = true := by decide +kernel
theorem subd6_3_244 : subd6_3 [-2, 2, -8] = true := by decide +kernel
theorem subd6_3_245 : subd6_3 [-2, 2, -7] = true := by decide +kernel
theorem subd6_3_246 : subd6_3 [-2, 2, -6] = true := by decide +kernel
theorem subd6_3_247 : subd6_3 [-2, 2, -5] = true := by decide +kernel
theorem subd6_3_248 : subd6_3 [-2, 2, -4] = true := by decide +kernel
theorem subd6_3_249 : subd6_3 [-2, 2, -3] = true := by decide +kernel
theorem subd6_3_250 : subd6_3 [-2, 2, -2] = true := by decide +kernel
theorem subd6_3_251 : subd6_3 [-2, 2, -1] = true := by decide +kernel
theorem subd6_3_252 : subd6_3 [-2, 2, 0] = true := by decide +kernel
theorem subd6_3_253 : subd6_3 [-2, 2, 1] = true := by decide +kernel
theorem subd6_3_254 : subd6_3 [-2, 2, 2] = true := by decide +kernel
theorem subd6_3_255 : subd6_3 [-2, 2, 3] = true := by decide +kernel
theorem sbd6_3_7 : ∀ q ∈ blkd6_3_7, subd6_3 q = true := by
  unfold blkd6_3_7
  exact List.forall_mem_cons.2 ⟨subd6_3_224, List.forall_mem_cons.2 ⟨subd6_3_225, List.forall_mem_cons.2 ⟨subd6_3_226, List.forall_mem_cons.2 ⟨subd6_3_227, List.forall_mem_cons.2 ⟨subd6_3_228, List.forall_mem_cons.2 ⟨subd6_3_229, List.forall_mem_cons.2 ⟨subd6_3_230, List.forall_mem_cons.2 ⟨subd6_3_231, List.forall_mem_cons.2 ⟨subd6_3_232, List.forall_mem_cons.2 ⟨subd6_3_233, List.forall_mem_cons.2 ⟨subd6_3_234, List.forall_mem_cons.2 ⟨subd6_3_235, List.forall_mem_cons.2 ⟨subd6_3_236, List.forall_mem_cons.2 ⟨subd6_3_237, List.forall_mem_cons.2 ⟨subd6_3_238, List.forall_mem_cons.2 ⟨subd6_3_239, List.forall_mem_cons.2 ⟨subd6_3_240, List.forall_mem_cons.2 ⟨subd6_3_241, List.forall_mem_cons.2 ⟨subd6_3_242, List.forall_mem_cons.2 ⟨subd6_3_243, List.forall_mem_cons.2 ⟨subd6_3_244, List.forall_mem_cons.2 ⟨subd6_3_245, List.forall_mem_cons.2 ⟨subd6_3_246, List.forall_mem_cons.2 ⟨subd6_3_247, List.forall_mem_cons.2 ⟨subd6_3_248, List.forall_mem_cons.2 ⟨subd6_3_249, List.forall_mem_cons.2 ⟨subd6_3_250, List.forall_mem_cons.2 ⟨subd6_3_251, List.forall_mem_cons.2 ⟨subd6_3_252, List.forall_mem_cons.2 ⟨subd6_3_253, List.forall_mem_cons.2 ⟨subd6_3_254, List.forall_mem_cons.2 ⟨subd6_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_256 : subd6_3 [-2, 2, 4] = true := by decide +kernel
theorem subd6_3_257 : subd6_3 [-2, 2, 5] = true := by decide +kernel
theorem subd6_3_258 : subd6_3 [-2, 2, 6] = true := by decide +kernel
theorem subd6_3_259 : subd6_3 [-2, 3, -9] = true := by decide +kernel
theorem subd6_3_260 : subd6_3 [-2, 3, -8] = true := by decide +kernel
theorem subd6_3_261 : subd6_3 [-2, 3, -7] = true := by decide +kernel
theorem subd6_3_262 : subd6_3 [-2, 3, -6] = true := by decide +kernel
theorem subd6_3_263 : subd6_3 [-2, 3, -5] = true := by decide +kernel
theorem subd6_3_264 : subd6_3 [-2, 3, -4] = true := by decide +kernel
theorem subd6_3_265 : subd6_3 [-2, 3, -3] = true := by decide +kernel
theorem subd6_3_266 : subd6_3 [-2, 3, -2] = true := by decide +kernel
theorem subd6_3_267 : subd6_3 [-2, 3, -1] = true := by decide +kernel
theorem subd6_3_268 : subd6_3 [-2, 3, 0] = true := by decide +kernel
theorem subd6_3_269 : subd6_3 [-2, 3, 1] = true := by decide +kernel
theorem subd6_3_270 : subd6_3 [-2, 3, 2] = true := by decide +kernel
theorem subd6_3_271 : subd6_3 [-2, 3, 3] = true := by decide +kernel
theorem subd6_3_272 : subd6_3 [-2, 3, 4] = true := by decide +kernel
theorem subd6_3_273 : subd6_3 [-2, 3, 5] = true := by decide +kernel
theorem subd6_3_274 : subd6_3 [-2, 4] = true := by decide +kernel
theorem subd6_3_275 : subd6_3 [-2, 5] = true := by decide +kernel
theorem subd6_3_276 : subd6_3 [-1, -7] = true := by decide +kernel
theorem subd6_3_277 : subd6_3 [-1, -6] = true := by decide +kernel
theorem subd6_3_278 : subd6_3 [-1, -5] = true := by decide +kernel
theorem subd6_3_279 : subd6_3 [-1, -4, -6] = true := by decide +kernel
theorem subd6_3_280 : subd6_3 [-1, -4, -5] = true := by decide +kernel
theorem subd6_3_281 : subd6_3 [-1, -4, -4] = true := by decide +kernel
theorem subd6_3_282 : subd6_3 [-1, -4, -3] = true := by decide +kernel
theorem subd6_3_283 : subd6_3 [-1, -4, -2] = true := by decide +kernel
theorem subd6_3_284 : subd6_3 [-1, -4, -1] = true := by decide +kernel
theorem subd6_3_285 : subd6_3 [-1, -4, 0] = true := by decide +kernel
theorem subd6_3_286 : subd6_3 [-1, -4, 1] = true := by decide +kernel
theorem subd6_3_287 : subd6_3 [-1, -4, 2] = true := by decide +kernel
theorem sbd6_3_8 : ∀ q ∈ blkd6_3_8, subd6_3 q = true := by
  unfold blkd6_3_8
  exact List.forall_mem_cons.2 ⟨subd6_3_256, List.forall_mem_cons.2 ⟨subd6_3_257, List.forall_mem_cons.2 ⟨subd6_3_258, List.forall_mem_cons.2 ⟨subd6_3_259, List.forall_mem_cons.2 ⟨subd6_3_260, List.forall_mem_cons.2 ⟨subd6_3_261, List.forall_mem_cons.2 ⟨subd6_3_262, List.forall_mem_cons.2 ⟨subd6_3_263, List.forall_mem_cons.2 ⟨subd6_3_264, List.forall_mem_cons.2 ⟨subd6_3_265, List.forall_mem_cons.2 ⟨subd6_3_266, List.forall_mem_cons.2 ⟨subd6_3_267, List.forall_mem_cons.2 ⟨subd6_3_268, List.forall_mem_cons.2 ⟨subd6_3_269, List.forall_mem_cons.2 ⟨subd6_3_270, List.forall_mem_cons.2 ⟨subd6_3_271, List.forall_mem_cons.2 ⟨subd6_3_272, List.forall_mem_cons.2 ⟨subd6_3_273, List.forall_mem_cons.2 ⟨subd6_3_274, List.forall_mem_cons.2 ⟨subd6_3_275, List.forall_mem_cons.2 ⟨subd6_3_276, List.forall_mem_cons.2 ⟨subd6_3_277, List.forall_mem_cons.2 ⟨subd6_3_278, List.forall_mem_cons.2 ⟨subd6_3_279, List.forall_mem_cons.2 ⟨subd6_3_280, List.forall_mem_cons.2 ⟨subd6_3_281, List.forall_mem_cons.2 ⟨subd6_3_282, List.forall_mem_cons.2 ⟨subd6_3_283, List.forall_mem_cons.2 ⟨subd6_3_284, List.forall_mem_cons.2 ⟨subd6_3_285, List.forall_mem_cons.2 ⟨subd6_3_286, List.forall_mem_cons.2 ⟨subd6_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_288 : subd6_3 [-1, -4, 3] = true := by decide +kernel
theorem subd6_3_289 : subd6_3 [-1, -4, 4] = true := by decide +kernel
theorem subd6_3_290 : subd6_3 [-1, -4, 5] = true := by decide +kernel
theorem subd6_3_291 : subd6_3 [-1, -4, 6] = true := by decide +kernel
theorem subd6_3_292 : subd6_3 [-1, -4, 7] = true := by decide +kernel
theorem subd6_3_293 : subd6_3 [-1, -4, 8] = true := by decide +kernel
theorem subd6_3_294 : subd6_3 [-1, -3, -7] = true := by decide +kernel
theorem subd6_3_295 : subd6_3 [-1, -3, -6] = true := by decide +kernel
theorem subd6_3_296 : subd6_3 [-1, -3, -5] = true := by decide +kernel
theorem subd6_3_297 : subd6_3 [-1, -3, -4] = true := by decide +kernel
theorem subd6_3_298 : subd6_3 [-1, -3, -3] = true := by decide +kernel
theorem subd6_3_299 : subd6_3 [-1, -3, -2] = true := by decide +kernel
theorem subd6_3_300 : subd6_3 [-1, -3, -1] = true := by decide +kernel
theorem subd6_3_301 : subd6_3 [-1, -3, 0] = true := by decide +kernel
theorem subd6_3_302 : subd6_3 [-1, -3, 1] = true := by decide +kernel
theorem subd6_3_303 : subd6_3 [-1, -3, 2] = true := by decide +kernel
theorem subd6_3_304 : subd6_3 [-1, -3, 3] = true := by decide +kernel
theorem subd6_3_305 : subd6_3 [-1, -3, 4] = true := by decide +kernel
theorem subd6_3_306 : subd6_3 [-1, -3, 5] = true := by decide +kernel
theorem subd6_3_307 : subd6_3 [-1, -3, 6] = true := by decide +kernel
theorem subd6_3_308 : subd6_3 [-1, -3, 7] = true := by decide +kernel
theorem subd6_3_309 : subd6_3 [-1, -3, 8] = true := by decide +kernel
theorem subd6_3_310 : subd6_3 [-1, -2, -8] = true := by decide +kernel
theorem subd6_3_311 : subd6_3 [-1, -2, -7] = true := by decide +kernel
theorem subd6_3_312 : subd6_3 [-1, -2, -6] = true := by decide +kernel
theorem subd6_3_313 : subd6_3 [-1, -2, -5] = true := by decide +kernel
theorem subd6_3_314 : subd6_3 [-1, -2, -4] = true := by decide +kernel
theorem subd6_3_315 : subd6_3 [-1, -2, -3] = true := by decide +kernel
theorem subd6_3_316 : subd6_3 [-1, -2, -2] = true := by decide +kernel
theorem subd6_3_317 : subd6_3 [-1, -2, -1] = true := by decide +kernel
theorem subd6_3_318 : subd6_3 [-1, -2, 0] = true := by decide +kernel
theorem subd6_3_319 : subd6_3 [-1, -2, 1] = true := by decide +kernel
theorem sbd6_3_9 : ∀ q ∈ blkd6_3_9, subd6_3 q = true := by
  unfold blkd6_3_9
  exact List.forall_mem_cons.2 ⟨subd6_3_288, List.forall_mem_cons.2 ⟨subd6_3_289, List.forall_mem_cons.2 ⟨subd6_3_290, List.forall_mem_cons.2 ⟨subd6_3_291, List.forall_mem_cons.2 ⟨subd6_3_292, List.forall_mem_cons.2 ⟨subd6_3_293, List.forall_mem_cons.2 ⟨subd6_3_294, List.forall_mem_cons.2 ⟨subd6_3_295, List.forall_mem_cons.2 ⟨subd6_3_296, List.forall_mem_cons.2 ⟨subd6_3_297, List.forall_mem_cons.2 ⟨subd6_3_298, List.forall_mem_cons.2 ⟨subd6_3_299, List.forall_mem_cons.2 ⟨subd6_3_300, List.forall_mem_cons.2 ⟨subd6_3_301, List.forall_mem_cons.2 ⟨subd6_3_302, List.forall_mem_cons.2 ⟨subd6_3_303, List.forall_mem_cons.2 ⟨subd6_3_304, List.forall_mem_cons.2 ⟨subd6_3_305, List.forall_mem_cons.2 ⟨subd6_3_306, List.forall_mem_cons.2 ⟨subd6_3_307, List.forall_mem_cons.2 ⟨subd6_3_308, List.forall_mem_cons.2 ⟨subd6_3_309, List.forall_mem_cons.2 ⟨subd6_3_310, List.forall_mem_cons.2 ⟨subd6_3_311, List.forall_mem_cons.2 ⟨subd6_3_312, List.forall_mem_cons.2 ⟨subd6_3_313, List.forall_mem_cons.2 ⟨subd6_3_314, List.forall_mem_cons.2 ⟨subd6_3_315, List.forall_mem_cons.2 ⟨subd6_3_316, List.forall_mem_cons.2 ⟨subd6_3_317, List.forall_mem_cons.2 ⟨subd6_3_318, List.forall_mem_cons.2 ⟨subd6_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_320 : subd6_3 [-1, -2, 2] = true := by decide +kernel
theorem subd6_3_321 : subd6_3 [-1, -2, 3] = true := by decide +kernel
theorem subd6_3_322 : subd6_3 [-1, -2, 4] = true := by decide +kernel
theorem subd6_3_323 : subd6_3 [-1, -2, 5] = true := by decide +kernel
theorem subd6_3_324 : subd6_3 [-1, -2, 6] = true := by decide +kernel
theorem subd6_3_325 : subd6_3 [-1, -2, 7] = true := by decide +kernel
theorem subd6_3_326 : subd6_3 [-1, -2, 8] = true := by decide +kernel
theorem subd6_3_327 : subd6_3 [-1, -1, -9] = true := by decide +kernel
theorem subd6_3_328 : subd6_3 [-1, -1, -8] = true := by decide +kernel
theorem subd6_3_329 : subd6_3 [-1, -1, -7] = true := by decide +kernel
theorem subd6_3_330 : subd6_3 [-1, -1, -6] = true := by decide +kernel
theorem subd6_3_331 : subd6_3 [-1, -1, -5] = true := by decide +kernel
theorem subd6_3_332 : subd6_3 [-1, -1, -4] = true := by decide +kernel
theorem subd6_3_333 : subd6_3 [-1, -1, -3] = true := by decide +kernel
theorem subd6_3_334 : subd6_3 [-1, -1, -2] = true := by decide +kernel
theorem subd6_3_335 : subd6_3 [-1, -1, -1] = true := by decide +kernel
theorem subd6_3_336 : subd6_3 [-1, -1, 0] = true := by decide +kernel
theorem subd6_3_337 : subd6_3 [-1, -1, 1] = true := by decide +kernel
theorem subd6_3_338 : subd6_3 [-1, -1, 2] = true := by decide +kernel
theorem subd6_3_339 : subd6_3 [-1, -1, 3] = true := by decide +kernel
theorem subd6_3_340 : subd6_3 [-1, -1, 4] = true := by decide +kernel
theorem subd6_3_341 : subd6_3 [-1, -1, 5] = true := by decide +kernel
theorem subd6_3_342 : subd6_3 [-1, -1, 6] = true := by decide +kernel
theorem subd6_3_343 : subd6_3 [-1, -1, 7] = true := by decide +kernel
theorem subd6_3_344 : subd6_3 [-1, -1, 8] = true := by decide +kernel
theorem subd6_3_345 : subd6_3 [-1, 0, -10] = true := by decide +kernel
theorem subd6_3_346 : subd6_3 [-1, 0, -9] = true := by decide +kernel
theorem subd6_3_347 : subd6_3 [-1, 0, -8] = true := by decide +kernel
theorem subd6_3_348 : subd6_3 [-1, 0, -7] = true := by decide +kernel
theorem subd6_3_349 : subd6_3 [-1, 0, -6] = true := by decide +kernel
theorem subd6_3_350 : subd6_3 [-1, 0, -5] = true := by decide +kernel
theorem subd6_3_351 : subd6_3 [-1, 0, -4] = true := by decide +kernel
theorem sbd6_3_10 : ∀ q ∈ blkd6_3_10, subd6_3 q = true := by
  unfold blkd6_3_10
  exact List.forall_mem_cons.2 ⟨subd6_3_320, List.forall_mem_cons.2 ⟨subd6_3_321, List.forall_mem_cons.2 ⟨subd6_3_322, List.forall_mem_cons.2 ⟨subd6_3_323, List.forall_mem_cons.2 ⟨subd6_3_324, List.forall_mem_cons.2 ⟨subd6_3_325, List.forall_mem_cons.2 ⟨subd6_3_326, List.forall_mem_cons.2 ⟨subd6_3_327, List.forall_mem_cons.2 ⟨subd6_3_328, List.forall_mem_cons.2 ⟨subd6_3_329, List.forall_mem_cons.2 ⟨subd6_3_330, List.forall_mem_cons.2 ⟨subd6_3_331, List.forall_mem_cons.2 ⟨subd6_3_332, List.forall_mem_cons.2 ⟨subd6_3_333, List.forall_mem_cons.2 ⟨subd6_3_334, List.forall_mem_cons.2 ⟨subd6_3_335, List.forall_mem_cons.2 ⟨subd6_3_336, List.forall_mem_cons.2 ⟨subd6_3_337, List.forall_mem_cons.2 ⟨subd6_3_338, List.forall_mem_cons.2 ⟨subd6_3_339, List.forall_mem_cons.2 ⟨subd6_3_340, List.forall_mem_cons.2 ⟨subd6_3_341, List.forall_mem_cons.2 ⟨subd6_3_342, List.forall_mem_cons.2 ⟨subd6_3_343, List.forall_mem_cons.2 ⟨subd6_3_344, List.forall_mem_cons.2 ⟨subd6_3_345, List.forall_mem_cons.2 ⟨subd6_3_346, List.forall_mem_cons.2 ⟨subd6_3_347, List.forall_mem_cons.2 ⟨subd6_3_348, List.forall_mem_cons.2 ⟨subd6_3_349, List.forall_mem_cons.2 ⟨subd6_3_350, List.forall_mem_cons.2 ⟨subd6_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
