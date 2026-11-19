import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_2_480 : subd10_2 [2, 0, -5] = true := by decide +kernel
theorem subd10_2_481 : subd10_2 [2, 0, -4] = true := by decide +kernel
theorem subd10_2_482 : subd10_2 [2, 0, -3] = true := by decide +kernel
theorem subd10_2_483 : subd10_2 [2, 0, -2] = true := by decide +kernel
theorem subd10_2_484 : subd10_2 [2, 0, -1] = true := by decide +kernel
theorem subd10_2_485 : subd10_2 [2, 0, 0] = true := by decide +kernel
theorem subd10_2_486 : subd10_2 [2, 0, 1] = true := by decide +kernel
theorem subd10_2_487 : subd10_2 [2, 0, 2] = true := by decide +kernel
theorem subd10_2_488 : subd10_2 [2, 0, 3] = true := by decide +kernel
theorem subd10_2_489 : subd10_2 [2, 0, 4] = true := by decide +kernel
theorem subd10_2_490 : subd10_2 [2, 0, 5] = true := by decide +kernel
theorem subd10_2_491 : subd10_2 [2, 0, 6] = true := by decide +kernel
theorem subd10_2_492 : subd10_2 [2, 0, 7] = true := by decide +kernel
theorem subd10_2_493 : subd10_2 [2, 0, 8] = true := by decide +kernel
theorem subd10_2_494 : subd10_2 [2, 0, 9] = true := by decide +kernel
theorem subd10_2_495 : subd10_2 [2, 0, 10] = true := by decide +kernel
theorem subd10_2_496 : subd10_2 [2, 1, -9] = true := by decide +kernel
theorem subd10_2_497 : subd10_2 [2, 1, -8] = true := by decide +kernel
theorem subd10_2_498 : subd10_2 [2, 1, -7] = true := by decide +kernel
theorem subd10_2_499 : subd10_2 [2, 1, -6] = true := by decide +kernel
theorem subd10_2_500 : subd10_2 [2, 1, -5] = true := by decide +kernel
theorem subd10_2_501 : subd10_2 [2, 1, -4] = true := by decide +kernel
theorem subd10_2_502 : subd10_2 [2, 1, -3] = true := by decide +kernel
theorem subd10_2_503 : subd10_2 [2, 1, -2] = true := by decide +kernel
theorem subd10_2_504 : subd10_2 [2, 1, -1] = true := by decide +kernel
theorem subd10_2_505 : subd10_2 [2, 1, 0] = true := by decide +kernel
theorem subd10_2_506 : subd10_2 [2, 1, 1] = true := by decide +kernel
theorem subd10_2_507 : subd10_2 [2, 1, 2] = true := by decide +kernel
theorem subd10_2_508 : subd10_2 [2, 1, 3] = true := by decide +kernel
theorem subd10_2_509 : subd10_2 [2, 1, 4] = true := by decide +kernel
theorem subd10_2_510 : subd10_2 [2, 1, 5] = true := by decide +kernel
theorem subd10_2_511 : subd10_2 [2, 1, 6] = true := by decide +kernel
theorem sbd10_2_15 : ∀ q ∈ blkd10_2_15, subd10_2 q = true := by
  unfold blkd10_2_15
  exact List.forall_mem_cons.2 ⟨subd10_2_480, List.forall_mem_cons.2 ⟨subd10_2_481, List.forall_mem_cons.2 ⟨subd10_2_482, List.forall_mem_cons.2 ⟨subd10_2_483, List.forall_mem_cons.2 ⟨subd10_2_484, List.forall_mem_cons.2 ⟨subd10_2_485, List.forall_mem_cons.2 ⟨subd10_2_486, List.forall_mem_cons.2 ⟨subd10_2_487, List.forall_mem_cons.2 ⟨subd10_2_488, List.forall_mem_cons.2 ⟨subd10_2_489, List.forall_mem_cons.2 ⟨subd10_2_490, List.forall_mem_cons.2 ⟨subd10_2_491, List.forall_mem_cons.2 ⟨subd10_2_492, List.forall_mem_cons.2 ⟨subd10_2_493, List.forall_mem_cons.2 ⟨subd10_2_494, List.forall_mem_cons.2 ⟨subd10_2_495, List.forall_mem_cons.2 ⟨subd10_2_496, List.forall_mem_cons.2 ⟨subd10_2_497, List.forall_mem_cons.2 ⟨subd10_2_498, List.forall_mem_cons.2 ⟨subd10_2_499, List.forall_mem_cons.2 ⟨subd10_2_500, List.forall_mem_cons.2 ⟨subd10_2_501, List.forall_mem_cons.2 ⟨subd10_2_502, List.forall_mem_cons.2 ⟨subd10_2_503, List.forall_mem_cons.2 ⟨subd10_2_504, List.forall_mem_cons.2 ⟨subd10_2_505, List.forall_mem_cons.2 ⟨subd10_2_506, List.forall_mem_cons.2 ⟨subd10_2_507, List.forall_mem_cons.2 ⟨subd10_2_508, List.forall_mem_cons.2 ⟨subd10_2_509, List.forall_mem_cons.2 ⟨subd10_2_510, List.forall_mem_cons.2 ⟨subd10_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_512 : subd10_2 [2, 1, 7] = true := by decide +kernel
theorem subd10_2_513 : subd10_2 [2, 1, 8] = true := by decide +kernel
theorem subd10_2_514 : subd10_2 [2, 1, 9] = true := by decide +kernel
theorem subd10_2_515 : subd10_2 [2, 2, -6] = true := by decide +kernel
theorem subd10_2_516 : subd10_2 [2, 2, -5] = true := by decide +kernel
theorem subd10_2_517 : subd10_2 [2, 2, -4] = true := by decide +kernel
theorem subd10_2_518 : subd10_2 [2, 2, -3] = true := by decide +kernel
theorem subd10_2_519 : subd10_2 [2, 2, -2] = true := by decide +kernel
theorem subd10_2_520 : subd10_2 [2, 2, -1] = true := by decide +kernel
theorem subd10_2_521 : subd10_2 [2, 2, 0] = true := by decide +kernel
theorem subd10_2_522 : subd10_2 [2, 2, 1] = true := by decide +kernel
theorem subd10_2_523 : subd10_2 [2, 2, 2] = true := by decide +kernel
theorem subd10_2_524 : subd10_2 [2, 2, 3] = true := by decide +kernel
theorem subd10_2_525 : subd10_2 [2, 2, 4] = true := by decide +kernel
theorem subd10_2_526 : subd10_2 [2, 2, 5] = true := by decide +kernel
theorem subd10_2_527 : subd10_2 [2, 2, 6] = true := by decide +kernel
theorem subd10_2_528 : subd10_2 [2, 2, 7] = true := by decide +kernel
theorem subd10_2_529 : subd10_2 [3, -2] = true := by decide +kernel
theorem subd10_2_530 : subd10_2 [3, -1] = true := by decide +kernel
theorem subd10_2_531 : subd10_2 [3, 0] = true := by decide +kernel
theorem subd10_2_532 : subd10_2 [3, 1] = true := by decide +kernel
theorem sbd10_2_16 : ∀ q ∈ blkd10_2_16, subd10_2 q = true := by
  unfold blkd10_2_16
  exact List.forall_mem_cons.2 ⟨subd10_2_512, List.forall_mem_cons.2 ⟨subd10_2_513, List.forall_mem_cons.2 ⟨subd10_2_514, List.forall_mem_cons.2 ⟨subd10_2_515, List.forall_mem_cons.2 ⟨subd10_2_516, List.forall_mem_cons.2 ⟨subd10_2_517, List.forall_mem_cons.2 ⟨subd10_2_518, List.forall_mem_cons.2 ⟨subd10_2_519, List.forall_mem_cons.2 ⟨subd10_2_520, List.forall_mem_cons.2 ⟨subd10_2_521, List.forall_mem_cons.2 ⟨subd10_2_522, List.forall_mem_cons.2 ⟨subd10_2_523, List.forall_mem_cons.2 ⟨subd10_2_524, List.forall_mem_cons.2 ⟨subd10_2_525, List.forall_mem_cons.2 ⟨subd10_2_526, List.forall_mem_cons.2 ⟨subd10_2_527, List.forall_mem_cons.2 ⟨subd10_2_528, List.forall_mem_cons.2 ⟨subd10_2_529, List.forall_mem_cons.2 ⟨subd10_2_530, List.forall_mem_cons.2 ⟨subd10_2_531, List.forall_mem_cons.2 ⟨subd10_2_532, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-5, -3] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-5, -2] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-5, -1] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-5, 0] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [-5, 1] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [-5, 2] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [-5, 3] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [-4, -5] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [-4, -4] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [-4, -3] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [-4, -2] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [-4, -1] = true := by decide +kernel
theorem subd10_3_12 : subd10_3 [-4, 0] = true := by decide +kernel
theorem subd10_3_13 : subd10_3 [-4, 1] = true := by decide +kernel
theorem subd10_3_14 : subd10_3 [-4, 2] = true := by decide +kernel
theorem subd10_3_15 : subd10_3 [-4, 3] = true := by decide +kernel
theorem subd10_3_16 : subd10_3 [-4, 4] = true := by decide +kernel
theorem subd10_3_17 : subd10_3 [-3, -5] = true := by decide +kernel
theorem subd10_3_18 : subd10_3 [-3, -4] = true := by decide +kernel
theorem subd10_3_19 : subd10_3 [-3, -3] = true := by decide +kernel
theorem subd10_3_20 : subd10_3 [-3, -2] = true := by decide +kernel
theorem subd10_3_21 : subd10_3 [-3, -1] = true := by decide +kernel
theorem subd10_3_22 : subd10_3 [-3, 0] = true := by decide +kernel
theorem subd10_3_23 : subd10_3 [-3, 1] = true := by decide +kernel
theorem subd10_3_24 : subd10_3 [-3, 2] = true := by decide +kernel
theorem subd10_3_25 : subd10_3 [-3, 3] = true := by decide +kernel
theorem subd10_3_26 : subd10_3 [-3, 4] = true := by decide +kernel
theorem subd10_3_27 : subd10_3 [-3, 5] = true := by decide +kernel
theorem subd10_3_28 : subd10_3 [-2, -6] = true := by decide +kernel
theorem subd10_3_29 : subd10_3 [-2, -5] = true := by decide +kernel
theorem subd10_3_30 : subd10_3 [-2, -4] = true := by decide +kernel
theorem subd10_3_31 : subd10_3 [-2, -3] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_cons.2 ⟨subd10_3_12, List.forall_mem_cons.2 ⟨subd10_3_13, List.forall_mem_cons.2 ⟨subd10_3_14, List.forall_mem_cons.2 ⟨subd10_3_15, List.forall_mem_cons.2 ⟨subd10_3_16, List.forall_mem_cons.2 ⟨subd10_3_17, List.forall_mem_cons.2 ⟨subd10_3_18, List.forall_mem_cons.2 ⟨subd10_3_19, List.forall_mem_cons.2 ⟨subd10_3_20, List.forall_mem_cons.2 ⟨subd10_3_21, List.forall_mem_cons.2 ⟨subd10_3_22, List.forall_mem_cons.2 ⟨subd10_3_23, List.forall_mem_cons.2 ⟨subd10_3_24, List.forall_mem_cons.2 ⟨subd10_3_25, List.forall_mem_cons.2 ⟨subd10_3_26, List.forall_mem_cons.2 ⟨subd10_3_27, List.forall_mem_cons.2 ⟨subd10_3_28, List.forall_mem_cons.2 ⟨subd10_3_29, List.forall_mem_cons.2 ⟨subd10_3_30, List.forall_mem_cons.2 ⟨subd10_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_32 : subd10_3 [-2, -2] = true := by decide +kernel
theorem subd10_3_33 : subd10_3 [-2, -1, -7] = true := by decide +kernel
theorem subd10_3_34 : subd10_3 [-2, -1, -6] = true := by decide +kernel
theorem subd10_3_35 : subd10_3 [-2, -1, -5] = true := by decide +kernel
theorem subd10_3_36 : subd10_3 [-2, -1, -4] = true := by decide +kernel
theorem subd10_3_37 : subd10_3 [-2, -1, -3] = true := by decide +kernel
theorem subd10_3_38 : subd10_3 [-2, -1, -2] = true := by decide +kernel
theorem subd10_3_39 : subd10_3 [-2, -1, -1] = true := by decide +kernel
theorem subd10_3_40 : subd10_3 [-2, -1, 0] = true := by decide +kernel
theorem subd10_3_41 : subd10_3 [-2, -1, 1] = true := by decide +kernel
theorem subd10_3_42 : subd10_3 [-2, -1, 2] = true := by decide +kernel
theorem subd10_3_43 : subd10_3 [-2, -1, 3] = true := by decide +kernel
theorem subd10_3_44 : subd10_3 [-2, -1, 4] = true := by decide +kernel
theorem subd10_3_45 : subd10_3 [-2, -1, 5] = true := by decide +kernel
theorem subd10_3_46 : subd10_3 [-2, -1, 6] = true := by decide +kernel
theorem subd10_3_47 : subd10_3 [-2, 0, -7] = true := by decide +kernel
theorem subd10_3_48 : subd10_3 [-2, 0, -6] = true := by decide +kernel
theorem subd10_3_49 : subd10_3 [-2, 0, -5] = true := by decide +kernel
theorem subd10_3_50 : subd10_3 [-2, 0, -4] = true := by decide +kernel
theorem subd10_3_51 : subd10_3 [-2, 0, -3] = true := by decide +kernel
theorem subd10_3_52 : subd10_3 [-2, 0, -2] = true := by decide +kernel
theorem subd10_3_53 : subd10_3 [-2, 0, -1] = true := by decide +kernel
theorem subd10_3_54 : subd10_3 [-2, 0, 0] = true := by decide +kernel
theorem subd10_3_55 : subd10_3 [-2, 0, 1] = true := by decide +kernel
theorem subd10_3_56 : subd10_3 [-2, 0, 2] = true := by decide +kernel
theorem subd10_3_57 : subd10_3 [-2, 0, 3] = true := by decide +kernel
theorem subd10_3_58 : subd10_3 [-2, 0, 4] = true := by decide +kernel
theorem subd10_3_59 : subd10_3 [-2, 0, 5] = true := by decide +kernel
theorem subd10_3_60 : subd10_3 [-2, 0, 6] = true := by decide +kernel
theorem subd10_3_61 : subd10_3 [-2, 1, -7] = true := by decide +kernel
theorem subd10_3_62 : subd10_3 [-2, 1, -6] = true := by decide +kernel
theorem subd10_3_63 : subd10_3 [-2, 1, -5] = true := by decide +kernel
theorem sbd10_3_1 : ∀ q ∈ blkd10_3_1, subd10_3 q = true := by
  unfold blkd10_3_1
  exact List.forall_mem_cons.2 ⟨subd10_3_32, List.forall_mem_cons.2 ⟨subd10_3_33, List.forall_mem_cons.2 ⟨subd10_3_34, List.forall_mem_cons.2 ⟨subd10_3_35, List.forall_mem_cons.2 ⟨subd10_3_36, List.forall_mem_cons.2 ⟨subd10_3_37, List.forall_mem_cons.2 ⟨subd10_3_38, List.forall_mem_cons.2 ⟨subd10_3_39, List.forall_mem_cons.2 ⟨subd10_3_40, List.forall_mem_cons.2 ⟨subd10_3_41, List.forall_mem_cons.2 ⟨subd10_3_42, List.forall_mem_cons.2 ⟨subd10_3_43, List.forall_mem_cons.2 ⟨subd10_3_44, List.forall_mem_cons.2 ⟨subd10_3_45, List.forall_mem_cons.2 ⟨subd10_3_46, List.forall_mem_cons.2 ⟨subd10_3_47, List.forall_mem_cons.2 ⟨subd10_3_48, List.forall_mem_cons.2 ⟨subd10_3_49, List.forall_mem_cons.2 ⟨subd10_3_50, List.forall_mem_cons.2 ⟨subd10_3_51, List.forall_mem_cons.2 ⟨subd10_3_52, List.forall_mem_cons.2 ⟨subd10_3_53, List.forall_mem_cons.2 ⟨subd10_3_54, List.forall_mem_cons.2 ⟨subd10_3_55, List.forall_mem_cons.2 ⟨subd10_3_56, List.forall_mem_cons.2 ⟨subd10_3_57, List.forall_mem_cons.2 ⟨subd10_3_58, List.forall_mem_cons.2 ⟨subd10_3_59, List.forall_mem_cons.2 ⟨subd10_3_60, List.forall_mem_cons.2 ⟨subd10_3_61, List.forall_mem_cons.2 ⟨subd10_3_62, List.forall_mem_cons.2 ⟨subd10_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_64 : subd10_3 [-2, 1, -4] = true := by decide +kernel
theorem subd10_3_65 : subd10_3 [-2, 1, -3] = true := by decide +kernel
theorem subd10_3_66 : subd10_3 [-2, 1, -2] = true := by decide +kernel
theorem subd10_3_67 : subd10_3 [-2, 1, -1] = true := by decide +kernel
theorem subd10_3_68 : subd10_3 [-2, 1, 0] = true := by decide +kernel
theorem subd10_3_69 : subd10_3 [-2, 1, 1] = true := by decide +kernel
theorem subd10_3_70 : subd10_3 [-2, 1, 2] = true := by decide +kernel
theorem subd10_3_71 : subd10_3 [-2, 1, 3] = true := by decide +kernel
theorem subd10_3_72 : subd10_3 [-2, 1, 4] = true := by decide +kernel
theorem subd10_3_73 : subd10_3 [-2, 1, 5] = true := by decide +kernel
theorem subd10_3_74 : subd10_3 [-2, 1, 6] = true := by decide +kernel
theorem subd10_3_75 : subd10_3 [-2, 2, -7] = true := by decide +kernel
theorem subd10_3_76 : subd10_3 [-2, 2, -6] = true := by decide +kernel
theorem subd10_3_77 : subd10_3 [-2, 2, -5] = true := by decide +kernel
theorem subd10_3_78 : subd10_3 [-2, 2, -4] = true := by decide +kernel
theorem subd10_3_79 : subd10_3 [-2, 2, -3] = true := by decide +kernel
theorem subd10_3_80 : subd10_3 [-2, 2, -2] = true := by decide +kernel
theorem subd10_3_81 : subd10_3 [-2, 2, -1] = true := by decide +kernel
theorem subd10_3_82 : subd10_3 [-2, 2, 0] = true := by decide +kernel
theorem subd10_3_83 : subd10_3 [-2, 2, 1] = true := by decide +kernel
theorem subd10_3_84 : subd10_3 [-2, 2, 2] = true := by decide +kernel
theorem subd10_3_85 : subd10_3 [-2, 2, 3] = true := by decide +kernel
theorem subd10_3_86 : subd10_3 [-2, 2, 4] = true := by decide +kernel
theorem subd10_3_87 : subd10_3 [-2, 2, 5] = true := by decide +kernel
theorem subd10_3_88 : subd10_3 [-2, 3] = true := by decide +kernel
theorem subd10_3_89 : subd10_3 [-2, 4] = true := by decide +kernel
theorem subd10_3_90 : subd10_3 [-2, 5] = true := by decide +kernel
theorem subd10_3_91 : subd10_3 [-1, -6] = true := by decide +kernel
theorem subd10_3_92 : subd10_3 [-1, -5] = true := by decide +kernel
theorem subd10_3_93 : subd10_3 [-1, -4] = true := by decide +kernel
theorem subd10_3_94 : subd10_3 [-1, -3] = true := by decide +kernel
theorem subd10_3_95 : subd10_3 [-1, -2, -7] = true := by decide +kernel
theorem sbd10_3_2 : ∀ q ∈ blkd10_3_2, subd10_3 q = true := by
  unfold blkd10_3_2
  exact List.forall_mem_cons.2 ⟨subd10_3_64, List.forall_mem_cons.2 ⟨subd10_3_65, List.forall_mem_cons.2 ⟨subd10_3_66, List.forall_mem_cons.2 ⟨subd10_3_67, List.forall_mem_cons.2 ⟨subd10_3_68, List.forall_mem_cons.2 ⟨subd10_3_69, List.forall_mem_cons.2 ⟨subd10_3_70, List.forall_mem_cons.2 ⟨subd10_3_71, List.forall_mem_cons.2 ⟨subd10_3_72, List.forall_mem_cons.2 ⟨subd10_3_73, List.forall_mem_cons.2 ⟨subd10_3_74, List.forall_mem_cons.2 ⟨subd10_3_75, List.forall_mem_cons.2 ⟨subd10_3_76, List.forall_mem_cons.2 ⟨subd10_3_77, List.forall_mem_cons.2 ⟨subd10_3_78, List.forall_mem_cons.2 ⟨subd10_3_79, List.forall_mem_cons.2 ⟨subd10_3_80, List.forall_mem_cons.2 ⟨subd10_3_81, List.forall_mem_cons.2 ⟨subd10_3_82, List.forall_mem_cons.2 ⟨subd10_3_83, List.forall_mem_cons.2 ⟨subd10_3_84, List.forall_mem_cons.2 ⟨subd10_3_85, List.forall_mem_cons.2 ⟨subd10_3_86, List.forall_mem_cons.2 ⟨subd10_3_87, List.forall_mem_cons.2 ⟨subd10_3_88, List.forall_mem_cons.2 ⟨subd10_3_89, List.forall_mem_cons.2 ⟨subd10_3_90, List.forall_mem_cons.2 ⟨subd10_3_91, List.forall_mem_cons.2 ⟨subd10_3_92, List.forall_mem_cons.2 ⟨subd10_3_93, List.forall_mem_cons.2 ⟨subd10_3_94, List.forall_mem_cons.2 ⟨subd10_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_96 : subd10_3 [-1, -2, -6] = true := by decide +kernel
theorem subd10_3_97 : subd10_3 [-1, -2, -5] = true := by decide +kernel
theorem subd10_3_98 : subd10_3 [-1, -2, -4] = true := by decide +kernel
theorem subd10_3_99 : subd10_3 [-1, -2, -3] = true := by decide +kernel
theorem subd10_3_100 : subd10_3 [-1, -2, -2] = true := by decide +kernel
theorem subd10_3_101 : subd10_3 [-1, -2, -1] = true := by decide +kernel
theorem subd10_3_102 : subd10_3 [-1, -2, 0] = true := by decide +kernel
theorem subd10_3_103 : subd10_3 [-1, -2, 1] = true := by decide +kernel
theorem subd10_3_104 : subd10_3 [-1, -2, 2] = true := by decide +kernel
theorem subd10_3_105 : subd10_3 [-1, -2, 3] = true := by decide +kernel
theorem subd10_3_106 : subd10_3 [-1, -2, 4] = true := by decide +kernel
theorem subd10_3_107 : subd10_3 [-1, -2, 5] = true := by decide +kernel
theorem subd10_3_108 : subd10_3 [-1, -2, 6] = true := by decide +kernel
theorem subd10_3_109 : subd10_3 [-1, -1, -7] = true := by decide +kernel
theorem subd10_3_110 : subd10_3 [-1, -1, -6] = true := by decide +kernel
theorem subd10_3_111 : subd10_3 [-1, -1, -5] = true := by decide +kernel
theorem subd10_3_112 : subd10_3 [-1, -1, -4] = true := by decide +kernel
theorem subd10_3_113 : subd10_3 [-1, -1, -3] = true := by decide +kernel
theorem subd10_3_114 : subd10_3 [-1, -1, -2] = true := by decide +kernel
theorem subd10_3_115 : subd10_3 [-1, -1, -1] = true := by decide +kernel
theorem subd10_3_116 : subd10_3 [-1, -1, 0] = true := by decide +kernel
theorem subd10_3_117 : subd10_3 [-1, -1, 1] = true := by decide +kernel
theorem subd10_3_118 : subd10_3 [-1, -1, 2] = true := by decide +kernel
theorem subd10_3_119 : subd10_3 [-1, -1, 3] = true := by decide +kernel
theorem subd10_3_120 : subd10_3 [-1, -1, 4] = true := by decide +kernel
theorem subd10_3_121 : subd10_3 [-1, -1, 5] = true := by decide +kernel
theorem subd10_3_122 : subd10_3 [-1, -1, 6] = true := by decide +kernel
theorem subd10_3_123 : subd10_3 [-1, 0, -7] = true := by decide +kernel
theorem subd10_3_124 : subd10_3 [-1, 0, -6] = true := by decide +kernel
theorem subd10_3_125 : subd10_3 [-1, 0, -5] = true := by decide +kernel
theorem subd10_3_126 : subd10_3 [-1, 0, -4] = true := by decide +kernel
theorem subd10_3_127 : subd10_3 [-1, 0, -3] = true := by decide +kernel
theorem sbd10_3_3 : ∀ q ∈ blkd10_3_3, subd10_3 q = true := by
  unfold blkd10_3_3
  exact List.forall_mem_cons.2 ⟨subd10_3_96, List.forall_mem_cons.2 ⟨subd10_3_97, List.forall_mem_cons.2 ⟨subd10_3_98, List.forall_mem_cons.2 ⟨subd10_3_99, List.forall_mem_cons.2 ⟨subd10_3_100, List.forall_mem_cons.2 ⟨subd10_3_101, List.forall_mem_cons.2 ⟨subd10_3_102, List.forall_mem_cons.2 ⟨subd10_3_103, List.forall_mem_cons.2 ⟨subd10_3_104, List.forall_mem_cons.2 ⟨subd10_3_105, List.forall_mem_cons.2 ⟨subd10_3_106, List.forall_mem_cons.2 ⟨subd10_3_107, List.forall_mem_cons.2 ⟨subd10_3_108, List.forall_mem_cons.2 ⟨subd10_3_109, List.forall_mem_cons.2 ⟨subd10_3_110, List.forall_mem_cons.2 ⟨subd10_3_111, List.forall_mem_cons.2 ⟨subd10_3_112, List.forall_mem_cons.2 ⟨subd10_3_113, List.forall_mem_cons.2 ⟨subd10_3_114, List.forall_mem_cons.2 ⟨subd10_3_115, List.forall_mem_cons.2 ⟨subd10_3_116, List.forall_mem_cons.2 ⟨subd10_3_117, List.forall_mem_cons.2 ⟨subd10_3_118, List.forall_mem_cons.2 ⟨subd10_3_119, List.forall_mem_cons.2 ⟨subd10_3_120, List.forall_mem_cons.2 ⟨subd10_3_121, List.forall_mem_cons.2 ⟨subd10_3_122, List.forall_mem_cons.2 ⟨subd10_3_123, List.forall_mem_cons.2 ⟨subd10_3_124, List.forall_mem_cons.2 ⟨subd10_3_125, List.forall_mem_cons.2 ⟨subd10_3_126, List.forall_mem_cons.2 ⟨subd10_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_128 : subd10_3 [-1, 0, -2] = true := by decide +kernel
theorem subd10_3_129 : subd10_3 [-1, 0, -1] = true := by decide +kernel
theorem subd10_3_130 : subd10_3 [-1, 0, 0] = true := by decide +kernel
theorem subd10_3_131 : subd10_3 [-1, 0, 1] = true := by decide +kernel
theorem subd10_3_132 : subd10_3 [-1, 0, 2] = true := by decide +kernel
theorem subd10_3_133 : subd10_3 [-1, 0, 3] = true := by decide +kernel
theorem subd10_3_134 : subd10_3 [-1, 0, 4] = true := by decide +kernel
theorem subd10_3_135 : subd10_3 [-1, 0, 5] = true := by decide +kernel
theorem subd10_3_136 : subd10_3 [-1, 0, 6] = true := by decide +kernel
theorem subd10_3_137 : subd10_3 [-1, 1, -8] = true := by decide +kernel
theorem subd10_3_138 : subd10_3 [-1, 1, -7] = true := by decide +kernel
theorem subd10_3_139 : subd10_3 [-1, 1, -6] = true := by decide +kernel
theorem subd10_3_140 : subd10_3 [-1, 1, -5] = true := by decide +kernel
theorem subd10_3_141 : subd10_3 [-1, 1, -4] = true := by decide +kernel
theorem subd10_3_142 : subd10_3 [-1, 1, -3] = true := by decide +kernel
theorem subd10_3_143 : subd10_3 [-1, 1, -2] = true := by decide +kernel
theorem subd10_3_144 : subd10_3 [-1, 1, -1] = true := by decide +kernel
theorem subd10_3_145 : subd10_3 [-1, 1, 0] = true := by decide +kernel
theorem subd10_3_146 : subd10_3 [-1, 1, 1] = true := by decide +kernel
theorem subd10_3_147 : subd10_3 [-1, 1, 2] = true := by decide +kernel
theorem subd10_3_148 : subd10_3 [-1, 1, 3] = true := by decide +kernel
theorem subd10_3_149 : subd10_3 [-1, 1, 4] = true := by decide +kernel
theorem subd10_3_150 : subd10_3 [-1, 1, 5] = true := by decide +kernel
theorem subd10_3_151 : subd10_3 [-1, 1, 6] = true := by decide +kernel
theorem subd10_3_152 : subd10_3 [-1, 2, -8] = true := by decide +kernel
theorem subd10_3_153 : subd10_3 [-1, 2, -7] = true := by decide +kernel
theorem subd10_3_154 : subd10_3 [-1, 2, -6] = true := by decide +kernel
theorem subd10_3_155 : subd10_3 [-1, 2, -5] = true := by decide +kernel
theorem subd10_3_156 : subd10_3 [-1, 2, -4] = true := by decide +kernel
theorem subd10_3_157 : subd10_3 [-1, 2, -3] = true := by decide +kernel
theorem subd10_3_158 : subd10_3 [-1, 2, -2] = true := by decide +kernel
theorem subd10_3_159 : subd10_3 [-1, 2, -1] = true := by decide +kernel
theorem sbd10_3_4 : ∀ q ∈ blkd10_3_4, subd10_3 q = true := by
  unfold blkd10_3_4
  exact List.forall_mem_cons.2 ⟨subd10_3_128, List.forall_mem_cons.2 ⟨subd10_3_129, List.forall_mem_cons.2 ⟨subd10_3_130, List.forall_mem_cons.2 ⟨subd10_3_131, List.forall_mem_cons.2 ⟨subd10_3_132, List.forall_mem_cons.2 ⟨subd10_3_133, List.forall_mem_cons.2 ⟨subd10_3_134, List.forall_mem_cons.2 ⟨subd10_3_135, List.forall_mem_cons.2 ⟨subd10_3_136, List.forall_mem_cons.2 ⟨subd10_3_137, List.forall_mem_cons.2 ⟨subd10_3_138, List.forall_mem_cons.2 ⟨subd10_3_139, List.forall_mem_cons.2 ⟨subd10_3_140, List.forall_mem_cons.2 ⟨subd10_3_141, List.forall_mem_cons.2 ⟨subd10_3_142, List.forall_mem_cons.2 ⟨subd10_3_143, List.forall_mem_cons.2 ⟨subd10_3_144, List.forall_mem_cons.2 ⟨subd10_3_145, List.forall_mem_cons.2 ⟨subd10_3_146, List.forall_mem_cons.2 ⟨subd10_3_147, List.forall_mem_cons.2 ⟨subd10_3_148, List.forall_mem_cons.2 ⟨subd10_3_149, List.forall_mem_cons.2 ⟨subd10_3_150, List.forall_mem_cons.2 ⟨subd10_3_151, List.forall_mem_cons.2 ⟨subd10_3_152, List.forall_mem_cons.2 ⟨subd10_3_153, List.forall_mem_cons.2 ⟨subd10_3_154, List.forall_mem_cons.2 ⟨subd10_3_155, List.forall_mem_cons.2 ⟨subd10_3_156, List.forall_mem_cons.2 ⟨subd10_3_157, List.forall_mem_cons.2 ⟨subd10_3_158, List.forall_mem_cons.2 ⟨subd10_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_160 : subd10_3 [-1, 2, 0] = true := by decide +kernel
theorem subd10_3_161 : subd10_3 [-1, 2, 1] = true := by decide +kernel
theorem subd10_3_162 : subd10_3 [-1, 2, 2] = true := by decide +kernel
theorem subd10_3_163 : subd10_3 [-1, 2, 3] = true := by decide +kernel
theorem subd10_3_164 : subd10_3 [-1, 2, 4] = true := by decide +kernel
theorem subd10_3_165 : subd10_3 [-1, 2, 5] = true := by decide +kernel
theorem subd10_3_166 : subd10_3 [-1, 3] = true := by decide +kernel
theorem subd10_3_167 : subd10_3 [-1, 4] = true := by decide +kernel
theorem subd10_3_168 : subd10_3 [-1, 5] = true := by decide +kernel
theorem subd10_3_169 : subd10_3 [-1, 6] = true := by decide +kernel
theorem subd10_3_170 : subd10_3 [0, -7] = true := by decide +kernel
theorem subd10_3_171 : subd10_3 [0, -6] = true := by decide +kernel
theorem subd10_3_172 : subd10_3 [0, -5] = true := by decide +kernel
theorem subd10_3_173 : subd10_3 [0, -4] = true := by decide +kernel
theorem subd10_3_174 : subd10_3 [0, -3] = true := by decide +kernel
theorem subd10_3_175 : subd10_3 [0, -2, -7] = true := by decide +kernel
theorem subd10_3_176 : subd10_3 [0, -2, -6] = true := by decide +kernel
theorem subd10_3_177 : subd10_3 [0, -2, -5] = true := by decide +kernel
theorem subd10_3_178 : subd10_3 [0, -2, -4] = true := by decide +kernel
theorem subd10_3_179 : subd10_3 [0, -2, -3] = true := by decide +kernel
theorem subd10_3_180 : subd10_3 [0, -2, -2] = true := by decide +kernel
theorem subd10_3_181 : subd10_3 [0, -2, -1] = true := by decide +kernel
theorem subd10_3_182 : subd10_3 [0, -2, 0] = true := by decide +kernel
theorem subd10_3_183 : subd10_3 [0, -2, 1] = true := by decide +kernel
theorem subd10_3_184 : subd10_3 [0, -2, 2] = true := by decide +kernel
theorem subd10_3_185 : subd10_3 [0, -2, 3] = true := by decide +kernel
theorem subd10_3_186 : subd10_3 [0, -2, 4] = true := by decide +kernel
theorem subd10_3_187 : subd10_3 [0, -2, 5] = true := by decide +kernel
theorem subd10_3_188 : subd10_3 [0, -2, 6] = true := by decide +kernel
theorem subd10_3_189 : subd10_3 [0, -2, 7] = true := by decide +kernel
theorem subd10_3_190 : subd10_3 [0, -1, -7] = true := by decide +kernel
theorem subd10_3_191 : subd10_3 [0, -1, -6] = true := by decide +kernel
theorem sbd10_3_5 : ∀ q ∈ blkd10_3_5, subd10_3 q = true := by
  unfold blkd10_3_5
  exact List.forall_mem_cons.2 ⟨subd10_3_160, List.forall_mem_cons.2 ⟨subd10_3_161, List.forall_mem_cons.2 ⟨subd10_3_162, List.forall_mem_cons.2 ⟨subd10_3_163, List.forall_mem_cons.2 ⟨subd10_3_164, List.forall_mem_cons.2 ⟨subd10_3_165, List.forall_mem_cons.2 ⟨subd10_3_166, List.forall_mem_cons.2 ⟨subd10_3_167, List.forall_mem_cons.2 ⟨subd10_3_168, List.forall_mem_cons.2 ⟨subd10_3_169, List.forall_mem_cons.2 ⟨subd10_3_170, List.forall_mem_cons.2 ⟨subd10_3_171, List.forall_mem_cons.2 ⟨subd10_3_172, List.forall_mem_cons.2 ⟨subd10_3_173, List.forall_mem_cons.2 ⟨subd10_3_174, List.forall_mem_cons.2 ⟨subd10_3_175, List.forall_mem_cons.2 ⟨subd10_3_176, List.forall_mem_cons.2 ⟨subd10_3_177, List.forall_mem_cons.2 ⟨subd10_3_178, List.forall_mem_cons.2 ⟨subd10_3_179, List.forall_mem_cons.2 ⟨subd10_3_180, List.forall_mem_cons.2 ⟨subd10_3_181, List.forall_mem_cons.2 ⟨subd10_3_182, List.forall_mem_cons.2 ⟨subd10_3_183, List.forall_mem_cons.2 ⟨subd10_3_184, List.forall_mem_cons.2 ⟨subd10_3_185, List.forall_mem_cons.2 ⟨subd10_3_186, List.forall_mem_cons.2 ⟨subd10_3_187, List.forall_mem_cons.2 ⟨subd10_3_188, List.forall_mem_cons.2 ⟨subd10_3_189, List.forall_mem_cons.2 ⟨subd10_3_190, List.forall_mem_cons.2 ⟨subd10_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_192 : subd10_3 [0, -1, -5] = true := by decide +kernel
theorem subd10_3_193 : subd10_3 [0, -1, -4] = true := by decide +kernel
theorem subd10_3_194 : subd10_3 [0, -1, -3] = true := by decide +kernel
theorem subd10_3_195 : subd10_3 [0, -1, -2] = true := by decide +kernel
theorem subd10_3_196 : subd10_3 [0, -1, -1] = true := by decide +kernel
theorem subd10_3_197 : subd10_3 [0, -1, 0] = true := by decide +kernel
theorem subd10_3_198 : subd10_3 [0, -1, 1] = true := by decide +kernel
theorem subd10_3_199 : subd10_3 [0, -1, 2] = true := by decide +kernel
theorem subd10_3_200 : subd10_3 [0, -1, 3] = true := by decide +kernel
theorem subd10_3_201 : subd10_3 [0, -1, 4] = true := by decide +kernel
theorem subd10_3_202 : subd10_3 [0, -1, 5] = true := by decide +kernel
theorem subd10_3_203 : subd10_3 [0, -1, 6] = true := by decide +kernel
theorem subd10_3_204 : subd10_3 [0, -1, 7] = true := by decide +kernel
theorem subd10_3_205 : subd10_3 [0, 0, -7] = true := by decide +kernel
theorem subd10_3_206 : subd10_3 [0, 0, -6] = true := by decide +kernel
theorem subd10_3_207 : subd10_3 [0, 0, -5] = true := by decide +kernel
theorem subd10_3_208 : subd10_3 [0, 0, -4] = true := by decide +kernel
theorem subd10_3_209 : subd10_3 [0, 0, -3] = true := by decide +kernel
theorem subd10_3_210 : subd10_3 [0, 0, -2] = true := by decide +kernel
theorem subd10_3_211 : subd10_3 [0, 0, -1] = true := by decide +kernel
theorem subd10_3_212 : subd10_3 [0, 0, 0] = true := by decide +kernel
theorem subd10_3_213 : subd10_3 [0, 0, 1] = true := by decide +kernel
theorem subd10_3_214 : subd10_3 [0, 0, 2] = true := by decide +kernel
theorem subd10_3_215 : subd10_3 [0, 0, 3] = true := by decide +kernel
theorem subd10_3_216 : subd10_3 [0, 0, 4] = true := by decide +kernel
theorem subd10_3_217 : subd10_3 [0, 0, 5] = true := by decide +kernel
theorem subd10_3_218 : subd10_3 [0, 0, 6] = true := by decide +kernel
theorem subd10_3_219 : subd10_3 [0, 1, -8] = true := by decide +kernel
theorem subd10_3_220 : subd10_3 [0, 1, -7] = true := by decide +kernel
theorem subd10_3_221 : subd10_3 [0, 1, -6] = true := by decide +kernel
theorem subd10_3_222 : subd10_3 [0, 1, -5] = true := by decide +kernel
theorem subd10_3_223 : subd10_3 [0, 1, -4] = true := by decide +kernel
theorem sbd10_3_6 : ∀ q ∈ blkd10_3_6, subd10_3 q = true := by
  unfold blkd10_3_6
  exact List.forall_mem_cons.2 ⟨subd10_3_192, List.forall_mem_cons.2 ⟨subd10_3_193, List.forall_mem_cons.2 ⟨subd10_3_194, List.forall_mem_cons.2 ⟨subd10_3_195, List.forall_mem_cons.2 ⟨subd10_3_196, List.forall_mem_cons.2 ⟨subd10_3_197, List.forall_mem_cons.2 ⟨subd10_3_198, List.forall_mem_cons.2 ⟨subd10_3_199, List.forall_mem_cons.2 ⟨subd10_3_200, List.forall_mem_cons.2 ⟨subd10_3_201, List.forall_mem_cons.2 ⟨subd10_3_202, List.forall_mem_cons.2 ⟨subd10_3_203, List.forall_mem_cons.2 ⟨subd10_3_204, List.forall_mem_cons.2 ⟨subd10_3_205, List.forall_mem_cons.2 ⟨subd10_3_206, List.forall_mem_cons.2 ⟨subd10_3_207, List.forall_mem_cons.2 ⟨subd10_3_208, List.forall_mem_cons.2 ⟨subd10_3_209, List.forall_mem_cons.2 ⟨subd10_3_210, List.forall_mem_cons.2 ⟨subd10_3_211, List.forall_mem_cons.2 ⟨subd10_3_212, List.forall_mem_cons.2 ⟨subd10_3_213, List.forall_mem_cons.2 ⟨subd10_3_214, List.forall_mem_cons.2 ⟨subd10_3_215, List.forall_mem_cons.2 ⟨subd10_3_216, List.forall_mem_cons.2 ⟨subd10_3_217, List.forall_mem_cons.2 ⟨subd10_3_218, List.forall_mem_cons.2 ⟨subd10_3_219, List.forall_mem_cons.2 ⟨subd10_3_220, List.forall_mem_cons.2 ⟨subd10_3_221, List.forall_mem_cons.2 ⟨subd10_3_222, List.forall_mem_cons.2 ⟨subd10_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
