import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_6_480 : subd5_6 [2, 2, -1] = true := by decide +kernel
theorem subd5_6_481 : subd5_6 [2, 2, 0] = true := by decide +kernel
theorem subd5_6_482 : subd5_6 [2, 2, 1] = true := by decide +kernel
theorem subd5_6_483 : subd5_6 [2, 2, 2] = true := by decide +kernel
theorem subd5_6_484 : subd5_6 [2, 2, 3] = true := by decide +kernel
theorem subd5_6_485 : subd5_6 [2, 2, 4] = true := by decide +kernel
theorem subd5_6_486 : subd5_6 [2, 2, 5] = true := by decide +kernel
theorem subd5_6_487 : subd5_6 [2, 2, 6] = true := by decide +kernel
theorem subd5_6_488 : subd5_6 [2, 3] = true := by decide +kernel
theorem subd5_6_489 : subd5_6 [2, 4] = true := by decide +kernel
theorem subd5_6_490 : subd5_6 [2, 5] = true := by decide +kernel
theorem subd5_6_491 : subd5_6 [2, 6] = true := by decide +kernel
theorem subd5_6_492 : subd5_6 [3, -5] = true := by decide +kernel
theorem subd5_6_493 : subd5_6 [3, -4] = true := by decide +kernel
theorem subd5_6_494 : subd5_6 [3, -3] = true := by decide +kernel
theorem subd5_6_495 : subd5_6 [3, -2] = true := by decide +kernel
theorem subd5_6_496 : subd5_6 [3, -1] = true := by decide +kernel
theorem subd5_6_497 : subd5_6 [3, 0] = true := by decide +kernel
theorem subd5_6_498 : subd5_6 [3, 1] = true := by decide +kernel
theorem subd5_6_499 : subd5_6 [3, 2] = true := by decide +kernel
theorem subd5_6_500 : subd5_6 [3, 3] = true := by decide +kernel
theorem subd5_6_501 : subd5_6 [3, 4] = true := by decide +kernel
theorem subd5_6_502 : subd5_6 [3, 5] = true := by decide +kernel
theorem subd5_6_503 : subd5_6 [3, 6] = true := by decide +kernel
theorem subd5_6_504 : subd5_6 [4, -4] = true := by decide +kernel
theorem subd5_6_505 : subd5_6 [4, -3] = true := by decide +kernel
theorem subd5_6_506 : subd5_6 [4, -2] = true := by decide +kernel
theorem subd5_6_507 : subd5_6 [4, -1] = true := by decide +kernel
theorem subd5_6_508 : subd5_6 [4, 0] = true := by decide +kernel
theorem subd5_6_509 : subd5_6 [4, 1] = true := by decide +kernel
theorem subd5_6_510 : subd5_6 [4, 2] = true := by decide +kernel
theorem subd5_6_511 : subd5_6 [4, 3] = true := by decide +kernel
theorem sbd5_6_15 : ∀ q ∈ blkd5_6_15, subd5_6 q = true := by
  unfold blkd5_6_15
  exact List.forall_mem_cons.2 ⟨subd5_6_480, List.forall_mem_cons.2 ⟨subd5_6_481, List.forall_mem_cons.2 ⟨subd5_6_482, List.forall_mem_cons.2 ⟨subd5_6_483, List.forall_mem_cons.2 ⟨subd5_6_484, List.forall_mem_cons.2 ⟨subd5_6_485, List.forall_mem_cons.2 ⟨subd5_6_486, List.forall_mem_cons.2 ⟨subd5_6_487, List.forall_mem_cons.2 ⟨subd5_6_488, List.forall_mem_cons.2 ⟨subd5_6_489, List.forall_mem_cons.2 ⟨subd5_6_490, List.forall_mem_cons.2 ⟨subd5_6_491, List.forall_mem_cons.2 ⟨subd5_6_492, List.forall_mem_cons.2 ⟨subd5_6_493, List.forall_mem_cons.2 ⟨subd5_6_494, List.forall_mem_cons.2 ⟨subd5_6_495, List.forall_mem_cons.2 ⟨subd5_6_496, List.forall_mem_cons.2 ⟨subd5_6_497, List.forall_mem_cons.2 ⟨subd5_6_498, List.forall_mem_cons.2 ⟨subd5_6_499, List.forall_mem_cons.2 ⟨subd5_6_500, List.forall_mem_cons.2 ⟨subd5_6_501, List.forall_mem_cons.2 ⟨subd5_6_502, List.forall_mem_cons.2 ⟨subd5_6_503, List.forall_mem_cons.2 ⟨subd5_6_504, List.forall_mem_cons.2 ⟨subd5_6_505, List.forall_mem_cons.2 ⟨subd5_6_506, List.forall_mem_cons.2 ⟨subd5_6_507, List.forall_mem_cons.2 ⟨subd5_6_508, List.forall_mem_cons.2 ⟨subd5_6_509, List.forall_mem_cons.2 ⟨subd5_6_510, List.forall_mem_cons.2 ⟨subd5_6_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_512 : subd5_6 [4, 4] = true := by decide +kernel
theorem subd5_6_513 : subd5_6 [4, 5] = true := by decide +kernel
theorem subd5_6_514 : subd5_6 [4, 6] = true := by decide +kernel
theorem subd5_6_515 : subd5_6 [5, -3] = true := by decide +kernel
theorem subd5_6_516 : subd5_6 [5, -2] = true := by decide +kernel
theorem subd5_6_517 : subd5_6 [5, -1] = true := by decide +kernel
theorem subd5_6_518 : subd5_6 [5, 0] = true := by decide +kernel
theorem subd5_6_519 : subd5_6 [5, 1] = true := by decide +kernel
theorem subd5_6_520 : subd5_6 [5, 2] = true := by decide +kernel
theorem subd5_6_521 : subd5_6 [5, 3] = true := by decide +kernel
theorem subd5_6_522 : subd5_6 [5, 4] = true := by decide +kernel
theorem subd5_6_523 : subd5_6 [5, 5] = true := by decide +kernel
theorem subd5_6_524 : subd5_6 [6] = true := by decide +kernel
theorem sbd5_6_16 : ∀ q ∈ blkd5_6_16, subd5_6 q = true := by
  unfold blkd5_6_16
  exact List.forall_mem_cons.2 ⟨subd5_6_512, List.forall_mem_cons.2 ⟨subd5_6_513, List.forall_mem_cons.2 ⟨subd5_6_514, List.forall_mem_cons.2 ⟨subd5_6_515, List.forall_mem_cons.2 ⟨subd5_6_516, List.forall_mem_cons.2 ⟨subd5_6_517, List.forall_mem_cons.2 ⟨subd5_6_518, List.forall_mem_cons.2 ⟨subd5_6_519, List.forall_mem_cons.2 ⟨subd5_6_520, List.forall_mem_cons.2 ⟨subd5_6_521, List.forall_mem_cons.2 ⟨subd5_6_522, List.forall_mem_cons.2 ⟨subd5_6_523, List.forall_mem_cons.2 ⟨subd5_6_524, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_7 : ldCheck G d5_7.U d5_7.ms ldd5_7 = true := by decide +kernel
theorem pre_okd5_7 : subPre G cell5 d5_7 = true := by decide +kernel
theorem subd5_7_0 : subd5_7 [-5] = true := by decide +kernel
theorem subd5_7_1 : subd5_7 [-4, -5] = true := by decide +kernel
theorem subd5_7_2 : subd5_7 [-4, -4] = true := by decide +kernel
theorem subd5_7_3 : subd5_7 [-4, -3] = true := by decide +kernel
theorem subd5_7_4 : subd5_7 [-4, -2] = true := by decide +kernel
theorem subd5_7_5 : subd5_7 [-4, -1] = true := by decide +kernel
theorem subd5_7_6 : subd5_7 [-4, 0] = true := by decide +kernel
theorem subd5_7_7 : subd5_7 [-4, 1] = true := by decide +kernel
theorem subd5_7_8 : subd5_7 [-4, 2] = true := by decide +kernel
theorem subd5_7_9 : subd5_7 [-3, -6] = true := by decide +kernel
theorem subd5_7_10 : subd5_7 [-3, -5] = true := by decide +kernel
theorem subd5_7_11 : subd5_7 [-3, -4] = true := by decide +kernel
theorem subd5_7_12 : subd5_7 [-3, -3] = true := by decide +kernel
theorem subd5_7_13 : subd5_7 [-3, -2] = true := by decide +kernel
theorem subd5_7_14 : subd5_7 [-3, -1] = true := by decide +kernel
theorem subd5_7_15 : subd5_7 [-3, 0] = true := by decide +kernel
theorem subd5_7_16 : subd5_7 [-3, 1] = true := by decide +kernel
theorem subd5_7_17 : subd5_7 [-3, 2] = true := by decide +kernel
theorem subd5_7_18 : subd5_7 [-3, 3] = true := by decide +kernel
theorem subd5_7_19 : subd5_7 [-2, -6] = true := by decide +kernel
theorem subd5_7_20 : subd5_7 [-2, -5] = true := by decide +kernel
theorem subd5_7_21 : subd5_7 [-2, -4] = true := by decide +kernel
theorem subd5_7_22 : subd5_7 [-2, -3] = true := by decide +kernel
theorem subd5_7_23 : subd5_7 [-2, -2] = true := by decide +kernel
theorem subd5_7_24 : subd5_7 [-2, -1, -8] = true := by decide +kernel
theorem subd5_7_25 : subd5_7 [-2, -1, -7] = true := by decide +kernel
theorem subd5_7_26 : subd5_7 [-2, -1, -6] = true := by decide +kernel
theorem subd5_7_27 : subd5_7 [-2, -1, -5] = true := by decide +kernel
theorem subd5_7_28 : subd5_7 [-2, -1, -4] = true := by decide +kernel
theorem subd5_7_29 : subd5_7 [-2, -1, -3] = true := by decide +kernel
theorem subd5_7_30 : subd5_7 [-2, -1, -2] = true := by decide +kernel
theorem subd5_7_31 : subd5_7 [-2, -1, -1] = true := by decide +kernel
theorem sbd5_7_0 : ∀ q ∈ blkd5_7_0, subd5_7 q = true := by
  unfold blkd5_7_0
  exact List.forall_mem_cons.2 ⟨subd5_7_0, List.forall_mem_cons.2 ⟨subd5_7_1, List.forall_mem_cons.2 ⟨subd5_7_2, List.forall_mem_cons.2 ⟨subd5_7_3, List.forall_mem_cons.2 ⟨subd5_7_4, List.forall_mem_cons.2 ⟨subd5_7_5, List.forall_mem_cons.2 ⟨subd5_7_6, List.forall_mem_cons.2 ⟨subd5_7_7, List.forall_mem_cons.2 ⟨subd5_7_8, List.forall_mem_cons.2 ⟨subd5_7_9, List.forall_mem_cons.2 ⟨subd5_7_10, List.forall_mem_cons.2 ⟨subd5_7_11, List.forall_mem_cons.2 ⟨subd5_7_12, List.forall_mem_cons.2 ⟨subd5_7_13, List.forall_mem_cons.2 ⟨subd5_7_14, List.forall_mem_cons.2 ⟨subd5_7_15, List.forall_mem_cons.2 ⟨subd5_7_16, List.forall_mem_cons.2 ⟨subd5_7_17, List.forall_mem_cons.2 ⟨subd5_7_18, List.forall_mem_cons.2 ⟨subd5_7_19, List.forall_mem_cons.2 ⟨subd5_7_20, List.forall_mem_cons.2 ⟨subd5_7_21, List.forall_mem_cons.2 ⟨subd5_7_22, List.forall_mem_cons.2 ⟨subd5_7_23, List.forall_mem_cons.2 ⟨subd5_7_24, List.forall_mem_cons.2 ⟨subd5_7_25, List.forall_mem_cons.2 ⟨subd5_7_26, List.forall_mem_cons.2 ⟨subd5_7_27, List.forall_mem_cons.2 ⟨subd5_7_28, List.forall_mem_cons.2 ⟨subd5_7_29, List.forall_mem_cons.2 ⟨subd5_7_30, List.forall_mem_cons.2 ⟨subd5_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_32 : subd5_7 [-2, -1, 0] = true := by decide +kernel
theorem subd5_7_33 : subd5_7 [-2, -1, 1] = true := by decide +kernel
theorem subd5_7_34 : subd5_7 [-2, -1, 2] = true := by decide +kernel
theorem subd5_7_35 : subd5_7 [-2, -1, 3] = true := by decide +kernel
theorem subd5_7_36 : subd5_7 [-2, -1, 4] = true := by decide +kernel
theorem subd5_7_37 : subd5_7 [-2, -1, 5] = true := by decide +kernel
theorem subd5_7_38 : subd5_7 [-2, 0, -7] = true := by decide +kernel
theorem subd5_7_39 : subd5_7 [-2, 0, -6] = true := by decide +kernel
theorem subd5_7_40 : subd5_7 [-2, 0, -5] = true := by decide +kernel
theorem subd5_7_41 : subd5_7 [-2, 0, -4] = true := by decide +kernel
theorem subd5_7_42 : subd5_7 [-2, 0, -3] = true := by decide +kernel
theorem subd5_7_43 : subd5_7 [-2, 0, -2] = true := by decide +kernel
theorem subd5_7_44 : subd5_7 [-2, 0, -1] = true := by decide +kernel
theorem subd5_7_45 : subd5_7 [-2, 0, 0] = true := by decide +kernel
theorem subd5_7_46 : subd5_7 [-2, 0, 1] = true := by decide +kernel
theorem subd5_7_47 : subd5_7 [-2, 0, 2] = true := by decide +kernel
theorem subd5_7_48 : subd5_7 [-2, 0, 3] = true := by decide +kernel
theorem subd5_7_49 : subd5_7 [-2, 0, 4] = true := by decide +kernel
theorem subd5_7_50 : subd5_7 [-2, 0, 5] = true := by decide +kernel
theorem subd5_7_51 : subd5_7 [-2, 1] = true := by decide +kernel
theorem subd5_7_52 : subd5_7 [-2, 2] = true := by decide +kernel
theorem subd5_7_53 : subd5_7 [-2, 3] = true := by decide +kernel
theorem subd5_7_54 : subd5_7 [-2, 4] = true := by decide +kernel
theorem subd5_7_55 : subd5_7 [-1, -6] = true := by decide +kernel
theorem subd5_7_56 : subd5_7 [-1, -5] = true := by decide +kernel
theorem subd5_7_57 : subd5_7 [-1, -4] = true := by decide +kernel
theorem subd5_7_58 : subd5_7 [-1, -3] = true := by decide +kernel
theorem subd5_7_59 : subd5_7 [-1, -2, -8] = true := by decide +kernel
theorem subd5_7_60 : subd5_7 [-1, -2, -7] = true := by decide +kernel
theorem subd5_7_61 : subd5_7 [-1, -2, -6] = true := by decide +kernel
theorem subd5_7_62 : subd5_7 [-1, -2, -5] = true := by decide +kernel
theorem subd5_7_63 : subd5_7 [-1, -2, -4] = true := by decide +kernel
theorem sbd5_7_1 : ∀ q ∈ blkd5_7_1, subd5_7 q = true := by
  unfold blkd5_7_1
  exact List.forall_mem_cons.2 ⟨subd5_7_32, List.forall_mem_cons.2 ⟨subd5_7_33, List.forall_mem_cons.2 ⟨subd5_7_34, List.forall_mem_cons.2 ⟨subd5_7_35, List.forall_mem_cons.2 ⟨subd5_7_36, List.forall_mem_cons.2 ⟨subd5_7_37, List.forall_mem_cons.2 ⟨subd5_7_38, List.forall_mem_cons.2 ⟨subd5_7_39, List.forall_mem_cons.2 ⟨subd5_7_40, List.forall_mem_cons.2 ⟨subd5_7_41, List.forall_mem_cons.2 ⟨subd5_7_42, List.forall_mem_cons.2 ⟨subd5_7_43, List.forall_mem_cons.2 ⟨subd5_7_44, List.forall_mem_cons.2 ⟨subd5_7_45, List.forall_mem_cons.2 ⟨subd5_7_46, List.forall_mem_cons.2 ⟨subd5_7_47, List.forall_mem_cons.2 ⟨subd5_7_48, List.forall_mem_cons.2 ⟨subd5_7_49, List.forall_mem_cons.2 ⟨subd5_7_50, List.forall_mem_cons.2 ⟨subd5_7_51, List.forall_mem_cons.2 ⟨subd5_7_52, List.forall_mem_cons.2 ⟨subd5_7_53, List.forall_mem_cons.2 ⟨subd5_7_54, List.forall_mem_cons.2 ⟨subd5_7_55, List.forall_mem_cons.2 ⟨subd5_7_56, List.forall_mem_cons.2 ⟨subd5_7_57, List.forall_mem_cons.2 ⟨subd5_7_58, List.forall_mem_cons.2 ⟨subd5_7_59, List.forall_mem_cons.2 ⟨subd5_7_60, List.forall_mem_cons.2 ⟨subd5_7_61, List.forall_mem_cons.2 ⟨subd5_7_62, List.forall_mem_cons.2 ⟨subd5_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_64 : subd5_7 [-1, -2, -3] = true := by decide +kernel
theorem subd5_7_65 : subd5_7 [-1, -2, -2] = true := by decide +kernel
theorem subd5_7_66 : subd5_7 [-1, -2, -1] = true := by decide +kernel
theorem subd5_7_67 : subd5_7 [-1, -2, 0] = true := by decide +kernel
theorem subd5_7_68 : subd5_7 [-1, -2, 1] = true := by decide +kernel
theorem subd5_7_69 : subd5_7 [-1, -2, 2] = true := by decide +kernel
theorem subd5_7_70 : subd5_7 [-1, -2, 3] = true := by decide +kernel
theorem subd5_7_71 : subd5_7 [-1, -2, 4] = true := by decide +kernel
theorem subd5_7_72 : subd5_7 [-1, -2, 5] = true := by decide +kernel
theorem subd5_7_73 : subd5_7 [-1, -1, -8] = true := by decide +kernel
theorem subd5_7_74 : subd5_7 [-1, -1, -7] = true := by decide +kernel
theorem subd5_7_75 : subd5_7 [-1, -1, -6] = true := by decide +kernel
theorem subd5_7_76 : subd5_7 [-1, -1, -5] = true := by decide +kernel
theorem subd5_7_77 : subd5_7 [-1, -1, -4] = true := by decide +kernel
theorem subd5_7_78 : subd5_7 [-1, -1, -3] = true := by decide +kernel
theorem subd5_7_79 : subd5_7 [-1, -1, -2] = true := by decide +kernel
theorem subd5_7_80 : subd5_7 [-1, -1, -1] = true := by decide +kernel
theorem subd5_7_81 : subd5_7 [-1, -1, 0] = true := by decide +kernel
theorem subd5_7_82 : subd5_7 [-1, -1, 1] = true := by decide +kernel
theorem subd5_7_83 : subd5_7 [-1, -1, 2] = true := by decide +kernel
theorem subd5_7_84 : subd5_7 [-1, -1, 3] = true := by decide +kernel
theorem subd5_7_85 : subd5_7 [-1, -1, 4] = true := by decide +kernel
theorem subd5_7_86 : subd5_7 [-1, -1, 5] = true := by decide +kernel
theorem subd5_7_87 : subd5_7 [-1, -1, 6] = true := by decide +kernel
theorem subd5_7_88 : subd5_7 [-1, 0, -8] = true := by decide +kernel
theorem subd5_7_89 : subd5_7 [-1, 0, -7] = true := by decide +kernel
theorem subd5_7_90 : subd5_7 [-1, 0, -6] = true := by decide +kernel
theorem subd5_7_91 : subd5_7 [-1, 0, -5] = true := by decide +kernel
theorem subd5_7_92 : subd5_7 [-1, 0, -4] = true := by decide +kernel
theorem subd5_7_93 : subd5_7 [-1, 0, -3] = true := by decide +kernel
theorem subd5_7_94 : subd5_7 [-1, 0, -2] = true := by decide +kernel
theorem subd5_7_95 : subd5_7 [-1, 0, -1] = true := by decide +kernel
theorem sbd5_7_2 : ∀ q ∈ blkd5_7_2, subd5_7 q = true := by
  unfold blkd5_7_2
  exact List.forall_mem_cons.2 ⟨subd5_7_64, List.forall_mem_cons.2 ⟨subd5_7_65, List.forall_mem_cons.2 ⟨subd5_7_66, List.forall_mem_cons.2 ⟨subd5_7_67, List.forall_mem_cons.2 ⟨subd5_7_68, List.forall_mem_cons.2 ⟨subd5_7_69, List.forall_mem_cons.2 ⟨subd5_7_70, List.forall_mem_cons.2 ⟨subd5_7_71, List.forall_mem_cons.2 ⟨subd5_7_72, List.forall_mem_cons.2 ⟨subd5_7_73, List.forall_mem_cons.2 ⟨subd5_7_74, List.forall_mem_cons.2 ⟨subd5_7_75, List.forall_mem_cons.2 ⟨subd5_7_76, List.forall_mem_cons.2 ⟨subd5_7_77, List.forall_mem_cons.2 ⟨subd5_7_78, List.forall_mem_cons.2 ⟨subd5_7_79, List.forall_mem_cons.2 ⟨subd5_7_80, List.forall_mem_cons.2 ⟨subd5_7_81, List.forall_mem_cons.2 ⟨subd5_7_82, List.forall_mem_cons.2 ⟨subd5_7_83, List.forall_mem_cons.2 ⟨subd5_7_84, List.forall_mem_cons.2 ⟨subd5_7_85, List.forall_mem_cons.2 ⟨subd5_7_86, List.forall_mem_cons.2 ⟨subd5_7_87, List.forall_mem_cons.2 ⟨subd5_7_88, List.forall_mem_cons.2 ⟨subd5_7_89, List.forall_mem_cons.2 ⟨subd5_7_90, List.forall_mem_cons.2 ⟨subd5_7_91, List.forall_mem_cons.2 ⟨subd5_7_92, List.forall_mem_cons.2 ⟨subd5_7_93, List.forall_mem_cons.2 ⟨subd5_7_94, List.forall_mem_cons.2 ⟨subd5_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_96 : subd5_7 [-1, 0, 0] = true := by decide +kernel
theorem subd5_7_97 : subd5_7 [-1, 0, 1] = true := by decide +kernel
theorem subd5_7_98 : subd5_7 [-1, 0, 2] = true := by decide +kernel
theorem subd5_7_99 : subd5_7 [-1, 0, 3] = true := by decide +kernel
theorem subd5_7_100 : subd5_7 [-1, 0, 4] = true := by decide +kernel
theorem subd5_7_101 : subd5_7 [-1, 0, 5] = true := by decide +kernel
theorem subd5_7_102 : subd5_7 [-1, 0, 6] = true := by decide +kernel
theorem subd5_7_103 : subd5_7 [-1, 1, -7] = true := by decide +kernel
theorem subd5_7_104 : subd5_7 [-1, 1, -6] = true := by decide +kernel
theorem subd5_7_105 : subd5_7 [-1, 1, -5] = true := by decide +kernel
theorem subd5_7_106 : subd5_7 [-1, 1, -4] = true := by decide +kernel
theorem subd5_7_107 : subd5_7 [-1, 1, -3] = true := by decide +kernel
theorem subd5_7_108 : subd5_7 [-1, 1, -2] = true := by decide +kernel
theorem subd5_7_109 : subd5_7 [-1, 1, -1] = true := by decide +kernel
theorem subd5_7_110 : subd5_7 [-1, 1, 0] = true := by decide +kernel
theorem subd5_7_111 : subd5_7 [-1, 1, 1] = true := by decide +kernel
theorem subd5_7_112 : subd5_7 [-1, 1, 2] = true := by decide +kernel
theorem subd5_7_113 : subd5_7 [-1, 1, 3] = true := by decide +kernel
theorem subd5_7_114 : subd5_7 [-1, 1, 4] = true := by decide +kernel
theorem subd5_7_115 : subd5_7 [-1, 1, 5] = true := by decide +kernel
theorem subd5_7_116 : subd5_7 [-1, 1, 6] = true := by decide +kernel
theorem subd5_7_117 : subd5_7 [-1, 2] = true := by decide +kernel
theorem subd5_7_118 : subd5_7 [-1, 3] = true := by decide +kernel
theorem subd5_7_119 : subd5_7 [-1, 4] = true := by decide +kernel
theorem subd5_7_120 : subd5_7 [-1, 5] = true := by decide +kernel
theorem subd5_7_121 : subd5_7 [0, -6] = true := by decide +kernel
theorem subd5_7_122 : subd5_7 [0, -5] = true := by decide +kernel
theorem subd5_7_123 : subd5_7 [0, -4] = true := by decide +kernel
theorem subd5_7_124 : subd5_7 [0, -3] = true := by decide +kernel
theorem subd5_7_125 : subd5_7 [0, -2, -7] = true := by decide +kernel
theorem subd5_7_126 : subd5_7 [0, -2, -6] = true := by decide +kernel
theorem subd5_7_127 : subd5_7 [0, -2, -5] = true := by decide +kernel
theorem sbd5_7_3 : ∀ q ∈ blkd5_7_3, subd5_7 q = true := by
  unfold blkd5_7_3
  exact List.forall_mem_cons.2 ⟨subd5_7_96, List.forall_mem_cons.2 ⟨subd5_7_97, List.forall_mem_cons.2 ⟨subd5_7_98, List.forall_mem_cons.2 ⟨subd5_7_99, List.forall_mem_cons.2 ⟨subd5_7_100, List.forall_mem_cons.2 ⟨subd5_7_101, List.forall_mem_cons.2 ⟨subd5_7_102, List.forall_mem_cons.2 ⟨subd5_7_103, List.forall_mem_cons.2 ⟨subd5_7_104, List.forall_mem_cons.2 ⟨subd5_7_105, List.forall_mem_cons.2 ⟨subd5_7_106, List.forall_mem_cons.2 ⟨subd5_7_107, List.forall_mem_cons.2 ⟨subd5_7_108, List.forall_mem_cons.2 ⟨subd5_7_109, List.forall_mem_cons.2 ⟨subd5_7_110, List.forall_mem_cons.2 ⟨subd5_7_111, List.forall_mem_cons.2 ⟨subd5_7_112, List.forall_mem_cons.2 ⟨subd5_7_113, List.forall_mem_cons.2 ⟨subd5_7_114, List.forall_mem_cons.2 ⟨subd5_7_115, List.forall_mem_cons.2 ⟨subd5_7_116, List.forall_mem_cons.2 ⟨subd5_7_117, List.forall_mem_cons.2 ⟨subd5_7_118, List.forall_mem_cons.2 ⟨subd5_7_119, List.forall_mem_cons.2 ⟨subd5_7_120, List.forall_mem_cons.2 ⟨subd5_7_121, List.forall_mem_cons.2 ⟨subd5_7_122, List.forall_mem_cons.2 ⟨subd5_7_123, List.forall_mem_cons.2 ⟨subd5_7_124, List.forall_mem_cons.2 ⟨subd5_7_125, List.forall_mem_cons.2 ⟨subd5_7_126, List.forall_mem_cons.2 ⟨subd5_7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C099
