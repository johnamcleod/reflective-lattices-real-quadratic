import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_2_512 : subd8_2 [2, 0, 2] = true := by decide +kernel
theorem subd8_2_513 : subd8_2 [2, 0, 3] = true := by decide +kernel
theorem subd8_2_514 : subd8_2 [2, 0, 4] = true := by decide +kernel
theorem subd8_2_515 : subd8_2 [2, 0, 5] = true := by decide +kernel
theorem subd8_2_516 : subd8_2 [2, 0, 6] = true := by decide +kernel
theorem subd8_2_517 : subd8_2 [2, 0, 7] = true := by decide +kernel
theorem subd8_2_518 : subd8_2 [2, 1, -8] = true := by decide +kernel
theorem subd8_2_519 : subd8_2 [2, 1, -7] = true := by decide +kernel
theorem subd8_2_520 : subd8_2 [2, 1, -6] = true := by decide +kernel
theorem subd8_2_521 : subd8_2 [2, 1, -5] = true := by decide +kernel
theorem subd8_2_522 : subd8_2 [2, 1, -4] = true := by decide +kernel
theorem subd8_2_523 : subd8_2 [2, 1, -3] = true := by decide +kernel
theorem subd8_2_524 : subd8_2 [2, 1, -2] = true := by decide +kernel
theorem subd8_2_525 : subd8_2 [2, 1, -1] = true := by decide +kernel
theorem subd8_2_526 : subd8_2 [2, 1, 0] = true := by decide +kernel
theorem subd8_2_527 : subd8_2 [2, 1, 1] = true := by decide +kernel
theorem subd8_2_528 : subd8_2 [2, 1, 2] = true := by decide +kernel
theorem subd8_2_529 : subd8_2 [2, 1, 3] = true := by decide +kernel
theorem subd8_2_530 : subd8_2 [2, 1, 4] = true := by decide +kernel
theorem subd8_2_531 : subd8_2 [2, 1, 5] = true := by decide +kernel
theorem subd8_2_532 : subd8_2 [2, 1, 6] = true := by decide +kernel
theorem subd8_2_533 : subd8_2 [2, 2] = true := by decide +kernel
theorem subd8_2_534 : subd8_2 [2, 3] = true := by decide +kernel
theorem subd8_2_535 : subd8_2 [3, -5] = true := by decide +kernel
theorem subd8_2_536 : subd8_2 [3, -4] = true := by decide +kernel
theorem subd8_2_537 : subd8_2 [3, -3] = true := by decide +kernel
theorem subd8_2_538 : subd8_2 [3, -2, -7] = true := by decide +kernel
theorem subd8_2_539 : subd8_2 [3, -2, -6] = true := by decide +kernel
theorem subd8_2_540 : subd8_2 [3, -2, -5] = true := by decide +kernel
theorem subd8_2_541 : subd8_2 [3, -2, -4] = true := by decide +kernel
theorem subd8_2_542 : subd8_2 [3, -2, -3] = true := by decide +kernel
theorem subd8_2_543 : subd8_2 [3, -2, -2] = true := by decide +kernel
theorem sbd8_2_16 : ∀ q ∈ blkd8_2_16, subd8_2 q = true := by
  unfold blkd8_2_16
  exact List.forall_mem_cons.2 ⟨subd8_2_512, List.forall_mem_cons.2 ⟨subd8_2_513, List.forall_mem_cons.2 ⟨subd8_2_514, List.forall_mem_cons.2 ⟨subd8_2_515, List.forall_mem_cons.2 ⟨subd8_2_516, List.forall_mem_cons.2 ⟨subd8_2_517, List.forall_mem_cons.2 ⟨subd8_2_518, List.forall_mem_cons.2 ⟨subd8_2_519, List.forall_mem_cons.2 ⟨subd8_2_520, List.forall_mem_cons.2 ⟨subd8_2_521, List.forall_mem_cons.2 ⟨subd8_2_522, List.forall_mem_cons.2 ⟨subd8_2_523, List.forall_mem_cons.2 ⟨subd8_2_524, List.forall_mem_cons.2 ⟨subd8_2_525, List.forall_mem_cons.2 ⟨subd8_2_526, List.forall_mem_cons.2 ⟨subd8_2_527, List.forall_mem_cons.2 ⟨subd8_2_528, List.forall_mem_cons.2 ⟨subd8_2_529, List.forall_mem_cons.2 ⟨subd8_2_530, List.forall_mem_cons.2 ⟨subd8_2_531, List.forall_mem_cons.2 ⟨subd8_2_532, List.forall_mem_cons.2 ⟨subd8_2_533, List.forall_mem_cons.2 ⟨subd8_2_534, List.forall_mem_cons.2 ⟨subd8_2_535, List.forall_mem_cons.2 ⟨subd8_2_536, List.forall_mem_cons.2 ⟨subd8_2_537, List.forall_mem_cons.2 ⟨subd8_2_538, List.forall_mem_cons.2 ⟨subd8_2_539, List.forall_mem_cons.2 ⟨subd8_2_540, List.forall_mem_cons.2 ⟨subd8_2_541, List.forall_mem_cons.2 ⟨subd8_2_542, List.forall_mem_cons.2 ⟨subd8_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_544 : subd8_2 [3, -2, -1] = true := by decide +kernel
theorem subd8_2_545 : subd8_2 [3, -2, 0] = true := by decide +kernel
theorem subd8_2_546 : subd8_2 [3, -2, 1] = true := by decide +kernel
theorem subd8_2_547 : subd8_2 [3, -2, 2] = true := by decide +kernel
theorem subd8_2_548 : subd8_2 [3, -2, 3] = true := by decide +kernel
theorem subd8_2_549 : subd8_2 [3, -2, 4] = true := by decide +kernel
theorem subd8_2_550 : subd8_2 [3, -2, 5] = true := by decide +kernel
theorem subd8_2_551 : subd8_2 [3, -1, -7] = true := by decide +kernel
theorem subd8_2_552 : subd8_2 [3, -1, -6] = true := by decide +kernel
theorem subd8_2_553 : subd8_2 [3, -1, -5] = true := by decide +kernel
theorem subd8_2_554 : subd8_2 [3, -1, -4] = true := by decide +kernel
theorem subd8_2_555 : subd8_2 [3, -1, -3] = true := by decide +kernel
theorem subd8_2_556 : subd8_2 [3, -1, -2] = true := by decide +kernel
theorem subd8_2_557 : subd8_2 [3, -1, -1] = true := by decide +kernel
theorem subd8_2_558 : subd8_2 [3, -1, 0] = true := by decide +kernel
theorem subd8_2_559 : subd8_2 [3, -1, 1] = true := by decide +kernel
theorem subd8_2_560 : subd8_2 [3, -1, 2] = true := by decide +kernel
theorem subd8_2_561 : subd8_2 [3, -1, 3] = true := by decide +kernel
theorem subd8_2_562 : subd8_2 [3, -1, 4] = true := by decide +kernel
theorem subd8_2_563 : subd8_2 [3, -1, 5] = true := by decide +kernel
theorem subd8_2_564 : subd8_2 [3, 0] = true := by decide +kernel
theorem subd8_2_565 : subd8_2 [3, 1] = true := by decide +kernel
theorem subd8_2_566 : subd8_2 [4] = true := by decide +kernel
theorem sbd8_2_17 : ∀ q ∈ blkd8_2_17, subd8_2 q = true := by
  unfold blkd8_2_17
  exact List.forall_mem_cons.2 ⟨subd8_2_544, List.forall_mem_cons.2 ⟨subd8_2_545, List.forall_mem_cons.2 ⟨subd8_2_546, List.forall_mem_cons.2 ⟨subd8_2_547, List.forall_mem_cons.2 ⟨subd8_2_548, List.forall_mem_cons.2 ⟨subd8_2_549, List.forall_mem_cons.2 ⟨subd8_2_550, List.forall_mem_cons.2 ⟨subd8_2_551, List.forall_mem_cons.2 ⟨subd8_2_552, List.forall_mem_cons.2 ⟨subd8_2_553, List.forall_mem_cons.2 ⟨subd8_2_554, List.forall_mem_cons.2 ⟨subd8_2_555, List.forall_mem_cons.2 ⟨subd8_2_556, List.forall_mem_cons.2 ⟨subd8_2_557, List.forall_mem_cons.2 ⟨subd8_2_558, List.forall_mem_cons.2 ⟨subd8_2_559, List.forall_mem_cons.2 ⟨subd8_2_560, List.forall_mem_cons.2 ⟨subd8_2_561, List.forall_mem_cons.2 ⟨subd8_2_562, List.forall_mem_cons.2 ⟨subd8_2_563, List.forall_mem_cons.2 ⟨subd8_2_564, List.forall_mem_cons.2 ⟨subd8_2_565, List.forall_mem_cons.2 ⟨subd8_2_566, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-4] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-3, -4] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-3, -3] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-3, -2] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [-3, -1] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [-3, 0] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [-3, 1] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [-3, 2] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [-3, 3] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [-3, 4] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [-2, -5] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [-2, -4] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [-2, -3] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [-2, -2] = true := by decide +kernel
theorem subd8_3_14 : subd8_3 [-2, -1] = true := by decide +kernel
theorem subd8_3_15 : subd8_3 [-2, 0] = true := by decide +kernel
theorem subd8_3_16 : subd8_3 [-2, 1] = true := by decide +kernel
theorem subd8_3_17 : subd8_3 [-2, 2] = true := by decide +kernel
theorem subd8_3_18 : subd8_3 [-2, 3] = true := by decide +kernel
theorem subd8_3_19 : subd8_3 [-2, 4] = true := by decide +kernel
theorem subd8_3_20 : subd8_3 [-1, -6] = true := by decide +kernel
theorem subd8_3_21 : subd8_3 [-1, -5] = true := by decide +kernel
theorem subd8_3_22 : subd8_3 [-1, -4] = true := by decide +kernel
theorem subd8_3_23 : subd8_3 [-1, -3] = true := by decide +kernel
theorem subd8_3_24 : subd8_3 [-1, -2] = true := by decide +kernel
theorem subd8_3_25 : subd8_3 [-1, -1] = true := by decide +kernel
theorem subd8_3_26 : subd8_3 [-1, 0] = true := by decide +kernel
theorem subd8_3_27 : subd8_3 [-1, 1] = true := by decide +kernel
theorem subd8_3_28 : subd8_3 [-1, 2] = true := by decide +kernel
theorem subd8_3_29 : subd8_3 [-1, 3] = true := by decide +kernel
theorem subd8_3_30 : subd8_3 [-1, 4] = true := by decide +kernel
theorem subd8_3_31 : subd8_3 [-1, 5] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_cons.2 ⟨subd8_3_14, List.forall_mem_cons.2 ⟨subd8_3_15, List.forall_mem_cons.2 ⟨subd8_3_16, List.forall_mem_cons.2 ⟨subd8_3_17, List.forall_mem_cons.2 ⟨subd8_3_18, List.forall_mem_cons.2 ⟨subd8_3_19, List.forall_mem_cons.2 ⟨subd8_3_20, List.forall_mem_cons.2 ⟨subd8_3_21, List.forall_mem_cons.2 ⟨subd8_3_22, List.forall_mem_cons.2 ⟨subd8_3_23, List.forall_mem_cons.2 ⟨subd8_3_24, List.forall_mem_cons.2 ⟨subd8_3_25, List.forall_mem_cons.2 ⟨subd8_3_26, List.forall_mem_cons.2 ⟨subd8_3_27, List.forall_mem_cons.2 ⟨subd8_3_28, List.forall_mem_cons.2 ⟨subd8_3_29, List.forall_mem_cons.2 ⟨subd8_3_30, List.forall_mem_cons.2 ⟨subd8_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_32 : subd8_3 [0, -6] = true := by decide +kernel
theorem subd8_3_33 : subd8_3 [0, -5] = true := by decide +kernel
theorem subd8_3_34 : subd8_3 [0, -4] = true := by decide +kernel
theorem subd8_3_35 : subd8_3 [0, -3] = true := by decide +kernel
theorem subd8_3_36 : subd8_3 [0, -2] = true := by decide +kernel
theorem subd8_3_37 : subd8_3 [0, -1] = true := by decide +kernel
theorem subd8_3_38 : subd8_3 [0, 0] = true := by decide +kernel
theorem subd8_3_39 : subd8_3 [0, 1] = true := by decide +kernel
theorem subd8_3_40 : subd8_3 [0, 2] = true := by decide +kernel
theorem subd8_3_41 : subd8_3 [0, 3] = true := by decide +kernel
theorem subd8_3_42 : subd8_3 [0, 4] = true := by decide +kernel
theorem subd8_3_43 : subd8_3 [0, 5] = true := by decide +kernel
theorem subd8_3_44 : subd8_3 [1, -6] = true := by decide +kernel
theorem subd8_3_45 : subd8_3 [1, -5] = true := by decide +kernel
theorem subd8_3_46 : subd8_3 [1, -4] = true := by decide +kernel
theorem subd8_3_47 : subd8_3 [1, -3] = true := by decide +kernel
theorem subd8_3_48 : subd8_3 [1, -2] = true := by decide +kernel
theorem subd8_3_49 : subd8_3 [1, -1] = true := by decide +kernel
theorem subd8_3_50 : subd8_3 [1, 0] = true := by decide +kernel
theorem subd8_3_51 : subd8_3 [1, 1] = true := by decide +kernel
theorem subd8_3_52 : subd8_3 [1, 2] = true := by decide +kernel
theorem subd8_3_53 : subd8_3 [1, 3] = true := by decide +kernel
theorem subd8_3_54 : subd8_3 [1, 4] = true := by decide +kernel
theorem subd8_3_55 : subd8_3 [1, 5] = true := by decide +kernel
theorem subd8_3_56 : subd8_3 [2, -5] = true := by decide +kernel
theorem subd8_3_57 : subd8_3 [2, -4] = true := by decide +kernel
theorem subd8_3_58 : subd8_3 [2, -3] = true := by decide +kernel
theorem subd8_3_59 : subd8_3 [2, -2] = true := by decide +kernel
theorem subd8_3_60 : subd8_3 [2, -1] = true := by decide +kernel
theorem subd8_3_61 : subd8_3 [2, 0] = true := by decide +kernel
theorem subd8_3_62 : subd8_3 [2, 1] = true := by decide +kernel
theorem subd8_3_63 : subd8_3 [2, 2] = true := by decide +kernel
theorem sbd8_3_1 : ∀ q ∈ blkd8_3_1, subd8_3 q = true := by
  unfold blkd8_3_1
  exact List.forall_mem_cons.2 ⟨subd8_3_32, List.forall_mem_cons.2 ⟨subd8_3_33, List.forall_mem_cons.2 ⟨subd8_3_34, List.forall_mem_cons.2 ⟨subd8_3_35, List.forall_mem_cons.2 ⟨subd8_3_36, List.forall_mem_cons.2 ⟨subd8_3_37, List.forall_mem_cons.2 ⟨subd8_3_38, List.forall_mem_cons.2 ⟨subd8_3_39, List.forall_mem_cons.2 ⟨subd8_3_40, List.forall_mem_cons.2 ⟨subd8_3_41, List.forall_mem_cons.2 ⟨subd8_3_42, List.forall_mem_cons.2 ⟨subd8_3_43, List.forall_mem_cons.2 ⟨subd8_3_44, List.forall_mem_cons.2 ⟨subd8_3_45, List.forall_mem_cons.2 ⟨subd8_3_46, List.forall_mem_cons.2 ⟨subd8_3_47, List.forall_mem_cons.2 ⟨subd8_3_48, List.forall_mem_cons.2 ⟨subd8_3_49, List.forall_mem_cons.2 ⟨subd8_3_50, List.forall_mem_cons.2 ⟨subd8_3_51, List.forall_mem_cons.2 ⟨subd8_3_52, List.forall_mem_cons.2 ⟨subd8_3_53, List.forall_mem_cons.2 ⟨subd8_3_54, List.forall_mem_cons.2 ⟨subd8_3_55, List.forall_mem_cons.2 ⟨subd8_3_56, List.forall_mem_cons.2 ⟨subd8_3_57, List.forall_mem_cons.2 ⟨subd8_3_58, List.forall_mem_cons.2 ⟨subd8_3_59, List.forall_mem_cons.2 ⟨subd8_3_60, List.forall_mem_cons.2 ⟨subd8_3_61, List.forall_mem_cons.2 ⟨subd8_3_62, List.forall_mem_cons.2 ⟨subd8_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_64 : subd8_3 [2, 3] = true := by decide +kernel
theorem subd8_3_65 : subd8_3 [2, 4] = true := by decide +kernel
theorem subd8_3_66 : subd8_3 [3, -5] = true := by decide +kernel
theorem subd8_3_67 : subd8_3 [3, -4] = true := by decide +kernel
theorem subd8_3_68 : subd8_3 [3, -3] = true := by decide +kernel
theorem subd8_3_69 : subd8_3 [3, -2] = true := by decide +kernel
theorem subd8_3_70 : subd8_3 [3, -1] = true := by decide +kernel
theorem subd8_3_71 : subd8_3 [3, 0] = true := by decide +kernel
theorem subd8_3_72 : subd8_3 [3, 1] = true := by decide +kernel
theorem subd8_3_73 : subd8_3 [3, 2] = true := by decide +kernel
theorem subd8_3_74 : subd8_3 [3, 3] = true := by decide +kernel
theorem subd8_3_75 : subd8_3 [4] = true := by decide +kernel
theorem sbd8_3_2 : ∀ q ∈ blkd8_3_2, subd8_3 q = true := by
  unfold blkd8_3_2
  exact List.forall_mem_cons.2 ⟨subd8_3_64, List.forall_mem_cons.2 ⟨subd8_3_65, List.forall_mem_cons.2 ⟨subd8_3_66, List.forall_mem_cons.2 ⟨subd8_3_67, List.forall_mem_cons.2 ⟨subd8_3_68, List.forall_mem_cons.2 ⟨subd8_3_69, List.forall_mem_cons.2 ⟨subd8_3_70, List.forall_mem_cons.2 ⟨subd8_3_71, List.forall_mem_cons.2 ⟨subd8_3_72, List.forall_mem_cons.2 ⟨subd8_3_73, List.forall_mem_cons.2 ⟨subd8_3_74, List.forall_mem_cons.2 ⟨subd8_3_75, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_4 : ldCheck G d8_4.U d8_4.ms ldd8_4 = true := by decide +kernel
theorem pre_okd8_4 : subPre G cell8 d8_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C110
