import ReflectZphi.Data.Cert5.C102.Base

namespace ReflectZphi.Data.Cert5.C102
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_544 : sub5 [2, 1, 3] = true := by decide +kernel
theorem sub5_545 : sub5 [2, 1, 4] = true := by decide +kernel
theorem sub5_546 : sub5 [2, 1, 5] = true := by decide +kernel
theorem sub5_547 : sub5 [2, 1, 6] = true := by decide +kernel
theorem sub5_548 : sub5 [2, 1, 7] = true := by decide +kernel
theorem sub5_549 : sub5 [2, 1, 8] = true := by decide +kernel
theorem sub5_550 : sub5 [2, 2, -6] = true := by decide +kernel
theorem sub5_551 : sub5 [2, 2, -5] = true := by decide +kernel
theorem sub5_552 : sub5 [2, 2, -4] = true := by decide +kernel
theorem sub5_553 : sub5 [2, 2, -3] = true := by decide +kernel
theorem sub5_554 : sub5 [2, 2, -2] = true := by decide +kernel
theorem sub5_555 : sub5 [2, 2, -1] = true := by decide +kernel
theorem sub5_556 : sub5 [2, 2, 0] = true := by decide +kernel
theorem sub5_557 : sub5 [2, 2, 1] = true := by decide +kernel
theorem sub5_558 : sub5 [2, 2, 2] = true := by decide +kernel
theorem sub5_559 : sub5 [2, 2, 3] = true := by decide +kernel
theorem sub5_560 : sub5 [2, 2, 4] = true := by decide +kernel
theorem sub5_561 : sub5 [2, 2, 5] = true := by decide +kernel
theorem sub5_562 : sub5 [2, 2, 6] = true := by decide +kernel
theorem sub5_563 : sub5 [2, 2, 7] = true := by decide +kernel
theorem sub5_564 : sub5 [2, 2, 8] = true := by decide +kernel
theorem sub5_565 : sub5 [2, 3] = true := by decide +kernel
theorem sub5_566 : sub5 [2, 4] = true := by decide +kernel
theorem sub5_567 : sub5 [2, 5] = true := by decide +kernel
theorem sub5_568 : sub5 [3, -5] = true := by decide +kernel
theorem sub5_569 : sub5 [3, -4] = true := by decide +kernel
theorem sub5_570 : sub5 [3, -3] = true := by decide +kernel
theorem sub5_571 : sub5 [3, -2] = true := by decide +kernel
theorem sub5_572 : sub5 [3, -1] = true := by decide +kernel
theorem sub5_573 : sub5 [3, 0, -6] = true := by decide +kernel
theorem sub5_574 : sub5 [3, 0, -5] = true := by decide +kernel
theorem sub5_575 : sub5 [3, 0, -4] = true := by decide +kernel
theorem sb5_17 : ∀ q ∈ blk5_17, sub5 q = true := by
  unfold blk5_17
  exact List.forall_mem_cons.2 ⟨sub5_544, List.forall_mem_cons.2 ⟨sub5_545, List.forall_mem_cons.2 ⟨sub5_546, List.forall_mem_cons.2 ⟨sub5_547, List.forall_mem_cons.2 ⟨sub5_548, List.forall_mem_cons.2 ⟨sub5_549, List.forall_mem_cons.2 ⟨sub5_550, List.forall_mem_cons.2 ⟨sub5_551, List.forall_mem_cons.2 ⟨sub5_552, List.forall_mem_cons.2 ⟨sub5_553, List.forall_mem_cons.2 ⟨sub5_554, List.forall_mem_cons.2 ⟨sub5_555, List.forall_mem_cons.2 ⟨sub5_556, List.forall_mem_cons.2 ⟨sub5_557, List.forall_mem_cons.2 ⟨sub5_558, List.forall_mem_cons.2 ⟨sub5_559, List.forall_mem_cons.2 ⟨sub5_560, List.forall_mem_cons.2 ⟨sub5_561, List.forall_mem_cons.2 ⟨sub5_562, List.forall_mem_cons.2 ⟨sub5_563, List.forall_mem_cons.2 ⟨sub5_564, List.forall_mem_cons.2 ⟨sub5_565, List.forall_mem_cons.2 ⟨sub5_566, List.forall_mem_cons.2 ⟨sub5_567, List.forall_mem_cons.2 ⟨sub5_568, List.forall_mem_cons.2 ⟨sub5_569, List.forall_mem_cons.2 ⟨sub5_570, List.forall_mem_cons.2 ⟨sub5_571, List.forall_mem_cons.2 ⟨sub5_572, List.forall_mem_cons.2 ⟨sub5_573, List.forall_mem_cons.2 ⟨sub5_574, List.forall_mem_cons.2 ⟨sub5_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_576 : sub5 [3, 0, -3] = true := by decide +kernel
theorem sub5_577 : sub5 [3, 0, -2] = true := by decide +kernel
theorem sub5_578 : sub5 [3, 0, -1] = true := by decide +kernel
theorem sub5_579 : sub5 [3, 0, 0] = true := by decide +kernel
theorem sub5_580 : sub5 [3, 0, 1] = true := by decide +kernel
theorem sub5_581 : sub5 [3, 0, 2] = true := by decide +kernel
theorem sub5_582 : sub5 [3, 0, 3] = true := by decide +kernel
theorem sub5_583 : sub5 [3, 0, 4] = true := by decide +kernel
theorem sub5_584 : sub5 [3, 0, 5] = true := by decide +kernel
theorem sub5_585 : sub5 [3, 0, 6] = true := by decide +kernel
theorem sub5_586 : sub5 [3, 0, 7] = true := by decide +kernel
theorem sub5_587 : sub5 [3, 1, -6] = true := by decide +kernel
theorem sub5_588 : sub5 [3, 1, -5] = true := by decide +kernel
theorem sub5_589 : sub5 [3, 1, -4] = true := by decide +kernel
theorem sub5_590 : sub5 [3, 1, -3] = true := by decide +kernel
theorem sub5_591 : sub5 [3, 1, -2] = true := by decide +kernel
theorem sub5_592 : sub5 [3, 1, -1] = true := by decide +kernel
theorem sub5_593 : sub5 [3, 1, 0] = true := by decide +kernel
theorem sub5_594 : sub5 [3, 1, 1] = true := by decide +kernel
theorem sub5_595 : sub5 [3, 1, 2] = true := by decide +kernel
theorem sub5_596 : sub5 [3, 1, 3] = true := by decide +kernel
theorem sub5_597 : sub5 [3, 1, 4] = true := by decide +kernel
theorem sub5_598 : sub5 [3, 1, 5] = true := by decide +kernel
theorem sub5_599 : sub5 [3, 1, 6] = true := by decide +kernel
theorem sub5_600 : sub5 [3, 1, 7] = true := by decide +kernel
theorem sub5_601 : sub5 [3, 1, 8] = true := by decide +kernel
theorem sub5_602 : sub5 [3, 2] = true := by decide +kernel
theorem sub5_603 : sub5 [3, 3] = true := by decide +kernel
theorem sub5_604 : sub5 [3, 4] = true := by decide +kernel
theorem sub5_605 : sub5 [4, -3] = true := by decide +kernel
theorem sub5_606 : sub5 [4, -2] = true := by decide +kernel
theorem sub5_607 : sub5 [4, -1] = true := by decide +kernel
theorem sb5_18 : ∀ q ∈ blk5_18, sub5 q = true := by
  unfold blk5_18
  exact List.forall_mem_cons.2 ⟨sub5_576, List.forall_mem_cons.2 ⟨sub5_577, List.forall_mem_cons.2 ⟨sub5_578, List.forall_mem_cons.2 ⟨sub5_579, List.forall_mem_cons.2 ⟨sub5_580, List.forall_mem_cons.2 ⟨sub5_581, List.forall_mem_cons.2 ⟨sub5_582, List.forall_mem_cons.2 ⟨sub5_583, List.forall_mem_cons.2 ⟨sub5_584, List.forall_mem_cons.2 ⟨sub5_585, List.forall_mem_cons.2 ⟨sub5_586, List.forall_mem_cons.2 ⟨sub5_587, List.forall_mem_cons.2 ⟨sub5_588, List.forall_mem_cons.2 ⟨sub5_589, List.forall_mem_cons.2 ⟨sub5_590, List.forall_mem_cons.2 ⟨sub5_591, List.forall_mem_cons.2 ⟨sub5_592, List.forall_mem_cons.2 ⟨sub5_593, List.forall_mem_cons.2 ⟨sub5_594, List.forall_mem_cons.2 ⟨sub5_595, List.forall_mem_cons.2 ⟨sub5_596, List.forall_mem_cons.2 ⟨sub5_597, List.forall_mem_cons.2 ⟨sub5_598, List.forall_mem_cons.2 ⟨sub5_599, List.forall_mem_cons.2 ⟨sub5_600, List.forall_mem_cons.2 ⟨sub5_601, List.forall_mem_cons.2 ⟨sub5_602, List.forall_mem_cons.2 ⟨sub5_603, List.forall_mem_cons.2 ⟨sub5_604, List.forall_mem_cons.2 ⟨sub5_605, List.forall_mem_cons.2 ⟨sub5_606, List.forall_mem_cons.2 ⟨sub5_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_608 : sub5 [4, 0] = true := by decide +kernel
theorem sub5_609 : sub5 [4, 1] = true := by decide +kernel
theorem sub5_610 : sub5 [4, 2] = true := by decide +kernel
theorem sub5_611 : sub5 [4, 3] = true := by decide +kernel
theorem sub5_612 : sub5 [5] = true := by decide +kernel
theorem sb5_19 : ∀ q ∈ blk5_19, sub5 q = true := by
  unfold blk5_19
  exact List.forall_mem_cons.2 ⟨sub5_608, List.forall_mem_cons.2 ⟨sub5_609, List.forall_mem_cons.2 ⟨sub5_610, List.forall_mem_cons.2 ⟨sub5_611, List.forall_mem_cons.2 ⟨sub5_612, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-4] = true := by decide +kernel
theorem sub6_1 : sub6 [-3, -3] = true := by decide +kernel
theorem sub6_2 : sub6 [-3, -2] = true := by decide +kernel
theorem sub6_3 : sub6 [-3, -1, -8] = true := by decide +kernel
theorem sub6_4 : sub6 [-3, -1, -7] = true := by decide +kernel
theorem sub6_5 : sub6 [-3, -1, -6] = true := by decide +kernel
theorem sub6_6 : sub6 [-3, -1, -5] = true := by decide +kernel
theorem sub6_7 : sub6 [-3, -1, -4] = true := by decide +kernel
theorem sub6_8 : sub6 [-3, -1, -3] = true := by decide +kernel
theorem sub6_9 : sub6 [-3, -1, -2] = true := by decide +kernel
theorem sub6_10 : sub6 [-3, -1, -1] = true := by decide +kernel
theorem sub6_11 : sub6 [-3, -1, 0] = true := by decide +kernel
theorem sub6_12 : sub6 [-3, -1, 1] = true := by decide +kernel
theorem sub6_13 : sub6 [-3, -1, 2] = true := by decide +kernel
theorem sub6_14 : sub6 [-3, -1, 3] = true := by decide +kernel
theorem sub6_15 : sub6 [-3, -1, 4] = true := by decide +kernel
theorem sub6_16 : sub6 [-3, -1, 5] = true := by decide +kernel
theorem sub6_17 : sub6 [-3, -1, 6] = true := by decide +kernel
theorem sub6_18 : sub6 [-3, 0, -9] = true := by decide +kernel
theorem sub6_19 : sub6 [-3, 0, -8] = true := by decide +kernel
theorem sub6_20 : sub6 [-3, 0, -7] = true := by decide +kernel
theorem sub6_21 : sub6 [-3, 0, -6] = true := by decide +kernel
theorem sub6_22 : sub6 [-3, 0, -5] = true := by decide +kernel
theorem sub6_23 : sub6 [-3, 0, -4] = true := by decide +kernel
theorem sub6_24 : sub6 [-3, 0, -3] = true := by decide +kernel
theorem sub6_25 : sub6 [-3, 0, -2] = true := by decide +kernel
theorem sub6_26 : sub6 [-3, 0, -1] = true := by decide +kernel
theorem sub6_27 : sub6 [-3, 0, 0] = true := by decide +kernel
theorem sub6_28 : sub6 [-3, 0, 1] = true := by decide +kernel
theorem sub6_29 : sub6 [-3, 0, 2] = true := by decide +kernel
theorem sub6_30 : sub6 [-3, 0, 3] = true := by decide +kernel
theorem sub6_31 : sub6 [-3, 0, 4] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_32 : sub6 [-3, 0, 5] = true := by decide +kernel
theorem sub6_33 : sub6 [-3, 0, 6] = true := by decide +kernel
theorem sub6_34 : sub6 [-3, 1, -10] = true := by decide +kernel
theorem sub6_35 : sub6 [-3, 1, -9] = true := by decide +kernel
theorem sub6_36 : sub6 [-3, 1, -8] = true := by decide +kernel
theorem sub6_37 : sub6 [-3, 1, -7] = true := by decide +kernel
theorem sub6_38 : sub6 [-3, 1, -6] = true := by decide +kernel
theorem sub6_39 : sub6 [-3, 1, -5] = true := by decide +kernel
theorem sub6_40 : sub6 [-3, 1, -4] = true := by decide +kernel
theorem sub6_41 : sub6 [-3, 1, -3] = true := by decide +kernel
theorem sub6_42 : sub6 [-3, 1, -2] = true := by decide +kernel
theorem sub6_43 : sub6 [-3, 1, -1] = true := by decide +kernel
theorem sub6_44 : sub6 [-3, 1, 0] = true := by decide +kernel
theorem sub6_45 : sub6 [-3, 1, 1] = true := by decide +kernel
theorem sub6_46 : sub6 [-3, 1, 2] = true := by decide +kernel
theorem sub6_47 : sub6 [-3, 1, 3] = true := by decide +kernel
theorem sub6_48 : sub6 [-3, 1, 4] = true := by decide +kernel
theorem sub6_49 : sub6 [-3, 1, 5] = true := by decide +kernel
theorem sub6_50 : sub6 [-3, 1, 6] = true := by decide +kernel
theorem sub6_51 : sub6 [-3, 2, -10] = true := by decide +kernel
theorem sub6_52 : sub6 [-3, 2, -9] = true := by decide +kernel
theorem sub6_53 : sub6 [-3, 2, -8] = true := by decide +kernel
theorem sub6_54 : sub6 [-3, 2, -7] = true := by decide +kernel
theorem sub6_55 : sub6 [-3, 2, -6] = true := by decide +kernel
theorem sub6_56 : sub6 [-3, 2, -5] = true := by decide +kernel
theorem sub6_57 : sub6 [-3, 2, -4] = true := by decide +kernel
theorem sub6_58 : sub6 [-3, 2, -3] = true := by decide +kernel
theorem sub6_59 : sub6 [-3, 2, -2] = true := by decide +kernel
theorem sub6_60 : sub6 [-3, 2, -1] = true := by decide +kernel
theorem sub6_61 : sub6 [-3, 2, 0] = true := by decide +kernel
theorem sub6_62 : sub6 [-3, 2, 1] = true := by decide +kernel
theorem sub6_63 : sub6 [-3, 2, 2] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_cons.2 ⟨sub6_38, List.forall_mem_cons.2 ⟨sub6_39, List.forall_mem_cons.2 ⟨sub6_40, List.forall_mem_cons.2 ⟨sub6_41, List.forall_mem_cons.2 ⟨sub6_42, List.forall_mem_cons.2 ⟨sub6_43, List.forall_mem_cons.2 ⟨sub6_44, List.forall_mem_cons.2 ⟨sub6_45, List.forall_mem_cons.2 ⟨sub6_46, List.forall_mem_cons.2 ⟨sub6_47, List.forall_mem_cons.2 ⟨sub6_48, List.forall_mem_cons.2 ⟨sub6_49, List.forall_mem_cons.2 ⟨sub6_50, List.forall_mem_cons.2 ⟨sub6_51, List.forall_mem_cons.2 ⟨sub6_52, List.forall_mem_cons.2 ⟨sub6_53, List.forall_mem_cons.2 ⟨sub6_54, List.forall_mem_cons.2 ⟨sub6_55, List.forall_mem_cons.2 ⟨sub6_56, List.forall_mem_cons.2 ⟨sub6_57, List.forall_mem_cons.2 ⟨sub6_58, List.forall_mem_cons.2 ⟨sub6_59, List.forall_mem_cons.2 ⟨sub6_60, List.forall_mem_cons.2 ⟨sub6_61, List.forall_mem_cons.2 ⟨sub6_62, List.forall_mem_cons.2 ⟨sub6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_64 : sub6 [-3, 2, 3] = true := by decide +kernel
theorem sub6_65 : sub6 [-3, 2, 4] = true := by decide +kernel
theorem sub6_66 : sub6 [-3, 2, 5] = true := by decide +kernel
theorem sub6_67 : sub6 [-3, 3] = true := by decide +kernel
theorem sub6_68 : sub6 [-2, -4] = true := by decide +kernel
theorem sub6_69 : sub6 [-2, -3] = true := by decide +kernel
theorem sub6_70 : sub6 [-2, -2, -8] = true := by decide +kernel
theorem sub6_71 : sub6 [-2, -2, -7] = true := by decide +kernel
theorem sub6_72 : sub6 [-2, -2, -6] = true := by decide +kernel
theorem sub6_73 : sub6 [-2, -2, -5] = true := by decide +kernel
theorem sub6_74 : sub6 [-2, -2, -4] = true := by decide +kernel
theorem sub6_75 : sub6 [-2, -2, -3] = true := by decide +kernel
theorem sub6_76 : sub6 [-2, -2, -2] = true := by decide +kernel
theorem sub6_77 : sub6 [-2, -2, -1] = true := by decide +kernel
theorem sub6_78 : sub6 [-2, -2, 0] = true := by decide +kernel
theorem sub6_79 : sub6 [-2, -2, 1] = true := by decide +kernel
theorem sub6_80 : sub6 [-2, -2, 2] = true := by decide +kernel
theorem sub6_81 : sub6 [-2, -2, 3] = true := by decide +kernel
theorem sub6_82 : sub6 [-2, -2, 4] = true := by decide +kernel
theorem sub6_83 : sub6 [-2, -2, 5] = true := by decide +kernel
theorem sub6_84 : sub6 [-2, -2, 6] = true := by decide +kernel
theorem sub6_85 : sub6 [-2, -2, 7] = true := by decide +kernel
theorem sub6_86 : sub6 [-2, -2, 8] = true := by decide +kernel
theorem sub6_87 : sub6 [-2, -1, -10] = true := by decide +kernel
theorem sub6_88 : sub6 [-2, -1, -9] = true := by decide +kernel
theorem sub6_89 : sub6 [-2, -1, -8] = true := by decide +kernel
theorem sub6_90 : sub6 [-2, -1, -7] = true := by decide +kernel
theorem sub6_91 : sub6 [-2, -1, -6] = true := by decide +kernel
theorem sub6_92 : sub6 [-2, -1, -5] = true := by decide +kernel
theorem sub6_93 : sub6 [-2, -1, -4] = true := by decide +kernel
theorem sub6_94 : sub6 [-2, -1, -3] = true := by decide +kernel
theorem sub6_95 : sub6 [-2, -1, -2] = true := by decide +kernel
theorem sb6_2 : ∀ q ∈ blk6_2, sub6 q = true := by
  unfold blk6_2
  exact List.forall_mem_cons.2 ⟨sub6_64, List.forall_mem_cons.2 ⟨sub6_65, List.forall_mem_cons.2 ⟨sub6_66, List.forall_mem_cons.2 ⟨sub6_67, List.forall_mem_cons.2 ⟨sub6_68, List.forall_mem_cons.2 ⟨sub6_69, List.forall_mem_cons.2 ⟨sub6_70, List.forall_mem_cons.2 ⟨sub6_71, List.forall_mem_cons.2 ⟨sub6_72, List.forall_mem_cons.2 ⟨sub6_73, List.forall_mem_cons.2 ⟨sub6_74, List.forall_mem_cons.2 ⟨sub6_75, List.forall_mem_cons.2 ⟨sub6_76, List.forall_mem_cons.2 ⟨sub6_77, List.forall_mem_cons.2 ⟨sub6_78, List.forall_mem_cons.2 ⟨sub6_79, List.forall_mem_cons.2 ⟨sub6_80, List.forall_mem_cons.2 ⟨sub6_81, List.forall_mem_cons.2 ⟨sub6_82, List.forall_mem_cons.2 ⟨sub6_83, List.forall_mem_cons.2 ⟨sub6_84, List.forall_mem_cons.2 ⟨sub6_85, List.forall_mem_cons.2 ⟨sub6_86, List.forall_mem_cons.2 ⟨sub6_87, List.forall_mem_cons.2 ⟨sub6_88, List.forall_mem_cons.2 ⟨sub6_89, List.forall_mem_cons.2 ⟨sub6_90, List.forall_mem_cons.2 ⟨sub6_91, List.forall_mem_cons.2 ⟨sub6_92, List.forall_mem_cons.2 ⟨sub6_93, List.forall_mem_cons.2 ⟨sub6_94, List.forall_mem_cons.2 ⟨sub6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_96 : sub6 [-2, -1, -1] = true := by decide +kernel
theorem sub6_97 : sub6 [-2, -1, 0] = true := by decide +kernel
theorem sub6_98 : sub6 [-2, -1, 1] = true := by decide +kernel
theorem sub6_99 : sub6 [-2, -1, 2] = true := by decide +kernel
theorem sub6_100 : sub6 [-2, -1, 3] = true := by decide +kernel
theorem sub6_101 : sub6 [-2, -1, 4] = true := by decide +kernel
theorem sub6_102 : sub6 [-2, -1, 5] = true := by decide +kernel
theorem sub6_103 : sub6 [-2, -1, 6] = true := by decide +kernel
theorem sub6_104 : sub6 [-2, -1, 7] = true := by decide +kernel
theorem sub6_105 : sub6 [-2, -1, 8] = true := by decide +kernel
theorem sub6_106 : sub6 [-2, -1, 9] = true := by decide +kernel
theorem sub6_107 : sub6 [-2, 0, -11] = true := by decide +kernel
theorem sub6_108 : sub6 [-2, 0, -10] = true := by decide +kernel
theorem sub6_109 : sub6 [-2, 0, -9] = true := by decide +kernel
theorem sub6_110 : sub6 [-2, 0, -8] = true := by decide +kernel
theorem sub6_111 : sub6 [-2, 0, -7] = true := by decide +kernel
theorem sub6_112 : sub6 [-2, 0, -6] = true := by decide +kernel
theorem sub6_113 : sub6 [-2, 0, -5] = true := by decide +kernel
theorem sub6_114 : sub6 [-2, 0, -4] = true := by decide +kernel
theorem sub6_115 : sub6 [-2, 0, -3] = true := by decide +kernel
theorem sub6_116 : sub6 [-2, 0, -2] = true := by decide +kernel
theorem sub6_117 : sub6 [-2, 0, -1] = true := by decide +kernel
theorem sub6_118 : sub6 [-2, 0, 0] = true := by decide +kernel
theorem sub6_119 : sub6 [-2, 0, 1] = true := by decide +kernel
theorem sub6_120 : sub6 [-2, 0, 2] = true := by decide +kernel
theorem sub6_121 : sub6 [-2, 0, 3] = true := by decide +kernel
theorem sub6_122 : sub6 [-2, 0, 4] = true := by decide +kernel
theorem sub6_123 : sub6 [-2, 0, 5] = true := by decide +kernel
theorem sub6_124 : sub6 [-2, 0, 6] = true := by decide +kernel
theorem sub6_125 : sub6 [-2, 0, 7] = true := by decide +kernel
theorem sub6_126 : sub6 [-2, 0, 8] = true := by decide +kernel
theorem sub6_127 : sub6 [-2, 0, 9] = true := by decide +kernel
theorem sb6_3 : ∀ q ∈ blk6_3, sub6 q = true := by
  unfold blk6_3
  exact List.forall_mem_cons.2 ⟨sub6_96, List.forall_mem_cons.2 ⟨sub6_97, List.forall_mem_cons.2 ⟨sub6_98, List.forall_mem_cons.2 ⟨sub6_99, List.forall_mem_cons.2 ⟨sub6_100, List.forall_mem_cons.2 ⟨sub6_101, List.forall_mem_cons.2 ⟨sub6_102, List.forall_mem_cons.2 ⟨sub6_103, List.forall_mem_cons.2 ⟨sub6_104, List.forall_mem_cons.2 ⟨sub6_105, List.forall_mem_cons.2 ⟨sub6_106, List.forall_mem_cons.2 ⟨sub6_107, List.forall_mem_cons.2 ⟨sub6_108, List.forall_mem_cons.2 ⟨sub6_109, List.forall_mem_cons.2 ⟨sub6_110, List.forall_mem_cons.2 ⟨sub6_111, List.forall_mem_cons.2 ⟨sub6_112, List.forall_mem_cons.2 ⟨sub6_113, List.forall_mem_cons.2 ⟨sub6_114, List.forall_mem_cons.2 ⟨sub6_115, List.forall_mem_cons.2 ⟨sub6_116, List.forall_mem_cons.2 ⟨sub6_117, List.forall_mem_cons.2 ⟨sub6_118, List.forall_mem_cons.2 ⟨sub6_119, List.forall_mem_cons.2 ⟨sub6_120, List.forall_mem_cons.2 ⟨sub6_121, List.forall_mem_cons.2 ⟨sub6_122, List.forall_mem_cons.2 ⟨sub6_123, List.forall_mem_cons.2 ⟨sub6_124, List.forall_mem_cons.2 ⟨sub6_125, List.forall_mem_cons.2 ⟨sub6_126, List.forall_mem_cons.2 ⟨sub6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_128 : sub6 [-2, 1, -11] = true := by decide +kernel
theorem sub6_129 : sub6 [-2, 1, -10] = true := by decide +kernel
theorem sub6_130 : sub6 [-2, 1, -9] = true := by decide +kernel
theorem sub6_131 : sub6 [-2, 1, -8] = true := by decide +kernel
theorem sub6_132 : sub6 [-2, 1, -7] = true := by decide +kernel
theorem sub6_133 : sub6 [-2, 1, -6] = true := by decide +kernel
theorem sub6_134 : sub6 [-2, 1, -5] = true := by decide +kernel
theorem sub6_135 : sub6 [-2, 1, -4] = true := by decide +kernel
theorem sub6_136 : sub6 [-2, 1, -3] = true := by decide +kernel
theorem sub6_137 : sub6 [-2, 1, -2] = true := by decide +kernel
theorem sub6_138 : sub6 [-2, 1, -1] = true := by decide +kernel
theorem sub6_139 : sub6 [-2, 1, 0] = true := by decide +kernel
theorem sub6_140 : sub6 [-2, 1, 1] = true := by decide +kernel
theorem sub6_141 : sub6 [-2, 1, 2] = true := by decide +kernel
theorem sub6_142 : sub6 [-2, 1, 3] = true := by decide +kernel
theorem sub6_143 : sub6 [-2, 1, 4] = true := by decide +kernel
theorem sub6_144 : sub6 [-2, 1, 5] = true := by decide +kernel
theorem sub6_145 : sub6 [-2, 1, 6] = true := by decide +kernel
theorem sub6_146 : sub6 [-2, 1, 7] = true := by decide +kernel
theorem sub6_147 : sub6 [-2, 1, 8] = true := by decide +kernel
theorem sub6_148 : sub6 [-2, 2, -11] = true := by decide +kernel
theorem sub6_149 : sub6 [-2, 2, -10] = true := by decide +kernel
theorem sub6_150 : sub6 [-2, 2, -9] = true := by decide +kernel
theorem sub6_151 : sub6 [-2, 2, -8] = true := by decide +kernel
theorem sub6_152 : sub6 [-2, 2, -7] = true := by decide +kernel
theorem sub6_153 : sub6 [-2, 2, -6] = true := by decide +kernel
theorem sub6_154 : sub6 [-2, 2, -5] = true := by decide +kernel
theorem sub6_155 : sub6 [-2, 2, -4] = true := by decide +kernel
theorem sub6_156 : sub6 [-2, 2, -3] = true := by decide +kernel
theorem sub6_157 : sub6 [-2, 2, -2] = true := by decide +kernel
theorem sub6_158 : sub6 [-2, 2, -1] = true := by decide +kernel
theorem sub6_159 : sub6 [-2, 2, 0] = true := by decide +kernel
theorem sb6_4 : ∀ q ∈ blk6_4, sub6 q = true := by
  unfold blk6_4
  exact List.forall_mem_cons.2 ⟨sub6_128, List.forall_mem_cons.2 ⟨sub6_129, List.forall_mem_cons.2 ⟨sub6_130, List.forall_mem_cons.2 ⟨sub6_131, List.forall_mem_cons.2 ⟨sub6_132, List.forall_mem_cons.2 ⟨sub6_133, List.forall_mem_cons.2 ⟨sub6_134, List.forall_mem_cons.2 ⟨sub6_135, List.forall_mem_cons.2 ⟨sub6_136, List.forall_mem_cons.2 ⟨sub6_137, List.forall_mem_cons.2 ⟨sub6_138, List.forall_mem_cons.2 ⟨sub6_139, List.forall_mem_cons.2 ⟨sub6_140, List.forall_mem_cons.2 ⟨sub6_141, List.forall_mem_cons.2 ⟨sub6_142, List.forall_mem_cons.2 ⟨sub6_143, List.forall_mem_cons.2 ⟨sub6_144, List.forall_mem_cons.2 ⟨sub6_145, List.forall_mem_cons.2 ⟨sub6_146, List.forall_mem_cons.2 ⟨sub6_147, List.forall_mem_cons.2 ⟨sub6_148, List.forall_mem_cons.2 ⟨sub6_149, List.forall_mem_cons.2 ⟨sub6_150, List.forall_mem_cons.2 ⟨sub6_151, List.forall_mem_cons.2 ⟨sub6_152, List.forall_mem_cons.2 ⟨sub6_153, List.forall_mem_cons.2 ⟨sub6_154, List.forall_mem_cons.2 ⟨sub6_155, List.forall_mem_cons.2 ⟨sub6_156, List.forall_mem_cons.2 ⟨sub6_157, List.forall_mem_cons.2 ⟨sub6_158, List.forall_mem_cons.2 ⟨sub6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_160 : sub6 [-2, 2, 1] = true := by decide +kernel
theorem sub6_161 : sub6 [-2, 2, 2] = true := by decide +kernel
theorem sub6_162 : sub6 [-2, 2, 3] = true := by decide +kernel
theorem sub6_163 : sub6 [-2, 2, 4] = true := by decide +kernel
theorem sub6_164 : sub6 [-2, 2, 5] = true := by decide +kernel
theorem sub6_165 : sub6 [-2, 2, 6] = true := by decide +kernel
theorem sub6_166 : sub6 [-2, 2, 7] = true := by decide +kernel
theorem sub6_167 : sub6 [-2, 3, -10] = true := by decide +kernel
theorem sub6_168 : sub6 [-2, 3, -9] = true := by decide +kernel
theorem sub6_169 : sub6 [-2, 3, -8] = true := by decide +kernel
theorem sub6_170 : sub6 [-2, 3, -7] = true := by decide +kernel
theorem sub6_171 : sub6 [-2, 3, -6] = true := by decide +kernel
theorem sub6_172 : sub6 [-2, 3, -5] = true := by decide +kernel
theorem sub6_173 : sub6 [-2, 3, -4] = true := by decide +kernel
theorem sub6_174 : sub6 [-2, 3, -3] = true := by decide +kernel
theorem sub6_175 : sub6 [-2, 3, -2] = true := by decide +kernel
theorem sub6_176 : sub6 [-2, 3, -1] = true := by decide +kernel
theorem sub6_177 : sub6 [-2, 3, 0] = true := by decide +kernel
theorem sub6_178 : sub6 [-2, 3, 1] = true := by decide +kernel
theorem sub6_179 : sub6 [-2, 3, 2] = true := by decide +kernel
theorem sub6_180 : sub6 [-2, 3, 3] = true := by decide +kernel
theorem sub6_181 : sub6 [-2, 3, 4] = true := by decide +kernel
theorem sub6_182 : sub6 [-2, 3, 5] = true := by decide +kernel
theorem sub6_183 : sub6 [-2, 4] = true := by decide +kernel
theorem sub6_184 : sub6 [-1, -5] = true := by decide +kernel
theorem sub6_185 : sub6 [-1, -4] = true := by decide +kernel
theorem sub6_186 : sub6 [-1, -3, -7] = true := by decide +kernel
theorem sub6_187 : sub6 [-1, -3, -6] = true := by decide +kernel
theorem sub6_188 : sub6 [-1, -3, -5] = true := by decide +kernel
theorem sub6_189 : sub6 [-1, -3, -4] = true := by decide +kernel
theorem sub6_190 : sub6 [-1, -3, -3] = true := by decide +kernel
theorem sub6_191 : sub6 [-1, -3, -2] = true := by decide +kernel
theorem sb6_5 : ∀ q ∈ blk6_5, sub6 q = true := by
  unfold blk6_5
  exact List.forall_mem_cons.2 ⟨sub6_160, List.forall_mem_cons.2 ⟨sub6_161, List.forall_mem_cons.2 ⟨sub6_162, List.forall_mem_cons.2 ⟨sub6_163, List.forall_mem_cons.2 ⟨sub6_164, List.forall_mem_cons.2 ⟨sub6_165, List.forall_mem_cons.2 ⟨sub6_166, List.forall_mem_cons.2 ⟨sub6_167, List.forall_mem_cons.2 ⟨sub6_168, List.forall_mem_cons.2 ⟨sub6_169, List.forall_mem_cons.2 ⟨sub6_170, List.forall_mem_cons.2 ⟨sub6_171, List.forall_mem_cons.2 ⟨sub6_172, List.forall_mem_cons.2 ⟨sub6_173, List.forall_mem_cons.2 ⟨sub6_174, List.forall_mem_cons.2 ⟨sub6_175, List.forall_mem_cons.2 ⟨sub6_176, List.forall_mem_cons.2 ⟨sub6_177, List.forall_mem_cons.2 ⟨sub6_178, List.forall_mem_cons.2 ⟨sub6_179, List.forall_mem_cons.2 ⟨sub6_180, List.forall_mem_cons.2 ⟨sub6_181, List.forall_mem_cons.2 ⟨sub6_182, List.forall_mem_cons.2 ⟨sub6_183, List.forall_mem_cons.2 ⟨sub6_184, List.forall_mem_cons.2 ⟨sub6_185, List.forall_mem_cons.2 ⟨sub6_186, List.forall_mem_cons.2 ⟨sub6_187, List.forall_mem_cons.2 ⟨sub6_188, List.forall_mem_cons.2 ⟨sub6_189, List.forall_mem_cons.2 ⟨sub6_190, List.forall_mem_cons.2 ⟨sub6_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_192 : sub6 [-1, -3, -1] = true := by decide +kernel
theorem sub6_193 : sub6 [-1, -3, 0] = true := by decide +kernel
theorem sub6_194 : sub6 [-1, -3, 1] = true := by decide +kernel
theorem sub6_195 : sub6 [-1, -3, 2] = true := by decide +kernel
theorem sub6_196 : sub6 [-1, -3, 3] = true := by decide +kernel
theorem sub6_197 : sub6 [-1, -3, 4] = true := by decide +kernel
theorem sub6_198 : sub6 [-1, -3, 5] = true := by decide +kernel
theorem sub6_199 : sub6 [-1, -3, 6] = true := by decide +kernel
theorem sub6_200 : sub6 [-1, -3, 7] = true := by decide +kernel
theorem sub6_201 : sub6 [-1, -3, 8] = true := by decide +kernel
theorem sub6_202 : sub6 [-1, -2, -10] = true := by decide +kernel
theorem sub6_203 : sub6 [-1, -2, -9] = true := by decide +kernel
theorem sub6_204 : sub6 [-1, -2, -8] = true := by decide +kernel
theorem sub6_205 : sub6 [-1, -2, -7] = true := by decide +kernel
theorem sub6_206 : sub6 [-1, -2, -6] = true := by decide +kernel
theorem sub6_207 : sub6 [-1, -2, -5] = true := by decide +kernel
theorem sub6_208 : sub6 [-1, -2, -4] = true := by decide +kernel
theorem sub6_209 : sub6 [-1, -2, -3] = true := by decide +kernel
theorem sub6_210 : sub6 [-1, -2, -2] = true := by decide +kernel
theorem sub6_211 : sub6 [-1, -2, -1] = true := by decide +kernel
theorem sub6_212 : sub6 [-1, -2, 0] = true := by decide +kernel
theorem sub6_213 : sub6 [-1, -2, 1] = true := by decide +kernel
theorem sub6_214 : sub6 [-1, -2, 2] = true := by decide +kernel
theorem sub6_215 : sub6 [-1, -2, 3] = true := by decide +kernel
theorem sub6_216 : sub6 [-1, -2, 4] = true := by decide +kernel
theorem sub6_217 : sub6 [-1, -2, 5] = true := by decide +kernel
theorem sub6_218 : sub6 [-1, -2, 6] = true := by decide +kernel
theorem sub6_219 : sub6 [-1, -2, 7] = true := by decide +kernel
theorem sub6_220 : sub6 [-1, -2, 8] = true := by decide +kernel
theorem sub6_221 : sub6 [-1, -2, 9] = true := by decide +kernel
theorem sub6_222 : sub6 [-1, -2, 10] = true := by decide +kernel
theorem sub6_223 : sub6 [-1, -1, -11] = true := by decide +kernel
theorem sb6_6 : ∀ q ∈ blk6_6, sub6 q = true := by
  unfold blk6_6
  exact List.forall_mem_cons.2 ⟨sub6_192, List.forall_mem_cons.2 ⟨sub6_193, List.forall_mem_cons.2 ⟨sub6_194, List.forall_mem_cons.2 ⟨sub6_195, List.forall_mem_cons.2 ⟨sub6_196, List.forall_mem_cons.2 ⟨sub6_197, List.forall_mem_cons.2 ⟨sub6_198, List.forall_mem_cons.2 ⟨sub6_199, List.forall_mem_cons.2 ⟨sub6_200, List.forall_mem_cons.2 ⟨sub6_201, List.forall_mem_cons.2 ⟨sub6_202, List.forall_mem_cons.2 ⟨sub6_203, List.forall_mem_cons.2 ⟨sub6_204, List.forall_mem_cons.2 ⟨sub6_205, List.forall_mem_cons.2 ⟨sub6_206, List.forall_mem_cons.2 ⟨sub6_207, List.forall_mem_cons.2 ⟨sub6_208, List.forall_mem_cons.2 ⟨sub6_209, List.forall_mem_cons.2 ⟨sub6_210, List.forall_mem_cons.2 ⟨sub6_211, List.forall_mem_cons.2 ⟨sub6_212, List.forall_mem_cons.2 ⟨sub6_213, List.forall_mem_cons.2 ⟨sub6_214, List.forall_mem_cons.2 ⟨sub6_215, List.forall_mem_cons.2 ⟨sub6_216, List.forall_mem_cons.2 ⟨sub6_217, List.forall_mem_cons.2 ⟨sub6_218, List.forall_mem_cons.2 ⟨sub6_219, List.forall_mem_cons.2 ⟨sub6_220, List.forall_mem_cons.2 ⟨sub6_221, List.forall_mem_cons.2 ⟨sub6_222, List.forall_mem_cons.2 ⟨sub6_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_224 : sub6 [-1, -1, -10] = true := by decide +kernel
theorem sub6_225 : sub6 [-1, -1, -9] = true := by decide +kernel
theorem sub6_226 : sub6 [-1, -1, -8] = true := by decide +kernel
theorem sub6_227 : sub6 [-1, -1, -7] = true := by decide +kernel
theorem sub6_228 : sub6 [-1, -1, -6] = true := by decide +kernel
theorem sub6_229 : sub6 [-1, -1, -5] = true := by decide +kernel
theorem sub6_230 : sub6 [-1, -1, -4] = true := by decide +kernel
theorem sub6_231 : sub6 [-1, -1, -3] = true := by decide +kernel
theorem sub6_232 : sub6 [-1, -1, -2] = true := by decide +kernel
theorem sub6_233 : sub6 [-1, -1, -1] = true := by decide +kernel
theorem sub6_234 : sub6 [-1, -1, 0] = true := by decide +kernel
theorem sub6_235 : sub6 [-1, -1, 1] = true := by decide +kernel
theorem sub6_236 : sub6 [-1, -1, 2] = true := by decide +kernel
theorem sub6_237 : sub6 [-1, -1, 3] = true := by decide +kernel
theorem sub6_238 : sub6 [-1, -1, 4] = true := by decide +kernel
theorem sub6_239 : sub6 [-1, -1, 5] = true := by decide +kernel
theorem sub6_240 : sub6 [-1, -1, 6] = true := by decide +kernel
theorem sub6_241 : sub6 [-1, -1, 7] = true := by decide +kernel
theorem sub6_242 : sub6 [-1, -1, 8] = true := by decide +kernel
theorem sub6_243 : sub6 [-1, -1, 9] = true := by decide +kernel
theorem sub6_244 : sub6 [-1, -1, 10] = true := by decide +kernel
theorem sub6_245 : sub6 [-1, 0, -12] = true := by decide +kernel
theorem sub6_246 : sub6 [-1, 0, -11] = true := by decide +kernel
theorem sub6_247 : sub6 [-1, 0, -10] = true := by decide +kernel
theorem sub6_248 : sub6 [-1, 0, -9] = true := by decide +kernel
theorem sub6_249 : sub6 [-1, 0, -8] = true := by decide +kernel
theorem sub6_250 : sub6 [-1, 0, -7] = true := by decide +kernel
theorem sub6_251 : sub6 [-1, 0, -6] = true := by decide +kernel
theorem sub6_252 : sub6 [-1, 0, -5] = true := by decide +kernel
theorem sub6_253 : sub6 [-1, 0, -4] = true := by decide +kernel
theorem sub6_254 : sub6 [-1, 0, -3] = true := by decide +kernel
theorem sub6_255 : sub6 [-1, 0, -2] = true := by decide +kernel
theorem sb6_7 : ∀ q ∈ blk6_7, sub6 q = true := by
  unfold blk6_7
  exact List.forall_mem_cons.2 ⟨sub6_224, List.forall_mem_cons.2 ⟨sub6_225, List.forall_mem_cons.2 ⟨sub6_226, List.forall_mem_cons.2 ⟨sub6_227, List.forall_mem_cons.2 ⟨sub6_228, List.forall_mem_cons.2 ⟨sub6_229, List.forall_mem_cons.2 ⟨sub6_230, List.forall_mem_cons.2 ⟨sub6_231, List.forall_mem_cons.2 ⟨sub6_232, List.forall_mem_cons.2 ⟨sub6_233, List.forall_mem_cons.2 ⟨sub6_234, List.forall_mem_cons.2 ⟨sub6_235, List.forall_mem_cons.2 ⟨sub6_236, List.forall_mem_cons.2 ⟨sub6_237, List.forall_mem_cons.2 ⟨sub6_238, List.forall_mem_cons.2 ⟨sub6_239, List.forall_mem_cons.2 ⟨sub6_240, List.forall_mem_cons.2 ⟨sub6_241, List.forall_mem_cons.2 ⟨sub6_242, List.forall_mem_cons.2 ⟨sub6_243, List.forall_mem_cons.2 ⟨sub6_244, List.forall_mem_cons.2 ⟨sub6_245, List.forall_mem_cons.2 ⟨sub6_246, List.forall_mem_cons.2 ⟨sub6_247, List.forall_mem_cons.2 ⟨sub6_248, List.forall_mem_cons.2 ⟨sub6_249, List.forall_mem_cons.2 ⟨sub6_250, List.forall_mem_cons.2 ⟨sub6_251, List.forall_mem_cons.2 ⟨sub6_252, List.forall_mem_cons.2 ⟨sub6_253, List.forall_mem_cons.2 ⟨sub6_254, List.forall_mem_cons.2 ⟨sub6_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_256 : sub6 [-1, 0, -1] = true := by decide +kernel
theorem sub6_257 : sub6 [-1, 0, 0] = true := by decide +kernel
theorem sub6_258 : sub6 [-1, 0, 1] = true := by decide +kernel
theorem sub6_259 : sub6 [-1, 0, 2] = true := by decide +kernel
theorem sub6_260 : sub6 [-1, 0, 3] = true := by decide +kernel
theorem sub6_261 : sub6 [-1, 0, 4] = true := by decide +kernel
theorem sub6_262 : sub6 [-1, 0, 5] = true := by decide +kernel
theorem sub6_263 : sub6 [-1, 0, 6] = true := by decide +kernel
theorem sub6_264 : sub6 [-1, 0, 7] = true := by decide +kernel
theorem sub6_265 : sub6 [-1, 0, 8] = true := by decide +kernel
theorem sub6_266 : sub6 [-1, 0, 9] = true := by decide +kernel
theorem sub6_267 : sub6 [-1, 0, 10] = true := by decide +kernel
theorem sub6_268 : sub6 [-1, 1, -12] = true := by decide +kernel
theorem sub6_269 : sub6 [-1, 1, -11] = true := by decide +kernel
theorem sub6_270 : sub6 [-1, 1, -10] = true := by decide +kernel
theorem sub6_271 : sub6 [-1, 1, -9] = true := by decide +kernel
theorem sub6_272 : sub6 [-1, 1, -8] = true := by decide +kernel
theorem sub6_273 : sub6 [-1, 1, -7] = true := by decide +kernel
theorem sub6_274 : sub6 [-1, 1, -6] = true := by decide +kernel
theorem sub6_275 : sub6 [-1, 1, -5] = true := by decide +kernel
theorem sub6_276 : sub6 [-1, 1, -4] = true := by decide +kernel
theorem sub6_277 : sub6 [-1, 1, -3] = true := by decide +kernel
theorem sub6_278 : sub6 [-1, 1, -2] = true := by decide +kernel
theorem sub6_279 : sub6 [-1, 1, -1] = true := by decide +kernel
theorem sub6_280 : sub6 [-1, 1, 0] = true := by decide +kernel
theorem sub6_281 : sub6 [-1, 1, 1] = true := by decide +kernel
theorem sub6_282 : sub6 [-1, 1, 2] = true := by decide +kernel
theorem sub6_283 : sub6 [-1, 1, 3] = true := by decide +kernel
theorem sub6_284 : sub6 [-1, 1, 4] = true := by decide +kernel
theorem sub6_285 : sub6 [-1, 1, 5] = true := by decide +kernel
theorem sub6_286 : sub6 [-1, 1, 6] = true := by decide +kernel
theorem sub6_287 : sub6 [-1, 1, 7] = true := by decide +kernel
theorem sb6_8 : ∀ q ∈ blk6_8, sub6 q = true := by
  unfold blk6_8
  exact List.forall_mem_cons.2 ⟨sub6_256, List.forall_mem_cons.2 ⟨sub6_257, List.forall_mem_cons.2 ⟨sub6_258, List.forall_mem_cons.2 ⟨sub6_259, List.forall_mem_cons.2 ⟨sub6_260, List.forall_mem_cons.2 ⟨sub6_261, List.forall_mem_cons.2 ⟨sub6_262, List.forall_mem_cons.2 ⟨sub6_263, List.forall_mem_cons.2 ⟨sub6_264, List.forall_mem_cons.2 ⟨sub6_265, List.forall_mem_cons.2 ⟨sub6_266, List.forall_mem_cons.2 ⟨sub6_267, List.forall_mem_cons.2 ⟨sub6_268, List.forall_mem_cons.2 ⟨sub6_269, List.forall_mem_cons.2 ⟨sub6_270, List.forall_mem_cons.2 ⟨sub6_271, List.forall_mem_cons.2 ⟨sub6_272, List.forall_mem_cons.2 ⟨sub6_273, List.forall_mem_cons.2 ⟨sub6_274, List.forall_mem_cons.2 ⟨sub6_275, List.forall_mem_cons.2 ⟨sub6_276, List.forall_mem_cons.2 ⟨sub6_277, List.forall_mem_cons.2 ⟨sub6_278, List.forall_mem_cons.2 ⟨sub6_279, List.forall_mem_cons.2 ⟨sub6_280, List.forall_mem_cons.2 ⟨sub6_281, List.forall_mem_cons.2 ⟨sub6_282, List.forall_mem_cons.2 ⟨sub6_283, List.forall_mem_cons.2 ⟨sub6_284, List.forall_mem_cons.2 ⟨sub6_285, List.forall_mem_cons.2 ⟨sub6_286, List.forall_mem_cons.2 ⟨sub6_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_288 : sub6 [-1, 1, 8] = true := by decide +kernel
theorem sub6_289 : sub6 [-1, 1, 9] = true := by decide +kernel
theorem sub6_290 : sub6 [-1, 1, 10] = true := by decide +kernel
theorem sub6_291 : sub6 [-1, 2, -12] = true := by decide +kernel
theorem sub6_292 : sub6 [-1, 2, -11] = true := by decide +kernel
theorem sub6_293 : sub6 [-1, 2, -10] = true := by decide +kernel
theorem sub6_294 : sub6 [-1, 2, -9] = true := by decide +kernel
theorem sub6_295 : sub6 [-1, 2, -8] = true := by decide +kernel
theorem sub6_296 : sub6 [-1, 2, -7] = true := by decide +kernel
theorem sub6_297 : sub6 [-1, 2, -6] = true := by decide +kernel
theorem sub6_298 : sub6 [-1, 2, -5] = true := by decide +kernel
theorem sub6_299 : sub6 [-1, 2, -4] = true := by decide +kernel
theorem sub6_300 : sub6 [-1, 2, -3] = true := by decide +kernel
theorem sub6_301 : sub6 [-1, 2, -2] = true := by decide +kernel
theorem sub6_302 : sub6 [-1, 2, -1] = true := by decide +kernel
theorem sub6_303 : sub6 [-1, 2, 0] = true := by decide +kernel
theorem sub6_304 : sub6 [-1, 2, 1] = true := by decide +kernel
theorem sub6_305 : sub6 [-1, 2, 2] = true := by decide +kernel
theorem sub6_306 : sub6 [-1, 2, 3] = true := by decide +kernel
theorem sub6_307 : sub6 [-1, 2, 4] = true := by decide +kernel
theorem sub6_308 : sub6 [-1, 2, 5] = true := by decide +kernel
theorem sub6_309 : sub6 [-1, 2, 6] = true := by decide +kernel
theorem sub6_310 : sub6 [-1, 2, 7] = true := by decide +kernel
theorem sub6_311 : sub6 [-1, 2, 8] = true := by decide +kernel
theorem sub6_312 : sub6 [-1, 2, 9] = true := by decide +kernel
theorem sub6_313 : sub6 [-1, 3, -11] = true := by decide +kernel
theorem sub6_314 : sub6 [-1, 3, -10] = true := by decide +kernel
theorem sub6_315 : sub6 [-1, 3, -9] = true := by decide +kernel
theorem sub6_316 : sub6 [-1, 3, -8] = true := by decide +kernel
theorem sub6_317 : sub6 [-1, 3, -7] = true := by decide +kernel
theorem sub6_318 : sub6 [-1, 3, -6] = true := by decide +kernel
theorem sub6_319 : sub6 [-1, 3, -5] = true := by decide +kernel
theorem sb6_9 : ∀ q ∈ blk6_9, sub6 q = true := by
  unfold blk6_9
  exact List.forall_mem_cons.2 ⟨sub6_288, List.forall_mem_cons.2 ⟨sub6_289, List.forall_mem_cons.2 ⟨sub6_290, List.forall_mem_cons.2 ⟨sub6_291, List.forall_mem_cons.2 ⟨sub6_292, List.forall_mem_cons.2 ⟨sub6_293, List.forall_mem_cons.2 ⟨sub6_294, List.forall_mem_cons.2 ⟨sub6_295, List.forall_mem_cons.2 ⟨sub6_296, List.forall_mem_cons.2 ⟨sub6_297, List.forall_mem_cons.2 ⟨sub6_298, List.forall_mem_cons.2 ⟨sub6_299, List.forall_mem_cons.2 ⟨sub6_300, List.forall_mem_cons.2 ⟨sub6_301, List.forall_mem_cons.2 ⟨sub6_302, List.forall_mem_cons.2 ⟨sub6_303, List.forall_mem_cons.2 ⟨sub6_304, List.forall_mem_cons.2 ⟨sub6_305, List.forall_mem_cons.2 ⟨sub6_306, List.forall_mem_cons.2 ⟨sub6_307, List.forall_mem_cons.2 ⟨sub6_308, List.forall_mem_cons.2 ⟨sub6_309, List.forall_mem_cons.2 ⟨sub6_310, List.forall_mem_cons.2 ⟨sub6_311, List.forall_mem_cons.2 ⟨sub6_312, List.forall_mem_cons.2 ⟨sub6_313, List.forall_mem_cons.2 ⟨sub6_314, List.forall_mem_cons.2 ⟨sub6_315, List.forall_mem_cons.2 ⟨sub6_316, List.forall_mem_cons.2 ⟨sub6_317, List.forall_mem_cons.2 ⟨sub6_318, List.forall_mem_cons.2 ⟨sub6_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C102
