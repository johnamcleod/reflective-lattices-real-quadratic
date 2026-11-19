import ReflectZphi.Data.Cert5.C105.Base

namespace ReflectZphi.Data.Cert5.C105
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub10_544 : sub10 [3, -1, -7] = true := by decide +kernel
theorem sub10_545 : sub10 [3, -1, -6] = true := by decide +kernel
theorem sub10_546 : sub10 [3, -1, -5] = true := by decide +kernel
theorem sub10_547 : sub10 [3, -1, -4] = true := by decide +kernel
theorem sub10_548 : sub10 [3, -1, -3] = true := by decide +kernel
theorem sub10_549 : sub10 [3, -1, -2] = true := by decide +kernel
theorem sub10_550 : sub10 [3, -1, -1] = true := by decide +kernel
theorem sub10_551 : sub10 [3, -1, 0] = true := by decide +kernel
theorem sub10_552 : sub10 [3, -1, 1] = true := by decide +kernel
theorem sub10_553 : sub10 [3, -1, 2] = true := by decide +kernel
theorem sub10_554 : sub10 [3, -1, 3] = true := by decide +kernel
theorem sub10_555 : sub10 [3, -1, 4] = true := by decide +kernel
theorem sub10_556 : sub10 [3, -1, 5] = true := by decide +kernel
theorem sub10_557 : sub10 [3, 0, -7] = true := by decide +kernel
theorem sub10_558 : sub10 [3, 0, -6] = true := by decide +kernel
theorem sub10_559 : sub10 [3, 0, -5] = true := by decide +kernel
theorem sub10_560 : sub10 [3, 0, -4] = true := by decide +kernel
theorem sub10_561 : sub10 [3, 0, -3] = true := by decide +kernel
theorem sub10_562 : sub10 [3, 0, -2] = true := by decide +kernel
theorem sub10_563 : sub10 [3, 0, -1] = true := by decide +kernel
theorem sub10_564 : sub10 [3, 0, 0] = true := by decide +kernel
theorem sub10_565 : sub10 [3, 0, 1] = true := by decide +kernel
theorem sub10_566 : sub10 [3, 0, 2] = true := by decide +kernel
theorem sub10_567 : sub10 [3, 0, 3] = true := by decide +kernel
theorem sub10_568 : sub10 [3, 0, 4] = true := by decide +kernel
theorem sub10_569 : sub10 [3, 0, 5] = true := by decide +kernel
theorem sub10_570 : sub10 [3, 0, 6] = true := by decide +kernel
theorem sub10_571 : sub10 [3, 1, -7] = true := by decide +kernel
theorem sub10_572 : sub10 [3, 1, -6] = true := by decide +kernel
theorem sub10_573 : sub10 [3, 1, -5] = true := by decide +kernel
theorem sub10_574 : sub10 [3, 1, -4] = true := by decide +kernel
theorem sub10_575 : sub10 [3, 1, -3] = true := by decide +kernel
theorem sb10_17 : ∀ q ∈ blk10_17, sub10 q = true := by
  unfold blk10_17
  exact List.forall_mem_cons.2 ⟨sub10_544, List.forall_mem_cons.2 ⟨sub10_545, List.forall_mem_cons.2 ⟨sub10_546, List.forall_mem_cons.2 ⟨sub10_547, List.forall_mem_cons.2 ⟨sub10_548, List.forall_mem_cons.2 ⟨sub10_549, List.forall_mem_cons.2 ⟨sub10_550, List.forall_mem_cons.2 ⟨sub10_551, List.forall_mem_cons.2 ⟨sub10_552, List.forall_mem_cons.2 ⟨sub10_553, List.forall_mem_cons.2 ⟨sub10_554, List.forall_mem_cons.2 ⟨sub10_555, List.forall_mem_cons.2 ⟨sub10_556, List.forall_mem_cons.2 ⟨sub10_557, List.forall_mem_cons.2 ⟨sub10_558, List.forall_mem_cons.2 ⟨sub10_559, List.forall_mem_cons.2 ⟨sub10_560, List.forall_mem_cons.2 ⟨sub10_561, List.forall_mem_cons.2 ⟨sub10_562, List.forall_mem_cons.2 ⟨sub10_563, List.forall_mem_cons.2 ⟨sub10_564, List.forall_mem_cons.2 ⟨sub10_565, List.forall_mem_cons.2 ⟨sub10_566, List.forall_mem_cons.2 ⟨sub10_567, List.forall_mem_cons.2 ⟨sub10_568, List.forall_mem_cons.2 ⟨sub10_569, List.forall_mem_cons.2 ⟨sub10_570, List.forall_mem_cons.2 ⟨sub10_571, List.forall_mem_cons.2 ⟨sub10_572, List.forall_mem_cons.2 ⟨sub10_573, List.forall_mem_cons.2 ⟨sub10_574, List.forall_mem_cons.2 ⟨sub10_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_576 : sub10 [3, 1, -2] = true := by decide +kernel
theorem sub10_577 : sub10 [3, 1, -1] = true := by decide +kernel
theorem sub10_578 : sub10 [3, 1, 0] = true := by decide +kernel
theorem sub10_579 : sub10 [3, 1, 1] = true := by decide +kernel
theorem sub10_580 : sub10 [3, 1, 2] = true := by decide +kernel
theorem sub10_581 : sub10 [3, 1, 3] = true := by decide +kernel
theorem sub10_582 : sub10 [3, 1, 4] = true := by decide +kernel
theorem sub10_583 : sub10 [3, 1, 5] = true := by decide +kernel
theorem sub10_584 : sub10 [3, 1, 6] = true := by decide +kernel
theorem sub10_585 : sub10 [3, 2, -7] = true := by decide +kernel
theorem sub10_586 : sub10 [3, 2, -6] = true := by decide +kernel
theorem sub10_587 : sub10 [3, 2, -5] = true := by decide +kernel
theorem sub10_588 : sub10 [3, 2, -4] = true := by decide +kernel
theorem sub10_589 : sub10 [3, 2, -3] = true := by decide +kernel
theorem sub10_590 : sub10 [3, 2, -2] = true := by decide +kernel
theorem sub10_591 : sub10 [3, 2, -1] = true := by decide +kernel
theorem sub10_592 : sub10 [3, 2, 0] = true := by decide +kernel
theorem sub10_593 : sub10 [3, 2, 1] = true := by decide +kernel
theorem sub10_594 : sub10 [3, 2, 2] = true := by decide +kernel
theorem sub10_595 : sub10 [3, 2, 3] = true := by decide +kernel
theorem sub10_596 : sub10 [3, 2, 4] = true := by decide +kernel
theorem sub10_597 : sub10 [3, 2, 5] = true := by decide +kernel
theorem sub10_598 : sub10 [3, 2, 6] = true := by decide +kernel
theorem sub10_599 : sub10 [3, 3] = true := by decide +kernel
theorem sub10_600 : sub10 [3, 4] = true := by decide +kernel
theorem sub10_601 : sub10 [3, 5] = true := by decide +kernel
theorem sub10_602 : sub10 [4, -4] = true := by decide +kernel
theorem sub10_603 : sub10 [4, -3] = true := by decide +kernel
theorem sub10_604 : sub10 [4, -2] = true := by decide +kernel
theorem sub10_605 : sub10 [4, -1] = true := by decide +kernel
theorem sub10_606 : sub10 [4, 0] = true := by decide +kernel
theorem sub10_607 : sub10 [4, 1] = true := by decide +kernel
theorem sb10_18 : ∀ q ∈ blk10_18, sub10 q = true := by
  unfold blk10_18
  exact List.forall_mem_cons.2 ⟨sub10_576, List.forall_mem_cons.2 ⟨sub10_577, List.forall_mem_cons.2 ⟨sub10_578, List.forall_mem_cons.2 ⟨sub10_579, List.forall_mem_cons.2 ⟨sub10_580, List.forall_mem_cons.2 ⟨sub10_581, List.forall_mem_cons.2 ⟨sub10_582, List.forall_mem_cons.2 ⟨sub10_583, List.forall_mem_cons.2 ⟨sub10_584, List.forall_mem_cons.2 ⟨sub10_585, List.forall_mem_cons.2 ⟨sub10_586, List.forall_mem_cons.2 ⟨sub10_587, List.forall_mem_cons.2 ⟨sub10_588, List.forall_mem_cons.2 ⟨sub10_589, List.forall_mem_cons.2 ⟨sub10_590, List.forall_mem_cons.2 ⟨sub10_591, List.forall_mem_cons.2 ⟨sub10_592, List.forall_mem_cons.2 ⟨sub10_593, List.forall_mem_cons.2 ⟨sub10_594, List.forall_mem_cons.2 ⟨sub10_595, List.forall_mem_cons.2 ⟨sub10_596, List.forall_mem_cons.2 ⟨sub10_597, List.forall_mem_cons.2 ⟨sub10_598, List.forall_mem_cons.2 ⟨sub10_599, List.forall_mem_cons.2 ⟨sub10_600, List.forall_mem_cons.2 ⟨sub10_601, List.forall_mem_cons.2 ⟨sub10_602, List.forall_mem_cons.2 ⟨sub10_603, List.forall_mem_cons.2 ⟨sub10_604, List.forall_mem_cons.2 ⟨sub10_605, List.forall_mem_cons.2 ⟨sub10_606, List.forall_mem_cons.2 ⟨sub10_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_608 : sub10 [4, 2] = true := by decide +kernel
theorem sub10_609 : sub10 [4, 3] = true := by decide +kernel
theorem sub10_610 : sub10 [4, 4] = true := by decide +kernel
theorem sub10_611 : sub10 [4, 5] = true := by decide +kernel
theorem sub10_612 : sub10 [5, -3] = true := by decide +kernel
theorem sub10_613 : sub10 [5, -2] = true := by decide +kernel
theorem sub10_614 : sub10 [5, -1] = true := by decide +kernel
theorem sub10_615 : sub10 [5, 0] = true := by decide +kernel
theorem sub10_616 : sub10 [5, 1] = true := by decide +kernel
theorem sub10_617 : sub10 [5, 2] = true := by decide +kernel
theorem sub10_618 : sub10 [5, 3] = true := by decide +kernel
theorem sub10_619 : sub10 [5, 4] = true := by decide +kernel
theorem sub10_620 : sub10 [6] = true := by decide +kernel
theorem sb10_19 : ∀ q ∈ blk10_19, sub10 q = true := by
  unfold blk10_19
  exact List.forall_mem_cons.2 ⟨sub10_608, List.forall_mem_cons.2 ⟨sub10_609, List.forall_mem_cons.2 ⟨sub10_610, List.forall_mem_cons.2 ⟨sub10_611, List.forall_mem_cons.2 ⟨sub10_612, List.forall_mem_cons.2 ⟨sub10_613, List.forall_mem_cons.2 ⟨sub10_614, List.forall_mem_cons.2 ⟨sub10_615, List.forall_mem_cons.2 ⟨sub10_616, List.forall_mem_cons.2 ⟨sub10_617, List.forall_mem_cons.2 ⟨sub10_618, List.forall_mem_cons.2 ⟨sub10_619, List.forall_mem_cons.2 ⟨sub10_620, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_0 : sub11 [-5] = true := by decide +kernel
theorem sub11_1 : sub11 [-4, -6] = true := by decide +kernel
theorem sub11_2 : sub11 [-4, -5] = true := by decide +kernel
theorem sub11_3 : sub11 [-4, -4] = true := by decide +kernel
theorem sub11_4 : sub11 [-4, -3] = true := by decide +kernel
theorem sub11_5 : sub11 [-4, -2] = true := by decide +kernel
theorem sub11_6 : sub11 [-4, -1] = true := by decide +kernel
theorem sub11_7 : sub11 [-4, 0] = true := by decide +kernel
theorem sub11_8 : sub11 [-4, 1] = true := by decide +kernel
theorem sub11_9 : sub11 [-3, -7] = true := by decide +kernel
theorem sub11_10 : sub11 [-3, -6] = true := by decide +kernel
theorem sub11_11 : sub11 [-3, -5] = true := by decide +kernel
theorem sub11_12 : sub11 [-3, -4] = true := by decide +kernel
theorem sub11_13 : sub11 [-3, -3] = true := by decide +kernel
theorem sub11_14 : sub11 [-3, -2] = true := by decide +kernel
theorem sub11_15 : sub11 [-3, -1] = true := by decide +kernel
theorem sub11_16 : sub11 [-3, 0] = true := by decide +kernel
theorem sub11_17 : sub11 [-3, 1] = true := by decide +kernel
theorem sub11_18 : sub11 [-3, 2] = true := by decide +kernel
theorem sub11_19 : sub11 [-3, 3] = true := by decide +kernel
theorem sub11_20 : sub11 [-2, -7] = true := by decide +kernel
theorem sub11_21 : sub11 [-2, -6] = true := by decide +kernel
theorem sub11_22 : sub11 [-2, -5] = true := by decide +kernel
theorem sub11_23 : sub11 [-2, -4] = true := by decide +kernel
theorem sub11_24 : sub11 [-2, -3] = true := by decide +kernel
theorem sub11_25 : sub11 [-2, -2] = true := by decide +kernel
theorem sub11_26 : sub11 [-2, -1] = true := by decide +kernel
theorem sub11_27 : sub11 [-2, 0] = true := by decide +kernel
theorem sub11_28 : sub11 [-2, 1] = true := by decide +kernel
theorem sub11_29 : sub11 [-2, 2] = true := by decide +kernel
theorem sub11_30 : sub11 [-2, 3] = true := by decide +kernel
theorem sub11_31 : sub11 [-2, 4] = true := by decide +kernel
theorem sb11_0 : ∀ q ∈ blk11_0, sub11 q = true := by
  unfold blk11_0
  exact List.forall_mem_cons.2 ⟨sub11_0, List.forall_mem_cons.2 ⟨sub11_1, List.forall_mem_cons.2 ⟨sub11_2, List.forall_mem_cons.2 ⟨sub11_3, List.forall_mem_cons.2 ⟨sub11_4, List.forall_mem_cons.2 ⟨sub11_5, List.forall_mem_cons.2 ⟨sub11_6, List.forall_mem_cons.2 ⟨sub11_7, List.forall_mem_cons.2 ⟨sub11_8, List.forall_mem_cons.2 ⟨sub11_9, List.forall_mem_cons.2 ⟨sub11_10, List.forall_mem_cons.2 ⟨sub11_11, List.forall_mem_cons.2 ⟨sub11_12, List.forall_mem_cons.2 ⟨sub11_13, List.forall_mem_cons.2 ⟨sub11_14, List.forall_mem_cons.2 ⟨sub11_15, List.forall_mem_cons.2 ⟨sub11_16, List.forall_mem_cons.2 ⟨sub11_17, List.forall_mem_cons.2 ⟨sub11_18, List.forall_mem_cons.2 ⟨sub11_19, List.forall_mem_cons.2 ⟨sub11_20, List.forall_mem_cons.2 ⟨sub11_21, List.forall_mem_cons.2 ⟨sub11_22, List.forall_mem_cons.2 ⟨sub11_23, List.forall_mem_cons.2 ⟨sub11_24, List.forall_mem_cons.2 ⟨sub11_25, List.forall_mem_cons.2 ⟨sub11_26, List.forall_mem_cons.2 ⟨sub11_27, List.forall_mem_cons.2 ⟨sub11_28, List.forall_mem_cons.2 ⟨sub11_29, List.forall_mem_cons.2 ⟨sub11_30, List.forall_mem_cons.2 ⟨sub11_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_32 : sub11 [-1, -7] = true := by decide +kernel
theorem sub11_33 : sub11 [-1, -6] = true := by decide +kernel
theorem sub11_34 : sub11 [-1, -5] = true := by decide +kernel
theorem sub11_35 : sub11 [-1, -4] = true := by decide +kernel
theorem sub11_36 : sub11 [-1, -3] = true := by decide +kernel
theorem sub11_37 : sub11 [-1, -2] = true := by decide +kernel
theorem sub11_38 : sub11 [-1, -1] = true := by decide +kernel
theorem sub11_39 : sub11 [-1, 0] = true := by decide +kernel
theorem sub11_40 : sub11 [-1, 1] = true := by decide +kernel
theorem sub11_41 : sub11 [-1, 2] = true := by decide +kernel
theorem sub11_42 : sub11 [-1, 3] = true := by decide +kernel
theorem sub11_43 : sub11 [-1, 4] = true := by decide +kernel
theorem sub11_44 : sub11 [-1, 5] = true := by decide +kernel
theorem sub11_45 : sub11 [0, -6] = true := by decide +kernel
theorem sub11_46 : sub11 [0, -5] = true := by decide +kernel
theorem sub11_47 : sub11 [0, -4] = true := by decide +kernel
theorem sub11_48 : sub11 [0, -3] = true := by decide +kernel
theorem sub11_49 : sub11 [0, -2] = true := by decide +kernel
theorem sub11_50 : sub11 [0, -1] = true := by decide +kernel
theorem sub11_51 : sub11 [0, 0] = true := by decide +kernel
theorem sub11_52 : sub11 [0, 1] = true := by decide +kernel
theorem sub11_53 : sub11 [0, 2] = true := by decide +kernel
theorem sub11_54 : sub11 [0, 3] = true := by decide +kernel
theorem sub11_55 : sub11 [0, 4] = true := by decide +kernel
theorem sub11_56 : sub11 [0, 5] = true := by decide +kernel
theorem sub11_57 : sub11 [1, -6] = true := by decide +kernel
theorem sub11_58 : sub11 [1, -5] = true := by decide +kernel
theorem sub11_59 : sub11 [1, -4] = true := by decide +kernel
theorem sub11_60 : sub11 [1, -3] = true := by decide +kernel
theorem sub11_61 : sub11 [1, -2] = true := by decide +kernel
theorem sub11_62 : sub11 [1, -1] = true := by decide +kernel
theorem sub11_63 : sub11 [1, 0] = true := by decide +kernel
theorem sb11_1 : ∀ q ∈ blk11_1, sub11 q = true := by
  unfold blk11_1
  exact List.forall_mem_cons.2 ⟨sub11_32, List.forall_mem_cons.2 ⟨sub11_33, List.forall_mem_cons.2 ⟨sub11_34, List.forall_mem_cons.2 ⟨sub11_35, List.forall_mem_cons.2 ⟨sub11_36, List.forall_mem_cons.2 ⟨sub11_37, List.forall_mem_cons.2 ⟨sub11_38, List.forall_mem_cons.2 ⟨sub11_39, List.forall_mem_cons.2 ⟨sub11_40, List.forall_mem_cons.2 ⟨sub11_41, List.forall_mem_cons.2 ⟨sub11_42, List.forall_mem_cons.2 ⟨sub11_43, List.forall_mem_cons.2 ⟨sub11_44, List.forall_mem_cons.2 ⟨sub11_45, List.forall_mem_cons.2 ⟨sub11_46, List.forall_mem_cons.2 ⟨sub11_47, List.forall_mem_cons.2 ⟨sub11_48, List.forall_mem_cons.2 ⟨sub11_49, List.forall_mem_cons.2 ⟨sub11_50, List.forall_mem_cons.2 ⟨sub11_51, List.forall_mem_cons.2 ⟨sub11_52, List.forall_mem_cons.2 ⟨sub11_53, List.forall_mem_cons.2 ⟨sub11_54, List.forall_mem_cons.2 ⟨sub11_55, List.forall_mem_cons.2 ⟨sub11_56, List.forall_mem_cons.2 ⟨sub11_57, List.forall_mem_cons.2 ⟨sub11_58, List.forall_mem_cons.2 ⟨sub11_59, List.forall_mem_cons.2 ⟨sub11_60, List.forall_mem_cons.2 ⟨sub11_61, List.forall_mem_cons.2 ⟨sub11_62, List.forall_mem_cons.2 ⟨sub11_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_64 : sub11 [1, 1] = true := by decide +kernel
theorem sub11_65 : sub11 [1, 2] = true := by decide +kernel
theorem sub11_66 : sub11 [1, 3] = true := by decide +kernel
theorem sub11_67 : sub11 [1, 4] = true := by decide +kernel
theorem sub11_68 : sub11 [1, 5] = true := by decide +kernel
theorem sub11_69 : sub11 [1, 6] = true := by decide +kernel
theorem sub11_70 : sub11 [2, -5] = true := by decide +kernel
theorem sub11_71 : sub11 [2, -4] = true := by decide +kernel
theorem sub11_72 : sub11 [2, -3] = true := by decide +kernel
theorem sub11_73 : sub11 [2, -2] = true := by decide +kernel
theorem sub11_74 : sub11 [2, -1] = true := by decide +kernel
theorem sub11_75 : sub11 [2, 0] = true := by decide +kernel
theorem sub11_76 : sub11 [2, 1] = true := by decide +kernel
theorem sub11_77 : sub11 [2, 2] = true := by decide +kernel
theorem sub11_78 : sub11 [2, 3] = true := by decide +kernel
theorem sub11_79 : sub11 [2, 4] = true := by decide +kernel
theorem sub11_80 : sub11 [2, 5] = true := by decide +kernel
theorem sub11_81 : sub11 [2, 6] = true := by decide +kernel
theorem sub11_82 : sub11 [3, -4] = true := by decide +kernel
theorem sub11_83 : sub11 [3, -3] = true := by decide +kernel
theorem sub11_84 : sub11 [3, -2] = true := by decide +kernel
theorem sub11_85 : sub11 [3, -1] = true := by decide +kernel
theorem sub11_86 : sub11 [3, 0] = true := by decide +kernel
theorem sub11_87 : sub11 [3, 1] = true := by decide +kernel
theorem sub11_88 : sub11 [3, 2] = true := by decide +kernel
theorem sub11_89 : sub11 [3, 3] = true := by decide +kernel
theorem sub11_90 : sub11 [3, 4] = true := by decide +kernel
theorem sub11_91 : sub11 [3, 5] = true := by decide +kernel
theorem sub11_92 : sub11 [3, 6] = true := by decide +kernel
theorem sub11_93 : sub11 [4, -2] = true := by decide +kernel
theorem sub11_94 : sub11 [4, -1] = true := by decide +kernel
theorem sub11_95 : sub11 [4, 0] = true := by decide +kernel
theorem sb11_2 : ∀ q ∈ blk11_2, sub11 q = true := by
  unfold blk11_2
  exact List.forall_mem_cons.2 ⟨sub11_64, List.forall_mem_cons.2 ⟨sub11_65, List.forall_mem_cons.2 ⟨sub11_66, List.forall_mem_cons.2 ⟨sub11_67, List.forall_mem_cons.2 ⟨sub11_68, List.forall_mem_cons.2 ⟨sub11_69, List.forall_mem_cons.2 ⟨sub11_70, List.forall_mem_cons.2 ⟨sub11_71, List.forall_mem_cons.2 ⟨sub11_72, List.forall_mem_cons.2 ⟨sub11_73, List.forall_mem_cons.2 ⟨sub11_74, List.forall_mem_cons.2 ⟨sub11_75, List.forall_mem_cons.2 ⟨sub11_76, List.forall_mem_cons.2 ⟨sub11_77, List.forall_mem_cons.2 ⟨sub11_78, List.forall_mem_cons.2 ⟨sub11_79, List.forall_mem_cons.2 ⟨sub11_80, List.forall_mem_cons.2 ⟨sub11_81, List.forall_mem_cons.2 ⟨sub11_82, List.forall_mem_cons.2 ⟨sub11_83, List.forall_mem_cons.2 ⟨sub11_84, List.forall_mem_cons.2 ⟨sub11_85, List.forall_mem_cons.2 ⟨sub11_86, List.forall_mem_cons.2 ⟨sub11_87, List.forall_mem_cons.2 ⟨sub11_88, List.forall_mem_cons.2 ⟨sub11_89, List.forall_mem_cons.2 ⟨sub11_90, List.forall_mem_cons.2 ⟨sub11_91, List.forall_mem_cons.2 ⟨sub11_92, List.forall_mem_cons.2 ⟨sub11_93, List.forall_mem_cons.2 ⟨sub11_94, List.forall_mem_cons.2 ⟨sub11_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_96 : sub11 [4, 1] = true := by decide +kernel
theorem sub11_97 : sub11 [4, 2] = true := by decide +kernel
theorem sub11_98 : sub11 [4, 3] = true := by decide +kernel
theorem sub11_99 : sub11 [4, 4] = true := by decide +kernel
theorem sub11_100 : sub11 [4, 5] = true := by decide +kernel
theorem sub11_101 : sub11 [5] = true := by decide +kernel
theorem sb11_3 : ∀ q ∈ blk11_3, sub11 q = true := by
  unfold blk11_3
  exact List.forall_mem_cons.2 ⟨sub11_96, List.forall_mem_cons.2 ⟨sub11_97, List.forall_mem_cons.2 ⟨sub11_98, List.forall_mem_cons.2 ⟨sub11_99, List.forall_mem_cons.2 ⟨sub11_100, List.forall_mem_cons.2 ⟨sub11_101, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C105
