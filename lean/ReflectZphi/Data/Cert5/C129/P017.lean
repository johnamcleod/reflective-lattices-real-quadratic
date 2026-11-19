import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_2_576 : subd7_2 [2, 2, -6] = true := by decide +kernel
theorem subd7_2_577 : subd7_2 [2, 2, -5] = true := by decide +kernel
theorem subd7_2_578 : subd7_2 [2, 2, -4] = true := by decide +kernel
theorem subd7_2_579 : subd7_2 [2, 2, -3] = true := by decide +kernel
theorem subd7_2_580 : subd7_2 [2, 2, -2] = true := by decide +kernel
theorem subd7_2_581 : subd7_2 [2, 2, -1] = true := by decide +kernel
theorem subd7_2_582 : subd7_2 [2, 2, 0] = true := by decide +kernel
theorem subd7_2_583 : subd7_2 [2, 2, 1] = true := by decide +kernel
theorem subd7_2_584 : subd7_2 [2, 2, 2] = true := by decide +kernel
theorem subd7_2_585 : subd7_2 [2, 2, 3] = true := by decide +kernel
theorem subd7_2_586 : subd7_2 [2, 2, 4] = true := by decide +kernel
theorem subd7_2_587 : subd7_2 [2, 2, 5] = true := by decide +kernel
theorem subd7_2_588 : subd7_2 [2, 2, 6] = true := by decide +kernel
theorem subd7_2_589 : subd7_2 [2, 2, 7] = true := by decide +kernel
theorem subd7_2_590 : subd7_2 [2, 3] = true := by decide +kernel
theorem subd7_2_591 : subd7_2 [2, 4] = true := by decide +kernel
theorem subd7_2_592 : subd7_2 [3, -4] = true := by decide +kernel
theorem subd7_2_593 : subd7_2 [3, -3] = true := by decide +kernel
theorem subd7_2_594 : subd7_2 [3, -2] = true := by decide +kernel
theorem subd7_2_595 : subd7_2 [3, -1, -9] = true := by decide +kernel
theorem subd7_2_596 : subd7_2 [3, -1, -8] = true := by decide +kernel
theorem subd7_2_597 : subd7_2 [3, -1, -7] = true := by decide +kernel
theorem subd7_2_598 : subd7_2 [3, -1, -6] = true := by decide +kernel
theorem subd7_2_599 : subd7_2 [3, -1, -5] = true := by decide +kernel
theorem subd7_2_600 : subd7_2 [3, -1, -4] = true := by decide +kernel
theorem subd7_2_601 : subd7_2 [3, -1, -3] = true := by decide +kernel
theorem subd7_2_602 : subd7_2 [3, -1, -2] = true := by decide +kernel
theorem subd7_2_603 : subd7_2 [3, -1, -1] = true := by decide +kernel
theorem subd7_2_604 : subd7_2 [3, -1, 0] = true := by decide +kernel
theorem subd7_2_605 : subd7_2 [3, -1, 1] = true := by decide +kernel
theorem subd7_2_606 : subd7_2 [3, -1, 2] = true := by decide +kernel
theorem subd7_2_607 : subd7_2 [3, -1, 3] = true := by decide +kernel
theorem sbd7_2_18 : ∀ q ∈ blkd7_2_18, subd7_2 q = true := by
  unfold blkd7_2_18
  exact List.forall_mem_cons.2 ⟨subd7_2_576, List.forall_mem_cons.2 ⟨subd7_2_577, List.forall_mem_cons.2 ⟨subd7_2_578, List.forall_mem_cons.2 ⟨subd7_2_579, List.forall_mem_cons.2 ⟨subd7_2_580, List.forall_mem_cons.2 ⟨subd7_2_581, List.forall_mem_cons.2 ⟨subd7_2_582, List.forall_mem_cons.2 ⟨subd7_2_583, List.forall_mem_cons.2 ⟨subd7_2_584, List.forall_mem_cons.2 ⟨subd7_2_585, List.forall_mem_cons.2 ⟨subd7_2_586, List.forall_mem_cons.2 ⟨subd7_2_587, List.forall_mem_cons.2 ⟨subd7_2_588, List.forall_mem_cons.2 ⟨subd7_2_589, List.forall_mem_cons.2 ⟨subd7_2_590, List.forall_mem_cons.2 ⟨subd7_2_591, List.forall_mem_cons.2 ⟨subd7_2_592, List.forall_mem_cons.2 ⟨subd7_2_593, List.forall_mem_cons.2 ⟨subd7_2_594, List.forall_mem_cons.2 ⟨subd7_2_595, List.forall_mem_cons.2 ⟨subd7_2_596, List.forall_mem_cons.2 ⟨subd7_2_597, List.forall_mem_cons.2 ⟨subd7_2_598, List.forall_mem_cons.2 ⟨subd7_2_599, List.forall_mem_cons.2 ⟨subd7_2_600, List.forall_mem_cons.2 ⟨subd7_2_601, List.forall_mem_cons.2 ⟨subd7_2_602, List.forall_mem_cons.2 ⟨subd7_2_603, List.forall_mem_cons.2 ⟨subd7_2_604, List.forall_mem_cons.2 ⟨subd7_2_605, List.forall_mem_cons.2 ⟨subd7_2_606, List.forall_mem_cons.2 ⟨subd7_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_608 : subd7_2 [3, -1, 4] = true := by decide +kernel
theorem subd7_2_609 : subd7_2 [3, -1, 5] = true := by decide +kernel
theorem subd7_2_610 : subd7_2 [3, 0, -9] = true := by decide +kernel
theorem subd7_2_611 : subd7_2 [3, 0, -8] = true := by decide +kernel
theorem subd7_2_612 : subd7_2 [3, 0, -7] = true := by decide +kernel
theorem subd7_2_613 : subd7_2 [3, 0, -6] = true := by decide +kernel
theorem subd7_2_614 : subd7_2 [3, 0, -5] = true := by decide +kernel
theorem subd7_2_615 : subd7_2 [3, 0, -4] = true := by decide +kernel
theorem subd7_2_616 : subd7_2 [3, 0, -3] = true := by decide +kernel
theorem subd7_2_617 : subd7_2 [3, 0, -2] = true := by decide +kernel
theorem subd7_2_618 : subd7_2 [3, 0, -1] = true := by decide +kernel
theorem subd7_2_619 : subd7_2 [3, 0, 0] = true := by decide +kernel
theorem subd7_2_620 : subd7_2 [3, 0, 1] = true := by decide +kernel
theorem subd7_2_621 : subd7_2 [3, 0, 2] = true := by decide +kernel
theorem subd7_2_622 : subd7_2 [3, 0, 3] = true := by decide +kernel
theorem subd7_2_623 : subd7_2 [3, 0, 4] = true := by decide +kernel
theorem subd7_2_624 : subd7_2 [3, 0, 5] = true := by decide +kernel
theorem subd7_2_625 : subd7_2 [3, 1, -8] = true := by decide +kernel
theorem subd7_2_626 : subd7_2 [3, 1, -7] = true := by decide +kernel
theorem subd7_2_627 : subd7_2 [3, 1, -6] = true := by decide +kernel
theorem subd7_2_628 : subd7_2 [3, 1, -5] = true := by decide +kernel
theorem subd7_2_629 : subd7_2 [3, 1, -4] = true := by decide +kernel
theorem subd7_2_630 : subd7_2 [3, 1, -3] = true := by decide +kernel
theorem subd7_2_631 : subd7_2 [3, 1, -2] = true := by decide +kernel
theorem subd7_2_632 : subd7_2 [3, 1, -1] = true := by decide +kernel
theorem subd7_2_633 : subd7_2 [3, 1, 0] = true := by decide +kernel
theorem subd7_2_634 : subd7_2 [3, 1, 1] = true := by decide +kernel
theorem subd7_2_635 : subd7_2 [3, 1, 2] = true := by decide +kernel
theorem subd7_2_636 : subd7_2 [3, 1, 3] = true := by decide +kernel
theorem subd7_2_637 : subd7_2 [3, 1, 4] = true := by decide +kernel
theorem subd7_2_638 : subd7_2 [3, 1, 5] = true := by decide +kernel
theorem subd7_2_639 : subd7_2 [3, 2] = true := by decide +kernel
theorem sbd7_2_19 : ∀ q ∈ blkd7_2_19, subd7_2 q = true := by
  unfold blkd7_2_19
  exact List.forall_mem_cons.2 ⟨subd7_2_608, List.forall_mem_cons.2 ⟨subd7_2_609, List.forall_mem_cons.2 ⟨subd7_2_610, List.forall_mem_cons.2 ⟨subd7_2_611, List.forall_mem_cons.2 ⟨subd7_2_612, List.forall_mem_cons.2 ⟨subd7_2_613, List.forall_mem_cons.2 ⟨subd7_2_614, List.forall_mem_cons.2 ⟨subd7_2_615, List.forall_mem_cons.2 ⟨subd7_2_616, List.forall_mem_cons.2 ⟨subd7_2_617, List.forall_mem_cons.2 ⟨subd7_2_618, List.forall_mem_cons.2 ⟨subd7_2_619, List.forall_mem_cons.2 ⟨subd7_2_620, List.forall_mem_cons.2 ⟨subd7_2_621, List.forall_mem_cons.2 ⟨subd7_2_622, List.forall_mem_cons.2 ⟨subd7_2_623, List.forall_mem_cons.2 ⟨subd7_2_624, List.forall_mem_cons.2 ⟨subd7_2_625, List.forall_mem_cons.2 ⟨subd7_2_626, List.forall_mem_cons.2 ⟨subd7_2_627, List.forall_mem_cons.2 ⟨subd7_2_628, List.forall_mem_cons.2 ⟨subd7_2_629, List.forall_mem_cons.2 ⟨subd7_2_630, List.forall_mem_cons.2 ⟨subd7_2_631, List.forall_mem_cons.2 ⟨subd7_2_632, List.forall_mem_cons.2 ⟨subd7_2_633, List.forall_mem_cons.2 ⟨subd7_2_634, List.forall_mem_cons.2 ⟨subd7_2_635, List.forall_mem_cons.2 ⟨subd7_2_636, List.forall_mem_cons.2 ⟨subd7_2_637, List.forall_mem_cons.2 ⟨subd7_2_638, List.forall_mem_cons.2 ⟨subd7_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_640 : subd7_2 [3, 3] = true := by decide +kernel
theorem subd7_2_641 : subd7_2 [4, -3] = true := by decide +kernel
theorem subd7_2_642 : subd7_2 [4, -2] = true := by decide +kernel
theorem subd7_2_643 : subd7_2 [4, -1] = true := by decide +kernel
theorem subd7_2_644 : subd7_2 [4, 0] = true := by decide +kernel
theorem subd7_2_645 : subd7_2 [4, 1] = true := by decide +kernel
theorem subd7_2_646 : subd7_2 [4, 2] = true := by decide +kernel
theorem sbd7_2_20 : ∀ q ∈ blkd7_2_20, subd7_2 q = true := by
  unfold blkd7_2_20
  exact List.forall_mem_cons.2 ⟨subd7_2_640, List.forall_mem_cons.2 ⟨subd7_2_641, List.forall_mem_cons.2 ⟨subd7_2_642, List.forall_mem_cons.2 ⟨subd7_2_643, List.forall_mem_cons.2 ⟨subd7_2_644, List.forall_mem_cons.2 ⟨subd7_2_645, List.forall_mem_cons.2 ⟨subd7_2_646, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-2, -2] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [-2, -1, -10] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [-2, -1, -9] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [-2, -1, -8] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [-2, -1, -7] = true := by decide +kernel
theorem subd7_3_5 : subd7_3 [-2, -1, -6] = true := by decide +kernel
theorem subd7_3_6 : subd7_3 [-2, -1, -5] = true := by decide +kernel
theorem subd7_3_7 : subd7_3 [-2, -1, -4] = true := by decide +kernel
theorem subd7_3_8 : subd7_3 [-2, -1, -3] = true := by decide +kernel
theorem subd7_3_9 : subd7_3 [-2, -1, -2] = true := by decide +kernel
theorem subd7_3_10 : subd7_3 [-2, -1, -1] = true := by decide +kernel
theorem subd7_3_11 : subd7_3 [-2, -1, 0] = true := by decide +kernel
theorem subd7_3_12 : subd7_3 [-2, -1, 1] = true := by decide +kernel
theorem subd7_3_13 : subd7_3 [-2, -1, 2] = true := by decide +kernel
theorem subd7_3_14 : subd7_3 [-2, -1, 3] = true := by decide +kernel
theorem subd7_3_15 : subd7_3 [-2, -1, 4] = true := by decide +kernel
theorem subd7_3_16 : subd7_3 [-2, -1, 5] = true := by decide +kernel
theorem subd7_3_17 : subd7_3 [-2, -1, 6] = true := by decide +kernel
theorem subd7_3_18 : subd7_3 [-2, -1, 7] = true := by decide +kernel
theorem subd7_3_19 : subd7_3 [-2, -1, 8] = true := by decide +kernel
theorem subd7_3_20 : subd7_3 [-2, -1, 9] = true := by decide +kernel
theorem subd7_3_21 : subd7_3 [-2, -1, 10] = true := by decide +kernel
theorem subd7_3_22 : subd7_3 [-2, 0, -13] = true := by decide +kernel
theorem subd7_3_23 : subd7_3 [-2, 0, -12] = true := by decide +kernel
theorem subd7_3_24 : subd7_3 [-2, 0, -11] = true := by decide +kernel
theorem subd7_3_25 : subd7_3 [-2, 0, -10] = true := by decide +kernel
theorem subd7_3_26 : subd7_3 [-2, 0, -9] = true := by decide +kernel
theorem subd7_3_27 : subd7_3 [-2, 0, -8] = true := by decide +kernel
theorem subd7_3_28 : subd7_3 [-2, 0, -7] = true := by decide +kernel
theorem subd7_3_29 : subd7_3 [-2, 0, -6] = true := by decide +kernel
theorem subd7_3_30 : subd7_3 [-2, 0, -5] = true := by decide +kernel
theorem subd7_3_31 : subd7_3 [-2, 0, -4] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_cons.2 ⟨subd7_3_5, List.forall_mem_cons.2 ⟨subd7_3_6, List.forall_mem_cons.2 ⟨subd7_3_7, List.forall_mem_cons.2 ⟨subd7_3_8, List.forall_mem_cons.2 ⟨subd7_3_9, List.forall_mem_cons.2 ⟨subd7_3_10, List.forall_mem_cons.2 ⟨subd7_3_11, List.forall_mem_cons.2 ⟨subd7_3_12, List.forall_mem_cons.2 ⟨subd7_3_13, List.forall_mem_cons.2 ⟨subd7_3_14, List.forall_mem_cons.2 ⟨subd7_3_15, List.forall_mem_cons.2 ⟨subd7_3_16, List.forall_mem_cons.2 ⟨subd7_3_17, List.forall_mem_cons.2 ⟨subd7_3_18, List.forall_mem_cons.2 ⟨subd7_3_19, List.forall_mem_cons.2 ⟨subd7_3_20, List.forall_mem_cons.2 ⟨subd7_3_21, List.forall_mem_cons.2 ⟨subd7_3_22, List.forall_mem_cons.2 ⟨subd7_3_23, List.forall_mem_cons.2 ⟨subd7_3_24, List.forall_mem_cons.2 ⟨subd7_3_25, List.forall_mem_cons.2 ⟨subd7_3_26, List.forall_mem_cons.2 ⟨subd7_3_27, List.forall_mem_cons.2 ⟨subd7_3_28, List.forall_mem_cons.2 ⟨subd7_3_29, List.forall_mem_cons.2 ⟨subd7_3_30, List.forall_mem_cons.2 ⟨subd7_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_32 : subd7_3 [-2, 0, -3] = true := by decide +kernel
theorem subd7_3_33 : subd7_3 [-2, 0, -2] = true := by decide +kernel
theorem subd7_3_34 : subd7_3 [-2, 0, -1] = true := by decide +kernel
theorem subd7_3_35 : subd7_3 [-2, 0, 0] = true := by decide +kernel
theorem subd7_3_36 : subd7_3 [-2, 0, 1] = true := by decide +kernel
theorem subd7_3_37 : subd7_3 [-2, 0, 2] = true := by decide +kernel
theorem subd7_3_38 : subd7_3 [-2, 0, 3] = true := by decide +kernel
theorem subd7_3_39 : subd7_3 [-2, 0, 4] = true := by decide +kernel
theorem subd7_3_40 : subd7_3 [-2, 0, 5] = true := by decide +kernel
theorem subd7_3_41 : subd7_3 [-2, 0, 6] = true := by decide +kernel
theorem subd7_3_42 : subd7_3 [-2, 0, 7] = true := by decide +kernel
theorem subd7_3_43 : subd7_3 [-2, 0, 8] = true := by decide +kernel
theorem subd7_3_44 : subd7_3 [-2, 0, 9] = true := by decide +kernel
theorem subd7_3_45 : subd7_3 [-2, 0, 10] = true := by decide +kernel
theorem subd7_3_46 : subd7_3 [-2, 0, 11] = true := by decide +kernel
theorem subd7_3_47 : subd7_3 [-2, 0, 12] = true := by decide +kernel
theorem subd7_3_48 : subd7_3 [-2, 0, 13] = true := by decide +kernel
theorem subd7_3_49 : subd7_3 [-2, 1, -9] = true := by decide +kernel
theorem subd7_3_50 : subd7_3 [-2, 1, -8] = true := by decide +kernel
theorem subd7_3_51 : subd7_3 [-2, 1, -7] = true := by decide +kernel
theorem subd7_3_52 : subd7_3 [-2, 1, -6] = true := by decide +kernel
theorem subd7_3_53 : subd7_3 [-2, 1, -5] = true := by decide +kernel
theorem subd7_3_54 : subd7_3 [-2, 1, -4] = true := by decide +kernel
theorem subd7_3_55 : subd7_3 [-2, 1, -3] = true := by decide +kernel
theorem subd7_3_56 : subd7_3 [-2, 1, -2] = true := by decide +kernel
theorem subd7_3_57 : subd7_3 [-2, 1, -1] = true := by decide +kernel
theorem subd7_3_58 : subd7_3 [-2, 1, 0] = true := by decide +kernel
theorem subd7_3_59 : subd7_3 [-2, 1, 1] = true := by decide +kernel
theorem subd7_3_60 : subd7_3 [-2, 1, 2] = true := by decide +kernel
theorem subd7_3_61 : subd7_3 [-2, 1, 3] = true := by decide +kernel
theorem subd7_3_62 : subd7_3 [-2, 1, 4] = true := by decide +kernel
theorem subd7_3_63 : subd7_3 [-2, 1, 5] = true := by decide +kernel
theorem sbd7_3_1 : ∀ q ∈ blkd7_3_1, subd7_3 q = true := by
  unfold blkd7_3_1
  exact List.forall_mem_cons.2 ⟨subd7_3_32, List.forall_mem_cons.2 ⟨subd7_3_33, List.forall_mem_cons.2 ⟨subd7_3_34, List.forall_mem_cons.2 ⟨subd7_3_35, List.forall_mem_cons.2 ⟨subd7_3_36, List.forall_mem_cons.2 ⟨subd7_3_37, List.forall_mem_cons.2 ⟨subd7_3_38, List.forall_mem_cons.2 ⟨subd7_3_39, List.forall_mem_cons.2 ⟨subd7_3_40, List.forall_mem_cons.2 ⟨subd7_3_41, List.forall_mem_cons.2 ⟨subd7_3_42, List.forall_mem_cons.2 ⟨subd7_3_43, List.forall_mem_cons.2 ⟨subd7_3_44, List.forall_mem_cons.2 ⟨subd7_3_45, List.forall_mem_cons.2 ⟨subd7_3_46, List.forall_mem_cons.2 ⟨subd7_3_47, List.forall_mem_cons.2 ⟨subd7_3_48, List.forall_mem_cons.2 ⟨subd7_3_49, List.forall_mem_cons.2 ⟨subd7_3_50, List.forall_mem_cons.2 ⟨subd7_3_51, List.forall_mem_cons.2 ⟨subd7_3_52, List.forall_mem_cons.2 ⟨subd7_3_53, List.forall_mem_cons.2 ⟨subd7_3_54, List.forall_mem_cons.2 ⟨subd7_3_55, List.forall_mem_cons.2 ⟨subd7_3_56, List.forall_mem_cons.2 ⟨subd7_3_57, List.forall_mem_cons.2 ⟨subd7_3_58, List.forall_mem_cons.2 ⟨subd7_3_59, List.forall_mem_cons.2 ⟨subd7_3_60, List.forall_mem_cons.2 ⟨subd7_3_61, List.forall_mem_cons.2 ⟨subd7_3_62, List.forall_mem_cons.2 ⟨subd7_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_64 : subd7_3 [-2, 1, 6] = true := by decide +kernel
theorem subd7_3_65 : subd7_3 [-2, 1, 7] = true := by decide +kernel
theorem subd7_3_66 : subd7_3 [-2, 1, 8] = true := by decide +kernel
theorem subd7_3_67 : subd7_3 [-2, 1, 9] = true := by decide +kernel
theorem subd7_3_68 : subd7_3 [-1, -3] = true := by decide +kernel
theorem subd7_3_69 : subd7_3 [-1, -2, -10] = true := by decide +kernel
theorem subd7_3_70 : subd7_3 [-1, -2, -9] = true := by decide +kernel
theorem subd7_3_71 : subd7_3 [-1, -2, -8] = true := by decide +kernel
theorem subd7_3_72 : subd7_3 [-1, -2, -7] = true := by decide +kernel
theorem subd7_3_73 : subd7_3 [-1, -2, -6] = true := by decide +kernel
theorem subd7_3_74 : subd7_3 [-1, -2, -5] = true := by decide +kernel
theorem subd7_3_75 : subd7_3 [-1, -2, -4] = true := by decide +kernel
theorem subd7_3_76 : subd7_3 [-1, -2, -3] = true := by decide +kernel
theorem subd7_3_77 : subd7_3 [-1, -2, -2] = true := by decide +kernel
theorem subd7_3_78 : subd7_3 [-1, -2, -1] = true := by decide +kernel
theorem subd7_3_79 : subd7_3 [-1, -2, 0] = true := by decide +kernel
theorem subd7_3_80 : subd7_3 [-1, -2, 1] = true := by decide +kernel
theorem subd7_3_81 : subd7_3 [-1, -2, 2] = true := by decide +kernel
theorem subd7_3_82 : subd7_3 [-1, -2, 3] = true := by decide +kernel
theorem subd7_3_83 : subd7_3 [-1, -2, 4] = true := by decide +kernel
theorem subd7_3_84 : subd7_3 [-1, -2, 5] = true := by decide +kernel
theorem subd7_3_85 : subd7_3 [-1, -2, 6] = true := by decide +kernel
theorem subd7_3_86 : subd7_3 [-1, -2, 7] = true := by decide +kernel
theorem subd7_3_87 : subd7_3 [-1, -2, 8] = true := by decide +kernel
theorem subd7_3_88 : subd7_3 [-1, -2, 9] = true := by decide +kernel
theorem subd7_3_89 : subd7_3 [-1, -2, 10] = true := by decide +kernel
theorem subd7_3_90 : subd7_3 [-1, -1, -18] = true := by decide +kernel
theorem subd7_3_91 : subd7_3 [-1, -1, -17] = true := by decide +kernel
theorem subd7_3_92 : subd7_3 [-1, -1, -16] = true := by decide +kernel
theorem subd7_3_93 : subd7_3 [-1, -1, -15] = true := by decide +kernel
theorem subd7_3_94 : subd7_3 [-1, -1, -14] = true := by decide +kernel
theorem subd7_3_95 : subd7_3 [-1, -1, -13] = true := by decide +kernel
theorem sbd7_3_2 : ∀ q ∈ blkd7_3_2, subd7_3 q = true := by
  unfold blkd7_3_2
  exact List.forall_mem_cons.2 ⟨subd7_3_64, List.forall_mem_cons.2 ⟨subd7_3_65, List.forall_mem_cons.2 ⟨subd7_3_66, List.forall_mem_cons.2 ⟨subd7_3_67, List.forall_mem_cons.2 ⟨subd7_3_68, List.forall_mem_cons.2 ⟨subd7_3_69, List.forall_mem_cons.2 ⟨subd7_3_70, List.forall_mem_cons.2 ⟨subd7_3_71, List.forall_mem_cons.2 ⟨subd7_3_72, List.forall_mem_cons.2 ⟨subd7_3_73, List.forall_mem_cons.2 ⟨subd7_3_74, List.forall_mem_cons.2 ⟨subd7_3_75, List.forall_mem_cons.2 ⟨subd7_3_76, List.forall_mem_cons.2 ⟨subd7_3_77, List.forall_mem_cons.2 ⟨subd7_3_78, List.forall_mem_cons.2 ⟨subd7_3_79, List.forall_mem_cons.2 ⟨subd7_3_80, List.forall_mem_cons.2 ⟨subd7_3_81, List.forall_mem_cons.2 ⟨subd7_3_82, List.forall_mem_cons.2 ⟨subd7_3_83, List.forall_mem_cons.2 ⟨subd7_3_84, List.forall_mem_cons.2 ⟨subd7_3_85, List.forall_mem_cons.2 ⟨subd7_3_86, List.forall_mem_cons.2 ⟨subd7_3_87, List.forall_mem_cons.2 ⟨subd7_3_88, List.forall_mem_cons.2 ⟨subd7_3_89, List.forall_mem_cons.2 ⟨subd7_3_90, List.forall_mem_cons.2 ⟨subd7_3_91, List.forall_mem_cons.2 ⟨subd7_3_92, List.forall_mem_cons.2 ⟨subd7_3_93, List.forall_mem_cons.2 ⟨subd7_3_94, List.forall_mem_cons.2 ⟨subd7_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_96 : subd7_3 [-1, -1, -12] = true := by decide +kernel
theorem subd7_3_97 : subd7_3 [-1, -1, -11] = true := by decide +kernel
theorem subd7_3_98 : subd7_3 [-1, -1, -10] = true := by decide +kernel
theorem subd7_3_99 : subd7_3 [-1, -1, -9] = true := by decide +kernel
theorem subd7_3_100 : subd7_3 [-1, -1, -8] = true := by decide +kernel
theorem subd7_3_101 : subd7_3 [-1, -1, -7] = true := by decide +kernel
theorem subd7_3_102 : subd7_3 [-1, -1, -6] = true := by decide +kernel
theorem subd7_3_103 : subd7_3 [-1, -1, -5] = true := by decide +kernel
theorem subd7_3_104 : subd7_3 [-1, -1, -4] = true := by decide +kernel
theorem subd7_3_105 : subd7_3 [-1, -1, -3] = true := by decide +kernel
theorem subd7_3_106 : subd7_3 [-1, -1, -2] = true := by decide +kernel
theorem subd7_3_107 : subd7_3 [-1, -1, -1] = true := by decide +kernel
theorem subd7_3_108 : subd7_3 [-1, -1, 0] = true := by decide +kernel
theorem subd7_3_109 : subd7_3 [-1, -1, 1] = true := by decide +kernel
theorem subd7_3_110 : subd7_3 [-1, -1, 2] = true := by decide +kernel
theorem subd7_3_111 : subd7_3 [-1, -1, 3] = true := by decide +kernel
theorem subd7_3_112 : subd7_3 [-1, -1, 4] = true := by decide +kernel
theorem subd7_3_113 : subd7_3 [-1, -1, 5] = true := by decide +kernel
theorem subd7_3_114 : subd7_3 [-1, -1, 6] = true := by decide +kernel
theorem subd7_3_115 : subd7_3 [-1, -1, 7] = true := by decide +kernel
theorem subd7_3_116 : subd7_3 [-1, -1, 8] = true := by decide +kernel
theorem subd7_3_117 : subd7_3 [-1, -1, 9] = true := by decide +kernel
theorem subd7_3_118 : subd7_3 [-1, -1, 10] = true := by decide +kernel
theorem subd7_3_119 : subd7_3 [-1, -1, 11] = true := by decide +kernel
theorem subd7_3_120 : subd7_3 [-1, -1, 12] = true := by decide +kernel
theorem subd7_3_121 : subd7_3 [-1, -1, 13] = true := by decide +kernel
theorem subd7_3_122 : subd7_3 [-1, -1, 14] = true := by decide +kernel
theorem subd7_3_123 : subd7_3 [-1, -1, 15] = true := by decide +kernel
theorem subd7_3_124 : subd7_3 [-1, -1, 16] = true := by decide +kernel
theorem subd7_3_125 : subd7_3 [-1, -1, 17] = true := by decide +kernel
theorem subd7_3_126 : subd7_3 [-1, 0, -20] = true := by decide +kernel
theorem subd7_3_127 : subd7_3 [-1, 0, -19] = true := by decide +kernel
theorem sbd7_3_3 : ∀ q ∈ blkd7_3_3, subd7_3 q = true := by
  unfold blkd7_3_3
  exact List.forall_mem_cons.2 ⟨subd7_3_96, List.forall_mem_cons.2 ⟨subd7_3_97, List.forall_mem_cons.2 ⟨subd7_3_98, List.forall_mem_cons.2 ⟨subd7_3_99, List.forall_mem_cons.2 ⟨subd7_3_100, List.forall_mem_cons.2 ⟨subd7_3_101, List.forall_mem_cons.2 ⟨subd7_3_102, List.forall_mem_cons.2 ⟨subd7_3_103, List.forall_mem_cons.2 ⟨subd7_3_104, List.forall_mem_cons.2 ⟨subd7_3_105, List.forall_mem_cons.2 ⟨subd7_3_106, List.forall_mem_cons.2 ⟨subd7_3_107, List.forall_mem_cons.2 ⟨subd7_3_108, List.forall_mem_cons.2 ⟨subd7_3_109, List.forall_mem_cons.2 ⟨subd7_3_110, List.forall_mem_cons.2 ⟨subd7_3_111, List.forall_mem_cons.2 ⟨subd7_3_112, List.forall_mem_cons.2 ⟨subd7_3_113, List.forall_mem_cons.2 ⟨subd7_3_114, List.forall_mem_cons.2 ⟨subd7_3_115, List.forall_mem_cons.2 ⟨subd7_3_116, List.forall_mem_cons.2 ⟨subd7_3_117, List.forall_mem_cons.2 ⟨subd7_3_118, List.forall_mem_cons.2 ⟨subd7_3_119, List.forall_mem_cons.2 ⟨subd7_3_120, List.forall_mem_cons.2 ⟨subd7_3_121, List.forall_mem_cons.2 ⟨subd7_3_122, List.forall_mem_cons.2 ⟨subd7_3_123, List.forall_mem_cons.2 ⟨subd7_3_124, List.forall_mem_cons.2 ⟨subd7_3_125, List.forall_mem_cons.2 ⟨subd7_3_126, List.forall_mem_cons.2 ⟨subd7_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_128 : subd7_3 [-1, 0, -18] = true := by decide +kernel
theorem subd7_3_129 : subd7_3 [-1, 0, -17] = true := by decide +kernel
theorem subd7_3_130 : subd7_3 [-1, 0, -16] = true := by decide +kernel
theorem subd7_3_131 : subd7_3 [-1, 0, -15] = true := by decide +kernel
theorem subd7_3_132 : subd7_3 [-1, 0, -14] = true := by decide +kernel
theorem subd7_3_133 : subd7_3 [-1, 0, -13] = true := by decide +kernel
theorem subd7_3_134 : subd7_3 [-1, 0, -12] = true := by decide +kernel
theorem subd7_3_135 : subd7_3 [-1, 0, -11] = true := by decide +kernel
theorem subd7_3_136 : subd7_3 [-1, 0, -10] = true := by decide +kernel
theorem subd7_3_137 : subd7_3 [-1, 0, -9] = true := by decide +kernel
theorem subd7_3_138 : subd7_3 [-1, 0, -8] = true := by decide +kernel
theorem subd7_3_139 : subd7_3 [-1, 0, -7] = true := by decide +kernel
theorem subd7_3_140 : subd7_3 [-1, 0, -6] = true := by decide +kernel
theorem subd7_3_141 : subd7_3 [-1, 0, -5] = true := by decide +kernel
theorem subd7_3_142 : subd7_3 [-1, 0, -4] = true := by decide +kernel
theorem subd7_3_143 : subd7_3 [-1, 0, -3] = true := by decide +kernel
theorem subd7_3_144 : subd7_3 [-1, 0, -2] = true := by decide +kernel
theorem subd7_3_145 : subd7_3 [-1, 0, -1] = true := by decide +kernel
theorem subd7_3_146 : subd7_3 [-1, 0, 0] = true := by decide +kernel
theorem subd7_3_147 : subd7_3 [-1, 0, 1] = true := by decide +kernel
theorem subd7_3_148 : subd7_3 [-1, 0, 2] = true := by decide +kernel
theorem subd7_3_149 : subd7_3 [-1, 0, 3] = true := by decide +kernel
theorem subd7_3_150 : subd7_3 [-1, 0, 4] = true := by decide +kernel
theorem subd7_3_151 : subd7_3 [-1, 0, 5] = true := by decide +kernel
theorem subd7_3_152 : subd7_3 [-1, 0, 6] = true := by decide +kernel
theorem subd7_3_153 : subd7_3 [-1, 0, 7] = true := by decide +kernel
theorem subd7_3_154 : subd7_3 [-1, 0, 8] = true := by decide +kernel
theorem subd7_3_155 : subd7_3 [-1, 0, 9] = true := by decide +kernel
theorem subd7_3_156 : subd7_3 [-1, 0, 10] = true := by decide +kernel
theorem subd7_3_157 : subd7_3 [-1, 0, 11] = true := by decide +kernel
theorem subd7_3_158 : subd7_3 [-1, 0, 12] = true := by decide +kernel
theorem subd7_3_159 : subd7_3 [-1, 0, 13] = true := by decide +kernel
theorem sbd7_3_4 : ∀ q ∈ blkd7_3_4, subd7_3 q = true := by
  unfold blkd7_3_4
  exact List.forall_mem_cons.2 ⟨subd7_3_128, List.forall_mem_cons.2 ⟨subd7_3_129, List.forall_mem_cons.2 ⟨subd7_3_130, List.forall_mem_cons.2 ⟨subd7_3_131, List.forall_mem_cons.2 ⟨subd7_3_132, List.forall_mem_cons.2 ⟨subd7_3_133, List.forall_mem_cons.2 ⟨subd7_3_134, List.forall_mem_cons.2 ⟨subd7_3_135, List.forall_mem_cons.2 ⟨subd7_3_136, List.forall_mem_cons.2 ⟨subd7_3_137, List.forall_mem_cons.2 ⟨subd7_3_138, List.forall_mem_cons.2 ⟨subd7_3_139, List.forall_mem_cons.2 ⟨subd7_3_140, List.forall_mem_cons.2 ⟨subd7_3_141, List.forall_mem_cons.2 ⟨subd7_3_142, List.forall_mem_cons.2 ⟨subd7_3_143, List.forall_mem_cons.2 ⟨subd7_3_144, List.forall_mem_cons.2 ⟨subd7_3_145, List.forall_mem_cons.2 ⟨subd7_3_146, List.forall_mem_cons.2 ⟨subd7_3_147, List.forall_mem_cons.2 ⟨subd7_3_148, List.forall_mem_cons.2 ⟨subd7_3_149, List.forall_mem_cons.2 ⟨subd7_3_150, List.forall_mem_cons.2 ⟨subd7_3_151, List.forall_mem_cons.2 ⟨subd7_3_152, List.forall_mem_cons.2 ⟨subd7_3_153, List.forall_mem_cons.2 ⟨subd7_3_154, List.forall_mem_cons.2 ⟨subd7_3_155, List.forall_mem_cons.2 ⟨subd7_3_156, List.forall_mem_cons.2 ⟨subd7_3_157, List.forall_mem_cons.2 ⟨subd7_3_158, List.forall_mem_cons.2 ⟨subd7_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_160 : subd7_3 [-1, 0, 14] = true := by decide +kernel
theorem subd7_3_161 : subd7_3 [-1, 0, 15] = true := by decide +kernel
theorem subd7_3_162 : subd7_3 [-1, 0, 16] = true := by decide +kernel
theorem subd7_3_163 : subd7_3 [-1, 0, 17] = true := by decide +kernel
theorem subd7_3_164 : subd7_3 [-1, 0, 18] = true := by decide +kernel
theorem subd7_3_165 : subd7_3 [-1, 0, 19] = true := by decide +kernel
theorem subd7_3_166 : subd7_3 [-1, 1, -18] = true := by decide +kernel
theorem subd7_3_167 : subd7_3 [-1, 1, -17] = true := by decide +kernel
theorem subd7_3_168 : subd7_3 [-1, 1, -16] = true := by decide +kernel
theorem subd7_3_169 : subd7_3 [-1, 1, -15] = true := by decide +kernel
theorem subd7_3_170 : subd7_3 [-1, 1, -14] = true := by decide +kernel
theorem subd7_3_171 : subd7_3 [-1, 1, -13] = true := by decide +kernel
theorem subd7_3_172 : subd7_3 [-1, 1, -12] = true := by decide +kernel
theorem subd7_3_173 : subd7_3 [-1, 1, -11] = true := by decide +kernel
theorem subd7_3_174 : subd7_3 [-1, 1, -10] = true := by decide +kernel
theorem subd7_3_175 : subd7_3 [-1, 1, -9] = true := by decide +kernel
theorem subd7_3_176 : subd7_3 [-1, 1, -8] = true := by decide +kernel
theorem subd7_3_177 : subd7_3 [-1, 1, -7] = true := by decide +kernel
theorem subd7_3_178 : subd7_3 [-1, 1, -6] = true := by decide +kernel
theorem subd7_3_179 : subd7_3 [-1, 1, -5] = true := by decide +kernel
theorem subd7_3_180 : subd7_3 [-1, 1, -4] = true := by decide +kernel
theorem subd7_3_181 : subd7_3 [-1, 1, -3] = true := by decide +kernel
theorem subd7_3_182 : subd7_3 [-1, 1, -2] = true := by decide +kernel
theorem subd7_3_183 : subd7_3 [-1, 1, -1] = true := by decide +kernel
theorem subd7_3_184 : subd7_3 [-1, 1, 0] = true := by decide +kernel
theorem subd7_3_185 : subd7_3 [-1, 1, 1] = true := by decide +kernel
theorem subd7_3_186 : subd7_3 [-1, 1, 2] = true := by decide +kernel
theorem subd7_3_187 : subd7_3 [-1, 1, 3] = true := by decide +kernel
theorem subd7_3_188 : subd7_3 [-1, 1, 4] = true := by decide +kernel
theorem subd7_3_189 : subd7_3 [-1, 1, 5] = true := by decide +kernel
theorem subd7_3_190 : subd7_3 [-1, 1, 6] = true := by decide +kernel
theorem subd7_3_191 : subd7_3 [-1, 1, 7] = true := by decide +kernel
theorem sbd7_3_5 : ∀ q ∈ blkd7_3_5, subd7_3 q = true := by
  unfold blkd7_3_5
  exact List.forall_mem_cons.2 ⟨subd7_3_160, List.forall_mem_cons.2 ⟨subd7_3_161, List.forall_mem_cons.2 ⟨subd7_3_162, List.forall_mem_cons.2 ⟨subd7_3_163, List.forall_mem_cons.2 ⟨subd7_3_164, List.forall_mem_cons.2 ⟨subd7_3_165, List.forall_mem_cons.2 ⟨subd7_3_166, List.forall_mem_cons.2 ⟨subd7_3_167, List.forall_mem_cons.2 ⟨subd7_3_168, List.forall_mem_cons.2 ⟨subd7_3_169, List.forall_mem_cons.2 ⟨subd7_3_170, List.forall_mem_cons.2 ⟨subd7_3_171, List.forall_mem_cons.2 ⟨subd7_3_172, List.forall_mem_cons.2 ⟨subd7_3_173, List.forall_mem_cons.2 ⟨subd7_3_174, List.forall_mem_cons.2 ⟨subd7_3_175, List.forall_mem_cons.2 ⟨subd7_3_176, List.forall_mem_cons.2 ⟨subd7_3_177, List.forall_mem_cons.2 ⟨subd7_3_178, List.forall_mem_cons.2 ⟨subd7_3_179, List.forall_mem_cons.2 ⟨subd7_3_180, List.forall_mem_cons.2 ⟨subd7_3_181, List.forall_mem_cons.2 ⟨subd7_3_182, List.forall_mem_cons.2 ⟨subd7_3_183, List.forall_mem_cons.2 ⟨subd7_3_184, List.forall_mem_cons.2 ⟨subd7_3_185, List.forall_mem_cons.2 ⟨subd7_3_186, List.forall_mem_cons.2 ⟨subd7_3_187, List.forall_mem_cons.2 ⟨subd7_3_188, List.forall_mem_cons.2 ⟨subd7_3_189, List.forall_mem_cons.2 ⟨subd7_3_190, List.forall_mem_cons.2 ⟨subd7_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_192 : subd7_3 [-1, 1, 8] = true := by decide +kernel
theorem subd7_3_193 : subd7_3 [-1, 1, 9] = true := by decide +kernel
theorem subd7_3_194 : subd7_3 [-1, 1, 10] = true := by decide +kernel
theorem subd7_3_195 : subd7_3 [-1, 1, 11] = true := by decide +kernel
theorem subd7_3_196 : subd7_3 [-1, 1, 12] = true := by decide +kernel
theorem subd7_3_197 : subd7_3 [-1, 1, 13] = true := by decide +kernel
theorem subd7_3_198 : subd7_3 [-1, 1, 14] = true := by decide +kernel
theorem subd7_3_199 : subd7_3 [-1, 1, 15] = true := by decide +kernel
theorem subd7_3_200 : subd7_3 [-1, 1, 16] = true := by decide +kernel
theorem subd7_3_201 : subd7_3 [-1, 1, 17] = true := by decide +kernel
theorem subd7_3_202 : subd7_3 [-1, 2, -10] = true := by decide +kernel
theorem subd7_3_203 : subd7_3 [-1, 2, -9] = true := by decide +kernel
theorem subd7_3_204 : subd7_3 [-1, 2, -8] = true := by decide +kernel
theorem subd7_3_205 : subd7_3 [-1, 2, -7] = true := by decide +kernel
theorem subd7_3_206 : subd7_3 [-1, 2, -6] = true := by decide +kernel
theorem subd7_3_207 : subd7_3 [-1, 2, -5] = true := by decide +kernel
theorem subd7_3_208 : subd7_3 [-1, 2, -4] = true := by decide +kernel
theorem subd7_3_209 : subd7_3 [-1, 2, -3] = true := by decide +kernel
theorem subd7_3_210 : subd7_3 [-1, 2, -2] = true := by decide +kernel
theorem subd7_3_211 : subd7_3 [-1, 2, -1] = true := by decide +kernel
theorem subd7_3_212 : subd7_3 [-1, 2, 0] = true := by decide +kernel
theorem subd7_3_213 : subd7_3 [-1, 2, 1] = true := by decide +kernel
theorem subd7_3_214 : subd7_3 [-1, 2, 2] = true := by decide +kernel
theorem subd7_3_215 : subd7_3 [-1, 2, 3] = true := by decide +kernel
theorem subd7_3_216 : subd7_3 [-1, 2, 4] = true := by decide +kernel
theorem subd7_3_217 : subd7_3 [-1, 2, 5] = true := by decide +kernel
theorem subd7_3_218 : subd7_3 [-1, 2, 6] = true := by decide +kernel
theorem subd7_3_219 : subd7_3 [-1, 2, 7] = true := by decide +kernel
theorem subd7_3_220 : subd7_3 [-1, 2, 8] = true := by decide +kernel
theorem subd7_3_221 : subd7_3 [-1, 2, 9] = true := by decide +kernel
theorem subd7_3_222 : subd7_3 [0, -3] = true := by decide +kernel
theorem subd7_3_223 : subd7_3 [0, -2, -13] = true := by decide +kernel
theorem sbd7_3_6 : ∀ q ∈ blkd7_3_6, subd7_3 q = true := by
  unfold blkd7_3_6
  exact List.forall_mem_cons.2 ⟨subd7_3_192, List.forall_mem_cons.2 ⟨subd7_3_193, List.forall_mem_cons.2 ⟨subd7_3_194, List.forall_mem_cons.2 ⟨subd7_3_195, List.forall_mem_cons.2 ⟨subd7_3_196, List.forall_mem_cons.2 ⟨subd7_3_197, List.forall_mem_cons.2 ⟨subd7_3_198, List.forall_mem_cons.2 ⟨subd7_3_199, List.forall_mem_cons.2 ⟨subd7_3_200, List.forall_mem_cons.2 ⟨subd7_3_201, List.forall_mem_cons.2 ⟨subd7_3_202, List.forall_mem_cons.2 ⟨subd7_3_203, List.forall_mem_cons.2 ⟨subd7_3_204, List.forall_mem_cons.2 ⟨subd7_3_205, List.forall_mem_cons.2 ⟨subd7_3_206, List.forall_mem_cons.2 ⟨subd7_3_207, List.forall_mem_cons.2 ⟨subd7_3_208, List.forall_mem_cons.2 ⟨subd7_3_209, List.forall_mem_cons.2 ⟨subd7_3_210, List.forall_mem_cons.2 ⟨subd7_3_211, List.forall_mem_cons.2 ⟨subd7_3_212, List.forall_mem_cons.2 ⟨subd7_3_213, List.forall_mem_cons.2 ⟨subd7_3_214, List.forall_mem_cons.2 ⟨subd7_3_215, List.forall_mem_cons.2 ⟨subd7_3_216, List.forall_mem_cons.2 ⟨subd7_3_217, List.forall_mem_cons.2 ⟨subd7_3_218, List.forall_mem_cons.2 ⟨subd7_3_219, List.forall_mem_cons.2 ⟨subd7_3_220, List.forall_mem_cons.2 ⟨subd7_3_221, List.forall_mem_cons.2 ⟨subd7_3_222, List.forall_mem_cons.2 ⟨subd7_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
