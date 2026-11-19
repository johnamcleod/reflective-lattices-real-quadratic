import ReflectZphi.Data.Cert5.C098.Base

namespace ReflectZphi.Data.Cert5.C098
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_608 : sub6 [2, 3, -2] = true := by decide +kernel
theorem sub6_609 : sub6 [2, 3, -1] = true := by decide +kernel
theorem sub6_610 : sub6 [2, 3, 0] = true := by decide +kernel
theorem sub6_611 : sub6 [2, 3, 1] = true := by decide +kernel
theorem sub6_612 : sub6 [2, 3, 2] = true := by decide +kernel
theorem sub6_613 : sub6 [2, 3, 3] = true := by decide +kernel
theorem sub6_614 : sub6 [2, 3, 4] = true := by decide +kernel
theorem sub6_615 : sub6 [2, 4] = true := by decide +kernel
theorem sub6_616 : sub6 [3, -4] = true := by decide +kernel
theorem sub6_617 : sub6 [3, -3] = true := by decide +kernel
theorem sub6_618 : sub6 [3, -2] = true := by decide +kernel
theorem sub6_619 : sub6 [3, -1, -8] = true := by decide +kernel
theorem sub6_620 : sub6 [3, -1, -7] = true := by decide +kernel
theorem sub6_621 : sub6 [3, -1, -6] = true := by decide +kernel
theorem sub6_622 : sub6 [3, -1, -5] = true := by decide +kernel
theorem sub6_623 : sub6 [3, -1, -4] = true := by decide +kernel
theorem sub6_624 : sub6 [3, -1, -3] = true := by decide +kernel
theorem sub6_625 : sub6 [3, -1, -2] = true := by decide +kernel
theorem sub6_626 : sub6 [3, -1, -1] = true := by decide +kernel
theorem sub6_627 : sub6 [3, -1, 0] = true := by decide +kernel
theorem sub6_628 : sub6 [3, -1, 1] = true := by decide +kernel
theorem sub6_629 : sub6 [3, -1, 2] = true := by decide +kernel
theorem sub6_630 : sub6 [3, -1, 3] = true := by decide +kernel
theorem sub6_631 : sub6 [3, -1, 4] = true := by decide +kernel
theorem sub6_632 : sub6 [3, -1, 5] = true := by decide +kernel
theorem sub6_633 : sub6 [3, 0, -9] = true := by decide +kernel
theorem sub6_634 : sub6 [3, 0, -8] = true := by decide +kernel
theorem sub6_635 : sub6 [3, 0, -7] = true := by decide +kernel
theorem sub6_636 : sub6 [3, 0, -6] = true := by decide +kernel
theorem sub6_637 : sub6 [3, 0, -5] = true := by decide +kernel
theorem sub6_638 : sub6 [3, 0, -4] = true := by decide +kernel
theorem sub6_639 : sub6 [3, 0, -3] = true := by decide +kernel
theorem sb6_19 : ∀ q ∈ blk6_19, sub6 q = true := by
  unfold blk6_19
  exact List.forall_mem_cons.2 ⟨sub6_608, List.forall_mem_cons.2 ⟨sub6_609, List.forall_mem_cons.2 ⟨sub6_610, List.forall_mem_cons.2 ⟨sub6_611, List.forall_mem_cons.2 ⟨sub6_612, List.forall_mem_cons.2 ⟨sub6_613, List.forall_mem_cons.2 ⟨sub6_614, List.forall_mem_cons.2 ⟨sub6_615, List.forall_mem_cons.2 ⟨sub6_616, List.forall_mem_cons.2 ⟨sub6_617, List.forall_mem_cons.2 ⟨sub6_618, List.forall_mem_cons.2 ⟨sub6_619, List.forall_mem_cons.2 ⟨sub6_620, List.forall_mem_cons.2 ⟨sub6_621, List.forall_mem_cons.2 ⟨sub6_622, List.forall_mem_cons.2 ⟨sub6_623, List.forall_mem_cons.2 ⟨sub6_624, List.forall_mem_cons.2 ⟨sub6_625, List.forall_mem_cons.2 ⟨sub6_626, List.forall_mem_cons.2 ⟨sub6_627, List.forall_mem_cons.2 ⟨sub6_628, List.forall_mem_cons.2 ⟨sub6_629, List.forall_mem_cons.2 ⟨sub6_630, List.forall_mem_cons.2 ⟨sub6_631, List.forall_mem_cons.2 ⟨sub6_632, List.forall_mem_cons.2 ⟨sub6_633, List.forall_mem_cons.2 ⟨sub6_634, List.forall_mem_cons.2 ⟨sub6_635, List.forall_mem_cons.2 ⟨sub6_636, List.forall_mem_cons.2 ⟨sub6_637, List.forall_mem_cons.2 ⟨sub6_638, List.forall_mem_cons.2 ⟨sub6_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_640 : sub6 [3, 0, -2] = true := by decide +kernel
theorem sub6_641 : sub6 [3, 0, -1] = true := by decide +kernel
theorem sub6_642 : sub6 [3, 0, 0] = true := by decide +kernel
theorem sub6_643 : sub6 [3, 0, 1] = true := by decide +kernel
theorem sub6_644 : sub6 [3, 0, 2] = true := by decide +kernel
theorem sub6_645 : sub6 [3, 0, 3] = true := by decide +kernel
theorem sub6_646 : sub6 [3, 0, 4] = true := by decide +kernel
theorem sub6_647 : sub6 [3, 0, 5] = true := by decide +kernel
theorem sub6_648 : sub6 [3, 1, -9] = true := by decide +kernel
theorem sub6_649 : sub6 [3, 1, -8] = true := by decide +kernel
theorem sub6_650 : sub6 [3, 1, -7] = true := by decide +kernel
theorem sub6_651 : sub6 [3, 1, -6] = true := by decide +kernel
theorem sub6_652 : sub6 [3, 1, -5] = true := by decide +kernel
theorem sub6_653 : sub6 [3, 1, -4] = true := by decide +kernel
theorem sub6_654 : sub6 [3, 1, -3] = true := by decide +kernel
theorem sub6_655 : sub6 [3, 1, -2] = true := by decide +kernel
theorem sub6_656 : sub6 [3, 1, -1] = true := by decide +kernel
theorem sub6_657 : sub6 [3, 1, 0] = true := by decide +kernel
theorem sub6_658 : sub6 [3, 1, 1] = true := by decide +kernel
theorem sub6_659 : sub6 [3, 1, 2] = true := by decide +kernel
theorem sub6_660 : sub6 [3, 1, 3] = true := by decide +kernel
theorem sub6_661 : sub6 [3, 1, 4] = true := by decide +kernel
theorem sub6_662 : sub6 [3, 1, 5] = true := by decide +kernel
theorem sub6_663 : sub6 [3, 2, -9] = true := by decide +kernel
theorem sub6_664 : sub6 [3, 2, -8] = true := by decide +kernel
theorem sub6_665 : sub6 [3, 2, -7] = true := by decide +kernel
theorem sub6_666 : sub6 [3, 2, -6] = true := by decide +kernel
theorem sub6_667 : sub6 [3, 2, -5] = true := by decide +kernel
theorem sub6_668 : sub6 [3, 2, -4] = true := by decide +kernel
theorem sub6_669 : sub6 [3, 2, -3] = true := by decide +kernel
theorem sub6_670 : sub6 [3, 2, -2] = true := by decide +kernel
theorem sub6_671 : sub6 [3, 2, -1] = true := by decide +kernel
theorem sb6_20 : ∀ q ∈ blk6_20, sub6 q = true := by
  unfold blk6_20
  exact List.forall_mem_cons.2 ⟨sub6_640, List.forall_mem_cons.2 ⟨sub6_641, List.forall_mem_cons.2 ⟨sub6_642, List.forall_mem_cons.2 ⟨sub6_643, List.forall_mem_cons.2 ⟨sub6_644, List.forall_mem_cons.2 ⟨sub6_645, List.forall_mem_cons.2 ⟨sub6_646, List.forall_mem_cons.2 ⟨sub6_647, List.forall_mem_cons.2 ⟨sub6_648, List.forall_mem_cons.2 ⟨sub6_649, List.forall_mem_cons.2 ⟨sub6_650, List.forall_mem_cons.2 ⟨sub6_651, List.forall_mem_cons.2 ⟨sub6_652, List.forall_mem_cons.2 ⟨sub6_653, List.forall_mem_cons.2 ⟨sub6_654, List.forall_mem_cons.2 ⟨sub6_655, List.forall_mem_cons.2 ⟨sub6_656, List.forall_mem_cons.2 ⟨sub6_657, List.forall_mem_cons.2 ⟨sub6_658, List.forall_mem_cons.2 ⟨sub6_659, List.forall_mem_cons.2 ⟨sub6_660, List.forall_mem_cons.2 ⟨sub6_661, List.forall_mem_cons.2 ⟨sub6_662, List.forall_mem_cons.2 ⟨sub6_663, List.forall_mem_cons.2 ⟨sub6_664, List.forall_mem_cons.2 ⟨sub6_665, List.forall_mem_cons.2 ⟨sub6_666, List.forall_mem_cons.2 ⟨sub6_667, List.forall_mem_cons.2 ⟨sub6_668, List.forall_mem_cons.2 ⟨sub6_669, List.forall_mem_cons.2 ⟨sub6_670, List.forall_mem_cons.2 ⟨sub6_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_672 : sub6 [3, 2, 0] = true := by decide +kernel
theorem sub6_673 : sub6 [3, 2, 1] = true := by decide +kernel
theorem sub6_674 : sub6 [3, 2, 2] = true := by decide +kernel
theorem sub6_675 : sub6 [3, 2, 3] = true := by decide +kernel
theorem sub6_676 : sub6 [3, 2, 4] = true := by decide +kernel
theorem sub6_677 : sub6 [3, 3] = true := by decide +kernel
theorem sub6_678 : sub6 [3, 4] = true := by decide +kernel
theorem sub6_679 : sub6 [4, -3] = true := by decide +kernel
theorem sub6_680 : sub6 [4, -2] = true := by decide +kernel
theorem sub6_681 : sub6 [4, -1] = true := by decide +kernel
theorem sub6_682 : sub6 [4, 0] = true := by decide +kernel
theorem sub6_683 : sub6 [4, 1] = true := by decide +kernel
theorem sub6_684 : sub6 [4, 2] = true := by decide +kernel
theorem sub6_685 : sub6 [4, 3] = true := by decide +kernel
theorem sub6_686 : sub6 [5] = true := by decide +kernel
theorem sb6_21 : ∀ q ∈ blk6_21, sub6 q = true := by
  unfold blk6_21
  exact List.forall_mem_cons.2 ⟨sub6_672, List.forall_mem_cons.2 ⟨sub6_673, List.forall_mem_cons.2 ⟨sub6_674, List.forall_mem_cons.2 ⟨sub6_675, List.forall_mem_cons.2 ⟨sub6_676, List.forall_mem_cons.2 ⟨sub6_677, List.forall_mem_cons.2 ⟨sub6_678, List.forall_mem_cons.2 ⟨sub6_679, List.forall_mem_cons.2 ⟨sub6_680, List.forall_mem_cons.2 ⟨sub6_681, List.forall_mem_cons.2 ⟨sub6_682, List.forall_mem_cons.2 ⟨sub6_683, List.forall_mem_cons.2 ⟨sub6_684, List.forall_mem_cons.2 ⟨sub6_685, List.forall_mem_cons.2 ⟨sub6_686, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_0 : sub7 [-6, -3] = true := by decide +kernel
theorem sub7_1 : sub7 [-6, -2] = true := by decide +kernel
theorem sub7_2 : sub7 [-6, -1] = true := by decide +kernel
theorem sub7_3 : sub7 [-6, 0] = true := by decide +kernel
theorem sub7_4 : sub7 [-6, 1] = true := by decide +kernel
theorem sub7_5 : sub7 [-6, 2] = true := by decide +kernel
theorem sub7_6 : sub7 [-6, 3] = true := by decide +kernel
theorem sub7_7 : sub7 [-5, -4] = true := by decide +kernel
theorem sub7_8 : sub7 [-5, -3] = true := by decide +kernel
theorem sub7_9 : sub7 [-5, -2] = true := by decide +kernel
theorem sub7_10 : sub7 [-5, -1] = true := by decide +kernel
theorem sub7_11 : sub7 [-5, 0] = true := by decide +kernel
theorem sub7_12 : sub7 [-5, 1] = true := by decide +kernel
theorem sub7_13 : sub7 [-5, 2] = true := by decide +kernel
theorem sub7_14 : sub7 [-5, 3] = true := by decide +kernel
theorem sub7_15 : sub7 [-5, 4] = true := by decide +kernel
theorem sub7_16 : sub7 [-5, 5] = true := by decide +kernel
theorem sub7_17 : sub7 [-4, -5] = true := by decide +kernel
theorem sub7_18 : sub7 [-4, -4] = true := by decide +kernel
theorem sub7_19 : sub7 [-4, -3] = true := by decide +kernel
theorem sub7_20 : sub7 [-4, -2] = true := by decide +kernel
theorem sub7_21 : sub7 [-4, -1] = true := by decide +kernel
theorem sub7_22 : sub7 [-4, 0] = true := by decide +kernel
theorem sub7_23 : sub7 [-4, 1, -8] = true := by decide +kernel
theorem sub7_24 : sub7 [-4, 1, -7] = true := by decide +kernel
theorem sub7_25 : sub7 [-4, 1, -6] = true := by decide +kernel
theorem sub7_26 : sub7 [-4, 1, -5] = true := by decide +kernel
theorem sub7_27 : sub7 [-4, 1, -4] = true := by decide +kernel
theorem sub7_28 : sub7 [-4, 1, -3] = true := by decide +kernel
theorem sub7_29 : sub7 [-4, 1, -2] = true := by decide +kernel
theorem sub7_30 : sub7 [-4, 1, -1] = true := by decide +kernel
theorem sub7_31 : sub7 [-4, 1, 0] = true := by decide +kernel
theorem sb7_0 : ∀ q ∈ blk7_0, sub7 q = true := by
  unfold blk7_0
  exact List.forall_mem_cons.2 ⟨sub7_0, List.forall_mem_cons.2 ⟨sub7_1, List.forall_mem_cons.2 ⟨sub7_2, List.forall_mem_cons.2 ⟨sub7_3, List.forall_mem_cons.2 ⟨sub7_4, List.forall_mem_cons.2 ⟨sub7_5, List.forall_mem_cons.2 ⟨sub7_6, List.forall_mem_cons.2 ⟨sub7_7, List.forall_mem_cons.2 ⟨sub7_8, List.forall_mem_cons.2 ⟨sub7_9, List.forall_mem_cons.2 ⟨sub7_10, List.forall_mem_cons.2 ⟨sub7_11, List.forall_mem_cons.2 ⟨sub7_12, List.forall_mem_cons.2 ⟨sub7_13, List.forall_mem_cons.2 ⟨sub7_14, List.forall_mem_cons.2 ⟨sub7_15, List.forall_mem_cons.2 ⟨sub7_16, List.forall_mem_cons.2 ⟨sub7_17, List.forall_mem_cons.2 ⟨sub7_18, List.forall_mem_cons.2 ⟨sub7_19, List.forall_mem_cons.2 ⟨sub7_20, List.forall_mem_cons.2 ⟨sub7_21, List.forall_mem_cons.2 ⟨sub7_22, List.forall_mem_cons.2 ⟨sub7_23, List.forall_mem_cons.2 ⟨sub7_24, List.forall_mem_cons.2 ⟨sub7_25, List.forall_mem_cons.2 ⟨sub7_26, List.forall_mem_cons.2 ⟨sub7_27, List.forall_mem_cons.2 ⟨sub7_28, List.forall_mem_cons.2 ⟨sub7_29, List.forall_mem_cons.2 ⟨sub7_30, List.forall_mem_cons.2 ⟨sub7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_32 : sub7 [-4, 1, 1] = true := by decide +kernel
theorem sub7_33 : sub7 [-4, 1, 2] = true := by decide +kernel
theorem sub7_34 : sub7 [-4, 1, 3] = true := by decide +kernel
theorem sub7_35 : sub7 [-4, 1, 4] = true := by decide +kernel
theorem sub7_36 : sub7 [-4, 1, 5] = true := by decide +kernel
theorem sub7_37 : sub7 [-4, 1, 6] = true := by decide +kernel
theorem sub7_38 : sub7 [-4, 2] = true := by decide +kernel
theorem sub7_39 : sub7 [-4, 3] = true := by decide +kernel
theorem sub7_40 : sub7 [-4, 4] = true := by decide +kernel
theorem sub7_41 : sub7 [-4, 5] = true := by decide +kernel
theorem sub7_42 : sub7 [-4, 6] = true := by decide +kernel
theorem sub7_43 : sub7 [-3, -6] = true := by decide +kernel
theorem sub7_44 : sub7 [-3, -5] = true := by decide +kernel
theorem sub7_45 : sub7 [-3, -4] = true := by decide +kernel
theorem sub7_46 : sub7 [-3, -3] = true := by decide +kernel
theorem sub7_47 : sub7 [-3, -2, -9] = true := by decide +kernel
theorem sub7_48 : sub7 [-3, -2, -8] = true := by decide +kernel
theorem sub7_49 : sub7 [-3, -2, -7] = true := by decide +kernel
theorem sub7_50 : sub7 [-3, -2, -6] = true := by decide +kernel
theorem sub7_51 : sub7 [-3, -2, -5] = true := by decide +kernel
theorem sub7_52 : sub7 [-3, -2, -4] = true := by decide +kernel
theorem sub7_53 : sub7 [-3, -2, -3] = true := by decide +kernel
theorem sub7_54 : sub7 [-3, -2, -2] = true := by decide +kernel
theorem sub7_55 : sub7 [-3, -2, -1] = true := by decide +kernel
theorem sub7_56 : sub7 [-3, -2, 0] = true := by decide +kernel
theorem sub7_57 : sub7 [-3, -2, 1] = true := by decide +kernel
theorem sub7_58 : sub7 [-3, -2, 2] = true := by decide +kernel
theorem sub7_59 : sub7 [-3, -2, 3] = true := by decide +kernel
theorem sub7_60 : sub7 [-3, -2, 4] = true := by decide +kernel
theorem sub7_61 : sub7 [-3, -2, 5] = true := by decide +kernel
theorem sub7_62 : sub7 [-3, -1, -9] = true := by decide +kernel
theorem sub7_63 : sub7 [-3, -1, -8] = true := by decide +kernel
theorem sb7_1 : ∀ q ∈ blk7_1, sub7 q = true := by
  unfold blk7_1
  exact List.forall_mem_cons.2 ⟨sub7_32, List.forall_mem_cons.2 ⟨sub7_33, List.forall_mem_cons.2 ⟨sub7_34, List.forall_mem_cons.2 ⟨sub7_35, List.forall_mem_cons.2 ⟨sub7_36, List.forall_mem_cons.2 ⟨sub7_37, List.forall_mem_cons.2 ⟨sub7_38, List.forall_mem_cons.2 ⟨sub7_39, List.forall_mem_cons.2 ⟨sub7_40, List.forall_mem_cons.2 ⟨sub7_41, List.forall_mem_cons.2 ⟨sub7_42, List.forall_mem_cons.2 ⟨sub7_43, List.forall_mem_cons.2 ⟨sub7_44, List.forall_mem_cons.2 ⟨sub7_45, List.forall_mem_cons.2 ⟨sub7_46, List.forall_mem_cons.2 ⟨sub7_47, List.forall_mem_cons.2 ⟨sub7_48, List.forall_mem_cons.2 ⟨sub7_49, List.forall_mem_cons.2 ⟨sub7_50, List.forall_mem_cons.2 ⟨sub7_51, List.forall_mem_cons.2 ⟨sub7_52, List.forall_mem_cons.2 ⟨sub7_53, List.forall_mem_cons.2 ⟨sub7_54, List.forall_mem_cons.2 ⟨sub7_55, List.forall_mem_cons.2 ⟨sub7_56, List.forall_mem_cons.2 ⟨sub7_57, List.forall_mem_cons.2 ⟨sub7_58, List.forall_mem_cons.2 ⟨sub7_59, List.forall_mem_cons.2 ⟨sub7_60, List.forall_mem_cons.2 ⟨sub7_61, List.forall_mem_cons.2 ⟨sub7_62, List.forall_mem_cons.2 ⟨sub7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_64 : sub7 [-3, -1, -7] = true := by decide +kernel
theorem sub7_65 : sub7 [-3, -1, -6] = true := by decide +kernel
theorem sub7_66 : sub7 [-3, -1, -5] = true := by decide +kernel
theorem sub7_67 : sub7 [-3, -1, -4] = true := by decide +kernel
theorem sub7_68 : sub7 [-3, -1, -3] = true := by decide +kernel
theorem sub7_69 : sub7 [-3, -1, -2] = true := by decide +kernel
theorem sub7_70 : sub7 [-3, -1, -1] = true := by decide +kernel
theorem sub7_71 : sub7 [-3, -1, 0] = true := by decide +kernel
theorem sub7_72 : sub7 [-3, -1, 1] = true := by decide +kernel
theorem sub7_73 : sub7 [-3, -1, 2] = true := by decide +kernel
theorem sub7_74 : sub7 [-3, -1, 3] = true := by decide +kernel
theorem sub7_75 : sub7 [-3, -1, 4] = true := by decide +kernel
theorem sub7_76 : sub7 [-3, -1, 5] = true := by decide +kernel
theorem sub7_77 : sub7 [-3, -1, 6] = true := by decide +kernel
theorem sub7_78 : sub7 [-3, 0, -9] = true := by decide +kernel
theorem sub7_79 : sub7 [-3, 0, -8] = true := by decide +kernel
theorem sub7_80 : sub7 [-3, 0, -7] = true := by decide +kernel
theorem sub7_81 : sub7 [-3, 0, -6] = true := by decide +kernel
theorem sub7_82 : sub7 [-3, 0, -5] = true := by decide +kernel
theorem sub7_83 : sub7 [-3, 0, -4] = true := by decide +kernel
theorem sub7_84 : sub7 [-3, 0, -3] = true := by decide +kernel
theorem sub7_85 : sub7 [-3, 0, -2] = true := by decide +kernel
theorem sub7_86 : sub7 [-3, 0, -1] = true := by decide +kernel
theorem sub7_87 : sub7 [-3, 0, 0] = true := by decide +kernel
theorem sub7_88 : sub7 [-3, 0, 1] = true := by decide +kernel
theorem sub7_89 : sub7 [-3, 0, 2] = true := by decide +kernel
theorem sub7_90 : sub7 [-3, 0, 3] = true := by decide +kernel
theorem sub7_91 : sub7 [-3, 0, 4] = true := by decide +kernel
theorem sub7_92 : sub7 [-3, 0, 5] = true := by decide +kernel
theorem sub7_93 : sub7 [-3, 0, 6] = true := by decide +kernel
theorem sub7_94 : sub7 [-3, 1, -8] = true := by decide +kernel
theorem sub7_95 : sub7 [-3, 1, -7] = true := by decide +kernel
theorem sb7_2 : ∀ q ∈ blk7_2, sub7 q = true := by
  unfold blk7_2
  exact List.forall_mem_cons.2 ⟨sub7_64, List.forall_mem_cons.2 ⟨sub7_65, List.forall_mem_cons.2 ⟨sub7_66, List.forall_mem_cons.2 ⟨sub7_67, List.forall_mem_cons.2 ⟨sub7_68, List.forall_mem_cons.2 ⟨sub7_69, List.forall_mem_cons.2 ⟨sub7_70, List.forall_mem_cons.2 ⟨sub7_71, List.forall_mem_cons.2 ⟨sub7_72, List.forall_mem_cons.2 ⟨sub7_73, List.forall_mem_cons.2 ⟨sub7_74, List.forall_mem_cons.2 ⟨sub7_75, List.forall_mem_cons.2 ⟨sub7_76, List.forall_mem_cons.2 ⟨sub7_77, List.forall_mem_cons.2 ⟨sub7_78, List.forall_mem_cons.2 ⟨sub7_79, List.forall_mem_cons.2 ⟨sub7_80, List.forall_mem_cons.2 ⟨sub7_81, List.forall_mem_cons.2 ⟨sub7_82, List.forall_mem_cons.2 ⟨sub7_83, List.forall_mem_cons.2 ⟨sub7_84, List.forall_mem_cons.2 ⟨sub7_85, List.forall_mem_cons.2 ⟨sub7_86, List.forall_mem_cons.2 ⟨sub7_87, List.forall_mem_cons.2 ⟨sub7_88, List.forall_mem_cons.2 ⟨sub7_89, List.forall_mem_cons.2 ⟨sub7_90, List.forall_mem_cons.2 ⟨sub7_91, List.forall_mem_cons.2 ⟨sub7_92, List.forall_mem_cons.2 ⟨sub7_93, List.forall_mem_cons.2 ⟨sub7_94, List.forall_mem_cons.2 ⟨sub7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_96 : sub7 [-3, 1, -6] = true := by decide +kernel
theorem sub7_97 : sub7 [-3, 1, -5] = true := by decide +kernel
theorem sub7_98 : sub7 [-3, 1, -4] = true := by decide +kernel
theorem sub7_99 : sub7 [-3, 1, -3] = true := by decide +kernel
theorem sub7_100 : sub7 [-3, 1, -2] = true := by decide +kernel
theorem sub7_101 : sub7 [-3, 1, -1] = true := by decide +kernel
theorem sub7_102 : sub7 [-3, 1, 0] = true := by decide +kernel
theorem sub7_103 : sub7 [-3, 1, 1] = true := by decide +kernel
theorem sub7_104 : sub7 [-3, 1, 2] = true := by decide +kernel
theorem sub7_105 : sub7 [-3, 1, 3] = true := by decide +kernel
theorem sub7_106 : sub7 [-3, 1, 4] = true := by decide +kernel
theorem sub7_107 : sub7 [-3, 1, 5] = true := by decide +kernel
theorem sub7_108 : sub7 [-3, 1, 6] = true := by decide +kernel
theorem sub7_109 : sub7 [-3, 1, 7] = true := by decide +kernel
theorem sub7_110 : sub7 [-3, 2, -8] = true := by decide +kernel
theorem sub7_111 : sub7 [-3, 2, -7] = true := by decide +kernel
theorem sub7_112 : sub7 [-3, 2, -6] = true := by decide +kernel
theorem sub7_113 : sub7 [-3, 2, -5] = true := by decide +kernel
theorem sub7_114 : sub7 [-3, 2, -4] = true := by decide +kernel
theorem sub7_115 : sub7 [-3, 2, -3] = true := by decide +kernel
theorem sub7_116 : sub7 [-3, 2, -2] = true := by decide +kernel
theorem sub7_117 : sub7 [-3, 2, -1] = true := by decide +kernel
theorem sub7_118 : sub7 [-3, 2, 0] = true := by decide +kernel
theorem sub7_119 : sub7 [-3, 2, 1] = true := by decide +kernel
theorem sub7_120 : sub7 [-3, 2, 2] = true := by decide +kernel
theorem sub7_121 : sub7 [-3, 2, 3] = true := by decide +kernel
theorem sub7_122 : sub7 [-3, 2, 4] = true := by decide +kernel
theorem sub7_123 : sub7 [-3, 2, 5] = true := by decide +kernel
theorem sub7_124 : sub7 [-3, 2, 6] = true := by decide +kernel
theorem sub7_125 : sub7 [-3, 2, 7] = true := by decide +kernel
theorem sub7_126 : sub7 [-3, 3, -7] = true := by decide +kernel
theorem sub7_127 : sub7 [-3, 3, -6] = true := by decide +kernel
theorem sb7_3 : ∀ q ∈ blk7_3, sub7 q = true := by
  unfold blk7_3
  exact List.forall_mem_cons.2 ⟨sub7_96, List.forall_mem_cons.2 ⟨sub7_97, List.forall_mem_cons.2 ⟨sub7_98, List.forall_mem_cons.2 ⟨sub7_99, List.forall_mem_cons.2 ⟨sub7_100, List.forall_mem_cons.2 ⟨sub7_101, List.forall_mem_cons.2 ⟨sub7_102, List.forall_mem_cons.2 ⟨sub7_103, List.forall_mem_cons.2 ⟨sub7_104, List.forall_mem_cons.2 ⟨sub7_105, List.forall_mem_cons.2 ⟨sub7_106, List.forall_mem_cons.2 ⟨sub7_107, List.forall_mem_cons.2 ⟨sub7_108, List.forall_mem_cons.2 ⟨sub7_109, List.forall_mem_cons.2 ⟨sub7_110, List.forall_mem_cons.2 ⟨sub7_111, List.forall_mem_cons.2 ⟨sub7_112, List.forall_mem_cons.2 ⟨sub7_113, List.forall_mem_cons.2 ⟨sub7_114, List.forall_mem_cons.2 ⟨sub7_115, List.forall_mem_cons.2 ⟨sub7_116, List.forall_mem_cons.2 ⟨sub7_117, List.forall_mem_cons.2 ⟨sub7_118, List.forall_mem_cons.2 ⟨sub7_119, List.forall_mem_cons.2 ⟨sub7_120, List.forall_mem_cons.2 ⟨sub7_121, List.forall_mem_cons.2 ⟨sub7_122, List.forall_mem_cons.2 ⟨sub7_123, List.forall_mem_cons.2 ⟨sub7_124, List.forall_mem_cons.2 ⟨sub7_125, List.forall_mem_cons.2 ⟨sub7_126, List.forall_mem_cons.2 ⟨sub7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_128 : sub7 [-3, 3, -5] = true := by decide +kernel
theorem sub7_129 : sub7 [-3, 3, -4] = true := by decide +kernel
theorem sub7_130 : sub7 [-3, 3, -3] = true := by decide +kernel
theorem sub7_131 : sub7 [-3, 3, -2] = true := by decide +kernel
theorem sub7_132 : sub7 [-3, 3, -1] = true := by decide +kernel
theorem sub7_133 : sub7 [-3, 3, 0] = true := by decide +kernel
theorem sub7_134 : sub7 [-3, 3, 1] = true := by decide +kernel
theorem sub7_135 : sub7 [-3, 3, 2] = true := by decide +kernel
theorem sub7_136 : sub7 [-3, 3, 3] = true := by decide +kernel
theorem sub7_137 : sub7 [-3, 3, 4] = true := by decide +kernel
theorem sub7_138 : sub7 [-3, 3, 5] = true := by decide +kernel
theorem sub7_139 : sub7 [-3, 3, 6] = true := by decide +kernel
theorem sub7_140 : sub7 [-3, 3, 7] = true := by decide +kernel
theorem sub7_141 : sub7 [-3, 4] = true := by decide +kernel
theorem sub7_142 : sub7 [-3, 5] = true := by decide +kernel
theorem sub7_143 : sub7 [-3, 6] = true := by decide +kernel
theorem sub7_144 : sub7 [-2, -7] = true := by decide +kernel
theorem sub7_145 : sub7 [-2, -6] = true := by decide +kernel
theorem sub7_146 : sub7 [-2, -5] = true := by decide +kernel
theorem sub7_147 : sub7 [-2, -4] = true := by decide +kernel
theorem sub7_148 : sub7 [-2, -3, -9] = true := by decide +kernel
theorem sub7_149 : sub7 [-2, -3, -8] = true := by decide +kernel
theorem sub7_150 : sub7 [-2, -3, -7] = true := by decide +kernel
theorem sub7_151 : sub7 [-2, -3, -6] = true := by decide +kernel
theorem sub7_152 : sub7 [-2, -3, -5] = true := by decide +kernel
theorem sub7_153 : sub7 [-2, -3, -4] = true := by decide +kernel
theorem sub7_154 : sub7 [-2, -3, -3] = true := by decide +kernel
theorem sub7_155 : sub7 [-2, -3, -2] = true := by decide +kernel
theorem sub7_156 : sub7 [-2, -3, -1] = true := by decide +kernel
theorem sub7_157 : sub7 [-2, -3, 0] = true := by decide +kernel
theorem sub7_158 : sub7 [-2, -3, 1] = true := by decide +kernel
theorem sub7_159 : sub7 [-2, -3, 2] = true := by decide +kernel
theorem sb7_4 : ∀ q ∈ blk7_4, sub7 q = true := by
  unfold blk7_4
  exact List.forall_mem_cons.2 ⟨sub7_128, List.forall_mem_cons.2 ⟨sub7_129, List.forall_mem_cons.2 ⟨sub7_130, List.forall_mem_cons.2 ⟨sub7_131, List.forall_mem_cons.2 ⟨sub7_132, List.forall_mem_cons.2 ⟨sub7_133, List.forall_mem_cons.2 ⟨sub7_134, List.forall_mem_cons.2 ⟨sub7_135, List.forall_mem_cons.2 ⟨sub7_136, List.forall_mem_cons.2 ⟨sub7_137, List.forall_mem_cons.2 ⟨sub7_138, List.forall_mem_cons.2 ⟨sub7_139, List.forall_mem_cons.2 ⟨sub7_140, List.forall_mem_cons.2 ⟨sub7_141, List.forall_mem_cons.2 ⟨sub7_142, List.forall_mem_cons.2 ⟨sub7_143, List.forall_mem_cons.2 ⟨sub7_144, List.forall_mem_cons.2 ⟨sub7_145, List.forall_mem_cons.2 ⟨sub7_146, List.forall_mem_cons.2 ⟨sub7_147, List.forall_mem_cons.2 ⟨sub7_148, List.forall_mem_cons.2 ⟨sub7_149, List.forall_mem_cons.2 ⟨sub7_150, List.forall_mem_cons.2 ⟨sub7_151, List.forall_mem_cons.2 ⟨sub7_152, List.forall_mem_cons.2 ⟨sub7_153, List.forall_mem_cons.2 ⟨sub7_154, List.forall_mem_cons.2 ⟨sub7_155, List.forall_mem_cons.2 ⟨sub7_156, List.forall_mem_cons.2 ⟨sub7_157, List.forall_mem_cons.2 ⟨sub7_158, List.forall_mem_cons.2 ⟨sub7_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_160 : sub7 [-2, -3, 3] = true := by decide +kernel
theorem sub7_161 : sub7 [-2, -3, 4] = true := by decide +kernel
theorem sub7_162 : sub7 [-2, -3, 5] = true := by decide +kernel
theorem sub7_163 : sub7 [-2, -2, -9] = true := by decide +kernel
theorem sub7_164 : sub7 [-2, -2, -8] = true := by decide +kernel
theorem sub7_165 : sub7 [-2, -2, -7] = true := by decide +kernel
theorem sub7_166 : sub7 [-2, -2, -6] = true := by decide +kernel
theorem sub7_167 : sub7 [-2, -2, -5] = true := by decide +kernel
theorem sub7_168 : sub7 [-2, -2, -4] = true := by decide +kernel
theorem sub7_169 : sub7 [-2, -2, -3] = true := by decide +kernel
theorem sub7_170 : sub7 [-2, -2, -2] = true := by decide +kernel
theorem sub7_171 : sub7 [-2, -2, -1] = true := by decide +kernel
theorem sub7_172 : sub7 [-2, -2, 0] = true := by decide +kernel
theorem sub7_173 : sub7 [-2, -2, 1] = true := by decide +kernel
theorem sub7_174 : sub7 [-2, -2, 2] = true := by decide +kernel
theorem sub7_175 : sub7 [-2, -2, 3] = true := by decide +kernel
theorem sub7_176 : sub7 [-2, -2, 4] = true := by decide +kernel
theorem sub7_177 : sub7 [-2, -2, 5] = true := by decide +kernel
theorem sub7_178 : sub7 [-2, -2, 6] = true := by decide +kernel
theorem sub7_179 : sub7 [-2, -1, -9] = true := by decide +kernel
theorem sub7_180 : sub7 [-2, -1, -8] = true := by decide +kernel
theorem sub7_181 : sub7 [-2, -1, -7] = true := by decide +kernel
theorem sub7_182 : sub7 [-2, -1, -6] = true := by decide +kernel
theorem sub7_183 : sub7 [-2, -1, -5] = true := by decide +kernel
theorem sub7_184 : sub7 [-2, -1, -4] = true := by decide +kernel
theorem sub7_185 : sub7 [-2, -1, -3] = true := by decide +kernel
theorem sub7_186 : sub7 [-2, -1, -2] = true := by decide +kernel
theorem sub7_187 : sub7 [-2, -1, -1] = true := by decide +kernel
theorem sub7_188 : sub7 [-2, -1, 0] = true := by decide +kernel
theorem sub7_189 : sub7 [-2, -1, 1] = true := by decide +kernel
theorem sub7_190 : sub7 [-2, -1, 2] = true := by decide +kernel
theorem sub7_191 : sub7 [-2, -1, 3] = true := by decide +kernel
theorem sb7_5 : ∀ q ∈ blk7_5, sub7 q = true := by
  unfold blk7_5
  exact List.forall_mem_cons.2 ⟨sub7_160, List.forall_mem_cons.2 ⟨sub7_161, List.forall_mem_cons.2 ⟨sub7_162, List.forall_mem_cons.2 ⟨sub7_163, List.forall_mem_cons.2 ⟨sub7_164, List.forall_mem_cons.2 ⟨sub7_165, List.forall_mem_cons.2 ⟨sub7_166, List.forall_mem_cons.2 ⟨sub7_167, List.forall_mem_cons.2 ⟨sub7_168, List.forall_mem_cons.2 ⟨sub7_169, List.forall_mem_cons.2 ⟨sub7_170, List.forall_mem_cons.2 ⟨sub7_171, List.forall_mem_cons.2 ⟨sub7_172, List.forall_mem_cons.2 ⟨sub7_173, List.forall_mem_cons.2 ⟨sub7_174, List.forall_mem_cons.2 ⟨sub7_175, List.forall_mem_cons.2 ⟨sub7_176, List.forall_mem_cons.2 ⟨sub7_177, List.forall_mem_cons.2 ⟨sub7_178, List.forall_mem_cons.2 ⟨sub7_179, List.forall_mem_cons.2 ⟨sub7_180, List.forall_mem_cons.2 ⟨sub7_181, List.forall_mem_cons.2 ⟨sub7_182, List.forall_mem_cons.2 ⟨sub7_183, List.forall_mem_cons.2 ⟨sub7_184, List.forall_mem_cons.2 ⟨sub7_185, List.forall_mem_cons.2 ⟨sub7_186, List.forall_mem_cons.2 ⟨sub7_187, List.forall_mem_cons.2 ⟨sub7_188, List.forall_mem_cons.2 ⟨sub7_189, List.forall_mem_cons.2 ⟨sub7_190, List.forall_mem_cons.2 ⟨sub7_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_192 : sub7 [-2, -1, 4] = true := by decide +kernel
theorem sub7_193 : sub7 [-2, -1, 5] = true := by decide +kernel
theorem sub7_194 : sub7 [-2, -1, 6] = true := by decide +kernel
theorem sub7_195 : sub7 [-2, -1, 7] = true := by decide +kernel
theorem sub7_196 : sub7 [-2, 0, -9] = true := by decide +kernel
theorem sub7_197 : sub7 [-2, 0, -8] = true := by decide +kernel
theorem sub7_198 : sub7 [-2, 0, -7] = true := by decide +kernel
theorem sub7_199 : sub7 [-2, 0, -6] = true := by decide +kernel
theorem sub7_200 : sub7 [-2, 0, -5] = true := by decide +kernel
theorem sub7_201 : sub7 [-2, 0, -4] = true := by decide +kernel
theorem sub7_202 : sub7 [-2, 0, -3] = true := by decide +kernel
theorem sub7_203 : sub7 [-2, 0, -2] = true := by decide +kernel
theorem sub7_204 : sub7 [-2, 0, -1] = true := by decide +kernel
theorem sub7_205 : sub7 [-2, 0, 0] = true := by decide +kernel
theorem sub7_206 : sub7 [-2, 0, 1] = true := by decide +kernel
theorem sub7_207 : sub7 [-2, 0, 2] = true := by decide +kernel
theorem sub7_208 : sub7 [-2, 0, 3] = true := by decide +kernel
theorem sub7_209 : sub7 [-2, 0, 4] = true := by decide +kernel
theorem sub7_210 : sub7 [-2, 0, 5] = true := by decide +kernel
theorem sub7_211 : sub7 [-2, 0, 6] = true := by decide +kernel
theorem sub7_212 : sub7 [-2, 0, 7] = true := by decide +kernel
theorem sub7_213 : sub7 [-2, 1, -9] = true := by decide +kernel
theorem sub7_214 : sub7 [-2, 1, -8] = true := by decide +kernel
theorem sub7_215 : sub7 [-2, 1, -7] = true := by decide +kernel
theorem sub7_216 : sub7 [-2, 1, -6] = true := by decide +kernel
theorem sub7_217 : sub7 [-2, 1, -5] = true := by decide +kernel
theorem sub7_218 : sub7 [-2, 1, -4] = true := by decide +kernel
theorem sub7_219 : sub7 [-2, 1, -3] = true := by decide +kernel
theorem sub7_220 : sub7 [-2, 1, -2] = true := by decide +kernel
theorem sub7_221 : sub7 [-2, 1, -1] = true := by decide +kernel
theorem sub7_222 : sub7 [-2, 1, 0] = true := by decide +kernel
theorem sub7_223 : sub7 [-2, 1, 1] = true := by decide +kernel
theorem sb7_6 : ∀ q ∈ blk7_6, sub7 q = true := by
  unfold blk7_6
  exact List.forall_mem_cons.2 ⟨sub7_192, List.forall_mem_cons.2 ⟨sub7_193, List.forall_mem_cons.2 ⟨sub7_194, List.forall_mem_cons.2 ⟨sub7_195, List.forall_mem_cons.2 ⟨sub7_196, List.forall_mem_cons.2 ⟨sub7_197, List.forall_mem_cons.2 ⟨sub7_198, List.forall_mem_cons.2 ⟨sub7_199, List.forall_mem_cons.2 ⟨sub7_200, List.forall_mem_cons.2 ⟨sub7_201, List.forall_mem_cons.2 ⟨sub7_202, List.forall_mem_cons.2 ⟨sub7_203, List.forall_mem_cons.2 ⟨sub7_204, List.forall_mem_cons.2 ⟨sub7_205, List.forall_mem_cons.2 ⟨sub7_206, List.forall_mem_cons.2 ⟨sub7_207, List.forall_mem_cons.2 ⟨sub7_208, List.forall_mem_cons.2 ⟨sub7_209, List.forall_mem_cons.2 ⟨sub7_210, List.forall_mem_cons.2 ⟨sub7_211, List.forall_mem_cons.2 ⟨sub7_212, List.forall_mem_cons.2 ⟨sub7_213, List.forall_mem_cons.2 ⟨sub7_214, List.forall_mem_cons.2 ⟨sub7_215, List.forall_mem_cons.2 ⟨sub7_216, List.forall_mem_cons.2 ⟨sub7_217, List.forall_mem_cons.2 ⟨sub7_218, List.forall_mem_cons.2 ⟨sub7_219, List.forall_mem_cons.2 ⟨sub7_220, List.forall_mem_cons.2 ⟨sub7_221, List.forall_mem_cons.2 ⟨sub7_222, List.forall_mem_cons.2 ⟨sub7_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_224 : sub7 [-2, 1, 2] = true := by decide +kernel
theorem sub7_225 : sub7 [-2, 1, 3] = true := by decide +kernel
theorem sub7_226 : sub7 [-2, 1, 4] = true := by decide +kernel
theorem sub7_227 : sub7 [-2, 1, 5] = true := by decide +kernel
theorem sub7_228 : sub7 [-2, 1, 6] = true := by decide +kernel
theorem sub7_229 : sub7 [-2, 1, 7] = true := by decide +kernel
theorem sub7_230 : sub7 [-2, 2, -8] = true := by decide +kernel
theorem sub7_231 : sub7 [-2, 2, -7] = true := by decide +kernel
theorem sub7_232 : sub7 [-2, 2, -6] = true := by decide +kernel
theorem sub7_233 : sub7 [-2, 2, -5] = true := by decide +kernel
theorem sub7_234 : sub7 [-2, 2, -4] = true := by decide +kernel
theorem sub7_235 : sub7 [-2, 2, -3] = true := by decide +kernel
theorem sub7_236 : sub7 [-2, 2, -2] = true := by decide +kernel
theorem sub7_237 : sub7 [-2, 2, -1] = true := by decide +kernel
theorem sub7_238 : sub7 [-2, 2, 0] = true := by decide +kernel
theorem sub7_239 : sub7 [-2, 2, 1] = true := by decide +kernel
theorem sub7_240 : sub7 [-2, 2, 2] = true := by decide +kernel
theorem sub7_241 : sub7 [-2, 2, 3] = true := by decide +kernel
theorem sub7_242 : sub7 [-2, 2, 4] = true := by decide +kernel
theorem sub7_243 : sub7 [-2, 2, 5] = true := by decide +kernel
theorem sub7_244 : sub7 [-2, 2, 6] = true := by decide +kernel
theorem sub7_245 : sub7 [-2, 2, 7] = true := by decide +kernel
theorem sub7_246 : sub7 [-2, 3, -8] = true := by decide +kernel
theorem sub7_247 : sub7 [-2, 3, -7] = true := by decide +kernel
theorem sub7_248 : sub7 [-2, 3, -6] = true := by decide +kernel
theorem sub7_249 : sub7 [-2, 3, -5] = true := by decide +kernel
theorem sub7_250 : sub7 [-2, 3, -4] = true := by decide +kernel
theorem sub7_251 : sub7 [-2, 3, -3] = true := by decide +kernel
theorem sub7_252 : sub7 [-2, 3, -2] = true := by decide +kernel
theorem sub7_253 : sub7 [-2, 3, -1] = true := by decide +kernel
theorem sub7_254 : sub7 [-2, 3, 0] = true := by decide +kernel
theorem sub7_255 : sub7 [-2, 3, 1] = true := by decide +kernel
theorem sb7_7 : ∀ q ∈ blk7_7, sub7 q = true := by
  unfold blk7_7
  exact List.forall_mem_cons.2 ⟨sub7_224, List.forall_mem_cons.2 ⟨sub7_225, List.forall_mem_cons.2 ⟨sub7_226, List.forall_mem_cons.2 ⟨sub7_227, List.forall_mem_cons.2 ⟨sub7_228, List.forall_mem_cons.2 ⟨sub7_229, List.forall_mem_cons.2 ⟨sub7_230, List.forall_mem_cons.2 ⟨sub7_231, List.forall_mem_cons.2 ⟨sub7_232, List.forall_mem_cons.2 ⟨sub7_233, List.forall_mem_cons.2 ⟨sub7_234, List.forall_mem_cons.2 ⟨sub7_235, List.forall_mem_cons.2 ⟨sub7_236, List.forall_mem_cons.2 ⟨sub7_237, List.forall_mem_cons.2 ⟨sub7_238, List.forall_mem_cons.2 ⟨sub7_239, List.forall_mem_cons.2 ⟨sub7_240, List.forall_mem_cons.2 ⟨sub7_241, List.forall_mem_cons.2 ⟨sub7_242, List.forall_mem_cons.2 ⟨sub7_243, List.forall_mem_cons.2 ⟨sub7_244, List.forall_mem_cons.2 ⟨sub7_245, List.forall_mem_cons.2 ⟨sub7_246, List.forall_mem_cons.2 ⟨sub7_247, List.forall_mem_cons.2 ⟨sub7_248, List.forall_mem_cons.2 ⟨sub7_249, List.forall_mem_cons.2 ⟨sub7_250, List.forall_mem_cons.2 ⟨sub7_251, List.forall_mem_cons.2 ⟨sub7_252, List.forall_mem_cons.2 ⟨sub7_253, List.forall_mem_cons.2 ⟨sub7_254, List.forall_mem_cons.2 ⟨sub7_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_256 : sub7 [-2, 3, 2] = true := by decide +kernel
theorem sub7_257 : sub7 [-2, 3, 3] = true := by decide +kernel
theorem sub7_258 : sub7 [-2, 3, 4] = true := by decide +kernel
theorem sub7_259 : sub7 [-2, 3, 5] = true := by decide +kernel
theorem sub7_260 : sub7 [-2, 3, 6] = true := by decide +kernel
theorem sub7_261 : sub7 [-2, 3, 7] = true := by decide +kernel
theorem sub7_262 : sub7 [-2, 4] = true := by decide +kernel
theorem sub7_263 : sub7 [-2, 5] = true := by decide +kernel
theorem sub7_264 : sub7 [-2, 6] = true := by decide +kernel
theorem sub7_265 : sub7 [-1, -7] = true := by decide +kernel
theorem sub7_266 : sub7 [-1, -6] = true := by decide +kernel
theorem sub7_267 : sub7 [-1, -5] = true := by decide +kernel
theorem sub7_268 : sub7 [-1, -4, -8] = true := by decide +kernel
theorem sub7_269 : sub7 [-1, -4, -7] = true := by decide +kernel
theorem sub7_270 : sub7 [-1, -4, -6] = true := by decide +kernel
theorem sub7_271 : sub7 [-1, -4, -5] = true := by decide +kernel
theorem sub7_272 : sub7 [-1, -4, -4] = true := by decide +kernel
theorem sub7_273 : sub7 [-1, -4, -3] = true := by decide +kernel
theorem sub7_274 : sub7 [-1, -4, -2] = true := by decide +kernel
theorem sub7_275 : sub7 [-1, -4, -1] = true := by decide +kernel
theorem sub7_276 : sub7 [-1, -4, 0] = true := by decide +kernel
theorem sub7_277 : sub7 [-1, -4, 1] = true := by decide +kernel
theorem sub7_278 : sub7 [-1, -4, 2] = true := by decide +kernel
theorem sub7_279 : sub7 [-1, -4, 3] = true := by decide +kernel
theorem sub7_280 : sub7 [-1, -4, 4] = true := by decide +kernel
theorem sub7_281 : sub7 [-1, -4, 5] = true := by decide +kernel
theorem sub7_282 : sub7 [-1, -3, -9] = true := by decide +kernel
theorem sub7_283 : sub7 [-1, -3, -8] = true := by decide +kernel
theorem sub7_284 : sub7 [-1, -3, -7] = true := by decide +kernel
theorem sub7_285 : sub7 [-1, -3, -6] = true := by decide +kernel
theorem sub7_286 : sub7 [-1, -3, -5] = true := by decide +kernel
theorem sub7_287 : sub7 [-1, -3, -4] = true := by decide +kernel
theorem sb7_8 : ∀ q ∈ blk7_8, sub7 q = true := by
  unfold blk7_8
  exact List.forall_mem_cons.2 ⟨sub7_256, List.forall_mem_cons.2 ⟨sub7_257, List.forall_mem_cons.2 ⟨sub7_258, List.forall_mem_cons.2 ⟨sub7_259, List.forall_mem_cons.2 ⟨sub7_260, List.forall_mem_cons.2 ⟨sub7_261, List.forall_mem_cons.2 ⟨sub7_262, List.forall_mem_cons.2 ⟨sub7_263, List.forall_mem_cons.2 ⟨sub7_264, List.forall_mem_cons.2 ⟨sub7_265, List.forall_mem_cons.2 ⟨sub7_266, List.forall_mem_cons.2 ⟨sub7_267, List.forall_mem_cons.2 ⟨sub7_268, List.forall_mem_cons.2 ⟨sub7_269, List.forall_mem_cons.2 ⟨sub7_270, List.forall_mem_cons.2 ⟨sub7_271, List.forall_mem_cons.2 ⟨sub7_272, List.forall_mem_cons.2 ⟨sub7_273, List.forall_mem_cons.2 ⟨sub7_274, List.forall_mem_cons.2 ⟨sub7_275, List.forall_mem_cons.2 ⟨sub7_276, List.forall_mem_cons.2 ⟨sub7_277, List.forall_mem_cons.2 ⟨sub7_278, List.forall_mem_cons.2 ⟨sub7_279, List.forall_mem_cons.2 ⟨sub7_280, List.forall_mem_cons.2 ⟨sub7_281, List.forall_mem_cons.2 ⟨sub7_282, List.forall_mem_cons.2 ⟨sub7_283, List.forall_mem_cons.2 ⟨sub7_284, List.forall_mem_cons.2 ⟨sub7_285, List.forall_mem_cons.2 ⟨sub7_286, List.forall_mem_cons.2 ⟨sub7_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C098
