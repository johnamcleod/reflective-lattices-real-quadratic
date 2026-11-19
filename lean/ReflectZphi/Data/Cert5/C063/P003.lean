import ReflectZphi.Data.Cert5.C063.Base

namespace ReflectZphi.Data.Cert5.C063
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_640 : sub3 [3, 2, -8] = true := by decide +kernel
theorem sub3_641 : sub3 [3, 2, -7] = true := by decide +kernel
theorem sub3_642 : sub3 [3, 2, -6] = true := by decide +kernel
theorem sub3_643 : sub3 [3, 2, -5] = true := by decide +kernel
theorem sub3_644 : sub3 [3, 2, -4] = true := by decide +kernel
theorem sub3_645 : sub3 [3, 2, -3] = true := by decide +kernel
theorem sub3_646 : sub3 [3, 2, -2] = true := by decide +kernel
theorem sub3_647 : sub3 [3, 2, -1] = true := by decide +kernel
theorem sub3_648 : sub3 [3, 2, 0] = true := by decide +kernel
theorem sub3_649 : sub3 [3, 2, 1] = true := by decide +kernel
theorem sub3_650 : sub3 [3, 2, 2] = true := by decide +kernel
theorem sub3_651 : sub3 [3, 2, 3] = true := by decide +kernel
theorem sub3_652 : sub3 [3, 2, 4] = true := by decide +kernel
theorem sub3_653 : sub3 [3, 2, 5] = true := by decide +kernel
theorem sub3_654 : sub3 [3, 2, 6] = true := by decide +kernel
theorem sub3_655 : sub3 [3, 3] = true := by decide +kernel
theorem sub3_656 : sub3 [3, 4] = true := by decide +kernel
theorem sub3_657 : sub3 [3, 5] = true := by decide +kernel
theorem sub3_658 : sub3 [3, 6] = true := by decide +kernel
theorem sub3_659 : sub3 [3, 7] = true := by decide +kernel
theorem sub3_660 : sub3 [3, 8] = true := by decide +kernel
theorem sub3_661 : sub3 [4, -6] = true := by decide +kernel
theorem sub3_662 : sub3 [4, -5] = true := by decide +kernel
theorem sub3_663 : sub3 [4, -4] = true := by decide +kernel
theorem sub3_664 : sub3 [4, -3] = true := by decide +kernel
theorem sub3_665 : sub3 [4, -2] = true := by decide +kernel
theorem sub3_666 : sub3 [4, -1] = true := by decide +kernel
theorem sub3_667 : sub3 [4, 0] = true := by decide +kernel
theorem sub3_668 : sub3 [4, 1] = true := by decide +kernel
theorem sub3_669 : sub3 [4, 2] = true := by decide +kernel
theorem sub3_670 : sub3 [4, 3] = true := by decide +kernel
theorem sub3_671 : sub3 [4, 4] = true := by decide +kernel
theorem sb3_20 : ∀ q ∈ blk3_20, sub3 q = true := by
  unfold blk3_20
  exact List.forall_mem_cons.2 ⟨sub3_640, List.forall_mem_cons.2 ⟨sub3_641, List.forall_mem_cons.2 ⟨sub3_642, List.forall_mem_cons.2 ⟨sub3_643, List.forall_mem_cons.2 ⟨sub3_644, List.forall_mem_cons.2 ⟨sub3_645, List.forall_mem_cons.2 ⟨sub3_646, List.forall_mem_cons.2 ⟨sub3_647, List.forall_mem_cons.2 ⟨sub3_648, List.forall_mem_cons.2 ⟨sub3_649, List.forall_mem_cons.2 ⟨sub3_650, List.forall_mem_cons.2 ⟨sub3_651, List.forall_mem_cons.2 ⟨sub3_652, List.forall_mem_cons.2 ⟨sub3_653, List.forall_mem_cons.2 ⟨sub3_654, List.forall_mem_cons.2 ⟨sub3_655, List.forall_mem_cons.2 ⟨sub3_656, List.forall_mem_cons.2 ⟨sub3_657, List.forall_mem_cons.2 ⟨sub3_658, List.forall_mem_cons.2 ⟨sub3_659, List.forall_mem_cons.2 ⟨sub3_660, List.forall_mem_cons.2 ⟨sub3_661, List.forall_mem_cons.2 ⟨sub3_662, List.forall_mem_cons.2 ⟨sub3_663, List.forall_mem_cons.2 ⟨sub3_664, List.forall_mem_cons.2 ⟨sub3_665, List.forall_mem_cons.2 ⟨sub3_666, List.forall_mem_cons.2 ⟨sub3_667, List.forall_mem_cons.2 ⟨sub3_668, List.forall_mem_cons.2 ⟨sub3_669, List.forall_mem_cons.2 ⟨sub3_670, List.forall_mem_cons.2 ⟨sub3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_672 : sub3 [4, 5] = true := by decide +kernel
theorem sub3_673 : sub3 [4, 6] = true := by decide +kernel
theorem sub3_674 : sub3 [4, 7] = true := by decide +kernel
theorem sub3_675 : sub3 [5, -5] = true := by decide +kernel
theorem sub3_676 : sub3 [5, -4] = true := by decide +kernel
theorem sub3_677 : sub3 [5, -3] = true := by decide +kernel
theorem sub3_678 : sub3 [5, -2] = true := by decide +kernel
theorem sub3_679 : sub3 [5, -1] = true := by decide +kernel
theorem sub3_680 : sub3 [5, 0] = true := by decide +kernel
theorem sub3_681 : sub3 [5, 1] = true := by decide +kernel
theorem sub3_682 : sub3 [5, 2] = true := by decide +kernel
theorem sub3_683 : sub3 [5, 3] = true := by decide +kernel
theorem sub3_684 : sub3 [5, 4] = true := by decide +kernel
theorem sub3_685 : sub3 [5, 5] = true := by decide +kernel
theorem sub3_686 : sub3 [5, 6] = true := by decide +kernel
theorem sub3_687 : sub3 [5, 7] = true := by decide +kernel
theorem sub3_688 : sub3 [6, -4] = true := by decide +kernel
theorem sub3_689 : sub3 [6, -3] = true := by decide +kernel
theorem sub3_690 : sub3 [6, -2] = true := by decide +kernel
theorem sub3_691 : sub3 [6, -1] = true := by decide +kernel
theorem sub3_692 : sub3 [6, 0] = true := by decide +kernel
theorem sub3_693 : sub3 [6, 1] = true := by decide +kernel
theorem sub3_694 : sub3 [6, 2] = true := by decide +kernel
theorem sub3_695 : sub3 [6, 3] = true := by decide +kernel
theorem sub3_696 : sub3 [6, 4] = true := by decide +kernel
theorem sub3_697 : sub3 [6, 5] = true := by decide +kernel
theorem sub3_698 : sub3 [6, 6] = true := by decide +kernel
theorem sub3_699 : sub3 [7, -2] = true := by decide +kernel
theorem sub3_700 : sub3 [7, -1] = true := by decide +kernel
theorem sub3_701 : sub3 [7, 0] = true := by decide +kernel
theorem sub3_702 : sub3 [7, 1] = true := by decide +kernel
theorem sub3_703 : sub3 [7, 2] = true := by decide +kernel
theorem sb3_21 : ∀ q ∈ blk3_21, sub3 q = true := by
  unfold blk3_21
  exact List.forall_mem_cons.2 ⟨sub3_672, List.forall_mem_cons.2 ⟨sub3_673, List.forall_mem_cons.2 ⟨sub3_674, List.forall_mem_cons.2 ⟨sub3_675, List.forall_mem_cons.2 ⟨sub3_676, List.forall_mem_cons.2 ⟨sub3_677, List.forall_mem_cons.2 ⟨sub3_678, List.forall_mem_cons.2 ⟨sub3_679, List.forall_mem_cons.2 ⟨sub3_680, List.forall_mem_cons.2 ⟨sub3_681, List.forall_mem_cons.2 ⟨sub3_682, List.forall_mem_cons.2 ⟨sub3_683, List.forall_mem_cons.2 ⟨sub3_684, List.forall_mem_cons.2 ⟨sub3_685, List.forall_mem_cons.2 ⟨sub3_686, List.forall_mem_cons.2 ⟨sub3_687, List.forall_mem_cons.2 ⟨sub3_688, List.forall_mem_cons.2 ⟨sub3_689, List.forall_mem_cons.2 ⟨sub3_690, List.forall_mem_cons.2 ⟨sub3_691, List.forall_mem_cons.2 ⟨sub3_692, List.forall_mem_cons.2 ⟨sub3_693, List.forall_mem_cons.2 ⟨sub3_694, List.forall_mem_cons.2 ⟨sub3_695, List.forall_mem_cons.2 ⟨sub3_696, List.forall_mem_cons.2 ⟨sub3_697, List.forall_mem_cons.2 ⟨sub3_698, List.forall_mem_cons.2 ⟨sub3_699, List.forall_mem_cons.2 ⟨sub3_700, List.forall_mem_cons.2 ⟨sub3_701, List.forall_mem_cons.2 ⟨sub3_702, List.forall_mem_cons.2 ⟨sub3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_704 : sub3 [7, 3] = true := by decide +kernel
theorem sub3_705 : sub3 [7, 4] = true := by decide +kernel
theorem sub3_706 : sub3 [7, 5] = true := by decide +kernel
theorem sb3_22 : ∀ q ∈ blk3_22, sub3 q = true := by
  unfold blk3_22
  exact List.forall_mem_cons.2 ⟨sub3_704, List.forall_mem_cons.2 ⟨sub3_705, List.forall_mem_cons.2 ⟨sub3_706, List.forall_mem_nil _⟩⟩⟩
theorem sub4_0 : sub4 [-7] = true := by decide +kernel
theorem sub4_1 : sub4 [-6, -1] = true := by decide +kernel
theorem sub4_2 : sub4 [-6, 0] = true := by decide +kernel
theorem sub4_3 : sub4 [-6, 1] = true := by decide +kernel
theorem sub4_4 : sub4 [-6, 2] = true := by decide +kernel
theorem sub4_5 : sub4 [-6, 3] = true := by decide +kernel
theorem sub4_6 : sub4 [-6, 4] = true := by decide +kernel
theorem sub4_7 : sub4 [-6, 5] = true := by decide +kernel
theorem sub4_8 : sub4 [-6, 6] = true := by decide +kernel
theorem sub4_9 : sub4 [-5, -3] = true := by decide +kernel
theorem sub4_10 : sub4 [-5, -2] = true := by decide +kernel
theorem sub4_11 : sub4 [-5, -1] = true := by decide +kernel
theorem sub4_12 : sub4 [-5, 0] = true := by decide +kernel
theorem sub4_13 : sub4 [-5, 1] = true := by decide +kernel
theorem sub4_14 : sub4 [-5, 2] = true := by decide +kernel
theorem sub4_15 : sub4 [-5, 3] = true := by decide +kernel
theorem sub4_16 : sub4 [-5, 4] = true := by decide +kernel
theorem sub4_17 : sub4 [-5, 5] = true := by decide +kernel
theorem sub4_18 : sub4 [-5, 6] = true := by decide +kernel
theorem sub4_19 : sub4 [-4, -4] = true := by decide +kernel
theorem sub4_20 : sub4 [-4, -3] = true := by decide +kernel
theorem sub4_21 : sub4 [-4, -2] = true := by decide +kernel
theorem sub4_22 : sub4 [-4, -1] = true := by decide +kernel
theorem sub4_23 : sub4 [-4, 0] = true := by decide +kernel
theorem sub4_24 : sub4 [-4, 1] = true := by decide +kernel
theorem sub4_25 : sub4 [-4, 2] = true := by decide +kernel
theorem sub4_26 : sub4 [-4, 3] = true := by decide +kernel
theorem sub4_27 : sub4 [-4, 4] = true := by decide +kernel
theorem sub4_28 : sub4 [-4, 5] = true := by decide +kernel
theorem sub4_29 : sub4 [-4, 6] = true := by decide +kernel
theorem sub4_30 : sub4 [-3, -5] = true := by decide +kernel
theorem sub4_31 : sub4 [-3, -4] = true := by decide +kernel
theorem sb4_0 : ∀ q ∈ blk4_0, sub4 q = true := by
  unfold blk4_0
  exact List.forall_mem_cons.2 ⟨sub4_0, List.forall_mem_cons.2 ⟨sub4_1, List.forall_mem_cons.2 ⟨sub4_2, List.forall_mem_cons.2 ⟨sub4_3, List.forall_mem_cons.2 ⟨sub4_4, List.forall_mem_cons.2 ⟨sub4_5, List.forall_mem_cons.2 ⟨sub4_6, List.forall_mem_cons.2 ⟨sub4_7, List.forall_mem_cons.2 ⟨sub4_8, List.forall_mem_cons.2 ⟨sub4_9, List.forall_mem_cons.2 ⟨sub4_10, List.forall_mem_cons.2 ⟨sub4_11, List.forall_mem_cons.2 ⟨sub4_12, List.forall_mem_cons.2 ⟨sub4_13, List.forall_mem_cons.2 ⟨sub4_14, List.forall_mem_cons.2 ⟨sub4_15, List.forall_mem_cons.2 ⟨sub4_16, List.forall_mem_cons.2 ⟨sub4_17, List.forall_mem_cons.2 ⟨sub4_18, List.forall_mem_cons.2 ⟨sub4_19, List.forall_mem_cons.2 ⟨sub4_20, List.forall_mem_cons.2 ⟨sub4_21, List.forall_mem_cons.2 ⟨sub4_22, List.forall_mem_cons.2 ⟨sub4_23, List.forall_mem_cons.2 ⟨sub4_24, List.forall_mem_cons.2 ⟨sub4_25, List.forall_mem_cons.2 ⟨sub4_26, List.forall_mem_cons.2 ⟨sub4_27, List.forall_mem_cons.2 ⟨sub4_28, List.forall_mem_cons.2 ⟨sub4_29, List.forall_mem_cons.2 ⟨sub4_30, List.forall_mem_cons.2 ⟨sub4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_32 : sub4 [-3, -3] = true := by decide +kernel
theorem sub4_33 : sub4 [-3, -2] = true := by decide +kernel
theorem sub4_34 : sub4 [-3, -1] = true := by decide +kernel
theorem sub4_35 : sub4 [-3, 0] = true := by decide +kernel
theorem sub4_36 : sub4 [-3, 1, -8] = true := by decide +kernel
theorem sub4_37 : sub4 [-3, 1, -7] = true := by decide +kernel
theorem sub4_38 : sub4 [-3, 1, -6] = true := by decide +kernel
theorem sub4_39 : sub4 [-3, 1, -5] = true := by decide +kernel
theorem sub4_40 : sub4 [-3, 1, -4] = true := by decide +kernel
theorem sub4_41 : sub4 [-3, 1, -3] = true := by decide +kernel
theorem sub4_42 : sub4 [-3, 1, -2] = true := by decide +kernel
theorem sub4_43 : sub4 [-3, 1, -1] = true := by decide +kernel
theorem sub4_44 : sub4 [-3, 1, 0] = true := by decide +kernel
theorem sub4_45 : sub4 [-3, 1, 1] = true := by decide +kernel
theorem sub4_46 : sub4 [-3, 1, 2] = true := by decide +kernel
theorem sub4_47 : sub4 [-3, 1, 3] = true := by decide +kernel
theorem sub4_48 : sub4 [-3, 1, 4] = true := by decide +kernel
theorem sub4_49 : sub4 [-3, 1, 5] = true := by decide +kernel
theorem sub4_50 : sub4 [-3, 1, 6] = true := by decide +kernel
theorem sub4_51 : sub4 [-3, 2, -8] = true := by decide +kernel
theorem sub4_52 : sub4 [-3, 2, -7] = true := by decide +kernel
theorem sub4_53 : sub4 [-3, 2, -6] = true := by decide +kernel
theorem sub4_54 : sub4 [-3, 2, -5] = true := by decide +kernel
theorem sub4_55 : sub4 [-3, 2, -4] = true := by decide +kernel
theorem sub4_56 : sub4 [-3, 2, -3] = true := by decide +kernel
theorem sub4_57 : sub4 [-3, 2, -2] = true := by decide +kernel
theorem sub4_58 : sub4 [-3, 2, -1] = true := by decide +kernel
theorem sub4_59 : sub4 [-3, 2, 0] = true := by decide +kernel
theorem sub4_60 : sub4 [-3, 2, 1] = true := by decide +kernel
theorem sub4_61 : sub4 [-3, 2, 2] = true := by decide +kernel
theorem sub4_62 : sub4 [-3, 2, 3] = true := by decide +kernel
theorem sub4_63 : sub4 [-3, 2, 4] = true := by decide +kernel
theorem sb4_1 : ∀ q ∈ blk4_1, sub4 q = true := by
  unfold blk4_1
  exact List.forall_mem_cons.2 ⟨sub4_32, List.forall_mem_cons.2 ⟨sub4_33, List.forall_mem_cons.2 ⟨sub4_34, List.forall_mem_cons.2 ⟨sub4_35, List.forall_mem_cons.2 ⟨sub4_36, List.forall_mem_cons.2 ⟨sub4_37, List.forall_mem_cons.2 ⟨sub4_38, List.forall_mem_cons.2 ⟨sub4_39, List.forall_mem_cons.2 ⟨sub4_40, List.forall_mem_cons.2 ⟨sub4_41, List.forall_mem_cons.2 ⟨sub4_42, List.forall_mem_cons.2 ⟨sub4_43, List.forall_mem_cons.2 ⟨sub4_44, List.forall_mem_cons.2 ⟨sub4_45, List.forall_mem_cons.2 ⟨sub4_46, List.forall_mem_cons.2 ⟨sub4_47, List.forall_mem_cons.2 ⟨sub4_48, List.forall_mem_cons.2 ⟨sub4_49, List.forall_mem_cons.2 ⟨sub4_50, List.forall_mem_cons.2 ⟨sub4_51, List.forall_mem_cons.2 ⟨sub4_52, List.forall_mem_cons.2 ⟨sub4_53, List.forall_mem_cons.2 ⟨sub4_54, List.forall_mem_cons.2 ⟨sub4_55, List.forall_mem_cons.2 ⟨sub4_56, List.forall_mem_cons.2 ⟨sub4_57, List.forall_mem_cons.2 ⟨sub4_58, List.forall_mem_cons.2 ⟨sub4_59, List.forall_mem_cons.2 ⟨sub4_60, List.forall_mem_cons.2 ⟨sub4_61, List.forall_mem_cons.2 ⟨sub4_62, List.forall_mem_cons.2 ⟨sub4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_64 : sub4 [-3, 2, 5] = true := by decide +kernel
theorem sub4_65 : sub4 [-3, 2, 6] = true := by decide +kernel
theorem sub4_66 : sub4 [-3, 3] = true := by decide +kernel
theorem sub4_67 : sub4 [-3, 4] = true := by decide +kernel
theorem sub4_68 : sub4 [-3, 5] = true := by decide +kernel
theorem sub4_69 : sub4 [-3, 6] = true := by decide +kernel
theorem sub4_70 : sub4 [-2, -5] = true := by decide +kernel
theorem sub4_71 : sub4 [-2, -4] = true := by decide +kernel
theorem sub4_72 : sub4 [-2, -3] = true := by decide +kernel
theorem sub4_73 : sub4 [-2, -2] = true := by decide +kernel
theorem sub4_74 : sub4 [-2, -1] = true := by decide +kernel
theorem sub4_75 : sub4 [-2, 0, -8] = true := by decide +kernel
theorem sub4_76 : sub4 [-2, 0, -7] = true := by decide +kernel
theorem sub4_77 : sub4 [-2, 0, -6] = true := by decide +kernel
theorem sub4_78 : sub4 [-2, 0, -5] = true := by decide +kernel
theorem sub4_79 : sub4 [-2, 0, -4] = true := by decide +kernel
theorem sub4_80 : sub4 [-2, 0, -3] = true := by decide +kernel
theorem sub4_81 : sub4 [-2, 0, -2] = true := by decide +kernel
theorem sub4_82 : sub4 [-2, 0, -1] = true := by decide +kernel
theorem sub4_83 : sub4 [-2, 0, 0] = true := by decide +kernel
theorem sub4_84 : sub4 [-2, 0, 1] = true := by decide +kernel
theorem sub4_85 : sub4 [-2, 0, 2] = true := by decide +kernel
theorem sub4_86 : sub4 [-2, 0, 3] = true := by decide +kernel
theorem sub4_87 : sub4 [-2, 0, 4] = true := by decide +kernel
theorem sub4_88 : sub4 [-2, 0, 5] = true := by decide +kernel
theorem sub4_89 : sub4 [-2, 0, 6] = true := by decide +kernel
theorem sub4_90 : sub4 [-2, 0, 7] = true := by decide +kernel
theorem sub4_91 : sub4 [-2, 1, -8] = true := by decide +kernel
theorem sub4_92 : sub4 [-2, 1, -7] = true := by decide +kernel
theorem sub4_93 : sub4 [-2, 1, -6] = true := by decide +kernel
theorem sub4_94 : sub4 [-2, 1, -5] = true := by decide +kernel
theorem sub4_95 : sub4 [-2, 1, -4] = true := by decide +kernel
theorem sb4_2 : ∀ q ∈ blk4_2, sub4 q = true := by
  unfold blk4_2
  exact List.forall_mem_cons.2 ⟨sub4_64, List.forall_mem_cons.2 ⟨sub4_65, List.forall_mem_cons.2 ⟨sub4_66, List.forall_mem_cons.2 ⟨sub4_67, List.forall_mem_cons.2 ⟨sub4_68, List.forall_mem_cons.2 ⟨sub4_69, List.forall_mem_cons.2 ⟨sub4_70, List.forall_mem_cons.2 ⟨sub4_71, List.forall_mem_cons.2 ⟨sub4_72, List.forall_mem_cons.2 ⟨sub4_73, List.forall_mem_cons.2 ⟨sub4_74, List.forall_mem_cons.2 ⟨sub4_75, List.forall_mem_cons.2 ⟨sub4_76, List.forall_mem_cons.2 ⟨sub4_77, List.forall_mem_cons.2 ⟨sub4_78, List.forall_mem_cons.2 ⟨sub4_79, List.forall_mem_cons.2 ⟨sub4_80, List.forall_mem_cons.2 ⟨sub4_81, List.forall_mem_cons.2 ⟨sub4_82, List.forall_mem_cons.2 ⟨sub4_83, List.forall_mem_cons.2 ⟨sub4_84, List.forall_mem_cons.2 ⟨sub4_85, List.forall_mem_cons.2 ⟨sub4_86, List.forall_mem_cons.2 ⟨sub4_87, List.forall_mem_cons.2 ⟨sub4_88, List.forall_mem_cons.2 ⟨sub4_89, List.forall_mem_cons.2 ⟨sub4_90, List.forall_mem_cons.2 ⟨sub4_91, List.forall_mem_cons.2 ⟨sub4_92, List.forall_mem_cons.2 ⟨sub4_93, List.forall_mem_cons.2 ⟨sub4_94, List.forall_mem_cons.2 ⟨sub4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C063
