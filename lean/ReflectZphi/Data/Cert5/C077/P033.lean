import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_3_672 : subd12_3 [3, -1] = true := by decide +kernel
theorem subd12_3_673 : subd12_3 [3, 0, -5] = true := by decide +kernel
theorem subd12_3_674 : subd12_3 [3, 0, -4] = true := by decide +kernel
theorem subd12_3_675 : subd12_3 [3, 0, -3] = true := by decide +kernel
theorem subd12_3_676 : subd12_3 [3, 0, -2] = true := by decide +kernel
theorem subd12_3_677 : subd12_3 [3, 0, -1] = true := by decide +kernel
theorem subd12_3_678 : subd12_3 [3, 0, 0] = true := by decide +kernel
theorem subd12_3_679 : subd12_3 [3, 0, 1] = true := by decide +kernel
theorem subd12_3_680 : subd12_3 [3, 0, 2] = true := by decide +kernel
theorem subd12_3_681 : subd12_3 [3, 0, 3] = true := by decide +kernel
theorem subd12_3_682 : subd12_3 [3, 0, 4] = true := by decide +kernel
theorem subd12_3_683 : subd12_3 [3, 0, 5] = true := by decide +kernel
theorem subd12_3_684 : subd12_3 [3, 0, 6] = true := by decide +kernel
theorem subd12_3_685 : subd12_3 [3, 0, 7] = true := by decide +kernel
theorem subd12_3_686 : subd12_3 [3, 1, -6] = true := by decide +kernel
theorem subd12_3_687 : subd12_3 [3, 1, -5] = true := by decide +kernel
theorem subd12_3_688 : subd12_3 [3, 1, -4] = true := by decide +kernel
theorem subd12_3_689 : subd12_3 [3, 1, -3] = true := by decide +kernel
theorem subd12_3_690 : subd12_3 [3, 1, -2] = true := by decide +kernel
theorem subd12_3_691 : subd12_3 [3, 1, -1] = true := by decide +kernel
theorem subd12_3_692 : subd12_3 [3, 1, 0] = true := by decide +kernel
theorem subd12_3_693 : subd12_3 [3, 1, 1] = true := by decide +kernel
theorem subd12_3_694 : subd12_3 [3, 1, 2] = true := by decide +kernel
theorem subd12_3_695 : subd12_3 [3, 1, 3] = true := by decide +kernel
theorem subd12_3_696 : subd12_3 [3, 1, 4] = true := by decide +kernel
theorem subd12_3_697 : subd12_3 [3, 1, 5] = true := by decide +kernel
theorem subd12_3_698 : subd12_3 [3, 1, 6] = true := by decide +kernel
theorem subd12_3_699 : subd12_3 [3, 1, 7] = true := by decide +kernel
theorem subd12_3_700 : subd12_3 [3, 1, 8] = true := by decide +kernel
theorem subd12_3_701 : subd12_3 [3, 2, -6] = true := by decide +kernel
theorem subd12_3_702 : subd12_3 [3, 2, -5] = true := by decide +kernel
theorem subd12_3_703 : subd12_3 [3, 2, -4] = true := by decide +kernel
theorem sbd12_3_21 : ∀ q ∈ blkd12_3_21, subd12_3 q = true := by
  unfold blkd12_3_21
  exact List.forall_mem_cons.2 ⟨subd12_3_672, List.forall_mem_cons.2 ⟨subd12_3_673, List.forall_mem_cons.2 ⟨subd12_3_674, List.forall_mem_cons.2 ⟨subd12_3_675, List.forall_mem_cons.2 ⟨subd12_3_676, List.forall_mem_cons.2 ⟨subd12_3_677, List.forall_mem_cons.2 ⟨subd12_3_678, List.forall_mem_cons.2 ⟨subd12_3_679, List.forall_mem_cons.2 ⟨subd12_3_680, List.forall_mem_cons.2 ⟨subd12_3_681, List.forall_mem_cons.2 ⟨subd12_3_682, List.forall_mem_cons.2 ⟨subd12_3_683, List.forall_mem_cons.2 ⟨subd12_3_684, List.forall_mem_cons.2 ⟨subd12_3_685, List.forall_mem_cons.2 ⟨subd12_3_686, List.forall_mem_cons.2 ⟨subd12_3_687, List.forall_mem_cons.2 ⟨subd12_3_688, List.forall_mem_cons.2 ⟨subd12_3_689, List.forall_mem_cons.2 ⟨subd12_3_690, List.forall_mem_cons.2 ⟨subd12_3_691, List.forall_mem_cons.2 ⟨subd12_3_692, List.forall_mem_cons.2 ⟨subd12_3_693, List.forall_mem_cons.2 ⟨subd12_3_694, List.forall_mem_cons.2 ⟨subd12_3_695, List.forall_mem_cons.2 ⟨subd12_3_696, List.forall_mem_cons.2 ⟨subd12_3_697, List.forall_mem_cons.2 ⟨subd12_3_698, List.forall_mem_cons.2 ⟨subd12_3_699, List.forall_mem_cons.2 ⟨subd12_3_700, List.forall_mem_cons.2 ⟨subd12_3_701, List.forall_mem_cons.2 ⟨subd12_3_702, List.forall_mem_cons.2 ⟨subd12_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_704 : subd12_3 [3, 2, -3] = true := by decide +kernel
theorem subd12_3_705 : subd12_3 [3, 2, -2] = true := by decide +kernel
theorem subd12_3_706 : subd12_3 [3, 2, -1] = true := by decide +kernel
theorem subd12_3_707 : subd12_3 [3, 2, 0] = true := by decide +kernel
theorem subd12_3_708 : subd12_3 [3, 2, 1] = true := by decide +kernel
theorem subd12_3_709 : subd12_3 [3, 2, 2] = true := by decide +kernel
theorem subd12_3_710 : subd12_3 [3, 2, 3] = true := by decide +kernel
theorem subd12_3_711 : subd12_3 [3, 2, 4] = true := by decide +kernel
theorem subd12_3_712 : subd12_3 [3, 2, 5] = true := by decide +kernel
theorem subd12_3_713 : subd12_3 [3, 2, 6] = true := by decide +kernel
theorem subd12_3_714 : subd12_3 [3, 2, 7] = true := by decide +kernel
theorem subd12_3_715 : subd12_3 [3, 3, -6] = true := by decide +kernel
theorem subd12_3_716 : subd12_3 [3, 3, -5] = true := by decide +kernel
theorem subd12_3_717 : subd12_3 [3, 3, -4] = true := by decide +kernel
theorem subd12_3_718 : subd12_3 [3, 3, -3] = true := by decide +kernel
theorem subd12_3_719 : subd12_3 [3, 3, -2] = true := by decide +kernel
theorem subd12_3_720 : subd12_3 [3, 3, -1] = true := by decide +kernel
theorem subd12_3_721 : subd12_3 [3, 3, 0] = true := by decide +kernel
theorem subd12_3_722 : subd12_3 [3, 3, 1] = true := by decide +kernel
theorem subd12_3_723 : subd12_3 [3, 3, 2] = true := by decide +kernel
theorem subd12_3_724 : subd12_3 [3, 3, 3] = true := by decide +kernel
theorem subd12_3_725 : subd12_3 [3, 3, 4] = true := by decide +kernel
theorem subd12_3_726 : subd12_3 [3, 3, 5] = true := by decide +kernel
theorem subd12_3_727 : subd12_3 [3, 3, 6] = true := by decide +kernel
theorem subd12_3_728 : subd12_3 [3, 3, 7] = true := by decide +kernel
theorem subd12_3_729 : subd12_3 [3, 4] = true := by decide +kernel
theorem subd12_3_730 : subd12_3 [3, 5] = true := by decide +kernel
theorem subd12_3_731 : subd12_3 [4, -1] = true := by decide +kernel
theorem subd12_3_732 : subd12_3 [4, 0] = true := by decide +kernel
theorem subd12_3_733 : subd12_3 [4, 1] = true := by decide +kernel
theorem subd12_3_734 : subd12_3 [4, 2] = true := by decide +kernel
theorem subd12_3_735 : subd12_3 [4, 3] = true := by decide +kernel
theorem sbd12_3_22 : ∀ q ∈ blkd12_3_22, subd12_3 q = true := by
  unfold blkd12_3_22
  exact List.forall_mem_cons.2 ⟨subd12_3_704, List.forall_mem_cons.2 ⟨subd12_3_705, List.forall_mem_cons.2 ⟨subd12_3_706, List.forall_mem_cons.2 ⟨subd12_3_707, List.forall_mem_cons.2 ⟨subd12_3_708, List.forall_mem_cons.2 ⟨subd12_3_709, List.forall_mem_cons.2 ⟨subd12_3_710, List.forall_mem_cons.2 ⟨subd12_3_711, List.forall_mem_cons.2 ⟨subd12_3_712, List.forall_mem_cons.2 ⟨subd12_3_713, List.forall_mem_cons.2 ⟨subd12_3_714, List.forall_mem_cons.2 ⟨subd12_3_715, List.forall_mem_cons.2 ⟨subd12_3_716, List.forall_mem_cons.2 ⟨subd12_3_717, List.forall_mem_cons.2 ⟨subd12_3_718, List.forall_mem_cons.2 ⟨subd12_3_719, List.forall_mem_cons.2 ⟨subd12_3_720, List.forall_mem_cons.2 ⟨subd12_3_721, List.forall_mem_cons.2 ⟨subd12_3_722, List.forall_mem_cons.2 ⟨subd12_3_723, List.forall_mem_cons.2 ⟨subd12_3_724, List.forall_mem_cons.2 ⟨subd12_3_725, List.forall_mem_cons.2 ⟨subd12_3_726, List.forall_mem_cons.2 ⟨subd12_3_727, List.forall_mem_cons.2 ⟨subd12_3_728, List.forall_mem_cons.2 ⟨subd12_3_729, List.forall_mem_cons.2 ⟨subd12_3_730, List.forall_mem_cons.2 ⟨subd12_3_731, List.forall_mem_cons.2 ⟨subd12_3_732, List.forall_mem_cons.2 ⟨subd12_3_733, List.forall_mem_cons.2 ⟨subd12_3_734, List.forall_mem_cons.2 ⟨subd12_3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_736 : subd12_3 [4, 4] = true := by decide +kernel
theorem sbd12_3_23 : ∀ q ∈ blkd12_3_23, subd12_3 q = true := by
  unfold blkd12_3_23
  exact List.forall_mem_cons.2 ⟨subd12_3_736, List.forall_mem_nil _⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [-3] = true := by decide +kernel
theorem subd13_0_1 : subd13_0 [-2] = true := by decide +kernel
theorem subd13_0_2 : subd13_0 [-1] = true := by decide +kernel
theorem subd13_0_3 : subd13_0 [0, -4] = true := by decide +kernel
theorem subd13_0_4 : subd13_0 [0, -3] = true := by decide +kernel
theorem subd13_0_5 : subd13_0 [0, -2] = true := by decide +kernel
theorem subd13_0_6 : subd13_0 [0, -1] = true := by decide +kernel
theorem subd13_0_7 : subd13_0 [0, 0] = true := by decide +kernel
theorem subd13_0_8 : subd13_0 [0, 1] = true := by decide +kernel
theorem subd13_0_9 : subd13_0 [0, 2] = true := by decide +kernel
theorem subd13_0_10 : subd13_0 [0, 3] = true := by decide +kernel
theorem subd13_0_11 : subd13_0 [1] = true := by decide +kernel
theorem subd13_0_12 : subd13_0 [2] = true := by decide +kernel
theorem subd13_0_13 : subd13_0 [3] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_cons.2 ⟨subd13_0_1, List.forall_mem_cons.2 ⟨subd13_0_2, List.forall_mem_cons.2 ⟨subd13_0_3, List.forall_mem_cons.2 ⟨subd13_0_4, List.forall_mem_cons.2 ⟨subd13_0_5, List.forall_mem_cons.2 ⟨subd13_0_6, List.forall_mem_cons.2 ⟨subd13_0_7, List.forall_mem_cons.2 ⟨subd13_0_8, List.forall_mem_cons.2 ⟨subd13_0_9, List.forall_mem_cons.2 ⟨subd13_0_10, List.forall_mem_cons.2 ⟨subd13_0_11, List.forall_mem_cons.2 ⟨subd13_0_12, List.forall_mem_cons.2 ⟨subd13_0_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [-4] = true := by decide +kernel
theorem subd13_1_1 : subd13_1 [-3, -3] = true := by decide +kernel
theorem subd13_1_2 : subd13_1 [-3, -2] = true := by decide +kernel
theorem subd13_1_3 : subd13_1 [-3, -1] = true := by decide +kernel
theorem subd13_1_4 : subd13_1 [-3, 0] = true := by decide +kernel
theorem subd13_1_5 : subd13_1 [-3, 1] = true := by decide +kernel
theorem subd13_1_6 : subd13_1 [-3, 2] = true := by decide +kernel
theorem subd13_1_7 : subd13_1 [-3, 3] = true := by decide +kernel
theorem subd13_1_8 : subd13_1 [-3, 4] = true := by decide +kernel
theorem subd13_1_9 : subd13_1 [-2, -4] = true := by decide +kernel
theorem subd13_1_10 : subd13_1 [-2, -3] = true := by decide +kernel
theorem subd13_1_11 : subd13_1 [-2, -2] = true := by decide +kernel
theorem subd13_1_12 : subd13_1 [-2, -1] = true := by decide +kernel
theorem subd13_1_13 : subd13_1 [-2, 0] = true := by decide +kernel
theorem subd13_1_14 : subd13_1 [-2, 1] = true := by decide +kernel
theorem subd13_1_15 : subd13_1 [-2, 2] = true := by decide +kernel
theorem subd13_1_16 : subd13_1 [-2, 3] = true := by decide +kernel
theorem subd13_1_17 : subd13_1 [-2, 4] = true := by decide +kernel
theorem subd13_1_18 : subd13_1 [-2, 5] = true := by decide +kernel
theorem subd13_1_19 : subd13_1 [-1, -5] = true := by decide +kernel
theorem subd13_1_20 : subd13_1 [-1, -4] = true := by decide +kernel
theorem subd13_1_21 : subd13_1 [-1, -3] = true := by decide +kernel
theorem subd13_1_22 : subd13_1 [-1, -2] = true := by decide +kernel
theorem subd13_1_23 : subd13_1 [-1, -1] = true := by decide +kernel
theorem subd13_1_24 : subd13_1 [-1, 0] = true := by decide +kernel
theorem subd13_1_25 : subd13_1 [-1, 1] = true := by decide +kernel
theorem subd13_1_26 : subd13_1 [-1, 2] = true := by decide +kernel
theorem subd13_1_27 : subd13_1 [-1, 3] = true := by decide +kernel
theorem subd13_1_28 : subd13_1 [-1, 4] = true := by decide +kernel
theorem subd13_1_29 : subd13_1 [-1, 5] = true := by decide +kernel
theorem subd13_1_30 : subd13_1 [0, -5] = true := by decide +kernel
theorem subd13_1_31 : subd13_1 [0, -4] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_cons.2 ⟨subd13_1_1, List.forall_mem_cons.2 ⟨subd13_1_2, List.forall_mem_cons.2 ⟨subd13_1_3, List.forall_mem_cons.2 ⟨subd13_1_4, List.forall_mem_cons.2 ⟨subd13_1_5, List.forall_mem_cons.2 ⟨subd13_1_6, List.forall_mem_cons.2 ⟨subd13_1_7, List.forall_mem_cons.2 ⟨subd13_1_8, List.forall_mem_cons.2 ⟨subd13_1_9, List.forall_mem_cons.2 ⟨subd13_1_10, List.forall_mem_cons.2 ⟨subd13_1_11, List.forall_mem_cons.2 ⟨subd13_1_12, List.forall_mem_cons.2 ⟨subd13_1_13, List.forall_mem_cons.2 ⟨subd13_1_14, List.forall_mem_cons.2 ⟨subd13_1_15, List.forall_mem_cons.2 ⟨subd13_1_16, List.forall_mem_cons.2 ⟨subd13_1_17, List.forall_mem_cons.2 ⟨subd13_1_18, List.forall_mem_cons.2 ⟨subd13_1_19, List.forall_mem_cons.2 ⟨subd13_1_20, List.forall_mem_cons.2 ⟨subd13_1_21, List.forall_mem_cons.2 ⟨subd13_1_22, List.forall_mem_cons.2 ⟨subd13_1_23, List.forall_mem_cons.2 ⟨subd13_1_24, List.forall_mem_cons.2 ⟨subd13_1_25, List.forall_mem_cons.2 ⟨subd13_1_26, List.forall_mem_cons.2 ⟨subd13_1_27, List.forall_mem_cons.2 ⟨subd13_1_28, List.forall_mem_cons.2 ⟨subd13_1_29, List.forall_mem_cons.2 ⟨subd13_1_30, List.forall_mem_cons.2 ⟨subd13_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_32 : subd13_1 [0, -3] = true := by decide +kernel
theorem subd13_1_33 : subd13_1 [0, -2] = true := by decide +kernel
theorem subd13_1_34 : subd13_1 [0, -1] = true := by decide +kernel
theorem subd13_1_35 : subd13_1 [0, 0] = true := by decide +kernel
theorem subd13_1_36 : subd13_1 [0, 1] = true := by decide +kernel
theorem subd13_1_37 : subd13_1 [0, 2] = true := by decide +kernel
theorem subd13_1_38 : subd13_1 [0, 3] = true := by decide +kernel
theorem subd13_1_39 : subd13_1 [0, 4] = true := by decide +kernel
theorem subd13_1_40 : subd13_1 [1, -6] = true := by decide +kernel
theorem subd13_1_41 : subd13_1 [1, -5] = true := by decide +kernel
theorem subd13_1_42 : subd13_1 [1, -4] = true := by decide +kernel
theorem subd13_1_43 : subd13_1 [1, -3] = true := by decide +kernel
theorem subd13_1_44 : subd13_1 [1, -2] = true := by decide +kernel
theorem subd13_1_45 : subd13_1 [1, -1] = true := by decide +kernel
theorem subd13_1_46 : subd13_1 [1, 0] = true := by decide +kernel
theorem subd13_1_47 : subd13_1 [1, 1] = true := by decide +kernel
theorem subd13_1_48 : subd13_1 [1, 2] = true := by decide +kernel
theorem subd13_1_49 : subd13_1 [1, 3] = true := by decide +kernel
theorem subd13_1_50 : subd13_1 [1, 4] = true := by decide +kernel
theorem subd13_1_51 : subd13_1 [2, -6] = true := by decide +kernel
theorem subd13_1_52 : subd13_1 [2, -5] = true := by decide +kernel
theorem subd13_1_53 : subd13_1 [2, -4] = true := by decide +kernel
theorem subd13_1_54 : subd13_1 [2, -3] = true := by decide +kernel
theorem subd13_1_55 : subd13_1 [2, -2] = true := by decide +kernel
theorem subd13_1_56 : subd13_1 [2, -1] = true := by decide +kernel
theorem subd13_1_57 : subd13_1 [2, 0] = true := by decide +kernel
theorem subd13_1_58 : subd13_1 [2, 1] = true := by decide +kernel
theorem subd13_1_59 : subd13_1 [2, 2] = true := by decide +kernel
theorem subd13_1_60 : subd13_1 [2, 3] = true := by decide +kernel
theorem subd13_1_61 : subd13_1 [3, -5] = true := by decide +kernel
theorem subd13_1_62 : subd13_1 [3, -4] = true := by decide +kernel
theorem subd13_1_63 : subd13_1 [3, -3] = true := by decide +kernel
theorem sbd13_1_1 : ∀ q ∈ blkd13_1_1, subd13_1 q = true := by
  unfold blkd13_1_1
  exact List.forall_mem_cons.2 ⟨subd13_1_32, List.forall_mem_cons.2 ⟨subd13_1_33, List.forall_mem_cons.2 ⟨subd13_1_34, List.forall_mem_cons.2 ⟨subd13_1_35, List.forall_mem_cons.2 ⟨subd13_1_36, List.forall_mem_cons.2 ⟨subd13_1_37, List.forall_mem_cons.2 ⟨subd13_1_38, List.forall_mem_cons.2 ⟨subd13_1_39, List.forall_mem_cons.2 ⟨subd13_1_40, List.forall_mem_cons.2 ⟨subd13_1_41, List.forall_mem_cons.2 ⟨subd13_1_42, List.forall_mem_cons.2 ⟨subd13_1_43, List.forall_mem_cons.2 ⟨subd13_1_44, List.forall_mem_cons.2 ⟨subd13_1_45, List.forall_mem_cons.2 ⟨subd13_1_46, List.forall_mem_cons.2 ⟨subd13_1_47, List.forall_mem_cons.2 ⟨subd13_1_48, List.forall_mem_cons.2 ⟨subd13_1_49, List.forall_mem_cons.2 ⟨subd13_1_50, List.forall_mem_cons.2 ⟨subd13_1_51, List.forall_mem_cons.2 ⟨subd13_1_52, List.forall_mem_cons.2 ⟨subd13_1_53, List.forall_mem_cons.2 ⟨subd13_1_54, List.forall_mem_cons.2 ⟨subd13_1_55, List.forall_mem_cons.2 ⟨subd13_1_56, List.forall_mem_cons.2 ⟨subd13_1_57, List.forall_mem_cons.2 ⟨subd13_1_58, List.forall_mem_cons.2 ⟨subd13_1_59, List.forall_mem_cons.2 ⟨subd13_1_60, List.forall_mem_cons.2 ⟨subd13_1_61, List.forall_mem_cons.2 ⟨subd13_1_62, List.forall_mem_cons.2 ⟨subd13_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_64 : subd13_1 [3, -2] = true := by decide +kernel
theorem subd13_1_65 : subd13_1 [3, -1] = true := by decide +kernel
theorem subd13_1_66 : subd13_1 [3, 0] = true := by decide +kernel
theorem subd13_1_67 : subd13_1 [3, 1] = true := by decide +kernel
theorem subd13_1_68 : subd13_1 [3, 2] = true := by decide +kernel
theorem subd13_1_69 : subd13_1 [4] = true := by decide +kernel
theorem sbd13_1_2 : ∀ q ∈ blkd13_1_2, subd13_1 q = true := by
  unfold blkd13_1_2
  exact List.forall_mem_cons.2 ⟨subd13_1_64, List.forall_mem_cons.2 ⟨subd13_1_65, List.forall_mem_cons.2 ⟨subd13_1_66, List.forall_mem_cons.2 ⟨subd13_1_67, List.forall_mem_cons.2 ⟨subd13_1_68, List.forall_mem_cons.2 ⟨subd13_1_69, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
