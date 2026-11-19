import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_640 : subd8_1 [3, 0, 0] = true := by decide +kernel
theorem subd8_1_641 : subd8_1 [3, 0, 1] = true := by decide +kernel
theorem subd8_1_642 : subd8_1 [3, 0, 2] = true := by decide +kernel
theorem subd8_1_643 : subd8_1 [3, 0, 3] = true := by decide +kernel
theorem subd8_1_644 : subd8_1 [3, 0, 4] = true := by decide +kernel
theorem subd8_1_645 : subd8_1 [3, 0, 5] = true := by decide +kernel
theorem subd8_1_646 : subd8_1 [3, 1, -9] = true := by decide +kernel
theorem subd8_1_647 : subd8_1 [3, 1, -8] = true := by decide +kernel
theorem subd8_1_648 : subd8_1 [3, 1, -7] = true := by decide +kernel
theorem subd8_1_649 : subd8_1 [3, 1, -6] = true := by decide +kernel
theorem subd8_1_650 : subd8_1 [3, 1, -5] = true := by decide +kernel
theorem subd8_1_651 : subd8_1 [3, 1, -4] = true := by decide +kernel
theorem subd8_1_652 : subd8_1 [3, 1, -3] = true := by decide +kernel
theorem subd8_1_653 : subd8_1 [3, 1, -2] = true := by decide +kernel
theorem subd8_1_654 : subd8_1 [3, 1, -1] = true := by decide +kernel
theorem subd8_1_655 : subd8_1 [3, 1, 0] = true := by decide +kernel
theorem subd8_1_656 : subd8_1 [3, 1, 1] = true := by decide +kernel
theorem subd8_1_657 : subd8_1 [3, 1, 2] = true := by decide +kernel
theorem subd8_1_658 : subd8_1 [3, 1, 3] = true := by decide +kernel
theorem subd8_1_659 : subd8_1 [3, 1, 4] = true := by decide +kernel
theorem subd8_1_660 : subd8_1 [3, 1, 5] = true := by decide +kernel
theorem subd8_1_661 : subd8_1 [3, 1, 6] = true := by decide +kernel
theorem subd8_1_662 : subd8_1 [3, 2] = true := by decide +kernel
theorem subd8_1_663 : subd8_1 [3, 3] = true := by decide +kernel
theorem subd8_1_664 : subd8_1 [3, 4] = true := by decide +kernel
theorem subd8_1_665 : subd8_1 [3, 5] = true := by decide +kernel
theorem subd8_1_666 : subd8_1 [4, -4] = true := by decide +kernel
theorem subd8_1_667 : subd8_1 [4, -3] = true := by decide +kernel
theorem subd8_1_668 : subd8_1 [4, -2] = true := by decide +kernel
theorem subd8_1_669 : subd8_1 [4, -1] = true := by decide +kernel
theorem subd8_1_670 : subd8_1 [4, 0] = true := by decide +kernel
theorem subd8_1_671 : subd8_1 [4, 1] = true := by decide +kernel
theorem sbd8_1_20 : ∀ q ∈ blkd8_1_20, subd8_1 q = true := by
  unfold blkd8_1_20
  exact List.forall_mem_cons.2 ⟨subd8_1_640, List.forall_mem_cons.2 ⟨subd8_1_641, List.forall_mem_cons.2 ⟨subd8_1_642, List.forall_mem_cons.2 ⟨subd8_1_643, List.forall_mem_cons.2 ⟨subd8_1_644, List.forall_mem_cons.2 ⟨subd8_1_645, List.forall_mem_cons.2 ⟨subd8_1_646, List.forall_mem_cons.2 ⟨subd8_1_647, List.forall_mem_cons.2 ⟨subd8_1_648, List.forall_mem_cons.2 ⟨subd8_1_649, List.forall_mem_cons.2 ⟨subd8_1_650, List.forall_mem_cons.2 ⟨subd8_1_651, List.forall_mem_cons.2 ⟨subd8_1_652, List.forall_mem_cons.2 ⟨subd8_1_653, List.forall_mem_cons.2 ⟨subd8_1_654, List.forall_mem_cons.2 ⟨subd8_1_655, List.forall_mem_cons.2 ⟨subd8_1_656, List.forall_mem_cons.2 ⟨subd8_1_657, List.forall_mem_cons.2 ⟨subd8_1_658, List.forall_mem_cons.2 ⟨subd8_1_659, List.forall_mem_cons.2 ⟨subd8_1_660, List.forall_mem_cons.2 ⟨subd8_1_661, List.forall_mem_cons.2 ⟨subd8_1_662, List.forall_mem_cons.2 ⟨subd8_1_663, List.forall_mem_cons.2 ⟨subd8_1_664, List.forall_mem_cons.2 ⟨subd8_1_665, List.forall_mem_cons.2 ⟨subd8_1_666, List.forall_mem_cons.2 ⟨subd8_1_667, List.forall_mem_cons.2 ⟨subd8_1_668, List.forall_mem_cons.2 ⟨subd8_1_669, List.forall_mem_cons.2 ⟨subd8_1_670, List.forall_mem_cons.2 ⟨subd8_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_672 : subd8_1 [4, 2] = true := by decide +kernel
theorem subd8_1_673 : subd8_1 [4, 3] = true := by decide +kernel
theorem subd8_1_674 : subd8_1 [4, 4] = true := by decide +kernel
theorem subd8_1_675 : subd8_1 [4, 5] = true := by decide +kernel
theorem subd8_1_676 : subd8_1 [5, -2] = true := by decide +kernel
theorem subd8_1_677 : subd8_1 [5, -1] = true := by decide +kernel
theorem subd8_1_678 : subd8_1 [5, 0] = true := by decide +kernel
theorem subd8_1_679 : subd8_1 [5, 1] = true := by decide +kernel
theorem subd8_1_680 : subd8_1 [5, 2] = true := by decide +kernel
theorem subd8_1_681 : subd8_1 [5, 3] = true := by decide +kernel
theorem subd8_1_682 : subd8_1 [5, 4] = true := by decide +kernel
theorem sbd8_1_21 : ∀ q ∈ blkd8_1_21, subd8_1 q = true := by
  unfold blkd8_1_21
  exact List.forall_mem_cons.2 ⟨subd8_1_672, List.forall_mem_cons.2 ⟨subd8_1_673, List.forall_mem_cons.2 ⟨subd8_1_674, List.forall_mem_cons.2 ⟨subd8_1_675, List.forall_mem_cons.2 ⟨subd8_1_676, List.forall_mem_cons.2 ⟨subd8_1_677, List.forall_mem_cons.2 ⟨subd8_1_678, List.forall_mem_cons.2 ⟨subd8_1_679, List.forall_mem_cons.2 ⟨subd8_1_680, List.forall_mem_cons.2 ⟨subd8_1_681, List.forall_mem_cons.2 ⟨subd8_1_682, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-2, -2] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-2, -1, -12] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-2, -1, -11] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-2, -1, -10] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-2, -1, -9] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-2, -1, -8] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [-2, -1, -7] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [-2, -1, -6] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [-2, -1, -5] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [-2, -1, -4] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [-2, -1, -3] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [-2, -1, -2] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [-2, -1, -1] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [-2, -1, 0] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [-2, -1, 1] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [-2, -1, 2] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [-2, -1, 3] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [-2, -1, 4] = true := by decide +kernel
theorem subd8_2_18 : subd8_2 [-2, -1, 5] = true := by decide +kernel
theorem subd8_2_19 : subd8_2 [-2, -1, 6] = true := by decide +kernel
theorem subd8_2_20 : subd8_2 [-2, -1, 7] = true := by decide +kernel
theorem subd8_2_21 : subd8_2 [-2, -1, 8] = true := by decide +kernel
theorem subd8_2_22 : subd8_2 [-2, -1, 9] = true := by decide +kernel
theorem subd8_2_23 : subd8_2 [-2, 0, -12] = true := by decide +kernel
theorem subd8_2_24 : subd8_2 [-2, 0, -11] = true := by decide +kernel
theorem subd8_2_25 : subd8_2 [-2, 0, -10] = true := by decide +kernel
theorem subd8_2_26 : subd8_2 [-2, 0, -9] = true := by decide +kernel
theorem subd8_2_27 : subd8_2 [-2, 0, -8] = true := by decide +kernel
theorem subd8_2_28 : subd8_2 [-2, 0, -7] = true := by decide +kernel
theorem subd8_2_29 : subd8_2 [-2, 0, -6] = true := by decide +kernel
theorem subd8_2_30 : subd8_2 [-2, 0, -5] = true := by decide +kernel
theorem subd8_2_31 : subd8_2 [-2, 0, -4] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_cons.2 ⟨subd8_2_18, List.forall_mem_cons.2 ⟨subd8_2_19, List.forall_mem_cons.2 ⟨subd8_2_20, List.forall_mem_cons.2 ⟨subd8_2_21, List.forall_mem_cons.2 ⟨subd8_2_22, List.forall_mem_cons.2 ⟨subd8_2_23, List.forall_mem_cons.2 ⟨subd8_2_24, List.forall_mem_cons.2 ⟨subd8_2_25, List.forall_mem_cons.2 ⟨subd8_2_26, List.forall_mem_cons.2 ⟨subd8_2_27, List.forall_mem_cons.2 ⟨subd8_2_28, List.forall_mem_cons.2 ⟨subd8_2_29, List.forall_mem_cons.2 ⟨subd8_2_30, List.forall_mem_cons.2 ⟨subd8_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_32 : subd8_2 [-2, 0, -3] = true := by decide +kernel
theorem subd8_2_33 : subd8_2 [-2, 0, -2] = true := by decide +kernel
theorem subd8_2_34 : subd8_2 [-2, 0, -1] = true := by decide +kernel
theorem subd8_2_35 : subd8_2 [-2, 0, 0] = true := by decide +kernel
theorem subd8_2_36 : subd8_2 [-2, 0, 1] = true := by decide +kernel
theorem subd8_2_37 : subd8_2 [-2, 0, 2] = true := by decide +kernel
theorem subd8_2_38 : subd8_2 [-2, 0, 3] = true := by decide +kernel
theorem subd8_2_39 : subd8_2 [-2, 0, 4] = true := by decide +kernel
theorem subd8_2_40 : subd8_2 [-2, 0, 5] = true := by decide +kernel
theorem subd8_2_41 : subd8_2 [-2, 0, 6] = true := by decide +kernel
theorem subd8_2_42 : subd8_2 [-2, 0, 7] = true := by decide +kernel
theorem subd8_2_43 : subd8_2 [-2, 0, 8] = true := by decide +kernel
theorem subd8_2_44 : subd8_2 [-2, 0, 9] = true := by decide +kernel
theorem subd8_2_45 : subd8_2 [-2, 0, 10] = true := by decide +kernel
theorem subd8_2_46 : subd8_2 [-2, 0, 11] = true := by decide +kernel
theorem subd8_2_47 : subd8_2 [-2, 1] = true := by decide +kernel
theorem subd8_2_48 : subd8_2 [-1, -3] = true := by decide +kernel
theorem subd8_2_49 : subd8_2 [-1, -2, -13] = true := by decide +kernel
theorem subd8_2_50 : subd8_2 [-1, -2, -12] = true := by decide +kernel
theorem subd8_2_51 : subd8_2 [-1, -2, -11] = true := by decide +kernel
theorem subd8_2_52 : subd8_2 [-1, -2, -10] = true := by decide +kernel
theorem subd8_2_53 : subd8_2 [-1, -2, -9] = true := by decide +kernel
theorem subd8_2_54 : subd8_2 [-1, -2, -8] = true := by decide +kernel
theorem subd8_2_55 : subd8_2 [-1, -2, -7] = true := by decide +kernel
theorem subd8_2_56 : subd8_2 [-1, -2, -6] = true := by decide +kernel
theorem subd8_2_57 : subd8_2 [-1, -2, -5] = true := by decide +kernel
theorem subd8_2_58 : subd8_2 [-1, -2, -4] = true := by decide +kernel
theorem subd8_2_59 : subd8_2 [-1, -2, -3] = true := by decide +kernel
theorem subd8_2_60 : subd8_2 [-1, -2, -2] = true := by decide +kernel
theorem subd8_2_61 : subd8_2 [-1, -2, -1] = true := by decide +kernel
theorem subd8_2_62 : subd8_2 [-1, -2, 0] = true := by decide +kernel
theorem subd8_2_63 : subd8_2 [-1, -2, 1] = true := by decide +kernel
theorem sbd8_2_1 : ∀ q ∈ blkd8_2_1, subd8_2 q = true := by
  unfold blkd8_2_1
  exact List.forall_mem_cons.2 ⟨subd8_2_32, List.forall_mem_cons.2 ⟨subd8_2_33, List.forall_mem_cons.2 ⟨subd8_2_34, List.forall_mem_cons.2 ⟨subd8_2_35, List.forall_mem_cons.2 ⟨subd8_2_36, List.forall_mem_cons.2 ⟨subd8_2_37, List.forall_mem_cons.2 ⟨subd8_2_38, List.forall_mem_cons.2 ⟨subd8_2_39, List.forall_mem_cons.2 ⟨subd8_2_40, List.forall_mem_cons.2 ⟨subd8_2_41, List.forall_mem_cons.2 ⟨subd8_2_42, List.forall_mem_cons.2 ⟨subd8_2_43, List.forall_mem_cons.2 ⟨subd8_2_44, List.forall_mem_cons.2 ⟨subd8_2_45, List.forall_mem_cons.2 ⟨subd8_2_46, List.forall_mem_cons.2 ⟨subd8_2_47, List.forall_mem_cons.2 ⟨subd8_2_48, List.forall_mem_cons.2 ⟨subd8_2_49, List.forall_mem_cons.2 ⟨subd8_2_50, List.forall_mem_cons.2 ⟨subd8_2_51, List.forall_mem_cons.2 ⟨subd8_2_52, List.forall_mem_cons.2 ⟨subd8_2_53, List.forall_mem_cons.2 ⟨subd8_2_54, List.forall_mem_cons.2 ⟨subd8_2_55, List.forall_mem_cons.2 ⟨subd8_2_56, List.forall_mem_cons.2 ⟨subd8_2_57, List.forall_mem_cons.2 ⟨subd8_2_58, List.forall_mem_cons.2 ⟨subd8_2_59, List.forall_mem_cons.2 ⟨subd8_2_60, List.forall_mem_cons.2 ⟨subd8_2_61, List.forall_mem_cons.2 ⟨subd8_2_62, List.forall_mem_cons.2 ⟨subd8_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_64 : subd8_2 [-1, -2, 2] = true := by decide +kernel
theorem subd8_2_65 : subd8_2 [-1, -2, 3] = true := by decide +kernel
theorem subd8_2_66 : subd8_2 [-1, -2, 4] = true := by decide +kernel
theorem subd8_2_67 : subd8_2 [-1, -2, 5] = true := by decide +kernel
theorem subd8_2_68 : subd8_2 [-1, -2, 6] = true := by decide +kernel
theorem subd8_2_69 : subd8_2 [-1, -2, 7] = true := by decide +kernel
theorem subd8_2_70 : subd8_2 [-1, -2, 8] = true := by decide +kernel
theorem subd8_2_71 : subd8_2 [-1, -2, 9] = true := by decide +kernel
theorem subd8_2_72 : subd8_2 [-1, -2, 10] = true := by decide +kernel
theorem subd8_2_73 : subd8_2 [-1, -2, 11] = true := by decide +kernel
theorem subd8_2_74 : subd8_2 [-1, -1, -19] = true := by decide +kernel
theorem subd8_2_75 : subd8_2 [-1, -1, -18] = true := by decide +kernel
theorem subd8_2_76 : subd8_2 [-1, -1, -17] = true := by decide +kernel
theorem subd8_2_77 : subd8_2 [-1, -1, -16] = true := by decide +kernel
theorem subd8_2_78 : subd8_2 [-1, -1, -15] = true := by decide +kernel
theorem subd8_2_79 : subd8_2 [-1, -1, -14] = true := by decide +kernel
theorem subd8_2_80 : subd8_2 [-1, -1, -13] = true := by decide +kernel
theorem subd8_2_81 : subd8_2 [-1, -1, -12] = true := by decide +kernel
theorem subd8_2_82 : subd8_2 [-1, -1, -11] = true := by decide +kernel
theorem subd8_2_83 : subd8_2 [-1, -1, -10] = true := by decide +kernel
theorem subd8_2_84 : subd8_2 [-1, -1, -9] = true := by decide +kernel
theorem subd8_2_85 : subd8_2 [-1, -1, -8] = true := by decide +kernel
theorem subd8_2_86 : subd8_2 [-1, -1, -7] = true := by decide +kernel
theorem subd8_2_87 : subd8_2 [-1, -1, -6] = true := by decide +kernel
theorem subd8_2_88 : subd8_2 [-1, -1, -5] = true := by decide +kernel
theorem subd8_2_89 : subd8_2 [-1, -1, -4] = true := by decide +kernel
theorem subd8_2_90 : subd8_2 [-1, -1, -3] = true := by decide +kernel
theorem subd8_2_91 : subd8_2 [-1, -1, -2] = true := by decide +kernel
theorem subd8_2_92 : subd8_2 [-1, -1, -1] = true := by decide +kernel
theorem subd8_2_93 : subd8_2 [-1, -1, 0] = true := by decide +kernel
theorem subd8_2_94 : subd8_2 [-1, -1, 1] = true := by decide +kernel
theorem subd8_2_95 : subd8_2 [-1, -1, 2] = true := by decide +kernel
theorem sbd8_2_2 : ∀ q ∈ blkd8_2_2, subd8_2 q = true := by
  unfold blkd8_2_2
  exact List.forall_mem_cons.2 ⟨subd8_2_64, List.forall_mem_cons.2 ⟨subd8_2_65, List.forall_mem_cons.2 ⟨subd8_2_66, List.forall_mem_cons.2 ⟨subd8_2_67, List.forall_mem_cons.2 ⟨subd8_2_68, List.forall_mem_cons.2 ⟨subd8_2_69, List.forall_mem_cons.2 ⟨subd8_2_70, List.forall_mem_cons.2 ⟨subd8_2_71, List.forall_mem_cons.2 ⟨subd8_2_72, List.forall_mem_cons.2 ⟨subd8_2_73, List.forall_mem_cons.2 ⟨subd8_2_74, List.forall_mem_cons.2 ⟨subd8_2_75, List.forall_mem_cons.2 ⟨subd8_2_76, List.forall_mem_cons.2 ⟨subd8_2_77, List.forall_mem_cons.2 ⟨subd8_2_78, List.forall_mem_cons.2 ⟨subd8_2_79, List.forall_mem_cons.2 ⟨subd8_2_80, List.forall_mem_cons.2 ⟨subd8_2_81, List.forall_mem_cons.2 ⟨subd8_2_82, List.forall_mem_cons.2 ⟨subd8_2_83, List.forall_mem_cons.2 ⟨subd8_2_84, List.forall_mem_cons.2 ⟨subd8_2_85, List.forall_mem_cons.2 ⟨subd8_2_86, List.forall_mem_cons.2 ⟨subd8_2_87, List.forall_mem_cons.2 ⟨subd8_2_88, List.forall_mem_cons.2 ⟨subd8_2_89, List.forall_mem_cons.2 ⟨subd8_2_90, List.forall_mem_cons.2 ⟨subd8_2_91, List.forall_mem_cons.2 ⟨subd8_2_92, List.forall_mem_cons.2 ⟨subd8_2_93, List.forall_mem_cons.2 ⟨subd8_2_94, List.forall_mem_cons.2 ⟨subd8_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_96 : subd8_2 [-1, -1, 3] = true := by decide +kernel
theorem subd8_2_97 : subd8_2 [-1, -1, 4] = true := by decide +kernel
theorem subd8_2_98 : subd8_2 [-1, -1, 5] = true := by decide +kernel
theorem subd8_2_99 : subd8_2 [-1, -1, 6] = true := by decide +kernel
theorem subd8_2_100 : subd8_2 [-1, -1, 7] = true := by decide +kernel
theorem subd8_2_101 : subd8_2 [-1, -1, 8] = true := by decide +kernel
theorem subd8_2_102 : subd8_2 [-1, -1, 9] = true := by decide +kernel
theorem subd8_2_103 : subd8_2 [-1, -1, 10] = true := by decide +kernel
theorem subd8_2_104 : subd8_2 [-1, -1, 11] = true := by decide +kernel
theorem subd8_2_105 : subd8_2 [-1, -1, 12] = true := by decide +kernel
theorem subd8_2_106 : subd8_2 [-1, -1, 13] = true := by decide +kernel
theorem subd8_2_107 : subd8_2 [-1, -1, 14] = true := by decide +kernel
theorem subd8_2_108 : subd8_2 [-1, -1, 15] = true := by decide +kernel
theorem subd8_2_109 : subd8_2 [-1, -1, 16] = true := by decide +kernel
theorem subd8_2_110 : subd8_2 [-1, -1, 17] = true := by decide +kernel
theorem subd8_2_111 : subd8_2 [-1, 0, -20] = true := by decide +kernel
theorem subd8_2_112 : subd8_2 [-1, 0, -19] = true := by decide +kernel
theorem subd8_2_113 : subd8_2 [-1, 0, -18] = true := by decide +kernel
theorem subd8_2_114 : subd8_2 [-1, 0, -17] = true := by decide +kernel
theorem subd8_2_115 : subd8_2 [-1, 0, -16] = true := by decide +kernel
theorem subd8_2_116 : subd8_2 [-1, 0, -15] = true := by decide +kernel
theorem subd8_2_117 : subd8_2 [-1, 0, -14] = true := by decide +kernel
theorem subd8_2_118 : subd8_2 [-1, 0, -13] = true := by decide +kernel
theorem subd8_2_119 : subd8_2 [-1, 0, -12] = true := by decide +kernel
theorem subd8_2_120 : subd8_2 [-1, 0, -11] = true := by decide +kernel
theorem subd8_2_121 : subd8_2 [-1, 0, -10] = true := by decide +kernel
theorem subd8_2_122 : subd8_2 [-1, 0, -9] = true := by decide +kernel
theorem subd8_2_123 : subd8_2 [-1, 0, -8] = true := by decide +kernel
theorem subd8_2_124 : subd8_2 [-1, 0, -7] = true := by decide +kernel
theorem subd8_2_125 : subd8_2 [-1, 0, -6] = true := by decide +kernel
theorem subd8_2_126 : subd8_2 [-1, 0, -5] = true := by decide +kernel
theorem subd8_2_127 : subd8_2 [-1, 0, -4] = true := by decide +kernel
theorem sbd8_2_3 : ∀ q ∈ blkd8_2_3, subd8_2 q = true := by
  unfold blkd8_2_3
  exact List.forall_mem_cons.2 ⟨subd8_2_96, List.forall_mem_cons.2 ⟨subd8_2_97, List.forall_mem_cons.2 ⟨subd8_2_98, List.forall_mem_cons.2 ⟨subd8_2_99, List.forall_mem_cons.2 ⟨subd8_2_100, List.forall_mem_cons.2 ⟨subd8_2_101, List.forall_mem_cons.2 ⟨subd8_2_102, List.forall_mem_cons.2 ⟨subd8_2_103, List.forall_mem_cons.2 ⟨subd8_2_104, List.forall_mem_cons.2 ⟨subd8_2_105, List.forall_mem_cons.2 ⟨subd8_2_106, List.forall_mem_cons.2 ⟨subd8_2_107, List.forall_mem_cons.2 ⟨subd8_2_108, List.forall_mem_cons.2 ⟨subd8_2_109, List.forall_mem_cons.2 ⟨subd8_2_110, List.forall_mem_cons.2 ⟨subd8_2_111, List.forall_mem_cons.2 ⟨subd8_2_112, List.forall_mem_cons.2 ⟨subd8_2_113, List.forall_mem_cons.2 ⟨subd8_2_114, List.forall_mem_cons.2 ⟨subd8_2_115, List.forall_mem_cons.2 ⟨subd8_2_116, List.forall_mem_cons.2 ⟨subd8_2_117, List.forall_mem_cons.2 ⟨subd8_2_118, List.forall_mem_cons.2 ⟨subd8_2_119, List.forall_mem_cons.2 ⟨subd8_2_120, List.forall_mem_cons.2 ⟨subd8_2_121, List.forall_mem_cons.2 ⟨subd8_2_122, List.forall_mem_cons.2 ⟨subd8_2_123, List.forall_mem_cons.2 ⟨subd8_2_124, List.forall_mem_cons.2 ⟨subd8_2_125, List.forall_mem_cons.2 ⟨subd8_2_126, List.forall_mem_cons.2 ⟨subd8_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_128 : subd8_2 [-1, 0, -3] = true := by decide +kernel
theorem subd8_2_129 : subd8_2 [-1, 0, -2] = true := by decide +kernel
theorem subd8_2_130 : subd8_2 [-1, 0, -1] = true := by decide +kernel
theorem subd8_2_131 : subd8_2 [-1, 0, 0] = true := by decide +kernel
theorem subd8_2_132 : subd8_2 [-1, 0, 1] = true := by decide +kernel
theorem subd8_2_133 : subd8_2 [-1, 0, 2] = true := by decide +kernel
theorem subd8_2_134 : subd8_2 [-1, 0, 3] = true := by decide +kernel
theorem subd8_2_135 : subd8_2 [-1, 0, 4] = true := by decide +kernel
theorem subd8_2_136 : subd8_2 [-1, 0, 5] = true := by decide +kernel
theorem subd8_2_137 : subd8_2 [-1, 0, 6] = true := by decide +kernel
theorem subd8_2_138 : subd8_2 [-1, 0, 7] = true := by decide +kernel
theorem subd8_2_139 : subd8_2 [-1, 0, 8] = true := by decide +kernel
theorem subd8_2_140 : subd8_2 [-1, 0, 9] = true := by decide +kernel
theorem subd8_2_141 : subd8_2 [-1, 0, 10] = true := by decide +kernel
theorem subd8_2_142 : subd8_2 [-1, 0, 11] = true := by decide +kernel
theorem subd8_2_143 : subd8_2 [-1, 0, 12] = true := by decide +kernel
theorem subd8_2_144 : subd8_2 [-1, 0, 13] = true := by decide +kernel
theorem subd8_2_145 : subd8_2 [-1, 0, 14] = true := by decide +kernel
theorem subd8_2_146 : subd8_2 [-1, 0, 15] = true := by decide +kernel
theorem subd8_2_147 : subd8_2 [-1, 0, 16] = true := by decide +kernel
theorem subd8_2_148 : subd8_2 [-1, 0, 17] = true := by decide +kernel
theorem subd8_2_149 : subd8_2 [-1, 0, 18] = true := by decide +kernel
theorem subd8_2_150 : subd8_2 [-1, 0, 19] = true := by decide +kernel
theorem subd8_2_151 : subd8_2 [-1, 1, -17] = true := by decide +kernel
theorem subd8_2_152 : subd8_2 [-1, 1, -16] = true := by decide +kernel
theorem subd8_2_153 : subd8_2 [-1, 1, -15] = true := by decide +kernel
theorem subd8_2_154 : subd8_2 [-1, 1, -14] = true := by decide +kernel
theorem subd8_2_155 : subd8_2 [-1, 1, -13] = true := by decide +kernel
theorem subd8_2_156 : subd8_2 [-1, 1, -12] = true := by decide +kernel
theorem subd8_2_157 : subd8_2 [-1, 1, -11] = true := by decide +kernel
theorem subd8_2_158 : subd8_2 [-1, 1, -10] = true := by decide +kernel
theorem subd8_2_159 : subd8_2 [-1, 1, -9] = true := by decide +kernel
theorem sbd8_2_4 : ∀ q ∈ blkd8_2_4, subd8_2 q = true := by
  unfold blkd8_2_4
  exact List.forall_mem_cons.2 ⟨subd8_2_128, List.forall_mem_cons.2 ⟨subd8_2_129, List.forall_mem_cons.2 ⟨subd8_2_130, List.forall_mem_cons.2 ⟨subd8_2_131, List.forall_mem_cons.2 ⟨subd8_2_132, List.forall_mem_cons.2 ⟨subd8_2_133, List.forall_mem_cons.2 ⟨subd8_2_134, List.forall_mem_cons.2 ⟨subd8_2_135, List.forall_mem_cons.2 ⟨subd8_2_136, List.forall_mem_cons.2 ⟨subd8_2_137, List.forall_mem_cons.2 ⟨subd8_2_138, List.forall_mem_cons.2 ⟨subd8_2_139, List.forall_mem_cons.2 ⟨subd8_2_140, List.forall_mem_cons.2 ⟨subd8_2_141, List.forall_mem_cons.2 ⟨subd8_2_142, List.forall_mem_cons.2 ⟨subd8_2_143, List.forall_mem_cons.2 ⟨subd8_2_144, List.forall_mem_cons.2 ⟨subd8_2_145, List.forall_mem_cons.2 ⟨subd8_2_146, List.forall_mem_cons.2 ⟨subd8_2_147, List.forall_mem_cons.2 ⟨subd8_2_148, List.forall_mem_cons.2 ⟨subd8_2_149, List.forall_mem_cons.2 ⟨subd8_2_150, List.forall_mem_cons.2 ⟨subd8_2_151, List.forall_mem_cons.2 ⟨subd8_2_152, List.forall_mem_cons.2 ⟨subd8_2_153, List.forall_mem_cons.2 ⟨subd8_2_154, List.forall_mem_cons.2 ⟨subd8_2_155, List.forall_mem_cons.2 ⟨subd8_2_156, List.forall_mem_cons.2 ⟨subd8_2_157, List.forall_mem_cons.2 ⟨subd8_2_158, List.forall_mem_cons.2 ⟨subd8_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_160 : subd8_2 [-1, 1, -8] = true := by decide +kernel
theorem subd8_2_161 : subd8_2 [-1, 1, -7] = true := by decide +kernel
theorem subd8_2_162 : subd8_2 [-1, 1, -6] = true := by decide +kernel
theorem subd8_2_163 : subd8_2 [-1, 1, -5] = true := by decide +kernel
theorem subd8_2_164 : subd8_2 [-1, 1, -4] = true := by decide +kernel
theorem subd8_2_165 : subd8_2 [-1, 1, -3] = true := by decide +kernel
theorem subd8_2_166 : subd8_2 [-1, 1, -2] = true := by decide +kernel
theorem subd8_2_167 : subd8_2 [-1, 1, -1] = true := by decide +kernel
theorem subd8_2_168 : subd8_2 [-1, 1, 0] = true := by decide +kernel
theorem subd8_2_169 : subd8_2 [-1, 1, 1] = true := by decide +kernel
theorem subd8_2_170 : subd8_2 [-1, 1, 2] = true := by decide +kernel
theorem subd8_2_171 : subd8_2 [-1, 1, 3] = true := by decide +kernel
theorem subd8_2_172 : subd8_2 [-1, 1, 4] = true := by decide +kernel
theorem subd8_2_173 : subd8_2 [-1, 1, 5] = true := by decide +kernel
theorem subd8_2_174 : subd8_2 [-1, 1, 6] = true := by decide +kernel
theorem subd8_2_175 : subd8_2 [-1, 1, 7] = true := by decide +kernel
theorem subd8_2_176 : subd8_2 [-1, 1, 8] = true := by decide +kernel
theorem subd8_2_177 : subd8_2 [-1, 1, 9] = true := by decide +kernel
theorem subd8_2_178 : subd8_2 [-1, 1, 10] = true := by decide +kernel
theorem subd8_2_179 : subd8_2 [-1, 1, 11] = true := by decide +kernel
theorem subd8_2_180 : subd8_2 [-1, 1, 12] = true := by decide +kernel
theorem subd8_2_181 : subd8_2 [-1, 1, 13] = true := by decide +kernel
theorem subd8_2_182 : subd8_2 [-1, 1, 14] = true := by decide +kernel
theorem subd8_2_183 : subd8_2 [-1, 1, 15] = true := by decide +kernel
theorem subd8_2_184 : subd8_2 [-1, 1, 16] = true := by decide +kernel
theorem subd8_2_185 : subd8_2 [-1, 1, 17] = true := by decide +kernel
theorem subd8_2_186 : subd8_2 [-1, 2] = true := by decide +kernel
theorem subd8_2_187 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_188 : subd8_2 [0, -2, -15] = true := by decide +kernel
theorem subd8_2_189 : subd8_2 [0, -2, -14] = true := by decide +kernel
theorem subd8_2_190 : subd8_2 [0, -2, -13] = true := by decide +kernel
theorem subd8_2_191 : subd8_2 [0, -2, -12] = true := by decide +kernel
theorem sbd8_2_5 : ∀ q ∈ blkd8_2_5, subd8_2 q = true := by
  unfold blkd8_2_5
  exact List.forall_mem_cons.2 ⟨subd8_2_160, List.forall_mem_cons.2 ⟨subd8_2_161, List.forall_mem_cons.2 ⟨subd8_2_162, List.forall_mem_cons.2 ⟨subd8_2_163, List.forall_mem_cons.2 ⟨subd8_2_164, List.forall_mem_cons.2 ⟨subd8_2_165, List.forall_mem_cons.2 ⟨subd8_2_166, List.forall_mem_cons.2 ⟨subd8_2_167, List.forall_mem_cons.2 ⟨subd8_2_168, List.forall_mem_cons.2 ⟨subd8_2_169, List.forall_mem_cons.2 ⟨subd8_2_170, List.forall_mem_cons.2 ⟨subd8_2_171, List.forall_mem_cons.2 ⟨subd8_2_172, List.forall_mem_cons.2 ⟨subd8_2_173, List.forall_mem_cons.2 ⟨subd8_2_174, List.forall_mem_cons.2 ⟨subd8_2_175, List.forall_mem_cons.2 ⟨subd8_2_176, List.forall_mem_cons.2 ⟨subd8_2_177, List.forall_mem_cons.2 ⟨subd8_2_178, List.forall_mem_cons.2 ⟨subd8_2_179, List.forall_mem_cons.2 ⟨subd8_2_180, List.forall_mem_cons.2 ⟨subd8_2_181, List.forall_mem_cons.2 ⟨subd8_2_182, List.forall_mem_cons.2 ⟨subd8_2_183, List.forall_mem_cons.2 ⟨subd8_2_184, List.forall_mem_cons.2 ⟨subd8_2_185, List.forall_mem_cons.2 ⟨subd8_2_186, List.forall_mem_cons.2 ⟨subd8_2_187, List.forall_mem_cons.2 ⟨subd8_2_188, List.forall_mem_cons.2 ⟨subd8_2_189, List.forall_mem_cons.2 ⟨subd8_2_190, List.forall_mem_cons.2 ⟨subd8_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_192 : subd8_2 [0, -2, -11] = true := by decide +kernel
theorem subd8_2_193 : subd8_2 [0, -2, -10] = true := by decide +kernel
theorem subd8_2_194 : subd8_2 [0, -2, -9] = true := by decide +kernel
theorem subd8_2_195 : subd8_2 [0, -2, -8] = true := by decide +kernel
theorem subd8_2_196 : subd8_2 [0, -2, -7] = true := by decide +kernel
theorem subd8_2_197 : subd8_2 [0, -2, -6] = true := by decide +kernel
theorem subd8_2_198 : subd8_2 [0, -2, -5] = true := by decide +kernel
theorem subd8_2_199 : subd8_2 [0, -2, -4] = true := by decide +kernel
theorem subd8_2_200 : subd8_2 [0, -2, -3] = true := by decide +kernel
theorem subd8_2_201 : subd8_2 [0, -2, -2] = true := by decide +kernel
theorem subd8_2_202 : subd8_2 [0, -2, -1] = true := by decide +kernel
theorem subd8_2_203 : subd8_2 [0, -2, 0] = true := by decide +kernel
theorem subd8_2_204 : subd8_2 [0, -2, 1] = true := by decide +kernel
theorem subd8_2_205 : subd8_2 [0, -2, 2] = true := by decide +kernel
theorem subd8_2_206 : subd8_2 [0, -2, 3] = true := by decide +kernel
theorem subd8_2_207 : subd8_2 [0, -2, 4] = true := by decide +kernel
theorem subd8_2_208 : subd8_2 [0, -2, 5] = true := by decide +kernel
theorem subd8_2_209 : subd8_2 [0, -2, 6] = true := by decide +kernel
theorem subd8_2_210 : subd8_2 [0, -2, 7] = true := by decide +kernel
theorem subd8_2_211 : subd8_2 [0, -2, 8] = true := by decide +kernel
theorem subd8_2_212 : subd8_2 [0, -2, 9] = true := by decide +kernel
theorem subd8_2_213 : subd8_2 [0, -2, 10] = true := by decide +kernel
theorem subd8_2_214 : subd8_2 [0, -2, 11] = true := by decide +kernel
theorem subd8_2_215 : subd8_2 [0, -2, 12] = true := by decide +kernel
theorem subd8_2_216 : subd8_2 [0, -1, -21] = true := by decide +kernel
theorem subd8_2_217 : subd8_2 [0, -1, -20] = true := by decide +kernel
theorem subd8_2_218 : subd8_2 [0, -1, -19] = true := by decide +kernel
theorem subd8_2_219 : subd8_2 [0, -1, -18] = true := by decide +kernel
theorem subd8_2_220 : subd8_2 [0, -1, -17] = true := by decide +kernel
theorem subd8_2_221 : subd8_2 [0, -1, -16] = true := by decide +kernel
theorem subd8_2_222 : subd8_2 [0, -1, -15] = true := by decide +kernel
theorem subd8_2_223 : subd8_2 [0, -1, -14] = true := by decide +kernel
theorem sbd8_2_6 : ∀ q ∈ blkd8_2_6, subd8_2 q = true := by
  unfold blkd8_2_6
  exact List.forall_mem_cons.2 ⟨subd8_2_192, List.forall_mem_cons.2 ⟨subd8_2_193, List.forall_mem_cons.2 ⟨subd8_2_194, List.forall_mem_cons.2 ⟨subd8_2_195, List.forall_mem_cons.2 ⟨subd8_2_196, List.forall_mem_cons.2 ⟨subd8_2_197, List.forall_mem_cons.2 ⟨subd8_2_198, List.forall_mem_cons.2 ⟨subd8_2_199, List.forall_mem_cons.2 ⟨subd8_2_200, List.forall_mem_cons.2 ⟨subd8_2_201, List.forall_mem_cons.2 ⟨subd8_2_202, List.forall_mem_cons.2 ⟨subd8_2_203, List.forall_mem_cons.2 ⟨subd8_2_204, List.forall_mem_cons.2 ⟨subd8_2_205, List.forall_mem_cons.2 ⟨subd8_2_206, List.forall_mem_cons.2 ⟨subd8_2_207, List.forall_mem_cons.2 ⟨subd8_2_208, List.forall_mem_cons.2 ⟨subd8_2_209, List.forall_mem_cons.2 ⟨subd8_2_210, List.forall_mem_cons.2 ⟨subd8_2_211, List.forall_mem_cons.2 ⟨subd8_2_212, List.forall_mem_cons.2 ⟨subd8_2_213, List.forall_mem_cons.2 ⟨subd8_2_214, List.forall_mem_cons.2 ⟨subd8_2_215, List.forall_mem_cons.2 ⟨subd8_2_216, List.forall_mem_cons.2 ⟨subd8_2_217, List.forall_mem_cons.2 ⟨subd8_2_218, List.forall_mem_cons.2 ⟨subd8_2_219, List.forall_mem_cons.2 ⟨subd8_2_220, List.forall_mem_cons.2 ⟨subd8_2_221, List.forall_mem_cons.2 ⟨subd8_2_222, List.forall_mem_cons.2 ⟨subd8_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
