import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_608 : subd8_1 [3, 2, 3] = true := by decide +kernel
theorem subd8_1_609 : subd8_1 [3, 2, 4] = true := by decide +kernel
theorem subd8_1_610 : subd8_1 [3, 2, 5] = true := by decide +kernel
theorem subd8_1_611 : subd8_1 [3, 3, -8] = true := by decide +kernel
theorem subd8_1_612 : subd8_1 [3, 3, -7] = true := by decide +kernel
theorem subd8_1_613 : subd8_1 [3, 3, -6] = true := by decide +kernel
theorem subd8_1_614 : subd8_1 [3, 3, -5] = true := by decide +kernel
theorem subd8_1_615 : subd8_1 [3, 3, -4] = true := by decide +kernel
theorem subd8_1_616 : subd8_1 [3, 3, -3] = true := by decide +kernel
theorem subd8_1_617 : subd8_1 [3, 3, -2] = true := by decide +kernel
theorem subd8_1_618 : subd8_1 [3, 3, -1] = true := by decide +kernel
theorem subd8_1_619 : subd8_1 [3, 3, 0] = true := by decide +kernel
theorem subd8_1_620 : subd8_1 [3, 3, 1] = true := by decide +kernel
theorem subd8_1_621 : subd8_1 [3, 3, 2] = true := by decide +kernel
theorem subd8_1_622 : subd8_1 [3, 3, 3] = true := by decide +kernel
theorem subd8_1_623 : subd8_1 [3, 3, 4] = true := by decide +kernel
theorem subd8_1_624 : subd8_1 [3, 3, 5] = true := by decide +kernel
theorem subd8_1_625 : subd8_1 [3, 4] = true := by decide +kernel
theorem subd8_1_626 : subd8_1 [3, 5] = true := by decide +kernel
theorem subd8_1_627 : subd8_1 [3, 6] = true := by decide +kernel
theorem subd8_1_628 : subd8_1 [3, 7] = true := by decide +kernel
theorem subd8_1_629 : subd8_1 [4, -4] = true := by decide +kernel
theorem subd8_1_630 : subd8_1 [4, -3] = true := by decide +kernel
theorem subd8_1_631 : subd8_1 [4, -2] = true := by decide +kernel
theorem subd8_1_632 : subd8_1 [4, -1] = true := by decide +kernel
theorem subd8_1_633 : subd8_1 [4, 0] = true := by decide +kernel
theorem subd8_1_634 : subd8_1 [4, 1] = true := by decide +kernel
theorem subd8_1_635 : subd8_1 [4, 2] = true := by decide +kernel
theorem subd8_1_636 : subd8_1 [4, 3] = true := by decide +kernel
theorem subd8_1_637 : subd8_1 [4, 4] = true := by decide +kernel
theorem subd8_1_638 : subd8_1 [4, 5] = true := by decide +kernel
theorem subd8_1_639 : subd8_1 [4, 6] = true := by decide +kernel
theorem sbd8_1_19 : ∀ q ∈ blkd8_1_19, subd8_1 q = true := by
  unfold blkd8_1_19
  exact List.forall_mem_cons.2 ⟨subd8_1_608, List.forall_mem_cons.2 ⟨subd8_1_609, List.forall_mem_cons.2 ⟨subd8_1_610, List.forall_mem_cons.2 ⟨subd8_1_611, List.forall_mem_cons.2 ⟨subd8_1_612, List.forall_mem_cons.2 ⟨subd8_1_613, List.forall_mem_cons.2 ⟨subd8_1_614, List.forall_mem_cons.2 ⟨subd8_1_615, List.forall_mem_cons.2 ⟨subd8_1_616, List.forall_mem_cons.2 ⟨subd8_1_617, List.forall_mem_cons.2 ⟨subd8_1_618, List.forall_mem_cons.2 ⟨subd8_1_619, List.forall_mem_cons.2 ⟨subd8_1_620, List.forall_mem_cons.2 ⟨subd8_1_621, List.forall_mem_cons.2 ⟨subd8_1_622, List.forall_mem_cons.2 ⟨subd8_1_623, List.forall_mem_cons.2 ⟨subd8_1_624, List.forall_mem_cons.2 ⟨subd8_1_625, List.forall_mem_cons.2 ⟨subd8_1_626, List.forall_mem_cons.2 ⟨subd8_1_627, List.forall_mem_cons.2 ⟨subd8_1_628, List.forall_mem_cons.2 ⟨subd8_1_629, List.forall_mem_cons.2 ⟨subd8_1_630, List.forall_mem_cons.2 ⟨subd8_1_631, List.forall_mem_cons.2 ⟨subd8_1_632, List.forall_mem_cons.2 ⟨subd8_1_633, List.forall_mem_cons.2 ⟨subd8_1_634, List.forall_mem_cons.2 ⟨subd8_1_635, List.forall_mem_cons.2 ⟨subd8_1_636, List.forall_mem_cons.2 ⟨subd8_1_637, List.forall_mem_cons.2 ⟨subd8_1_638, List.forall_mem_cons.2 ⟨subd8_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_640 : subd8_1 [4, 7] = true := by decide +kernel
theorem subd8_1_641 : subd8_1 [5, -3] = true := by decide +kernel
theorem subd8_1_642 : subd8_1 [5, -2] = true := by decide +kernel
theorem subd8_1_643 : subd8_1 [5, -1] = true := by decide +kernel
theorem subd8_1_644 : subd8_1 [5, 0] = true := by decide +kernel
theorem subd8_1_645 : subd8_1 [5, 1] = true := by decide +kernel
theorem subd8_1_646 : subd8_1 [5, 2] = true := by decide +kernel
theorem subd8_1_647 : subd8_1 [5, 3] = true := by decide +kernel
theorem subd8_1_648 : subd8_1 [5, 4] = true := by decide +kernel
theorem subd8_1_649 : subd8_1 [5, 5] = true := by decide +kernel
theorem subd8_1_650 : subd8_1 [5, 6] = true := by decide +kernel
theorem subd8_1_651 : subd8_1 [5, 7] = true := by decide +kernel
theorem subd8_1_652 : subd8_1 [6] = true := by decide +kernel
theorem sbd8_1_20 : ∀ q ∈ blkd8_1_20, subd8_1 q = true := by
  unfold blkd8_1_20
  exact List.forall_mem_cons.2 ⟨subd8_1_640, List.forall_mem_cons.2 ⟨subd8_1_641, List.forall_mem_cons.2 ⟨subd8_1_642, List.forall_mem_cons.2 ⟨subd8_1_643, List.forall_mem_cons.2 ⟨subd8_1_644, List.forall_mem_cons.2 ⟨subd8_1_645, List.forall_mem_cons.2 ⟨subd8_1_646, List.forall_mem_cons.2 ⟨subd8_1_647, List.forall_mem_cons.2 ⟨subd8_1_648, List.forall_mem_cons.2 ⟨subd8_1_649, List.forall_mem_cons.2 ⟨subd8_1_650, List.forall_mem_cons.2 ⟨subd8_1_651, List.forall_mem_cons.2 ⟨subd8_1_652, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-2, -3] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-2, -2] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-2, -1] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-2, 0] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-2, 1] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-1, -3] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [-1, -2] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [-1, -1, -7] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [-1, -1, -6] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [-1, -1, -5] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [-1, -1, -4] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [-1, -1, -3] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [-1, -1, -2] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [-1, -1, -1] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [-1, -1, 0] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [-1, -1, 1] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [-1, -1, 2] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [-1, -1, 3] = true := by decide +kernel
theorem subd8_2_18 : subd8_2 [-1, -1, 4] = true := by decide +kernel
theorem subd8_2_19 : subd8_2 [-1, -1, 5] = true := by decide +kernel
theorem subd8_2_20 : subd8_2 [-1, -1, 6] = true := by decide +kernel
theorem subd8_2_21 : subd8_2 [-1, 0, -7] = true := by decide +kernel
theorem subd8_2_22 : subd8_2 [-1, 0, -6] = true := by decide +kernel
theorem subd8_2_23 : subd8_2 [-1, 0, -5] = true := by decide +kernel
theorem subd8_2_24 : subd8_2 [-1, 0, -4] = true := by decide +kernel
theorem subd8_2_25 : subd8_2 [-1, 0, -3] = true := by decide +kernel
theorem subd8_2_26 : subd8_2 [-1, 0, -2] = true := by decide +kernel
theorem subd8_2_27 : subd8_2 [-1, 0, -1] = true := by decide +kernel
theorem subd8_2_28 : subd8_2 [-1, 0, 0] = true := by decide +kernel
theorem subd8_2_29 : subd8_2 [-1, 0, 1] = true := by decide +kernel
theorem subd8_2_30 : subd8_2 [-1, 0, 2] = true := by decide +kernel
theorem subd8_2_31 : subd8_2 [-1, 0, 3] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_cons.2 ⟨subd8_2_18, List.forall_mem_cons.2 ⟨subd8_2_19, List.forall_mem_cons.2 ⟨subd8_2_20, List.forall_mem_cons.2 ⟨subd8_2_21, List.forall_mem_cons.2 ⟨subd8_2_22, List.forall_mem_cons.2 ⟨subd8_2_23, List.forall_mem_cons.2 ⟨subd8_2_24, List.forall_mem_cons.2 ⟨subd8_2_25, List.forall_mem_cons.2 ⟨subd8_2_26, List.forall_mem_cons.2 ⟨subd8_2_27, List.forall_mem_cons.2 ⟨subd8_2_28, List.forall_mem_cons.2 ⟨subd8_2_29, List.forall_mem_cons.2 ⟨subd8_2_30, List.forall_mem_cons.2 ⟨subd8_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_32 : subd8_2 [-1, 0, 4] = true := by decide +kernel
theorem subd8_2_33 : subd8_2 [-1, 0, 5] = true := by decide +kernel
theorem subd8_2_34 : subd8_2 [-1, 0, 6] = true := by decide +kernel
theorem subd8_2_35 : subd8_2 [-1, 1] = true := by decide +kernel
theorem subd8_2_36 : subd8_2 [-1, 2] = true := by decide +kernel
theorem subd8_2_37 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_38 : subd8_2 [0, -2] = true := by decide +kernel
theorem subd8_2_39 : subd8_2 [0, -1, -7] = true := by decide +kernel
theorem subd8_2_40 : subd8_2 [0, -1, -6] = true := by decide +kernel
theorem subd8_2_41 : subd8_2 [0, -1, -5] = true := by decide +kernel
theorem subd8_2_42 : subd8_2 [0, -1, -4] = true := by decide +kernel
theorem subd8_2_43 : subd8_2 [0, -1, -3] = true := by decide +kernel
theorem subd8_2_44 : subd8_2 [0, -1, -2] = true := by decide +kernel
theorem subd8_2_45 : subd8_2 [0, -1, -1] = true := by decide +kernel
theorem subd8_2_46 : subd8_2 [0, -1, 0] = true := by decide +kernel
theorem subd8_2_47 : subd8_2 [0, -1, 1] = true := by decide +kernel
theorem subd8_2_48 : subd8_2 [0, -1, 2] = true := by decide +kernel
theorem subd8_2_49 : subd8_2 [0, -1, 3] = true := by decide +kernel
theorem subd8_2_50 : subd8_2 [0, -1, 4] = true := by decide +kernel
theorem subd8_2_51 : subd8_2 [0, -1, 5] = true := by decide +kernel
theorem subd8_2_52 : subd8_2 [0, -1, 6] = true := by decide +kernel
theorem subd8_2_53 : subd8_2 [0, -1, 7] = true := by decide +kernel
theorem subd8_2_54 : subd8_2 [0, 0, -8] = true := by decide +kernel
theorem subd8_2_55 : subd8_2 [0, 0, -7] = true := by decide +kernel
theorem subd8_2_56 : subd8_2 [0, 0, -6] = true := by decide +kernel
theorem subd8_2_57 : subd8_2 [0, 0, -5] = true := by decide +kernel
theorem subd8_2_58 : subd8_2 [0, 0, -4] = true := by decide +kernel
theorem subd8_2_59 : subd8_2 [0, 0, -3] = true := by decide +kernel
theorem subd8_2_60 : subd8_2 [0, 0, -2] = true := by decide +kernel
theorem subd8_2_61 : subd8_2 [0, 0, -1] = true := by decide +kernel
theorem subd8_2_62 : subd8_2 [0, 0, 0] = true := by decide +kernel
theorem subd8_2_63 : subd8_2 [0, 0, 1] = true := by decide +kernel
theorem sbd8_2_1 : ∀ q ∈ blkd8_2_1, subd8_2 q = true := by
  unfold blkd8_2_1
  exact List.forall_mem_cons.2 ⟨subd8_2_32, List.forall_mem_cons.2 ⟨subd8_2_33, List.forall_mem_cons.2 ⟨subd8_2_34, List.forall_mem_cons.2 ⟨subd8_2_35, List.forall_mem_cons.2 ⟨subd8_2_36, List.forall_mem_cons.2 ⟨subd8_2_37, List.forall_mem_cons.2 ⟨subd8_2_38, List.forall_mem_cons.2 ⟨subd8_2_39, List.forall_mem_cons.2 ⟨subd8_2_40, List.forall_mem_cons.2 ⟨subd8_2_41, List.forall_mem_cons.2 ⟨subd8_2_42, List.forall_mem_cons.2 ⟨subd8_2_43, List.forall_mem_cons.2 ⟨subd8_2_44, List.forall_mem_cons.2 ⟨subd8_2_45, List.forall_mem_cons.2 ⟨subd8_2_46, List.forall_mem_cons.2 ⟨subd8_2_47, List.forall_mem_cons.2 ⟨subd8_2_48, List.forall_mem_cons.2 ⟨subd8_2_49, List.forall_mem_cons.2 ⟨subd8_2_50, List.forall_mem_cons.2 ⟨subd8_2_51, List.forall_mem_cons.2 ⟨subd8_2_52, List.forall_mem_cons.2 ⟨subd8_2_53, List.forall_mem_cons.2 ⟨subd8_2_54, List.forall_mem_cons.2 ⟨subd8_2_55, List.forall_mem_cons.2 ⟨subd8_2_56, List.forall_mem_cons.2 ⟨subd8_2_57, List.forall_mem_cons.2 ⟨subd8_2_58, List.forall_mem_cons.2 ⟨subd8_2_59, List.forall_mem_cons.2 ⟨subd8_2_60, List.forall_mem_cons.2 ⟨subd8_2_61, List.forall_mem_cons.2 ⟨subd8_2_62, List.forall_mem_cons.2 ⟨subd8_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_64 : subd8_2 [0, 0, 2] = true := by decide +kernel
theorem subd8_2_65 : subd8_2 [0, 0, 3] = true := by decide +kernel
theorem subd8_2_66 : subd8_2 [0, 0, 4] = true := by decide +kernel
theorem subd8_2_67 : subd8_2 [0, 0, 5] = true := by decide +kernel
theorem subd8_2_68 : subd8_2 [0, 0, 6] = true := by decide +kernel
theorem subd8_2_69 : subd8_2 [0, 0, 7] = true := by decide +kernel
theorem subd8_2_70 : subd8_2 [0, 1, -8] = true := by decide +kernel
theorem subd8_2_71 : subd8_2 [0, 1, -7] = true := by decide +kernel
theorem subd8_2_72 : subd8_2 [0, 1, -6] = true := by decide +kernel
theorem subd8_2_73 : subd8_2 [0, 1, -5] = true := by decide +kernel
theorem subd8_2_74 : subd8_2 [0, 1, -4] = true := by decide +kernel
theorem subd8_2_75 : subd8_2 [0, 1, -3] = true := by decide +kernel
theorem subd8_2_76 : subd8_2 [0, 1, -2] = true := by decide +kernel
theorem subd8_2_77 : subd8_2 [0, 1, -1] = true := by decide +kernel
theorem subd8_2_78 : subd8_2 [0, 1, 0] = true := by decide +kernel
theorem subd8_2_79 : subd8_2 [0, 1, 1] = true := by decide +kernel
theorem subd8_2_80 : subd8_2 [0, 1, 2] = true := by decide +kernel
theorem subd8_2_81 : subd8_2 [0, 1, 3] = true := by decide +kernel
theorem subd8_2_82 : subd8_2 [0, 1, 4] = true := by decide +kernel
theorem subd8_2_83 : subd8_2 [0, 1, 5] = true := by decide +kernel
theorem subd8_2_84 : subd8_2 [0, 1, 6] = true := by decide +kernel
theorem subd8_2_85 : subd8_2 [0, 2] = true := by decide +kernel
theorem subd8_2_86 : subd8_2 [1, -3] = true := by decide +kernel
theorem subd8_2_87 : subd8_2 [1, -2] = true := by decide +kernel
theorem subd8_2_88 : subd8_2 [1, -1] = true := by decide +kernel
theorem subd8_2_89 : subd8_2 [1, 0, -7] = true := by decide +kernel
theorem subd8_2_90 : subd8_2 [1, 0, -6] = true := by decide +kernel
theorem subd8_2_91 : subd8_2 [1, 0, -5] = true := by decide +kernel
theorem subd8_2_92 : subd8_2 [1, 0, -4] = true := by decide +kernel
theorem subd8_2_93 : subd8_2 [1, 0, -3] = true := by decide +kernel
theorem subd8_2_94 : subd8_2 [1, 0, -2] = true := by decide +kernel
theorem subd8_2_95 : subd8_2 [1, 0, -1] = true := by decide +kernel
theorem sbd8_2_2 : ∀ q ∈ blkd8_2_2, subd8_2 q = true := by
  unfold blkd8_2_2
  exact List.forall_mem_cons.2 ⟨subd8_2_64, List.forall_mem_cons.2 ⟨subd8_2_65, List.forall_mem_cons.2 ⟨subd8_2_66, List.forall_mem_cons.2 ⟨subd8_2_67, List.forall_mem_cons.2 ⟨subd8_2_68, List.forall_mem_cons.2 ⟨subd8_2_69, List.forall_mem_cons.2 ⟨subd8_2_70, List.forall_mem_cons.2 ⟨subd8_2_71, List.forall_mem_cons.2 ⟨subd8_2_72, List.forall_mem_cons.2 ⟨subd8_2_73, List.forall_mem_cons.2 ⟨subd8_2_74, List.forall_mem_cons.2 ⟨subd8_2_75, List.forall_mem_cons.2 ⟨subd8_2_76, List.forall_mem_cons.2 ⟨subd8_2_77, List.forall_mem_cons.2 ⟨subd8_2_78, List.forall_mem_cons.2 ⟨subd8_2_79, List.forall_mem_cons.2 ⟨subd8_2_80, List.forall_mem_cons.2 ⟨subd8_2_81, List.forall_mem_cons.2 ⟨subd8_2_82, List.forall_mem_cons.2 ⟨subd8_2_83, List.forall_mem_cons.2 ⟨subd8_2_84, List.forall_mem_cons.2 ⟨subd8_2_85, List.forall_mem_cons.2 ⟨subd8_2_86, List.forall_mem_cons.2 ⟨subd8_2_87, List.forall_mem_cons.2 ⟨subd8_2_88, List.forall_mem_cons.2 ⟨subd8_2_89, List.forall_mem_cons.2 ⟨subd8_2_90, List.forall_mem_cons.2 ⟨subd8_2_91, List.forall_mem_cons.2 ⟨subd8_2_92, List.forall_mem_cons.2 ⟨subd8_2_93, List.forall_mem_cons.2 ⟨subd8_2_94, List.forall_mem_cons.2 ⟨subd8_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_96 : subd8_2 [1, 0, 0] = true := by decide +kernel
theorem subd8_2_97 : subd8_2 [1, 0, 1] = true := by decide +kernel
theorem subd8_2_98 : subd8_2 [1, 0, 2] = true := by decide +kernel
theorem subd8_2_99 : subd8_2 [1, 0, 3] = true := by decide +kernel
theorem subd8_2_100 : subd8_2 [1, 0, 4] = true := by decide +kernel
theorem subd8_2_101 : subd8_2 [1, 0, 5] = true := by decide +kernel
theorem subd8_2_102 : subd8_2 [1, 0, 6] = true := by decide +kernel
theorem subd8_2_103 : subd8_2 [1, 1, -7] = true := by decide +kernel
theorem subd8_2_104 : subd8_2 [1, 1, -6] = true := by decide +kernel
theorem subd8_2_105 : subd8_2 [1, 1, -5] = true := by decide +kernel
theorem subd8_2_106 : subd8_2 [1, 1, -4] = true := by decide +kernel
theorem subd8_2_107 : subd8_2 [1, 1, -3] = true := by decide +kernel
theorem subd8_2_108 : subd8_2 [1, 1, -2] = true := by decide +kernel
theorem subd8_2_109 : subd8_2 [1, 1, -1] = true := by decide +kernel
theorem subd8_2_110 : subd8_2 [1, 1, 0] = true := by decide +kernel
theorem subd8_2_111 : subd8_2 [1, 1, 1] = true := by decide +kernel
theorem subd8_2_112 : subd8_2 [1, 1, 2] = true := by decide +kernel
theorem subd8_2_113 : subd8_2 [1, 1, 3] = true := by decide +kernel
theorem subd8_2_114 : subd8_2 [1, 1, 4] = true := by decide +kernel
theorem subd8_2_115 : subd8_2 [1, 1, 5] = true := by decide +kernel
theorem subd8_2_116 : subd8_2 [1, 1, 6] = true := by decide +kernel
theorem subd8_2_117 : subd8_2 [1, 2] = true := by decide +kernel
theorem subd8_2_118 : subd8_2 [2, -2] = true := by decide +kernel
theorem subd8_2_119 : subd8_2 [2, -1] = true := by decide +kernel
theorem subd8_2_120 : subd8_2 [2, 0] = true := by decide +kernel
theorem subd8_2_121 : subd8_2 [2, 1] = true := by decide +kernel
theorem subd8_2_122 : subd8_2 [2, 2] = true := by decide +kernel
theorem sbd8_2_3 : ∀ q ∈ blkd8_2_3, subd8_2 q = true := by
  unfold blkd8_2_3
  exact List.forall_mem_cons.2 ⟨subd8_2_96, List.forall_mem_cons.2 ⟨subd8_2_97, List.forall_mem_cons.2 ⟨subd8_2_98, List.forall_mem_cons.2 ⟨subd8_2_99, List.forall_mem_cons.2 ⟨subd8_2_100, List.forall_mem_cons.2 ⟨subd8_2_101, List.forall_mem_cons.2 ⟨subd8_2_102, List.forall_mem_cons.2 ⟨subd8_2_103, List.forall_mem_cons.2 ⟨subd8_2_104, List.forall_mem_cons.2 ⟨subd8_2_105, List.forall_mem_cons.2 ⟨subd8_2_106, List.forall_mem_cons.2 ⟨subd8_2_107, List.forall_mem_cons.2 ⟨subd8_2_108, List.forall_mem_cons.2 ⟨subd8_2_109, List.forall_mem_cons.2 ⟨subd8_2_110, List.forall_mem_cons.2 ⟨subd8_2_111, List.forall_mem_cons.2 ⟨subd8_2_112, List.forall_mem_cons.2 ⟨subd8_2_113, List.forall_mem_cons.2 ⟨subd8_2_114, List.forall_mem_cons.2 ⟨subd8_2_115, List.forall_mem_cons.2 ⟨subd8_2_116, List.forall_mem_cons.2 ⟨subd8_2_117, List.forall_mem_cons.2 ⟨subd8_2_118, List.forall_mem_cons.2 ⟨subd8_2_119, List.forall_mem_cons.2 ⟨subd8_2_120, List.forall_mem_cons.2 ⟨subd8_2_121, List.forall_mem_cons.2 ⟨subd8_2_122, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C077
