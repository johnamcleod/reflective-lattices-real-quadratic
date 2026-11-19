import ReflectZphi.Data.Cert5.C090.Base

namespace ReflectZphi.Data.Cert5.C090

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_0 : ldCheck G d3_0.U d3_0.ms ldd3_0 = true := by decide +kernel
theorem pre_okd3_0 : subPre G cell3 d3_0 = true := by decide +kernel
theorem subd3_0_0 : subd3_0 [-2] = true := by decide +kernel
theorem subd3_0_1 : subd3_0 [-1] = true := by decide +kernel
theorem subd3_0_2 : subd3_0 [0] = true := by decide +kernel
theorem subd3_0_3 : subd3_0 [1] = true := by decide +kernel
theorem subd3_0_4 : subd3_0 [2] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_cons.2 ⟨subd3_0_1, List.forall_mem_cons.2 ⟨subd3_0_2, List.forall_mem_cons.2 ⟨subd3_0_3, List.forall_mem_cons.2 ⟨subd3_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [-2] = true := by decide +kernel
theorem subd3_1_1 : subd3_1 [-1] = true := by decide +kernel
theorem subd3_1_2 : subd3_1 [0] = true := by decide +kernel
theorem subd3_1_3 : subd3_1 [1] = true := by decide +kernel
theorem subd3_1_4 : subd3_1 [2] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_cons.2 ⟨subd3_1_1, List.forall_mem_cons.2 ⟨subd3_1_2, List.forall_mem_cons.2 ⟨subd3_1_3, List.forall_mem_cons.2 ⟨subd3_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_nil _⟩
theorem ld_okd3_3 : ldCheck G d3_3.U d3_3.ms ldd3_3 = true := by decide +kernel
theorem pre_okd3_3 : subPre G cell3 d3_3 = true := by decide +kernel
theorem subd3_3_0 : subd3_3 [-1] = true := by decide +kernel
theorem subd3_3_1 : subd3_3 [0] = true := by decide +kernel
theorem subd3_3_2 : subd3_3 [1] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_cons.2 ⟨subd3_3_1, List.forall_mem_cons.2 ⟨subd3_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd3_4 : ldCheck G d3_4.U d3_4.ms ldd3_4 = true := by decide +kernel
theorem pre_okd3_4 : subPre G cell3 d3_4 = true := by decide +kernel
theorem subd3_4_0 : subd3_4 [-2] = true := by decide +kernel
theorem subd3_4_1 : subd3_4 [-1, -3] = true := by decide +kernel
theorem subd3_4_2 : subd3_4 [-1, -2] = true := by decide +kernel
theorem subd3_4_3 : subd3_4 [-1, -1, -9] = true := by decide +kernel
theorem subd3_4_4 : subd3_4 [-1, -1, -8] = true := by decide +kernel
theorem subd3_4_5 : subd3_4 [-1, -1, -7] = true := by decide +kernel
theorem subd3_4_6 : subd3_4 [-1, -1, -6] = true := by decide +kernel
theorem subd3_4_7 : subd3_4 [-1, -1, -5] = true := by decide +kernel
theorem subd3_4_8 : subd3_4 [-1, -1, -4] = true := by decide +kernel
theorem subd3_4_9 : subd3_4 [-1, -1, -3] = true := by decide +kernel
theorem subd3_4_10 : subd3_4 [-1, -1, -2] = true := by decide +kernel
theorem subd3_4_11 : subd3_4 [-1, -1, -1] = true := by decide +kernel
theorem subd3_4_12 : subd3_4 [-1, -1, 0] = true := by decide +kernel
theorem subd3_4_13 : subd3_4 [-1, -1, 1] = true := by decide +kernel
theorem subd3_4_14 : subd3_4 [-1, -1, 2] = true := by decide +kernel
theorem subd3_4_15 : subd3_4 [-1, -1, 3] = true := by decide +kernel
theorem subd3_4_16 : subd3_4 [-1, -1, 4] = true := by decide +kernel
theorem subd3_4_17 : subd3_4 [-1, -1, 5] = true := by decide +kernel
theorem subd3_4_18 : subd3_4 [-1, -1, 6] = true := by decide +kernel
theorem subd3_4_19 : subd3_4 [-1, -1, 7] = true := by decide +kernel
theorem subd3_4_20 : subd3_4 [-1, 0, -9] = true := by decide +kernel
theorem subd3_4_21 : subd3_4 [-1, 0, -8] = true := by decide +kernel
theorem subd3_4_22 : subd3_4 [-1, 0, -7] = true := by decide +kernel
theorem subd3_4_23 : subd3_4 [-1, 0, -6] = true := by decide +kernel
theorem subd3_4_24 : subd3_4 [-1, 0, -5] = true := by decide +kernel
theorem subd3_4_25 : subd3_4 [-1, 0, -4] = true := by decide +kernel
theorem subd3_4_26 : subd3_4 [-1, 0, -3] = true := by decide +kernel
theorem subd3_4_27 : subd3_4 [-1, 0, -2] = true := by decide +kernel
theorem subd3_4_28 : subd3_4 [-1, 0, -1] = true := by decide +kernel
theorem subd3_4_29 : subd3_4 [-1, 0, 0] = true := by decide +kernel
theorem subd3_4_30 : subd3_4 [-1, 0, 1] = true := by decide +kernel
theorem subd3_4_31 : subd3_4 [-1, 0, 2] = true := by decide +kernel
theorem sbd3_4_0 : ∀ q ∈ blkd3_4_0, subd3_4 q = true := by
  unfold blkd3_4_0
  exact List.forall_mem_cons.2 ⟨subd3_4_0, List.forall_mem_cons.2 ⟨subd3_4_1, List.forall_mem_cons.2 ⟨subd3_4_2, List.forall_mem_cons.2 ⟨subd3_4_3, List.forall_mem_cons.2 ⟨subd3_4_4, List.forall_mem_cons.2 ⟨subd3_4_5, List.forall_mem_cons.2 ⟨subd3_4_6, List.forall_mem_cons.2 ⟨subd3_4_7, List.forall_mem_cons.2 ⟨subd3_4_8, List.forall_mem_cons.2 ⟨subd3_4_9, List.forall_mem_cons.2 ⟨subd3_4_10, List.forall_mem_cons.2 ⟨subd3_4_11, List.forall_mem_cons.2 ⟨subd3_4_12, List.forall_mem_cons.2 ⟨subd3_4_13, List.forall_mem_cons.2 ⟨subd3_4_14, List.forall_mem_cons.2 ⟨subd3_4_15, List.forall_mem_cons.2 ⟨subd3_4_16, List.forall_mem_cons.2 ⟨subd3_4_17, List.forall_mem_cons.2 ⟨subd3_4_18, List.forall_mem_cons.2 ⟨subd3_4_19, List.forall_mem_cons.2 ⟨subd3_4_20, List.forall_mem_cons.2 ⟨subd3_4_21, List.forall_mem_cons.2 ⟨subd3_4_22, List.forall_mem_cons.2 ⟨subd3_4_23, List.forall_mem_cons.2 ⟨subd3_4_24, List.forall_mem_cons.2 ⟨subd3_4_25, List.forall_mem_cons.2 ⟨subd3_4_26, List.forall_mem_cons.2 ⟨subd3_4_27, List.forall_mem_cons.2 ⟨subd3_4_28, List.forall_mem_cons.2 ⟨subd3_4_29, List.forall_mem_cons.2 ⟨subd3_4_30, List.forall_mem_cons.2 ⟨subd3_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_4_32 : subd3_4 [-1, 0, 3] = true := by decide +kernel
theorem subd3_4_33 : subd3_4 [-1, 0, 4] = true := by decide +kernel
theorem subd3_4_34 : subd3_4 [-1, 0, 5] = true := by decide +kernel
theorem subd3_4_35 : subd3_4 [-1, 0, 6] = true := by decide +kernel
theorem subd3_4_36 : subd3_4 [-1, 0, 7] = true := by decide +kernel
theorem subd3_4_37 : subd3_4 [-1, 1, -7] = true := by decide +kernel
theorem subd3_4_38 : subd3_4 [-1, 1, -6] = true := by decide +kernel
theorem subd3_4_39 : subd3_4 [-1, 1, -5] = true := by decide +kernel
theorem subd3_4_40 : subd3_4 [-1, 1, -4] = true := by decide +kernel
theorem subd3_4_41 : subd3_4 [-1, 1, -3] = true := by decide +kernel
theorem subd3_4_42 : subd3_4 [-1, 1, -2] = true := by decide +kernel
theorem subd3_4_43 : subd3_4 [-1, 1, -1] = true := by decide +kernel
theorem subd3_4_44 : subd3_4 [-1, 1, 0] = true := by decide +kernel
theorem subd3_4_45 : subd3_4 [-1, 1, 1] = true := by decide +kernel
theorem subd3_4_46 : subd3_4 [-1, 1, 2] = true := by decide +kernel
theorem subd3_4_47 : subd3_4 [-1, 1, 3] = true := by decide +kernel
theorem subd3_4_48 : subd3_4 [-1, 1, 4] = true := by decide +kernel
theorem subd3_4_49 : subd3_4 [-1, 1, 5] = true := by decide +kernel
theorem subd3_4_50 : subd3_4 [-1, 1, 6] = true := by decide +kernel
theorem subd3_4_51 : subd3_4 [0, -3] = true := by decide +kernel
theorem subd3_4_52 : subd3_4 [0, -2] = true := by decide +kernel
theorem subd3_4_53 : subd3_4 [0, -1, -9] = true := by decide +kernel
theorem subd3_4_54 : subd3_4 [0, -1, -8] = true := by decide +kernel
theorem subd3_4_55 : subd3_4 [0, -1, -7] = true := by decide +kernel
theorem subd3_4_56 : subd3_4 [0, -1, -6] = true := by decide +kernel
theorem subd3_4_57 : subd3_4 [0, -1, -5] = true := by decide +kernel
theorem subd3_4_58 : subd3_4 [0, -1, -4] = true := by decide +kernel
theorem subd3_4_59 : subd3_4 [0, -1, -3] = true := by decide +kernel
theorem subd3_4_60 : subd3_4 [0, -1, -2] = true := by decide +kernel
theorem subd3_4_61 : subd3_4 [0, -1, -1] = true := by decide +kernel
theorem subd3_4_62 : subd3_4 [0, -1, 0] = true := by decide +kernel
theorem subd3_4_63 : subd3_4 [0, -1, 1] = true := by decide +kernel
theorem sbd3_4_1 : ∀ q ∈ blkd3_4_1, subd3_4 q = true := by
  unfold blkd3_4_1
  exact List.forall_mem_cons.2 ⟨subd3_4_32, List.forall_mem_cons.2 ⟨subd3_4_33, List.forall_mem_cons.2 ⟨subd3_4_34, List.forall_mem_cons.2 ⟨subd3_4_35, List.forall_mem_cons.2 ⟨subd3_4_36, List.forall_mem_cons.2 ⟨subd3_4_37, List.forall_mem_cons.2 ⟨subd3_4_38, List.forall_mem_cons.2 ⟨subd3_4_39, List.forall_mem_cons.2 ⟨subd3_4_40, List.forall_mem_cons.2 ⟨subd3_4_41, List.forall_mem_cons.2 ⟨subd3_4_42, List.forall_mem_cons.2 ⟨subd3_4_43, List.forall_mem_cons.2 ⟨subd3_4_44, List.forall_mem_cons.2 ⟨subd3_4_45, List.forall_mem_cons.2 ⟨subd3_4_46, List.forall_mem_cons.2 ⟨subd3_4_47, List.forall_mem_cons.2 ⟨subd3_4_48, List.forall_mem_cons.2 ⟨subd3_4_49, List.forall_mem_cons.2 ⟨subd3_4_50, List.forall_mem_cons.2 ⟨subd3_4_51, List.forall_mem_cons.2 ⟨subd3_4_52, List.forall_mem_cons.2 ⟨subd3_4_53, List.forall_mem_cons.2 ⟨subd3_4_54, List.forall_mem_cons.2 ⟨subd3_4_55, List.forall_mem_cons.2 ⟨subd3_4_56, List.forall_mem_cons.2 ⟨subd3_4_57, List.forall_mem_cons.2 ⟨subd3_4_58, List.forall_mem_cons.2 ⟨subd3_4_59, List.forall_mem_cons.2 ⟨subd3_4_60, List.forall_mem_cons.2 ⟨subd3_4_61, List.forall_mem_cons.2 ⟨subd3_4_62, List.forall_mem_cons.2 ⟨subd3_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_4_64 : subd3_4 [0, -1, 2] = true := by decide +kernel
theorem subd3_4_65 : subd3_4 [0, -1, 3] = true := by decide +kernel
theorem subd3_4_66 : subd3_4 [0, -1, 4] = true := by decide +kernel
theorem subd3_4_67 : subd3_4 [0, -1, 5] = true := by decide +kernel
theorem subd3_4_68 : subd3_4 [0, -1, 6] = true := by decide +kernel
theorem subd3_4_69 : subd3_4 [0, -1, 7] = true := by decide +kernel
theorem subd3_4_70 : subd3_4 [0, 0, -10] = true := by decide +kernel
theorem subd3_4_71 : subd3_4 [0, 0, -9] = true := by decide +kernel
theorem subd3_4_72 : subd3_4 [0, 0, -8] = true := by decide +kernel
theorem subd3_4_73 : subd3_4 [0, 0, -7] = true := by decide +kernel
theorem subd3_4_74 : subd3_4 [0, 0, -6] = true := by decide +kernel
theorem subd3_4_75 : subd3_4 [0, 0, -5] = true := by decide +kernel
theorem subd3_4_76 : subd3_4 [0, 0, -4] = true := by decide +kernel
theorem subd3_4_77 : subd3_4 [0, 0, -3] = true := by decide +kernel
theorem subd3_4_78 : subd3_4 [0, 0, -2] = true := by decide +kernel
theorem subd3_4_79 : subd3_4 [0, 0, -1] = true := by decide +kernel
theorem subd3_4_80 : subd3_4 [0, 0, 0] = true := by decide +kernel
theorem subd3_4_81 : subd3_4 [0, 0, 1] = true := by decide +kernel
theorem subd3_4_82 : subd3_4 [0, 0, 2] = true := by decide +kernel
theorem subd3_4_83 : subd3_4 [0, 0, 3] = true := by decide +kernel
theorem subd3_4_84 : subd3_4 [0, 0, 4] = true := by decide +kernel
theorem subd3_4_85 : subd3_4 [0, 0, 5] = true := by decide +kernel
theorem subd3_4_86 : subd3_4 [0, 0, 6] = true := by decide +kernel
theorem subd3_4_87 : subd3_4 [0, 0, 7] = true := by decide +kernel
theorem subd3_4_88 : subd3_4 [0, 0, 8] = true := by decide +kernel
theorem subd3_4_89 : subd3_4 [0, 0, 9] = true := by decide +kernel
theorem subd3_4_90 : subd3_4 [0, 1, -8] = true := by decide +kernel
theorem subd3_4_91 : subd3_4 [0, 1, -7] = true := by decide +kernel
theorem subd3_4_92 : subd3_4 [0, 1, -6] = true := by decide +kernel
theorem subd3_4_93 : subd3_4 [0, 1, -5] = true := by decide +kernel
theorem subd3_4_94 : subd3_4 [0, 1, -4] = true := by decide +kernel
theorem subd3_4_95 : subd3_4 [0, 1, -3] = true := by decide +kernel
theorem sbd3_4_2 : ∀ q ∈ blkd3_4_2, subd3_4 q = true := by
  unfold blkd3_4_2
  exact List.forall_mem_cons.2 ⟨subd3_4_64, List.forall_mem_cons.2 ⟨subd3_4_65, List.forall_mem_cons.2 ⟨subd3_4_66, List.forall_mem_cons.2 ⟨subd3_4_67, List.forall_mem_cons.2 ⟨subd3_4_68, List.forall_mem_cons.2 ⟨subd3_4_69, List.forall_mem_cons.2 ⟨subd3_4_70, List.forall_mem_cons.2 ⟨subd3_4_71, List.forall_mem_cons.2 ⟨subd3_4_72, List.forall_mem_cons.2 ⟨subd3_4_73, List.forall_mem_cons.2 ⟨subd3_4_74, List.forall_mem_cons.2 ⟨subd3_4_75, List.forall_mem_cons.2 ⟨subd3_4_76, List.forall_mem_cons.2 ⟨subd3_4_77, List.forall_mem_cons.2 ⟨subd3_4_78, List.forall_mem_cons.2 ⟨subd3_4_79, List.forall_mem_cons.2 ⟨subd3_4_80, List.forall_mem_cons.2 ⟨subd3_4_81, List.forall_mem_cons.2 ⟨subd3_4_82, List.forall_mem_cons.2 ⟨subd3_4_83, List.forall_mem_cons.2 ⟨subd3_4_84, List.forall_mem_cons.2 ⟨subd3_4_85, List.forall_mem_cons.2 ⟨subd3_4_86, List.forall_mem_cons.2 ⟨subd3_4_87, List.forall_mem_cons.2 ⟨subd3_4_88, List.forall_mem_cons.2 ⟨subd3_4_89, List.forall_mem_cons.2 ⟨subd3_4_90, List.forall_mem_cons.2 ⟨subd3_4_91, List.forall_mem_cons.2 ⟨subd3_4_92, List.forall_mem_cons.2 ⟨subd3_4_93, List.forall_mem_cons.2 ⟨subd3_4_94, List.forall_mem_cons.2 ⟨subd3_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_4_96 : subd3_4 [0, 1, -2] = true := by decide +kernel
theorem subd3_4_97 : subd3_4 [0, 1, -1] = true := by decide +kernel
theorem subd3_4_98 : subd3_4 [0, 1, 0] = true := by decide +kernel
theorem subd3_4_99 : subd3_4 [0, 1, 1] = true := by decide +kernel
theorem subd3_4_100 : subd3_4 [0, 1, 2] = true := by decide +kernel
theorem subd3_4_101 : subd3_4 [0, 1, 3] = true := by decide +kernel
theorem subd3_4_102 : subd3_4 [0, 1, 4] = true := by decide +kernel
theorem subd3_4_103 : subd3_4 [0, 1, 5] = true := by decide +kernel
theorem subd3_4_104 : subd3_4 [0, 1, 6] = true := by decide +kernel
theorem subd3_4_105 : subd3_4 [0, 1, 7] = true := by decide +kernel
theorem subd3_4_106 : subd3_4 [0, 1, 8] = true := by decide +kernel
theorem subd3_4_107 : subd3_4 [0, 2] = true := by decide +kernel
theorem subd3_4_108 : subd3_4 [1, -2] = true := by decide +kernel
theorem subd3_4_109 : subd3_4 [1, -1, -7] = true := by decide +kernel
theorem subd3_4_110 : subd3_4 [1, -1, -6] = true := by decide +kernel
theorem subd3_4_111 : subd3_4 [1, -1, -5] = true := by decide +kernel
theorem subd3_4_112 : subd3_4 [1, -1, -4] = true := by decide +kernel
theorem subd3_4_113 : subd3_4 [1, -1, -3] = true := by decide +kernel
theorem subd3_4_114 : subd3_4 [1, -1, -2] = true := by decide +kernel
theorem subd3_4_115 : subd3_4 [1, -1, -1] = true := by decide +kernel
theorem subd3_4_116 : subd3_4 [1, -1, 0] = true := by decide +kernel
theorem subd3_4_117 : subd3_4 [1, -1, 1] = true := by decide +kernel
theorem subd3_4_118 : subd3_4 [1, -1, 2] = true := by decide +kernel
theorem subd3_4_119 : subd3_4 [1, -1, 3] = true := by decide +kernel
theorem subd3_4_120 : subd3_4 [1, -1, 4] = true := by decide +kernel
theorem subd3_4_121 : subd3_4 [1, -1, 5] = true := by decide +kernel
theorem subd3_4_122 : subd3_4 [1, -1, 6] = true := by decide +kernel
theorem subd3_4_123 : subd3_4 [1, 0, -8] = true := by decide +kernel
theorem subd3_4_124 : subd3_4 [1, 0, -7] = true := by decide +kernel
theorem subd3_4_125 : subd3_4 [1, 0, -6] = true := by decide +kernel
theorem subd3_4_126 : subd3_4 [1, 0, -5] = true := by decide +kernel
theorem subd3_4_127 : subd3_4 [1, 0, -4] = true := by decide +kernel
theorem sbd3_4_3 : ∀ q ∈ blkd3_4_3, subd3_4 q = true := by
  unfold blkd3_4_3
  exact List.forall_mem_cons.2 ⟨subd3_4_96, List.forall_mem_cons.2 ⟨subd3_4_97, List.forall_mem_cons.2 ⟨subd3_4_98, List.forall_mem_cons.2 ⟨subd3_4_99, List.forall_mem_cons.2 ⟨subd3_4_100, List.forall_mem_cons.2 ⟨subd3_4_101, List.forall_mem_cons.2 ⟨subd3_4_102, List.forall_mem_cons.2 ⟨subd3_4_103, List.forall_mem_cons.2 ⟨subd3_4_104, List.forall_mem_cons.2 ⟨subd3_4_105, List.forall_mem_cons.2 ⟨subd3_4_106, List.forall_mem_cons.2 ⟨subd3_4_107, List.forall_mem_cons.2 ⟨subd3_4_108, List.forall_mem_cons.2 ⟨subd3_4_109, List.forall_mem_cons.2 ⟨subd3_4_110, List.forall_mem_cons.2 ⟨subd3_4_111, List.forall_mem_cons.2 ⟨subd3_4_112, List.forall_mem_cons.2 ⟨subd3_4_113, List.forall_mem_cons.2 ⟨subd3_4_114, List.forall_mem_cons.2 ⟨subd3_4_115, List.forall_mem_cons.2 ⟨subd3_4_116, List.forall_mem_cons.2 ⟨subd3_4_117, List.forall_mem_cons.2 ⟨subd3_4_118, List.forall_mem_cons.2 ⟨subd3_4_119, List.forall_mem_cons.2 ⟨subd3_4_120, List.forall_mem_cons.2 ⟨subd3_4_121, List.forall_mem_cons.2 ⟨subd3_4_122, List.forall_mem_cons.2 ⟨subd3_4_123, List.forall_mem_cons.2 ⟨subd3_4_124, List.forall_mem_cons.2 ⟨subd3_4_125, List.forall_mem_cons.2 ⟨subd3_4_126, List.forall_mem_cons.2 ⟨subd3_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_4_128 : subd3_4 [1, 0, -3] = true := by decide +kernel
theorem subd3_4_129 : subd3_4 [1, 0, -2] = true := by decide +kernel
theorem subd3_4_130 : subd3_4 [1, 0, -1] = true := by decide +kernel
theorem subd3_4_131 : subd3_4 [1, 0, 0] = true := by decide +kernel
theorem subd3_4_132 : subd3_4 [1, 0, 1] = true := by decide +kernel
theorem subd3_4_133 : subd3_4 [1, 0, 2] = true := by decide +kernel
theorem subd3_4_134 : subd3_4 [1, 0, 3] = true := by decide +kernel
theorem subd3_4_135 : subd3_4 [1, 0, 4] = true := by decide +kernel
theorem subd3_4_136 : subd3_4 [1, 0, 5] = true := by decide +kernel
theorem subd3_4_137 : subd3_4 [1, 0, 6] = true := by decide +kernel
theorem subd3_4_138 : subd3_4 [1, 0, 7] = true := by decide +kernel
theorem subd3_4_139 : subd3_4 [1, 0, 8] = true := by decide +kernel
theorem subd3_4_140 : subd3_4 [1, 1, -8] = true := by decide +kernel
theorem subd3_4_141 : subd3_4 [1, 1, -7] = true := by decide +kernel
theorem subd3_4_142 : subd3_4 [1, 1, -6] = true := by decide +kernel
theorem subd3_4_143 : subd3_4 [1, 1, -5] = true := by decide +kernel
theorem subd3_4_144 : subd3_4 [1, 1, -4] = true := by decide +kernel
theorem subd3_4_145 : subd3_4 [1, 1, -3] = true := by decide +kernel
theorem subd3_4_146 : subd3_4 [1, 1, -2] = true := by decide +kernel
theorem subd3_4_147 : subd3_4 [1, 1, -1] = true := by decide +kernel
theorem subd3_4_148 : subd3_4 [1, 1, 0] = true := by decide +kernel
theorem subd3_4_149 : subd3_4 [1, 1, 1] = true := by decide +kernel
theorem subd3_4_150 : subd3_4 [1, 1, 2] = true := by decide +kernel
theorem subd3_4_151 : subd3_4 [1, 1, 3] = true := by decide +kernel
theorem subd3_4_152 : subd3_4 [1, 1, 4] = true := by decide +kernel
theorem subd3_4_153 : subd3_4 [1, 1, 5] = true := by decide +kernel
theorem subd3_4_154 : subd3_4 [1, 1, 6] = true := by decide +kernel
theorem subd3_4_155 : subd3_4 [1, 1, 7] = true := by decide +kernel
theorem subd3_4_156 : subd3_4 [1, 1, 8] = true := by decide +kernel
theorem subd3_4_157 : subd3_4 [1, 2] = true := by decide +kernel
theorem subd3_4_158 : subd3_4 [2] = true := by decide +kernel
theorem sbd3_4_4 : ∀ q ∈ blkd3_4_4, subd3_4 q = true := by
  unfold blkd3_4_4
  exact List.forall_mem_cons.2 ⟨subd3_4_128, List.forall_mem_cons.2 ⟨subd3_4_129, List.forall_mem_cons.2 ⟨subd3_4_130, List.forall_mem_cons.2 ⟨subd3_4_131, List.forall_mem_cons.2 ⟨subd3_4_132, List.forall_mem_cons.2 ⟨subd3_4_133, List.forall_mem_cons.2 ⟨subd3_4_134, List.forall_mem_cons.2 ⟨subd3_4_135, List.forall_mem_cons.2 ⟨subd3_4_136, List.forall_mem_cons.2 ⟨subd3_4_137, List.forall_mem_cons.2 ⟨subd3_4_138, List.forall_mem_cons.2 ⟨subd3_4_139, List.forall_mem_cons.2 ⟨subd3_4_140, List.forall_mem_cons.2 ⟨subd3_4_141, List.forall_mem_cons.2 ⟨subd3_4_142, List.forall_mem_cons.2 ⟨subd3_4_143, List.forall_mem_cons.2 ⟨subd3_4_144, List.forall_mem_cons.2 ⟨subd3_4_145, List.forall_mem_cons.2 ⟨subd3_4_146, List.forall_mem_cons.2 ⟨subd3_4_147, List.forall_mem_cons.2 ⟨subd3_4_148, List.forall_mem_cons.2 ⟨subd3_4_149, List.forall_mem_cons.2 ⟨subd3_4_150, List.forall_mem_cons.2 ⟨subd3_4_151, List.forall_mem_cons.2 ⟨subd3_4_152, List.forall_mem_cons.2 ⟨subd3_4_153, List.forall_mem_cons.2 ⟨subd3_4_154, List.forall_mem_cons.2 ⟨subd3_4_155, List.forall_mem_cons.2 ⟨subd3_4_156, List.forall_mem_cons.2 ⟨subd3_4_157, List.forall_mem_cons.2 ⟨subd3_4_158, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C090
