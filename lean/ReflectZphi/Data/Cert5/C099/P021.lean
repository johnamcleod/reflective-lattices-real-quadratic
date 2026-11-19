import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_nil _⟩
theorem ld_okd8_4 : ldCheck G d8_4.U d8_4.ms ldd8_4 = true := by decide +kernel
theorem pre_okd8_4 : subPre G cell8 d8_4 = true := by decide +kernel
theorem subd8_4_0 : subd8_4 [-2] = true := by decide +kernel
theorem subd8_4_1 : subd8_4 [-1] = true := by decide +kernel
theorem subd8_4_2 : subd8_4 [0] = true := by decide +kernel
theorem subd8_4_3 : subd8_4 [1] = true := by decide +kernel
theorem subd8_4_4 : subd8_4 [2] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_cons.2 ⟨subd8_4_1, List.forall_mem_cons.2 ⟨subd8_4_2, List.forall_mem_cons.2 ⟨subd8_4_3, List.forall_mem_cons.2 ⟨subd8_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_5 : ldCheck G d8_5.U d8_5.ms ldd8_5 = true := by decide +kernel
theorem pre_okd8_5 : subPre G cell8 d8_5 = true := by decide +kernel
theorem subd8_5_0 : subd8_5 [-1, -2] = true := by decide +kernel
theorem subd8_5_1 : subd8_5 [-1, -1] = true := by decide +kernel
theorem subd8_5_2 : subd8_5 [-1, 0] = true := by decide +kernel
theorem subd8_5_3 : subd8_5 [-1, 1] = true := by decide +kernel
theorem subd8_5_4 : subd8_5 [0, -2] = true := by decide +kernel
theorem subd8_5_5 : subd8_5 [0, -1] = true := by decide +kernel
theorem subd8_5_6 : subd8_5 [0, 0] = true := by decide +kernel
theorem subd8_5_7 : subd8_5 [0, 1] = true := by decide +kernel
theorem subd8_5_8 : subd8_5 [1, -2] = true := by decide +kernel
theorem subd8_5_9 : subd8_5 [1, -1] = true := by decide +kernel
theorem subd8_5_10 : subd8_5 [1, 0] = true := by decide +kernel
theorem subd8_5_11 : subd8_5 [1, 1] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_cons.2 ⟨subd8_5_1, List.forall_mem_cons.2 ⟨subd8_5_2, List.forall_mem_cons.2 ⟨subd8_5_3, List.forall_mem_cons.2 ⟨subd8_5_4, List.forall_mem_cons.2 ⟨subd8_5_5, List.forall_mem_cons.2 ⟨subd8_5_6, List.forall_mem_cons.2 ⟨subd8_5_7, List.forall_mem_cons.2 ⟨subd8_5_8, List.forall_mem_cons.2 ⟨subd8_5_9, List.forall_mem_cons.2 ⟨subd8_5_10, List.forall_mem_cons.2 ⟨subd8_5_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_6 : ldCheck G d8_6.U d8_6.ms ldd8_6 = true := by decide +kernel
theorem pre_okd8_6 : subPre G cell8 d8_6 = true := by decide +kernel
theorem subd8_6_0 : subd8_6 [-2, -3] = true := by decide +kernel
theorem subd8_6_1 : subd8_6 [-2, -2] = true := by decide +kernel
theorem subd8_6_2 : subd8_6 [-2, -1] = true := by decide +kernel
theorem subd8_6_3 : subd8_6 [-2, 0] = true := by decide +kernel
theorem subd8_6_4 : subd8_6 [-2, 1] = true := by decide +kernel
theorem subd8_6_5 : subd8_6 [-1, -3] = true := by decide +kernel
theorem subd8_6_6 : subd8_6 [-1, -2] = true := by decide +kernel
theorem subd8_6_7 : subd8_6 [-1, -1, -7] = true := by decide +kernel
theorem subd8_6_8 : subd8_6 [-1, -1, -6] = true := by decide +kernel
theorem subd8_6_9 : subd8_6 [-1, -1, -5] = true := by decide +kernel
theorem subd8_6_10 : subd8_6 [-1, -1, -4] = true := by decide +kernel
theorem subd8_6_11 : subd8_6 [-1, -1, -3] = true := by decide +kernel
theorem subd8_6_12 : subd8_6 [-1, -1, -2] = true := by decide +kernel
theorem subd8_6_13 : subd8_6 [-1, -1, -1] = true := by decide +kernel
theorem subd8_6_14 : subd8_6 [-1, -1, 0] = true := by decide +kernel
theorem subd8_6_15 : subd8_6 [-1, -1, 1] = true := by decide +kernel
theorem subd8_6_16 : subd8_6 [-1, -1, 2] = true := by decide +kernel
theorem subd8_6_17 : subd8_6 [-1, -1, 3] = true := by decide +kernel
theorem subd8_6_18 : subd8_6 [-1, -1, 4] = true := by decide +kernel
theorem subd8_6_19 : subd8_6 [-1, -1, 5] = true := by decide +kernel
theorem subd8_6_20 : subd8_6 [-1, -1, 6] = true := by decide +kernel
theorem subd8_6_21 : subd8_6 [-1, -1, 7] = true := by decide +kernel
theorem subd8_6_22 : subd8_6 [-1, 0, -8] = true := by decide +kernel
theorem subd8_6_23 : subd8_6 [-1, 0, -7] = true := by decide +kernel
theorem subd8_6_24 : subd8_6 [-1, 0, -6] = true := by decide +kernel
theorem subd8_6_25 : subd8_6 [-1, 0, -5] = true := by decide +kernel
theorem subd8_6_26 : subd8_6 [-1, 0, -4] = true := by decide +kernel
theorem subd8_6_27 : subd8_6 [-1, 0, -3] = true := by decide +kernel
theorem subd8_6_28 : subd8_6 [-1, 0, -2] = true := by decide +kernel
theorem subd8_6_29 : subd8_6 [-1, 0, -1] = true := by decide +kernel
theorem subd8_6_30 : subd8_6 [-1, 0, 0] = true := by decide +kernel
theorem subd8_6_31 : subd8_6 [-1, 0, 1] = true := by decide +kernel
theorem sbd8_6_0 : ∀ q ∈ blkd8_6_0, subd8_6 q = true := by
  unfold blkd8_6_0
  exact List.forall_mem_cons.2 ⟨subd8_6_0, List.forall_mem_cons.2 ⟨subd8_6_1, List.forall_mem_cons.2 ⟨subd8_6_2, List.forall_mem_cons.2 ⟨subd8_6_3, List.forall_mem_cons.2 ⟨subd8_6_4, List.forall_mem_cons.2 ⟨subd8_6_5, List.forall_mem_cons.2 ⟨subd8_6_6, List.forall_mem_cons.2 ⟨subd8_6_7, List.forall_mem_cons.2 ⟨subd8_6_8, List.forall_mem_cons.2 ⟨subd8_6_9, List.forall_mem_cons.2 ⟨subd8_6_10, List.forall_mem_cons.2 ⟨subd8_6_11, List.forall_mem_cons.2 ⟨subd8_6_12, List.forall_mem_cons.2 ⟨subd8_6_13, List.forall_mem_cons.2 ⟨subd8_6_14, List.forall_mem_cons.2 ⟨subd8_6_15, List.forall_mem_cons.2 ⟨subd8_6_16, List.forall_mem_cons.2 ⟨subd8_6_17, List.forall_mem_cons.2 ⟨subd8_6_18, List.forall_mem_cons.2 ⟨subd8_6_19, List.forall_mem_cons.2 ⟨subd8_6_20, List.forall_mem_cons.2 ⟨subd8_6_21, List.forall_mem_cons.2 ⟨subd8_6_22, List.forall_mem_cons.2 ⟨subd8_6_23, List.forall_mem_cons.2 ⟨subd8_6_24, List.forall_mem_cons.2 ⟨subd8_6_25, List.forall_mem_cons.2 ⟨subd8_6_26, List.forall_mem_cons.2 ⟨subd8_6_27, List.forall_mem_cons.2 ⟨subd8_6_28, List.forall_mem_cons.2 ⟨subd8_6_29, List.forall_mem_cons.2 ⟨subd8_6_30, List.forall_mem_cons.2 ⟨subd8_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_6_32 : subd8_6 [-1, 0, 2] = true := by decide +kernel
theorem subd8_6_33 : subd8_6 [-1, 0, 3] = true := by decide +kernel
theorem subd8_6_34 : subd8_6 [-1, 0, 4] = true := by decide +kernel
theorem subd8_6_35 : subd8_6 [-1, 0, 5] = true := by decide +kernel
theorem subd8_6_36 : subd8_6 [-1, 0, 6] = true := by decide +kernel
theorem subd8_6_37 : subd8_6 [-1, 0, 7] = true := by decide +kernel
theorem subd8_6_38 : subd8_6 [-1, 1] = true := by decide +kernel
theorem subd8_6_39 : subd8_6 [-1, 2] = true := by decide +kernel
theorem subd8_6_40 : subd8_6 [0, -3] = true := by decide +kernel
theorem subd8_6_41 : subd8_6 [0, -2] = true := by decide +kernel
theorem subd8_6_42 : subd8_6 [0, -1, -8] = true := by decide +kernel
theorem subd8_6_43 : subd8_6 [0, -1, -7] = true := by decide +kernel
theorem subd8_6_44 : subd8_6 [0, -1, -6] = true := by decide +kernel
theorem subd8_6_45 : subd8_6 [0, -1, -5] = true := by decide +kernel
theorem subd8_6_46 : subd8_6 [0, -1, -4] = true := by decide +kernel
theorem subd8_6_47 : subd8_6 [0, -1, -3] = true := by decide +kernel
theorem subd8_6_48 : subd8_6 [0, -1, -2] = true := by decide +kernel
theorem subd8_6_49 : subd8_6 [0, -1, -1] = true := by decide +kernel
theorem subd8_6_50 : subd8_6 [0, -1, 0] = true := by decide +kernel
theorem subd8_6_51 : subd8_6 [0, -1, 1] = true := by decide +kernel
theorem subd8_6_52 : subd8_6 [0, -1, 2] = true := by decide +kernel
theorem subd8_6_53 : subd8_6 [0, -1, 3] = true := by decide +kernel
theorem subd8_6_54 : subd8_6 [0, -1, 4] = true := by decide +kernel
theorem subd8_6_55 : subd8_6 [0, -1, 5] = true := by decide +kernel
theorem subd8_6_56 : subd8_6 [0, -1, 6] = true := by decide +kernel
theorem subd8_6_57 : subd8_6 [0, -1, 7] = true := by decide +kernel
theorem subd8_6_58 : subd8_6 [0, 0, -9] = true := by decide +kernel
theorem subd8_6_59 : subd8_6 [0, 0, -8] = true := by decide +kernel
theorem subd8_6_60 : subd8_6 [0, 0, -7] = true := by decide +kernel
theorem subd8_6_61 : subd8_6 [0, 0, -6] = true := by decide +kernel
theorem subd8_6_62 : subd8_6 [0, 0, -5] = true := by decide +kernel
theorem subd8_6_63 : subd8_6 [0, 0, -4] = true := by decide +kernel
theorem sbd8_6_1 : ∀ q ∈ blkd8_6_1, subd8_6 q = true := by
  unfold blkd8_6_1
  exact List.forall_mem_cons.2 ⟨subd8_6_32, List.forall_mem_cons.2 ⟨subd8_6_33, List.forall_mem_cons.2 ⟨subd8_6_34, List.forall_mem_cons.2 ⟨subd8_6_35, List.forall_mem_cons.2 ⟨subd8_6_36, List.forall_mem_cons.2 ⟨subd8_6_37, List.forall_mem_cons.2 ⟨subd8_6_38, List.forall_mem_cons.2 ⟨subd8_6_39, List.forall_mem_cons.2 ⟨subd8_6_40, List.forall_mem_cons.2 ⟨subd8_6_41, List.forall_mem_cons.2 ⟨subd8_6_42, List.forall_mem_cons.2 ⟨subd8_6_43, List.forall_mem_cons.2 ⟨subd8_6_44, List.forall_mem_cons.2 ⟨subd8_6_45, List.forall_mem_cons.2 ⟨subd8_6_46, List.forall_mem_cons.2 ⟨subd8_6_47, List.forall_mem_cons.2 ⟨subd8_6_48, List.forall_mem_cons.2 ⟨subd8_6_49, List.forall_mem_cons.2 ⟨subd8_6_50, List.forall_mem_cons.2 ⟨subd8_6_51, List.forall_mem_cons.2 ⟨subd8_6_52, List.forall_mem_cons.2 ⟨subd8_6_53, List.forall_mem_cons.2 ⟨subd8_6_54, List.forall_mem_cons.2 ⟨subd8_6_55, List.forall_mem_cons.2 ⟨subd8_6_56, List.forall_mem_cons.2 ⟨subd8_6_57, List.forall_mem_cons.2 ⟨subd8_6_58, List.forall_mem_cons.2 ⟨subd8_6_59, List.forall_mem_cons.2 ⟨subd8_6_60, List.forall_mem_cons.2 ⟨subd8_6_61, List.forall_mem_cons.2 ⟨subd8_6_62, List.forall_mem_cons.2 ⟨subd8_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_6_64 : subd8_6 [0, 0, -3] = true := by decide +kernel
theorem subd8_6_65 : subd8_6 [0, 0, -2] = true := by decide +kernel
theorem subd8_6_66 : subd8_6 [0, 0, -1] = true := by decide +kernel
theorem subd8_6_67 : subd8_6 [0, 0, 0] = true := by decide +kernel
theorem subd8_6_68 : subd8_6 [0, 0, 1] = true := by decide +kernel
theorem subd8_6_69 : subd8_6 [0, 0, 2] = true := by decide +kernel
theorem subd8_6_70 : subd8_6 [0, 0, 3] = true := by decide +kernel
theorem subd8_6_71 : subd8_6 [0, 0, 4] = true := by decide +kernel
theorem subd8_6_72 : subd8_6 [0, 0, 5] = true := by decide +kernel
theorem subd8_6_73 : subd8_6 [0, 0, 6] = true := by decide +kernel
theorem subd8_6_74 : subd8_6 [0, 0, 7] = true := by decide +kernel
theorem subd8_6_75 : subd8_6 [0, 0, 8] = true := by decide +kernel
theorem subd8_6_76 : subd8_6 [0, 1, -8] = true := by decide +kernel
theorem subd8_6_77 : subd8_6 [0, 1, -7] = true := by decide +kernel
theorem subd8_6_78 : subd8_6 [0, 1, -6] = true := by decide +kernel
theorem subd8_6_79 : subd8_6 [0, 1, -5] = true := by decide +kernel
theorem subd8_6_80 : subd8_6 [0, 1, -4] = true := by decide +kernel
theorem subd8_6_81 : subd8_6 [0, 1, -3] = true := by decide +kernel
theorem subd8_6_82 : subd8_6 [0, 1, -2] = true := by decide +kernel
theorem subd8_6_83 : subd8_6 [0, 1, -1] = true := by decide +kernel
theorem subd8_6_84 : subd8_6 [0, 1, 0] = true := by decide +kernel
theorem subd8_6_85 : subd8_6 [0, 1, 1] = true := by decide +kernel
theorem subd8_6_86 : subd8_6 [0, 1, 2] = true := by decide +kernel
theorem subd8_6_87 : subd8_6 [0, 1, 3] = true := by decide +kernel
theorem subd8_6_88 : subd8_6 [0, 1, 4] = true := by decide +kernel
theorem subd8_6_89 : subd8_6 [0, 1, 5] = true := by decide +kernel
theorem subd8_6_90 : subd8_6 [0, 1, 6] = true := by decide +kernel
theorem subd8_6_91 : subd8_6 [0, 1, 7] = true := by decide +kernel
theorem subd8_6_92 : subd8_6 [0, 2] = true := by decide +kernel
theorem subd8_6_93 : subd8_6 [1, -3] = true := by decide +kernel
theorem subd8_6_94 : subd8_6 [1, -2] = true := by decide +kernel
theorem subd8_6_95 : subd8_6 [1, -1] = true := by decide +kernel
theorem sbd8_6_2 : ∀ q ∈ blkd8_6_2, subd8_6 q = true := by
  unfold blkd8_6_2
  exact List.forall_mem_cons.2 ⟨subd8_6_64, List.forall_mem_cons.2 ⟨subd8_6_65, List.forall_mem_cons.2 ⟨subd8_6_66, List.forall_mem_cons.2 ⟨subd8_6_67, List.forall_mem_cons.2 ⟨subd8_6_68, List.forall_mem_cons.2 ⟨subd8_6_69, List.forall_mem_cons.2 ⟨subd8_6_70, List.forall_mem_cons.2 ⟨subd8_6_71, List.forall_mem_cons.2 ⟨subd8_6_72, List.forall_mem_cons.2 ⟨subd8_6_73, List.forall_mem_cons.2 ⟨subd8_6_74, List.forall_mem_cons.2 ⟨subd8_6_75, List.forall_mem_cons.2 ⟨subd8_6_76, List.forall_mem_cons.2 ⟨subd8_6_77, List.forall_mem_cons.2 ⟨subd8_6_78, List.forall_mem_cons.2 ⟨subd8_6_79, List.forall_mem_cons.2 ⟨subd8_6_80, List.forall_mem_cons.2 ⟨subd8_6_81, List.forall_mem_cons.2 ⟨subd8_6_82, List.forall_mem_cons.2 ⟨subd8_6_83, List.forall_mem_cons.2 ⟨subd8_6_84, List.forall_mem_cons.2 ⟨subd8_6_85, List.forall_mem_cons.2 ⟨subd8_6_86, List.forall_mem_cons.2 ⟨subd8_6_87, List.forall_mem_cons.2 ⟨subd8_6_88, List.forall_mem_cons.2 ⟨subd8_6_89, List.forall_mem_cons.2 ⟨subd8_6_90, List.forall_mem_cons.2 ⟨subd8_6_91, List.forall_mem_cons.2 ⟨subd8_6_92, List.forall_mem_cons.2 ⟨subd8_6_93, List.forall_mem_cons.2 ⟨subd8_6_94, List.forall_mem_cons.2 ⟨subd8_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_6_96 : subd8_6 [1, 0, -8] = true := by decide +kernel
theorem subd8_6_97 : subd8_6 [1, 0, -7] = true := by decide +kernel
theorem subd8_6_98 : subd8_6 [1, 0, -6] = true := by decide +kernel
theorem subd8_6_99 : subd8_6 [1, 0, -5] = true := by decide +kernel
theorem subd8_6_100 : subd8_6 [1, 0, -4] = true := by decide +kernel
theorem subd8_6_101 : subd8_6 [1, 0, -3] = true := by decide +kernel
theorem subd8_6_102 : subd8_6 [1, 0, -2] = true := by decide +kernel
theorem subd8_6_103 : subd8_6 [1, 0, -1] = true := by decide +kernel
theorem subd8_6_104 : subd8_6 [1, 0, 0] = true := by decide +kernel
theorem subd8_6_105 : subd8_6 [1, 0, 1] = true := by decide +kernel
theorem subd8_6_106 : subd8_6 [1, 0, 2] = true := by decide +kernel
theorem subd8_6_107 : subd8_6 [1, 0, 3] = true := by decide +kernel
theorem subd8_6_108 : subd8_6 [1, 0, 4] = true := by decide +kernel
theorem subd8_6_109 : subd8_6 [1, 0, 5] = true := by decide +kernel
theorem subd8_6_110 : subd8_6 [1, 0, 6] = true := by decide +kernel
theorem subd8_6_111 : subd8_6 [1, 0, 7] = true := by decide +kernel
theorem subd8_6_112 : subd8_6 [1, 1, -8] = true := by decide +kernel
theorem subd8_6_113 : subd8_6 [1, 1, -7] = true := by decide +kernel
theorem subd8_6_114 : subd8_6 [1, 1, -6] = true := by decide +kernel
theorem subd8_6_115 : subd8_6 [1, 1, -5] = true := by decide +kernel
theorem subd8_6_116 : subd8_6 [1, 1, -4] = true := by decide +kernel
theorem subd8_6_117 : subd8_6 [1, 1, -3] = true := by decide +kernel
theorem subd8_6_118 : subd8_6 [1, 1, -2] = true := by decide +kernel
theorem subd8_6_119 : subd8_6 [1, 1, -1] = true := by decide +kernel
theorem subd8_6_120 : subd8_6 [1, 1, 0] = true := by decide +kernel
theorem subd8_6_121 : subd8_6 [1, 1, 1] = true := by decide +kernel
theorem subd8_6_122 : subd8_6 [1, 1, 2] = true := by decide +kernel
theorem subd8_6_123 : subd8_6 [1, 1, 3] = true := by decide +kernel
theorem subd8_6_124 : subd8_6 [1, 1, 4] = true := by decide +kernel
theorem subd8_6_125 : subd8_6 [1, 1, 5] = true := by decide +kernel
theorem subd8_6_126 : subd8_6 [1, 1, 6] = true := by decide +kernel
theorem subd8_6_127 : subd8_6 [1, 2] = true := by decide +kernel
theorem sbd8_6_3 : ∀ q ∈ blkd8_6_3, subd8_6 q = true := by
  unfold blkd8_6_3
  exact List.forall_mem_cons.2 ⟨subd8_6_96, List.forall_mem_cons.2 ⟨subd8_6_97, List.forall_mem_cons.2 ⟨subd8_6_98, List.forall_mem_cons.2 ⟨subd8_6_99, List.forall_mem_cons.2 ⟨subd8_6_100, List.forall_mem_cons.2 ⟨subd8_6_101, List.forall_mem_cons.2 ⟨subd8_6_102, List.forall_mem_cons.2 ⟨subd8_6_103, List.forall_mem_cons.2 ⟨subd8_6_104, List.forall_mem_cons.2 ⟨subd8_6_105, List.forall_mem_cons.2 ⟨subd8_6_106, List.forall_mem_cons.2 ⟨subd8_6_107, List.forall_mem_cons.2 ⟨subd8_6_108, List.forall_mem_cons.2 ⟨subd8_6_109, List.forall_mem_cons.2 ⟨subd8_6_110, List.forall_mem_cons.2 ⟨subd8_6_111, List.forall_mem_cons.2 ⟨subd8_6_112, List.forall_mem_cons.2 ⟨subd8_6_113, List.forall_mem_cons.2 ⟨subd8_6_114, List.forall_mem_cons.2 ⟨subd8_6_115, List.forall_mem_cons.2 ⟨subd8_6_116, List.forall_mem_cons.2 ⟨subd8_6_117, List.forall_mem_cons.2 ⟨subd8_6_118, List.forall_mem_cons.2 ⟨subd8_6_119, List.forall_mem_cons.2 ⟨subd8_6_120, List.forall_mem_cons.2 ⟨subd8_6_121, List.forall_mem_cons.2 ⟨subd8_6_122, List.forall_mem_cons.2 ⟨subd8_6_123, List.forall_mem_cons.2 ⟨subd8_6_124, List.forall_mem_cons.2 ⟨subd8_6_125, List.forall_mem_cons.2 ⟨subd8_6_126, List.forall_mem_cons.2 ⟨subd8_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_6_128 : subd8_6 [2, -2] = true := by decide +kernel
theorem subd8_6_129 : subd8_6 [2, -1] = true := by decide +kernel
theorem subd8_6_130 : subd8_6 [2, 0] = true := by decide +kernel
theorem subd8_6_131 : subd8_6 [2, 1] = true := by decide +kernel
theorem subd8_6_132 : subd8_6 [2, 2] = true := by decide +kernel
theorem sbd8_6_4 : ∀ q ∈ blkd8_6_4, subd8_6 q = true := by
  unfold blkd8_6_4
  exact List.forall_mem_cons.2 ⟨subd8_6_128, List.forall_mem_cons.2 ⟨subd8_6_129, List.forall_mem_cons.2 ⟨subd8_6_130, List.forall_mem_cons.2 ⟨subd8_6_131, List.forall_mem_cons.2 ⟨subd8_6_132, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_7 : ldCheck G d8_7.U d8_7.ms ldd8_7 = true := by decide +kernel
theorem pre_okd8_7 : subPre G cell8 d8_7 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C099
