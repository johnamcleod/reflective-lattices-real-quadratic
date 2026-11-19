import ReflectZphi.Data.Cert5.C118.Base

namespace ReflectZphi.Data.Cert5.C118

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_1_0 : subd5_1 [] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_nil _⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [-4] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-3, -2] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [-3, -1] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [-3, 0] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [-3, 1] = true := by decide +kernel
theorem subd5_2_5 : subd5_2 [-3, 2] = true := by decide +kernel
theorem subd5_2_6 : subd5_2 [-3, 3] = true := by decide +kernel
theorem subd5_2_7 : subd5_2 [-2, -3] = true := by decide +kernel
theorem subd5_2_8 : subd5_2 [-2, -2] = true := by decide +kernel
theorem subd5_2_9 : subd5_2 [-2, -1] = true := by decide +kernel
theorem subd5_2_10 : subd5_2 [-2, 0, -7] = true := by decide +kernel
theorem subd5_2_11 : subd5_2 [-2, 0, -6] = true := by decide +kernel
theorem subd5_2_12 : subd5_2 [-2, 0, -5] = true := by decide +kernel
theorem subd5_2_13 : subd5_2 [-2, 0, -4] = true := by decide +kernel
theorem subd5_2_14 : subd5_2 [-2, 0, -3] = true := by decide +kernel
theorem subd5_2_15 : subd5_2 [-2, 0, -2] = true := by decide +kernel
theorem subd5_2_16 : subd5_2 [-2, 0, -1] = true := by decide +kernel
theorem subd5_2_17 : subd5_2 [-2, 0, 0] = true := by decide +kernel
theorem subd5_2_18 : subd5_2 [-2, 0, 1] = true := by decide +kernel
theorem subd5_2_19 : subd5_2 [-2, 0, 2] = true := by decide +kernel
theorem subd5_2_20 : subd5_2 [-2, 0, 3] = true := by decide +kernel
theorem subd5_2_21 : subd5_2 [-2, 0, 4] = true := by decide +kernel
theorem subd5_2_22 : subd5_2 [-2, 0, 5] = true := by decide +kernel
theorem subd5_2_23 : subd5_2 [-2, 0, 6] = true := by decide +kernel
theorem subd5_2_24 : subd5_2 [-2, 0, 7] = true := by decide +kernel
theorem subd5_2_25 : subd5_2 [-2, 1] = true := by decide +kernel
theorem subd5_2_26 : subd5_2 [-2, 2] = true := by decide +kernel
theorem subd5_2_27 : subd5_2 [-2, 3] = true := by decide +kernel
theorem subd5_2_28 : subd5_2 [-1, -4] = true := by decide +kernel
theorem subd5_2_29 : subd5_2 [-1, -3] = true := by decide +kernel
theorem subd5_2_30 : subd5_2 [-1, -2] = true := by decide +kernel
theorem subd5_2_31 : subd5_2 [-1, -1, -8] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_cons.2 ⟨subd5_2_5, List.forall_mem_cons.2 ⟨subd5_2_6, List.forall_mem_cons.2 ⟨subd5_2_7, List.forall_mem_cons.2 ⟨subd5_2_8, List.forall_mem_cons.2 ⟨subd5_2_9, List.forall_mem_cons.2 ⟨subd5_2_10, List.forall_mem_cons.2 ⟨subd5_2_11, List.forall_mem_cons.2 ⟨subd5_2_12, List.forall_mem_cons.2 ⟨subd5_2_13, List.forall_mem_cons.2 ⟨subd5_2_14, List.forall_mem_cons.2 ⟨subd5_2_15, List.forall_mem_cons.2 ⟨subd5_2_16, List.forall_mem_cons.2 ⟨subd5_2_17, List.forall_mem_cons.2 ⟨subd5_2_18, List.forall_mem_cons.2 ⟨subd5_2_19, List.forall_mem_cons.2 ⟨subd5_2_20, List.forall_mem_cons.2 ⟨subd5_2_21, List.forall_mem_cons.2 ⟨subd5_2_22, List.forall_mem_cons.2 ⟨subd5_2_23, List.forall_mem_cons.2 ⟨subd5_2_24, List.forall_mem_cons.2 ⟨subd5_2_25, List.forall_mem_cons.2 ⟨subd5_2_26, List.forall_mem_cons.2 ⟨subd5_2_27, List.forall_mem_cons.2 ⟨subd5_2_28, List.forall_mem_cons.2 ⟨subd5_2_29, List.forall_mem_cons.2 ⟨subd5_2_30, List.forall_mem_cons.2 ⟨subd5_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_32 : subd5_2 [-1, -1, -7] = true := by decide +kernel
theorem subd5_2_33 : subd5_2 [-1, -1, -6] = true := by decide +kernel
theorem subd5_2_34 : subd5_2 [-1, -1, -5] = true := by decide +kernel
theorem subd5_2_35 : subd5_2 [-1, -1, -4] = true := by decide +kernel
theorem subd5_2_36 : subd5_2 [-1, -1, -3] = true := by decide +kernel
theorem subd5_2_37 : subd5_2 [-1, -1, -2] = true := by decide +kernel
theorem subd5_2_38 : subd5_2 [-1, -1, -1] = true := by decide +kernel
theorem subd5_2_39 : subd5_2 [-1, -1, 0] = true := by decide +kernel
theorem subd5_2_40 : subd5_2 [-1, -1, 1] = true := by decide +kernel
theorem subd5_2_41 : subd5_2 [-1, -1, 2] = true := by decide +kernel
theorem subd5_2_42 : subd5_2 [-1, -1, 3] = true := by decide +kernel
theorem subd5_2_43 : subd5_2 [-1, -1, 4] = true := by decide +kernel
theorem subd5_2_44 : subd5_2 [-1, -1, 5] = true := by decide +kernel
theorem subd5_2_45 : subd5_2 [-1, -1, 6] = true := by decide +kernel
theorem subd5_2_46 : subd5_2 [-1, -1, 7] = true := by decide +kernel
theorem subd5_2_47 : subd5_2 [-1, 0, -8] = true := by decide +kernel
theorem subd5_2_48 : subd5_2 [-1, 0, -7] = true := by decide +kernel
theorem subd5_2_49 : subd5_2 [-1, 0, -6] = true := by decide +kernel
theorem subd5_2_50 : subd5_2 [-1, 0, -5] = true := by decide +kernel
theorem subd5_2_51 : subd5_2 [-1, 0, -4] = true := by decide +kernel
theorem subd5_2_52 : subd5_2 [-1, 0, -3] = true := by decide +kernel
theorem subd5_2_53 : subd5_2 [-1, 0, -2] = true := by decide +kernel
theorem subd5_2_54 : subd5_2 [-1, 0, -1] = true := by decide +kernel
theorem subd5_2_55 : subd5_2 [-1, 0, 0] = true := by decide +kernel
theorem subd5_2_56 : subd5_2 [-1, 0, 1] = true := by decide +kernel
theorem subd5_2_57 : subd5_2 [-1, 0, 2] = true := by decide +kernel
theorem subd5_2_58 : subd5_2 [-1, 0, 3] = true := by decide +kernel
theorem subd5_2_59 : subd5_2 [-1, 0, 4] = true := by decide +kernel
theorem subd5_2_60 : subd5_2 [-1, 0, 5] = true := by decide +kernel
theorem subd5_2_61 : subd5_2 [-1, 0, 6] = true := by decide +kernel
theorem subd5_2_62 : subd5_2 [-1, 0, 7] = true := by decide +kernel
theorem subd5_2_63 : subd5_2 [-1, 1, -8] = true := by decide +kernel
theorem sbd5_2_1 : ∀ q ∈ blkd5_2_1, subd5_2 q = true := by
  unfold blkd5_2_1
  exact List.forall_mem_cons.2 ⟨subd5_2_32, List.forall_mem_cons.2 ⟨subd5_2_33, List.forall_mem_cons.2 ⟨subd5_2_34, List.forall_mem_cons.2 ⟨subd5_2_35, List.forall_mem_cons.2 ⟨subd5_2_36, List.forall_mem_cons.2 ⟨subd5_2_37, List.forall_mem_cons.2 ⟨subd5_2_38, List.forall_mem_cons.2 ⟨subd5_2_39, List.forall_mem_cons.2 ⟨subd5_2_40, List.forall_mem_cons.2 ⟨subd5_2_41, List.forall_mem_cons.2 ⟨subd5_2_42, List.forall_mem_cons.2 ⟨subd5_2_43, List.forall_mem_cons.2 ⟨subd5_2_44, List.forall_mem_cons.2 ⟨subd5_2_45, List.forall_mem_cons.2 ⟨subd5_2_46, List.forall_mem_cons.2 ⟨subd5_2_47, List.forall_mem_cons.2 ⟨subd5_2_48, List.forall_mem_cons.2 ⟨subd5_2_49, List.forall_mem_cons.2 ⟨subd5_2_50, List.forall_mem_cons.2 ⟨subd5_2_51, List.forall_mem_cons.2 ⟨subd5_2_52, List.forall_mem_cons.2 ⟨subd5_2_53, List.forall_mem_cons.2 ⟨subd5_2_54, List.forall_mem_cons.2 ⟨subd5_2_55, List.forall_mem_cons.2 ⟨subd5_2_56, List.forall_mem_cons.2 ⟨subd5_2_57, List.forall_mem_cons.2 ⟨subd5_2_58, List.forall_mem_cons.2 ⟨subd5_2_59, List.forall_mem_cons.2 ⟨subd5_2_60, List.forall_mem_cons.2 ⟨subd5_2_61, List.forall_mem_cons.2 ⟨subd5_2_62, List.forall_mem_cons.2 ⟨subd5_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_64 : subd5_2 [-1, 1, -7] = true := by decide +kernel
theorem subd5_2_65 : subd5_2 [-1, 1, -6] = true := by decide +kernel
theorem subd5_2_66 : subd5_2 [-1, 1, -5] = true := by decide +kernel
theorem subd5_2_67 : subd5_2 [-1, 1, -4] = true := by decide +kernel
theorem subd5_2_68 : subd5_2 [-1, 1, -3] = true := by decide +kernel
theorem subd5_2_69 : subd5_2 [-1, 1, -2] = true := by decide +kernel
theorem subd5_2_70 : subd5_2 [-1, 1, -1] = true := by decide +kernel
theorem subd5_2_71 : subd5_2 [-1, 1, 0] = true := by decide +kernel
theorem subd5_2_72 : subd5_2 [-1, 1, 1] = true := by decide +kernel
theorem subd5_2_73 : subd5_2 [-1, 1, 2] = true := by decide +kernel
theorem subd5_2_74 : subd5_2 [-1, 1, 3] = true := by decide +kernel
theorem subd5_2_75 : subd5_2 [-1, 1, 4] = true := by decide +kernel
theorem subd5_2_76 : subd5_2 [-1, 1, 5] = true := by decide +kernel
theorem subd5_2_77 : subd5_2 [-1, 1, 6] = true := by decide +kernel
theorem subd5_2_78 : subd5_2 [-1, 1, 7] = true := by decide +kernel
theorem subd5_2_79 : subd5_2 [-1, 2] = true := by decide +kernel
theorem subd5_2_80 : subd5_2 [-1, 3] = true := by decide +kernel
theorem subd5_2_81 : subd5_2 [0, -4] = true := by decide +kernel
theorem subd5_2_82 : subd5_2 [0, -3] = true := by decide +kernel
theorem subd5_2_83 : subd5_2 [0, -2] = true := by decide +kernel
theorem subd5_2_84 : subd5_2 [0, -1, -8] = true := by decide +kernel
theorem subd5_2_85 : subd5_2 [0, -1, -7] = true := by decide +kernel
theorem subd5_2_86 : subd5_2 [0, -1, -6] = true := by decide +kernel
theorem subd5_2_87 : subd5_2 [0, -1, -5] = true := by decide +kernel
theorem subd5_2_88 : subd5_2 [0, -1, -4] = true := by decide +kernel
theorem subd5_2_89 : subd5_2 [0, -1, -3] = true := by decide +kernel
theorem subd5_2_90 : subd5_2 [0, -1, -2] = true := by decide +kernel
theorem subd5_2_91 : subd5_2 [0, -1, -1] = true := by decide +kernel
theorem subd5_2_92 : subd5_2 [0, -1, 0] = true := by decide +kernel
theorem subd5_2_93 : subd5_2 [0, -1, 1] = true := by decide +kernel
theorem subd5_2_94 : subd5_2 [0, -1, 2] = true := by decide +kernel
theorem subd5_2_95 : subd5_2 [0, -1, 3] = true := by decide +kernel
theorem sbd5_2_2 : ∀ q ∈ blkd5_2_2, subd5_2 q = true := by
  unfold blkd5_2_2
  exact List.forall_mem_cons.2 ⟨subd5_2_64, List.forall_mem_cons.2 ⟨subd5_2_65, List.forall_mem_cons.2 ⟨subd5_2_66, List.forall_mem_cons.2 ⟨subd5_2_67, List.forall_mem_cons.2 ⟨subd5_2_68, List.forall_mem_cons.2 ⟨subd5_2_69, List.forall_mem_cons.2 ⟨subd5_2_70, List.forall_mem_cons.2 ⟨subd5_2_71, List.forall_mem_cons.2 ⟨subd5_2_72, List.forall_mem_cons.2 ⟨subd5_2_73, List.forall_mem_cons.2 ⟨subd5_2_74, List.forall_mem_cons.2 ⟨subd5_2_75, List.forall_mem_cons.2 ⟨subd5_2_76, List.forall_mem_cons.2 ⟨subd5_2_77, List.forall_mem_cons.2 ⟨subd5_2_78, List.forall_mem_cons.2 ⟨subd5_2_79, List.forall_mem_cons.2 ⟨subd5_2_80, List.forall_mem_cons.2 ⟨subd5_2_81, List.forall_mem_cons.2 ⟨subd5_2_82, List.forall_mem_cons.2 ⟨subd5_2_83, List.forall_mem_cons.2 ⟨subd5_2_84, List.forall_mem_cons.2 ⟨subd5_2_85, List.forall_mem_cons.2 ⟨subd5_2_86, List.forall_mem_cons.2 ⟨subd5_2_87, List.forall_mem_cons.2 ⟨subd5_2_88, List.forall_mem_cons.2 ⟨subd5_2_89, List.forall_mem_cons.2 ⟨subd5_2_90, List.forall_mem_cons.2 ⟨subd5_2_91, List.forall_mem_cons.2 ⟨subd5_2_92, List.forall_mem_cons.2 ⟨subd5_2_93, List.forall_mem_cons.2 ⟨subd5_2_94, List.forall_mem_cons.2 ⟨subd5_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_96 : subd5_2 [0, -1, 4] = true := by decide +kernel
theorem subd5_2_97 : subd5_2 [0, -1, 5] = true := by decide +kernel
theorem subd5_2_98 : subd5_2 [0, -1, 6] = true := by decide +kernel
theorem subd5_2_99 : subd5_2 [0, -1, 7] = true := by decide +kernel
theorem subd5_2_100 : subd5_2 [0, 0, -9] = true := by decide +kernel
theorem subd5_2_101 : subd5_2 [0, 0, -8] = true := by decide +kernel
theorem subd5_2_102 : subd5_2 [0, 0, -7] = true := by decide +kernel
theorem subd5_2_103 : subd5_2 [0, 0, -6] = true := by decide +kernel
theorem subd5_2_104 : subd5_2 [0, 0, -5] = true := by decide +kernel
theorem subd5_2_105 : subd5_2 [0, 0, -4] = true := by decide +kernel
theorem subd5_2_106 : subd5_2 [0, 0, -3] = true := by decide +kernel
theorem subd5_2_107 : subd5_2 [0, 0, -2] = true := by decide +kernel
theorem subd5_2_108 : subd5_2 [0, 0, -1] = true := by decide +kernel
theorem subd5_2_109 : subd5_2 [0, 0, 0] = true := by decide +kernel
theorem subd5_2_110 : subd5_2 [0, 0, 1] = true := by decide +kernel
theorem subd5_2_111 : subd5_2 [0, 0, 2] = true := by decide +kernel
theorem subd5_2_112 : subd5_2 [0, 0, 3] = true := by decide +kernel
theorem subd5_2_113 : subd5_2 [0, 0, 4] = true := by decide +kernel
theorem subd5_2_114 : subd5_2 [0, 0, 5] = true := by decide +kernel
theorem subd5_2_115 : subd5_2 [0, 0, 6] = true := by decide +kernel
theorem subd5_2_116 : subd5_2 [0, 0, 7] = true := by decide +kernel
theorem subd5_2_117 : subd5_2 [0, 0, 8] = true := by decide +kernel
theorem subd5_2_118 : subd5_2 [0, 1, -8] = true := by decide +kernel
theorem subd5_2_119 : subd5_2 [0, 1, -7] = true := by decide +kernel
theorem subd5_2_120 : subd5_2 [0, 1, -6] = true := by decide +kernel
theorem subd5_2_121 : subd5_2 [0, 1, -5] = true := by decide +kernel
theorem subd5_2_122 : subd5_2 [0, 1, -4] = true := by decide +kernel
theorem subd5_2_123 : subd5_2 [0, 1, -3] = true := by decide +kernel
theorem subd5_2_124 : subd5_2 [0, 1, -2] = true := by decide +kernel
theorem subd5_2_125 : subd5_2 [0, 1, -1] = true := by decide +kernel
theorem subd5_2_126 : subd5_2 [0, 1, 0] = true := by decide +kernel
theorem subd5_2_127 : subd5_2 [0, 1, 1] = true := by decide +kernel
theorem sbd5_2_3 : ∀ q ∈ blkd5_2_3, subd5_2 q = true := by
  unfold blkd5_2_3
  exact List.forall_mem_cons.2 ⟨subd5_2_96, List.forall_mem_cons.2 ⟨subd5_2_97, List.forall_mem_cons.2 ⟨subd5_2_98, List.forall_mem_cons.2 ⟨subd5_2_99, List.forall_mem_cons.2 ⟨subd5_2_100, List.forall_mem_cons.2 ⟨subd5_2_101, List.forall_mem_cons.2 ⟨subd5_2_102, List.forall_mem_cons.2 ⟨subd5_2_103, List.forall_mem_cons.2 ⟨subd5_2_104, List.forall_mem_cons.2 ⟨subd5_2_105, List.forall_mem_cons.2 ⟨subd5_2_106, List.forall_mem_cons.2 ⟨subd5_2_107, List.forall_mem_cons.2 ⟨subd5_2_108, List.forall_mem_cons.2 ⟨subd5_2_109, List.forall_mem_cons.2 ⟨subd5_2_110, List.forall_mem_cons.2 ⟨subd5_2_111, List.forall_mem_cons.2 ⟨subd5_2_112, List.forall_mem_cons.2 ⟨subd5_2_113, List.forall_mem_cons.2 ⟨subd5_2_114, List.forall_mem_cons.2 ⟨subd5_2_115, List.forall_mem_cons.2 ⟨subd5_2_116, List.forall_mem_cons.2 ⟨subd5_2_117, List.forall_mem_cons.2 ⟨subd5_2_118, List.forall_mem_cons.2 ⟨subd5_2_119, List.forall_mem_cons.2 ⟨subd5_2_120, List.forall_mem_cons.2 ⟨subd5_2_121, List.forall_mem_cons.2 ⟨subd5_2_122, List.forall_mem_cons.2 ⟨subd5_2_123, List.forall_mem_cons.2 ⟨subd5_2_124, List.forall_mem_cons.2 ⟨subd5_2_125, List.forall_mem_cons.2 ⟨subd5_2_126, List.forall_mem_cons.2 ⟨subd5_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_128 : subd5_2 [0, 1, 2] = true := by decide +kernel
theorem subd5_2_129 : subd5_2 [0, 1, 3] = true := by decide +kernel
theorem subd5_2_130 : subd5_2 [0, 1, 4] = true := by decide +kernel
theorem subd5_2_131 : subd5_2 [0, 1, 5] = true := by decide +kernel
theorem subd5_2_132 : subd5_2 [0, 1, 6] = true := by decide +kernel
theorem subd5_2_133 : subd5_2 [0, 1, 7] = true := by decide +kernel
theorem subd5_2_134 : subd5_2 [0, 2] = true := by decide +kernel
theorem subd5_2_135 : subd5_2 [0, 3] = true := by decide +kernel
theorem subd5_2_136 : subd5_2 [1, -4] = true := by decide +kernel
theorem subd5_2_137 : subd5_2 [1, -3] = true := by decide +kernel
theorem subd5_2_138 : subd5_2 [1, -2] = true := by decide +kernel
theorem subd5_2_139 : subd5_2 [1, -1, -8] = true := by decide +kernel
theorem subd5_2_140 : subd5_2 [1, -1, -7] = true := by decide +kernel
theorem subd5_2_141 : subd5_2 [1, -1, -6] = true := by decide +kernel
theorem subd5_2_142 : subd5_2 [1, -1, -5] = true := by decide +kernel
theorem subd5_2_143 : subd5_2 [1, -1, -4] = true := by decide +kernel
theorem subd5_2_144 : subd5_2 [1, -1, -3] = true := by decide +kernel
theorem subd5_2_145 : subd5_2 [1, -1, -2] = true := by decide +kernel
theorem subd5_2_146 : subd5_2 [1, -1, -1] = true := by decide +kernel
theorem subd5_2_147 : subd5_2 [1, -1, 0] = true := by decide +kernel
theorem subd5_2_148 : subd5_2 [1, -1, 1] = true := by decide +kernel
theorem subd5_2_149 : subd5_2 [1, -1, 2] = true := by decide +kernel
theorem subd5_2_150 : subd5_2 [1, -1, 3] = true := by decide +kernel
theorem subd5_2_151 : subd5_2 [1, -1, 4] = true := by decide +kernel
theorem subd5_2_152 : subd5_2 [1, -1, 5] = true := by decide +kernel
theorem subd5_2_153 : subd5_2 [1, -1, 6] = true := by decide +kernel
theorem subd5_2_154 : subd5_2 [1, -1, 7] = true := by decide +kernel
theorem subd5_2_155 : subd5_2 [1, 0, -8] = true := by decide +kernel
theorem subd5_2_156 : subd5_2 [1, 0, -7] = true := by decide +kernel
theorem subd5_2_157 : subd5_2 [1, 0, -6] = true := by decide +kernel
theorem subd5_2_158 : subd5_2 [1, 0, -5] = true := by decide +kernel
theorem subd5_2_159 : subd5_2 [1, 0, -4] = true := by decide +kernel
theorem sbd5_2_4 : ∀ q ∈ blkd5_2_4, subd5_2 q = true := by
  unfold blkd5_2_4
  exact List.forall_mem_cons.2 ⟨subd5_2_128, List.forall_mem_cons.2 ⟨subd5_2_129, List.forall_mem_cons.2 ⟨subd5_2_130, List.forall_mem_cons.2 ⟨subd5_2_131, List.forall_mem_cons.2 ⟨subd5_2_132, List.forall_mem_cons.2 ⟨subd5_2_133, List.forall_mem_cons.2 ⟨subd5_2_134, List.forall_mem_cons.2 ⟨subd5_2_135, List.forall_mem_cons.2 ⟨subd5_2_136, List.forall_mem_cons.2 ⟨subd5_2_137, List.forall_mem_cons.2 ⟨subd5_2_138, List.forall_mem_cons.2 ⟨subd5_2_139, List.forall_mem_cons.2 ⟨subd5_2_140, List.forall_mem_cons.2 ⟨subd5_2_141, List.forall_mem_cons.2 ⟨subd5_2_142, List.forall_mem_cons.2 ⟨subd5_2_143, List.forall_mem_cons.2 ⟨subd5_2_144, List.forall_mem_cons.2 ⟨subd5_2_145, List.forall_mem_cons.2 ⟨subd5_2_146, List.forall_mem_cons.2 ⟨subd5_2_147, List.forall_mem_cons.2 ⟨subd5_2_148, List.forall_mem_cons.2 ⟨subd5_2_149, List.forall_mem_cons.2 ⟨subd5_2_150, List.forall_mem_cons.2 ⟨subd5_2_151, List.forall_mem_cons.2 ⟨subd5_2_152, List.forall_mem_cons.2 ⟨subd5_2_153, List.forall_mem_cons.2 ⟨subd5_2_154, List.forall_mem_cons.2 ⟨subd5_2_155, List.forall_mem_cons.2 ⟨subd5_2_156, List.forall_mem_cons.2 ⟨subd5_2_157, List.forall_mem_cons.2 ⟨subd5_2_158, List.forall_mem_cons.2 ⟨subd5_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_160 : subd5_2 [1, 0, -3] = true := by decide +kernel
theorem subd5_2_161 : subd5_2 [1, 0, -2] = true := by decide +kernel
theorem subd5_2_162 : subd5_2 [1, 0, -1] = true := by decide +kernel
theorem subd5_2_163 : subd5_2 [1, 0, 0] = true := by decide +kernel
theorem subd5_2_164 : subd5_2 [1, 0, 1] = true := by decide +kernel
theorem subd5_2_165 : subd5_2 [1, 0, 2] = true := by decide +kernel
theorem subd5_2_166 : subd5_2 [1, 0, 3] = true := by decide +kernel
theorem subd5_2_167 : subd5_2 [1, 0, 4] = true := by decide +kernel
theorem subd5_2_168 : subd5_2 [1, 0, 5] = true := by decide +kernel
theorem subd5_2_169 : subd5_2 [1, 0, 6] = true := by decide +kernel
theorem subd5_2_170 : subd5_2 [1, 0, 7] = true := by decide +kernel
theorem subd5_2_171 : subd5_2 [1, 1, -8] = true := by decide +kernel
theorem subd5_2_172 : subd5_2 [1, 1, -7] = true := by decide +kernel
theorem subd5_2_173 : subd5_2 [1, 1, -6] = true := by decide +kernel
theorem subd5_2_174 : subd5_2 [1, 1, -5] = true := by decide +kernel
theorem subd5_2_175 : subd5_2 [1, 1, -4] = true := by decide +kernel
theorem subd5_2_176 : subd5_2 [1, 1, -3] = true := by decide +kernel
theorem subd5_2_177 : subd5_2 [1, 1, -2] = true := by decide +kernel
theorem subd5_2_178 : subd5_2 [1, 1, -1] = true := by decide +kernel
theorem subd5_2_179 : subd5_2 [1, 1, 0] = true := by decide +kernel
theorem subd5_2_180 : subd5_2 [1, 1, 1] = true := by decide +kernel
theorem subd5_2_181 : subd5_2 [1, 1, 2] = true := by decide +kernel
theorem subd5_2_182 : subd5_2 [1, 1, 3] = true := by decide +kernel
theorem subd5_2_183 : subd5_2 [1, 1, 4] = true := by decide +kernel
theorem subd5_2_184 : subd5_2 [1, 1, 5] = true := by decide +kernel
theorem subd5_2_185 : subd5_2 [1, 1, 6] = true := by decide +kernel
theorem subd5_2_186 : subd5_2 [1, 1, 7] = true := by decide +kernel
theorem subd5_2_187 : subd5_2 [1, 2] = true := by decide +kernel
theorem subd5_2_188 : subd5_2 [1, 3] = true := by decide +kernel
theorem subd5_2_189 : subd5_2 [2, -4] = true := by decide +kernel
theorem subd5_2_190 : subd5_2 [2, -3] = true := by decide +kernel
theorem subd5_2_191 : subd5_2 [2, -2] = true := by decide +kernel
theorem sbd5_2_5 : ∀ q ∈ blkd5_2_5, subd5_2 q = true := by
  unfold blkd5_2_5
  exact List.forall_mem_cons.2 ⟨subd5_2_160, List.forall_mem_cons.2 ⟨subd5_2_161, List.forall_mem_cons.2 ⟨subd5_2_162, List.forall_mem_cons.2 ⟨subd5_2_163, List.forall_mem_cons.2 ⟨subd5_2_164, List.forall_mem_cons.2 ⟨subd5_2_165, List.forall_mem_cons.2 ⟨subd5_2_166, List.forall_mem_cons.2 ⟨subd5_2_167, List.forall_mem_cons.2 ⟨subd5_2_168, List.forall_mem_cons.2 ⟨subd5_2_169, List.forall_mem_cons.2 ⟨subd5_2_170, List.forall_mem_cons.2 ⟨subd5_2_171, List.forall_mem_cons.2 ⟨subd5_2_172, List.forall_mem_cons.2 ⟨subd5_2_173, List.forall_mem_cons.2 ⟨subd5_2_174, List.forall_mem_cons.2 ⟨subd5_2_175, List.forall_mem_cons.2 ⟨subd5_2_176, List.forall_mem_cons.2 ⟨subd5_2_177, List.forall_mem_cons.2 ⟨subd5_2_178, List.forall_mem_cons.2 ⟨subd5_2_179, List.forall_mem_cons.2 ⟨subd5_2_180, List.forall_mem_cons.2 ⟨subd5_2_181, List.forall_mem_cons.2 ⟨subd5_2_182, List.forall_mem_cons.2 ⟨subd5_2_183, List.forall_mem_cons.2 ⟨subd5_2_184, List.forall_mem_cons.2 ⟨subd5_2_185, List.forall_mem_cons.2 ⟨subd5_2_186, List.forall_mem_cons.2 ⟨subd5_2_187, List.forall_mem_cons.2 ⟨subd5_2_188, List.forall_mem_cons.2 ⟨subd5_2_189, List.forall_mem_cons.2 ⟨subd5_2_190, List.forall_mem_cons.2 ⟨subd5_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_192 : subd5_2 [2, -1] = true := by decide +kernel
theorem subd5_2_193 : subd5_2 [2, 0, -8] = true := by decide +kernel
theorem subd5_2_194 : subd5_2 [2, 0, -7] = true := by decide +kernel
theorem subd5_2_195 : subd5_2 [2, 0, -6] = true := by decide +kernel
theorem subd5_2_196 : subd5_2 [2, 0, -5] = true := by decide +kernel
theorem subd5_2_197 : subd5_2 [2, 0, -4] = true := by decide +kernel
theorem subd5_2_198 : subd5_2 [2, 0, -3] = true := by decide +kernel
theorem subd5_2_199 : subd5_2 [2, 0, -2] = true := by decide +kernel
theorem subd5_2_200 : subd5_2 [2, 0, -1] = true := by decide +kernel
theorem subd5_2_201 : subd5_2 [2, 0, 0] = true := by decide +kernel
theorem subd5_2_202 : subd5_2 [2, 0, 1] = true := by decide +kernel
theorem subd5_2_203 : subd5_2 [2, 0, 2] = true := by decide +kernel
theorem subd5_2_204 : subd5_2 [2, 0, 3] = true := by decide +kernel
theorem subd5_2_205 : subd5_2 [2, 0, 4] = true := by decide +kernel
theorem subd5_2_206 : subd5_2 [2, 0, 5] = true := by decide +kernel
theorem subd5_2_207 : subd5_2 [2, 0, 6] = true := by decide +kernel
theorem subd5_2_208 : subd5_2 [2, 1] = true := by decide +kernel
theorem subd5_2_209 : subd5_2 [2, 2] = true := by decide +kernel
theorem subd5_2_210 : subd5_2 [3, -4] = true := by decide +kernel
theorem subd5_2_211 : subd5_2 [3, -3] = true := by decide +kernel
theorem subd5_2_212 : subd5_2 [3, -2] = true := by decide +kernel
theorem subd5_2_213 : subd5_2 [3, -1] = true := by decide +kernel
theorem subd5_2_214 : subd5_2 [3, 0] = true := by decide +kernel
theorem subd5_2_215 : subd5_2 [3, 1] = true := by decide +kernel
theorem subd5_2_216 : subd5_2 [4] = true := by decide +kernel
theorem sbd5_2_6 : ∀ q ∈ blkd5_2_6, subd5_2 q = true := by
  unfold blkd5_2_6
  exact List.forall_mem_cons.2 ⟨subd5_2_192, List.forall_mem_cons.2 ⟨subd5_2_193, List.forall_mem_cons.2 ⟨subd5_2_194, List.forall_mem_cons.2 ⟨subd5_2_195, List.forall_mem_cons.2 ⟨subd5_2_196, List.forall_mem_cons.2 ⟨subd5_2_197, List.forall_mem_cons.2 ⟨subd5_2_198, List.forall_mem_cons.2 ⟨subd5_2_199, List.forall_mem_cons.2 ⟨subd5_2_200, List.forall_mem_cons.2 ⟨subd5_2_201, List.forall_mem_cons.2 ⟨subd5_2_202, List.forall_mem_cons.2 ⟨subd5_2_203, List.forall_mem_cons.2 ⟨subd5_2_204, List.forall_mem_cons.2 ⟨subd5_2_205, List.forall_mem_cons.2 ⟨subd5_2_206, List.forall_mem_cons.2 ⟨subd5_2_207, List.forall_mem_cons.2 ⟨subd5_2_208, List.forall_mem_cons.2 ⟨subd5_2_209, List.forall_mem_cons.2 ⟨subd5_2_210, List.forall_mem_cons.2 ⟨subd5_2_211, List.forall_mem_cons.2 ⟨subd5_2_212, List.forall_mem_cons.2 ⟨subd5_2_213, List.forall_mem_cons.2 ⟨subd5_2_214, List.forall_mem_cons.2 ⟨subd5_2_215, List.forall_mem_cons.2 ⟨subd5_2_216, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C118
