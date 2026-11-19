import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel
theorem subd5_4_0 : subd5_4 [-4, -3] = true := by decide +kernel
theorem subd5_4_1 : subd5_4 [-4, -2] = true := by decide +kernel
theorem subd5_4_2 : subd5_4 [-4, -1] = true := by decide +kernel
theorem subd5_4_3 : subd5_4 [-4, 0] = true := by decide +kernel
theorem subd5_4_4 : subd5_4 [-4, 1] = true := by decide +kernel
theorem subd5_4_5 : subd5_4 [-3, -4] = true := by decide +kernel
theorem subd5_4_6 : subd5_4 [-3, -3] = true := by decide +kernel
theorem subd5_4_7 : subd5_4 [-3, -2] = true := by decide +kernel
theorem subd5_4_8 : subd5_4 [-3, -1] = true := by decide +kernel
theorem subd5_4_9 : subd5_4 [-3, 0] = true := by decide +kernel
theorem subd5_4_10 : subd5_4 [-3, 1] = true := by decide +kernel
theorem subd5_4_11 : subd5_4 [-3, 2] = true := by decide +kernel
theorem subd5_4_12 : subd5_4 [-2, -5] = true := by decide +kernel
theorem subd5_4_13 : subd5_4 [-2, -4] = true := by decide +kernel
theorem subd5_4_14 : subd5_4 [-2, -3] = true := by decide +kernel
theorem subd5_4_15 : subd5_4 [-2, -2] = true := by decide +kernel
theorem subd5_4_16 : subd5_4 [-2, -1] = true := by decide +kernel
theorem subd5_4_17 : subd5_4 [-2, 0] = true := by decide +kernel
theorem subd5_4_18 : subd5_4 [-2, 1] = true := by decide +kernel
theorem subd5_4_19 : subd5_4 [-2, 2] = true := by decide +kernel
theorem subd5_4_20 : subd5_4 [-2, 3] = true := by decide +kernel
theorem subd5_4_21 : subd5_4 [-1, -5] = true := by decide +kernel
theorem subd5_4_22 : subd5_4 [-1, -4] = true := by decide +kernel
theorem subd5_4_23 : subd5_4 [-1, -3] = true := by decide +kernel
theorem subd5_4_24 : subd5_4 [-1, -2] = true := by decide +kernel
theorem subd5_4_25 : subd5_4 [-1, -1, -7] = true := by decide +kernel
theorem subd5_4_26 : subd5_4 [-1, -1, -6] = true := by decide +kernel
theorem subd5_4_27 : subd5_4 [-1, -1, -5] = true := by decide +kernel
theorem subd5_4_28 : subd5_4 [-1, -1, -4] = true := by decide +kernel
theorem subd5_4_29 : subd5_4 [-1, -1, -3] = true := by decide +kernel
theorem subd5_4_30 : subd5_4 [-1, -1, -2] = true := by decide +kernel
theorem subd5_4_31 : subd5_4 [-1, -1, -1] = true := by decide +kernel
theorem sbd5_4_0 : ∀ q ∈ blkd5_4_0, subd5_4 q = true := by
  unfold blkd5_4_0
  exact List.forall_mem_cons.2 ⟨subd5_4_0, List.forall_mem_cons.2 ⟨subd5_4_1, List.forall_mem_cons.2 ⟨subd5_4_2, List.forall_mem_cons.2 ⟨subd5_4_3, List.forall_mem_cons.2 ⟨subd5_4_4, List.forall_mem_cons.2 ⟨subd5_4_5, List.forall_mem_cons.2 ⟨subd5_4_6, List.forall_mem_cons.2 ⟨subd5_4_7, List.forall_mem_cons.2 ⟨subd5_4_8, List.forall_mem_cons.2 ⟨subd5_4_9, List.forall_mem_cons.2 ⟨subd5_4_10, List.forall_mem_cons.2 ⟨subd5_4_11, List.forall_mem_cons.2 ⟨subd5_4_12, List.forall_mem_cons.2 ⟨subd5_4_13, List.forall_mem_cons.2 ⟨subd5_4_14, List.forall_mem_cons.2 ⟨subd5_4_15, List.forall_mem_cons.2 ⟨subd5_4_16, List.forall_mem_cons.2 ⟨subd5_4_17, List.forall_mem_cons.2 ⟨subd5_4_18, List.forall_mem_cons.2 ⟨subd5_4_19, List.forall_mem_cons.2 ⟨subd5_4_20, List.forall_mem_cons.2 ⟨subd5_4_21, List.forall_mem_cons.2 ⟨subd5_4_22, List.forall_mem_cons.2 ⟨subd5_4_23, List.forall_mem_cons.2 ⟨subd5_4_24, List.forall_mem_cons.2 ⟨subd5_4_25, List.forall_mem_cons.2 ⟨subd5_4_26, List.forall_mem_cons.2 ⟨subd5_4_27, List.forall_mem_cons.2 ⟨subd5_4_28, List.forall_mem_cons.2 ⟨subd5_4_29, List.forall_mem_cons.2 ⟨subd5_4_30, List.forall_mem_cons.2 ⟨subd5_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_4_32 : subd5_4 [-1, -1, 0] = true := by decide +kernel
theorem subd5_4_33 : subd5_4 [-1, -1, 1] = true := by decide +kernel
theorem subd5_4_34 : subd5_4 [-1, -1, 2] = true := by decide +kernel
theorem subd5_4_35 : subd5_4 [-1, -1, 3] = true := by decide +kernel
theorem subd5_4_36 : subd5_4 [-1, -1, 4] = true := by decide +kernel
theorem subd5_4_37 : subd5_4 [-1, -1, 5] = true := by decide +kernel
theorem subd5_4_38 : subd5_4 [-1, -1, 6] = true := by decide +kernel
theorem subd5_4_39 : subd5_4 [-1, 0, -7] = true := by decide +kernel
theorem subd5_4_40 : subd5_4 [-1, 0, -6] = true := by decide +kernel
theorem subd5_4_41 : subd5_4 [-1, 0, -5] = true := by decide +kernel
theorem subd5_4_42 : subd5_4 [-1, 0, -4] = true := by decide +kernel
theorem subd5_4_43 : subd5_4 [-1, 0, -3] = true := by decide +kernel
theorem subd5_4_44 : subd5_4 [-1, 0, -2] = true := by decide +kernel
theorem subd5_4_45 : subd5_4 [-1, 0, -1] = true := by decide +kernel
theorem subd5_4_46 : subd5_4 [-1, 0, 0] = true := by decide +kernel
theorem subd5_4_47 : subd5_4 [-1, 0, 1] = true := by decide +kernel
theorem subd5_4_48 : subd5_4 [-1, 0, 2] = true := by decide +kernel
theorem subd5_4_49 : subd5_4 [-1, 0, 3] = true := by decide +kernel
theorem subd5_4_50 : subd5_4 [-1, 0, 4] = true := by decide +kernel
theorem subd5_4_51 : subd5_4 [-1, 0, 5] = true := by decide +kernel
theorem subd5_4_52 : subd5_4 [-1, 0, 6] = true := by decide +kernel
theorem subd5_4_53 : subd5_4 [-1, 1] = true := by decide +kernel
theorem subd5_4_54 : subd5_4 [-1, 2] = true := by decide +kernel
theorem subd5_4_55 : subd5_4 [-1, 3] = true := by decide +kernel
theorem subd5_4_56 : subd5_4 [0, -5] = true := by decide +kernel
theorem subd5_4_57 : subd5_4 [0, -4] = true := by decide +kernel
theorem subd5_4_58 : subd5_4 [0, -3] = true := by decide +kernel
theorem subd5_4_59 : subd5_4 [0, -2] = true := by decide +kernel
theorem subd5_4_60 : subd5_4 [0, -1, -7] = true := by decide +kernel
theorem subd5_4_61 : subd5_4 [0, -1, -6] = true := by decide +kernel
theorem subd5_4_62 : subd5_4 [0, -1, -5] = true := by decide +kernel
theorem subd5_4_63 : subd5_4 [0, -1, -4] = true := by decide +kernel
theorem sbd5_4_1 : ∀ q ∈ blkd5_4_1, subd5_4 q = true := by
  unfold blkd5_4_1
  exact List.forall_mem_cons.2 ⟨subd5_4_32, List.forall_mem_cons.2 ⟨subd5_4_33, List.forall_mem_cons.2 ⟨subd5_4_34, List.forall_mem_cons.2 ⟨subd5_4_35, List.forall_mem_cons.2 ⟨subd5_4_36, List.forall_mem_cons.2 ⟨subd5_4_37, List.forall_mem_cons.2 ⟨subd5_4_38, List.forall_mem_cons.2 ⟨subd5_4_39, List.forall_mem_cons.2 ⟨subd5_4_40, List.forall_mem_cons.2 ⟨subd5_4_41, List.forall_mem_cons.2 ⟨subd5_4_42, List.forall_mem_cons.2 ⟨subd5_4_43, List.forall_mem_cons.2 ⟨subd5_4_44, List.forall_mem_cons.2 ⟨subd5_4_45, List.forall_mem_cons.2 ⟨subd5_4_46, List.forall_mem_cons.2 ⟨subd5_4_47, List.forall_mem_cons.2 ⟨subd5_4_48, List.forall_mem_cons.2 ⟨subd5_4_49, List.forall_mem_cons.2 ⟨subd5_4_50, List.forall_mem_cons.2 ⟨subd5_4_51, List.forall_mem_cons.2 ⟨subd5_4_52, List.forall_mem_cons.2 ⟨subd5_4_53, List.forall_mem_cons.2 ⟨subd5_4_54, List.forall_mem_cons.2 ⟨subd5_4_55, List.forall_mem_cons.2 ⟨subd5_4_56, List.forall_mem_cons.2 ⟨subd5_4_57, List.forall_mem_cons.2 ⟨subd5_4_58, List.forall_mem_cons.2 ⟨subd5_4_59, List.forall_mem_cons.2 ⟨subd5_4_60, List.forall_mem_cons.2 ⟨subd5_4_61, List.forall_mem_cons.2 ⟨subd5_4_62, List.forall_mem_cons.2 ⟨subd5_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_4_64 : subd5_4 [0, -1, -3] = true := by decide +kernel
theorem subd5_4_65 : subd5_4 [0, -1, -2] = true := by decide +kernel
theorem subd5_4_66 : subd5_4 [0, -1, -1] = true := by decide +kernel
theorem subd5_4_67 : subd5_4 [0, -1, 0] = true := by decide +kernel
theorem subd5_4_68 : subd5_4 [0, -1, 1] = true := by decide +kernel
theorem subd5_4_69 : subd5_4 [0, -1, 2] = true := by decide +kernel
theorem subd5_4_70 : subd5_4 [0, -1, 3] = true := by decide +kernel
theorem subd5_4_71 : subd5_4 [0, -1, 4] = true := by decide +kernel
theorem subd5_4_72 : subd5_4 [0, -1, 5] = true := by decide +kernel
theorem subd5_4_73 : subd5_4 [0, -1, 6] = true := by decide +kernel
theorem subd5_4_74 : subd5_4 [0, 0, -7] = true := by decide +kernel
theorem subd5_4_75 : subd5_4 [0, 0, -6] = true := by decide +kernel
theorem subd5_4_76 : subd5_4 [0, 0, -5] = true := by decide +kernel
theorem subd5_4_77 : subd5_4 [0, 0, -4] = true := by decide +kernel
theorem subd5_4_78 : subd5_4 [0, 0, -3] = true := by decide +kernel
theorem subd5_4_79 : subd5_4 [0, 0, -2] = true := by decide +kernel
theorem subd5_4_80 : subd5_4 [0, 0, -1] = true := by decide +kernel
theorem subd5_4_81 : subd5_4 [0, 0, 0] = true := by decide +kernel
theorem subd5_4_82 : subd5_4 [0, 0, 1] = true := by decide +kernel
theorem subd5_4_83 : subd5_4 [0, 0, 2] = true := by decide +kernel
theorem subd5_4_84 : subd5_4 [0, 0, 3] = true := by decide +kernel
theorem subd5_4_85 : subd5_4 [0, 0, 4] = true := by decide +kernel
theorem subd5_4_86 : subd5_4 [0, 0, 5] = true := by decide +kernel
theorem subd5_4_87 : subd5_4 [0, 0, 6] = true := by decide +kernel
theorem subd5_4_88 : subd5_4 [0, 1, -7] = true := by decide +kernel
theorem subd5_4_89 : subd5_4 [0, 1, -6] = true := by decide +kernel
theorem subd5_4_90 : subd5_4 [0, 1, -5] = true := by decide +kernel
theorem subd5_4_91 : subd5_4 [0, 1, -4] = true := by decide +kernel
theorem subd5_4_92 : subd5_4 [0, 1, -3] = true := by decide +kernel
theorem subd5_4_93 : subd5_4 [0, 1, -2] = true := by decide +kernel
theorem subd5_4_94 : subd5_4 [0, 1, -1] = true := by decide +kernel
theorem subd5_4_95 : subd5_4 [0, 1, 0] = true := by decide +kernel
theorem sbd5_4_2 : ∀ q ∈ blkd5_4_2, subd5_4 q = true := by
  unfold blkd5_4_2
  exact List.forall_mem_cons.2 ⟨subd5_4_64, List.forall_mem_cons.2 ⟨subd5_4_65, List.forall_mem_cons.2 ⟨subd5_4_66, List.forall_mem_cons.2 ⟨subd5_4_67, List.forall_mem_cons.2 ⟨subd5_4_68, List.forall_mem_cons.2 ⟨subd5_4_69, List.forall_mem_cons.2 ⟨subd5_4_70, List.forall_mem_cons.2 ⟨subd5_4_71, List.forall_mem_cons.2 ⟨subd5_4_72, List.forall_mem_cons.2 ⟨subd5_4_73, List.forall_mem_cons.2 ⟨subd5_4_74, List.forall_mem_cons.2 ⟨subd5_4_75, List.forall_mem_cons.2 ⟨subd5_4_76, List.forall_mem_cons.2 ⟨subd5_4_77, List.forall_mem_cons.2 ⟨subd5_4_78, List.forall_mem_cons.2 ⟨subd5_4_79, List.forall_mem_cons.2 ⟨subd5_4_80, List.forall_mem_cons.2 ⟨subd5_4_81, List.forall_mem_cons.2 ⟨subd5_4_82, List.forall_mem_cons.2 ⟨subd5_4_83, List.forall_mem_cons.2 ⟨subd5_4_84, List.forall_mem_cons.2 ⟨subd5_4_85, List.forall_mem_cons.2 ⟨subd5_4_86, List.forall_mem_cons.2 ⟨subd5_4_87, List.forall_mem_cons.2 ⟨subd5_4_88, List.forall_mem_cons.2 ⟨subd5_4_89, List.forall_mem_cons.2 ⟨subd5_4_90, List.forall_mem_cons.2 ⟨subd5_4_91, List.forall_mem_cons.2 ⟨subd5_4_92, List.forall_mem_cons.2 ⟨subd5_4_93, List.forall_mem_cons.2 ⟨subd5_4_94, List.forall_mem_cons.2 ⟨subd5_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_4_96 : subd5_4 [0, 1, 1] = true := by decide +kernel
theorem subd5_4_97 : subd5_4 [0, 1, 2] = true := by decide +kernel
theorem subd5_4_98 : subd5_4 [0, 1, 3] = true := by decide +kernel
theorem subd5_4_99 : subd5_4 [0, 1, 4] = true := by decide +kernel
theorem subd5_4_100 : subd5_4 [0, 1, 5] = true := by decide +kernel
theorem subd5_4_101 : subd5_4 [0, 1, 6] = true := by decide +kernel
theorem subd5_4_102 : subd5_4 [0, 2] = true := by decide +kernel
theorem subd5_4_103 : subd5_4 [0, 3] = true := by decide +kernel
theorem subd5_4_104 : subd5_4 [0, 4] = true := by decide +kernel
theorem subd5_4_105 : subd5_4 [1, -4] = true := by decide +kernel
theorem subd5_4_106 : subd5_4 [1, -3] = true := by decide +kernel
theorem subd5_4_107 : subd5_4 [1, -2] = true := by decide +kernel
theorem subd5_4_108 : subd5_4 [1, -1] = true := by decide +kernel
theorem subd5_4_109 : subd5_4 [1, 0, -7] = true := by decide +kernel
theorem subd5_4_110 : subd5_4 [1, 0, -6] = true := by decide +kernel
theorem subd5_4_111 : subd5_4 [1, 0, -5] = true := by decide +kernel
theorem subd5_4_112 : subd5_4 [1, 0, -4] = true := by decide +kernel
theorem subd5_4_113 : subd5_4 [1, 0, -3] = true := by decide +kernel
theorem subd5_4_114 : subd5_4 [1, 0, -2] = true := by decide +kernel
theorem subd5_4_115 : subd5_4 [1, 0, -1] = true := by decide +kernel
theorem subd5_4_116 : subd5_4 [1, 0, 0] = true := by decide +kernel
theorem subd5_4_117 : subd5_4 [1, 0, 1] = true := by decide +kernel
theorem subd5_4_118 : subd5_4 [1, 0, 2] = true := by decide +kernel
theorem subd5_4_119 : subd5_4 [1, 0, 3] = true := by decide +kernel
theorem subd5_4_120 : subd5_4 [1, 0, 4] = true := by decide +kernel
theorem subd5_4_121 : subd5_4 [1, 0, 5] = true := by decide +kernel
theorem subd5_4_122 : subd5_4 [1, 0, 6] = true := by decide +kernel
theorem subd5_4_123 : subd5_4 [1, 1, -7] = true := by decide +kernel
theorem subd5_4_124 : subd5_4 [1, 1, -6] = true := by decide +kernel
theorem subd5_4_125 : subd5_4 [1, 1, -5] = true := by decide +kernel
theorem subd5_4_126 : subd5_4 [1, 1, -4] = true := by decide +kernel
theorem subd5_4_127 : subd5_4 [1, 1, -3] = true := by decide +kernel
theorem sbd5_4_3 : ∀ q ∈ blkd5_4_3, subd5_4 q = true := by
  unfold blkd5_4_3
  exact List.forall_mem_cons.2 ⟨subd5_4_96, List.forall_mem_cons.2 ⟨subd5_4_97, List.forall_mem_cons.2 ⟨subd5_4_98, List.forall_mem_cons.2 ⟨subd5_4_99, List.forall_mem_cons.2 ⟨subd5_4_100, List.forall_mem_cons.2 ⟨subd5_4_101, List.forall_mem_cons.2 ⟨subd5_4_102, List.forall_mem_cons.2 ⟨subd5_4_103, List.forall_mem_cons.2 ⟨subd5_4_104, List.forall_mem_cons.2 ⟨subd5_4_105, List.forall_mem_cons.2 ⟨subd5_4_106, List.forall_mem_cons.2 ⟨subd5_4_107, List.forall_mem_cons.2 ⟨subd5_4_108, List.forall_mem_cons.2 ⟨subd5_4_109, List.forall_mem_cons.2 ⟨subd5_4_110, List.forall_mem_cons.2 ⟨subd5_4_111, List.forall_mem_cons.2 ⟨subd5_4_112, List.forall_mem_cons.2 ⟨subd5_4_113, List.forall_mem_cons.2 ⟨subd5_4_114, List.forall_mem_cons.2 ⟨subd5_4_115, List.forall_mem_cons.2 ⟨subd5_4_116, List.forall_mem_cons.2 ⟨subd5_4_117, List.forall_mem_cons.2 ⟨subd5_4_118, List.forall_mem_cons.2 ⟨subd5_4_119, List.forall_mem_cons.2 ⟨subd5_4_120, List.forall_mem_cons.2 ⟨subd5_4_121, List.forall_mem_cons.2 ⟨subd5_4_122, List.forall_mem_cons.2 ⟨subd5_4_123, List.forall_mem_cons.2 ⟨subd5_4_124, List.forall_mem_cons.2 ⟨subd5_4_125, List.forall_mem_cons.2 ⟨subd5_4_126, List.forall_mem_cons.2 ⟨subd5_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_4_128 : subd5_4 [1, 1, -2] = true := by decide +kernel
theorem subd5_4_129 : subd5_4 [1, 1, -1] = true := by decide +kernel
theorem subd5_4_130 : subd5_4 [1, 1, 0] = true := by decide +kernel
theorem subd5_4_131 : subd5_4 [1, 1, 1] = true := by decide +kernel
theorem subd5_4_132 : subd5_4 [1, 1, 2] = true := by decide +kernel
theorem subd5_4_133 : subd5_4 [1, 1, 3] = true := by decide +kernel
theorem subd5_4_134 : subd5_4 [1, 1, 4] = true := by decide +kernel
theorem subd5_4_135 : subd5_4 [1, 1, 5] = true := by decide +kernel
theorem subd5_4_136 : subd5_4 [1, 1, 6] = true := by decide +kernel
theorem subd5_4_137 : subd5_4 [1, 2] = true := by decide +kernel
theorem subd5_4_138 : subd5_4 [1, 3] = true := by decide +kernel
theorem subd5_4_139 : subd5_4 [1, 4] = true := by decide +kernel
theorem subd5_4_140 : subd5_4 [2, -4] = true := by decide +kernel
theorem subd5_4_141 : subd5_4 [2, -3] = true := by decide +kernel
theorem subd5_4_142 : subd5_4 [2, -2] = true := by decide +kernel
theorem subd5_4_143 : subd5_4 [2, -1] = true := by decide +kernel
theorem subd5_4_144 : subd5_4 [2, 0] = true := by decide +kernel
theorem subd5_4_145 : subd5_4 [2, 1] = true := by decide +kernel
theorem subd5_4_146 : subd5_4 [2, 2] = true := by decide +kernel
theorem subd5_4_147 : subd5_4 [2, 3] = true := by decide +kernel
theorem subd5_4_148 : subd5_4 [2, 4] = true := by decide +kernel
theorem subd5_4_149 : subd5_4 [3, -3] = true := by decide +kernel
theorem subd5_4_150 : subd5_4 [3, -2] = true := by decide +kernel
theorem subd5_4_151 : subd5_4 [3, -1] = true := by decide +kernel
theorem subd5_4_152 : subd5_4 [3, 0] = true := by decide +kernel
theorem subd5_4_153 : subd5_4 [3, 1] = true := by decide +kernel
theorem subd5_4_154 : subd5_4 [3, 2] = true := by decide +kernel
theorem subd5_4_155 : subd5_4 [3, 3] = true := by decide +kernel
theorem subd5_4_156 : subd5_4 [4, -2] = true := by decide +kernel
theorem subd5_4_157 : subd5_4 [4, -1] = true := by decide +kernel
theorem subd5_4_158 : subd5_4 [4, 0] = true := by decide +kernel
theorem subd5_4_159 : subd5_4 [4, 1] = true := by decide +kernel
theorem sbd5_4_4 : ∀ q ∈ blkd5_4_4, subd5_4 q = true := by
  unfold blkd5_4_4
  exact List.forall_mem_cons.2 ⟨subd5_4_128, List.forall_mem_cons.2 ⟨subd5_4_129, List.forall_mem_cons.2 ⟨subd5_4_130, List.forall_mem_cons.2 ⟨subd5_4_131, List.forall_mem_cons.2 ⟨subd5_4_132, List.forall_mem_cons.2 ⟨subd5_4_133, List.forall_mem_cons.2 ⟨subd5_4_134, List.forall_mem_cons.2 ⟨subd5_4_135, List.forall_mem_cons.2 ⟨subd5_4_136, List.forall_mem_cons.2 ⟨subd5_4_137, List.forall_mem_cons.2 ⟨subd5_4_138, List.forall_mem_cons.2 ⟨subd5_4_139, List.forall_mem_cons.2 ⟨subd5_4_140, List.forall_mem_cons.2 ⟨subd5_4_141, List.forall_mem_cons.2 ⟨subd5_4_142, List.forall_mem_cons.2 ⟨subd5_4_143, List.forall_mem_cons.2 ⟨subd5_4_144, List.forall_mem_cons.2 ⟨subd5_4_145, List.forall_mem_cons.2 ⟨subd5_4_146, List.forall_mem_cons.2 ⟨subd5_4_147, List.forall_mem_cons.2 ⟨subd5_4_148, List.forall_mem_cons.2 ⟨subd5_4_149, List.forall_mem_cons.2 ⟨subd5_4_150, List.forall_mem_cons.2 ⟨subd5_4_151, List.forall_mem_cons.2 ⟨subd5_4_152, List.forall_mem_cons.2 ⟨subd5_4_153, List.forall_mem_cons.2 ⟨subd5_4_154, List.forall_mem_cons.2 ⟨subd5_4_155, List.forall_mem_cons.2 ⟨subd5_4_156, List.forall_mem_cons.2 ⟨subd5_4_157, List.forall_mem_cons.2 ⟨subd5_4_158, List.forall_mem_cons.2 ⟨subd5_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_4_160 : subd5_4 [4, 2] = true := by decide +kernel
theorem sbd5_4_5 : ∀ q ∈ blkd5_4_5, subd5_4 q = true := by
  unfold blkd5_4_5
  exact List.forall_mem_cons.2 ⟨subd5_4_160, List.forall_mem_nil _⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C110
