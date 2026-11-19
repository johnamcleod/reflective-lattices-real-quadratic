import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_5 : ldCheck G d5_5.U d5_5.ms ldd5_5 = true := by decide +kernel
theorem pre_okd5_5 : subPre G cell5 d5_5 = true := by decide +kernel
theorem subd5_5_0 : subd5_5 [-4] = true := by decide +kernel
theorem subd5_5_1 : subd5_5 [-3, -5] = true := by decide +kernel
theorem subd5_5_2 : subd5_5 [-3, -4] = true := by decide +kernel
theorem subd5_5_3 : subd5_5 [-3, -3] = true := by decide +kernel
theorem subd5_5_4 : subd5_5 [-3, -2] = true := by decide +kernel
theorem subd5_5_5 : subd5_5 [-3, -1] = true := by decide +kernel
theorem subd5_5_6 : subd5_5 [-3, 0] = true := by decide +kernel
theorem subd5_5_7 : subd5_5 [-3, 1] = true := by decide +kernel
theorem subd5_5_8 : subd5_5 [-2, -6] = true := by decide +kernel
theorem subd5_5_9 : subd5_5 [-2, -5] = true := by decide +kernel
theorem subd5_5_10 : subd5_5 [-2, -4] = true := by decide +kernel
theorem subd5_5_11 : subd5_5 [-2, -3, -9] = true := by decide +kernel
theorem subd5_5_12 : subd5_5 [-2, -3, -8] = true := by decide +kernel
theorem subd5_5_13 : subd5_5 [-2, -3, -7] = true := by decide +kernel
theorem subd5_5_14 : subd5_5 [-2, -3, -6] = true := by decide +kernel
theorem subd5_5_15 : subd5_5 [-2, -3, -5] = true := by decide +kernel
theorem subd5_5_16 : subd5_5 [-2, -3, -4] = true := by decide +kernel
theorem subd5_5_17 : subd5_5 [-2, -3, -3] = true := by decide +kernel
theorem subd5_5_18 : subd5_5 [-2, -3, -2] = true := by decide +kernel
theorem subd5_5_19 : subd5_5 [-2, -3, -1] = true := by decide +kernel
theorem subd5_5_20 : subd5_5 [-2, -3, 0] = true := by decide +kernel
theorem subd5_5_21 : subd5_5 [-2, -3, 1] = true := by decide +kernel
theorem subd5_5_22 : subd5_5 [-2, -3, 2] = true := by decide +kernel
theorem subd5_5_23 : subd5_5 [-2, -3, 3] = true := by decide +kernel
theorem subd5_5_24 : subd5_5 [-2, -3, 4] = true := by decide +kernel
theorem subd5_5_25 : subd5_5 [-2, -2, -10] = true := by decide +kernel
theorem subd5_5_26 : subd5_5 [-2, -2, -9] = true := by decide +kernel
theorem subd5_5_27 : subd5_5 [-2, -2, -8] = true := by decide +kernel
theorem subd5_5_28 : subd5_5 [-2, -2, -7] = true := by decide +kernel
theorem subd5_5_29 : subd5_5 [-2, -2, -6] = true := by decide +kernel
theorem subd5_5_30 : subd5_5 [-2, -2, -5] = true := by decide +kernel
theorem subd5_5_31 : subd5_5 [-2, -2, -4] = true := by decide +kernel
theorem sbd5_5_0 : ∀ q ∈ blkd5_5_0, subd5_5 q = true := by
  unfold blkd5_5_0
  exact List.forall_mem_cons.2 ⟨subd5_5_0, List.forall_mem_cons.2 ⟨subd5_5_1, List.forall_mem_cons.2 ⟨subd5_5_2, List.forall_mem_cons.2 ⟨subd5_5_3, List.forall_mem_cons.2 ⟨subd5_5_4, List.forall_mem_cons.2 ⟨subd5_5_5, List.forall_mem_cons.2 ⟨subd5_5_6, List.forall_mem_cons.2 ⟨subd5_5_7, List.forall_mem_cons.2 ⟨subd5_5_8, List.forall_mem_cons.2 ⟨subd5_5_9, List.forall_mem_cons.2 ⟨subd5_5_10, List.forall_mem_cons.2 ⟨subd5_5_11, List.forall_mem_cons.2 ⟨subd5_5_12, List.forall_mem_cons.2 ⟨subd5_5_13, List.forall_mem_cons.2 ⟨subd5_5_14, List.forall_mem_cons.2 ⟨subd5_5_15, List.forall_mem_cons.2 ⟨subd5_5_16, List.forall_mem_cons.2 ⟨subd5_5_17, List.forall_mem_cons.2 ⟨subd5_5_18, List.forall_mem_cons.2 ⟨subd5_5_19, List.forall_mem_cons.2 ⟨subd5_5_20, List.forall_mem_cons.2 ⟨subd5_5_21, List.forall_mem_cons.2 ⟨subd5_5_22, List.forall_mem_cons.2 ⟨subd5_5_23, List.forall_mem_cons.2 ⟨subd5_5_24, List.forall_mem_cons.2 ⟨subd5_5_25, List.forall_mem_cons.2 ⟨subd5_5_26, List.forall_mem_cons.2 ⟨subd5_5_27, List.forall_mem_cons.2 ⟨subd5_5_28, List.forall_mem_cons.2 ⟨subd5_5_29, List.forall_mem_cons.2 ⟨subd5_5_30, List.forall_mem_cons.2 ⟨subd5_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_32 : subd5_5 [-2, -2, -3] = true := by decide +kernel
theorem subd5_5_33 : subd5_5 [-2, -2, -2] = true := by decide +kernel
theorem subd5_5_34 : subd5_5 [-2, -2, -1] = true := by decide +kernel
theorem subd5_5_35 : subd5_5 [-2, -2, 0] = true := by decide +kernel
theorem subd5_5_36 : subd5_5 [-2, -2, 1] = true := by decide +kernel
theorem subd5_5_37 : subd5_5 [-2, -2, 2] = true := by decide +kernel
theorem subd5_5_38 : subd5_5 [-2, -2, 3] = true := by decide +kernel
theorem subd5_5_39 : subd5_5 [-2, -2, 4] = true := by decide +kernel
theorem subd5_5_40 : subd5_5 [-2, -2, 5] = true := by decide +kernel
theorem subd5_5_41 : subd5_5 [-2, -1, -9] = true := by decide +kernel
theorem subd5_5_42 : subd5_5 [-2, -1, -8] = true := by decide +kernel
theorem subd5_5_43 : subd5_5 [-2, -1, -7] = true := by decide +kernel
theorem subd5_5_44 : subd5_5 [-2, -1, -6] = true := by decide +kernel
theorem subd5_5_45 : subd5_5 [-2, -1, -5] = true := by decide +kernel
theorem subd5_5_46 : subd5_5 [-2, -1, -4] = true := by decide +kernel
theorem subd5_5_47 : subd5_5 [-2, -1, -3] = true := by decide +kernel
theorem subd5_5_48 : subd5_5 [-2, -1, -2] = true := by decide +kernel
theorem subd5_5_49 : subd5_5 [-2, -1, -1] = true := by decide +kernel
theorem subd5_5_50 : subd5_5 [-2, -1, 0] = true := by decide +kernel
theorem subd5_5_51 : subd5_5 [-2, -1, 1] = true := by decide +kernel
theorem subd5_5_52 : subd5_5 [-2, -1, 2] = true := by decide +kernel
theorem subd5_5_53 : subd5_5 [-2, -1, 3] = true := by decide +kernel
theorem subd5_5_54 : subd5_5 [-2, -1, 4] = true := by decide +kernel
theorem subd5_5_55 : subd5_5 [-2, -1, 5] = true := by decide +kernel
theorem subd5_5_56 : subd5_5 [-2, -1, 6] = true := by decide +kernel
theorem subd5_5_57 : subd5_5 [-2, 0, -9] = true := by decide +kernel
theorem subd5_5_58 : subd5_5 [-2, 0, -8] = true := by decide +kernel
theorem subd5_5_59 : subd5_5 [-2, 0, -7] = true := by decide +kernel
theorem subd5_5_60 : subd5_5 [-2, 0, -6] = true := by decide +kernel
theorem subd5_5_61 : subd5_5 [-2, 0, -5] = true := by decide +kernel
theorem subd5_5_62 : subd5_5 [-2, 0, -4] = true := by decide +kernel
theorem subd5_5_63 : subd5_5 [-2, 0, -3] = true := by decide +kernel
theorem sbd5_5_1 : ∀ q ∈ blkd5_5_1, subd5_5 q = true := by
  unfold blkd5_5_1
  exact List.forall_mem_cons.2 ⟨subd5_5_32, List.forall_mem_cons.2 ⟨subd5_5_33, List.forall_mem_cons.2 ⟨subd5_5_34, List.forall_mem_cons.2 ⟨subd5_5_35, List.forall_mem_cons.2 ⟨subd5_5_36, List.forall_mem_cons.2 ⟨subd5_5_37, List.forall_mem_cons.2 ⟨subd5_5_38, List.forall_mem_cons.2 ⟨subd5_5_39, List.forall_mem_cons.2 ⟨subd5_5_40, List.forall_mem_cons.2 ⟨subd5_5_41, List.forall_mem_cons.2 ⟨subd5_5_42, List.forall_mem_cons.2 ⟨subd5_5_43, List.forall_mem_cons.2 ⟨subd5_5_44, List.forall_mem_cons.2 ⟨subd5_5_45, List.forall_mem_cons.2 ⟨subd5_5_46, List.forall_mem_cons.2 ⟨subd5_5_47, List.forall_mem_cons.2 ⟨subd5_5_48, List.forall_mem_cons.2 ⟨subd5_5_49, List.forall_mem_cons.2 ⟨subd5_5_50, List.forall_mem_cons.2 ⟨subd5_5_51, List.forall_mem_cons.2 ⟨subd5_5_52, List.forall_mem_cons.2 ⟨subd5_5_53, List.forall_mem_cons.2 ⟨subd5_5_54, List.forall_mem_cons.2 ⟨subd5_5_55, List.forall_mem_cons.2 ⟨subd5_5_56, List.forall_mem_cons.2 ⟨subd5_5_57, List.forall_mem_cons.2 ⟨subd5_5_58, List.forall_mem_cons.2 ⟨subd5_5_59, List.forall_mem_cons.2 ⟨subd5_5_60, List.forall_mem_cons.2 ⟨subd5_5_61, List.forall_mem_cons.2 ⟨subd5_5_62, List.forall_mem_cons.2 ⟨subd5_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_64 : subd5_5 [-2, 0, -2] = true := by decide +kernel
theorem subd5_5_65 : subd5_5 [-2, 0, -1] = true := by decide +kernel
theorem subd5_5_66 : subd5_5 [-2, 0, 0] = true := by decide +kernel
theorem subd5_5_67 : subd5_5 [-2, 0, 1] = true := by decide +kernel
theorem subd5_5_68 : subd5_5 [-2, 0, 2] = true := by decide +kernel
theorem subd5_5_69 : subd5_5 [-2, 0, 3] = true := by decide +kernel
theorem subd5_5_70 : subd5_5 [-2, 0, 4] = true := by decide +kernel
theorem subd5_5_71 : subd5_5 [-2, 0, 5] = true := by decide +kernel
theorem subd5_5_72 : subd5_5 [-2, 0, 6] = true := by decide +kernel
theorem subd5_5_73 : subd5_5 [-2, 1, -7] = true := by decide +kernel
theorem subd5_5_74 : subd5_5 [-2, 1, -6] = true := by decide +kernel
theorem subd5_5_75 : subd5_5 [-2, 1, -5] = true := by decide +kernel
theorem subd5_5_76 : subd5_5 [-2, 1, -4] = true := by decide +kernel
theorem subd5_5_77 : subd5_5 [-2, 1, -3] = true := by decide +kernel
theorem subd5_5_78 : subd5_5 [-2, 1, -2] = true := by decide +kernel
theorem subd5_5_79 : subd5_5 [-2, 1, -1] = true := by decide +kernel
theorem subd5_5_80 : subd5_5 [-2, 1, 0] = true := by decide +kernel
theorem subd5_5_81 : subd5_5 [-2, 1, 1] = true := by decide +kernel
theorem subd5_5_82 : subd5_5 [-2, 1, 2] = true := by decide +kernel
theorem subd5_5_83 : subd5_5 [-2, 1, 3] = true := by decide +kernel
theorem subd5_5_84 : subd5_5 [-2, 1, 4] = true := by decide +kernel
theorem subd5_5_85 : subd5_5 [-2, 1, 5] = true := by decide +kernel
theorem subd5_5_86 : subd5_5 [-2, 1, 6] = true := by decide +kernel
theorem subd5_5_87 : subd5_5 [-2, 2] = true := by decide +kernel
theorem subd5_5_88 : subd5_5 [-2, 3] = true := by decide +kernel
theorem subd5_5_89 : subd5_5 [-1, -6] = true := by decide +kernel
theorem subd5_5_90 : subd5_5 [-1, -5] = true := by decide +kernel
theorem subd5_5_91 : subd5_5 [-1, -4] = true := by decide +kernel
theorem subd5_5_92 : subd5_5 [-1, -3, -9] = true := by decide +kernel
theorem subd5_5_93 : subd5_5 [-1, -3, -8] = true := by decide +kernel
theorem subd5_5_94 : subd5_5 [-1, -3, -7] = true := by decide +kernel
theorem subd5_5_95 : subd5_5 [-1, -3, -6] = true := by decide +kernel
theorem sbd5_5_2 : ∀ q ∈ blkd5_5_2, subd5_5 q = true := by
  unfold blkd5_5_2
  exact List.forall_mem_cons.2 ⟨subd5_5_64, List.forall_mem_cons.2 ⟨subd5_5_65, List.forall_mem_cons.2 ⟨subd5_5_66, List.forall_mem_cons.2 ⟨subd5_5_67, List.forall_mem_cons.2 ⟨subd5_5_68, List.forall_mem_cons.2 ⟨subd5_5_69, List.forall_mem_cons.2 ⟨subd5_5_70, List.forall_mem_cons.2 ⟨subd5_5_71, List.forall_mem_cons.2 ⟨subd5_5_72, List.forall_mem_cons.2 ⟨subd5_5_73, List.forall_mem_cons.2 ⟨subd5_5_74, List.forall_mem_cons.2 ⟨subd5_5_75, List.forall_mem_cons.2 ⟨subd5_5_76, List.forall_mem_cons.2 ⟨subd5_5_77, List.forall_mem_cons.2 ⟨subd5_5_78, List.forall_mem_cons.2 ⟨subd5_5_79, List.forall_mem_cons.2 ⟨subd5_5_80, List.forall_mem_cons.2 ⟨subd5_5_81, List.forall_mem_cons.2 ⟨subd5_5_82, List.forall_mem_cons.2 ⟨subd5_5_83, List.forall_mem_cons.2 ⟨subd5_5_84, List.forall_mem_cons.2 ⟨subd5_5_85, List.forall_mem_cons.2 ⟨subd5_5_86, List.forall_mem_cons.2 ⟨subd5_5_87, List.forall_mem_cons.2 ⟨subd5_5_88, List.forall_mem_cons.2 ⟨subd5_5_89, List.forall_mem_cons.2 ⟨subd5_5_90, List.forall_mem_cons.2 ⟨subd5_5_91, List.forall_mem_cons.2 ⟨subd5_5_92, List.forall_mem_cons.2 ⟨subd5_5_93, List.forall_mem_cons.2 ⟨subd5_5_94, List.forall_mem_cons.2 ⟨subd5_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_96 : subd5_5 [-1, -3, -5] = true := by decide +kernel
theorem subd5_5_97 : subd5_5 [-1, -3, -4] = true := by decide +kernel
theorem subd5_5_98 : subd5_5 [-1, -3, -3] = true := by decide +kernel
theorem subd5_5_99 : subd5_5 [-1, -3, -2] = true := by decide +kernel
theorem subd5_5_100 : subd5_5 [-1, -3, -1] = true := by decide +kernel
theorem subd5_5_101 : subd5_5 [-1, -3, 0] = true := by decide +kernel
theorem subd5_5_102 : subd5_5 [-1, -3, 1] = true := by decide +kernel
theorem subd5_5_103 : subd5_5 [-1, -3, 2] = true := by decide +kernel
theorem subd5_5_104 : subd5_5 [-1, -3, 3] = true := by decide +kernel
theorem subd5_5_105 : subd5_5 [-1, -3, 4] = true := by decide +kernel
theorem subd5_5_106 : subd5_5 [-1, -3, 5] = true := by decide +kernel
theorem subd5_5_107 : subd5_5 [-1, -2, -10] = true := by decide +kernel
theorem subd5_5_108 : subd5_5 [-1, -2, -9] = true := by decide +kernel
theorem subd5_5_109 : subd5_5 [-1, -2, -8] = true := by decide +kernel
theorem subd5_5_110 : subd5_5 [-1, -2, -7] = true := by decide +kernel
theorem subd5_5_111 : subd5_5 [-1, -2, -6] = true := by decide +kernel
theorem subd5_5_112 : subd5_5 [-1, -2, -5] = true := by decide +kernel
theorem subd5_5_113 : subd5_5 [-1, -2, -4] = true := by decide +kernel
theorem subd5_5_114 : subd5_5 [-1, -2, -3] = true := by decide +kernel
theorem subd5_5_115 : subd5_5 [-1, -2, -2] = true := by decide +kernel
theorem subd5_5_116 : subd5_5 [-1, -2, -1] = true := by decide +kernel
theorem subd5_5_117 : subd5_5 [-1, -2, 0] = true := by decide +kernel
theorem subd5_5_118 : subd5_5 [-1, -2, 1] = true := by decide +kernel
theorem subd5_5_119 : subd5_5 [-1, -2, 2] = true := by decide +kernel
theorem subd5_5_120 : subd5_5 [-1, -2, 3] = true := by decide +kernel
theorem subd5_5_121 : subd5_5 [-1, -2, 4] = true := by decide +kernel
theorem subd5_5_122 : subd5_5 [-1, -2, 5] = true := by decide +kernel
theorem subd5_5_123 : subd5_5 [-1, -2, 6] = true := by decide +kernel
theorem subd5_5_124 : subd5_5 [-1, -1, -10] = true := by decide +kernel
theorem subd5_5_125 : subd5_5 [-1, -1, -9] = true := by decide +kernel
theorem subd5_5_126 : subd5_5 [-1, -1, -8] = true := by decide +kernel
theorem subd5_5_127 : subd5_5 [-1, -1, -7] = true := by decide +kernel
theorem sbd5_5_3 : ∀ q ∈ blkd5_5_3, subd5_5 q = true := by
  unfold blkd5_5_3
  exact List.forall_mem_cons.2 ⟨subd5_5_96, List.forall_mem_cons.2 ⟨subd5_5_97, List.forall_mem_cons.2 ⟨subd5_5_98, List.forall_mem_cons.2 ⟨subd5_5_99, List.forall_mem_cons.2 ⟨subd5_5_100, List.forall_mem_cons.2 ⟨subd5_5_101, List.forall_mem_cons.2 ⟨subd5_5_102, List.forall_mem_cons.2 ⟨subd5_5_103, List.forall_mem_cons.2 ⟨subd5_5_104, List.forall_mem_cons.2 ⟨subd5_5_105, List.forall_mem_cons.2 ⟨subd5_5_106, List.forall_mem_cons.2 ⟨subd5_5_107, List.forall_mem_cons.2 ⟨subd5_5_108, List.forall_mem_cons.2 ⟨subd5_5_109, List.forall_mem_cons.2 ⟨subd5_5_110, List.forall_mem_cons.2 ⟨subd5_5_111, List.forall_mem_cons.2 ⟨subd5_5_112, List.forall_mem_cons.2 ⟨subd5_5_113, List.forall_mem_cons.2 ⟨subd5_5_114, List.forall_mem_cons.2 ⟨subd5_5_115, List.forall_mem_cons.2 ⟨subd5_5_116, List.forall_mem_cons.2 ⟨subd5_5_117, List.forall_mem_cons.2 ⟨subd5_5_118, List.forall_mem_cons.2 ⟨subd5_5_119, List.forall_mem_cons.2 ⟨subd5_5_120, List.forall_mem_cons.2 ⟨subd5_5_121, List.forall_mem_cons.2 ⟨subd5_5_122, List.forall_mem_cons.2 ⟨subd5_5_123, List.forall_mem_cons.2 ⟨subd5_5_124, List.forall_mem_cons.2 ⟨subd5_5_125, List.forall_mem_cons.2 ⟨subd5_5_126, List.forall_mem_cons.2 ⟨subd5_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_128 : subd5_5 [-1, -1, -6] = true := by decide +kernel
theorem subd5_5_129 : subd5_5 [-1, -1, -5] = true := by decide +kernel
theorem subd5_5_130 : subd5_5 [-1, -1, -4] = true := by decide +kernel
theorem subd5_5_131 : subd5_5 [-1, -1, -3] = true := by decide +kernel
theorem subd5_5_132 : subd5_5 [-1, -1, -2] = true := by decide +kernel
theorem subd5_5_133 : subd5_5 [-1, -1, -1] = true := by decide +kernel
theorem subd5_5_134 : subd5_5 [-1, -1, 0] = true := by decide +kernel
theorem subd5_5_135 : subd5_5 [-1, -1, 1] = true := by decide +kernel
theorem subd5_5_136 : subd5_5 [-1, -1, 2] = true := by decide +kernel
theorem subd5_5_137 : subd5_5 [-1, -1, 3] = true := by decide +kernel
theorem subd5_5_138 : subd5_5 [-1, -1, 4] = true := by decide +kernel
theorem subd5_5_139 : subd5_5 [-1, -1, 5] = true := by decide +kernel
theorem subd5_5_140 : subd5_5 [-1, -1, 6] = true := by decide +kernel
theorem subd5_5_141 : subd5_5 [-1, -1, 7] = true := by decide +kernel
theorem subd5_5_142 : subd5_5 [-1, 0, -9] = true := by decide +kernel
theorem subd5_5_143 : subd5_5 [-1, 0, -8] = true := by decide +kernel
theorem subd5_5_144 : subd5_5 [-1, 0, -7] = true := by decide +kernel
theorem subd5_5_145 : subd5_5 [-1, 0, -6] = true := by decide +kernel
theorem subd5_5_146 : subd5_5 [-1, 0, -5] = true := by decide +kernel
theorem subd5_5_147 : subd5_5 [-1, 0, -4] = true := by decide +kernel
theorem subd5_5_148 : subd5_5 [-1, 0, -3] = true := by decide +kernel
theorem subd5_5_149 : subd5_5 [-1, 0, -2] = true := by decide +kernel
theorem subd5_5_150 : subd5_5 [-1, 0, -1] = true := by decide +kernel
theorem subd5_5_151 : subd5_5 [-1, 0, 0] = true := by decide +kernel
theorem subd5_5_152 : subd5_5 [-1, 0, 1] = true := by decide +kernel
theorem subd5_5_153 : subd5_5 [-1, 0, 2] = true := by decide +kernel
theorem subd5_5_154 : subd5_5 [-1, 0, 3] = true := by decide +kernel
theorem subd5_5_155 : subd5_5 [-1, 0, 4] = true := by decide +kernel
theorem subd5_5_156 : subd5_5 [-1, 0, 5] = true := by decide +kernel
theorem subd5_5_157 : subd5_5 [-1, 0, 6] = true := by decide +kernel
theorem subd5_5_158 : subd5_5 [-1, 0, 7] = true := by decide +kernel
theorem subd5_5_159 : subd5_5 [-1, 0, 8] = true := by decide +kernel
theorem sbd5_5_4 : ∀ q ∈ blkd5_5_4, subd5_5 q = true := by
  unfold blkd5_5_4
  exact List.forall_mem_cons.2 ⟨subd5_5_128, List.forall_mem_cons.2 ⟨subd5_5_129, List.forall_mem_cons.2 ⟨subd5_5_130, List.forall_mem_cons.2 ⟨subd5_5_131, List.forall_mem_cons.2 ⟨subd5_5_132, List.forall_mem_cons.2 ⟨subd5_5_133, List.forall_mem_cons.2 ⟨subd5_5_134, List.forall_mem_cons.2 ⟨subd5_5_135, List.forall_mem_cons.2 ⟨subd5_5_136, List.forall_mem_cons.2 ⟨subd5_5_137, List.forall_mem_cons.2 ⟨subd5_5_138, List.forall_mem_cons.2 ⟨subd5_5_139, List.forall_mem_cons.2 ⟨subd5_5_140, List.forall_mem_cons.2 ⟨subd5_5_141, List.forall_mem_cons.2 ⟨subd5_5_142, List.forall_mem_cons.2 ⟨subd5_5_143, List.forall_mem_cons.2 ⟨subd5_5_144, List.forall_mem_cons.2 ⟨subd5_5_145, List.forall_mem_cons.2 ⟨subd5_5_146, List.forall_mem_cons.2 ⟨subd5_5_147, List.forall_mem_cons.2 ⟨subd5_5_148, List.forall_mem_cons.2 ⟨subd5_5_149, List.forall_mem_cons.2 ⟨subd5_5_150, List.forall_mem_cons.2 ⟨subd5_5_151, List.forall_mem_cons.2 ⟨subd5_5_152, List.forall_mem_cons.2 ⟨subd5_5_153, List.forall_mem_cons.2 ⟨subd5_5_154, List.forall_mem_cons.2 ⟨subd5_5_155, List.forall_mem_cons.2 ⟨subd5_5_156, List.forall_mem_cons.2 ⟨subd5_5_157, List.forall_mem_cons.2 ⟨subd5_5_158, List.forall_mem_cons.2 ⟨subd5_5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_160 : subd5_5 [-1, 1, -8] = true := by decide +kernel
theorem subd5_5_161 : subd5_5 [-1, 1, -7] = true := by decide +kernel
theorem subd5_5_162 : subd5_5 [-1, 1, -6] = true := by decide +kernel
theorem subd5_5_163 : subd5_5 [-1, 1, -5] = true := by decide +kernel
theorem subd5_5_164 : subd5_5 [-1, 1, -4] = true := by decide +kernel
theorem subd5_5_165 : subd5_5 [-1, 1, -3] = true := by decide +kernel
theorem subd5_5_166 : subd5_5 [-1, 1, -2] = true := by decide +kernel
theorem subd5_5_167 : subd5_5 [-1, 1, -1] = true := by decide +kernel
theorem subd5_5_168 : subd5_5 [-1, 1, 0] = true := by decide +kernel
theorem subd5_5_169 : subd5_5 [-1, 1, 1] = true := by decide +kernel
theorem subd5_5_170 : subd5_5 [-1, 1, 2] = true := by decide +kernel
theorem subd5_5_171 : subd5_5 [-1, 1, 3] = true := by decide +kernel
theorem subd5_5_172 : subd5_5 [-1, 1, 4] = true := by decide +kernel
theorem subd5_5_173 : subd5_5 [-1, 1, 5] = true := by decide +kernel
theorem subd5_5_174 : subd5_5 [-1, 1, 6] = true := by decide +kernel
theorem subd5_5_175 : subd5_5 [-1, 1, 7] = true := by decide +kernel
theorem subd5_5_176 : subd5_5 [-1, 1, 8] = true := by decide +kernel
theorem subd5_5_177 : subd5_5 [-1, 2, -7] = true := by decide +kernel
theorem subd5_5_178 : subd5_5 [-1, 2, -6] = true := by decide +kernel
theorem subd5_5_179 : subd5_5 [-1, 2, -5] = true := by decide +kernel
theorem subd5_5_180 : subd5_5 [-1, 2, -4] = true := by decide +kernel
theorem subd5_5_181 : subd5_5 [-1, 2, -3] = true := by decide +kernel
theorem subd5_5_182 : subd5_5 [-1, 2, -2] = true := by decide +kernel
theorem subd5_5_183 : subd5_5 [-1, 2, -1] = true := by decide +kernel
theorem subd5_5_184 : subd5_5 [-1, 2, 0] = true := by decide +kernel
theorem subd5_5_185 : subd5_5 [-1, 2, 1] = true := by decide +kernel
theorem subd5_5_186 : subd5_5 [-1, 2, 2] = true := by decide +kernel
theorem subd5_5_187 : subd5_5 [-1, 2, 3] = true := by decide +kernel
theorem subd5_5_188 : subd5_5 [-1, 2, 4] = true := by decide +kernel
theorem subd5_5_189 : subd5_5 [-1, 2, 5] = true := by decide +kernel
theorem subd5_5_190 : subd5_5 [-1, 2, 6] = true := by decide +kernel
theorem subd5_5_191 : subd5_5 [-1, 2, 7] = true := by decide +kernel
theorem sbd5_5_5 : ∀ q ∈ blkd5_5_5, subd5_5 q = true := by
  unfold blkd5_5_5
  exact List.forall_mem_cons.2 ⟨subd5_5_160, List.forall_mem_cons.2 ⟨subd5_5_161, List.forall_mem_cons.2 ⟨subd5_5_162, List.forall_mem_cons.2 ⟨subd5_5_163, List.forall_mem_cons.2 ⟨subd5_5_164, List.forall_mem_cons.2 ⟨subd5_5_165, List.forall_mem_cons.2 ⟨subd5_5_166, List.forall_mem_cons.2 ⟨subd5_5_167, List.forall_mem_cons.2 ⟨subd5_5_168, List.forall_mem_cons.2 ⟨subd5_5_169, List.forall_mem_cons.2 ⟨subd5_5_170, List.forall_mem_cons.2 ⟨subd5_5_171, List.forall_mem_cons.2 ⟨subd5_5_172, List.forall_mem_cons.2 ⟨subd5_5_173, List.forall_mem_cons.2 ⟨subd5_5_174, List.forall_mem_cons.2 ⟨subd5_5_175, List.forall_mem_cons.2 ⟨subd5_5_176, List.forall_mem_cons.2 ⟨subd5_5_177, List.forall_mem_cons.2 ⟨subd5_5_178, List.forall_mem_cons.2 ⟨subd5_5_179, List.forall_mem_cons.2 ⟨subd5_5_180, List.forall_mem_cons.2 ⟨subd5_5_181, List.forall_mem_cons.2 ⟨subd5_5_182, List.forall_mem_cons.2 ⟨subd5_5_183, List.forall_mem_cons.2 ⟨subd5_5_184, List.forall_mem_cons.2 ⟨subd5_5_185, List.forall_mem_cons.2 ⟨subd5_5_186, List.forall_mem_cons.2 ⟨subd5_5_187, List.forall_mem_cons.2 ⟨subd5_5_188, List.forall_mem_cons.2 ⟨subd5_5_189, List.forall_mem_cons.2 ⟨subd5_5_190, List.forall_mem_cons.2 ⟨subd5_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_192 : subd5_5 [-1, 3] = true := by decide +kernel
theorem subd5_5_193 : subd5_5 [-1, 4] = true := by decide +kernel
theorem subd5_5_194 : subd5_5 [0, -5] = true := by decide +kernel
theorem subd5_5_195 : subd5_5 [0, -4] = true := by decide +kernel
theorem subd5_5_196 : subd5_5 [0, -3, -9] = true := by decide +kernel
theorem subd5_5_197 : subd5_5 [0, -3, -8] = true := by decide +kernel
theorem subd5_5_198 : subd5_5 [0, -3, -7] = true := by decide +kernel
theorem subd5_5_199 : subd5_5 [0, -3, -6] = true := by decide +kernel
theorem subd5_5_200 : subd5_5 [0, -3, -5] = true := by decide +kernel
theorem subd5_5_201 : subd5_5 [0, -3, -4] = true := by decide +kernel
theorem subd5_5_202 : subd5_5 [0, -3, -3] = true := by decide +kernel
theorem subd5_5_203 : subd5_5 [0, -3, -2] = true := by decide +kernel
theorem subd5_5_204 : subd5_5 [0, -3, -1] = true := by decide +kernel
theorem subd5_5_205 : subd5_5 [0, -3, 0] = true := by decide +kernel
theorem subd5_5_206 : subd5_5 [0, -3, 1] = true := by decide +kernel
theorem subd5_5_207 : subd5_5 [0, -3, 2] = true := by decide +kernel
theorem subd5_5_208 : subd5_5 [0, -3, 3] = true := by decide +kernel
theorem subd5_5_209 : subd5_5 [0, -3, 4] = true := by decide +kernel
theorem subd5_5_210 : subd5_5 [0, -3, 5] = true := by decide +kernel
theorem subd5_5_211 : subd5_5 [0, -2, -9] = true := by decide +kernel
theorem subd5_5_212 : subd5_5 [0, -2, -8] = true := by decide +kernel
theorem subd5_5_213 : subd5_5 [0, -2, -7] = true := by decide +kernel
theorem subd5_5_214 : subd5_5 [0, -2, -6] = true := by decide +kernel
theorem subd5_5_215 : subd5_5 [0, -2, -5] = true := by decide +kernel
theorem subd5_5_216 : subd5_5 [0, -2, -4] = true := by decide +kernel
theorem subd5_5_217 : subd5_5 [0, -2, -3] = true := by decide +kernel
theorem subd5_5_218 : subd5_5 [0, -2, -2] = true := by decide +kernel
theorem subd5_5_219 : subd5_5 [0, -2, -1] = true := by decide +kernel
theorem subd5_5_220 : subd5_5 [0, -2, 0] = true := by decide +kernel
theorem subd5_5_221 : subd5_5 [0, -2, 1] = true := by decide +kernel
theorem subd5_5_222 : subd5_5 [0, -2, 2] = true := by decide +kernel
theorem subd5_5_223 : subd5_5 [0, -2, 3] = true := by decide +kernel
theorem sbd5_5_6 : ∀ q ∈ blkd5_5_6, subd5_5 q = true := by
  unfold blkd5_5_6
  exact List.forall_mem_cons.2 ⟨subd5_5_192, List.forall_mem_cons.2 ⟨subd5_5_193, List.forall_mem_cons.2 ⟨subd5_5_194, List.forall_mem_cons.2 ⟨subd5_5_195, List.forall_mem_cons.2 ⟨subd5_5_196, List.forall_mem_cons.2 ⟨subd5_5_197, List.forall_mem_cons.2 ⟨subd5_5_198, List.forall_mem_cons.2 ⟨subd5_5_199, List.forall_mem_cons.2 ⟨subd5_5_200, List.forall_mem_cons.2 ⟨subd5_5_201, List.forall_mem_cons.2 ⟨subd5_5_202, List.forall_mem_cons.2 ⟨subd5_5_203, List.forall_mem_cons.2 ⟨subd5_5_204, List.forall_mem_cons.2 ⟨subd5_5_205, List.forall_mem_cons.2 ⟨subd5_5_206, List.forall_mem_cons.2 ⟨subd5_5_207, List.forall_mem_cons.2 ⟨subd5_5_208, List.forall_mem_cons.2 ⟨subd5_5_209, List.forall_mem_cons.2 ⟨subd5_5_210, List.forall_mem_cons.2 ⟨subd5_5_211, List.forall_mem_cons.2 ⟨subd5_5_212, List.forall_mem_cons.2 ⟨subd5_5_213, List.forall_mem_cons.2 ⟨subd5_5_214, List.forall_mem_cons.2 ⟨subd5_5_215, List.forall_mem_cons.2 ⟨subd5_5_216, List.forall_mem_cons.2 ⟨subd5_5_217, List.forall_mem_cons.2 ⟨subd5_5_218, List.forall_mem_cons.2 ⟨subd5_5_219, List.forall_mem_cons.2 ⟨subd5_5_220, List.forall_mem_cons.2 ⟨subd5_5_221, List.forall_mem_cons.2 ⟨subd5_5_222, List.forall_mem_cons.2 ⟨subd5_5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_224 : subd5_5 [0, -2, 4] = true := by decide +kernel
theorem subd5_5_225 : subd5_5 [0, -2, 5] = true := by decide +kernel
theorem subd5_5_226 : subd5_5 [0, -2, 6] = true := by decide +kernel
theorem subd5_5_227 : subd5_5 [0, -2, 7] = true := by decide +kernel
theorem subd5_5_228 : subd5_5 [0, -1, -10] = true := by decide +kernel
theorem subd5_5_229 : subd5_5 [0, -1, -9] = true := by decide +kernel
theorem subd5_5_230 : subd5_5 [0, -1, -8] = true := by decide +kernel
theorem subd5_5_231 : subd5_5 [0, -1, -7] = true := by decide +kernel
theorem subd5_5_232 : subd5_5 [0, -1, -6] = true := by decide +kernel
theorem subd5_5_233 : subd5_5 [0, -1, -5] = true := by decide +kernel
theorem subd5_5_234 : subd5_5 [0, -1, -4] = true := by decide +kernel
theorem subd5_5_235 : subd5_5 [0, -1, -3] = true := by decide +kernel
theorem subd5_5_236 : subd5_5 [0, -1, -2] = true := by decide +kernel
theorem subd5_5_237 : subd5_5 [0, -1, -1] = true := by decide +kernel
theorem subd5_5_238 : subd5_5 [0, -1, 0] = true := by decide +kernel
theorem subd5_5_239 : subd5_5 [0, -1, 1] = true := by decide +kernel
theorem subd5_5_240 : subd5_5 [0, -1, 2] = true := by decide +kernel
theorem subd5_5_241 : subd5_5 [0, -1, 3] = true := by decide +kernel
theorem subd5_5_242 : subd5_5 [0, -1, 4] = true := by decide +kernel
theorem subd5_5_243 : subd5_5 [0, -1, 5] = true := by decide +kernel
theorem subd5_5_244 : subd5_5 [0, -1, 6] = true := by decide +kernel
theorem subd5_5_245 : subd5_5 [0, -1, 7] = true := by decide +kernel
theorem subd5_5_246 : subd5_5 [0, -1, 8] = true := by decide +kernel
theorem subd5_5_247 : subd5_5 [0, 0, -9] = true := by decide +kernel
theorem subd5_5_248 : subd5_5 [0, 0, -8] = true := by decide +kernel
theorem subd5_5_249 : subd5_5 [0, 0, -7] = true := by decide +kernel
theorem subd5_5_250 : subd5_5 [0, 0, -6] = true := by decide +kernel
theorem subd5_5_251 : subd5_5 [0, 0, -5] = true := by decide +kernel
theorem subd5_5_252 : subd5_5 [0, 0, -4] = true := by decide +kernel
theorem subd5_5_253 : subd5_5 [0, 0, -3] = true := by decide +kernel
theorem subd5_5_254 : subd5_5 [0, 0, -2] = true := by decide +kernel
theorem subd5_5_255 : subd5_5 [0, 0, -1] = true := by decide +kernel
theorem sbd5_5_7 : ∀ q ∈ blkd5_5_7, subd5_5 q = true := by
  unfold blkd5_5_7
  exact List.forall_mem_cons.2 ⟨subd5_5_224, List.forall_mem_cons.2 ⟨subd5_5_225, List.forall_mem_cons.2 ⟨subd5_5_226, List.forall_mem_cons.2 ⟨subd5_5_227, List.forall_mem_cons.2 ⟨subd5_5_228, List.forall_mem_cons.2 ⟨subd5_5_229, List.forall_mem_cons.2 ⟨subd5_5_230, List.forall_mem_cons.2 ⟨subd5_5_231, List.forall_mem_cons.2 ⟨subd5_5_232, List.forall_mem_cons.2 ⟨subd5_5_233, List.forall_mem_cons.2 ⟨subd5_5_234, List.forall_mem_cons.2 ⟨subd5_5_235, List.forall_mem_cons.2 ⟨subd5_5_236, List.forall_mem_cons.2 ⟨subd5_5_237, List.forall_mem_cons.2 ⟨subd5_5_238, List.forall_mem_cons.2 ⟨subd5_5_239, List.forall_mem_cons.2 ⟨subd5_5_240, List.forall_mem_cons.2 ⟨subd5_5_241, List.forall_mem_cons.2 ⟨subd5_5_242, List.forall_mem_cons.2 ⟨subd5_5_243, List.forall_mem_cons.2 ⟨subd5_5_244, List.forall_mem_cons.2 ⟨subd5_5_245, List.forall_mem_cons.2 ⟨subd5_5_246, List.forall_mem_cons.2 ⟨subd5_5_247, List.forall_mem_cons.2 ⟨subd5_5_248, List.forall_mem_cons.2 ⟨subd5_5_249, List.forall_mem_cons.2 ⟨subd5_5_250, List.forall_mem_cons.2 ⟨subd5_5_251, List.forall_mem_cons.2 ⟨subd5_5_252, List.forall_mem_cons.2 ⟨subd5_5_253, List.forall_mem_cons.2 ⟨subd5_5_254, List.forall_mem_cons.2 ⟨subd5_5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_256 : subd5_5 [0, 0, 0] = true := by decide +kernel
theorem subd5_5_257 : subd5_5 [0, 0, 1] = true := by decide +kernel
theorem subd5_5_258 : subd5_5 [0, 0, 2] = true := by decide +kernel
theorem subd5_5_259 : subd5_5 [0, 0, 3] = true := by decide +kernel
theorem subd5_5_260 : subd5_5 [0, 0, 4] = true := by decide +kernel
theorem subd5_5_261 : subd5_5 [0, 0, 5] = true := by decide +kernel
theorem subd5_5_262 : subd5_5 [0, 0, 6] = true := by decide +kernel
theorem subd5_5_263 : subd5_5 [0, 0, 7] = true := by decide +kernel
theorem subd5_5_264 : subd5_5 [0, 0, 8] = true := by decide +kernel
theorem subd5_5_265 : subd5_5 [0, 1, -9] = true := by decide +kernel
theorem subd5_5_266 : subd5_5 [0, 1, -8] = true := by decide +kernel
theorem subd5_5_267 : subd5_5 [0, 1, -7] = true := by decide +kernel
theorem subd5_5_268 : subd5_5 [0, 1, -6] = true := by decide +kernel
theorem subd5_5_269 : subd5_5 [0, 1, -5] = true := by decide +kernel
theorem subd5_5_270 : subd5_5 [0, 1, -4] = true := by decide +kernel
theorem subd5_5_271 : subd5_5 [0, 1, -3] = true := by decide +kernel
theorem subd5_5_272 : subd5_5 [0, 1, -2] = true := by decide +kernel
theorem subd5_5_273 : subd5_5 [0, 1, -1] = true := by decide +kernel
theorem subd5_5_274 : subd5_5 [0, 1, 0] = true := by decide +kernel
theorem subd5_5_275 : subd5_5 [0, 1, 1] = true := by decide +kernel
theorem subd5_5_276 : subd5_5 [0, 1, 2] = true := by decide +kernel
theorem subd5_5_277 : subd5_5 [0, 1, 3] = true := by decide +kernel
theorem subd5_5_278 : subd5_5 [0, 1, 4] = true := by decide +kernel
theorem subd5_5_279 : subd5_5 [0, 1, 5] = true := by decide +kernel
theorem subd5_5_280 : subd5_5 [0, 1, 6] = true := by decide +kernel
theorem subd5_5_281 : subd5_5 [0, 1, 7] = true := by decide +kernel
theorem subd5_5_282 : subd5_5 [0, 1, 8] = true := by decide +kernel
theorem subd5_5_283 : subd5_5 [0, 1, 9] = true := by decide +kernel
theorem subd5_5_284 : subd5_5 [0, 2, -8] = true := by decide +kernel
theorem subd5_5_285 : subd5_5 [0, 2, -7] = true := by decide +kernel
theorem subd5_5_286 : subd5_5 [0, 2, -6] = true := by decide +kernel
theorem subd5_5_287 : subd5_5 [0, 2, -5] = true := by decide +kernel
theorem sbd5_5_8 : ∀ q ∈ blkd5_5_8, subd5_5 q = true := by
  unfold blkd5_5_8
  exact List.forall_mem_cons.2 ⟨subd5_5_256, List.forall_mem_cons.2 ⟨subd5_5_257, List.forall_mem_cons.2 ⟨subd5_5_258, List.forall_mem_cons.2 ⟨subd5_5_259, List.forall_mem_cons.2 ⟨subd5_5_260, List.forall_mem_cons.2 ⟨subd5_5_261, List.forall_mem_cons.2 ⟨subd5_5_262, List.forall_mem_cons.2 ⟨subd5_5_263, List.forall_mem_cons.2 ⟨subd5_5_264, List.forall_mem_cons.2 ⟨subd5_5_265, List.forall_mem_cons.2 ⟨subd5_5_266, List.forall_mem_cons.2 ⟨subd5_5_267, List.forall_mem_cons.2 ⟨subd5_5_268, List.forall_mem_cons.2 ⟨subd5_5_269, List.forall_mem_cons.2 ⟨subd5_5_270, List.forall_mem_cons.2 ⟨subd5_5_271, List.forall_mem_cons.2 ⟨subd5_5_272, List.forall_mem_cons.2 ⟨subd5_5_273, List.forall_mem_cons.2 ⟨subd5_5_274, List.forall_mem_cons.2 ⟨subd5_5_275, List.forall_mem_cons.2 ⟨subd5_5_276, List.forall_mem_cons.2 ⟨subd5_5_277, List.forall_mem_cons.2 ⟨subd5_5_278, List.forall_mem_cons.2 ⟨subd5_5_279, List.forall_mem_cons.2 ⟨subd5_5_280, List.forall_mem_cons.2 ⟨subd5_5_281, List.forall_mem_cons.2 ⟨subd5_5_282, List.forall_mem_cons.2 ⟨subd5_5_283, List.forall_mem_cons.2 ⟨subd5_5_284, List.forall_mem_cons.2 ⟨subd5_5_285, List.forall_mem_cons.2 ⟨subd5_5_286, List.forall_mem_cons.2 ⟨subd5_5_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_288 : subd5_5 [0, 2, -4] = true := by decide +kernel
theorem subd5_5_289 : subd5_5 [0, 2, -3] = true := by decide +kernel
theorem subd5_5_290 : subd5_5 [0, 2, -2] = true := by decide +kernel
theorem subd5_5_291 : subd5_5 [0, 2, -1] = true := by decide +kernel
theorem subd5_5_292 : subd5_5 [0, 2, 0] = true := by decide +kernel
theorem subd5_5_293 : subd5_5 [0, 2, 1] = true := by decide +kernel
theorem subd5_5_294 : subd5_5 [0, 2, 2] = true := by decide +kernel
theorem subd5_5_295 : subd5_5 [0, 2, 3] = true := by decide +kernel
theorem subd5_5_296 : subd5_5 [0, 2, 4] = true := by decide +kernel
theorem subd5_5_297 : subd5_5 [0, 2, 5] = true := by decide +kernel
theorem subd5_5_298 : subd5_5 [0, 2, 6] = true := by decide +kernel
theorem subd5_5_299 : subd5_5 [0, 2, 7] = true := by decide +kernel
theorem subd5_5_300 : subd5_5 [0, 2, 8] = true := by decide +kernel
theorem subd5_5_301 : subd5_5 [0, 3, -6] = true := by decide +kernel
theorem subd5_5_302 : subd5_5 [0, 3, -5] = true := by decide +kernel
theorem subd5_5_303 : subd5_5 [0, 3, -4] = true := by decide +kernel
theorem subd5_5_304 : subd5_5 [0, 3, -3] = true := by decide +kernel
theorem subd5_5_305 : subd5_5 [0, 3, -2] = true := by decide +kernel
theorem subd5_5_306 : subd5_5 [0, 3, -1] = true := by decide +kernel
theorem subd5_5_307 : subd5_5 [0, 3, 0] = true := by decide +kernel
theorem subd5_5_308 : subd5_5 [0, 3, 1] = true := by decide +kernel
theorem subd5_5_309 : subd5_5 [0, 3, 2] = true := by decide +kernel
theorem subd5_5_310 : subd5_5 [0, 3, 3] = true := by decide +kernel
theorem subd5_5_311 : subd5_5 [0, 3, 4] = true := by decide +kernel
theorem subd5_5_312 : subd5_5 [0, 3, 5] = true := by decide +kernel
theorem subd5_5_313 : subd5_5 [0, 3, 6] = true := by decide +kernel
theorem subd5_5_314 : subd5_5 [0, 3, 7] = true := by decide +kernel
theorem subd5_5_315 : subd5_5 [0, 3, 8] = true := by decide +kernel
theorem subd5_5_316 : subd5_5 [0, 4] = true := by decide +kernel
theorem subd5_5_317 : subd5_5 [1, -5] = true := by decide +kernel
theorem subd5_5_318 : subd5_5 [1, -4] = true := by decide +kernel
theorem subd5_5_319 : subd5_5 [1, -3] = true := by decide +kernel
theorem sbd5_5_9 : ∀ q ∈ blkd5_5_9, subd5_5 q = true := by
  unfold blkd5_5_9
  exact List.forall_mem_cons.2 ⟨subd5_5_288, List.forall_mem_cons.2 ⟨subd5_5_289, List.forall_mem_cons.2 ⟨subd5_5_290, List.forall_mem_cons.2 ⟨subd5_5_291, List.forall_mem_cons.2 ⟨subd5_5_292, List.forall_mem_cons.2 ⟨subd5_5_293, List.forall_mem_cons.2 ⟨subd5_5_294, List.forall_mem_cons.2 ⟨subd5_5_295, List.forall_mem_cons.2 ⟨subd5_5_296, List.forall_mem_cons.2 ⟨subd5_5_297, List.forall_mem_cons.2 ⟨subd5_5_298, List.forall_mem_cons.2 ⟨subd5_5_299, List.forall_mem_cons.2 ⟨subd5_5_300, List.forall_mem_cons.2 ⟨subd5_5_301, List.forall_mem_cons.2 ⟨subd5_5_302, List.forall_mem_cons.2 ⟨subd5_5_303, List.forall_mem_cons.2 ⟨subd5_5_304, List.forall_mem_cons.2 ⟨subd5_5_305, List.forall_mem_cons.2 ⟨subd5_5_306, List.forall_mem_cons.2 ⟨subd5_5_307, List.forall_mem_cons.2 ⟨subd5_5_308, List.forall_mem_cons.2 ⟨subd5_5_309, List.forall_mem_cons.2 ⟨subd5_5_310, List.forall_mem_cons.2 ⟨subd5_5_311, List.forall_mem_cons.2 ⟨subd5_5_312, List.forall_mem_cons.2 ⟨subd5_5_313, List.forall_mem_cons.2 ⟨subd5_5_314, List.forall_mem_cons.2 ⟨subd5_5_315, List.forall_mem_cons.2 ⟨subd5_5_316, List.forall_mem_cons.2 ⟨subd5_5_317, List.forall_mem_cons.2 ⟨subd5_5_318, List.forall_mem_cons.2 ⟨subd5_5_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_320 : subd5_5 [1, -2, -8] = true := by decide +kernel
theorem subd5_5_321 : subd5_5 [1, -2, -7] = true := by decide +kernel
theorem subd5_5_322 : subd5_5 [1, -2, -6] = true := by decide +kernel
theorem subd5_5_323 : subd5_5 [1, -2, -5] = true := by decide +kernel
theorem subd5_5_324 : subd5_5 [1, -2, -4] = true := by decide +kernel
theorem subd5_5_325 : subd5_5 [1, -2, -3] = true := by decide +kernel
theorem subd5_5_326 : subd5_5 [1, -2, -2] = true := by decide +kernel
theorem subd5_5_327 : subd5_5 [1, -2, -1] = true := by decide +kernel
theorem subd5_5_328 : subd5_5 [1, -2, 0] = true := by decide +kernel
theorem subd5_5_329 : subd5_5 [1, -2, 1] = true := by decide +kernel
theorem subd5_5_330 : subd5_5 [1, -2, 2] = true := by decide +kernel
theorem subd5_5_331 : subd5_5 [1, -2, 3] = true := by decide +kernel
theorem subd5_5_332 : subd5_5 [1, -2, 4] = true := by decide +kernel
theorem subd5_5_333 : subd5_5 [1, -2, 5] = true := by decide +kernel
theorem subd5_5_334 : subd5_5 [1, -2, 6] = true := by decide +kernel
theorem subd5_5_335 : subd5_5 [1, -1, -9] = true := by decide +kernel
theorem subd5_5_336 : subd5_5 [1, -1, -8] = true := by decide +kernel
theorem subd5_5_337 : subd5_5 [1, -1, -7] = true := by decide +kernel
theorem subd5_5_338 : subd5_5 [1, -1, -6] = true := by decide +kernel
theorem subd5_5_339 : subd5_5 [1, -1, -5] = true := by decide +kernel
theorem subd5_5_340 : subd5_5 [1, -1, -4] = true := by decide +kernel
theorem subd5_5_341 : subd5_5 [1, -1, -3] = true := by decide +kernel
theorem subd5_5_342 : subd5_5 [1, -1, -2] = true := by decide +kernel
theorem subd5_5_343 : subd5_5 [1, -1, -1] = true := by decide +kernel
theorem subd5_5_344 : subd5_5 [1, -1, 0] = true := by decide +kernel
theorem subd5_5_345 : subd5_5 [1, -1, 1] = true := by decide +kernel
theorem subd5_5_346 : subd5_5 [1, -1, 2] = true := by decide +kernel
theorem subd5_5_347 : subd5_5 [1, -1, 3] = true := by decide +kernel
theorem subd5_5_348 : subd5_5 [1, -1, 4] = true := by decide +kernel
theorem subd5_5_349 : subd5_5 [1, -1, 5] = true := by decide +kernel
theorem subd5_5_350 : subd5_5 [1, -1, 6] = true := by decide +kernel
theorem subd5_5_351 : subd5_5 [1, -1, 7] = true := by decide +kernel
theorem sbd5_5_10 : ∀ q ∈ blkd5_5_10, subd5_5 q = true := by
  unfold blkd5_5_10
  exact List.forall_mem_cons.2 ⟨subd5_5_320, List.forall_mem_cons.2 ⟨subd5_5_321, List.forall_mem_cons.2 ⟨subd5_5_322, List.forall_mem_cons.2 ⟨subd5_5_323, List.forall_mem_cons.2 ⟨subd5_5_324, List.forall_mem_cons.2 ⟨subd5_5_325, List.forall_mem_cons.2 ⟨subd5_5_326, List.forall_mem_cons.2 ⟨subd5_5_327, List.forall_mem_cons.2 ⟨subd5_5_328, List.forall_mem_cons.2 ⟨subd5_5_329, List.forall_mem_cons.2 ⟨subd5_5_330, List.forall_mem_cons.2 ⟨subd5_5_331, List.forall_mem_cons.2 ⟨subd5_5_332, List.forall_mem_cons.2 ⟨subd5_5_333, List.forall_mem_cons.2 ⟨subd5_5_334, List.forall_mem_cons.2 ⟨subd5_5_335, List.forall_mem_cons.2 ⟨subd5_5_336, List.forall_mem_cons.2 ⟨subd5_5_337, List.forall_mem_cons.2 ⟨subd5_5_338, List.forall_mem_cons.2 ⟨subd5_5_339, List.forall_mem_cons.2 ⟨subd5_5_340, List.forall_mem_cons.2 ⟨subd5_5_341, List.forall_mem_cons.2 ⟨subd5_5_342, List.forall_mem_cons.2 ⟨subd5_5_343, List.forall_mem_cons.2 ⟨subd5_5_344, List.forall_mem_cons.2 ⟨subd5_5_345, List.forall_mem_cons.2 ⟨subd5_5_346, List.forall_mem_cons.2 ⟨subd5_5_347, List.forall_mem_cons.2 ⟨subd5_5_348, List.forall_mem_cons.2 ⟨subd5_5_349, List.forall_mem_cons.2 ⟨subd5_5_350, List.forall_mem_cons.2 ⟨subd5_5_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_352 : subd5_5 [1, 0, -9] = true := by decide +kernel
theorem subd5_5_353 : subd5_5 [1, 0, -8] = true := by decide +kernel
theorem subd5_5_354 : subd5_5 [1, 0, -7] = true := by decide +kernel
theorem subd5_5_355 : subd5_5 [1, 0, -6] = true := by decide +kernel
theorem subd5_5_356 : subd5_5 [1, 0, -5] = true := by decide +kernel
theorem subd5_5_357 : subd5_5 [1, 0, -4] = true := by decide +kernel
theorem subd5_5_358 : subd5_5 [1, 0, -3] = true := by decide +kernel
theorem subd5_5_359 : subd5_5 [1, 0, -2] = true := by decide +kernel
theorem subd5_5_360 : subd5_5 [1, 0, -1] = true := by decide +kernel
theorem subd5_5_361 : subd5_5 [1, 0, 0] = true := by decide +kernel
theorem subd5_5_362 : subd5_5 [1, 0, 1] = true := by decide +kernel
theorem subd5_5_363 : subd5_5 [1, 0, 2] = true := by decide +kernel
theorem subd5_5_364 : subd5_5 [1, 0, 3] = true := by decide +kernel
theorem subd5_5_365 : subd5_5 [1, 0, 4] = true := by decide +kernel
theorem subd5_5_366 : subd5_5 [1, 0, 5] = true := by decide +kernel
theorem subd5_5_367 : subd5_5 [1, 0, 6] = true := by decide +kernel
theorem subd5_5_368 : subd5_5 [1, 0, 7] = true := by decide +kernel
theorem subd5_5_369 : subd5_5 [1, 0, 8] = true := by decide +kernel
theorem subd5_5_370 : subd5_5 [1, 1, -8] = true := by decide +kernel
theorem subd5_5_371 : subd5_5 [1, 1, -7] = true := by decide +kernel
theorem subd5_5_372 : subd5_5 [1, 1, -6] = true := by decide +kernel
theorem subd5_5_373 : subd5_5 [1, 1, -5] = true := by decide +kernel
theorem subd5_5_374 : subd5_5 [1, 1, -4] = true := by decide +kernel
theorem subd5_5_375 : subd5_5 [1, 1, -3] = true := by decide +kernel
theorem subd5_5_376 : subd5_5 [1, 1, -2] = true := by decide +kernel
theorem subd5_5_377 : subd5_5 [1, 1, -1] = true := by decide +kernel
theorem subd5_5_378 : subd5_5 [1, 1, 0] = true := by decide +kernel
theorem subd5_5_379 : subd5_5 [1, 1, 1] = true := by decide +kernel
theorem subd5_5_380 : subd5_5 [1, 1, 2] = true := by decide +kernel
theorem subd5_5_381 : subd5_5 [1, 1, 3] = true := by decide +kernel
theorem subd5_5_382 : subd5_5 [1, 1, 4] = true := by decide +kernel
theorem subd5_5_383 : subd5_5 [1, 1, 5] = true := by decide +kernel
theorem sbd5_5_11 : ∀ q ∈ blkd5_5_11, subd5_5 q = true := by
  unfold blkd5_5_11
  exact List.forall_mem_cons.2 ⟨subd5_5_352, List.forall_mem_cons.2 ⟨subd5_5_353, List.forall_mem_cons.2 ⟨subd5_5_354, List.forall_mem_cons.2 ⟨subd5_5_355, List.forall_mem_cons.2 ⟨subd5_5_356, List.forall_mem_cons.2 ⟨subd5_5_357, List.forall_mem_cons.2 ⟨subd5_5_358, List.forall_mem_cons.2 ⟨subd5_5_359, List.forall_mem_cons.2 ⟨subd5_5_360, List.forall_mem_cons.2 ⟨subd5_5_361, List.forall_mem_cons.2 ⟨subd5_5_362, List.forall_mem_cons.2 ⟨subd5_5_363, List.forall_mem_cons.2 ⟨subd5_5_364, List.forall_mem_cons.2 ⟨subd5_5_365, List.forall_mem_cons.2 ⟨subd5_5_366, List.forall_mem_cons.2 ⟨subd5_5_367, List.forall_mem_cons.2 ⟨subd5_5_368, List.forall_mem_cons.2 ⟨subd5_5_369, List.forall_mem_cons.2 ⟨subd5_5_370, List.forall_mem_cons.2 ⟨subd5_5_371, List.forall_mem_cons.2 ⟨subd5_5_372, List.forall_mem_cons.2 ⟨subd5_5_373, List.forall_mem_cons.2 ⟨subd5_5_374, List.forall_mem_cons.2 ⟨subd5_5_375, List.forall_mem_cons.2 ⟨subd5_5_376, List.forall_mem_cons.2 ⟨subd5_5_377, List.forall_mem_cons.2 ⟨subd5_5_378, List.forall_mem_cons.2 ⟨subd5_5_379, List.forall_mem_cons.2 ⟨subd5_5_380, List.forall_mem_cons.2 ⟨subd5_5_381, List.forall_mem_cons.2 ⟨subd5_5_382, List.forall_mem_cons.2 ⟨subd5_5_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_384 : subd5_5 [1, 1, 6] = true := by decide +kernel
theorem subd5_5_385 : subd5_5 [1, 1, 7] = true := by decide +kernel
theorem subd5_5_386 : subd5_5 [1, 1, 8] = true := by decide +kernel
theorem subd5_5_387 : subd5_5 [1, 1, 9] = true := by decide +kernel
theorem subd5_5_388 : subd5_5 [1, 2, -7] = true := by decide +kernel
theorem subd5_5_389 : subd5_5 [1, 2, -6] = true := by decide +kernel
theorem subd5_5_390 : subd5_5 [1, 2, -5] = true := by decide +kernel
theorem subd5_5_391 : subd5_5 [1, 2, -4] = true := by decide +kernel
theorem subd5_5_392 : subd5_5 [1, 2, -3] = true := by decide +kernel
theorem subd5_5_393 : subd5_5 [1, 2, -2] = true := by decide +kernel
theorem subd5_5_394 : subd5_5 [1, 2, -1] = true := by decide +kernel
theorem subd5_5_395 : subd5_5 [1, 2, 0] = true := by decide +kernel
theorem subd5_5_396 : subd5_5 [1, 2, 1] = true := by decide +kernel
theorem subd5_5_397 : subd5_5 [1, 2, 2] = true := by decide +kernel
theorem subd5_5_398 : subd5_5 [1, 2, 3] = true := by decide +kernel
theorem subd5_5_399 : subd5_5 [1, 2, 4] = true := by decide +kernel
theorem subd5_5_400 : subd5_5 [1, 2, 5] = true := by decide +kernel
theorem subd5_5_401 : subd5_5 [1, 2, 6] = true := by decide +kernel
theorem subd5_5_402 : subd5_5 [1, 2, 7] = true := by decide +kernel
theorem subd5_5_403 : subd5_5 [1, 2, 8] = true := by decide +kernel
theorem subd5_5_404 : subd5_5 [1, 2, 9] = true := by decide +kernel
theorem subd5_5_405 : subd5_5 [1, 3, -6] = true := by decide +kernel
theorem subd5_5_406 : subd5_5 [1, 3, -5] = true := by decide +kernel
theorem subd5_5_407 : subd5_5 [1, 3, -4] = true := by decide +kernel
theorem subd5_5_408 : subd5_5 [1, 3, -3] = true := by decide +kernel
theorem subd5_5_409 : subd5_5 [1, 3, -2] = true := by decide +kernel
theorem subd5_5_410 : subd5_5 [1, 3, -1] = true := by decide +kernel
theorem subd5_5_411 : subd5_5 [1, 3, 0] = true := by decide +kernel
theorem subd5_5_412 : subd5_5 [1, 3, 1] = true := by decide +kernel
theorem subd5_5_413 : subd5_5 [1, 3, 2] = true := by decide +kernel
theorem subd5_5_414 : subd5_5 [1, 3, 3] = true := by decide +kernel
theorem subd5_5_415 : subd5_5 [1, 3, 4] = true := by decide +kernel
theorem sbd5_5_12 : ∀ q ∈ blkd5_5_12, subd5_5 q = true := by
  unfold blkd5_5_12
  exact List.forall_mem_cons.2 ⟨subd5_5_384, List.forall_mem_cons.2 ⟨subd5_5_385, List.forall_mem_cons.2 ⟨subd5_5_386, List.forall_mem_cons.2 ⟨subd5_5_387, List.forall_mem_cons.2 ⟨subd5_5_388, List.forall_mem_cons.2 ⟨subd5_5_389, List.forall_mem_cons.2 ⟨subd5_5_390, List.forall_mem_cons.2 ⟨subd5_5_391, List.forall_mem_cons.2 ⟨subd5_5_392, List.forall_mem_cons.2 ⟨subd5_5_393, List.forall_mem_cons.2 ⟨subd5_5_394, List.forall_mem_cons.2 ⟨subd5_5_395, List.forall_mem_cons.2 ⟨subd5_5_396, List.forall_mem_cons.2 ⟨subd5_5_397, List.forall_mem_cons.2 ⟨subd5_5_398, List.forall_mem_cons.2 ⟨subd5_5_399, List.forall_mem_cons.2 ⟨subd5_5_400, List.forall_mem_cons.2 ⟨subd5_5_401, List.forall_mem_cons.2 ⟨subd5_5_402, List.forall_mem_cons.2 ⟨subd5_5_403, List.forall_mem_cons.2 ⟨subd5_5_404, List.forall_mem_cons.2 ⟨subd5_5_405, List.forall_mem_cons.2 ⟨subd5_5_406, List.forall_mem_cons.2 ⟨subd5_5_407, List.forall_mem_cons.2 ⟨subd5_5_408, List.forall_mem_cons.2 ⟨subd5_5_409, List.forall_mem_cons.2 ⟨subd5_5_410, List.forall_mem_cons.2 ⟨subd5_5_411, List.forall_mem_cons.2 ⟨subd5_5_412, List.forall_mem_cons.2 ⟨subd5_5_413, List.forall_mem_cons.2 ⟨subd5_5_414, List.forall_mem_cons.2 ⟨subd5_5_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
