import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd6_5 : ldCheck G d6_5.U d6_5.ms ldd6_5 = true := by decide +kernel
theorem pre_okd6_5 : subPre G cell6 d6_5 = true := by decide +kernel
theorem subd6_5_0 : subd6_5 [-4, -3] = true := by decide +kernel
theorem subd6_5_1 : subd6_5 [-4, -2] = true := by decide +kernel
theorem subd6_5_2 : subd6_5 [-4, -1] = true := by decide +kernel
theorem subd6_5_3 : subd6_5 [-4, 0] = true := by decide +kernel
theorem subd6_5_4 : subd6_5 [-4, 1] = true := by decide +kernel
theorem subd6_5_5 : subd6_5 [-4, 2] = true := by decide +kernel
theorem subd6_5_6 : subd6_5 [-4, 3] = true := by decide +kernel
theorem subd6_5_7 : subd6_5 [-3, -4] = true := by decide +kernel
theorem subd6_5_8 : subd6_5 [-3, -3] = true := by decide +kernel
theorem subd6_5_9 : subd6_5 [-3, -2] = true := by decide +kernel
theorem subd6_5_10 : subd6_5 [-3, -1] = true := by decide +kernel
theorem subd6_5_11 : subd6_5 [-3, 0] = true := by decide +kernel
theorem subd6_5_12 : subd6_5 [-3, 1] = true := by decide +kernel
theorem subd6_5_13 : subd6_5 [-3, 2] = true := by decide +kernel
theorem subd6_5_14 : subd6_5 [-3, 3] = true := by decide +kernel
theorem subd6_5_15 : subd6_5 [-3, 4] = true := by decide +kernel
theorem subd6_5_16 : subd6_5 [-2, -5] = true := by decide +kernel
theorem subd6_5_17 : subd6_5 [-2, -4] = true := by decide +kernel
theorem subd6_5_18 : subd6_5 [-2, -3] = true := by decide +kernel
theorem subd6_5_19 : subd6_5 [-2, -2] = true := by decide +kernel
theorem subd6_5_20 : subd6_5 [-2, -1] = true := by decide +kernel
theorem subd6_5_21 : subd6_5 [-2, 0] = true := by decide +kernel
theorem subd6_5_22 : subd6_5 [-2, 1] = true := by decide +kernel
theorem subd6_5_23 : subd6_5 [-2, 2] = true := by decide +kernel
theorem subd6_5_24 : subd6_5 [-2, 3] = true := by decide +kernel
theorem subd6_5_25 : subd6_5 [-2, 4] = true := by decide +kernel
theorem subd6_5_26 : subd6_5 [-2, 5] = true := by decide +kernel
theorem subd6_5_27 : subd6_5 [-1, -6] = true := by decide +kernel
theorem subd6_5_28 : subd6_5 [-1, -5] = true := by decide +kernel
theorem subd6_5_29 : subd6_5 [-1, -4] = true := by decide +kernel
theorem subd6_5_30 : subd6_5 [-1, -3] = true := by decide +kernel
theorem subd6_5_31 : subd6_5 [-1, -2] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_cons.2 ⟨subd6_5_1, List.forall_mem_cons.2 ⟨subd6_5_2, List.forall_mem_cons.2 ⟨subd6_5_3, List.forall_mem_cons.2 ⟨subd6_5_4, List.forall_mem_cons.2 ⟨subd6_5_5, List.forall_mem_cons.2 ⟨subd6_5_6, List.forall_mem_cons.2 ⟨subd6_5_7, List.forall_mem_cons.2 ⟨subd6_5_8, List.forall_mem_cons.2 ⟨subd6_5_9, List.forall_mem_cons.2 ⟨subd6_5_10, List.forall_mem_cons.2 ⟨subd6_5_11, List.forall_mem_cons.2 ⟨subd6_5_12, List.forall_mem_cons.2 ⟨subd6_5_13, List.forall_mem_cons.2 ⟨subd6_5_14, List.forall_mem_cons.2 ⟨subd6_5_15, List.forall_mem_cons.2 ⟨subd6_5_16, List.forall_mem_cons.2 ⟨subd6_5_17, List.forall_mem_cons.2 ⟨subd6_5_18, List.forall_mem_cons.2 ⟨subd6_5_19, List.forall_mem_cons.2 ⟨subd6_5_20, List.forall_mem_cons.2 ⟨subd6_5_21, List.forall_mem_cons.2 ⟨subd6_5_22, List.forall_mem_cons.2 ⟨subd6_5_23, List.forall_mem_cons.2 ⟨subd6_5_24, List.forall_mem_cons.2 ⟨subd6_5_25, List.forall_mem_cons.2 ⟨subd6_5_26, List.forall_mem_cons.2 ⟨subd6_5_27, List.forall_mem_cons.2 ⟨subd6_5_28, List.forall_mem_cons.2 ⟨subd6_5_29, List.forall_mem_cons.2 ⟨subd6_5_30, List.forall_mem_cons.2 ⟨subd6_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_5_32 : subd6_5 [-1, -1, -6] = true := by decide +kernel
theorem subd6_5_33 : subd6_5 [-1, -1, -5] = true := by decide +kernel
theorem subd6_5_34 : subd6_5 [-1, -1, -4] = true := by decide +kernel
theorem subd6_5_35 : subd6_5 [-1, -1, -3] = true := by decide +kernel
theorem subd6_5_36 : subd6_5 [-1, -1, -2] = true := by decide +kernel
theorem subd6_5_37 : subd6_5 [-1, -1, -1] = true := by decide +kernel
theorem subd6_5_38 : subd6_5 [-1, -1, 0] = true := by decide +kernel
theorem subd6_5_39 : subd6_5 [-1, -1, 1] = true := by decide +kernel
theorem subd6_5_40 : subd6_5 [-1, -1, 2] = true := by decide +kernel
theorem subd6_5_41 : subd6_5 [-1, -1, 3] = true := by decide +kernel
theorem subd6_5_42 : subd6_5 [-1, -1, 4] = true := by decide +kernel
theorem subd6_5_43 : subd6_5 [-1, -1, 5] = true := by decide +kernel
theorem subd6_5_44 : subd6_5 [-1, -1, 6] = true := by decide +kernel
theorem subd6_5_45 : subd6_5 [-1, 0, -7] = true := by decide +kernel
theorem subd6_5_46 : subd6_5 [-1, 0, -6] = true := by decide +kernel
theorem subd6_5_47 : subd6_5 [-1, 0, -5] = true := by decide +kernel
theorem subd6_5_48 : subd6_5 [-1, 0, -4] = true := by decide +kernel
theorem subd6_5_49 : subd6_5 [-1, 0, -3] = true := by decide +kernel
theorem subd6_5_50 : subd6_5 [-1, 0, -2] = true := by decide +kernel
theorem subd6_5_51 : subd6_5 [-1, 0, -1] = true := by decide +kernel
theorem subd6_5_52 : subd6_5 [-1, 0, 0] = true := by decide +kernel
theorem subd6_5_53 : subd6_5 [-1, 0, 1] = true := by decide +kernel
theorem subd6_5_54 : subd6_5 [-1, 0, 2] = true := by decide +kernel
theorem subd6_5_55 : subd6_5 [-1, 0, 3] = true := by decide +kernel
theorem subd6_5_56 : subd6_5 [-1, 0, 4] = true := by decide +kernel
theorem subd6_5_57 : subd6_5 [-1, 0, 5] = true := by decide +kernel
theorem subd6_5_58 : subd6_5 [-1, 0, 6] = true := by decide +kernel
theorem subd6_5_59 : subd6_5 [-1, 1, -7] = true := by decide +kernel
theorem subd6_5_60 : subd6_5 [-1, 1, -6] = true := by decide +kernel
theorem subd6_5_61 : subd6_5 [-1, 1, -5] = true := by decide +kernel
theorem subd6_5_62 : subd6_5 [-1, 1, -4] = true := by decide +kernel
theorem subd6_5_63 : subd6_5 [-1, 1, -3] = true := by decide +kernel
theorem sbd6_5_1 : ∀ q ∈ blkd6_5_1, subd6_5 q = true := by
  unfold blkd6_5_1
  exact List.forall_mem_cons.2 ⟨subd6_5_32, List.forall_mem_cons.2 ⟨subd6_5_33, List.forall_mem_cons.2 ⟨subd6_5_34, List.forall_mem_cons.2 ⟨subd6_5_35, List.forall_mem_cons.2 ⟨subd6_5_36, List.forall_mem_cons.2 ⟨subd6_5_37, List.forall_mem_cons.2 ⟨subd6_5_38, List.forall_mem_cons.2 ⟨subd6_5_39, List.forall_mem_cons.2 ⟨subd6_5_40, List.forall_mem_cons.2 ⟨subd6_5_41, List.forall_mem_cons.2 ⟨subd6_5_42, List.forall_mem_cons.2 ⟨subd6_5_43, List.forall_mem_cons.2 ⟨subd6_5_44, List.forall_mem_cons.2 ⟨subd6_5_45, List.forall_mem_cons.2 ⟨subd6_5_46, List.forall_mem_cons.2 ⟨subd6_5_47, List.forall_mem_cons.2 ⟨subd6_5_48, List.forall_mem_cons.2 ⟨subd6_5_49, List.forall_mem_cons.2 ⟨subd6_5_50, List.forall_mem_cons.2 ⟨subd6_5_51, List.forall_mem_cons.2 ⟨subd6_5_52, List.forall_mem_cons.2 ⟨subd6_5_53, List.forall_mem_cons.2 ⟨subd6_5_54, List.forall_mem_cons.2 ⟨subd6_5_55, List.forall_mem_cons.2 ⟨subd6_5_56, List.forall_mem_cons.2 ⟨subd6_5_57, List.forall_mem_cons.2 ⟨subd6_5_58, List.forall_mem_cons.2 ⟨subd6_5_59, List.forall_mem_cons.2 ⟨subd6_5_60, List.forall_mem_cons.2 ⟨subd6_5_61, List.forall_mem_cons.2 ⟨subd6_5_62, List.forall_mem_cons.2 ⟨subd6_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_5_64 : subd6_5 [-1, 1, -2] = true := by decide +kernel
theorem subd6_5_65 : subd6_5 [-1, 1, -1] = true := by decide +kernel
theorem subd6_5_66 : subd6_5 [-1, 1, 0] = true := by decide +kernel
theorem subd6_5_67 : subd6_5 [-1, 1, 1] = true := by decide +kernel
theorem subd6_5_68 : subd6_5 [-1, 1, 2] = true := by decide +kernel
theorem subd6_5_69 : subd6_5 [-1, 1, 3] = true := by decide +kernel
theorem subd6_5_70 : subd6_5 [-1, 1, 4] = true := by decide +kernel
theorem subd6_5_71 : subd6_5 [-1, 1, 5] = true := by decide +kernel
theorem subd6_5_72 : subd6_5 [-1, 1, 6] = true := by decide +kernel
theorem subd6_5_73 : subd6_5 [-1, 2] = true := by decide +kernel
theorem subd6_5_74 : subd6_5 [-1, 3] = true := by decide +kernel
theorem subd6_5_75 : subd6_5 [-1, 4] = true := by decide +kernel
theorem subd6_5_76 : subd6_5 [-1, 5] = true := by decide +kernel
theorem subd6_5_77 : subd6_5 [0, -6] = true := by decide +kernel
theorem subd6_5_78 : subd6_5 [0, -5] = true := by decide +kernel
theorem subd6_5_79 : subd6_5 [0, -4] = true := by decide +kernel
theorem subd6_5_80 : subd6_5 [0, -3] = true := by decide +kernel
theorem subd6_5_81 : subd6_5 [0, -2] = true := by decide +kernel
theorem subd6_5_82 : subd6_5 [0, -1, -7] = true := by decide +kernel
theorem subd6_5_83 : subd6_5 [0, -1, -6] = true := by decide +kernel
theorem subd6_5_84 : subd6_5 [0, -1, -5] = true := by decide +kernel
theorem subd6_5_85 : subd6_5 [0, -1, -4] = true := by decide +kernel
theorem subd6_5_86 : subd6_5 [0, -1, -3] = true := by decide +kernel
theorem subd6_5_87 : subd6_5 [0, -1, -2] = true := by decide +kernel
theorem subd6_5_88 : subd6_5 [0, -1, -1] = true := by decide +kernel
theorem subd6_5_89 : subd6_5 [0, -1, 0] = true := by decide +kernel
theorem subd6_5_90 : subd6_5 [0, -1, 1] = true := by decide +kernel
theorem subd6_5_91 : subd6_5 [0, -1, 2] = true := by decide +kernel
theorem subd6_5_92 : subd6_5 [0, -1, 3] = true := by decide +kernel
theorem subd6_5_93 : subd6_5 [0, -1, 4] = true := by decide +kernel
theorem subd6_5_94 : subd6_5 [0, -1, 5] = true := by decide +kernel
theorem subd6_5_95 : subd6_5 [0, -1, 6] = true := by decide +kernel
theorem sbd6_5_2 : ∀ q ∈ blkd6_5_2, subd6_5 q = true := by
  unfold blkd6_5_2
  exact List.forall_mem_cons.2 ⟨subd6_5_64, List.forall_mem_cons.2 ⟨subd6_5_65, List.forall_mem_cons.2 ⟨subd6_5_66, List.forall_mem_cons.2 ⟨subd6_5_67, List.forall_mem_cons.2 ⟨subd6_5_68, List.forall_mem_cons.2 ⟨subd6_5_69, List.forall_mem_cons.2 ⟨subd6_5_70, List.forall_mem_cons.2 ⟨subd6_5_71, List.forall_mem_cons.2 ⟨subd6_5_72, List.forall_mem_cons.2 ⟨subd6_5_73, List.forall_mem_cons.2 ⟨subd6_5_74, List.forall_mem_cons.2 ⟨subd6_5_75, List.forall_mem_cons.2 ⟨subd6_5_76, List.forall_mem_cons.2 ⟨subd6_5_77, List.forall_mem_cons.2 ⟨subd6_5_78, List.forall_mem_cons.2 ⟨subd6_5_79, List.forall_mem_cons.2 ⟨subd6_5_80, List.forall_mem_cons.2 ⟨subd6_5_81, List.forall_mem_cons.2 ⟨subd6_5_82, List.forall_mem_cons.2 ⟨subd6_5_83, List.forall_mem_cons.2 ⟨subd6_5_84, List.forall_mem_cons.2 ⟨subd6_5_85, List.forall_mem_cons.2 ⟨subd6_5_86, List.forall_mem_cons.2 ⟨subd6_5_87, List.forall_mem_cons.2 ⟨subd6_5_88, List.forall_mem_cons.2 ⟨subd6_5_89, List.forall_mem_cons.2 ⟨subd6_5_90, List.forall_mem_cons.2 ⟨subd6_5_91, List.forall_mem_cons.2 ⟨subd6_5_92, List.forall_mem_cons.2 ⟨subd6_5_93, List.forall_mem_cons.2 ⟨subd6_5_94, List.forall_mem_cons.2 ⟨subd6_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_5_96 : subd6_5 [0, 0, -7] = true := by decide +kernel
theorem subd6_5_97 : subd6_5 [0, 0, -6] = true := by decide +kernel
theorem subd6_5_98 : subd6_5 [0, 0, -5] = true := by decide +kernel
theorem subd6_5_99 : subd6_5 [0, 0, -4] = true := by decide +kernel
theorem subd6_5_100 : subd6_5 [0, 0, -3] = true := by decide +kernel
theorem subd6_5_101 : subd6_5 [0, 0, -2] = true := by decide +kernel
theorem subd6_5_102 : subd6_5 [0, 0, -1] = true := by decide +kernel
theorem subd6_5_103 : subd6_5 [0, 0, 0] = true := by decide +kernel
theorem subd6_5_104 : subd6_5 [0, 0, 1] = true := by decide +kernel
theorem subd6_5_105 : subd6_5 [0, 0, 2] = true := by decide +kernel
theorem subd6_5_106 : subd6_5 [0, 0, 3] = true := by decide +kernel
theorem subd6_5_107 : subd6_5 [0, 0, 4] = true := by decide +kernel
theorem subd6_5_108 : subd6_5 [0, 0, 5] = true := by decide +kernel
theorem subd6_5_109 : subd6_5 [0, 0, 6] = true := by decide +kernel
theorem subd6_5_110 : subd6_5 [0, 1, -7] = true := by decide +kernel
theorem subd6_5_111 : subd6_5 [0, 1, -6] = true := by decide +kernel
theorem subd6_5_112 : subd6_5 [0, 1, -5] = true := by decide +kernel
theorem subd6_5_113 : subd6_5 [0, 1, -4] = true := by decide +kernel
theorem subd6_5_114 : subd6_5 [0, 1, -3] = true := by decide +kernel
theorem subd6_5_115 : subd6_5 [0, 1, -2] = true := by decide +kernel
theorem subd6_5_116 : subd6_5 [0, 1, -1] = true := by decide +kernel
theorem subd6_5_117 : subd6_5 [0, 1, 0] = true := by decide +kernel
theorem subd6_5_118 : subd6_5 [0, 1, 1] = true := by decide +kernel
theorem subd6_5_119 : subd6_5 [0, 1, 2] = true := by decide +kernel
theorem subd6_5_120 : subd6_5 [0, 1, 3] = true := by decide +kernel
theorem subd6_5_121 : subd6_5 [0, 1, 4] = true := by decide +kernel
theorem subd6_5_122 : subd6_5 [0, 1, 5] = true := by decide +kernel
theorem subd6_5_123 : subd6_5 [0, 1, 6] = true := by decide +kernel
theorem subd6_5_124 : subd6_5 [0, 2] = true := by decide +kernel
theorem subd6_5_125 : subd6_5 [0, 3] = true := by decide +kernel
theorem subd6_5_126 : subd6_5 [0, 4] = true := by decide +kernel
theorem subd6_5_127 : subd6_5 [0, 5] = true := by decide +kernel
theorem sbd6_5_3 : ∀ q ∈ blkd6_5_3, subd6_5 q = true := by
  unfold blkd6_5_3
  exact List.forall_mem_cons.2 ⟨subd6_5_96, List.forall_mem_cons.2 ⟨subd6_5_97, List.forall_mem_cons.2 ⟨subd6_5_98, List.forall_mem_cons.2 ⟨subd6_5_99, List.forall_mem_cons.2 ⟨subd6_5_100, List.forall_mem_cons.2 ⟨subd6_5_101, List.forall_mem_cons.2 ⟨subd6_5_102, List.forall_mem_cons.2 ⟨subd6_5_103, List.forall_mem_cons.2 ⟨subd6_5_104, List.forall_mem_cons.2 ⟨subd6_5_105, List.forall_mem_cons.2 ⟨subd6_5_106, List.forall_mem_cons.2 ⟨subd6_5_107, List.forall_mem_cons.2 ⟨subd6_5_108, List.forall_mem_cons.2 ⟨subd6_5_109, List.forall_mem_cons.2 ⟨subd6_5_110, List.forall_mem_cons.2 ⟨subd6_5_111, List.forall_mem_cons.2 ⟨subd6_5_112, List.forall_mem_cons.2 ⟨subd6_5_113, List.forall_mem_cons.2 ⟨subd6_5_114, List.forall_mem_cons.2 ⟨subd6_5_115, List.forall_mem_cons.2 ⟨subd6_5_116, List.forall_mem_cons.2 ⟨subd6_5_117, List.forall_mem_cons.2 ⟨subd6_5_118, List.forall_mem_cons.2 ⟨subd6_5_119, List.forall_mem_cons.2 ⟨subd6_5_120, List.forall_mem_cons.2 ⟨subd6_5_121, List.forall_mem_cons.2 ⟨subd6_5_122, List.forall_mem_cons.2 ⟨subd6_5_123, List.forall_mem_cons.2 ⟨subd6_5_124, List.forall_mem_cons.2 ⟨subd6_5_125, List.forall_mem_cons.2 ⟨subd6_5_126, List.forall_mem_cons.2 ⟨subd6_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_5_128 : subd6_5 [1, -6] = true := by decide +kernel
theorem subd6_5_129 : subd6_5 [1, -5] = true := by decide +kernel
theorem subd6_5_130 : subd6_5 [1, -4] = true := by decide +kernel
theorem subd6_5_131 : subd6_5 [1, -3] = true := by decide +kernel
theorem subd6_5_132 : subd6_5 [1, -2] = true := by decide +kernel
theorem subd6_5_133 : subd6_5 [1, -1, -7] = true := by decide +kernel
theorem subd6_5_134 : subd6_5 [1, -1, -6] = true := by decide +kernel
theorem subd6_5_135 : subd6_5 [1, -1, -5] = true := by decide +kernel
theorem subd6_5_136 : subd6_5 [1, -1, -4] = true := by decide +kernel
theorem subd6_5_137 : subd6_5 [1, -1, -3] = true := by decide +kernel
theorem subd6_5_138 : subd6_5 [1, -1, -2] = true := by decide +kernel
theorem subd6_5_139 : subd6_5 [1, -1, -1] = true := by decide +kernel
theorem subd6_5_140 : subd6_5 [1, -1, 0] = true := by decide +kernel
theorem subd6_5_141 : subd6_5 [1, -1, 1] = true := by decide +kernel
theorem subd6_5_142 : subd6_5 [1, -1, 2] = true := by decide +kernel
theorem subd6_5_143 : subd6_5 [1, -1, 3] = true := by decide +kernel
theorem subd6_5_144 : subd6_5 [1, -1, 4] = true := by decide +kernel
theorem subd6_5_145 : subd6_5 [1, -1, 5] = true := by decide +kernel
theorem subd6_5_146 : subd6_5 [1, -1, 6] = true := by decide +kernel
theorem subd6_5_147 : subd6_5 [1, 0, -7] = true := by decide +kernel
theorem subd6_5_148 : subd6_5 [1, 0, -6] = true := by decide +kernel
theorem subd6_5_149 : subd6_5 [1, 0, -5] = true := by decide +kernel
theorem subd6_5_150 : subd6_5 [1, 0, -4] = true := by decide +kernel
theorem subd6_5_151 : subd6_5 [1, 0, -3] = true := by decide +kernel
theorem subd6_5_152 : subd6_5 [1, 0, -2] = true := by decide +kernel
theorem subd6_5_153 : subd6_5 [1, 0, -1] = true := by decide +kernel
theorem subd6_5_154 : subd6_5 [1, 0, 0] = true := by decide +kernel
theorem subd6_5_155 : subd6_5 [1, 0, 1] = true := by decide +kernel
theorem subd6_5_156 : subd6_5 [1, 0, 2] = true := by decide +kernel
theorem subd6_5_157 : subd6_5 [1, 0, 3] = true := by decide +kernel
theorem subd6_5_158 : subd6_5 [1, 0, 4] = true := by decide +kernel
theorem subd6_5_159 : subd6_5 [1, 0, 5] = true := by decide +kernel
theorem sbd6_5_4 : ∀ q ∈ blkd6_5_4, subd6_5 q = true := by
  unfold blkd6_5_4
  exact List.forall_mem_cons.2 ⟨subd6_5_128, List.forall_mem_cons.2 ⟨subd6_5_129, List.forall_mem_cons.2 ⟨subd6_5_130, List.forall_mem_cons.2 ⟨subd6_5_131, List.forall_mem_cons.2 ⟨subd6_5_132, List.forall_mem_cons.2 ⟨subd6_5_133, List.forall_mem_cons.2 ⟨subd6_5_134, List.forall_mem_cons.2 ⟨subd6_5_135, List.forall_mem_cons.2 ⟨subd6_5_136, List.forall_mem_cons.2 ⟨subd6_5_137, List.forall_mem_cons.2 ⟨subd6_5_138, List.forall_mem_cons.2 ⟨subd6_5_139, List.forall_mem_cons.2 ⟨subd6_5_140, List.forall_mem_cons.2 ⟨subd6_5_141, List.forall_mem_cons.2 ⟨subd6_5_142, List.forall_mem_cons.2 ⟨subd6_5_143, List.forall_mem_cons.2 ⟨subd6_5_144, List.forall_mem_cons.2 ⟨subd6_5_145, List.forall_mem_cons.2 ⟨subd6_5_146, List.forall_mem_cons.2 ⟨subd6_5_147, List.forall_mem_cons.2 ⟨subd6_5_148, List.forall_mem_cons.2 ⟨subd6_5_149, List.forall_mem_cons.2 ⟨subd6_5_150, List.forall_mem_cons.2 ⟨subd6_5_151, List.forall_mem_cons.2 ⟨subd6_5_152, List.forall_mem_cons.2 ⟨subd6_5_153, List.forall_mem_cons.2 ⟨subd6_5_154, List.forall_mem_cons.2 ⟨subd6_5_155, List.forall_mem_cons.2 ⟨subd6_5_156, List.forall_mem_cons.2 ⟨subd6_5_157, List.forall_mem_cons.2 ⟨subd6_5_158, List.forall_mem_cons.2 ⟨subd6_5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_5_160 : subd6_5 [1, 0, 6] = true := by decide +kernel
theorem subd6_5_161 : subd6_5 [1, 1, -7] = true := by decide +kernel
theorem subd6_5_162 : subd6_5 [1, 1, -6] = true := by decide +kernel
theorem subd6_5_163 : subd6_5 [1, 1, -5] = true := by decide +kernel
theorem subd6_5_164 : subd6_5 [1, 1, -4] = true := by decide +kernel
theorem subd6_5_165 : subd6_5 [1, 1, -3] = true := by decide +kernel
theorem subd6_5_166 : subd6_5 [1, 1, -2] = true := by decide +kernel
theorem subd6_5_167 : subd6_5 [1, 1, -1] = true := by decide +kernel
theorem subd6_5_168 : subd6_5 [1, 1, 0] = true := by decide +kernel
theorem subd6_5_169 : subd6_5 [1, 1, 1] = true := by decide +kernel
theorem subd6_5_170 : subd6_5 [1, 1, 2] = true := by decide +kernel
theorem subd6_5_171 : subd6_5 [1, 1, 3] = true := by decide +kernel
theorem subd6_5_172 : subd6_5 [1, 1, 4] = true := by decide +kernel
theorem subd6_5_173 : subd6_5 [1, 1, 5] = true := by decide +kernel
theorem subd6_5_174 : subd6_5 [1, 2] = true := by decide +kernel
theorem subd6_5_175 : subd6_5 [1, 3] = true := by decide +kernel
theorem subd6_5_176 : subd6_5 [1, 4] = true := by decide +kernel
theorem subd6_5_177 : subd6_5 [1, 5] = true := by decide +kernel
theorem subd6_5_178 : subd6_5 [2, -6] = true := by decide +kernel
theorem subd6_5_179 : subd6_5 [2, -5] = true := by decide +kernel
theorem subd6_5_180 : subd6_5 [2, -4] = true := by decide +kernel
theorem subd6_5_181 : subd6_5 [2, -3] = true := by decide +kernel
theorem subd6_5_182 : subd6_5 [2, -2] = true := by decide +kernel
theorem subd6_5_183 : subd6_5 [2, -1] = true := by decide +kernel
theorem subd6_5_184 : subd6_5 [2, 0] = true := by decide +kernel
theorem subd6_5_185 : subd6_5 [2, 1] = true := by decide +kernel
theorem subd6_5_186 : subd6_5 [2, 2] = true := by decide +kernel
theorem subd6_5_187 : subd6_5 [2, 3] = true := by decide +kernel
theorem subd6_5_188 : subd6_5 [2, 4] = true := by decide +kernel
theorem subd6_5_189 : subd6_5 [3, -5] = true := by decide +kernel
theorem subd6_5_190 : subd6_5 [3, -4] = true := by decide +kernel
theorem subd6_5_191 : subd6_5 [3, -3] = true := by decide +kernel
theorem sbd6_5_5 : ∀ q ∈ blkd6_5_5, subd6_5 q = true := by
  unfold blkd6_5_5
  exact List.forall_mem_cons.2 ⟨subd6_5_160, List.forall_mem_cons.2 ⟨subd6_5_161, List.forall_mem_cons.2 ⟨subd6_5_162, List.forall_mem_cons.2 ⟨subd6_5_163, List.forall_mem_cons.2 ⟨subd6_5_164, List.forall_mem_cons.2 ⟨subd6_5_165, List.forall_mem_cons.2 ⟨subd6_5_166, List.forall_mem_cons.2 ⟨subd6_5_167, List.forall_mem_cons.2 ⟨subd6_5_168, List.forall_mem_cons.2 ⟨subd6_5_169, List.forall_mem_cons.2 ⟨subd6_5_170, List.forall_mem_cons.2 ⟨subd6_5_171, List.forall_mem_cons.2 ⟨subd6_5_172, List.forall_mem_cons.2 ⟨subd6_5_173, List.forall_mem_cons.2 ⟨subd6_5_174, List.forall_mem_cons.2 ⟨subd6_5_175, List.forall_mem_cons.2 ⟨subd6_5_176, List.forall_mem_cons.2 ⟨subd6_5_177, List.forall_mem_cons.2 ⟨subd6_5_178, List.forall_mem_cons.2 ⟨subd6_5_179, List.forall_mem_cons.2 ⟨subd6_5_180, List.forall_mem_cons.2 ⟨subd6_5_181, List.forall_mem_cons.2 ⟨subd6_5_182, List.forall_mem_cons.2 ⟨subd6_5_183, List.forall_mem_cons.2 ⟨subd6_5_184, List.forall_mem_cons.2 ⟨subd6_5_185, List.forall_mem_cons.2 ⟨subd6_5_186, List.forall_mem_cons.2 ⟨subd6_5_187, List.forall_mem_cons.2 ⟨subd6_5_188, List.forall_mem_cons.2 ⟨subd6_5_189, List.forall_mem_cons.2 ⟨subd6_5_190, List.forall_mem_cons.2 ⟨subd6_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
