import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [-5, -3] = true := by decide +kernel
theorem subd13_1_1 : subd13_1 [-5, -2] = true := by decide +kernel
theorem subd13_1_2 : subd13_1 [-5, -1] = true := by decide +kernel
theorem subd13_1_3 : subd13_1 [-5, 0] = true := by decide +kernel
theorem subd13_1_4 : subd13_1 [-5, 1] = true := by decide +kernel
theorem subd13_1_5 : subd13_1 [-5, 2] = true := by decide +kernel
theorem subd13_1_6 : subd13_1 [-4, -4] = true := by decide +kernel
theorem subd13_1_7 : subd13_1 [-4, -3] = true := by decide +kernel
theorem subd13_1_8 : subd13_1 [-4, -2] = true := by decide +kernel
theorem subd13_1_9 : subd13_1 [-4, -1] = true := by decide +kernel
theorem subd13_1_10 : subd13_1 [-4, 0] = true := by decide +kernel
theorem subd13_1_11 : subd13_1 [-4, 1] = true := by decide +kernel
theorem subd13_1_12 : subd13_1 [-4, 2] = true := by decide +kernel
theorem subd13_1_13 : subd13_1 [-4, 3] = true := by decide +kernel
theorem subd13_1_14 : subd13_1 [-3, -5] = true := by decide +kernel
theorem subd13_1_15 : subd13_1 [-3, -4] = true := by decide +kernel
theorem subd13_1_16 : subd13_1 [-3, -3] = true := by decide +kernel
theorem subd13_1_17 : subd13_1 [-3, -2] = true := by decide +kernel
theorem subd13_1_18 : subd13_1 [-3, -1, -8] = true := by decide +kernel
theorem subd13_1_19 : subd13_1 [-3, -1, -7] = true := by decide +kernel
theorem subd13_1_20 : subd13_1 [-3, -1, -6] = true := by decide +kernel
theorem subd13_1_21 : subd13_1 [-3, -1, -5] = true := by decide +kernel
theorem subd13_1_22 : subd13_1 [-3, -1, -4] = true := by decide +kernel
theorem subd13_1_23 : subd13_1 [-3, -1, -3] = true := by decide +kernel
theorem subd13_1_24 : subd13_1 [-3, -1, -2] = true := by decide +kernel
theorem subd13_1_25 : subd13_1 [-3, -1, -1] = true := by decide +kernel
theorem subd13_1_26 : subd13_1 [-3, -1, 0] = true := by decide +kernel
theorem subd13_1_27 : subd13_1 [-3, -1, 1] = true := by decide +kernel
theorem subd13_1_28 : subd13_1 [-3, -1, 2] = true := by decide +kernel
theorem subd13_1_29 : subd13_1 [-3, -1, 3] = true := by decide +kernel
theorem subd13_1_30 : subd13_1 [-3, -1, 4] = true := by decide +kernel
theorem subd13_1_31 : subd13_1 [-3, -1, 5] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_cons.2 ⟨subd13_1_1, List.forall_mem_cons.2 ⟨subd13_1_2, List.forall_mem_cons.2 ⟨subd13_1_3, List.forall_mem_cons.2 ⟨subd13_1_4, List.forall_mem_cons.2 ⟨subd13_1_5, List.forall_mem_cons.2 ⟨subd13_1_6, List.forall_mem_cons.2 ⟨subd13_1_7, List.forall_mem_cons.2 ⟨subd13_1_8, List.forall_mem_cons.2 ⟨subd13_1_9, List.forall_mem_cons.2 ⟨subd13_1_10, List.forall_mem_cons.2 ⟨subd13_1_11, List.forall_mem_cons.2 ⟨subd13_1_12, List.forall_mem_cons.2 ⟨subd13_1_13, List.forall_mem_cons.2 ⟨subd13_1_14, List.forall_mem_cons.2 ⟨subd13_1_15, List.forall_mem_cons.2 ⟨subd13_1_16, List.forall_mem_cons.2 ⟨subd13_1_17, List.forall_mem_cons.2 ⟨subd13_1_18, List.forall_mem_cons.2 ⟨subd13_1_19, List.forall_mem_cons.2 ⟨subd13_1_20, List.forall_mem_cons.2 ⟨subd13_1_21, List.forall_mem_cons.2 ⟨subd13_1_22, List.forall_mem_cons.2 ⟨subd13_1_23, List.forall_mem_cons.2 ⟨subd13_1_24, List.forall_mem_cons.2 ⟨subd13_1_25, List.forall_mem_cons.2 ⟨subd13_1_26, List.forall_mem_cons.2 ⟨subd13_1_27, List.forall_mem_cons.2 ⟨subd13_1_28, List.forall_mem_cons.2 ⟨subd13_1_29, List.forall_mem_cons.2 ⟨subd13_1_30, List.forall_mem_cons.2 ⟨subd13_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_32 : subd13_1 [-3, 0, -8] = true := by decide +kernel
theorem subd13_1_33 : subd13_1 [-3, 0, -7] = true := by decide +kernel
theorem subd13_1_34 : subd13_1 [-3, 0, -6] = true := by decide +kernel
theorem subd13_1_35 : subd13_1 [-3, 0, -5] = true := by decide +kernel
theorem subd13_1_36 : subd13_1 [-3, 0, -4] = true := by decide +kernel
theorem subd13_1_37 : subd13_1 [-3, 0, -3] = true := by decide +kernel
theorem subd13_1_38 : subd13_1 [-3, 0, -2] = true := by decide +kernel
theorem subd13_1_39 : subd13_1 [-3, 0, -1] = true := by decide +kernel
theorem subd13_1_40 : subd13_1 [-3, 0, 0] = true := by decide +kernel
theorem subd13_1_41 : subd13_1 [-3, 0, 1] = true := by decide +kernel
theorem subd13_1_42 : subd13_1 [-3, 0, 2] = true := by decide +kernel
theorem subd13_1_43 : subd13_1 [-3, 0, 3] = true := by decide +kernel
theorem subd13_1_44 : subd13_1 [-3, 0, 4] = true := by decide +kernel
theorem subd13_1_45 : subd13_1 [-3, 0, 5] = true := by decide +kernel
theorem subd13_1_46 : subd13_1 [-3, 1, -8] = true := by decide +kernel
theorem subd13_1_47 : subd13_1 [-3, 1, -7] = true := by decide +kernel
theorem subd13_1_48 : subd13_1 [-3, 1, -6] = true := by decide +kernel
theorem subd13_1_49 : subd13_1 [-3, 1, -5] = true := by decide +kernel
theorem subd13_1_50 : subd13_1 [-3, 1, -4] = true := by decide +kernel
theorem subd13_1_51 : subd13_1 [-3, 1, -3] = true := by decide +kernel
theorem subd13_1_52 : subd13_1 [-3, 1, -2] = true := by decide +kernel
theorem subd13_1_53 : subd13_1 [-3, 1, -1] = true := by decide +kernel
theorem subd13_1_54 : subd13_1 [-3, 1, 0] = true := by decide +kernel
theorem subd13_1_55 : subd13_1 [-3, 1, 1] = true := by decide +kernel
theorem subd13_1_56 : subd13_1 [-3, 1, 2] = true := by decide +kernel
theorem subd13_1_57 : subd13_1 [-3, 1, 3] = true := by decide +kernel
theorem subd13_1_58 : subd13_1 [-3, 1, 4] = true := by decide +kernel
theorem subd13_1_59 : subd13_1 [-3, 1, 5] = true := by decide +kernel
theorem subd13_1_60 : subd13_1 [-3, 2] = true := by decide +kernel
theorem subd13_1_61 : subd13_1 [-3, 3] = true := by decide +kernel
theorem subd13_1_62 : subd13_1 [-3, 4] = true := by decide +kernel
theorem subd13_1_63 : subd13_1 [-2, -6] = true := by decide +kernel
theorem sbd13_1_1 : ∀ q ∈ blkd13_1_1, subd13_1 q = true := by
  unfold blkd13_1_1
  exact List.forall_mem_cons.2 ⟨subd13_1_32, List.forall_mem_cons.2 ⟨subd13_1_33, List.forall_mem_cons.2 ⟨subd13_1_34, List.forall_mem_cons.2 ⟨subd13_1_35, List.forall_mem_cons.2 ⟨subd13_1_36, List.forall_mem_cons.2 ⟨subd13_1_37, List.forall_mem_cons.2 ⟨subd13_1_38, List.forall_mem_cons.2 ⟨subd13_1_39, List.forall_mem_cons.2 ⟨subd13_1_40, List.forall_mem_cons.2 ⟨subd13_1_41, List.forall_mem_cons.2 ⟨subd13_1_42, List.forall_mem_cons.2 ⟨subd13_1_43, List.forall_mem_cons.2 ⟨subd13_1_44, List.forall_mem_cons.2 ⟨subd13_1_45, List.forall_mem_cons.2 ⟨subd13_1_46, List.forall_mem_cons.2 ⟨subd13_1_47, List.forall_mem_cons.2 ⟨subd13_1_48, List.forall_mem_cons.2 ⟨subd13_1_49, List.forall_mem_cons.2 ⟨subd13_1_50, List.forall_mem_cons.2 ⟨subd13_1_51, List.forall_mem_cons.2 ⟨subd13_1_52, List.forall_mem_cons.2 ⟨subd13_1_53, List.forall_mem_cons.2 ⟨subd13_1_54, List.forall_mem_cons.2 ⟨subd13_1_55, List.forall_mem_cons.2 ⟨subd13_1_56, List.forall_mem_cons.2 ⟨subd13_1_57, List.forall_mem_cons.2 ⟨subd13_1_58, List.forall_mem_cons.2 ⟨subd13_1_59, List.forall_mem_cons.2 ⟨subd13_1_60, List.forall_mem_cons.2 ⟨subd13_1_61, List.forall_mem_cons.2 ⟨subd13_1_62, List.forall_mem_cons.2 ⟨subd13_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_64 : subd13_1 [-2, -5] = true := by decide +kernel
theorem subd13_1_65 : subd13_1 [-2, -4] = true := by decide +kernel
theorem subd13_1_66 : subd13_1 [-2, -3] = true := by decide +kernel
theorem subd13_1_67 : subd13_1 [-2, -2, -8] = true := by decide +kernel
theorem subd13_1_68 : subd13_1 [-2, -2, -7] = true := by decide +kernel
theorem subd13_1_69 : subd13_1 [-2, -2, -6] = true := by decide +kernel
theorem subd13_1_70 : subd13_1 [-2, -2, -5] = true := by decide +kernel
theorem subd13_1_71 : subd13_1 [-2, -2, -4] = true := by decide +kernel
theorem subd13_1_72 : subd13_1 [-2, -2, -3] = true := by decide +kernel
theorem subd13_1_73 : subd13_1 [-2, -2, -2] = true := by decide +kernel
theorem subd13_1_74 : subd13_1 [-2, -2, -1] = true := by decide +kernel
theorem subd13_1_75 : subd13_1 [-2, -2, 0] = true := by decide +kernel
theorem subd13_1_76 : subd13_1 [-2, -2, 1] = true := by decide +kernel
theorem subd13_1_77 : subd13_1 [-2, -2, 2] = true := by decide +kernel
theorem subd13_1_78 : subd13_1 [-2, -2, 3] = true := by decide +kernel
theorem subd13_1_79 : subd13_1 [-2, -2, 4] = true := by decide +kernel
theorem subd13_1_80 : subd13_1 [-2, -2, 5] = true := by decide +kernel
theorem subd13_1_81 : subd13_1 [-2, -2, 6] = true := by decide +kernel
theorem subd13_1_82 : subd13_1 [-2, -1, -8] = true := by decide +kernel
theorem subd13_1_83 : subd13_1 [-2, -1, -7] = true := by decide +kernel
theorem subd13_1_84 : subd13_1 [-2, -1, -6] = true := by decide +kernel
theorem subd13_1_85 : subd13_1 [-2, -1, -5] = true := by decide +kernel
theorem subd13_1_86 : subd13_1 [-2, -1, -4] = true := by decide +kernel
theorem subd13_1_87 : subd13_1 [-2, -1, -3] = true := by decide +kernel
theorem subd13_1_88 : subd13_1 [-2, -1, -2] = true := by decide +kernel
theorem subd13_1_89 : subd13_1 [-2, -1, -1] = true := by decide +kernel
theorem subd13_1_90 : subd13_1 [-2, -1, 0] = true := by decide +kernel
theorem subd13_1_91 : subd13_1 [-2, -1, 1] = true := by decide +kernel
theorem subd13_1_92 : subd13_1 [-2, -1, 2] = true := by decide +kernel
theorem subd13_1_93 : subd13_1 [-2, -1, 3] = true := by decide +kernel
theorem subd13_1_94 : subd13_1 [-2, -1, 4] = true := by decide +kernel
theorem subd13_1_95 : subd13_1 [-2, -1, 5] = true := by decide +kernel
theorem sbd13_1_2 : ∀ q ∈ blkd13_1_2, subd13_1 q = true := by
  unfold blkd13_1_2
  exact List.forall_mem_cons.2 ⟨subd13_1_64, List.forall_mem_cons.2 ⟨subd13_1_65, List.forall_mem_cons.2 ⟨subd13_1_66, List.forall_mem_cons.2 ⟨subd13_1_67, List.forall_mem_cons.2 ⟨subd13_1_68, List.forall_mem_cons.2 ⟨subd13_1_69, List.forall_mem_cons.2 ⟨subd13_1_70, List.forall_mem_cons.2 ⟨subd13_1_71, List.forall_mem_cons.2 ⟨subd13_1_72, List.forall_mem_cons.2 ⟨subd13_1_73, List.forall_mem_cons.2 ⟨subd13_1_74, List.forall_mem_cons.2 ⟨subd13_1_75, List.forall_mem_cons.2 ⟨subd13_1_76, List.forall_mem_cons.2 ⟨subd13_1_77, List.forall_mem_cons.2 ⟨subd13_1_78, List.forall_mem_cons.2 ⟨subd13_1_79, List.forall_mem_cons.2 ⟨subd13_1_80, List.forall_mem_cons.2 ⟨subd13_1_81, List.forall_mem_cons.2 ⟨subd13_1_82, List.forall_mem_cons.2 ⟨subd13_1_83, List.forall_mem_cons.2 ⟨subd13_1_84, List.forall_mem_cons.2 ⟨subd13_1_85, List.forall_mem_cons.2 ⟨subd13_1_86, List.forall_mem_cons.2 ⟨subd13_1_87, List.forall_mem_cons.2 ⟨subd13_1_88, List.forall_mem_cons.2 ⟨subd13_1_89, List.forall_mem_cons.2 ⟨subd13_1_90, List.forall_mem_cons.2 ⟨subd13_1_91, List.forall_mem_cons.2 ⟨subd13_1_92, List.forall_mem_cons.2 ⟨subd13_1_93, List.forall_mem_cons.2 ⟨subd13_1_94, List.forall_mem_cons.2 ⟨subd13_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_96 : subd13_1 [-2, -1, 6] = true := by decide +kernel
theorem subd13_1_97 : subd13_1 [-2, 0, -8] = true := by decide +kernel
theorem subd13_1_98 : subd13_1 [-2, 0, -7] = true := by decide +kernel
theorem subd13_1_99 : subd13_1 [-2, 0, -6] = true := by decide +kernel
theorem subd13_1_100 : subd13_1 [-2, 0, -5] = true := by decide +kernel
theorem subd13_1_101 : subd13_1 [-2, 0, -4] = true := by decide +kernel
theorem subd13_1_102 : subd13_1 [-2, 0, -3] = true := by decide +kernel
theorem subd13_1_103 : subd13_1 [-2, 0, -2] = true := by decide +kernel
theorem subd13_1_104 : subd13_1 [-2, 0, -1] = true := by decide +kernel
theorem subd13_1_105 : subd13_1 [-2, 0, 0] = true := by decide +kernel
theorem subd13_1_106 : subd13_1 [-2, 0, 1] = true := by decide +kernel
theorem subd13_1_107 : subd13_1 [-2, 0, 2] = true := by decide +kernel
theorem subd13_1_108 : subd13_1 [-2, 0, 3] = true := by decide +kernel
theorem subd13_1_109 : subd13_1 [-2, 0, 4] = true := by decide +kernel
theorem subd13_1_110 : subd13_1 [-2, 0, 5] = true := by decide +kernel
theorem subd13_1_111 : subd13_1 [-2, 0, 6] = true := by decide +kernel
theorem subd13_1_112 : subd13_1 [-2, 1, -8] = true := by decide +kernel
theorem subd13_1_113 : subd13_1 [-2, 1, -7] = true := by decide +kernel
theorem subd13_1_114 : subd13_1 [-2, 1, -6] = true := by decide +kernel
theorem subd13_1_115 : subd13_1 [-2, 1, -5] = true := by decide +kernel
theorem subd13_1_116 : subd13_1 [-2, 1, -4] = true := by decide +kernel
theorem subd13_1_117 : subd13_1 [-2, 1, -3] = true := by decide +kernel
theorem subd13_1_118 : subd13_1 [-2, 1, -2] = true := by decide +kernel
theorem subd13_1_119 : subd13_1 [-2, 1, -1] = true := by decide +kernel
theorem subd13_1_120 : subd13_1 [-2, 1, 0] = true := by decide +kernel
theorem subd13_1_121 : subd13_1 [-2, 1, 1] = true := by decide +kernel
theorem subd13_1_122 : subd13_1 [-2, 1, 2] = true := by decide +kernel
theorem subd13_1_123 : subd13_1 [-2, 1, 3] = true := by decide +kernel
theorem subd13_1_124 : subd13_1 [-2, 1, 4] = true := by decide +kernel
theorem subd13_1_125 : subd13_1 [-2, 1, 5] = true := by decide +kernel
theorem subd13_1_126 : subd13_1 [-2, 1, 6] = true := by decide +kernel
theorem subd13_1_127 : subd13_1 [-2, 2, -8] = true := by decide +kernel
theorem sbd13_1_3 : ∀ q ∈ blkd13_1_3, subd13_1 q = true := by
  unfold blkd13_1_3
  exact List.forall_mem_cons.2 ⟨subd13_1_96, List.forall_mem_cons.2 ⟨subd13_1_97, List.forall_mem_cons.2 ⟨subd13_1_98, List.forall_mem_cons.2 ⟨subd13_1_99, List.forall_mem_cons.2 ⟨subd13_1_100, List.forall_mem_cons.2 ⟨subd13_1_101, List.forall_mem_cons.2 ⟨subd13_1_102, List.forall_mem_cons.2 ⟨subd13_1_103, List.forall_mem_cons.2 ⟨subd13_1_104, List.forall_mem_cons.2 ⟨subd13_1_105, List.forall_mem_cons.2 ⟨subd13_1_106, List.forall_mem_cons.2 ⟨subd13_1_107, List.forall_mem_cons.2 ⟨subd13_1_108, List.forall_mem_cons.2 ⟨subd13_1_109, List.forall_mem_cons.2 ⟨subd13_1_110, List.forall_mem_cons.2 ⟨subd13_1_111, List.forall_mem_cons.2 ⟨subd13_1_112, List.forall_mem_cons.2 ⟨subd13_1_113, List.forall_mem_cons.2 ⟨subd13_1_114, List.forall_mem_cons.2 ⟨subd13_1_115, List.forall_mem_cons.2 ⟨subd13_1_116, List.forall_mem_cons.2 ⟨subd13_1_117, List.forall_mem_cons.2 ⟨subd13_1_118, List.forall_mem_cons.2 ⟨subd13_1_119, List.forall_mem_cons.2 ⟨subd13_1_120, List.forall_mem_cons.2 ⟨subd13_1_121, List.forall_mem_cons.2 ⟨subd13_1_122, List.forall_mem_cons.2 ⟨subd13_1_123, List.forall_mem_cons.2 ⟨subd13_1_124, List.forall_mem_cons.2 ⟨subd13_1_125, List.forall_mem_cons.2 ⟨subd13_1_126, List.forall_mem_cons.2 ⟨subd13_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_128 : subd13_1 [-2, 2, -7] = true := by decide +kernel
theorem subd13_1_129 : subd13_1 [-2, 2, -6] = true := by decide +kernel
theorem subd13_1_130 : subd13_1 [-2, 2, -5] = true := by decide +kernel
theorem subd13_1_131 : subd13_1 [-2, 2, -4] = true := by decide +kernel
theorem subd13_1_132 : subd13_1 [-2, 2, -3] = true := by decide +kernel
theorem subd13_1_133 : subd13_1 [-2, 2, -2] = true := by decide +kernel
theorem subd13_1_134 : subd13_1 [-2, 2, -1] = true := by decide +kernel
theorem subd13_1_135 : subd13_1 [-2, 2, 0] = true := by decide +kernel
theorem subd13_1_136 : subd13_1 [-2, 2, 1] = true := by decide +kernel
theorem subd13_1_137 : subd13_1 [-2, 2, 2] = true := by decide +kernel
theorem subd13_1_138 : subd13_1 [-2, 2, 3] = true := by decide +kernel
theorem subd13_1_139 : subd13_1 [-2, 2, 4] = true := by decide +kernel
theorem subd13_1_140 : subd13_1 [-2, 2, 5] = true := by decide +kernel
theorem subd13_1_141 : subd13_1 [-2, 2, 6] = true := by decide +kernel
theorem subd13_1_142 : subd13_1 [-2, 3] = true := by decide +kernel
theorem subd13_1_143 : subd13_1 [-2, 4] = true := by decide +kernel
theorem subd13_1_144 : subd13_1 [-1, -6] = true := by decide +kernel
theorem subd13_1_145 : subd13_1 [-1, -5] = true := by decide +kernel
theorem subd13_1_146 : subd13_1 [-1, -4] = true := by decide +kernel
theorem subd13_1_147 : subd13_1 [-1, -3, -7] = true := by decide +kernel
theorem subd13_1_148 : subd13_1 [-1, -3, -6] = true := by decide +kernel
theorem subd13_1_149 : subd13_1 [-1, -3, -5] = true := by decide +kernel
theorem subd13_1_150 : subd13_1 [-1, -3, -4] = true := by decide +kernel
theorem subd13_1_151 : subd13_1 [-1, -3, -3] = true := by decide +kernel
theorem subd13_1_152 : subd13_1 [-1, -3, -2] = true := by decide +kernel
theorem subd13_1_153 : subd13_1 [-1, -3, -1] = true := by decide +kernel
theorem subd13_1_154 : subd13_1 [-1, -3, 0] = true := by decide +kernel
theorem subd13_1_155 : subd13_1 [-1, -3, 1] = true := by decide +kernel
theorem subd13_1_156 : subd13_1 [-1, -3, 2] = true := by decide +kernel
theorem subd13_1_157 : subd13_1 [-1, -3, 3] = true := by decide +kernel
theorem subd13_1_158 : subd13_1 [-1, -3, 4] = true := by decide +kernel
theorem subd13_1_159 : subd13_1 [-1, -3, 5] = true := by decide +kernel
theorem sbd13_1_4 : ∀ q ∈ blkd13_1_4, subd13_1 q = true := by
  unfold blkd13_1_4
  exact List.forall_mem_cons.2 ⟨subd13_1_128, List.forall_mem_cons.2 ⟨subd13_1_129, List.forall_mem_cons.2 ⟨subd13_1_130, List.forall_mem_cons.2 ⟨subd13_1_131, List.forall_mem_cons.2 ⟨subd13_1_132, List.forall_mem_cons.2 ⟨subd13_1_133, List.forall_mem_cons.2 ⟨subd13_1_134, List.forall_mem_cons.2 ⟨subd13_1_135, List.forall_mem_cons.2 ⟨subd13_1_136, List.forall_mem_cons.2 ⟨subd13_1_137, List.forall_mem_cons.2 ⟨subd13_1_138, List.forall_mem_cons.2 ⟨subd13_1_139, List.forall_mem_cons.2 ⟨subd13_1_140, List.forall_mem_cons.2 ⟨subd13_1_141, List.forall_mem_cons.2 ⟨subd13_1_142, List.forall_mem_cons.2 ⟨subd13_1_143, List.forall_mem_cons.2 ⟨subd13_1_144, List.forall_mem_cons.2 ⟨subd13_1_145, List.forall_mem_cons.2 ⟨subd13_1_146, List.forall_mem_cons.2 ⟨subd13_1_147, List.forall_mem_cons.2 ⟨subd13_1_148, List.forall_mem_cons.2 ⟨subd13_1_149, List.forall_mem_cons.2 ⟨subd13_1_150, List.forall_mem_cons.2 ⟨subd13_1_151, List.forall_mem_cons.2 ⟨subd13_1_152, List.forall_mem_cons.2 ⟨subd13_1_153, List.forall_mem_cons.2 ⟨subd13_1_154, List.forall_mem_cons.2 ⟨subd13_1_155, List.forall_mem_cons.2 ⟨subd13_1_156, List.forall_mem_cons.2 ⟨subd13_1_157, List.forall_mem_cons.2 ⟨subd13_1_158, List.forall_mem_cons.2 ⟨subd13_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_160 : subd13_1 [-1, -3, 6] = true := by decide +kernel
theorem subd13_1_161 : subd13_1 [-1, -2, -8] = true := by decide +kernel
theorem subd13_1_162 : subd13_1 [-1, -2, -7] = true := by decide +kernel
theorem subd13_1_163 : subd13_1 [-1, -2, -6] = true := by decide +kernel
theorem subd13_1_164 : subd13_1 [-1, -2, -5] = true := by decide +kernel
theorem subd13_1_165 : subd13_1 [-1, -2, -4] = true := by decide +kernel
theorem subd13_1_166 : subd13_1 [-1, -2, -3] = true := by decide +kernel
theorem subd13_1_167 : subd13_1 [-1, -2, -2] = true := by decide +kernel
theorem subd13_1_168 : subd13_1 [-1, -2, -1] = true := by decide +kernel
theorem subd13_1_169 : subd13_1 [-1, -2, 0] = true := by decide +kernel
theorem subd13_1_170 : subd13_1 [-1, -2, 1] = true := by decide +kernel
theorem subd13_1_171 : subd13_1 [-1, -2, 2] = true := by decide +kernel
theorem subd13_1_172 : subd13_1 [-1, -2, 3] = true := by decide +kernel
theorem subd13_1_173 : subd13_1 [-1, -2, 4] = true := by decide +kernel
theorem subd13_1_174 : subd13_1 [-1, -2, 5] = true := by decide +kernel
theorem subd13_1_175 : subd13_1 [-1, -2, 6] = true := by decide +kernel
theorem subd13_1_176 : subd13_1 [-1, -1, -8] = true := by decide +kernel
theorem subd13_1_177 : subd13_1 [-1, -1, -7] = true := by decide +kernel
theorem subd13_1_178 : subd13_1 [-1, -1, -6] = true := by decide +kernel
theorem subd13_1_179 : subd13_1 [-1, -1, -5] = true := by decide +kernel
theorem subd13_1_180 : subd13_1 [-1, -1, -4] = true := by decide +kernel
theorem subd13_1_181 : subd13_1 [-1, -1, -3] = true := by decide +kernel
theorem subd13_1_182 : subd13_1 [-1, -1, -2] = true := by decide +kernel
theorem subd13_1_183 : subd13_1 [-1, -1, -1] = true := by decide +kernel
theorem subd13_1_184 : subd13_1 [-1, -1, 0] = true := by decide +kernel
theorem subd13_1_185 : subd13_1 [-1, -1, 1] = true := by decide +kernel
theorem subd13_1_186 : subd13_1 [-1, -1, 2] = true := by decide +kernel
theorem subd13_1_187 : subd13_1 [-1, -1, 3] = true := by decide +kernel
theorem subd13_1_188 : subd13_1 [-1, -1, 4] = true := by decide +kernel
theorem subd13_1_189 : subd13_1 [-1, -1, 5] = true := by decide +kernel
theorem subd13_1_190 : subd13_1 [-1, -1, 6] = true := by decide +kernel
theorem subd13_1_191 : subd13_1 [-1, -1, 7] = true := by decide +kernel
theorem sbd13_1_5 : ∀ q ∈ blkd13_1_5, subd13_1 q = true := by
  unfold blkd13_1_5
  exact List.forall_mem_cons.2 ⟨subd13_1_160, List.forall_mem_cons.2 ⟨subd13_1_161, List.forall_mem_cons.2 ⟨subd13_1_162, List.forall_mem_cons.2 ⟨subd13_1_163, List.forall_mem_cons.2 ⟨subd13_1_164, List.forall_mem_cons.2 ⟨subd13_1_165, List.forall_mem_cons.2 ⟨subd13_1_166, List.forall_mem_cons.2 ⟨subd13_1_167, List.forall_mem_cons.2 ⟨subd13_1_168, List.forall_mem_cons.2 ⟨subd13_1_169, List.forall_mem_cons.2 ⟨subd13_1_170, List.forall_mem_cons.2 ⟨subd13_1_171, List.forall_mem_cons.2 ⟨subd13_1_172, List.forall_mem_cons.2 ⟨subd13_1_173, List.forall_mem_cons.2 ⟨subd13_1_174, List.forall_mem_cons.2 ⟨subd13_1_175, List.forall_mem_cons.2 ⟨subd13_1_176, List.forall_mem_cons.2 ⟨subd13_1_177, List.forall_mem_cons.2 ⟨subd13_1_178, List.forall_mem_cons.2 ⟨subd13_1_179, List.forall_mem_cons.2 ⟨subd13_1_180, List.forall_mem_cons.2 ⟨subd13_1_181, List.forall_mem_cons.2 ⟨subd13_1_182, List.forall_mem_cons.2 ⟨subd13_1_183, List.forall_mem_cons.2 ⟨subd13_1_184, List.forall_mem_cons.2 ⟨subd13_1_185, List.forall_mem_cons.2 ⟨subd13_1_186, List.forall_mem_cons.2 ⟨subd13_1_187, List.forall_mem_cons.2 ⟨subd13_1_188, List.forall_mem_cons.2 ⟨subd13_1_189, List.forall_mem_cons.2 ⟨subd13_1_190, List.forall_mem_cons.2 ⟨subd13_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_192 : subd13_1 [-1, 0, -9] = true := by decide +kernel
theorem subd13_1_193 : subd13_1 [-1, 0, -8] = true := by decide +kernel
theorem subd13_1_194 : subd13_1 [-1, 0, -7] = true := by decide +kernel
theorem subd13_1_195 : subd13_1 [-1, 0, -6] = true := by decide +kernel
theorem subd13_1_196 : subd13_1 [-1, 0, -5] = true := by decide +kernel
theorem subd13_1_197 : subd13_1 [-1, 0, -4] = true := by decide +kernel
theorem subd13_1_198 : subd13_1 [-1, 0, -3] = true := by decide +kernel
theorem subd13_1_199 : subd13_1 [-1, 0, -2] = true := by decide +kernel
theorem subd13_1_200 : subd13_1 [-1, 0, -1] = true := by decide +kernel
theorem subd13_1_201 : subd13_1 [-1, 0, 0] = true := by decide +kernel
theorem subd13_1_202 : subd13_1 [-1, 0, 1] = true := by decide +kernel
theorem subd13_1_203 : subd13_1 [-1, 0, 2] = true := by decide +kernel
theorem subd13_1_204 : subd13_1 [-1, 0, 3] = true := by decide +kernel
theorem subd13_1_205 : subd13_1 [-1, 0, 4] = true := by decide +kernel
theorem subd13_1_206 : subd13_1 [-1, 0, 5] = true := by decide +kernel
theorem subd13_1_207 : subd13_1 [-1, 0, 6] = true := by decide +kernel
theorem subd13_1_208 : subd13_1 [-1, 0, 7] = true := by decide +kernel
theorem subd13_1_209 : subd13_1 [-1, 1, -8] = true := by decide +kernel
theorem subd13_1_210 : subd13_1 [-1, 1, -7] = true := by decide +kernel
theorem subd13_1_211 : subd13_1 [-1, 1, -6] = true := by decide +kernel
theorem subd13_1_212 : subd13_1 [-1, 1, -5] = true := by decide +kernel
theorem subd13_1_213 : subd13_1 [-1, 1, -4] = true := by decide +kernel
theorem subd13_1_214 : subd13_1 [-1, 1, -3] = true := by decide +kernel
theorem subd13_1_215 : subd13_1 [-1, 1, -2] = true := by decide +kernel
theorem subd13_1_216 : subd13_1 [-1, 1, -1] = true := by decide +kernel
theorem subd13_1_217 : subd13_1 [-1, 1, 0] = true := by decide +kernel
theorem subd13_1_218 : subd13_1 [-1, 1, 1] = true := by decide +kernel
theorem subd13_1_219 : subd13_1 [-1, 1, 2] = true := by decide +kernel
theorem subd13_1_220 : subd13_1 [-1, 1, 3] = true := by decide +kernel
theorem subd13_1_221 : subd13_1 [-1, 1, 4] = true := by decide +kernel
theorem subd13_1_222 : subd13_1 [-1, 1, 5] = true := by decide +kernel
theorem subd13_1_223 : subd13_1 [-1, 1, 6] = true := by decide +kernel
theorem sbd13_1_6 : ∀ q ∈ blkd13_1_6, subd13_1 q = true := by
  unfold blkd13_1_6
  exact List.forall_mem_cons.2 ⟨subd13_1_192, List.forall_mem_cons.2 ⟨subd13_1_193, List.forall_mem_cons.2 ⟨subd13_1_194, List.forall_mem_cons.2 ⟨subd13_1_195, List.forall_mem_cons.2 ⟨subd13_1_196, List.forall_mem_cons.2 ⟨subd13_1_197, List.forall_mem_cons.2 ⟨subd13_1_198, List.forall_mem_cons.2 ⟨subd13_1_199, List.forall_mem_cons.2 ⟨subd13_1_200, List.forall_mem_cons.2 ⟨subd13_1_201, List.forall_mem_cons.2 ⟨subd13_1_202, List.forall_mem_cons.2 ⟨subd13_1_203, List.forall_mem_cons.2 ⟨subd13_1_204, List.forall_mem_cons.2 ⟨subd13_1_205, List.forall_mem_cons.2 ⟨subd13_1_206, List.forall_mem_cons.2 ⟨subd13_1_207, List.forall_mem_cons.2 ⟨subd13_1_208, List.forall_mem_cons.2 ⟨subd13_1_209, List.forall_mem_cons.2 ⟨subd13_1_210, List.forall_mem_cons.2 ⟨subd13_1_211, List.forall_mem_cons.2 ⟨subd13_1_212, List.forall_mem_cons.2 ⟨subd13_1_213, List.forall_mem_cons.2 ⟨subd13_1_214, List.forall_mem_cons.2 ⟨subd13_1_215, List.forall_mem_cons.2 ⟨subd13_1_216, List.forall_mem_cons.2 ⟨subd13_1_217, List.forall_mem_cons.2 ⟨subd13_1_218, List.forall_mem_cons.2 ⟨subd13_1_219, List.forall_mem_cons.2 ⟨subd13_1_220, List.forall_mem_cons.2 ⟨subd13_1_221, List.forall_mem_cons.2 ⟨subd13_1_222, List.forall_mem_cons.2 ⟨subd13_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_224 : subd13_1 [-1, 1, 7] = true := by decide +kernel
theorem subd13_1_225 : subd13_1 [-1, 2, -8] = true := by decide +kernel
theorem subd13_1_226 : subd13_1 [-1, 2, -7] = true := by decide +kernel
theorem subd13_1_227 : subd13_1 [-1, 2, -6] = true := by decide +kernel
theorem subd13_1_228 : subd13_1 [-1, 2, -5] = true := by decide +kernel
theorem subd13_1_229 : subd13_1 [-1, 2, -4] = true := by decide +kernel
theorem subd13_1_230 : subd13_1 [-1, 2, -3] = true := by decide +kernel
theorem subd13_1_231 : subd13_1 [-1, 2, -2] = true := by decide +kernel
theorem subd13_1_232 : subd13_1 [-1, 2, -1] = true := by decide +kernel
theorem subd13_1_233 : subd13_1 [-1, 2, 0] = true := by decide +kernel
theorem subd13_1_234 : subd13_1 [-1, 2, 1] = true := by decide +kernel
theorem subd13_1_235 : subd13_1 [-1, 2, 2] = true := by decide +kernel
theorem subd13_1_236 : subd13_1 [-1, 2, 3] = true := by decide +kernel
theorem subd13_1_237 : subd13_1 [-1, 2, 4] = true := by decide +kernel
theorem subd13_1_238 : subd13_1 [-1, 2, 5] = true := by decide +kernel
theorem subd13_1_239 : subd13_1 [-1, 2, 6] = true := by decide +kernel
theorem subd13_1_240 : subd13_1 [-1, 3, -7] = true := by decide +kernel
theorem subd13_1_241 : subd13_1 [-1, 3, -6] = true := by decide +kernel
theorem subd13_1_242 : subd13_1 [-1, 3, -5] = true := by decide +kernel
theorem subd13_1_243 : subd13_1 [-1, 3, -4] = true := by decide +kernel
theorem subd13_1_244 : subd13_1 [-1, 3, -3] = true := by decide +kernel
theorem subd13_1_245 : subd13_1 [-1, 3, -2] = true := by decide +kernel
theorem subd13_1_246 : subd13_1 [-1, 3, -1] = true := by decide +kernel
theorem subd13_1_247 : subd13_1 [-1, 3, 0] = true := by decide +kernel
theorem subd13_1_248 : subd13_1 [-1, 3, 1] = true := by decide +kernel
theorem subd13_1_249 : subd13_1 [-1, 3, 2] = true := by decide +kernel
theorem subd13_1_250 : subd13_1 [-1, 3, 3] = true := by decide +kernel
theorem subd13_1_251 : subd13_1 [-1, 3, 4] = true := by decide +kernel
theorem subd13_1_252 : subd13_1 [-1, 3, 5] = true := by decide +kernel
theorem subd13_1_253 : subd13_1 [-1, 3, 6] = true := by decide +kernel
theorem subd13_1_254 : subd13_1 [-1, 4] = true := by decide +kernel
theorem subd13_1_255 : subd13_1 [-1, 5] = true := by decide +kernel
theorem sbd13_1_7 : ∀ q ∈ blkd13_1_7, subd13_1 q = true := by
  unfold blkd13_1_7
  exact List.forall_mem_cons.2 ⟨subd13_1_224, List.forall_mem_cons.2 ⟨subd13_1_225, List.forall_mem_cons.2 ⟨subd13_1_226, List.forall_mem_cons.2 ⟨subd13_1_227, List.forall_mem_cons.2 ⟨subd13_1_228, List.forall_mem_cons.2 ⟨subd13_1_229, List.forall_mem_cons.2 ⟨subd13_1_230, List.forall_mem_cons.2 ⟨subd13_1_231, List.forall_mem_cons.2 ⟨subd13_1_232, List.forall_mem_cons.2 ⟨subd13_1_233, List.forall_mem_cons.2 ⟨subd13_1_234, List.forall_mem_cons.2 ⟨subd13_1_235, List.forall_mem_cons.2 ⟨subd13_1_236, List.forall_mem_cons.2 ⟨subd13_1_237, List.forall_mem_cons.2 ⟨subd13_1_238, List.forall_mem_cons.2 ⟨subd13_1_239, List.forall_mem_cons.2 ⟨subd13_1_240, List.forall_mem_cons.2 ⟨subd13_1_241, List.forall_mem_cons.2 ⟨subd13_1_242, List.forall_mem_cons.2 ⟨subd13_1_243, List.forall_mem_cons.2 ⟨subd13_1_244, List.forall_mem_cons.2 ⟨subd13_1_245, List.forall_mem_cons.2 ⟨subd13_1_246, List.forall_mem_cons.2 ⟨subd13_1_247, List.forall_mem_cons.2 ⟨subd13_1_248, List.forall_mem_cons.2 ⟨subd13_1_249, List.forall_mem_cons.2 ⟨subd13_1_250, List.forall_mem_cons.2 ⟨subd13_1_251, List.forall_mem_cons.2 ⟨subd13_1_252, List.forall_mem_cons.2 ⟨subd13_1_253, List.forall_mem_cons.2 ⟨subd13_1_254, List.forall_mem_cons.2 ⟨subd13_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_256 : subd13_1 [0, -6] = true := by decide +kernel
theorem subd13_1_257 : subd13_1 [0, -5] = true := by decide +kernel
theorem subd13_1_258 : subd13_1 [0, -4] = true := by decide +kernel
theorem subd13_1_259 : subd13_1 [0, -3, -7] = true := by decide +kernel
theorem subd13_1_260 : subd13_1 [0, -3, -6] = true := by decide +kernel
theorem subd13_1_261 : subd13_1 [0, -3, -5] = true := by decide +kernel
theorem subd13_1_262 : subd13_1 [0, -3, -4] = true := by decide +kernel
theorem subd13_1_263 : subd13_1 [0, -3, -3] = true := by decide +kernel
theorem subd13_1_264 : subd13_1 [0, -3, -2] = true := by decide +kernel
theorem subd13_1_265 : subd13_1 [0, -3, -1] = true := by decide +kernel
theorem subd13_1_266 : subd13_1 [0, -3, 0] = true := by decide +kernel
theorem subd13_1_267 : subd13_1 [0, -3, 1] = true := by decide +kernel
theorem subd13_1_268 : subd13_1 [0, -3, 2] = true := by decide +kernel
theorem subd13_1_269 : subd13_1 [0, -3, 3] = true := by decide +kernel
theorem subd13_1_270 : subd13_1 [0, -3, 4] = true := by decide +kernel
theorem subd13_1_271 : subd13_1 [0, -3, 5] = true := by decide +kernel
theorem subd13_1_272 : subd13_1 [0, -3, 6] = true := by decide +kernel
theorem subd13_1_273 : subd13_1 [0, -2, -8] = true := by decide +kernel
theorem subd13_1_274 : subd13_1 [0, -2, -7] = true := by decide +kernel
theorem subd13_1_275 : subd13_1 [0, -2, -6] = true := by decide +kernel
theorem subd13_1_276 : subd13_1 [0, -2, -5] = true := by decide +kernel
theorem subd13_1_277 : subd13_1 [0, -2, -4] = true := by decide +kernel
theorem subd13_1_278 : subd13_1 [0, -2, -3] = true := by decide +kernel
theorem subd13_1_279 : subd13_1 [0, -2, -2] = true := by decide +kernel
theorem subd13_1_280 : subd13_1 [0, -2, -1] = true := by decide +kernel
theorem subd13_1_281 : subd13_1 [0, -2, 0] = true := by decide +kernel
theorem subd13_1_282 : subd13_1 [0, -2, 1] = true := by decide +kernel
theorem subd13_1_283 : subd13_1 [0, -2, 2] = true := by decide +kernel
theorem subd13_1_284 : subd13_1 [0, -2, 3] = true := by decide +kernel
theorem subd13_1_285 : subd13_1 [0, -2, 4] = true := by decide +kernel
theorem subd13_1_286 : subd13_1 [0, -2, 5] = true := by decide +kernel
theorem subd13_1_287 : subd13_1 [0, -2, 6] = true := by decide +kernel
theorem sbd13_1_8 : ∀ q ∈ blkd13_1_8, subd13_1 q = true := by
  unfold blkd13_1_8
  exact List.forall_mem_cons.2 ⟨subd13_1_256, List.forall_mem_cons.2 ⟨subd13_1_257, List.forall_mem_cons.2 ⟨subd13_1_258, List.forall_mem_cons.2 ⟨subd13_1_259, List.forall_mem_cons.2 ⟨subd13_1_260, List.forall_mem_cons.2 ⟨subd13_1_261, List.forall_mem_cons.2 ⟨subd13_1_262, List.forall_mem_cons.2 ⟨subd13_1_263, List.forall_mem_cons.2 ⟨subd13_1_264, List.forall_mem_cons.2 ⟨subd13_1_265, List.forall_mem_cons.2 ⟨subd13_1_266, List.forall_mem_cons.2 ⟨subd13_1_267, List.forall_mem_cons.2 ⟨subd13_1_268, List.forall_mem_cons.2 ⟨subd13_1_269, List.forall_mem_cons.2 ⟨subd13_1_270, List.forall_mem_cons.2 ⟨subd13_1_271, List.forall_mem_cons.2 ⟨subd13_1_272, List.forall_mem_cons.2 ⟨subd13_1_273, List.forall_mem_cons.2 ⟨subd13_1_274, List.forall_mem_cons.2 ⟨subd13_1_275, List.forall_mem_cons.2 ⟨subd13_1_276, List.forall_mem_cons.2 ⟨subd13_1_277, List.forall_mem_cons.2 ⟨subd13_1_278, List.forall_mem_cons.2 ⟨subd13_1_279, List.forall_mem_cons.2 ⟨subd13_1_280, List.forall_mem_cons.2 ⟨subd13_1_281, List.forall_mem_cons.2 ⟨subd13_1_282, List.forall_mem_cons.2 ⟨subd13_1_283, List.forall_mem_cons.2 ⟨subd13_1_284, List.forall_mem_cons.2 ⟨subd13_1_285, List.forall_mem_cons.2 ⟨subd13_1_286, List.forall_mem_cons.2 ⟨subd13_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_288 : subd13_1 [0, -2, 7] = true := by decide +kernel
theorem subd13_1_289 : subd13_1 [0, -1, -8] = true := by decide +kernel
theorem subd13_1_290 : subd13_1 [0, -1, -7] = true := by decide +kernel
theorem subd13_1_291 : subd13_1 [0, -1, -6] = true := by decide +kernel
theorem subd13_1_292 : subd13_1 [0, -1, -5] = true := by decide +kernel
theorem subd13_1_293 : subd13_1 [0, -1, -4] = true := by decide +kernel
theorem subd13_1_294 : subd13_1 [0, -1, -3] = true := by decide +kernel
theorem subd13_1_295 : subd13_1 [0, -1, -2] = true := by decide +kernel
theorem subd13_1_296 : subd13_1 [0, -1, -1] = true := by decide +kernel
theorem subd13_1_297 : subd13_1 [0, -1, 0] = true := by decide +kernel
theorem subd13_1_298 : subd13_1 [0, -1, 1] = true := by decide +kernel
theorem subd13_1_299 : subd13_1 [0, -1, 2] = true := by decide +kernel
theorem subd13_1_300 : subd13_1 [0, -1, 3] = true := by decide +kernel
theorem subd13_1_301 : subd13_1 [0, -1, 4] = true := by decide +kernel
theorem subd13_1_302 : subd13_1 [0, -1, 5] = true := by decide +kernel
theorem subd13_1_303 : subd13_1 [0, -1, 6] = true := by decide +kernel
theorem subd13_1_304 : subd13_1 [0, -1, 7] = true := by decide +kernel
theorem subd13_1_305 : subd13_1 [0, 0, -8] = true := by decide +kernel
theorem subd13_1_306 : subd13_1 [0, 0, -7] = true := by decide +kernel
theorem subd13_1_307 : subd13_1 [0, 0, -6] = true := by decide +kernel
theorem subd13_1_308 : subd13_1 [0, 0, -5] = true := by decide +kernel
theorem subd13_1_309 : subd13_1 [0, 0, -4] = true := by decide +kernel
theorem subd13_1_310 : subd13_1 [0, 0, -3] = true := by decide +kernel
theorem subd13_1_311 : subd13_1 [0, 0, -2] = true := by decide +kernel
theorem subd13_1_312 : subd13_1 [0, 0, -1] = true := by decide +kernel
theorem subd13_1_313 : subd13_1 [0, 0, 0] = true := by decide +kernel
theorem subd13_1_314 : subd13_1 [0, 0, 1] = true := by decide +kernel
theorem subd13_1_315 : subd13_1 [0, 0, 2] = true := by decide +kernel
theorem subd13_1_316 : subd13_1 [0, 0, 3] = true := by decide +kernel
theorem subd13_1_317 : subd13_1 [0, 0, 4] = true := by decide +kernel
theorem subd13_1_318 : subd13_1 [0, 0, 5] = true := by decide +kernel
theorem subd13_1_319 : subd13_1 [0, 0, 6] = true := by decide +kernel
theorem sbd13_1_9 : ∀ q ∈ blkd13_1_9, subd13_1 q = true := by
  unfold blkd13_1_9
  exact List.forall_mem_cons.2 ⟨subd13_1_288, List.forall_mem_cons.2 ⟨subd13_1_289, List.forall_mem_cons.2 ⟨subd13_1_290, List.forall_mem_cons.2 ⟨subd13_1_291, List.forall_mem_cons.2 ⟨subd13_1_292, List.forall_mem_cons.2 ⟨subd13_1_293, List.forall_mem_cons.2 ⟨subd13_1_294, List.forall_mem_cons.2 ⟨subd13_1_295, List.forall_mem_cons.2 ⟨subd13_1_296, List.forall_mem_cons.2 ⟨subd13_1_297, List.forall_mem_cons.2 ⟨subd13_1_298, List.forall_mem_cons.2 ⟨subd13_1_299, List.forall_mem_cons.2 ⟨subd13_1_300, List.forall_mem_cons.2 ⟨subd13_1_301, List.forall_mem_cons.2 ⟨subd13_1_302, List.forall_mem_cons.2 ⟨subd13_1_303, List.forall_mem_cons.2 ⟨subd13_1_304, List.forall_mem_cons.2 ⟨subd13_1_305, List.forall_mem_cons.2 ⟨subd13_1_306, List.forall_mem_cons.2 ⟨subd13_1_307, List.forall_mem_cons.2 ⟨subd13_1_308, List.forall_mem_cons.2 ⟨subd13_1_309, List.forall_mem_cons.2 ⟨subd13_1_310, List.forall_mem_cons.2 ⟨subd13_1_311, List.forall_mem_cons.2 ⟨subd13_1_312, List.forall_mem_cons.2 ⟨subd13_1_313, List.forall_mem_cons.2 ⟨subd13_1_314, List.forall_mem_cons.2 ⟨subd13_1_315, List.forall_mem_cons.2 ⟨subd13_1_316, List.forall_mem_cons.2 ⟨subd13_1_317, List.forall_mem_cons.2 ⟨subd13_1_318, List.forall_mem_cons.2 ⟨subd13_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_320 : subd13_1 [0, 0, 7] = true := by decide +kernel
theorem subd13_1_321 : subd13_1 [0, 1, -8] = true := by decide +kernel
theorem subd13_1_322 : subd13_1 [0, 1, -7] = true := by decide +kernel
theorem subd13_1_323 : subd13_1 [0, 1, -6] = true := by decide +kernel
theorem subd13_1_324 : subd13_1 [0, 1, -5] = true := by decide +kernel
theorem subd13_1_325 : subd13_1 [0, 1, -4] = true := by decide +kernel
theorem subd13_1_326 : subd13_1 [0, 1, -3] = true := by decide +kernel
theorem subd13_1_327 : subd13_1 [0, 1, -2] = true := by decide +kernel
theorem subd13_1_328 : subd13_1 [0, 1, -1] = true := by decide +kernel
theorem subd13_1_329 : subd13_1 [0, 1, 0] = true := by decide +kernel
theorem subd13_1_330 : subd13_1 [0, 1, 1] = true := by decide +kernel
theorem subd13_1_331 : subd13_1 [0, 1, 2] = true := by decide +kernel
theorem subd13_1_332 : subd13_1 [0, 1, 3] = true := by decide +kernel
theorem subd13_1_333 : subd13_1 [0, 1, 4] = true := by decide +kernel
theorem subd13_1_334 : subd13_1 [0, 1, 5] = true := by decide +kernel
theorem subd13_1_335 : subd13_1 [0, 1, 6] = true := by decide +kernel
theorem subd13_1_336 : subd13_1 [0, 1, 7] = true := by decide +kernel
theorem subd13_1_337 : subd13_1 [0, 2, -8] = true := by decide +kernel
theorem subd13_1_338 : subd13_1 [0, 2, -7] = true := by decide +kernel
theorem subd13_1_339 : subd13_1 [0, 2, -6] = true := by decide +kernel
theorem subd13_1_340 : subd13_1 [0, 2, -5] = true := by decide +kernel
theorem subd13_1_341 : subd13_1 [0, 2, -4] = true := by decide +kernel
theorem subd13_1_342 : subd13_1 [0, 2, -3] = true := by decide +kernel
theorem subd13_1_343 : subd13_1 [0, 2, -2] = true := by decide +kernel
theorem subd13_1_344 : subd13_1 [0, 2, -1] = true := by decide +kernel
theorem subd13_1_345 : subd13_1 [0, 2, 0] = true := by decide +kernel
theorem subd13_1_346 : subd13_1 [0, 2, 1] = true := by decide +kernel
theorem subd13_1_347 : subd13_1 [0, 2, 2] = true := by decide +kernel
theorem subd13_1_348 : subd13_1 [0, 2, 3] = true := by decide +kernel
theorem subd13_1_349 : subd13_1 [0, 2, 4] = true := by decide +kernel
theorem subd13_1_350 : subd13_1 [0, 2, 5] = true := by decide +kernel
theorem subd13_1_351 : subd13_1 [0, 2, 6] = true := by decide +kernel
theorem sbd13_1_10 : ∀ q ∈ blkd13_1_10, subd13_1 q = true := by
  unfold blkd13_1_10
  exact List.forall_mem_cons.2 ⟨subd13_1_320, List.forall_mem_cons.2 ⟨subd13_1_321, List.forall_mem_cons.2 ⟨subd13_1_322, List.forall_mem_cons.2 ⟨subd13_1_323, List.forall_mem_cons.2 ⟨subd13_1_324, List.forall_mem_cons.2 ⟨subd13_1_325, List.forall_mem_cons.2 ⟨subd13_1_326, List.forall_mem_cons.2 ⟨subd13_1_327, List.forall_mem_cons.2 ⟨subd13_1_328, List.forall_mem_cons.2 ⟨subd13_1_329, List.forall_mem_cons.2 ⟨subd13_1_330, List.forall_mem_cons.2 ⟨subd13_1_331, List.forall_mem_cons.2 ⟨subd13_1_332, List.forall_mem_cons.2 ⟨subd13_1_333, List.forall_mem_cons.2 ⟨subd13_1_334, List.forall_mem_cons.2 ⟨subd13_1_335, List.forall_mem_cons.2 ⟨subd13_1_336, List.forall_mem_cons.2 ⟨subd13_1_337, List.forall_mem_cons.2 ⟨subd13_1_338, List.forall_mem_cons.2 ⟨subd13_1_339, List.forall_mem_cons.2 ⟨subd13_1_340, List.forall_mem_cons.2 ⟨subd13_1_341, List.forall_mem_cons.2 ⟨subd13_1_342, List.forall_mem_cons.2 ⟨subd13_1_343, List.forall_mem_cons.2 ⟨subd13_1_344, List.forall_mem_cons.2 ⟨subd13_1_345, List.forall_mem_cons.2 ⟨subd13_1_346, List.forall_mem_cons.2 ⟨subd13_1_347, List.forall_mem_cons.2 ⟨subd13_1_348, List.forall_mem_cons.2 ⟨subd13_1_349, List.forall_mem_cons.2 ⟨subd13_1_350, List.forall_mem_cons.2 ⟨subd13_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_352 : subd13_1 [0, 2, 7] = true := by decide +kernel
theorem subd13_1_353 : subd13_1 [0, 3, -7] = true := by decide +kernel
theorem subd13_1_354 : subd13_1 [0, 3, -6] = true := by decide +kernel
theorem subd13_1_355 : subd13_1 [0, 3, -5] = true := by decide +kernel
theorem subd13_1_356 : subd13_1 [0, 3, -4] = true := by decide +kernel
theorem subd13_1_357 : subd13_1 [0, 3, -3] = true := by decide +kernel
theorem subd13_1_358 : subd13_1 [0, 3, -2] = true := by decide +kernel
theorem subd13_1_359 : subd13_1 [0, 3, -1] = true := by decide +kernel
theorem subd13_1_360 : subd13_1 [0, 3, 0] = true := by decide +kernel
theorem subd13_1_361 : subd13_1 [0, 3, 1] = true := by decide +kernel
theorem subd13_1_362 : subd13_1 [0, 3, 2] = true := by decide +kernel
theorem subd13_1_363 : subd13_1 [0, 3, 3] = true := by decide +kernel
theorem subd13_1_364 : subd13_1 [0, 3, 4] = true := by decide +kernel
theorem subd13_1_365 : subd13_1 [0, 3, 5] = true := by decide +kernel
theorem subd13_1_366 : subd13_1 [0, 3, 6] = true := by decide +kernel
theorem subd13_1_367 : subd13_1 [0, 4] = true := by decide +kernel
theorem subd13_1_368 : subd13_1 [0, 5] = true := by decide +kernel
theorem subd13_1_369 : subd13_1 [1, -6] = true := by decide +kernel
theorem subd13_1_370 : subd13_1 [1, -5] = true := by decide +kernel
theorem subd13_1_371 : subd13_1 [1, -4] = true := by decide +kernel
theorem subd13_1_372 : subd13_1 [1, -3, -7] = true := by decide +kernel
theorem subd13_1_373 : subd13_1 [1, -3, -6] = true := by decide +kernel
theorem subd13_1_374 : subd13_1 [1, -3, -5] = true := by decide +kernel
theorem subd13_1_375 : subd13_1 [1, -3, -4] = true := by decide +kernel
theorem subd13_1_376 : subd13_1 [1, -3, -3] = true := by decide +kernel
theorem subd13_1_377 : subd13_1 [1, -3, -2] = true := by decide +kernel
theorem subd13_1_378 : subd13_1 [1, -3, -1] = true := by decide +kernel
theorem subd13_1_379 : subd13_1 [1, -3, 0] = true := by decide +kernel
theorem subd13_1_380 : subd13_1 [1, -3, 1] = true := by decide +kernel
theorem subd13_1_381 : subd13_1 [1, -3, 2] = true := by decide +kernel
theorem subd13_1_382 : subd13_1 [1, -3, 3] = true := by decide +kernel
theorem subd13_1_383 : subd13_1 [1, -3, 4] = true := by decide +kernel
theorem sbd13_1_11 : ∀ q ∈ blkd13_1_11, subd13_1 q = true := by
  unfold blkd13_1_11
  exact List.forall_mem_cons.2 ⟨subd13_1_352, List.forall_mem_cons.2 ⟨subd13_1_353, List.forall_mem_cons.2 ⟨subd13_1_354, List.forall_mem_cons.2 ⟨subd13_1_355, List.forall_mem_cons.2 ⟨subd13_1_356, List.forall_mem_cons.2 ⟨subd13_1_357, List.forall_mem_cons.2 ⟨subd13_1_358, List.forall_mem_cons.2 ⟨subd13_1_359, List.forall_mem_cons.2 ⟨subd13_1_360, List.forall_mem_cons.2 ⟨subd13_1_361, List.forall_mem_cons.2 ⟨subd13_1_362, List.forall_mem_cons.2 ⟨subd13_1_363, List.forall_mem_cons.2 ⟨subd13_1_364, List.forall_mem_cons.2 ⟨subd13_1_365, List.forall_mem_cons.2 ⟨subd13_1_366, List.forall_mem_cons.2 ⟨subd13_1_367, List.forall_mem_cons.2 ⟨subd13_1_368, List.forall_mem_cons.2 ⟨subd13_1_369, List.forall_mem_cons.2 ⟨subd13_1_370, List.forall_mem_cons.2 ⟨subd13_1_371, List.forall_mem_cons.2 ⟨subd13_1_372, List.forall_mem_cons.2 ⟨subd13_1_373, List.forall_mem_cons.2 ⟨subd13_1_374, List.forall_mem_cons.2 ⟨subd13_1_375, List.forall_mem_cons.2 ⟨subd13_1_376, List.forall_mem_cons.2 ⟨subd13_1_377, List.forall_mem_cons.2 ⟨subd13_1_378, List.forall_mem_cons.2 ⟨subd13_1_379, List.forall_mem_cons.2 ⟨subd13_1_380, List.forall_mem_cons.2 ⟨subd13_1_381, List.forall_mem_cons.2 ⟨subd13_1_382, List.forall_mem_cons.2 ⟨subd13_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
