import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_4_0 : subd6_4 [-6] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [-5, -4] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [-5, -3] = true := by decide +kernel
theorem subd6_4_3 : subd6_4 [-5, -2] = true := by decide +kernel
theorem subd6_4_4 : subd6_4 [-5, -1] = true := by decide +kernel
theorem subd6_4_5 : subd6_4 [-5, 0] = true := by decide +kernel
theorem subd6_4_6 : subd6_4 [-5, 1] = true := by decide +kernel
theorem subd6_4_7 : subd6_4 [-5, 2] = true := by decide +kernel
theorem subd6_4_8 : subd6_4 [-5, 3] = true := by decide +kernel
theorem subd6_4_9 : subd6_4 [-5, 4] = true := by decide +kernel
theorem subd6_4_10 : subd6_4 [-4, -5] = true := by decide +kernel
theorem subd6_4_11 : subd6_4 [-4, -4] = true := by decide +kernel
theorem subd6_4_12 : subd6_4 [-4, -3] = true := by decide +kernel
theorem subd6_4_13 : subd6_4 [-4, -2] = true := by decide +kernel
theorem subd6_4_14 : subd6_4 [-4, -1] = true := by decide +kernel
theorem subd6_4_15 : subd6_4 [-4, 0] = true := by decide +kernel
theorem subd6_4_16 : subd6_4 [-4, 1] = true := by decide +kernel
theorem subd6_4_17 : subd6_4 [-4, 2] = true := by decide +kernel
theorem subd6_4_18 : subd6_4 [-4, 3] = true := by decide +kernel
theorem subd6_4_19 : subd6_4 [-4, 4] = true := by decide +kernel
theorem subd6_4_20 : subd6_4 [-4, 5] = true := by decide +kernel
theorem subd6_4_21 : subd6_4 [-3, -6] = true := by decide +kernel
theorem subd6_4_22 : subd6_4 [-3, -5] = true := by decide +kernel
theorem subd6_4_23 : subd6_4 [-3, -4] = true := by decide +kernel
theorem subd6_4_24 : subd6_4 [-3, -3] = true := by decide +kernel
theorem subd6_4_25 : subd6_4 [-3, -2] = true := by decide +kernel
theorem subd6_4_26 : subd6_4 [-3, -1, -6] = true := by decide +kernel
theorem subd6_4_27 : subd6_4 [-3, -1, -5] = true := by decide +kernel
theorem subd6_4_28 : subd6_4 [-3, -1, -4] = true := by decide +kernel
theorem subd6_4_29 : subd6_4 [-3, -1, -3] = true := by decide +kernel
theorem subd6_4_30 : subd6_4 [-3, -1, -2] = true := by decide +kernel
theorem subd6_4_31 : subd6_4 [-3, -1, -1] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_cons.2 ⟨subd6_4_3, List.forall_mem_cons.2 ⟨subd6_4_4, List.forall_mem_cons.2 ⟨subd6_4_5, List.forall_mem_cons.2 ⟨subd6_4_6, List.forall_mem_cons.2 ⟨subd6_4_7, List.forall_mem_cons.2 ⟨subd6_4_8, List.forall_mem_cons.2 ⟨subd6_4_9, List.forall_mem_cons.2 ⟨subd6_4_10, List.forall_mem_cons.2 ⟨subd6_4_11, List.forall_mem_cons.2 ⟨subd6_4_12, List.forall_mem_cons.2 ⟨subd6_4_13, List.forall_mem_cons.2 ⟨subd6_4_14, List.forall_mem_cons.2 ⟨subd6_4_15, List.forall_mem_cons.2 ⟨subd6_4_16, List.forall_mem_cons.2 ⟨subd6_4_17, List.forall_mem_cons.2 ⟨subd6_4_18, List.forall_mem_cons.2 ⟨subd6_4_19, List.forall_mem_cons.2 ⟨subd6_4_20, List.forall_mem_cons.2 ⟨subd6_4_21, List.forall_mem_cons.2 ⟨subd6_4_22, List.forall_mem_cons.2 ⟨subd6_4_23, List.forall_mem_cons.2 ⟨subd6_4_24, List.forall_mem_cons.2 ⟨subd6_4_25, List.forall_mem_cons.2 ⟨subd6_4_26, List.forall_mem_cons.2 ⟨subd6_4_27, List.forall_mem_cons.2 ⟨subd6_4_28, List.forall_mem_cons.2 ⟨subd6_4_29, List.forall_mem_cons.2 ⟨subd6_4_30, List.forall_mem_cons.2 ⟨subd6_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_32 : subd6_4 [-3, -1, 0] = true := by decide +kernel
theorem subd6_4_33 : subd6_4 [-3, -1, 1] = true := by decide +kernel
theorem subd6_4_34 : subd6_4 [-3, -1, 2] = true := by decide +kernel
theorem subd6_4_35 : subd6_4 [-3, -1, 3] = true := by decide +kernel
theorem subd6_4_36 : subd6_4 [-3, -1, 4] = true := by decide +kernel
theorem subd6_4_37 : subd6_4 [-3, -1, 5] = true := by decide +kernel
theorem subd6_4_38 : subd6_4 [-3, -1, 6] = true := by decide +kernel
theorem subd6_4_39 : subd6_4 [-3, 0, -7] = true := by decide +kernel
theorem subd6_4_40 : subd6_4 [-3, 0, -6] = true := by decide +kernel
theorem subd6_4_41 : subd6_4 [-3, 0, -5] = true := by decide +kernel
theorem subd6_4_42 : subd6_4 [-3, 0, -4] = true := by decide +kernel
theorem subd6_4_43 : subd6_4 [-3, 0, -3] = true := by decide +kernel
theorem subd6_4_44 : subd6_4 [-3, 0, -2] = true := by decide +kernel
theorem subd6_4_45 : subd6_4 [-3, 0, -1] = true := by decide +kernel
theorem subd6_4_46 : subd6_4 [-3, 0, 0] = true := by decide +kernel
theorem subd6_4_47 : subd6_4 [-3, 0, 1] = true := by decide +kernel
theorem subd6_4_48 : subd6_4 [-3, 0, 2] = true := by decide +kernel
theorem subd6_4_49 : subd6_4 [-3, 0, 3] = true := by decide +kernel
theorem subd6_4_50 : subd6_4 [-3, 0, 4] = true := by decide +kernel
theorem subd6_4_51 : subd6_4 [-3, 0, 5] = true := by decide +kernel
theorem subd6_4_52 : subd6_4 [-3, 0, 6] = true := by decide +kernel
theorem subd6_4_53 : subd6_4 [-3, 1, -7] = true := by decide +kernel
theorem subd6_4_54 : subd6_4 [-3, 1, -6] = true := by decide +kernel
theorem subd6_4_55 : subd6_4 [-3, 1, -5] = true := by decide +kernel
theorem subd6_4_56 : subd6_4 [-3, 1, -4] = true := by decide +kernel
theorem subd6_4_57 : subd6_4 [-3, 1, -3] = true := by decide +kernel
theorem subd6_4_58 : subd6_4 [-3, 1, -2] = true := by decide +kernel
theorem subd6_4_59 : subd6_4 [-3, 1, -1] = true := by decide +kernel
theorem subd6_4_60 : subd6_4 [-3, 1, 0] = true := by decide +kernel
theorem subd6_4_61 : subd6_4 [-3, 1, 1] = true := by decide +kernel
theorem subd6_4_62 : subd6_4 [-3, 1, 2] = true := by decide +kernel
theorem subd6_4_63 : subd6_4 [-3, 1, 3] = true := by decide +kernel
theorem sbd6_4_1 : ∀ q ∈ blkd6_4_1, subd6_4 q = true := by
  unfold blkd6_4_1
  exact List.forall_mem_cons.2 ⟨subd6_4_32, List.forall_mem_cons.2 ⟨subd6_4_33, List.forall_mem_cons.2 ⟨subd6_4_34, List.forall_mem_cons.2 ⟨subd6_4_35, List.forall_mem_cons.2 ⟨subd6_4_36, List.forall_mem_cons.2 ⟨subd6_4_37, List.forall_mem_cons.2 ⟨subd6_4_38, List.forall_mem_cons.2 ⟨subd6_4_39, List.forall_mem_cons.2 ⟨subd6_4_40, List.forall_mem_cons.2 ⟨subd6_4_41, List.forall_mem_cons.2 ⟨subd6_4_42, List.forall_mem_cons.2 ⟨subd6_4_43, List.forall_mem_cons.2 ⟨subd6_4_44, List.forall_mem_cons.2 ⟨subd6_4_45, List.forall_mem_cons.2 ⟨subd6_4_46, List.forall_mem_cons.2 ⟨subd6_4_47, List.forall_mem_cons.2 ⟨subd6_4_48, List.forall_mem_cons.2 ⟨subd6_4_49, List.forall_mem_cons.2 ⟨subd6_4_50, List.forall_mem_cons.2 ⟨subd6_4_51, List.forall_mem_cons.2 ⟨subd6_4_52, List.forall_mem_cons.2 ⟨subd6_4_53, List.forall_mem_cons.2 ⟨subd6_4_54, List.forall_mem_cons.2 ⟨subd6_4_55, List.forall_mem_cons.2 ⟨subd6_4_56, List.forall_mem_cons.2 ⟨subd6_4_57, List.forall_mem_cons.2 ⟨subd6_4_58, List.forall_mem_cons.2 ⟨subd6_4_59, List.forall_mem_cons.2 ⟨subd6_4_60, List.forall_mem_cons.2 ⟨subd6_4_61, List.forall_mem_cons.2 ⟨subd6_4_62, List.forall_mem_cons.2 ⟨subd6_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_64 : subd6_4 [-3, 1, 4] = true := by decide +kernel
theorem subd6_4_65 : subd6_4 [-3, 1, 5] = true := by decide +kernel
theorem subd6_4_66 : subd6_4 [-3, 2, -8] = true := by decide +kernel
theorem subd6_4_67 : subd6_4 [-3, 2, -7] = true := by decide +kernel
theorem subd6_4_68 : subd6_4 [-3, 2, -6] = true := by decide +kernel
theorem subd6_4_69 : subd6_4 [-3, 2, -5] = true := by decide +kernel
theorem subd6_4_70 : subd6_4 [-3, 2, -4] = true := by decide +kernel
theorem subd6_4_71 : subd6_4 [-3, 2, -3] = true := by decide +kernel
theorem subd6_4_72 : subd6_4 [-3, 2, -2] = true := by decide +kernel
theorem subd6_4_73 : subd6_4 [-3, 2, -1] = true := by decide +kernel
theorem subd6_4_74 : subd6_4 [-3, 2, 0] = true := by decide +kernel
theorem subd6_4_75 : subd6_4 [-3, 2, 1] = true := by decide +kernel
theorem subd6_4_76 : subd6_4 [-3, 2, 2] = true := by decide +kernel
theorem subd6_4_77 : subd6_4 [-3, 2, 3] = true := by decide +kernel
theorem subd6_4_78 : subd6_4 [-3, 2, 4] = true := by decide +kernel
theorem subd6_4_79 : subd6_4 [-3, 2, 5] = true := by decide +kernel
theorem subd6_4_80 : subd6_4 [-3, 3] = true := by decide +kernel
theorem subd6_4_81 : subd6_4 [-3, 4] = true := by decide +kernel
theorem subd6_4_82 : subd6_4 [-3, 5] = true := by decide +kernel
theorem subd6_4_83 : subd6_4 [-2, -7] = true := by decide +kernel
theorem subd6_4_84 : subd6_4 [-2, -6] = true := by decide +kernel
theorem subd6_4_85 : subd6_4 [-2, -5] = true := by decide +kernel
theorem subd6_4_86 : subd6_4 [-2, -4] = true := by decide +kernel
theorem subd6_4_87 : subd6_4 [-2, -3] = true := by decide +kernel
theorem subd6_4_88 : subd6_4 [-2, -2, -6] = true := by decide +kernel
theorem subd6_4_89 : subd6_4 [-2, -2, -5] = true := by decide +kernel
theorem subd6_4_90 : subd6_4 [-2, -2, -4] = true := by decide +kernel
theorem subd6_4_91 : subd6_4 [-2, -2, -3] = true := by decide +kernel
theorem subd6_4_92 : subd6_4 [-2, -2, -2] = true := by decide +kernel
theorem subd6_4_93 : subd6_4 [-2, -2, -1] = true := by decide +kernel
theorem subd6_4_94 : subd6_4 [-2, -2, 0] = true := by decide +kernel
theorem subd6_4_95 : subd6_4 [-2, -2, 1] = true := by decide +kernel
theorem sbd6_4_2 : ∀ q ∈ blkd6_4_2, subd6_4 q = true := by
  unfold blkd6_4_2
  exact List.forall_mem_cons.2 ⟨subd6_4_64, List.forall_mem_cons.2 ⟨subd6_4_65, List.forall_mem_cons.2 ⟨subd6_4_66, List.forall_mem_cons.2 ⟨subd6_4_67, List.forall_mem_cons.2 ⟨subd6_4_68, List.forall_mem_cons.2 ⟨subd6_4_69, List.forall_mem_cons.2 ⟨subd6_4_70, List.forall_mem_cons.2 ⟨subd6_4_71, List.forall_mem_cons.2 ⟨subd6_4_72, List.forall_mem_cons.2 ⟨subd6_4_73, List.forall_mem_cons.2 ⟨subd6_4_74, List.forall_mem_cons.2 ⟨subd6_4_75, List.forall_mem_cons.2 ⟨subd6_4_76, List.forall_mem_cons.2 ⟨subd6_4_77, List.forall_mem_cons.2 ⟨subd6_4_78, List.forall_mem_cons.2 ⟨subd6_4_79, List.forall_mem_cons.2 ⟨subd6_4_80, List.forall_mem_cons.2 ⟨subd6_4_81, List.forall_mem_cons.2 ⟨subd6_4_82, List.forall_mem_cons.2 ⟨subd6_4_83, List.forall_mem_cons.2 ⟨subd6_4_84, List.forall_mem_cons.2 ⟨subd6_4_85, List.forall_mem_cons.2 ⟨subd6_4_86, List.forall_mem_cons.2 ⟨subd6_4_87, List.forall_mem_cons.2 ⟨subd6_4_88, List.forall_mem_cons.2 ⟨subd6_4_89, List.forall_mem_cons.2 ⟨subd6_4_90, List.forall_mem_cons.2 ⟨subd6_4_91, List.forall_mem_cons.2 ⟨subd6_4_92, List.forall_mem_cons.2 ⟨subd6_4_93, List.forall_mem_cons.2 ⟨subd6_4_94, List.forall_mem_cons.2 ⟨subd6_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_96 : subd6_4 [-2, -2, 2] = true := by decide +kernel
theorem subd6_4_97 : subd6_4 [-2, -2, 3] = true := by decide +kernel
theorem subd6_4_98 : subd6_4 [-2, -2, 4] = true := by decide +kernel
theorem subd6_4_99 : subd6_4 [-2, -2, 5] = true := by decide +kernel
theorem subd6_4_100 : subd6_4 [-2, -2, 6] = true := by decide +kernel
theorem subd6_4_101 : subd6_4 [-2, -2, 7] = true := by decide +kernel
theorem subd6_4_102 : subd6_4 [-2, -1, -7] = true := by decide +kernel
theorem subd6_4_103 : subd6_4 [-2, -1, -6] = true := by decide +kernel
theorem subd6_4_104 : subd6_4 [-2, -1, -5] = true := by decide +kernel
theorem subd6_4_105 : subd6_4 [-2, -1, -4] = true := by decide +kernel
theorem subd6_4_106 : subd6_4 [-2, -1, -3] = true := by decide +kernel
theorem subd6_4_107 : subd6_4 [-2, -1, -2] = true := by decide +kernel
theorem subd6_4_108 : subd6_4 [-2, -1, -1] = true := by decide +kernel
theorem subd6_4_109 : subd6_4 [-2, -1, 0] = true := by decide +kernel
theorem subd6_4_110 : subd6_4 [-2, -1, 1] = true := by decide +kernel
theorem subd6_4_111 : subd6_4 [-2, -1, 2] = true := by decide +kernel
theorem subd6_4_112 : subd6_4 [-2, -1, 3] = true := by decide +kernel
theorem subd6_4_113 : subd6_4 [-2, -1, 4] = true := by decide +kernel
theorem subd6_4_114 : subd6_4 [-2, -1, 5] = true := by decide +kernel
theorem subd6_4_115 : subd6_4 [-2, -1, 6] = true := by decide +kernel
theorem subd6_4_116 : subd6_4 [-2, -1, 7] = true := by decide +kernel
theorem subd6_4_117 : subd6_4 [-2, 0, -8] = true := by decide +kernel
theorem subd6_4_118 : subd6_4 [-2, 0, -7] = true := by decide +kernel
theorem subd6_4_119 : subd6_4 [-2, 0, -6] = true := by decide +kernel
theorem subd6_4_120 : subd6_4 [-2, 0, -5] = true := by decide +kernel
theorem subd6_4_121 : subd6_4 [-2, 0, -4] = true := by decide +kernel
theorem subd6_4_122 : subd6_4 [-2, 0, -3] = true := by decide +kernel
theorem subd6_4_123 : subd6_4 [-2, 0, -2] = true := by decide +kernel
theorem subd6_4_124 : subd6_4 [-2, 0, -1] = true := by decide +kernel
theorem subd6_4_125 : subd6_4 [-2, 0, 0] = true := by decide +kernel
theorem subd6_4_126 : subd6_4 [-2, 0, 1] = true := by decide +kernel
theorem subd6_4_127 : subd6_4 [-2, 0, 2] = true := by decide +kernel
theorem sbd6_4_3 : ∀ q ∈ blkd6_4_3, subd6_4 q = true := by
  unfold blkd6_4_3
  exact List.forall_mem_cons.2 ⟨subd6_4_96, List.forall_mem_cons.2 ⟨subd6_4_97, List.forall_mem_cons.2 ⟨subd6_4_98, List.forall_mem_cons.2 ⟨subd6_4_99, List.forall_mem_cons.2 ⟨subd6_4_100, List.forall_mem_cons.2 ⟨subd6_4_101, List.forall_mem_cons.2 ⟨subd6_4_102, List.forall_mem_cons.2 ⟨subd6_4_103, List.forall_mem_cons.2 ⟨subd6_4_104, List.forall_mem_cons.2 ⟨subd6_4_105, List.forall_mem_cons.2 ⟨subd6_4_106, List.forall_mem_cons.2 ⟨subd6_4_107, List.forall_mem_cons.2 ⟨subd6_4_108, List.forall_mem_cons.2 ⟨subd6_4_109, List.forall_mem_cons.2 ⟨subd6_4_110, List.forall_mem_cons.2 ⟨subd6_4_111, List.forall_mem_cons.2 ⟨subd6_4_112, List.forall_mem_cons.2 ⟨subd6_4_113, List.forall_mem_cons.2 ⟨subd6_4_114, List.forall_mem_cons.2 ⟨subd6_4_115, List.forall_mem_cons.2 ⟨subd6_4_116, List.forall_mem_cons.2 ⟨subd6_4_117, List.forall_mem_cons.2 ⟨subd6_4_118, List.forall_mem_cons.2 ⟨subd6_4_119, List.forall_mem_cons.2 ⟨subd6_4_120, List.forall_mem_cons.2 ⟨subd6_4_121, List.forall_mem_cons.2 ⟨subd6_4_122, List.forall_mem_cons.2 ⟨subd6_4_123, List.forall_mem_cons.2 ⟨subd6_4_124, List.forall_mem_cons.2 ⟨subd6_4_125, List.forall_mem_cons.2 ⟨subd6_4_126, List.forall_mem_cons.2 ⟨subd6_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_128 : subd6_4 [-2, 0, 3] = true := by decide +kernel
theorem subd6_4_129 : subd6_4 [-2, 0, 4] = true := by decide +kernel
theorem subd6_4_130 : subd6_4 [-2, 0, 5] = true := by decide +kernel
theorem subd6_4_131 : subd6_4 [-2, 0, 6] = true := by decide +kernel
theorem subd6_4_132 : subd6_4 [-2, 1, -8] = true := by decide +kernel
theorem subd6_4_133 : subd6_4 [-2, 1, -7] = true := by decide +kernel
theorem subd6_4_134 : subd6_4 [-2, 1, -6] = true := by decide +kernel
theorem subd6_4_135 : subd6_4 [-2, 1, -5] = true := by decide +kernel
theorem subd6_4_136 : subd6_4 [-2, 1, -4] = true := by decide +kernel
theorem subd6_4_137 : subd6_4 [-2, 1, -3] = true := by decide +kernel
theorem subd6_4_138 : subd6_4 [-2, 1, -2] = true := by decide +kernel
theorem subd6_4_139 : subd6_4 [-2, 1, -1] = true := by decide +kernel
theorem subd6_4_140 : subd6_4 [-2, 1, 0] = true := by decide +kernel
theorem subd6_4_141 : subd6_4 [-2, 1, 1] = true := by decide +kernel
theorem subd6_4_142 : subd6_4 [-2, 1, 2] = true := by decide +kernel
theorem subd6_4_143 : subd6_4 [-2, 1, 3] = true := by decide +kernel
theorem subd6_4_144 : subd6_4 [-2, 1, 4] = true := by decide +kernel
theorem subd6_4_145 : subd6_4 [-2, 1, 5] = true := by decide +kernel
theorem subd6_4_146 : subd6_4 [-2, 1, 6] = true := by decide +kernel
theorem subd6_4_147 : subd6_4 [-2, 2, -8] = true := by decide +kernel
theorem subd6_4_148 : subd6_4 [-2, 2, -7] = true := by decide +kernel
theorem subd6_4_149 : subd6_4 [-2, 2, -6] = true := by decide +kernel
theorem subd6_4_150 : subd6_4 [-2, 2, -5] = true := by decide +kernel
theorem subd6_4_151 : subd6_4 [-2, 2, -4] = true := by decide +kernel
theorem subd6_4_152 : subd6_4 [-2, 2, -3] = true := by decide +kernel
theorem subd6_4_153 : subd6_4 [-2, 2, -2] = true := by decide +kernel
theorem subd6_4_154 : subd6_4 [-2, 2, -1] = true := by decide +kernel
theorem subd6_4_155 : subd6_4 [-2, 2, 0] = true := by decide +kernel
theorem subd6_4_156 : subd6_4 [-2, 2, 1] = true := by decide +kernel
theorem subd6_4_157 : subd6_4 [-2, 2, 2] = true := by decide +kernel
theorem subd6_4_158 : subd6_4 [-2, 2, 3] = true := by decide +kernel
theorem subd6_4_159 : subd6_4 [-2, 2, 4] = true := by decide +kernel
theorem sbd6_4_4 : ∀ q ∈ blkd6_4_4, subd6_4 q = true := by
  unfold blkd6_4_4
  exact List.forall_mem_cons.2 ⟨subd6_4_128, List.forall_mem_cons.2 ⟨subd6_4_129, List.forall_mem_cons.2 ⟨subd6_4_130, List.forall_mem_cons.2 ⟨subd6_4_131, List.forall_mem_cons.2 ⟨subd6_4_132, List.forall_mem_cons.2 ⟨subd6_4_133, List.forall_mem_cons.2 ⟨subd6_4_134, List.forall_mem_cons.2 ⟨subd6_4_135, List.forall_mem_cons.2 ⟨subd6_4_136, List.forall_mem_cons.2 ⟨subd6_4_137, List.forall_mem_cons.2 ⟨subd6_4_138, List.forall_mem_cons.2 ⟨subd6_4_139, List.forall_mem_cons.2 ⟨subd6_4_140, List.forall_mem_cons.2 ⟨subd6_4_141, List.forall_mem_cons.2 ⟨subd6_4_142, List.forall_mem_cons.2 ⟨subd6_4_143, List.forall_mem_cons.2 ⟨subd6_4_144, List.forall_mem_cons.2 ⟨subd6_4_145, List.forall_mem_cons.2 ⟨subd6_4_146, List.forall_mem_cons.2 ⟨subd6_4_147, List.forall_mem_cons.2 ⟨subd6_4_148, List.forall_mem_cons.2 ⟨subd6_4_149, List.forall_mem_cons.2 ⟨subd6_4_150, List.forall_mem_cons.2 ⟨subd6_4_151, List.forall_mem_cons.2 ⟨subd6_4_152, List.forall_mem_cons.2 ⟨subd6_4_153, List.forall_mem_cons.2 ⟨subd6_4_154, List.forall_mem_cons.2 ⟨subd6_4_155, List.forall_mem_cons.2 ⟨subd6_4_156, List.forall_mem_cons.2 ⟨subd6_4_157, List.forall_mem_cons.2 ⟨subd6_4_158, List.forall_mem_cons.2 ⟨subd6_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_160 : subd6_4 [-2, 2, 5] = true := by decide +kernel
theorem subd6_4_161 : subd6_4 [-2, 3] = true := by decide +kernel
theorem subd6_4_162 : subd6_4 [-2, 4] = true := by decide +kernel
theorem subd6_4_163 : subd6_4 [-2, 5] = true := by decide +kernel
theorem subd6_4_164 : subd6_4 [-2, 6] = true := by decide +kernel
theorem subd6_4_165 : subd6_4 [-1, -7] = true := by decide +kernel
theorem subd6_4_166 : subd6_4 [-1, -6] = true := by decide +kernel
theorem subd6_4_167 : subd6_4 [-1, -5] = true := by decide +kernel
theorem subd6_4_168 : subd6_4 [-1, -4] = true := by decide +kernel
theorem subd6_4_169 : subd6_4 [-1, -3, -6] = true := by decide +kernel
theorem subd6_4_170 : subd6_4 [-1, -3, -5] = true := by decide +kernel
theorem subd6_4_171 : subd6_4 [-1, -3, -4] = true := by decide +kernel
theorem subd6_4_172 : subd6_4 [-1, -3, -3] = true := by decide +kernel
theorem subd6_4_173 : subd6_4 [-1, -3, -2] = true := by decide +kernel
theorem subd6_4_174 : subd6_4 [-1, -3, -1] = true := by decide +kernel
theorem subd6_4_175 : subd6_4 [-1, -3, 0] = true := by decide +kernel
theorem subd6_4_176 : subd6_4 [-1, -3, 1] = true := by decide +kernel
theorem subd6_4_177 : subd6_4 [-1, -3, 2] = true := by decide +kernel
theorem subd6_4_178 : subd6_4 [-1, -3, 3] = true := by decide +kernel
theorem subd6_4_179 : subd6_4 [-1, -3, 4] = true := by decide +kernel
theorem subd6_4_180 : subd6_4 [-1, -3, 5] = true := by decide +kernel
theorem subd6_4_181 : subd6_4 [-1, -3, 6] = true := by decide +kernel
theorem subd6_4_182 : subd6_4 [-1, -3, 7] = true := by decide +kernel
theorem subd6_4_183 : subd6_4 [-1, -2, -7] = true := by decide +kernel
theorem subd6_4_184 : subd6_4 [-1, -2, -6] = true := by decide +kernel
theorem subd6_4_185 : subd6_4 [-1, -2, -5] = true := by decide +kernel
theorem subd6_4_186 : subd6_4 [-1, -2, -4] = true := by decide +kernel
theorem subd6_4_187 : subd6_4 [-1, -2, -3] = true := by decide +kernel
theorem subd6_4_188 : subd6_4 [-1, -2, -2] = true := by decide +kernel
theorem subd6_4_189 : subd6_4 [-1, -2, -1] = true := by decide +kernel
theorem subd6_4_190 : subd6_4 [-1, -2, 0] = true := by decide +kernel
theorem subd6_4_191 : subd6_4 [-1, -2, 1] = true := by decide +kernel
theorem sbd6_4_5 : ∀ q ∈ blkd6_4_5, subd6_4 q = true := by
  unfold blkd6_4_5
  exact List.forall_mem_cons.2 ⟨subd6_4_160, List.forall_mem_cons.2 ⟨subd6_4_161, List.forall_mem_cons.2 ⟨subd6_4_162, List.forall_mem_cons.2 ⟨subd6_4_163, List.forall_mem_cons.2 ⟨subd6_4_164, List.forall_mem_cons.2 ⟨subd6_4_165, List.forall_mem_cons.2 ⟨subd6_4_166, List.forall_mem_cons.2 ⟨subd6_4_167, List.forall_mem_cons.2 ⟨subd6_4_168, List.forall_mem_cons.2 ⟨subd6_4_169, List.forall_mem_cons.2 ⟨subd6_4_170, List.forall_mem_cons.2 ⟨subd6_4_171, List.forall_mem_cons.2 ⟨subd6_4_172, List.forall_mem_cons.2 ⟨subd6_4_173, List.forall_mem_cons.2 ⟨subd6_4_174, List.forall_mem_cons.2 ⟨subd6_4_175, List.forall_mem_cons.2 ⟨subd6_4_176, List.forall_mem_cons.2 ⟨subd6_4_177, List.forall_mem_cons.2 ⟨subd6_4_178, List.forall_mem_cons.2 ⟨subd6_4_179, List.forall_mem_cons.2 ⟨subd6_4_180, List.forall_mem_cons.2 ⟨subd6_4_181, List.forall_mem_cons.2 ⟨subd6_4_182, List.forall_mem_cons.2 ⟨subd6_4_183, List.forall_mem_cons.2 ⟨subd6_4_184, List.forall_mem_cons.2 ⟨subd6_4_185, List.forall_mem_cons.2 ⟨subd6_4_186, List.forall_mem_cons.2 ⟨subd6_4_187, List.forall_mem_cons.2 ⟨subd6_4_188, List.forall_mem_cons.2 ⟨subd6_4_189, List.forall_mem_cons.2 ⟨subd6_4_190, List.forall_mem_cons.2 ⟨subd6_4_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_192 : subd6_4 [-1, -2, 2] = true := by decide +kernel
theorem subd6_4_193 : subd6_4 [-1, -2, 3] = true := by decide +kernel
theorem subd6_4_194 : subd6_4 [-1, -2, 4] = true := by decide +kernel
theorem subd6_4_195 : subd6_4 [-1, -2, 5] = true := by decide +kernel
theorem subd6_4_196 : subd6_4 [-1, -2, 6] = true := by decide +kernel
theorem subd6_4_197 : subd6_4 [-1, -2, 7] = true := by decide +kernel
theorem subd6_4_198 : subd6_4 [-1, -1, -7] = true := by decide +kernel
theorem subd6_4_199 : subd6_4 [-1, -1, -6] = true := by decide +kernel
theorem subd6_4_200 : subd6_4 [-1, -1, -5] = true := by decide +kernel
theorem subd6_4_201 : subd6_4 [-1, -1, -4] = true := by decide +kernel
theorem subd6_4_202 : subd6_4 [-1, -1, -3] = true := by decide +kernel
theorem subd6_4_203 : subd6_4 [-1, -1, -2] = true := by decide +kernel
theorem subd6_4_204 : subd6_4 [-1, -1, -1] = true := by decide +kernel
theorem subd6_4_205 : subd6_4 [-1, -1, 0] = true := by decide +kernel
theorem subd6_4_206 : subd6_4 [-1, -1, 1] = true := by decide +kernel
theorem subd6_4_207 : subd6_4 [-1, -1, 2] = true := by decide +kernel
theorem subd6_4_208 : subd6_4 [-1, -1, 3] = true := by decide +kernel
theorem subd6_4_209 : subd6_4 [-1, -1, 4] = true := by decide +kernel
theorem subd6_4_210 : subd6_4 [-1, -1, 5] = true := by decide +kernel
theorem subd6_4_211 : subd6_4 [-1, -1, 6] = true := by decide +kernel
theorem subd6_4_212 : subd6_4 [-1, -1, 7] = true := by decide +kernel
theorem subd6_4_213 : subd6_4 [-1, 0, -8] = true := by decide +kernel
theorem subd6_4_214 : subd6_4 [-1, 0, -7] = true := by decide +kernel
theorem subd6_4_215 : subd6_4 [-1, 0, -6] = true := by decide +kernel
theorem subd6_4_216 : subd6_4 [-1, 0, -5] = true := by decide +kernel
theorem subd6_4_217 : subd6_4 [-1, 0, -4] = true := by decide +kernel
theorem subd6_4_218 : subd6_4 [-1, 0, -3] = true := by decide +kernel
theorem subd6_4_219 : subd6_4 [-1, 0, -2] = true := by decide +kernel
theorem subd6_4_220 : subd6_4 [-1, 0, -1] = true := by decide +kernel
theorem subd6_4_221 : subd6_4 [-1, 0, 0] = true := by decide +kernel
theorem subd6_4_222 : subd6_4 [-1, 0, 1] = true := by decide +kernel
theorem subd6_4_223 : subd6_4 [-1, 0, 2] = true := by decide +kernel
theorem sbd6_4_6 : ∀ q ∈ blkd6_4_6, subd6_4 q = true := by
  unfold blkd6_4_6
  exact List.forall_mem_cons.2 ⟨subd6_4_192, List.forall_mem_cons.2 ⟨subd6_4_193, List.forall_mem_cons.2 ⟨subd6_4_194, List.forall_mem_cons.2 ⟨subd6_4_195, List.forall_mem_cons.2 ⟨subd6_4_196, List.forall_mem_cons.2 ⟨subd6_4_197, List.forall_mem_cons.2 ⟨subd6_4_198, List.forall_mem_cons.2 ⟨subd6_4_199, List.forall_mem_cons.2 ⟨subd6_4_200, List.forall_mem_cons.2 ⟨subd6_4_201, List.forall_mem_cons.2 ⟨subd6_4_202, List.forall_mem_cons.2 ⟨subd6_4_203, List.forall_mem_cons.2 ⟨subd6_4_204, List.forall_mem_cons.2 ⟨subd6_4_205, List.forall_mem_cons.2 ⟨subd6_4_206, List.forall_mem_cons.2 ⟨subd6_4_207, List.forall_mem_cons.2 ⟨subd6_4_208, List.forall_mem_cons.2 ⟨subd6_4_209, List.forall_mem_cons.2 ⟨subd6_4_210, List.forall_mem_cons.2 ⟨subd6_4_211, List.forall_mem_cons.2 ⟨subd6_4_212, List.forall_mem_cons.2 ⟨subd6_4_213, List.forall_mem_cons.2 ⟨subd6_4_214, List.forall_mem_cons.2 ⟨subd6_4_215, List.forall_mem_cons.2 ⟨subd6_4_216, List.forall_mem_cons.2 ⟨subd6_4_217, List.forall_mem_cons.2 ⟨subd6_4_218, List.forall_mem_cons.2 ⟨subd6_4_219, List.forall_mem_cons.2 ⟨subd6_4_220, List.forall_mem_cons.2 ⟨subd6_4_221, List.forall_mem_cons.2 ⟨subd6_4_222, List.forall_mem_cons.2 ⟨subd6_4_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_224 : subd6_4 [-1, 0, 3] = true := by decide +kernel
theorem subd6_4_225 : subd6_4 [-1, 0, 4] = true := by decide +kernel
theorem subd6_4_226 : subd6_4 [-1, 0, 5] = true := by decide +kernel
theorem subd6_4_227 : subd6_4 [-1, 0, 6] = true := by decide +kernel
theorem subd6_4_228 : subd6_4 [-1, 0, 7] = true := by decide +kernel
theorem subd6_4_229 : subd6_4 [-1, 1, -8] = true := by decide +kernel
theorem subd6_4_230 : subd6_4 [-1, 1, -7] = true := by decide +kernel
theorem subd6_4_231 : subd6_4 [-1, 1, -6] = true := by decide +kernel
theorem subd6_4_232 : subd6_4 [-1, 1, -5] = true := by decide +kernel
theorem subd6_4_233 : subd6_4 [-1, 1, -4] = true := by decide +kernel
theorem subd6_4_234 : subd6_4 [-1, 1, -3] = true := by decide +kernel
theorem subd6_4_235 : subd6_4 [-1, 1, -2] = true := by decide +kernel
theorem subd6_4_236 : subd6_4 [-1, 1, -1] = true := by decide +kernel
theorem subd6_4_237 : subd6_4 [-1, 1, 0] = true := by decide +kernel
theorem subd6_4_238 : subd6_4 [-1, 1, 1] = true := by decide +kernel
theorem subd6_4_239 : subd6_4 [-1, 1, 2] = true := by decide +kernel
theorem subd6_4_240 : subd6_4 [-1, 1, 3] = true := by decide +kernel
theorem subd6_4_241 : subd6_4 [-1, 1, 4] = true := by decide +kernel
theorem subd6_4_242 : subd6_4 [-1, 1, 5] = true := by decide +kernel
theorem subd6_4_243 : subd6_4 [-1, 1, 6] = true := by decide +kernel
theorem subd6_4_244 : subd6_4 [-1, 2, -8] = true := by decide +kernel
theorem subd6_4_245 : subd6_4 [-1, 2, -7] = true := by decide +kernel
theorem subd6_4_246 : subd6_4 [-1, 2, -6] = true := by decide +kernel
theorem subd6_4_247 : subd6_4 [-1, 2, -5] = true := by decide +kernel
theorem subd6_4_248 : subd6_4 [-1, 2, -4] = true := by decide +kernel
theorem subd6_4_249 : subd6_4 [-1, 2, -3] = true := by decide +kernel
theorem subd6_4_250 : subd6_4 [-1, 2, -2] = true := by decide +kernel
theorem subd6_4_251 : subd6_4 [-1, 2, -1] = true := by decide +kernel
theorem subd6_4_252 : subd6_4 [-1, 2, 0] = true := by decide +kernel
theorem subd6_4_253 : subd6_4 [-1, 2, 1] = true := by decide +kernel
theorem subd6_4_254 : subd6_4 [-1, 2, 2] = true := by decide +kernel
theorem subd6_4_255 : subd6_4 [-1, 2, 3] = true := by decide +kernel
theorem sbd6_4_7 : ∀ q ∈ blkd6_4_7, subd6_4 q = true := by
  unfold blkd6_4_7
  exact List.forall_mem_cons.2 ⟨subd6_4_224, List.forall_mem_cons.2 ⟨subd6_4_225, List.forall_mem_cons.2 ⟨subd6_4_226, List.forall_mem_cons.2 ⟨subd6_4_227, List.forall_mem_cons.2 ⟨subd6_4_228, List.forall_mem_cons.2 ⟨subd6_4_229, List.forall_mem_cons.2 ⟨subd6_4_230, List.forall_mem_cons.2 ⟨subd6_4_231, List.forall_mem_cons.2 ⟨subd6_4_232, List.forall_mem_cons.2 ⟨subd6_4_233, List.forall_mem_cons.2 ⟨subd6_4_234, List.forall_mem_cons.2 ⟨subd6_4_235, List.forall_mem_cons.2 ⟨subd6_4_236, List.forall_mem_cons.2 ⟨subd6_4_237, List.forall_mem_cons.2 ⟨subd6_4_238, List.forall_mem_cons.2 ⟨subd6_4_239, List.forall_mem_cons.2 ⟨subd6_4_240, List.forall_mem_cons.2 ⟨subd6_4_241, List.forall_mem_cons.2 ⟨subd6_4_242, List.forall_mem_cons.2 ⟨subd6_4_243, List.forall_mem_cons.2 ⟨subd6_4_244, List.forall_mem_cons.2 ⟨subd6_4_245, List.forall_mem_cons.2 ⟨subd6_4_246, List.forall_mem_cons.2 ⟨subd6_4_247, List.forall_mem_cons.2 ⟨subd6_4_248, List.forall_mem_cons.2 ⟨subd6_4_249, List.forall_mem_cons.2 ⟨subd6_4_250, List.forall_mem_cons.2 ⟨subd6_4_251, List.forall_mem_cons.2 ⟨subd6_4_252, List.forall_mem_cons.2 ⟨subd6_4_253, List.forall_mem_cons.2 ⟨subd6_4_254, List.forall_mem_cons.2 ⟨subd6_4_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_256 : subd6_4 [-1, 2, 4] = true := by decide +kernel
theorem subd6_4_257 : subd6_4 [-1, 2, 5] = true := by decide +kernel
theorem subd6_4_258 : subd6_4 [-1, 2, 6] = true := by decide +kernel
theorem subd6_4_259 : subd6_4 [-1, 3, -8] = true := by decide +kernel
theorem subd6_4_260 : subd6_4 [-1, 3, -7] = true := by decide +kernel
theorem subd6_4_261 : subd6_4 [-1, 3, -6] = true := by decide +kernel
theorem subd6_4_262 : subd6_4 [-1, 3, -5] = true := by decide +kernel
theorem subd6_4_263 : subd6_4 [-1, 3, -4] = true := by decide +kernel
theorem subd6_4_264 : subd6_4 [-1, 3, -3] = true := by decide +kernel
theorem subd6_4_265 : subd6_4 [-1, 3, -2] = true := by decide +kernel
theorem subd6_4_266 : subd6_4 [-1, 3, -1] = true := by decide +kernel
theorem subd6_4_267 : subd6_4 [-1, 3, 0] = true := by decide +kernel
theorem subd6_4_268 : subd6_4 [-1, 3, 1] = true := by decide +kernel
theorem subd6_4_269 : subd6_4 [-1, 3, 2] = true := by decide +kernel
theorem subd6_4_270 : subd6_4 [-1, 3, 3] = true := by decide +kernel
theorem subd6_4_271 : subd6_4 [-1, 3, 4] = true := by decide +kernel
theorem subd6_4_272 : subd6_4 [-1, 3, 5] = true := by decide +kernel
theorem subd6_4_273 : subd6_4 [-1, 4] = true := by decide +kernel
theorem subd6_4_274 : subd6_4 [-1, 5] = true := by decide +kernel
theorem subd6_4_275 : subd6_4 [-1, 6] = true := by decide +kernel
theorem subd6_4_276 : subd6_4 [0, -7] = true := by decide +kernel
theorem subd6_4_277 : subd6_4 [0, -6] = true := by decide +kernel
theorem subd6_4_278 : subd6_4 [0, -5] = true := by decide +kernel
theorem subd6_4_279 : subd6_4 [0, -4] = true := by decide +kernel
theorem subd6_4_280 : subd6_4 [0, -3, -6] = true := by decide +kernel
theorem subd6_4_281 : subd6_4 [0, -3, -5] = true := by decide +kernel
theorem subd6_4_282 : subd6_4 [0, -3, -4] = true := by decide +kernel
theorem subd6_4_283 : subd6_4 [0, -3, -3] = true := by decide +kernel
theorem subd6_4_284 : subd6_4 [0, -3, -2] = true := by decide +kernel
theorem subd6_4_285 : subd6_4 [0, -3, -1] = true := by decide +kernel
theorem subd6_4_286 : subd6_4 [0, -3, 0] = true := by decide +kernel
theorem subd6_4_287 : subd6_4 [0, -3, 1] = true := by decide +kernel
theorem sbd6_4_8 : ∀ q ∈ blkd6_4_8, subd6_4 q = true := by
  unfold blkd6_4_8
  exact List.forall_mem_cons.2 ⟨subd6_4_256, List.forall_mem_cons.2 ⟨subd6_4_257, List.forall_mem_cons.2 ⟨subd6_4_258, List.forall_mem_cons.2 ⟨subd6_4_259, List.forall_mem_cons.2 ⟨subd6_4_260, List.forall_mem_cons.2 ⟨subd6_4_261, List.forall_mem_cons.2 ⟨subd6_4_262, List.forall_mem_cons.2 ⟨subd6_4_263, List.forall_mem_cons.2 ⟨subd6_4_264, List.forall_mem_cons.2 ⟨subd6_4_265, List.forall_mem_cons.2 ⟨subd6_4_266, List.forall_mem_cons.2 ⟨subd6_4_267, List.forall_mem_cons.2 ⟨subd6_4_268, List.forall_mem_cons.2 ⟨subd6_4_269, List.forall_mem_cons.2 ⟨subd6_4_270, List.forall_mem_cons.2 ⟨subd6_4_271, List.forall_mem_cons.2 ⟨subd6_4_272, List.forall_mem_cons.2 ⟨subd6_4_273, List.forall_mem_cons.2 ⟨subd6_4_274, List.forall_mem_cons.2 ⟨subd6_4_275, List.forall_mem_cons.2 ⟨subd6_4_276, List.forall_mem_cons.2 ⟨subd6_4_277, List.forall_mem_cons.2 ⟨subd6_4_278, List.forall_mem_cons.2 ⟨subd6_4_279, List.forall_mem_cons.2 ⟨subd6_4_280, List.forall_mem_cons.2 ⟨subd6_4_281, List.forall_mem_cons.2 ⟨subd6_4_282, List.forall_mem_cons.2 ⟨subd6_4_283, List.forall_mem_cons.2 ⟨subd6_4_284, List.forall_mem_cons.2 ⟨subd6_4_285, List.forall_mem_cons.2 ⟨subd6_4_286, List.forall_mem_cons.2 ⟨subd6_4_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_288 : subd6_4 [0, -3, 2] = true := by decide +kernel
theorem subd6_4_289 : subd6_4 [0, -3, 3] = true := by decide +kernel
theorem subd6_4_290 : subd6_4 [0, -3, 4] = true := by decide +kernel
theorem subd6_4_291 : subd6_4 [0, -3, 5] = true := by decide +kernel
theorem subd6_4_292 : subd6_4 [0, -3, 6] = true := by decide +kernel
theorem subd6_4_293 : subd6_4 [0, -3, 7] = true := by decide +kernel
theorem subd6_4_294 : subd6_4 [0, -2, -7] = true := by decide +kernel
theorem subd6_4_295 : subd6_4 [0, -2, -6] = true := by decide +kernel
theorem subd6_4_296 : subd6_4 [0, -2, -5] = true := by decide +kernel
theorem subd6_4_297 : subd6_4 [0, -2, -4] = true := by decide +kernel
theorem subd6_4_298 : subd6_4 [0, -2, -3] = true := by decide +kernel
theorem subd6_4_299 : subd6_4 [0, -2, -2] = true := by decide +kernel
theorem subd6_4_300 : subd6_4 [0, -2, -1] = true := by decide +kernel
theorem subd6_4_301 : subd6_4 [0, -2, 0] = true := by decide +kernel
theorem subd6_4_302 : subd6_4 [0, -2, 1] = true := by decide +kernel
theorem subd6_4_303 : subd6_4 [0, -2, 2] = true := by decide +kernel
theorem subd6_4_304 : subd6_4 [0, -2, 3] = true := by decide +kernel
theorem subd6_4_305 : subd6_4 [0, -2, 4] = true := by decide +kernel
theorem subd6_4_306 : subd6_4 [0, -2, 5] = true := by decide +kernel
theorem subd6_4_307 : subd6_4 [0, -2, 6] = true := by decide +kernel
theorem subd6_4_308 : subd6_4 [0, -2, 7] = true := by decide +kernel
theorem subd6_4_309 : subd6_4 [0, -1, -7] = true := by decide +kernel
theorem subd6_4_310 : subd6_4 [0, -1, -6] = true := by decide +kernel
theorem subd6_4_311 : subd6_4 [0, -1, -5] = true := by decide +kernel
theorem subd6_4_312 : subd6_4 [0, -1, -4] = true := by decide +kernel
theorem subd6_4_313 : subd6_4 [0, -1, -3] = true := by decide +kernel
theorem subd6_4_314 : subd6_4 [0, -1, -2] = true := by decide +kernel
theorem subd6_4_315 : subd6_4 [0, -1, -1] = true := by decide +kernel
theorem subd6_4_316 : subd6_4 [0, -1, 0] = true := by decide +kernel
theorem subd6_4_317 : subd6_4 [0, -1, 1] = true := by decide +kernel
theorem subd6_4_318 : subd6_4 [0, -1, 2] = true := by decide +kernel
theorem subd6_4_319 : subd6_4 [0, -1, 3] = true := by decide +kernel
theorem sbd6_4_9 : ∀ q ∈ blkd6_4_9, subd6_4 q = true := by
  unfold blkd6_4_9
  exact List.forall_mem_cons.2 ⟨subd6_4_288, List.forall_mem_cons.2 ⟨subd6_4_289, List.forall_mem_cons.2 ⟨subd6_4_290, List.forall_mem_cons.2 ⟨subd6_4_291, List.forall_mem_cons.2 ⟨subd6_4_292, List.forall_mem_cons.2 ⟨subd6_4_293, List.forall_mem_cons.2 ⟨subd6_4_294, List.forall_mem_cons.2 ⟨subd6_4_295, List.forall_mem_cons.2 ⟨subd6_4_296, List.forall_mem_cons.2 ⟨subd6_4_297, List.forall_mem_cons.2 ⟨subd6_4_298, List.forall_mem_cons.2 ⟨subd6_4_299, List.forall_mem_cons.2 ⟨subd6_4_300, List.forall_mem_cons.2 ⟨subd6_4_301, List.forall_mem_cons.2 ⟨subd6_4_302, List.forall_mem_cons.2 ⟨subd6_4_303, List.forall_mem_cons.2 ⟨subd6_4_304, List.forall_mem_cons.2 ⟨subd6_4_305, List.forall_mem_cons.2 ⟨subd6_4_306, List.forall_mem_cons.2 ⟨subd6_4_307, List.forall_mem_cons.2 ⟨subd6_4_308, List.forall_mem_cons.2 ⟨subd6_4_309, List.forall_mem_cons.2 ⟨subd6_4_310, List.forall_mem_cons.2 ⟨subd6_4_311, List.forall_mem_cons.2 ⟨subd6_4_312, List.forall_mem_cons.2 ⟨subd6_4_313, List.forall_mem_cons.2 ⟨subd6_4_314, List.forall_mem_cons.2 ⟨subd6_4_315, List.forall_mem_cons.2 ⟨subd6_4_316, List.forall_mem_cons.2 ⟨subd6_4_317, List.forall_mem_cons.2 ⟨subd6_4_318, List.forall_mem_cons.2 ⟨subd6_4_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_320 : subd6_4 [0, -1, 4] = true := by decide +kernel
theorem subd6_4_321 : subd6_4 [0, -1, 5] = true := by decide +kernel
theorem subd6_4_322 : subd6_4 [0, -1, 6] = true := by decide +kernel
theorem subd6_4_323 : subd6_4 [0, -1, 7] = true := by decide +kernel
theorem subd6_4_324 : subd6_4 [0, 0, -8] = true := by decide +kernel
theorem subd6_4_325 : subd6_4 [0, 0, -7] = true := by decide +kernel
theorem subd6_4_326 : subd6_4 [0, 0, -6] = true := by decide +kernel
theorem subd6_4_327 : subd6_4 [0, 0, -5] = true := by decide +kernel
theorem subd6_4_328 : subd6_4 [0, 0, -4] = true := by decide +kernel
theorem subd6_4_329 : subd6_4 [0, 0, -3] = true := by decide +kernel
theorem subd6_4_330 : subd6_4 [0, 0, -2] = true := by decide +kernel
theorem subd6_4_331 : subd6_4 [0, 0, -1] = true := by decide +kernel
theorem subd6_4_332 : subd6_4 [0, 0, 0] = true := by decide +kernel
theorem subd6_4_333 : subd6_4 [0, 0, 1] = true := by decide +kernel
theorem subd6_4_334 : subd6_4 [0, 0, 2] = true := by decide +kernel
theorem subd6_4_335 : subd6_4 [0, 0, 3] = true := by decide +kernel
theorem subd6_4_336 : subd6_4 [0, 0, 4] = true := by decide +kernel
theorem subd6_4_337 : subd6_4 [0, 0, 5] = true := by decide +kernel
theorem subd6_4_338 : subd6_4 [0, 0, 6] = true := by decide +kernel
theorem subd6_4_339 : subd6_4 [0, 0, 7] = true := by decide +kernel
theorem subd6_4_340 : subd6_4 [0, 1, -8] = true := by decide +kernel
theorem subd6_4_341 : subd6_4 [0, 1, -7] = true := by decide +kernel
theorem subd6_4_342 : subd6_4 [0, 1, -6] = true := by decide +kernel
theorem subd6_4_343 : subd6_4 [0, 1, -5] = true := by decide +kernel
theorem subd6_4_344 : subd6_4 [0, 1, -4] = true := by decide +kernel
theorem subd6_4_345 : subd6_4 [0, 1, -3] = true := by decide +kernel
theorem subd6_4_346 : subd6_4 [0, 1, -2] = true := by decide +kernel
theorem subd6_4_347 : subd6_4 [0, 1, -1] = true := by decide +kernel
theorem subd6_4_348 : subd6_4 [0, 1, 0] = true := by decide +kernel
theorem subd6_4_349 : subd6_4 [0, 1, 1] = true := by decide +kernel
theorem subd6_4_350 : subd6_4 [0, 1, 2] = true := by decide +kernel
theorem subd6_4_351 : subd6_4 [0, 1, 3] = true := by decide +kernel
theorem sbd6_4_10 : ∀ q ∈ blkd6_4_10, subd6_4 q = true := by
  unfold blkd6_4_10
  exact List.forall_mem_cons.2 ⟨subd6_4_320, List.forall_mem_cons.2 ⟨subd6_4_321, List.forall_mem_cons.2 ⟨subd6_4_322, List.forall_mem_cons.2 ⟨subd6_4_323, List.forall_mem_cons.2 ⟨subd6_4_324, List.forall_mem_cons.2 ⟨subd6_4_325, List.forall_mem_cons.2 ⟨subd6_4_326, List.forall_mem_cons.2 ⟨subd6_4_327, List.forall_mem_cons.2 ⟨subd6_4_328, List.forall_mem_cons.2 ⟨subd6_4_329, List.forall_mem_cons.2 ⟨subd6_4_330, List.forall_mem_cons.2 ⟨subd6_4_331, List.forall_mem_cons.2 ⟨subd6_4_332, List.forall_mem_cons.2 ⟨subd6_4_333, List.forall_mem_cons.2 ⟨subd6_4_334, List.forall_mem_cons.2 ⟨subd6_4_335, List.forall_mem_cons.2 ⟨subd6_4_336, List.forall_mem_cons.2 ⟨subd6_4_337, List.forall_mem_cons.2 ⟨subd6_4_338, List.forall_mem_cons.2 ⟨subd6_4_339, List.forall_mem_cons.2 ⟨subd6_4_340, List.forall_mem_cons.2 ⟨subd6_4_341, List.forall_mem_cons.2 ⟨subd6_4_342, List.forall_mem_cons.2 ⟨subd6_4_343, List.forall_mem_cons.2 ⟨subd6_4_344, List.forall_mem_cons.2 ⟨subd6_4_345, List.forall_mem_cons.2 ⟨subd6_4_346, List.forall_mem_cons.2 ⟨subd6_4_347, List.forall_mem_cons.2 ⟨subd6_4_348, List.forall_mem_cons.2 ⟨subd6_4_349, List.forall_mem_cons.2 ⟨subd6_4_350, List.forall_mem_cons.2 ⟨subd6_4_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C110
