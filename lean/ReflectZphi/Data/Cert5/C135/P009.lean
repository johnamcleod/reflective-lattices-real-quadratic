import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_1_0 : subd6_1 [-5] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-4, -3] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-4, -2] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-4, -1] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-4, 0] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-4, 1] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-4, 2] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [-4, 3] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [-4, 4] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [-4, 5] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [-3, -4] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [-3, -3] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [-3, -2] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [-3, -1] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [-3, 0] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [-3, 1] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [-3, 2] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [-3, 3] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [-3, 4] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [-3, 5] = true := by decide +kernel
theorem subd6_1_20 : subd6_1 [-2, -5] = true := by decide +kernel
theorem subd6_1_21 : subd6_1 [-2, -4] = true := by decide +kernel
theorem subd6_1_22 : subd6_1 [-2, -3] = true := by decide +kernel
theorem subd6_1_23 : subd6_1 [-2, -2] = true := by decide +kernel
theorem subd6_1_24 : subd6_1 [-2, -1, -8] = true := by decide +kernel
theorem subd6_1_25 : subd6_1 [-2, -1, -7] = true := by decide +kernel
theorem subd6_1_26 : subd6_1 [-2, -1, -6] = true := by decide +kernel
theorem subd6_1_27 : subd6_1 [-2, -1, -5] = true := by decide +kernel
theorem subd6_1_28 : subd6_1 [-2, -1, -4] = true := by decide +kernel
theorem subd6_1_29 : subd6_1 [-2, -1, -3] = true := by decide +kernel
theorem subd6_1_30 : subd6_1 [-2, -1, -2] = true := by decide +kernel
theorem subd6_1_31 : subd6_1 [-2, -1, -1] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_cons.2 ⟨subd6_1_20, List.forall_mem_cons.2 ⟨subd6_1_21, List.forall_mem_cons.2 ⟨subd6_1_22, List.forall_mem_cons.2 ⟨subd6_1_23, List.forall_mem_cons.2 ⟨subd6_1_24, List.forall_mem_cons.2 ⟨subd6_1_25, List.forall_mem_cons.2 ⟨subd6_1_26, List.forall_mem_cons.2 ⟨subd6_1_27, List.forall_mem_cons.2 ⟨subd6_1_28, List.forall_mem_cons.2 ⟨subd6_1_29, List.forall_mem_cons.2 ⟨subd6_1_30, List.forall_mem_cons.2 ⟨subd6_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_32 : subd6_1 [-2, -1, 0] = true := by decide +kernel
theorem subd6_1_33 : subd6_1 [-2, -1, 1] = true := by decide +kernel
theorem subd6_1_34 : subd6_1 [-2, -1, 2] = true := by decide +kernel
theorem subd6_1_35 : subd6_1 [-2, -1, 3] = true := by decide +kernel
theorem subd6_1_36 : subd6_1 [-2, -1, 4] = true := by decide +kernel
theorem subd6_1_37 : subd6_1 [-2, -1, 5] = true := by decide +kernel
theorem subd6_1_38 : subd6_1 [-2, -1, 6] = true := by decide +kernel
theorem subd6_1_39 : subd6_1 [-2, 0, -9] = true := by decide +kernel
theorem subd6_1_40 : subd6_1 [-2, 0, -8] = true := by decide +kernel
theorem subd6_1_41 : subd6_1 [-2, 0, -7] = true := by decide +kernel
theorem subd6_1_42 : subd6_1 [-2, 0, -6] = true := by decide +kernel
theorem subd6_1_43 : subd6_1 [-2, 0, -5] = true := by decide +kernel
theorem subd6_1_44 : subd6_1 [-2, 0, -4] = true := by decide +kernel
theorem subd6_1_45 : subd6_1 [-2, 0, -3] = true := by decide +kernel
theorem subd6_1_46 : subd6_1 [-2, 0, -2] = true := by decide +kernel
theorem subd6_1_47 : subd6_1 [-2, 0, -1] = true := by decide +kernel
theorem subd6_1_48 : subd6_1 [-2, 0, 0] = true := by decide +kernel
theorem subd6_1_49 : subd6_1 [-2, 0, 1] = true := by decide +kernel
theorem subd6_1_50 : subd6_1 [-2, 0, 2] = true := by decide +kernel
theorem subd6_1_51 : subd6_1 [-2, 0, 3] = true := by decide +kernel
theorem subd6_1_52 : subd6_1 [-2, 0, 4] = true := by decide +kernel
theorem subd6_1_53 : subd6_1 [-2, 0, 5] = true := by decide +kernel
theorem subd6_1_54 : subd6_1 [-2, 0, 6] = true := by decide +kernel
theorem subd6_1_55 : subd6_1 [-2, 1, -9] = true := by decide +kernel
theorem subd6_1_56 : subd6_1 [-2, 1, -8] = true := by decide +kernel
theorem subd6_1_57 : subd6_1 [-2, 1, -7] = true := by decide +kernel
theorem subd6_1_58 : subd6_1 [-2, 1, -6] = true := by decide +kernel
theorem subd6_1_59 : subd6_1 [-2, 1, -5] = true := by decide +kernel
theorem subd6_1_60 : subd6_1 [-2, 1, -4] = true := by decide +kernel
theorem subd6_1_61 : subd6_1 [-2, 1, -3] = true := by decide +kernel
theorem subd6_1_62 : subd6_1 [-2, 1, -2] = true := by decide +kernel
theorem subd6_1_63 : subd6_1 [-2, 1, -1] = true := by decide +kernel
theorem sbd6_1_1 : ∀ q ∈ blkd6_1_1, subd6_1 q = true := by
  unfold blkd6_1_1
  exact List.forall_mem_cons.2 ⟨subd6_1_32, List.forall_mem_cons.2 ⟨subd6_1_33, List.forall_mem_cons.2 ⟨subd6_1_34, List.forall_mem_cons.2 ⟨subd6_1_35, List.forall_mem_cons.2 ⟨subd6_1_36, List.forall_mem_cons.2 ⟨subd6_1_37, List.forall_mem_cons.2 ⟨subd6_1_38, List.forall_mem_cons.2 ⟨subd6_1_39, List.forall_mem_cons.2 ⟨subd6_1_40, List.forall_mem_cons.2 ⟨subd6_1_41, List.forall_mem_cons.2 ⟨subd6_1_42, List.forall_mem_cons.2 ⟨subd6_1_43, List.forall_mem_cons.2 ⟨subd6_1_44, List.forall_mem_cons.2 ⟨subd6_1_45, List.forall_mem_cons.2 ⟨subd6_1_46, List.forall_mem_cons.2 ⟨subd6_1_47, List.forall_mem_cons.2 ⟨subd6_1_48, List.forall_mem_cons.2 ⟨subd6_1_49, List.forall_mem_cons.2 ⟨subd6_1_50, List.forall_mem_cons.2 ⟨subd6_1_51, List.forall_mem_cons.2 ⟨subd6_1_52, List.forall_mem_cons.2 ⟨subd6_1_53, List.forall_mem_cons.2 ⟨subd6_1_54, List.forall_mem_cons.2 ⟨subd6_1_55, List.forall_mem_cons.2 ⟨subd6_1_56, List.forall_mem_cons.2 ⟨subd6_1_57, List.forall_mem_cons.2 ⟨subd6_1_58, List.forall_mem_cons.2 ⟨subd6_1_59, List.forall_mem_cons.2 ⟨subd6_1_60, List.forall_mem_cons.2 ⟨subd6_1_61, List.forall_mem_cons.2 ⟨subd6_1_62, List.forall_mem_cons.2 ⟨subd6_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_64 : subd6_1 [-2, 1, 0] = true := by decide +kernel
theorem subd6_1_65 : subd6_1 [-2, 1, 1] = true := by decide +kernel
theorem subd6_1_66 : subd6_1 [-2, 1, 2] = true := by decide +kernel
theorem subd6_1_67 : subd6_1 [-2, 1, 3] = true := by decide +kernel
theorem subd6_1_68 : subd6_1 [-2, 1, 4] = true := by decide +kernel
theorem subd6_1_69 : subd6_1 [-2, 1, 5] = true := by decide +kernel
theorem subd6_1_70 : subd6_1 [-2, 1, 6] = true := by decide +kernel
theorem subd6_1_71 : subd6_1 [-2, 2, -9] = true := by decide +kernel
theorem subd6_1_72 : subd6_1 [-2, 2, -8] = true := by decide +kernel
theorem subd6_1_73 : subd6_1 [-2, 2, -7] = true := by decide +kernel
theorem subd6_1_74 : subd6_1 [-2, 2, -6] = true := by decide +kernel
theorem subd6_1_75 : subd6_1 [-2, 2, -5] = true := by decide +kernel
theorem subd6_1_76 : subd6_1 [-2, 2, -4] = true := by decide +kernel
theorem subd6_1_77 : subd6_1 [-2, 2, -3] = true := by decide +kernel
theorem subd6_1_78 : subd6_1 [-2, 2, -2] = true := by decide +kernel
theorem subd6_1_79 : subd6_1 [-2, 2, -1] = true := by decide +kernel
theorem subd6_1_80 : subd6_1 [-2, 2, 0] = true := by decide +kernel
theorem subd6_1_81 : subd6_1 [-2, 2, 1] = true := by decide +kernel
theorem subd6_1_82 : subd6_1 [-2, 2, 2] = true := by decide +kernel
theorem subd6_1_83 : subd6_1 [-2, 2, 3] = true := by decide +kernel
theorem subd6_1_84 : subd6_1 [-2, 2, 4] = true := by decide +kernel
theorem subd6_1_85 : subd6_1 [-2, 2, 5] = true := by decide +kernel
theorem subd6_1_86 : subd6_1 [-2, 2, 6] = true := by decide +kernel
theorem subd6_1_87 : subd6_1 [-2, 3, -8] = true := by decide +kernel
theorem subd6_1_88 : subd6_1 [-2, 3, -7] = true := by decide +kernel
theorem subd6_1_89 : subd6_1 [-2, 3, -6] = true := by decide +kernel
theorem subd6_1_90 : subd6_1 [-2, 3, -5] = true := by decide +kernel
theorem subd6_1_91 : subd6_1 [-2, 3, -4] = true := by decide +kernel
theorem subd6_1_92 : subd6_1 [-2, 3, -3] = true := by decide +kernel
theorem subd6_1_93 : subd6_1 [-2, 3, -2] = true := by decide +kernel
theorem subd6_1_94 : subd6_1 [-2, 3, -1] = true := by decide +kernel
theorem subd6_1_95 : subd6_1 [-2, 3, 0] = true := by decide +kernel
theorem sbd6_1_2 : ∀ q ∈ blkd6_1_2, subd6_1 q = true := by
  unfold blkd6_1_2
  exact List.forall_mem_cons.2 ⟨subd6_1_64, List.forall_mem_cons.2 ⟨subd6_1_65, List.forall_mem_cons.2 ⟨subd6_1_66, List.forall_mem_cons.2 ⟨subd6_1_67, List.forall_mem_cons.2 ⟨subd6_1_68, List.forall_mem_cons.2 ⟨subd6_1_69, List.forall_mem_cons.2 ⟨subd6_1_70, List.forall_mem_cons.2 ⟨subd6_1_71, List.forall_mem_cons.2 ⟨subd6_1_72, List.forall_mem_cons.2 ⟨subd6_1_73, List.forall_mem_cons.2 ⟨subd6_1_74, List.forall_mem_cons.2 ⟨subd6_1_75, List.forall_mem_cons.2 ⟨subd6_1_76, List.forall_mem_cons.2 ⟨subd6_1_77, List.forall_mem_cons.2 ⟨subd6_1_78, List.forall_mem_cons.2 ⟨subd6_1_79, List.forall_mem_cons.2 ⟨subd6_1_80, List.forall_mem_cons.2 ⟨subd6_1_81, List.forall_mem_cons.2 ⟨subd6_1_82, List.forall_mem_cons.2 ⟨subd6_1_83, List.forall_mem_cons.2 ⟨subd6_1_84, List.forall_mem_cons.2 ⟨subd6_1_85, List.forall_mem_cons.2 ⟨subd6_1_86, List.forall_mem_cons.2 ⟨subd6_1_87, List.forall_mem_cons.2 ⟨subd6_1_88, List.forall_mem_cons.2 ⟨subd6_1_89, List.forall_mem_cons.2 ⟨subd6_1_90, List.forall_mem_cons.2 ⟨subd6_1_91, List.forall_mem_cons.2 ⟨subd6_1_92, List.forall_mem_cons.2 ⟨subd6_1_93, List.forall_mem_cons.2 ⟨subd6_1_94, List.forall_mem_cons.2 ⟨subd6_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_96 : subd6_1 [-2, 3, 1] = true := by decide +kernel
theorem subd6_1_97 : subd6_1 [-2, 3, 2] = true := by decide +kernel
theorem subd6_1_98 : subd6_1 [-2, 3, 3] = true := by decide +kernel
theorem subd6_1_99 : subd6_1 [-2, 3, 4] = true := by decide +kernel
theorem subd6_1_100 : subd6_1 [-2, 3, 5] = true := by decide +kernel
theorem subd6_1_101 : subd6_1 [-2, 3, 6] = true := by decide +kernel
theorem subd6_1_102 : subd6_1 [-2, 4] = true := by decide +kernel
theorem subd6_1_103 : subd6_1 [-2, 5] = true := by decide +kernel
theorem subd6_1_104 : subd6_1 [-2, 6] = true := by decide +kernel
theorem subd6_1_105 : subd6_1 [-1, -6] = true := by decide +kernel
theorem subd6_1_106 : subd6_1 [-1, -5] = true := by decide +kernel
theorem subd6_1_107 : subd6_1 [-1, -4] = true := by decide +kernel
theorem subd6_1_108 : subd6_1 [-1, -3] = true := by decide +kernel
theorem subd6_1_109 : subd6_1 [-1, -2, -8] = true := by decide +kernel
theorem subd6_1_110 : subd6_1 [-1, -2, -7] = true := by decide +kernel
theorem subd6_1_111 : subd6_1 [-1, -2, -6] = true := by decide +kernel
theorem subd6_1_112 : subd6_1 [-1, -2, -5] = true := by decide +kernel
theorem subd6_1_113 : subd6_1 [-1, -2, -4] = true := by decide +kernel
theorem subd6_1_114 : subd6_1 [-1, -2, -3] = true := by decide +kernel
theorem subd6_1_115 : subd6_1 [-1, -2, -2] = true := by decide +kernel
theorem subd6_1_116 : subd6_1 [-1, -2, -1] = true := by decide +kernel
theorem subd6_1_117 : subd6_1 [-1, -2, 0] = true := by decide +kernel
theorem subd6_1_118 : subd6_1 [-1, -2, 1] = true := by decide +kernel
theorem subd6_1_119 : subd6_1 [-1, -2, 2] = true := by decide +kernel
theorem subd6_1_120 : subd6_1 [-1, -2, 3] = true := by decide +kernel
theorem subd6_1_121 : subd6_1 [-1, -2, 4] = true := by decide +kernel
theorem subd6_1_122 : subd6_1 [-1, -2, 5] = true := by decide +kernel
theorem subd6_1_123 : subd6_1 [-1, -2, 6] = true := by decide +kernel
theorem subd6_1_124 : subd6_1 [-1, -2, 7] = true := by decide +kernel
theorem subd6_1_125 : subd6_1 [-1, -1, -9] = true := by decide +kernel
theorem subd6_1_126 : subd6_1 [-1, -1, -8] = true := by decide +kernel
theorem subd6_1_127 : subd6_1 [-1, -1, -7] = true := by decide +kernel
theorem sbd6_1_3 : ∀ q ∈ blkd6_1_3, subd6_1 q = true := by
  unfold blkd6_1_3
  exact List.forall_mem_cons.2 ⟨subd6_1_96, List.forall_mem_cons.2 ⟨subd6_1_97, List.forall_mem_cons.2 ⟨subd6_1_98, List.forall_mem_cons.2 ⟨subd6_1_99, List.forall_mem_cons.2 ⟨subd6_1_100, List.forall_mem_cons.2 ⟨subd6_1_101, List.forall_mem_cons.2 ⟨subd6_1_102, List.forall_mem_cons.2 ⟨subd6_1_103, List.forall_mem_cons.2 ⟨subd6_1_104, List.forall_mem_cons.2 ⟨subd6_1_105, List.forall_mem_cons.2 ⟨subd6_1_106, List.forall_mem_cons.2 ⟨subd6_1_107, List.forall_mem_cons.2 ⟨subd6_1_108, List.forall_mem_cons.2 ⟨subd6_1_109, List.forall_mem_cons.2 ⟨subd6_1_110, List.forall_mem_cons.2 ⟨subd6_1_111, List.forall_mem_cons.2 ⟨subd6_1_112, List.forall_mem_cons.2 ⟨subd6_1_113, List.forall_mem_cons.2 ⟨subd6_1_114, List.forall_mem_cons.2 ⟨subd6_1_115, List.forall_mem_cons.2 ⟨subd6_1_116, List.forall_mem_cons.2 ⟨subd6_1_117, List.forall_mem_cons.2 ⟨subd6_1_118, List.forall_mem_cons.2 ⟨subd6_1_119, List.forall_mem_cons.2 ⟨subd6_1_120, List.forall_mem_cons.2 ⟨subd6_1_121, List.forall_mem_cons.2 ⟨subd6_1_122, List.forall_mem_cons.2 ⟨subd6_1_123, List.forall_mem_cons.2 ⟨subd6_1_124, List.forall_mem_cons.2 ⟨subd6_1_125, List.forall_mem_cons.2 ⟨subd6_1_126, List.forall_mem_cons.2 ⟨subd6_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_128 : subd6_1 [-1, -1, -6] = true := by decide +kernel
theorem subd6_1_129 : subd6_1 [-1, -1, -5] = true := by decide +kernel
theorem subd6_1_130 : subd6_1 [-1, -1, -4] = true := by decide +kernel
theorem subd6_1_131 : subd6_1 [-1, -1, -3] = true := by decide +kernel
theorem subd6_1_132 : subd6_1 [-1, -1, -2] = true := by decide +kernel
theorem subd6_1_133 : subd6_1 [-1, -1, -1] = true := by decide +kernel
theorem subd6_1_134 : subd6_1 [-1, -1, 0] = true := by decide +kernel
theorem subd6_1_135 : subd6_1 [-1, -1, 1] = true := by decide +kernel
theorem subd6_1_136 : subd6_1 [-1, -1, 2] = true := by decide +kernel
theorem subd6_1_137 : subd6_1 [-1, -1, 3] = true := by decide +kernel
theorem subd6_1_138 : subd6_1 [-1, -1, 4] = true := by decide +kernel
theorem subd6_1_139 : subd6_1 [-1, -1, 5] = true := by decide +kernel
theorem subd6_1_140 : subd6_1 [-1, -1, 6] = true := by decide +kernel
theorem subd6_1_141 : subd6_1 [-1, -1, 7] = true := by decide +kernel
theorem subd6_1_142 : subd6_1 [-1, 0, -9] = true := by decide +kernel
theorem subd6_1_143 : subd6_1 [-1, 0, -8] = true := by decide +kernel
theorem subd6_1_144 : subd6_1 [-1, 0, -7] = true := by decide +kernel
theorem subd6_1_145 : subd6_1 [-1, 0, -6] = true := by decide +kernel
theorem subd6_1_146 : subd6_1 [-1, 0, -5] = true := by decide +kernel
theorem subd6_1_147 : subd6_1 [-1, 0, -4] = true := by decide +kernel
theorem subd6_1_148 : subd6_1 [-1, 0, -3] = true := by decide +kernel
theorem subd6_1_149 : subd6_1 [-1, 0, -2] = true := by decide +kernel
theorem subd6_1_150 : subd6_1 [-1, 0, -1] = true := by decide +kernel
theorem subd6_1_151 : subd6_1 [-1, 0, 0] = true := by decide +kernel
theorem subd6_1_152 : subd6_1 [-1, 0, 1] = true := by decide +kernel
theorem subd6_1_153 : subd6_1 [-1, 0, 2] = true := by decide +kernel
theorem subd6_1_154 : subd6_1 [-1, 0, 3] = true := by decide +kernel
theorem subd6_1_155 : subd6_1 [-1, 0, 4] = true := by decide +kernel
theorem subd6_1_156 : subd6_1 [-1, 0, 5] = true := by decide +kernel
theorem subd6_1_157 : subd6_1 [-1, 0, 6] = true := by decide +kernel
theorem subd6_1_158 : subd6_1 [-1, 0, 7] = true := by decide +kernel
theorem subd6_1_159 : subd6_1 [-1, 1, -9] = true := by decide +kernel
theorem sbd6_1_4 : ∀ q ∈ blkd6_1_4, subd6_1 q = true := by
  unfold blkd6_1_4
  exact List.forall_mem_cons.2 ⟨subd6_1_128, List.forall_mem_cons.2 ⟨subd6_1_129, List.forall_mem_cons.2 ⟨subd6_1_130, List.forall_mem_cons.2 ⟨subd6_1_131, List.forall_mem_cons.2 ⟨subd6_1_132, List.forall_mem_cons.2 ⟨subd6_1_133, List.forall_mem_cons.2 ⟨subd6_1_134, List.forall_mem_cons.2 ⟨subd6_1_135, List.forall_mem_cons.2 ⟨subd6_1_136, List.forall_mem_cons.2 ⟨subd6_1_137, List.forall_mem_cons.2 ⟨subd6_1_138, List.forall_mem_cons.2 ⟨subd6_1_139, List.forall_mem_cons.2 ⟨subd6_1_140, List.forall_mem_cons.2 ⟨subd6_1_141, List.forall_mem_cons.2 ⟨subd6_1_142, List.forall_mem_cons.2 ⟨subd6_1_143, List.forall_mem_cons.2 ⟨subd6_1_144, List.forall_mem_cons.2 ⟨subd6_1_145, List.forall_mem_cons.2 ⟨subd6_1_146, List.forall_mem_cons.2 ⟨subd6_1_147, List.forall_mem_cons.2 ⟨subd6_1_148, List.forall_mem_cons.2 ⟨subd6_1_149, List.forall_mem_cons.2 ⟨subd6_1_150, List.forall_mem_cons.2 ⟨subd6_1_151, List.forall_mem_cons.2 ⟨subd6_1_152, List.forall_mem_cons.2 ⟨subd6_1_153, List.forall_mem_cons.2 ⟨subd6_1_154, List.forall_mem_cons.2 ⟨subd6_1_155, List.forall_mem_cons.2 ⟨subd6_1_156, List.forall_mem_cons.2 ⟨subd6_1_157, List.forall_mem_cons.2 ⟨subd6_1_158, List.forall_mem_cons.2 ⟨subd6_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_160 : subd6_1 [-1, 1, -8] = true := by decide +kernel
theorem subd6_1_161 : subd6_1 [-1, 1, -7] = true := by decide +kernel
theorem subd6_1_162 : subd6_1 [-1, 1, -6] = true := by decide +kernel
theorem subd6_1_163 : subd6_1 [-1, 1, -5] = true := by decide +kernel
theorem subd6_1_164 : subd6_1 [-1, 1, -4] = true := by decide +kernel
theorem subd6_1_165 : subd6_1 [-1, 1, -3] = true := by decide +kernel
theorem subd6_1_166 : subd6_1 [-1, 1, -2] = true := by decide +kernel
theorem subd6_1_167 : subd6_1 [-1, 1, -1] = true := by decide +kernel
theorem subd6_1_168 : subd6_1 [-1, 1, 0] = true := by decide +kernel
theorem subd6_1_169 : subd6_1 [-1, 1, 1] = true := by decide +kernel
theorem subd6_1_170 : subd6_1 [-1, 1, 2] = true := by decide +kernel
theorem subd6_1_171 : subd6_1 [-1, 1, 3] = true := by decide +kernel
theorem subd6_1_172 : subd6_1 [-1, 1, 4] = true := by decide +kernel
theorem subd6_1_173 : subd6_1 [-1, 1, 5] = true := by decide +kernel
theorem subd6_1_174 : subd6_1 [-1, 1, 6] = true := by decide +kernel
theorem subd6_1_175 : subd6_1 [-1, 1, 7] = true := by decide +kernel
theorem subd6_1_176 : subd6_1 [-1, 2, -9] = true := by decide +kernel
theorem subd6_1_177 : subd6_1 [-1, 2, -8] = true := by decide +kernel
theorem subd6_1_178 : subd6_1 [-1, 2, -7] = true := by decide +kernel
theorem subd6_1_179 : subd6_1 [-1, 2, -6] = true := by decide +kernel
theorem subd6_1_180 : subd6_1 [-1, 2, -5] = true := by decide +kernel
theorem subd6_1_181 : subd6_1 [-1, 2, -4] = true := by decide +kernel
theorem subd6_1_182 : subd6_1 [-1, 2, -3] = true := by decide +kernel
theorem subd6_1_183 : subd6_1 [-1, 2, -2] = true := by decide +kernel
theorem subd6_1_184 : subd6_1 [-1, 2, -1] = true := by decide +kernel
theorem subd6_1_185 : subd6_1 [-1, 2, 0] = true := by decide +kernel
theorem subd6_1_186 : subd6_1 [-1, 2, 1] = true := by decide +kernel
theorem subd6_1_187 : subd6_1 [-1, 2, 2] = true := by decide +kernel
theorem subd6_1_188 : subd6_1 [-1, 2, 3] = true := by decide +kernel
theorem subd6_1_189 : subd6_1 [-1, 2, 4] = true := by decide +kernel
theorem subd6_1_190 : subd6_1 [-1, 2, 5] = true := by decide +kernel
theorem subd6_1_191 : subd6_1 [-1, 2, 6] = true := by decide +kernel
theorem sbd6_1_5 : ∀ q ∈ blkd6_1_5, subd6_1 q = true := by
  unfold blkd6_1_5
  exact List.forall_mem_cons.2 ⟨subd6_1_160, List.forall_mem_cons.2 ⟨subd6_1_161, List.forall_mem_cons.2 ⟨subd6_1_162, List.forall_mem_cons.2 ⟨subd6_1_163, List.forall_mem_cons.2 ⟨subd6_1_164, List.forall_mem_cons.2 ⟨subd6_1_165, List.forall_mem_cons.2 ⟨subd6_1_166, List.forall_mem_cons.2 ⟨subd6_1_167, List.forall_mem_cons.2 ⟨subd6_1_168, List.forall_mem_cons.2 ⟨subd6_1_169, List.forall_mem_cons.2 ⟨subd6_1_170, List.forall_mem_cons.2 ⟨subd6_1_171, List.forall_mem_cons.2 ⟨subd6_1_172, List.forall_mem_cons.2 ⟨subd6_1_173, List.forall_mem_cons.2 ⟨subd6_1_174, List.forall_mem_cons.2 ⟨subd6_1_175, List.forall_mem_cons.2 ⟨subd6_1_176, List.forall_mem_cons.2 ⟨subd6_1_177, List.forall_mem_cons.2 ⟨subd6_1_178, List.forall_mem_cons.2 ⟨subd6_1_179, List.forall_mem_cons.2 ⟨subd6_1_180, List.forall_mem_cons.2 ⟨subd6_1_181, List.forall_mem_cons.2 ⟨subd6_1_182, List.forall_mem_cons.2 ⟨subd6_1_183, List.forall_mem_cons.2 ⟨subd6_1_184, List.forall_mem_cons.2 ⟨subd6_1_185, List.forall_mem_cons.2 ⟨subd6_1_186, List.forall_mem_cons.2 ⟨subd6_1_187, List.forall_mem_cons.2 ⟨subd6_1_188, List.forall_mem_cons.2 ⟨subd6_1_189, List.forall_mem_cons.2 ⟨subd6_1_190, List.forall_mem_cons.2 ⟨subd6_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_192 : subd6_1 [-1, 2, 7] = true := by decide +kernel
theorem subd6_1_193 : subd6_1 [-1, 3, -8] = true := by decide +kernel
theorem subd6_1_194 : subd6_1 [-1, 3, -7] = true := by decide +kernel
theorem subd6_1_195 : subd6_1 [-1, 3, -6] = true := by decide +kernel
theorem subd6_1_196 : subd6_1 [-1, 3, -5] = true := by decide +kernel
theorem subd6_1_197 : subd6_1 [-1, 3, -4] = true := by decide +kernel
theorem subd6_1_198 : subd6_1 [-1, 3, -3] = true := by decide +kernel
theorem subd6_1_199 : subd6_1 [-1, 3, -2] = true := by decide +kernel
theorem subd6_1_200 : subd6_1 [-1, 3, -1] = true := by decide +kernel
theorem subd6_1_201 : subd6_1 [-1, 3, 0] = true := by decide +kernel
theorem subd6_1_202 : subd6_1 [-1, 3, 1] = true := by decide +kernel
theorem subd6_1_203 : subd6_1 [-1, 3, 2] = true := by decide +kernel
theorem subd6_1_204 : subd6_1 [-1, 3, 3] = true := by decide +kernel
theorem subd6_1_205 : subd6_1 [-1, 3, 4] = true := by decide +kernel
theorem subd6_1_206 : subd6_1 [-1, 3, 5] = true := by decide +kernel
theorem subd6_1_207 : subd6_1 [-1, 3, 6] = true := by decide +kernel
theorem subd6_1_208 : subd6_1 [-1, 4] = true := by decide +kernel
theorem subd6_1_209 : subd6_1 [-1, 5] = true := by decide +kernel
theorem subd6_1_210 : subd6_1 [-1, 6] = true := by decide +kernel
theorem subd6_1_211 : subd6_1 [0, -6] = true := by decide +kernel
theorem subd6_1_212 : subd6_1 [0, -5] = true := by decide +kernel
theorem subd6_1_213 : subd6_1 [0, -4] = true := by decide +kernel
theorem subd6_1_214 : subd6_1 [0, -3, -7] = true := by decide +kernel
theorem subd6_1_215 : subd6_1 [0, -3, -6] = true := by decide +kernel
theorem subd6_1_216 : subd6_1 [0, -3, -5] = true := by decide +kernel
theorem subd6_1_217 : subd6_1 [0, -3, -4] = true := by decide +kernel
theorem subd6_1_218 : subd6_1 [0, -3, -3] = true := by decide +kernel
theorem subd6_1_219 : subd6_1 [0, -3, -2] = true := by decide +kernel
theorem subd6_1_220 : subd6_1 [0, -3, -1] = true := by decide +kernel
theorem subd6_1_221 : subd6_1 [0, -3, 0] = true := by decide +kernel
theorem subd6_1_222 : subd6_1 [0, -3, 1] = true := by decide +kernel
theorem subd6_1_223 : subd6_1 [0, -3, 2] = true := by decide +kernel
theorem sbd6_1_6 : ∀ q ∈ blkd6_1_6, subd6_1 q = true := by
  unfold blkd6_1_6
  exact List.forall_mem_cons.2 ⟨subd6_1_192, List.forall_mem_cons.2 ⟨subd6_1_193, List.forall_mem_cons.2 ⟨subd6_1_194, List.forall_mem_cons.2 ⟨subd6_1_195, List.forall_mem_cons.2 ⟨subd6_1_196, List.forall_mem_cons.2 ⟨subd6_1_197, List.forall_mem_cons.2 ⟨subd6_1_198, List.forall_mem_cons.2 ⟨subd6_1_199, List.forall_mem_cons.2 ⟨subd6_1_200, List.forall_mem_cons.2 ⟨subd6_1_201, List.forall_mem_cons.2 ⟨subd6_1_202, List.forall_mem_cons.2 ⟨subd6_1_203, List.forall_mem_cons.2 ⟨subd6_1_204, List.forall_mem_cons.2 ⟨subd6_1_205, List.forall_mem_cons.2 ⟨subd6_1_206, List.forall_mem_cons.2 ⟨subd6_1_207, List.forall_mem_cons.2 ⟨subd6_1_208, List.forall_mem_cons.2 ⟨subd6_1_209, List.forall_mem_cons.2 ⟨subd6_1_210, List.forall_mem_cons.2 ⟨subd6_1_211, List.forall_mem_cons.2 ⟨subd6_1_212, List.forall_mem_cons.2 ⟨subd6_1_213, List.forall_mem_cons.2 ⟨subd6_1_214, List.forall_mem_cons.2 ⟨subd6_1_215, List.forall_mem_cons.2 ⟨subd6_1_216, List.forall_mem_cons.2 ⟨subd6_1_217, List.forall_mem_cons.2 ⟨subd6_1_218, List.forall_mem_cons.2 ⟨subd6_1_219, List.forall_mem_cons.2 ⟨subd6_1_220, List.forall_mem_cons.2 ⟨subd6_1_221, List.forall_mem_cons.2 ⟨subd6_1_222, List.forall_mem_cons.2 ⟨subd6_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_224 : subd6_1 [0, -3, 3] = true := by decide +kernel
theorem subd6_1_225 : subd6_1 [0, -3, 4] = true := by decide +kernel
theorem subd6_1_226 : subd6_1 [0, -3, 5] = true := by decide +kernel
theorem subd6_1_227 : subd6_1 [0, -3, 6] = true := by decide +kernel
theorem subd6_1_228 : subd6_1 [0, -3, 7] = true := by decide +kernel
theorem subd6_1_229 : subd6_1 [0, -2, -8] = true := by decide +kernel
theorem subd6_1_230 : subd6_1 [0, -2, -7] = true := by decide +kernel
theorem subd6_1_231 : subd6_1 [0, -2, -6] = true := by decide +kernel
theorem subd6_1_232 : subd6_1 [0, -2, -5] = true := by decide +kernel
theorem subd6_1_233 : subd6_1 [0, -2, -4] = true := by decide +kernel
theorem subd6_1_234 : subd6_1 [0, -2, -3] = true := by decide +kernel
theorem subd6_1_235 : subd6_1 [0, -2, -2] = true := by decide +kernel
theorem subd6_1_236 : subd6_1 [0, -2, -1] = true := by decide +kernel
theorem subd6_1_237 : subd6_1 [0, -2, 0] = true := by decide +kernel
theorem subd6_1_238 : subd6_1 [0, -2, 1] = true := by decide +kernel
theorem subd6_1_239 : subd6_1 [0, -2, 2] = true := by decide +kernel
theorem subd6_1_240 : subd6_1 [0, -2, 3] = true := by decide +kernel
theorem subd6_1_241 : subd6_1 [0, -2, 4] = true := by decide +kernel
theorem subd6_1_242 : subd6_1 [0, -2, 5] = true := by decide +kernel
theorem subd6_1_243 : subd6_1 [0, -2, 6] = true := by decide +kernel
theorem subd6_1_244 : subd6_1 [0, -2, 7] = true := by decide +kernel
theorem subd6_1_245 : subd6_1 [0, -1, -9] = true := by decide +kernel
theorem subd6_1_246 : subd6_1 [0, -1, -8] = true := by decide +kernel
theorem subd6_1_247 : subd6_1 [0, -1, -7] = true := by decide +kernel
theorem subd6_1_248 : subd6_1 [0, -1, -6] = true := by decide +kernel
theorem subd6_1_249 : subd6_1 [0, -1, -5] = true := by decide +kernel
theorem subd6_1_250 : subd6_1 [0, -1, -4] = true := by decide +kernel
theorem subd6_1_251 : subd6_1 [0, -1, -3] = true := by decide +kernel
theorem subd6_1_252 : subd6_1 [0, -1, -2] = true := by decide +kernel
theorem subd6_1_253 : subd6_1 [0, -1, -1] = true := by decide +kernel
theorem subd6_1_254 : subd6_1 [0, -1, 0] = true := by decide +kernel
theorem subd6_1_255 : subd6_1 [0, -1, 1] = true := by decide +kernel
theorem sbd6_1_7 : ∀ q ∈ blkd6_1_7, subd6_1 q = true := by
  unfold blkd6_1_7
  exact List.forall_mem_cons.2 ⟨subd6_1_224, List.forall_mem_cons.2 ⟨subd6_1_225, List.forall_mem_cons.2 ⟨subd6_1_226, List.forall_mem_cons.2 ⟨subd6_1_227, List.forall_mem_cons.2 ⟨subd6_1_228, List.forall_mem_cons.2 ⟨subd6_1_229, List.forall_mem_cons.2 ⟨subd6_1_230, List.forall_mem_cons.2 ⟨subd6_1_231, List.forall_mem_cons.2 ⟨subd6_1_232, List.forall_mem_cons.2 ⟨subd6_1_233, List.forall_mem_cons.2 ⟨subd6_1_234, List.forall_mem_cons.2 ⟨subd6_1_235, List.forall_mem_cons.2 ⟨subd6_1_236, List.forall_mem_cons.2 ⟨subd6_1_237, List.forall_mem_cons.2 ⟨subd6_1_238, List.forall_mem_cons.2 ⟨subd6_1_239, List.forall_mem_cons.2 ⟨subd6_1_240, List.forall_mem_cons.2 ⟨subd6_1_241, List.forall_mem_cons.2 ⟨subd6_1_242, List.forall_mem_cons.2 ⟨subd6_1_243, List.forall_mem_cons.2 ⟨subd6_1_244, List.forall_mem_cons.2 ⟨subd6_1_245, List.forall_mem_cons.2 ⟨subd6_1_246, List.forall_mem_cons.2 ⟨subd6_1_247, List.forall_mem_cons.2 ⟨subd6_1_248, List.forall_mem_cons.2 ⟨subd6_1_249, List.forall_mem_cons.2 ⟨subd6_1_250, List.forall_mem_cons.2 ⟨subd6_1_251, List.forall_mem_cons.2 ⟨subd6_1_252, List.forall_mem_cons.2 ⟨subd6_1_253, List.forall_mem_cons.2 ⟨subd6_1_254, List.forall_mem_cons.2 ⟨subd6_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_256 : subd6_1 [0, -1, 2] = true := by decide +kernel
theorem subd6_1_257 : subd6_1 [0, -1, 3] = true := by decide +kernel
theorem subd6_1_258 : subd6_1 [0, -1, 4] = true := by decide +kernel
theorem subd6_1_259 : subd6_1 [0, -1, 5] = true := by decide +kernel
theorem subd6_1_260 : subd6_1 [0, -1, 6] = true := by decide +kernel
theorem subd6_1_261 : subd6_1 [0, -1, 7] = true := by decide +kernel
theorem subd6_1_262 : subd6_1 [0, -1, 8] = true := by decide +kernel
theorem subd6_1_263 : subd6_1 [0, 0, -9] = true := by decide +kernel
theorem subd6_1_264 : subd6_1 [0, 0, -8] = true := by decide +kernel
theorem subd6_1_265 : subd6_1 [0, 0, -7] = true := by decide +kernel
theorem subd6_1_266 : subd6_1 [0, 0, -6] = true := by decide +kernel
theorem subd6_1_267 : subd6_1 [0, 0, -5] = true := by decide +kernel
theorem subd6_1_268 : subd6_1 [0, 0, -4] = true := by decide +kernel
theorem subd6_1_269 : subd6_1 [0, 0, -3] = true := by decide +kernel
theorem subd6_1_270 : subd6_1 [0, 0, -2] = true := by decide +kernel
theorem subd6_1_271 : subd6_1 [0, 0, -1] = true := by decide +kernel
theorem subd6_1_272 : subd6_1 [0, 0, 0] = true := by decide +kernel
theorem subd6_1_273 : subd6_1 [0, 0, 1] = true := by decide +kernel
theorem subd6_1_274 : subd6_1 [0, 0, 2] = true := by decide +kernel
theorem subd6_1_275 : subd6_1 [0, 0, 3] = true := by decide +kernel
theorem subd6_1_276 : subd6_1 [0, 0, 4] = true := by decide +kernel
theorem subd6_1_277 : subd6_1 [0, 0, 5] = true := by decide +kernel
theorem subd6_1_278 : subd6_1 [0, 0, 6] = true := by decide +kernel
theorem subd6_1_279 : subd6_1 [0, 0, 7] = true := by decide +kernel
theorem subd6_1_280 : subd6_1 [0, 0, 8] = true := by decide +kernel
theorem subd6_1_281 : subd6_1 [0, 1, -9] = true := by decide +kernel
theorem subd6_1_282 : subd6_1 [0, 1, -8] = true := by decide +kernel
theorem subd6_1_283 : subd6_1 [0, 1, -7] = true := by decide +kernel
theorem subd6_1_284 : subd6_1 [0, 1, -6] = true := by decide +kernel
theorem subd6_1_285 : subd6_1 [0, 1, -5] = true := by decide +kernel
theorem subd6_1_286 : subd6_1 [0, 1, -4] = true := by decide +kernel
theorem subd6_1_287 : subd6_1 [0, 1, -3] = true := by decide +kernel
theorem sbd6_1_8 : ∀ q ∈ blkd6_1_8, subd6_1 q = true := by
  unfold blkd6_1_8
  exact List.forall_mem_cons.2 ⟨subd6_1_256, List.forall_mem_cons.2 ⟨subd6_1_257, List.forall_mem_cons.2 ⟨subd6_1_258, List.forall_mem_cons.2 ⟨subd6_1_259, List.forall_mem_cons.2 ⟨subd6_1_260, List.forall_mem_cons.2 ⟨subd6_1_261, List.forall_mem_cons.2 ⟨subd6_1_262, List.forall_mem_cons.2 ⟨subd6_1_263, List.forall_mem_cons.2 ⟨subd6_1_264, List.forall_mem_cons.2 ⟨subd6_1_265, List.forall_mem_cons.2 ⟨subd6_1_266, List.forall_mem_cons.2 ⟨subd6_1_267, List.forall_mem_cons.2 ⟨subd6_1_268, List.forall_mem_cons.2 ⟨subd6_1_269, List.forall_mem_cons.2 ⟨subd6_1_270, List.forall_mem_cons.2 ⟨subd6_1_271, List.forall_mem_cons.2 ⟨subd6_1_272, List.forall_mem_cons.2 ⟨subd6_1_273, List.forall_mem_cons.2 ⟨subd6_1_274, List.forall_mem_cons.2 ⟨subd6_1_275, List.forall_mem_cons.2 ⟨subd6_1_276, List.forall_mem_cons.2 ⟨subd6_1_277, List.forall_mem_cons.2 ⟨subd6_1_278, List.forall_mem_cons.2 ⟨subd6_1_279, List.forall_mem_cons.2 ⟨subd6_1_280, List.forall_mem_cons.2 ⟨subd6_1_281, List.forall_mem_cons.2 ⟨subd6_1_282, List.forall_mem_cons.2 ⟨subd6_1_283, List.forall_mem_cons.2 ⟨subd6_1_284, List.forall_mem_cons.2 ⟨subd6_1_285, List.forall_mem_cons.2 ⟨subd6_1_286, List.forall_mem_cons.2 ⟨subd6_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_288 : subd6_1 [0, 1, -2] = true := by decide +kernel
theorem subd6_1_289 : subd6_1 [0, 1, -1] = true := by decide +kernel
theorem subd6_1_290 : subd6_1 [0, 1, 0] = true := by decide +kernel
theorem subd6_1_291 : subd6_1 [0, 1, 1] = true := by decide +kernel
theorem subd6_1_292 : subd6_1 [0, 1, 2] = true := by decide +kernel
theorem subd6_1_293 : subd6_1 [0, 1, 3] = true := by decide +kernel
theorem subd6_1_294 : subd6_1 [0, 1, 4] = true := by decide +kernel
theorem subd6_1_295 : subd6_1 [0, 1, 5] = true := by decide +kernel
theorem subd6_1_296 : subd6_1 [0, 1, 6] = true := by decide +kernel
theorem subd6_1_297 : subd6_1 [0, 1, 7] = true := by decide +kernel
theorem subd6_1_298 : subd6_1 [0, 1, 8] = true := by decide +kernel
theorem subd6_1_299 : subd6_1 [0, 2, -8] = true := by decide +kernel
theorem subd6_1_300 : subd6_1 [0, 2, -7] = true := by decide +kernel
theorem subd6_1_301 : subd6_1 [0, 2, -6] = true := by decide +kernel
theorem subd6_1_302 : subd6_1 [0, 2, -5] = true := by decide +kernel
theorem subd6_1_303 : subd6_1 [0, 2, -4] = true := by decide +kernel
theorem subd6_1_304 : subd6_1 [0, 2, -3] = true := by decide +kernel
theorem subd6_1_305 : subd6_1 [0, 2, -2] = true := by decide +kernel
theorem subd6_1_306 : subd6_1 [0, 2, -1] = true := by decide +kernel
theorem subd6_1_307 : subd6_1 [0, 2, 0] = true := by decide +kernel
theorem subd6_1_308 : subd6_1 [0, 2, 1] = true := by decide +kernel
theorem subd6_1_309 : subd6_1 [0, 2, 2] = true := by decide +kernel
theorem subd6_1_310 : subd6_1 [0, 2, 3] = true := by decide +kernel
theorem subd6_1_311 : subd6_1 [0, 2, 4] = true := by decide +kernel
theorem subd6_1_312 : subd6_1 [0, 2, 5] = true := by decide +kernel
theorem subd6_1_313 : subd6_1 [0, 2, 6] = true := by decide +kernel
theorem subd6_1_314 : subd6_1 [0, 2, 7] = true := by decide +kernel
theorem subd6_1_315 : subd6_1 [0, 3, -8] = true := by decide +kernel
theorem subd6_1_316 : subd6_1 [0, 3, -7] = true := by decide +kernel
theorem subd6_1_317 : subd6_1 [0, 3, -6] = true := by decide +kernel
theorem subd6_1_318 : subd6_1 [0, 3, -5] = true := by decide +kernel
theorem subd6_1_319 : subd6_1 [0, 3, -4] = true := by decide +kernel
theorem sbd6_1_9 : ∀ q ∈ blkd6_1_9, subd6_1 q = true := by
  unfold blkd6_1_9
  exact List.forall_mem_cons.2 ⟨subd6_1_288, List.forall_mem_cons.2 ⟨subd6_1_289, List.forall_mem_cons.2 ⟨subd6_1_290, List.forall_mem_cons.2 ⟨subd6_1_291, List.forall_mem_cons.2 ⟨subd6_1_292, List.forall_mem_cons.2 ⟨subd6_1_293, List.forall_mem_cons.2 ⟨subd6_1_294, List.forall_mem_cons.2 ⟨subd6_1_295, List.forall_mem_cons.2 ⟨subd6_1_296, List.forall_mem_cons.2 ⟨subd6_1_297, List.forall_mem_cons.2 ⟨subd6_1_298, List.forall_mem_cons.2 ⟨subd6_1_299, List.forall_mem_cons.2 ⟨subd6_1_300, List.forall_mem_cons.2 ⟨subd6_1_301, List.forall_mem_cons.2 ⟨subd6_1_302, List.forall_mem_cons.2 ⟨subd6_1_303, List.forall_mem_cons.2 ⟨subd6_1_304, List.forall_mem_cons.2 ⟨subd6_1_305, List.forall_mem_cons.2 ⟨subd6_1_306, List.forall_mem_cons.2 ⟨subd6_1_307, List.forall_mem_cons.2 ⟨subd6_1_308, List.forall_mem_cons.2 ⟨subd6_1_309, List.forall_mem_cons.2 ⟨subd6_1_310, List.forall_mem_cons.2 ⟨subd6_1_311, List.forall_mem_cons.2 ⟨subd6_1_312, List.forall_mem_cons.2 ⟨subd6_1_313, List.forall_mem_cons.2 ⟨subd6_1_314, List.forall_mem_cons.2 ⟨subd6_1_315, List.forall_mem_cons.2 ⟨subd6_1_316, List.forall_mem_cons.2 ⟨subd6_1_317, List.forall_mem_cons.2 ⟨subd6_1_318, List.forall_mem_cons.2 ⟨subd6_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_320 : subd6_1 [0, 3, -3] = true := by decide +kernel
theorem subd6_1_321 : subd6_1 [0, 3, -2] = true := by decide +kernel
theorem subd6_1_322 : subd6_1 [0, 3, -1] = true := by decide +kernel
theorem subd6_1_323 : subd6_1 [0, 3, 0] = true := by decide +kernel
theorem subd6_1_324 : subd6_1 [0, 3, 1] = true := by decide +kernel
theorem subd6_1_325 : subd6_1 [0, 3, 2] = true := by decide +kernel
theorem subd6_1_326 : subd6_1 [0, 3, 3] = true := by decide +kernel
theorem subd6_1_327 : subd6_1 [0, 3, 4] = true := by decide +kernel
theorem subd6_1_328 : subd6_1 [0, 3, 5] = true := by decide +kernel
theorem subd6_1_329 : subd6_1 [0, 3, 6] = true := by decide +kernel
theorem subd6_1_330 : subd6_1 [0, 4] = true := by decide +kernel
theorem subd6_1_331 : subd6_1 [0, 5] = true := by decide +kernel
theorem subd6_1_332 : subd6_1 [1, -7] = true := by decide +kernel
theorem subd6_1_333 : subd6_1 [1, -6] = true := by decide +kernel
theorem subd6_1_334 : subd6_1 [1, -5] = true := by decide +kernel
theorem subd6_1_335 : subd6_1 [1, -4] = true := by decide +kernel
theorem subd6_1_336 : subd6_1 [1, -3, -7] = true := by decide +kernel
theorem subd6_1_337 : subd6_1 [1, -3, -6] = true := by decide +kernel
theorem subd6_1_338 : subd6_1 [1, -3, -5] = true := by decide +kernel
theorem subd6_1_339 : subd6_1 [1, -3, -4] = true := by decide +kernel
theorem subd6_1_340 : subd6_1 [1, -3, -3] = true := by decide +kernel
theorem subd6_1_341 : subd6_1 [1, -3, -2] = true := by decide +kernel
theorem subd6_1_342 : subd6_1 [1, -3, -1] = true := by decide +kernel
theorem subd6_1_343 : subd6_1 [1, -3, 0] = true := by decide +kernel
theorem subd6_1_344 : subd6_1 [1, -3, 1] = true := by decide +kernel
theorem subd6_1_345 : subd6_1 [1, -3, 2] = true := by decide +kernel
theorem subd6_1_346 : subd6_1 [1, -3, 3] = true := by decide +kernel
theorem subd6_1_347 : subd6_1 [1, -3, 4] = true := by decide +kernel
theorem subd6_1_348 : subd6_1 [1, -3, 5] = true := by decide +kernel
theorem subd6_1_349 : subd6_1 [1, -3, 6] = true := by decide +kernel
theorem subd6_1_350 : subd6_1 [1, -3, 7] = true := by decide +kernel
theorem subd6_1_351 : subd6_1 [1, -2, -8] = true := by decide +kernel
theorem sbd6_1_10 : ∀ q ∈ blkd6_1_10, subd6_1 q = true := by
  unfold blkd6_1_10
  exact List.forall_mem_cons.2 ⟨subd6_1_320, List.forall_mem_cons.2 ⟨subd6_1_321, List.forall_mem_cons.2 ⟨subd6_1_322, List.forall_mem_cons.2 ⟨subd6_1_323, List.forall_mem_cons.2 ⟨subd6_1_324, List.forall_mem_cons.2 ⟨subd6_1_325, List.forall_mem_cons.2 ⟨subd6_1_326, List.forall_mem_cons.2 ⟨subd6_1_327, List.forall_mem_cons.2 ⟨subd6_1_328, List.forall_mem_cons.2 ⟨subd6_1_329, List.forall_mem_cons.2 ⟨subd6_1_330, List.forall_mem_cons.2 ⟨subd6_1_331, List.forall_mem_cons.2 ⟨subd6_1_332, List.forall_mem_cons.2 ⟨subd6_1_333, List.forall_mem_cons.2 ⟨subd6_1_334, List.forall_mem_cons.2 ⟨subd6_1_335, List.forall_mem_cons.2 ⟨subd6_1_336, List.forall_mem_cons.2 ⟨subd6_1_337, List.forall_mem_cons.2 ⟨subd6_1_338, List.forall_mem_cons.2 ⟨subd6_1_339, List.forall_mem_cons.2 ⟨subd6_1_340, List.forall_mem_cons.2 ⟨subd6_1_341, List.forall_mem_cons.2 ⟨subd6_1_342, List.forall_mem_cons.2 ⟨subd6_1_343, List.forall_mem_cons.2 ⟨subd6_1_344, List.forall_mem_cons.2 ⟨subd6_1_345, List.forall_mem_cons.2 ⟨subd6_1_346, List.forall_mem_cons.2 ⟨subd6_1_347, List.forall_mem_cons.2 ⟨subd6_1_348, List.forall_mem_cons.2 ⟨subd6_1_349, List.forall_mem_cons.2 ⟨subd6_1_350, List.forall_mem_cons.2 ⟨subd6_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_352 : subd6_1 [1, -2, -7] = true := by decide +kernel
theorem subd6_1_353 : subd6_1 [1, -2, -6] = true := by decide +kernel
theorem subd6_1_354 : subd6_1 [1, -2, -5] = true := by decide +kernel
theorem subd6_1_355 : subd6_1 [1, -2, -4] = true := by decide +kernel
theorem subd6_1_356 : subd6_1 [1, -2, -3] = true := by decide +kernel
theorem subd6_1_357 : subd6_1 [1, -2, -2] = true := by decide +kernel
theorem subd6_1_358 : subd6_1 [1, -2, -1] = true := by decide +kernel
theorem subd6_1_359 : subd6_1 [1, -2, 0] = true := by decide +kernel
theorem subd6_1_360 : subd6_1 [1, -2, 1] = true := by decide +kernel
theorem subd6_1_361 : subd6_1 [1, -2, 2] = true := by decide +kernel
theorem subd6_1_362 : subd6_1 [1, -2, 3] = true := by decide +kernel
theorem subd6_1_363 : subd6_1 [1, -2, 4] = true := by decide +kernel
theorem subd6_1_364 : subd6_1 [1, -2, 5] = true := by decide +kernel
theorem subd6_1_365 : subd6_1 [1, -2, 6] = true := by decide +kernel
theorem subd6_1_366 : subd6_1 [1, -2, 7] = true := by decide +kernel
theorem subd6_1_367 : subd6_1 [1, -2, 8] = true := by decide +kernel
theorem subd6_1_368 : subd6_1 [1, -1, -8] = true := by decide +kernel
theorem subd6_1_369 : subd6_1 [1, -1, -7] = true := by decide +kernel
theorem subd6_1_370 : subd6_1 [1, -1, -6] = true := by decide +kernel
theorem subd6_1_371 : subd6_1 [1, -1, -5] = true := by decide +kernel
theorem subd6_1_372 : subd6_1 [1, -1, -4] = true := by decide +kernel
theorem subd6_1_373 : subd6_1 [1, -1, -3] = true := by decide +kernel
theorem subd6_1_374 : subd6_1 [1, -1, -2] = true := by decide +kernel
theorem subd6_1_375 : subd6_1 [1, -1, -1] = true := by decide +kernel
theorem subd6_1_376 : subd6_1 [1, -1, 0] = true := by decide +kernel
theorem subd6_1_377 : subd6_1 [1, -1, 1] = true := by decide +kernel
theorem subd6_1_378 : subd6_1 [1, -1, 2] = true := by decide +kernel
theorem subd6_1_379 : subd6_1 [1, -1, 3] = true := by decide +kernel
theorem subd6_1_380 : subd6_1 [1, -1, 4] = true := by decide +kernel
theorem subd6_1_381 : subd6_1 [1, -1, 5] = true := by decide +kernel
theorem subd6_1_382 : subd6_1 [1, -1, 6] = true := by decide +kernel
theorem subd6_1_383 : subd6_1 [1, -1, 7] = true := by decide +kernel
theorem sbd6_1_11 : ∀ q ∈ blkd6_1_11, subd6_1 q = true := by
  unfold blkd6_1_11
  exact List.forall_mem_cons.2 ⟨subd6_1_352, List.forall_mem_cons.2 ⟨subd6_1_353, List.forall_mem_cons.2 ⟨subd6_1_354, List.forall_mem_cons.2 ⟨subd6_1_355, List.forall_mem_cons.2 ⟨subd6_1_356, List.forall_mem_cons.2 ⟨subd6_1_357, List.forall_mem_cons.2 ⟨subd6_1_358, List.forall_mem_cons.2 ⟨subd6_1_359, List.forall_mem_cons.2 ⟨subd6_1_360, List.forall_mem_cons.2 ⟨subd6_1_361, List.forall_mem_cons.2 ⟨subd6_1_362, List.forall_mem_cons.2 ⟨subd6_1_363, List.forall_mem_cons.2 ⟨subd6_1_364, List.forall_mem_cons.2 ⟨subd6_1_365, List.forall_mem_cons.2 ⟨subd6_1_366, List.forall_mem_cons.2 ⟨subd6_1_367, List.forall_mem_cons.2 ⟨subd6_1_368, List.forall_mem_cons.2 ⟨subd6_1_369, List.forall_mem_cons.2 ⟨subd6_1_370, List.forall_mem_cons.2 ⟨subd6_1_371, List.forall_mem_cons.2 ⟨subd6_1_372, List.forall_mem_cons.2 ⟨subd6_1_373, List.forall_mem_cons.2 ⟨subd6_1_374, List.forall_mem_cons.2 ⟨subd6_1_375, List.forall_mem_cons.2 ⟨subd6_1_376, List.forall_mem_cons.2 ⟨subd6_1_377, List.forall_mem_cons.2 ⟨subd6_1_378, List.forall_mem_cons.2 ⟨subd6_1_379, List.forall_mem_cons.2 ⟨subd6_1_380, List.forall_mem_cons.2 ⟨subd6_1_381, List.forall_mem_cons.2 ⟨subd6_1_382, List.forall_mem_cons.2 ⟨subd6_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_384 : subd6_1 [1, -1, 8] = true := by decide +kernel
theorem subd6_1_385 : subd6_1 [1, 0, -8] = true := by decide +kernel
theorem subd6_1_386 : subd6_1 [1, 0, -7] = true := by decide +kernel
theorem subd6_1_387 : subd6_1 [1, 0, -6] = true := by decide +kernel
theorem subd6_1_388 : subd6_1 [1, 0, -5] = true := by decide +kernel
theorem subd6_1_389 : subd6_1 [1, 0, -4] = true := by decide +kernel
theorem subd6_1_390 : subd6_1 [1, 0, -3] = true := by decide +kernel
theorem subd6_1_391 : subd6_1 [1, 0, -2] = true := by decide +kernel
theorem subd6_1_392 : subd6_1 [1, 0, -1] = true := by decide +kernel
theorem subd6_1_393 : subd6_1 [1, 0, 0] = true := by decide +kernel
theorem subd6_1_394 : subd6_1 [1, 0, 1] = true := by decide +kernel
theorem subd6_1_395 : subd6_1 [1, 0, 2] = true := by decide +kernel
theorem subd6_1_396 : subd6_1 [1, 0, 3] = true := by decide +kernel
theorem subd6_1_397 : subd6_1 [1, 0, 4] = true := by decide +kernel
theorem subd6_1_398 : subd6_1 [1, 0, 5] = true := by decide +kernel
theorem subd6_1_399 : subd6_1 [1, 0, 6] = true := by decide +kernel
theorem subd6_1_400 : subd6_1 [1, 0, 7] = true := by decide +kernel
theorem subd6_1_401 : subd6_1 [1, 0, 8] = true := by decide +kernel
theorem subd6_1_402 : subd6_1 [1, 1, -8] = true := by decide +kernel
theorem subd6_1_403 : subd6_1 [1, 1, -7] = true := by decide +kernel
theorem subd6_1_404 : subd6_1 [1, 1, -6] = true := by decide +kernel
theorem subd6_1_405 : subd6_1 [1, 1, -5] = true := by decide +kernel
theorem subd6_1_406 : subd6_1 [1, 1, -4] = true := by decide +kernel
theorem subd6_1_407 : subd6_1 [1, 1, -3] = true := by decide +kernel
theorem subd6_1_408 : subd6_1 [1, 1, -2] = true := by decide +kernel
theorem subd6_1_409 : subd6_1 [1, 1, -1] = true := by decide +kernel
theorem subd6_1_410 : subd6_1 [1, 1, 0] = true := by decide +kernel
theorem subd6_1_411 : subd6_1 [1, 1, 1] = true := by decide +kernel
theorem subd6_1_412 : subd6_1 [1, 1, 2] = true := by decide +kernel
theorem subd6_1_413 : subd6_1 [1, 1, 3] = true := by decide +kernel
theorem subd6_1_414 : subd6_1 [1, 1, 4] = true := by decide +kernel
theorem subd6_1_415 : subd6_1 [1, 1, 5] = true := by decide +kernel
theorem sbd6_1_12 : ∀ q ∈ blkd6_1_12, subd6_1 q = true := by
  unfold blkd6_1_12
  exact List.forall_mem_cons.2 ⟨subd6_1_384, List.forall_mem_cons.2 ⟨subd6_1_385, List.forall_mem_cons.2 ⟨subd6_1_386, List.forall_mem_cons.2 ⟨subd6_1_387, List.forall_mem_cons.2 ⟨subd6_1_388, List.forall_mem_cons.2 ⟨subd6_1_389, List.forall_mem_cons.2 ⟨subd6_1_390, List.forall_mem_cons.2 ⟨subd6_1_391, List.forall_mem_cons.2 ⟨subd6_1_392, List.forall_mem_cons.2 ⟨subd6_1_393, List.forall_mem_cons.2 ⟨subd6_1_394, List.forall_mem_cons.2 ⟨subd6_1_395, List.forall_mem_cons.2 ⟨subd6_1_396, List.forall_mem_cons.2 ⟨subd6_1_397, List.forall_mem_cons.2 ⟨subd6_1_398, List.forall_mem_cons.2 ⟨subd6_1_399, List.forall_mem_cons.2 ⟨subd6_1_400, List.forall_mem_cons.2 ⟨subd6_1_401, List.forall_mem_cons.2 ⟨subd6_1_402, List.forall_mem_cons.2 ⟨subd6_1_403, List.forall_mem_cons.2 ⟨subd6_1_404, List.forall_mem_cons.2 ⟨subd6_1_405, List.forall_mem_cons.2 ⟨subd6_1_406, List.forall_mem_cons.2 ⟨subd6_1_407, List.forall_mem_cons.2 ⟨subd6_1_408, List.forall_mem_cons.2 ⟨subd6_1_409, List.forall_mem_cons.2 ⟨subd6_1_410, List.forall_mem_cons.2 ⟨subd6_1_411, List.forall_mem_cons.2 ⟨subd6_1_412, List.forall_mem_cons.2 ⟨subd6_1_413, List.forall_mem_cons.2 ⟨subd6_1_414, List.forall_mem_cons.2 ⟨subd6_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
