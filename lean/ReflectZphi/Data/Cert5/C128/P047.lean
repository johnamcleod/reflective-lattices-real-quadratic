import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_6_0 : subd7_6 [-6] = true := by decide +kernel
theorem subd7_6_1 : subd7_6 [-5, -7] = true := by decide +kernel
theorem subd7_6_2 : subd7_6 [-5, -6] = true := by decide +kernel
theorem subd7_6_3 : subd7_6 [-5, -5] = true := by decide +kernel
theorem subd7_6_4 : subd7_6 [-5, -4] = true := by decide +kernel
theorem subd7_6_5 : subd7_6 [-5, -3] = true := by decide +kernel
theorem subd7_6_6 : subd7_6 [-5, -2] = true := by decide +kernel
theorem subd7_6_7 : subd7_6 [-5, -1] = true := by decide +kernel
theorem subd7_6_8 : subd7_6 [-5, 0] = true := by decide +kernel
theorem subd7_6_9 : subd7_6 [-5, 1] = true := by decide +kernel
theorem subd7_6_10 : subd7_6 [-5, 2] = true := by decide +kernel
theorem subd7_6_11 : subd7_6 [-4, -7] = true := by decide +kernel
theorem subd7_6_12 : subd7_6 [-4, -6] = true := by decide +kernel
theorem subd7_6_13 : subd7_6 [-4, -5] = true := by decide +kernel
theorem subd7_6_14 : subd7_6 [-4, -4] = true := by decide +kernel
theorem subd7_6_15 : subd7_6 [-4, -3] = true := by decide +kernel
theorem subd7_6_16 : subd7_6 [-4, -2] = true := by decide +kernel
theorem subd7_6_17 : subd7_6 [-4, -1] = true := by decide +kernel
theorem subd7_6_18 : subd7_6 [-4, 0] = true := by decide +kernel
theorem subd7_6_19 : subd7_6 [-4, 1] = true := by decide +kernel
theorem subd7_6_20 : subd7_6 [-4, 2] = true := by decide +kernel
theorem subd7_6_21 : subd7_6 [-4, 3] = true := by decide +kernel
theorem subd7_6_22 : subd7_6 [-4, 4] = true := by decide +kernel
theorem subd7_6_23 : subd7_6 [-3, -8] = true := by decide +kernel
theorem subd7_6_24 : subd7_6 [-3, -7] = true := by decide +kernel
theorem subd7_6_25 : subd7_6 [-3, -6] = true := by decide +kernel
theorem subd7_6_26 : subd7_6 [-3, -5] = true := by decide +kernel
theorem subd7_6_27 : subd7_6 [-3, -4] = true := by decide +kernel
theorem subd7_6_28 : subd7_6 [-3, -3] = true := by decide +kernel
theorem subd7_6_29 : subd7_6 [-3, -2] = true := by decide +kernel
theorem subd7_6_30 : subd7_6 [-3, -1, -6] = true := by decide +kernel
theorem subd7_6_31 : subd7_6 [-3, -1, -5] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_cons.2 ⟨subd7_6_1, List.forall_mem_cons.2 ⟨subd7_6_2, List.forall_mem_cons.2 ⟨subd7_6_3, List.forall_mem_cons.2 ⟨subd7_6_4, List.forall_mem_cons.2 ⟨subd7_6_5, List.forall_mem_cons.2 ⟨subd7_6_6, List.forall_mem_cons.2 ⟨subd7_6_7, List.forall_mem_cons.2 ⟨subd7_6_8, List.forall_mem_cons.2 ⟨subd7_6_9, List.forall_mem_cons.2 ⟨subd7_6_10, List.forall_mem_cons.2 ⟨subd7_6_11, List.forall_mem_cons.2 ⟨subd7_6_12, List.forall_mem_cons.2 ⟨subd7_6_13, List.forall_mem_cons.2 ⟨subd7_6_14, List.forall_mem_cons.2 ⟨subd7_6_15, List.forall_mem_cons.2 ⟨subd7_6_16, List.forall_mem_cons.2 ⟨subd7_6_17, List.forall_mem_cons.2 ⟨subd7_6_18, List.forall_mem_cons.2 ⟨subd7_6_19, List.forall_mem_cons.2 ⟨subd7_6_20, List.forall_mem_cons.2 ⟨subd7_6_21, List.forall_mem_cons.2 ⟨subd7_6_22, List.forall_mem_cons.2 ⟨subd7_6_23, List.forall_mem_cons.2 ⟨subd7_6_24, List.forall_mem_cons.2 ⟨subd7_6_25, List.forall_mem_cons.2 ⟨subd7_6_26, List.forall_mem_cons.2 ⟨subd7_6_27, List.forall_mem_cons.2 ⟨subd7_6_28, List.forall_mem_cons.2 ⟨subd7_6_29, List.forall_mem_cons.2 ⟨subd7_6_30, List.forall_mem_cons.2 ⟨subd7_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_32 : subd7_6 [-3, -1, -4] = true := by decide +kernel
theorem subd7_6_33 : subd7_6 [-3, -1, -3] = true := by decide +kernel
theorem subd7_6_34 : subd7_6 [-3, -1, -2] = true := by decide +kernel
theorem subd7_6_35 : subd7_6 [-3, -1, -1] = true := by decide +kernel
theorem subd7_6_36 : subd7_6 [-3, -1, 0] = true := by decide +kernel
theorem subd7_6_37 : subd7_6 [-3, -1, 1] = true := by decide +kernel
theorem subd7_6_38 : subd7_6 [-3, -1, 2] = true := by decide +kernel
theorem subd7_6_39 : subd7_6 [-3, -1, 3] = true := by decide +kernel
theorem subd7_6_40 : subd7_6 [-3, -1, 4] = true := by decide +kernel
theorem subd7_6_41 : subd7_6 [-3, -1, 5] = true := by decide +kernel
theorem subd7_6_42 : subd7_6 [-3, -1, 6] = true := by decide +kernel
theorem subd7_6_43 : subd7_6 [-3, 0] = true := by decide +kernel
theorem subd7_6_44 : subd7_6 [-3, 1] = true := by decide +kernel
theorem subd7_6_45 : subd7_6 [-3, 2] = true := by decide +kernel
theorem subd7_6_46 : subd7_6 [-3, 3] = true := by decide +kernel
theorem subd7_6_47 : subd7_6 [-3, 4] = true := by decide +kernel
theorem subd7_6_48 : subd7_6 [-3, 5] = true := by decide +kernel
theorem subd7_6_49 : subd7_6 [-2, -8] = true := by decide +kernel
theorem subd7_6_50 : subd7_6 [-2, -7] = true := by decide +kernel
theorem subd7_6_51 : subd7_6 [-2, -6] = true := by decide +kernel
theorem subd7_6_52 : subd7_6 [-2, -5] = true := by decide +kernel
theorem subd7_6_53 : subd7_6 [-2, -4] = true := by decide +kernel
theorem subd7_6_54 : subd7_6 [-2, -3, -6] = true := by decide +kernel
theorem subd7_6_55 : subd7_6 [-2, -3, -5] = true := by decide +kernel
theorem subd7_6_56 : subd7_6 [-2, -3, -4] = true := by decide +kernel
theorem subd7_6_57 : subd7_6 [-2, -3, -3] = true := by decide +kernel
theorem subd7_6_58 : subd7_6 [-2, -3, -2] = true := by decide +kernel
theorem subd7_6_59 : subd7_6 [-2, -3, -1] = true := by decide +kernel
theorem subd7_6_60 : subd7_6 [-2, -3, 0] = true := by decide +kernel
theorem subd7_6_61 : subd7_6 [-2, -3, 1] = true := by decide +kernel
theorem subd7_6_62 : subd7_6 [-2, -3, 2] = true := by decide +kernel
theorem subd7_6_63 : subd7_6 [-2, -3, 3] = true := by decide +kernel
theorem sbd7_6_1 : ∀ q ∈ blkd7_6_1, subd7_6 q = true := by
  unfold blkd7_6_1
  exact List.forall_mem_cons.2 ⟨subd7_6_32, List.forall_mem_cons.2 ⟨subd7_6_33, List.forall_mem_cons.2 ⟨subd7_6_34, List.forall_mem_cons.2 ⟨subd7_6_35, List.forall_mem_cons.2 ⟨subd7_6_36, List.forall_mem_cons.2 ⟨subd7_6_37, List.forall_mem_cons.2 ⟨subd7_6_38, List.forall_mem_cons.2 ⟨subd7_6_39, List.forall_mem_cons.2 ⟨subd7_6_40, List.forall_mem_cons.2 ⟨subd7_6_41, List.forall_mem_cons.2 ⟨subd7_6_42, List.forall_mem_cons.2 ⟨subd7_6_43, List.forall_mem_cons.2 ⟨subd7_6_44, List.forall_mem_cons.2 ⟨subd7_6_45, List.forall_mem_cons.2 ⟨subd7_6_46, List.forall_mem_cons.2 ⟨subd7_6_47, List.forall_mem_cons.2 ⟨subd7_6_48, List.forall_mem_cons.2 ⟨subd7_6_49, List.forall_mem_cons.2 ⟨subd7_6_50, List.forall_mem_cons.2 ⟨subd7_6_51, List.forall_mem_cons.2 ⟨subd7_6_52, List.forall_mem_cons.2 ⟨subd7_6_53, List.forall_mem_cons.2 ⟨subd7_6_54, List.forall_mem_cons.2 ⟨subd7_6_55, List.forall_mem_cons.2 ⟨subd7_6_56, List.forall_mem_cons.2 ⟨subd7_6_57, List.forall_mem_cons.2 ⟨subd7_6_58, List.forall_mem_cons.2 ⟨subd7_6_59, List.forall_mem_cons.2 ⟨subd7_6_60, List.forall_mem_cons.2 ⟨subd7_6_61, List.forall_mem_cons.2 ⟨subd7_6_62, List.forall_mem_cons.2 ⟨subd7_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_64 : subd7_6 [-2, -3, 4] = true := by decide +kernel
theorem subd7_6_65 : subd7_6 [-2, -3, 5] = true := by decide +kernel
theorem subd7_6_66 : subd7_6 [-2, -3, 6] = true := by decide +kernel
theorem subd7_6_67 : subd7_6 [-2, -2, -6] = true := by decide +kernel
theorem subd7_6_68 : subd7_6 [-2, -2, -5] = true := by decide +kernel
theorem subd7_6_69 : subd7_6 [-2, -2, -4] = true := by decide +kernel
theorem subd7_6_70 : subd7_6 [-2, -2, -3] = true := by decide +kernel
theorem subd7_6_71 : subd7_6 [-2, -2, -2] = true := by decide +kernel
theorem subd7_6_72 : subd7_6 [-2, -2, -1] = true := by decide +kernel
theorem subd7_6_73 : subd7_6 [-2, -2, 0] = true := by decide +kernel
theorem subd7_6_74 : subd7_6 [-2, -2, 1] = true := by decide +kernel
theorem subd7_6_75 : subd7_6 [-2, -2, 2] = true := by decide +kernel
theorem subd7_6_76 : subd7_6 [-2, -2, 3] = true := by decide +kernel
theorem subd7_6_77 : subd7_6 [-2, -2, 4] = true := by decide +kernel
theorem subd7_6_78 : subd7_6 [-2, -2, 5] = true := by decide +kernel
theorem subd7_6_79 : subd7_6 [-2, -2, 6] = true := by decide +kernel
theorem subd7_6_80 : subd7_6 [-2, -1, -7] = true := by decide +kernel
theorem subd7_6_81 : subd7_6 [-2, -1, -6] = true := by decide +kernel
theorem subd7_6_82 : subd7_6 [-2, -1, -5] = true := by decide +kernel
theorem subd7_6_83 : subd7_6 [-2, -1, -4] = true := by decide +kernel
theorem subd7_6_84 : subd7_6 [-2, -1, -3] = true := by decide +kernel
theorem subd7_6_85 : subd7_6 [-2, -1, -2] = true := by decide +kernel
theorem subd7_6_86 : subd7_6 [-2, -1, -1] = true := by decide +kernel
theorem subd7_6_87 : subd7_6 [-2, -1, 0] = true := by decide +kernel
theorem subd7_6_88 : subd7_6 [-2, -1, 1] = true := by decide +kernel
theorem subd7_6_89 : subd7_6 [-2, -1, 2] = true := by decide +kernel
theorem subd7_6_90 : subd7_6 [-2, -1, 3] = true := by decide +kernel
theorem subd7_6_91 : subd7_6 [-2, -1, 4] = true := by decide +kernel
theorem subd7_6_92 : subd7_6 [-2, -1, 5] = true := by decide +kernel
theorem subd7_6_93 : subd7_6 [-2, -1, 6] = true := by decide +kernel
theorem subd7_6_94 : subd7_6 [-2, 0, -7] = true := by decide +kernel
theorem subd7_6_95 : subd7_6 [-2, 0, -6] = true := by decide +kernel
theorem sbd7_6_2 : ∀ q ∈ blkd7_6_2, subd7_6 q = true := by
  unfold blkd7_6_2
  exact List.forall_mem_cons.2 ⟨subd7_6_64, List.forall_mem_cons.2 ⟨subd7_6_65, List.forall_mem_cons.2 ⟨subd7_6_66, List.forall_mem_cons.2 ⟨subd7_6_67, List.forall_mem_cons.2 ⟨subd7_6_68, List.forall_mem_cons.2 ⟨subd7_6_69, List.forall_mem_cons.2 ⟨subd7_6_70, List.forall_mem_cons.2 ⟨subd7_6_71, List.forall_mem_cons.2 ⟨subd7_6_72, List.forall_mem_cons.2 ⟨subd7_6_73, List.forall_mem_cons.2 ⟨subd7_6_74, List.forall_mem_cons.2 ⟨subd7_6_75, List.forall_mem_cons.2 ⟨subd7_6_76, List.forall_mem_cons.2 ⟨subd7_6_77, List.forall_mem_cons.2 ⟨subd7_6_78, List.forall_mem_cons.2 ⟨subd7_6_79, List.forall_mem_cons.2 ⟨subd7_6_80, List.forall_mem_cons.2 ⟨subd7_6_81, List.forall_mem_cons.2 ⟨subd7_6_82, List.forall_mem_cons.2 ⟨subd7_6_83, List.forall_mem_cons.2 ⟨subd7_6_84, List.forall_mem_cons.2 ⟨subd7_6_85, List.forall_mem_cons.2 ⟨subd7_6_86, List.forall_mem_cons.2 ⟨subd7_6_87, List.forall_mem_cons.2 ⟨subd7_6_88, List.forall_mem_cons.2 ⟨subd7_6_89, List.forall_mem_cons.2 ⟨subd7_6_90, List.forall_mem_cons.2 ⟨subd7_6_91, List.forall_mem_cons.2 ⟨subd7_6_92, List.forall_mem_cons.2 ⟨subd7_6_93, List.forall_mem_cons.2 ⟨subd7_6_94, List.forall_mem_cons.2 ⟨subd7_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_96 : subd7_6 [-2, 0, -5] = true := by decide +kernel
theorem subd7_6_97 : subd7_6 [-2, 0, -4] = true := by decide +kernel
theorem subd7_6_98 : subd7_6 [-2, 0, -3] = true := by decide +kernel
theorem subd7_6_99 : subd7_6 [-2, 0, -2] = true := by decide +kernel
theorem subd7_6_100 : subd7_6 [-2, 0, -1] = true := by decide +kernel
theorem subd7_6_101 : subd7_6 [-2, 0, 0] = true := by decide +kernel
theorem subd7_6_102 : subd7_6 [-2, 0, 1] = true := by decide +kernel
theorem subd7_6_103 : subd7_6 [-2, 0, 2] = true := by decide +kernel
theorem subd7_6_104 : subd7_6 [-2, 0, 3] = true := by decide +kernel
theorem subd7_6_105 : subd7_6 [-2, 0, 4] = true := by decide +kernel
theorem subd7_6_106 : subd7_6 [-2, 0, 5] = true := by decide +kernel
theorem subd7_6_107 : subd7_6 [-2, 0, 6] = true := by decide +kernel
theorem subd7_6_108 : subd7_6 [-2, 1, -7] = true := by decide +kernel
theorem subd7_6_109 : subd7_6 [-2, 1, -6] = true := by decide +kernel
theorem subd7_6_110 : subd7_6 [-2, 1, -5] = true := by decide +kernel
theorem subd7_6_111 : subd7_6 [-2, 1, -4] = true := by decide +kernel
theorem subd7_6_112 : subd7_6 [-2, 1, -3] = true := by decide +kernel
theorem subd7_6_113 : subd7_6 [-2, 1, -2] = true := by decide +kernel
theorem subd7_6_114 : subd7_6 [-2, 1, -1] = true := by decide +kernel
theorem subd7_6_115 : subd7_6 [-2, 1, 0] = true := by decide +kernel
theorem subd7_6_116 : subd7_6 [-2, 1, 1] = true := by decide +kernel
theorem subd7_6_117 : subd7_6 [-2, 1, 2] = true := by decide +kernel
theorem subd7_6_118 : subd7_6 [-2, 1, 3] = true := by decide +kernel
theorem subd7_6_119 : subd7_6 [-2, 1, 4] = true := by decide +kernel
theorem subd7_6_120 : subd7_6 [-2, 1, 5] = true := by decide +kernel
theorem subd7_6_121 : subd7_6 [-2, 1, 6] = true := by decide +kernel
theorem subd7_6_122 : subd7_6 [-2, 2] = true := by decide +kernel
theorem subd7_6_123 : subd7_6 [-2, 3] = true := by decide +kernel
theorem subd7_6_124 : subd7_6 [-2, 4] = true := by decide +kernel
theorem subd7_6_125 : subd7_6 [-2, 5] = true := by decide +kernel
theorem subd7_6_126 : subd7_6 [-1, -8] = true := by decide +kernel
theorem subd7_6_127 : subd7_6 [-1, -7] = true := by decide +kernel
theorem sbd7_6_3 : ∀ q ∈ blkd7_6_3, subd7_6 q = true := by
  unfold blkd7_6_3
  exact List.forall_mem_cons.2 ⟨subd7_6_96, List.forall_mem_cons.2 ⟨subd7_6_97, List.forall_mem_cons.2 ⟨subd7_6_98, List.forall_mem_cons.2 ⟨subd7_6_99, List.forall_mem_cons.2 ⟨subd7_6_100, List.forall_mem_cons.2 ⟨subd7_6_101, List.forall_mem_cons.2 ⟨subd7_6_102, List.forall_mem_cons.2 ⟨subd7_6_103, List.forall_mem_cons.2 ⟨subd7_6_104, List.forall_mem_cons.2 ⟨subd7_6_105, List.forall_mem_cons.2 ⟨subd7_6_106, List.forall_mem_cons.2 ⟨subd7_6_107, List.forall_mem_cons.2 ⟨subd7_6_108, List.forall_mem_cons.2 ⟨subd7_6_109, List.forall_mem_cons.2 ⟨subd7_6_110, List.forall_mem_cons.2 ⟨subd7_6_111, List.forall_mem_cons.2 ⟨subd7_6_112, List.forall_mem_cons.2 ⟨subd7_6_113, List.forall_mem_cons.2 ⟨subd7_6_114, List.forall_mem_cons.2 ⟨subd7_6_115, List.forall_mem_cons.2 ⟨subd7_6_116, List.forall_mem_cons.2 ⟨subd7_6_117, List.forall_mem_cons.2 ⟨subd7_6_118, List.forall_mem_cons.2 ⟨subd7_6_119, List.forall_mem_cons.2 ⟨subd7_6_120, List.forall_mem_cons.2 ⟨subd7_6_121, List.forall_mem_cons.2 ⟨subd7_6_122, List.forall_mem_cons.2 ⟨subd7_6_123, List.forall_mem_cons.2 ⟨subd7_6_124, List.forall_mem_cons.2 ⟨subd7_6_125, List.forall_mem_cons.2 ⟨subd7_6_126, List.forall_mem_cons.2 ⟨subd7_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_128 : subd7_6 [-1, -6] = true := by decide +kernel
theorem subd7_6_129 : subd7_6 [-1, -5] = true := by decide +kernel
theorem subd7_6_130 : subd7_6 [-1, -4] = true := by decide +kernel
theorem subd7_6_131 : subd7_6 [-1, -3, -6] = true := by decide +kernel
theorem subd7_6_132 : subd7_6 [-1, -3, -5] = true := by decide +kernel
theorem subd7_6_133 : subd7_6 [-1, -3, -4] = true := by decide +kernel
theorem subd7_6_134 : subd7_6 [-1, -3, -3] = true := by decide +kernel
theorem subd7_6_135 : subd7_6 [-1, -3, -2] = true := by decide +kernel
theorem subd7_6_136 : subd7_6 [-1, -3, -1] = true := by decide +kernel
theorem subd7_6_137 : subd7_6 [-1, -3, 0] = true := by decide +kernel
theorem subd7_6_138 : subd7_6 [-1, -3, 1] = true := by decide +kernel
theorem subd7_6_139 : subd7_6 [-1, -3, 2] = true := by decide +kernel
theorem subd7_6_140 : subd7_6 [-1, -3, 3] = true := by decide +kernel
theorem subd7_6_141 : subd7_6 [-1, -3, 4] = true := by decide +kernel
theorem subd7_6_142 : subd7_6 [-1, -3, 5] = true := by decide +kernel
theorem subd7_6_143 : subd7_6 [-1, -3, 6] = true := by decide +kernel
theorem subd7_6_144 : subd7_6 [-1, -2, -7] = true := by decide +kernel
theorem subd7_6_145 : subd7_6 [-1, -2, -6] = true := by decide +kernel
theorem subd7_6_146 : subd7_6 [-1, -2, -5] = true := by decide +kernel
theorem subd7_6_147 : subd7_6 [-1, -2, -4] = true := by decide +kernel
theorem subd7_6_148 : subd7_6 [-1, -2, -3] = true := by decide +kernel
theorem subd7_6_149 : subd7_6 [-1, -2, -2] = true := by decide +kernel
theorem subd7_6_150 : subd7_6 [-1, -2, -1] = true := by decide +kernel
theorem subd7_6_151 : subd7_6 [-1, -2, 0] = true := by decide +kernel
theorem subd7_6_152 : subd7_6 [-1, -2, 1] = true := by decide +kernel
theorem subd7_6_153 : subd7_6 [-1, -2, 2] = true := by decide +kernel
theorem subd7_6_154 : subd7_6 [-1, -2, 3] = true := by decide +kernel
theorem subd7_6_155 : subd7_6 [-1, -2, 4] = true := by decide +kernel
theorem subd7_6_156 : subd7_6 [-1, -2, 5] = true := by decide +kernel
theorem subd7_6_157 : subd7_6 [-1, -2, 6] = true := by decide +kernel
theorem subd7_6_158 : subd7_6 [-1, -2, 7] = true := by decide +kernel
theorem subd7_6_159 : subd7_6 [-1, -1, -7] = true := by decide +kernel
theorem sbd7_6_4 : ∀ q ∈ blkd7_6_4, subd7_6 q = true := by
  unfold blkd7_6_4
  exact List.forall_mem_cons.2 ⟨subd7_6_128, List.forall_mem_cons.2 ⟨subd7_6_129, List.forall_mem_cons.2 ⟨subd7_6_130, List.forall_mem_cons.2 ⟨subd7_6_131, List.forall_mem_cons.2 ⟨subd7_6_132, List.forall_mem_cons.2 ⟨subd7_6_133, List.forall_mem_cons.2 ⟨subd7_6_134, List.forall_mem_cons.2 ⟨subd7_6_135, List.forall_mem_cons.2 ⟨subd7_6_136, List.forall_mem_cons.2 ⟨subd7_6_137, List.forall_mem_cons.2 ⟨subd7_6_138, List.forall_mem_cons.2 ⟨subd7_6_139, List.forall_mem_cons.2 ⟨subd7_6_140, List.forall_mem_cons.2 ⟨subd7_6_141, List.forall_mem_cons.2 ⟨subd7_6_142, List.forall_mem_cons.2 ⟨subd7_6_143, List.forall_mem_cons.2 ⟨subd7_6_144, List.forall_mem_cons.2 ⟨subd7_6_145, List.forall_mem_cons.2 ⟨subd7_6_146, List.forall_mem_cons.2 ⟨subd7_6_147, List.forall_mem_cons.2 ⟨subd7_6_148, List.forall_mem_cons.2 ⟨subd7_6_149, List.forall_mem_cons.2 ⟨subd7_6_150, List.forall_mem_cons.2 ⟨subd7_6_151, List.forall_mem_cons.2 ⟨subd7_6_152, List.forall_mem_cons.2 ⟨subd7_6_153, List.forall_mem_cons.2 ⟨subd7_6_154, List.forall_mem_cons.2 ⟨subd7_6_155, List.forall_mem_cons.2 ⟨subd7_6_156, List.forall_mem_cons.2 ⟨subd7_6_157, List.forall_mem_cons.2 ⟨subd7_6_158, List.forall_mem_cons.2 ⟨subd7_6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_160 : subd7_6 [-1, -1, -6] = true := by decide +kernel
theorem subd7_6_161 : subd7_6 [-1, -1, -5] = true := by decide +kernel
theorem subd7_6_162 : subd7_6 [-1, -1, -4] = true := by decide +kernel
theorem subd7_6_163 : subd7_6 [-1, -1, -3] = true := by decide +kernel
theorem subd7_6_164 : subd7_6 [-1, -1, -2] = true := by decide +kernel
theorem subd7_6_165 : subd7_6 [-1, -1, -1] = true := by decide +kernel
theorem subd7_6_166 : subd7_6 [-1, -1, 0] = true := by decide +kernel
theorem subd7_6_167 : subd7_6 [-1, -1, 1] = true := by decide +kernel
theorem subd7_6_168 : subd7_6 [-1, -1, 2] = true := by decide +kernel
theorem subd7_6_169 : subd7_6 [-1, -1, 3] = true := by decide +kernel
theorem subd7_6_170 : subd7_6 [-1, -1, 4] = true := by decide +kernel
theorem subd7_6_171 : subd7_6 [-1, -1, 5] = true := by decide +kernel
theorem subd7_6_172 : subd7_6 [-1, -1, 6] = true := by decide +kernel
theorem subd7_6_173 : subd7_6 [-1, -1, 7] = true := by decide +kernel
theorem subd7_6_174 : subd7_6 [-1, 0, -7] = true := by decide +kernel
theorem subd7_6_175 : subd7_6 [-1, 0, -6] = true := by decide +kernel
theorem subd7_6_176 : subd7_6 [-1, 0, -5] = true := by decide +kernel
theorem subd7_6_177 : subd7_6 [-1, 0, -4] = true := by decide +kernel
theorem subd7_6_178 : subd7_6 [-1, 0, -3] = true := by decide +kernel
theorem subd7_6_179 : subd7_6 [-1, 0, -2] = true := by decide +kernel
theorem subd7_6_180 : subd7_6 [-1, 0, -1] = true := by decide +kernel
theorem subd7_6_181 : subd7_6 [-1, 0, 0] = true := by decide +kernel
theorem subd7_6_182 : subd7_6 [-1, 0, 1] = true := by decide +kernel
theorem subd7_6_183 : subd7_6 [-1, 0, 2] = true := by decide +kernel
theorem subd7_6_184 : subd7_6 [-1, 0, 3] = true := by decide +kernel
theorem subd7_6_185 : subd7_6 [-1, 0, 4] = true := by decide +kernel
theorem subd7_6_186 : subd7_6 [-1, 0, 5] = true := by decide +kernel
theorem subd7_6_187 : subd7_6 [-1, 0, 6] = true := by decide +kernel
theorem subd7_6_188 : subd7_6 [-1, 1, -7] = true := by decide +kernel
theorem subd7_6_189 : subd7_6 [-1, 1, -6] = true := by decide +kernel
theorem subd7_6_190 : subd7_6 [-1, 1, -5] = true := by decide +kernel
theorem subd7_6_191 : subd7_6 [-1, 1, -4] = true := by decide +kernel
theorem sbd7_6_5 : ∀ q ∈ blkd7_6_5, subd7_6 q = true := by
  unfold blkd7_6_5
  exact List.forall_mem_cons.2 ⟨subd7_6_160, List.forall_mem_cons.2 ⟨subd7_6_161, List.forall_mem_cons.2 ⟨subd7_6_162, List.forall_mem_cons.2 ⟨subd7_6_163, List.forall_mem_cons.2 ⟨subd7_6_164, List.forall_mem_cons.2 ⟨subd7_6_165, List.forall_mem_cons.2 ⟨subd7_6_166, List.forall_mem_cons.2 ⟨subd7_6_167, List.forall_mem_cons.2 ⟨subd7_6_168, List.forall_mem_cons.2 ⟨subd7_6_169, List.forall_mem_cons.2 ⟨subd7_6_170, List.forall_mem_cons.2 ⟨subd7_6_171, List.forall_mem_cons.2 ⟨subd7_6_172, List.forall_mem_cons.2 ⟨subd7_6_173, List.forall_mem_cons.2 ⟨subd7_6_174, List.forall_mem_cons.2 ⟨subd7_6_175, List.forall_mem_cons.2 ⟨subd7_6_176, List.forall_mem_cons.2 ⟨subd7_6_177, List.forall_mem_cons.2 ⟨subd7_6_178, List.forall_mem_cons.2 ⟨subd7_6_179, List.forall_mem_cons.2 ⟨subd7_6_180, List.forall_mem_cons.2 ⟨subd7_6_181, List.forall_mem_cons.2 ⟨subd7_6_182, List.forall_mem_cons.2 ⟨subd7_6_183, List.forall_mem_cons.2 ⟨subd7_6_184, List.forall_mem_cons.2 ⟨subd7_6_185, List.forall_mem_cons.2 ⟨subd7_6_186, List.forall_mem_cons.2 ⟨subd7_6_187, List.forall_mem_cons.2 ⟨subd7_6_188, List.forall_mem_cons.2 ⟨subd7_6_189, List.forall_mem_cons.2 ⟨subd7_6_190, List.forall_mem_cons.2 ⟨subd7_6_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_192 : subd7_6 [-1, 1, -3] = true := by decide +kernel
theorem subd7_6_193 : subd7_6 [-1, 1, -2] = true := by decide +kernel
theorem subd7_6_194 : subd7_6 [-1, 1, -1] = true := by decide +kernel
theorem subd7_6_195 : subd7_6 [-1, 1, 0] = true := by decide +kernel
theorem subd7_6_196 : subd7_6 [-1, 1, 1] = true := by decide +kernel
theorem subd7_6_197 : subd7_6 [-1, 1, 2] = true := by decide +kernel
theorem subd7_6_198 : subd7_6 [-1, 1, 3] = true := by decide +kernel
theorem subd7_6_199 : subd7_6 [-1, 1, 4] = true := by decide +kernel
theorem subd7_6_200 : subd7_6 [-1, 1, 5] = true := by decide +kernel
theorem subd7_6_201 : subd7_6 [-1, 1, 6] = true := by decide +kernel
theorem subd7_6_202 : subd7_6 [-1, 2, -7] = true := by decide +kernel
theorem subd7_6_203 : subd7_6 [-1, 2, -6] = true := by decide +kernel
theorem subd7_6_204 : subd7_6 [-1, 2, -5] = true := by decide +kernel
theorem subd7_6_205 : subd7_6 [-1, 2, -4] = true := by decide +kernel
theorem subd7_6_206 : subd7_6 [-1, 2, -3] = true := by decide +kernel
theorem subd7_6_207 : subd7_6 [-1, 2, -2] = true := by decide +kernel
theorem subd7_6_208 : subd7_6 [-1, 2, -1] = true := by decide +kernel
theorem subd7_6_209 : subd7_6 [-1, 2, 0] = true := by decide +kernel
theorem subd7_6_210 : subd7_6 [-1, 2, 1] = true := by decide +kernel
theorem subd7_6_211 : subd7_6 [-1, 2, 2] = true := by decide +kernel
theorem subd7_6_212 : subd7_6 [-1, 2, 3] = true := by decide +kernel
theorem subd7_6_213 : subd7_6 [-1, 2, 4] = true := by decide +kernel
theorem subd7_6_214 : subd7_6 [-1, 2, 5] = true := by decide +kernel
theorem subd7_6_215 : subd7_6 [-1, 2, 6] = true := by decide +kernel
theorem subd7_6_216 : subd7_6 [-1, 3] = true := by decide +kernel
theorem subd7_6_217 : subd7_6 [-1, 4] = true := by decide +kernel
theorem subd7_6_218 : subd7_6 [-1, 5] = true := by decide +kernel
theorem subd7_6_219 : subd7_6 [-1, 6] = true := by decide +kernel
theorem subd7_6_220 : subd7_6 [0, -8] = true := by decide +kernel
theorem subd7_6_221 : subd7_6 [0, -7] = true := by decide +kernel
theorem subd7_6_222 : subd7_6 [0, -6] = true := by decide +kernel
theorem subd7_6_223 : subd7_6 [0, -5] = true := by decide +kernel
theorem sbd7_6_6 : ∀ q ∈ blkd7_6_6, subd7_6 q = true := by
  unfold blkd7_6_6
  exact List.forall_mem_cons.2 ⟨subd7_6_192, List.forall_mem_cons.2 ⟨subd7_6_193, List.forall_mem_cons.2 ⟨subd7_6_194, List.forall_mem_cons.2 ⟨subd7_6_195, List.forall_mem_cons.2 ⟨subd7_6_196, List.forall_mem_cons.2 ⟨subd7_6_197, List.forall_mem_cons.2 ⟨subd7_6_198, List.forall_mem_cons.2 ⟨subd7_6_199, List.forall_mem_cons.2 ⟨subd7_6_200, List.forall_mem_cons.2 ⟨subd7_6_201, List.forall_mem_cons.2 ⟨subd7_6_202, List.forall_mem_cons.2 ⟨subd7_6_203, List.forall_mem_cons.2 ⟨subd7_6_204, List.forall_mem_cons.2 ⟨subd7_6_205, List.forall_mem_cons.2 ⟨subd7_6_206, List.forall_mem_cons.2 ⟨subd7_6_207, List.forall_mem_cons.2 ⟨subd7_6_208, List.forall_mem_cons.2 ⟨subd7_6_209, List.forall_mem_cons.2 ⟨subd7_6_210, List.forall_mem_cons.2 ⟨subd7_6_211, List.forall_mem_cons.2 ⟨subd7_6_212, List.forall_mem_cons.2 ⟨subd7_6_213, List.forall_mem_cons.2 ⟨subd7_6_214, List.forall_mem_cons.2 ⟨subd7_6_215, List.forall_mem_cons.2 ⟨subd7_6_216, List.forall_mem_cons.2 ⟨subd7_6_217, List.forall_mem_cons.2 ⟨subd7_6_218, List.forall_mem_cons.2 ⟨subd7_6_219, List.forall_mem_cons.2 ⟨subd7_6_220, List.forall_mem_cons.2 ⟨subd7_6_221, List.forall_mem_cons.2 ⟨subd7_6_222, List.forall_mem_cons.2 ⟨subd7_6_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_224 : subd7_6 [0, -4] = true := by decide +kernel
theorem subd7_6_225 : subd7_6 [0, -3, -6] = true := by decide +kernel
theorem subd7_6_226 : subd7_6 [0, -3, -5] = true := by decide +kernel
theorem subd7_6_227 : subd7_6 [0, -3, -4] = true := by decide +kernel
theorem subd7_6_228 : subd7_6 [0, -3, -3] = true := by decide +kernel
theorem subd7_6_229 : subd7_6 [0, -3, -2] = true := by decide +kernel
theorem subd7_6_230 : subd7_6 [0, -3, -1] = true := by decide +kernel
theorem subd7_6_231 : subd7_6 [0, -3, 0] = true := by decide +kernel
theorem subd7_6_232 : subd7_6 [0, -3, 1] = true := by decide +kernel
theorem subd7_6_233 : subd7_6 [0, -3, 2] = true := by decide +kernel
theorem subd7_6_234 : subd7_6 [0, -3, 3] = true := by decide +kernel
theorem subd7_6_235 : subd7_6 [0, -3, 4] = true := by decide +kernel
theorem subd7_6_236 : subd7_6 [0, -3, 5] = true := by decide +kernel
theorem subd7_6_237 : subd7_6 [0, -3, 6] = true := by decide +kernel
theorem subd7_6_238 : subd7_6 [0, -2, -7] = true := by decide +kernel
theorem subd7_6_239 : subd7_6 [0, -2, -6] = true := by decide +kernel
theorem subd7_6_240 : subd7_6 [0, -2, -5] = true := by decide +kernel
theorem subd7_6_241 : subd7_6 [0, -2, -4] = true := by decide +kernel
theorem subd7_6_242 : subd7_6 [0, -2, -3] = true := by decide +kernel
theorem subd7_6_243 : subd7_6 [0, -2, -2] = true := by decide +kernel
theorem subd7_6_244 : subd7_6 [0, -2, -1] = true := by decide +kernel
theorem subd7_6_245 : subd7_6 [0, -2, 0] = true := by decide +kernel
theorem subd7_6_246 : subd7_6 [0, -2, 1] = true := by decide +kernel
theorem subd7_6_247 : subd7_6 [0, -2, 2] = true := by decide +kernel
theorem subd7_6_248 : subd7_6 [0, -2, 3] = true := by decide +kernel
theorem subd7_6_249 : subd7_6 [0, -2, 4] = true := by decide +kernel
theorem subd7_6_250 : subd7_6 [0, -2, 5] = true := by decide +kernel
theorem subd7_6_251 : subd7_6 [0, -2, 6] = true := by decide +kernel
theorem subd7_6_252 : subd7_6 [0, -1, -7] = true := by decide +kernel
theorem subd7_6_253 : subd7_6 [0, -1, -6] = true := by decide +kernel
theorem subd7_6_254 : subd7_6 [0, -1, -5] = true := by decide +kernel
theorem subd7_6_255 : subd7_6 [0, -1, -4] = true := by decide +kernel
theorem sbd7_6_7 : ∀ q ∈ blkd7_6_7, subd7_6 q = true := by
  unfold blkd7_6_7
  exact List.forall_mem_cons.2 ⟨subd7_6_224, List.forall_mem_cons.2 ⟨subd7_6_225, List.forall_mem_cons.2 ⟨subd7_6_226, List.forall_mem_cons.2 ⟨subd7_6_227, List.forall_mem_cons.2 ⟨subd7_6_228, List.forall_mem_cons.2 ⟨subd7_6_229, List.forall_mem_cons.2 ⟨subd7_6_230, List.forall_mem_cons.2 ⟨subd7_6_231, List.forall_mem_cons.2 ⟨subd7_6_232, List.forall_mem_cons.2 ⟨subd7_6_233, List.forall_mem_cons.2 ⟨subd7_6_234, List.forall_mem_cons.2 ⟨subd7_6_235, List.forall_mem_cons.2 ⟨subd7_6_236, List.forall_mem_cons.2 ⟨subd7_6_237, List.forall_mem_cons.2 ⟨subd7_6_238, List.forall_mem_cons.2 ⟨subd7_6_239, List.forall_mem_cons.2 ⟨subd7_6_240, List.forall_mem_cons.2 ⟨subd7_6_241, List.forall_mem_cons.2 ⟨subd7_6_242, List.forall_mem_cons.2 ⟨subd7_6_243, List.forall_mem_cons.2 ⟨subd7_6_244, List.forall_mem_cons.2 ⟨subd7_6_245, List.forall_mem_cons.2 ⟨subd7_6_246, List.forall_mem_cons.2 ⟨subd7_6_247, List.forall_mem_cons.2 ⟨subd7_6_248, List.forall_mem_cons.2 ⟨subd7_6_249, List.forall_mem_cons.2 ⟨subd7_6_250, List.forall_mem_cons.2 ⟨subd7_6_251, List.forall_mem_cons.2 ⟨subd7_6_252, List.forall_mem_cons.2 ⟨subd7_6_253, List.forall_mem_cons.2 ⟨subd7_6_254, List.forall_mem_cons.2 ⟨subd7_6_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_256 : subd7_6 [0, -1, -3] = true := by decide +kernel
theorem subd7_6_257 : subd7_6 [0, -1, -2] = true := by decide +kernel
theorem subd7_6_258 : subd7_6 [0, -1, -1] = true := by decide +kernel
theorem subd7_6_259 : subd7_6 [0, -1, 0] = true := by decide +kernel
theorem subd7_6_260 : subd7_6 [0, -1, 1] = true := by decide +kernel
theorem subd7_6_261 : subd7_6 [0, -1, 2] = true := by decide +kernel
theorem subd7_6_262 : subd7_6 [0, -1, 3] = true := by decide +kernel
theorem subd7_6_263 : subd7_6 [0, -1, 4] = true := by decide +kernel
theorem subd7_6_264 : subd7_6 [0, -1, 5] = true := by decide +kernel
theorem subd7_6_265 : subd7_6 [0, -1, 6] = true := by decide +kernel
theorem subd7_6_266 : subd7_6 [0, -1, 7] = true := by decide +kernel
theorem subd7_6_267 : subd7_6 [0, 0, -7] = true := by decide +kernel
theorem subd7_6_268 : subd7_6 [0, 0, -6] = true := by decide +kernel
theorem subd7_6_269 : subd7_6 [0, 0, -5] = true := by decide +kernel
theorem subd7_6_270 : subd7_6 [0, 0, -4] = true := by decide +kernel
theorem subd7_6_271 : subd7_6 [0, 0, -3] = true := by decide +kernel
theorem subd7_6_272 : subd7_6 [0, 0, -2] = true := by decide +kernel
theorem subd7_6_273 : subd7_6 [0, 0, -1] = true := by decide +kernel
theorem subd7_6_274 : subd7_6 [0, 0, 0] = true := by decide +kernel
theorem subd7_6_275 : subd7_6 [0, 0, 1] = true := by decide +kernel
theorem subd7_6_276 : subd7_6 [0, 0, 2] = true := by decide +kernel
theorem subd7_6_277 : subd7_6 [0, 0, 3] = true := by decide +kernel
theorem subd7_6_278 : subd7_6 [0, 0, 4] = true := by decide +kernel
theorem subd7_6_279 : subd7_6 [0, 0, 5] = true := by decide +kernel
theorem subd7_6_280 : subd7_6 [0, 0, 6] = true := by decide +kernel
theorem subd7_6_281 : subd7_6 [0, 1, -8] = true := by decide +kernel
theorem subd7_6_282 : subd7_6 [0, 1, -7] = true := by decide +kernel
theorem subd7_6_283 : subd7_6 [0, 1, -6] = true := by decide +kernel
theorem subd7_6_284 : subd7_6 [0, 1, -5] = true := by decide +kernel
theorem subd7_6_285 : subd7_6 [0, 1, -4] = true := by decide +kernel
theorem subd7_6_286 : subd7_6 [0, 1, -3] = true := by decide +kernel
theorem subd7_6_287 : subd7_6 [0, 1, -2] = true := by decide +kernel
theorem sbd7_6_8 : ∀ q ∈ blkd7_6_8, subd7_6 q = true := by
  unfold blkd7_6_8
  exact List.forall_mem_cons.2 ⟨subd7_6_256, List.forall_mem_cons.2 ⟨subd7_6_257, List.forall_mem_cons.2 ⟨subd7_6_258, List.forall_mem_cons.2 ⟨subd7_6_259, List.forall_mem_cons.2 ⟨subd7_6_260, List.forall_mem_cons.2 ⟨subd7_6_261, List.forall_mem_cons.2 ⟨subd7_6_262, List.forall_mem_cons.2 ⟨subd7_6_263, List.forall_mem_cons.2 ⟨subd7_6_264, List.forall_mem_cons.2 ⟨subd7_6_265, List.forall_mem_cons.2 ⟨subd7_6_266, List.forall_mem_cons.2 ⟨subd7_6_267, List.forall_mem_cons.2 ⟨subd7_6_268, List.forall_mem_cons.2 ⟨subd7_6_269, List.forall_mem_cons.2 ⟨subd7_6_270, List.forall_mem_cons.2 ⟨subd7_6_271, List.forall_mem_cons.2 ⟨subd7_6_272, List.forall_mem_cons.2 ⟨subd7_6_273, List.forall_mem_cons.2 ⟨subd7_6_274, List.forall_mem_cons.2 ⟨subd7_6_275, List.forall_mem_cons.2 ⟨subd7_6_276, List.forall_mem_cons.2 ⟨subd7_6_277, List.forall_mem_cons.2 ⟨subd7_6_278, List.forall_mem_cons.2 ⟨subd7_6_279, List.forall_mem_cons.2 ⟨subd7_6_280, List.forall_mem_cons.2 ⟨subd7_6_281, List.forall_mem_cons.2 ⟨subd7_6_282, List.forall_mem_cons.2 ⟨subd7_6_283, List.forall_mem_cons.2 ⟨subd7_6_284, List.forall_mem_cons.2 ⟨subd7_6_285, List.forall_mem_cons.2 ⟨subd7_6_286, List.forall_mem_cons.2 ⟨subd7_6_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_288 : subd7_6 [0, 1, -1] = true := by decide +kernel
theorem subd7_6_289 : subd7_6 [0, 1, 0] = true := by decide +kernel
theorem subd7_6_290 : subd7_6 [0, 1, 1] = true := by decide +kernel
theorem subd7_6_291 : subd7_6 [0, 1, 2] = true := by decide +kernel
theorem subd7_6_292 : subd7_6 [0, 1, 3] = true := by decide +kernel
theorem subd7_6_293 : subd7_6 [0, 1, 4] = true := by decide +kernel
theorem subd7_6_294 : subd7_6 [0, 1, 5] = true := by decide +kernel
theorem subd7_6_295 : subd7_6 [0, 1, 6] = true := by decide +kernel
theorem subd7_6_296 : subd7_6 [0, 2, -7] = true := by decide +kernel
theorem subd7_6_297 : subd7_6 [0, 2, -6] = true := by decide +kernel
theorem subd7_6_298 : subd7_6 [0, 2, -5] = true := by decide +kernel
theorem subd7_6_299 : subd7_6 [0, 2, -4] = true := by decide +kernel
theorem subd7_6_300 : subd7_6 [0, 2, -3] = true := by decide +kernel
theorem subd7_6_301 : subd7_6 [0, 2, -2] = true := by decide +kernel
theorem subd7_6_302 : subd7_6 [0, 2, -1] = true := by decide +kernel
theorem subd7_6_303 : subd7_6 [0, 2, 0] = true := by decide +kernel
theorem subd7_6_304 : subd7_6 [0, 2, 1] = true := by decide +kernel
theorem subd7_6_305 : subd7_6 [0, 2, 2] = true := by decide +kernel
theorem subd7_6_306 : subd7_6 [0, 2, 3] = true := by decide +kernel
theorem subd7_6_307 : subd7_6 [0, 2, 4] = true := by decide +kernel
theorem subd7_6_308 : subd7_6 [0, 2, 5] = true := by decide +kernel
theorem subd7_6_309 : subd7_6 [0, 2, 6] = true := by decide +kernel
theorem subd7_6_310 : subd7_6 [0, 3, -7] = true := by decide +kernel
theorem subd7_6_311 : subd7_6 [0, 3, -6] = true := by decide +kernel
theorem subd7_6_312 : subd7_6 [0, 3, -5] = true := by decide +kernel
theorem subd7_6_313 : subd7_6 [0, 3, -4] = true := by decide +kernel
theorem subd7_6_314 : subd7_6 [0, 3, -3] = true := by decide +kernel
theorem subd7_6_315 : subd7_6 [0, 3, -2] = true := by decide +kernel
theorem subd7_6_316 : subd7_6 [0, 3, -1] = true := by decide +kernel
theorem subd7_6_317 : subd7_6 [0, 3, 0] = true := by decide +kernel
theorem subd7_6_318 : subd7_6 [0, 3, 1] = true := by decide +kernel
theorem subd7_6_319 : subd7_6 [0, 3, 2] = true := by decide +kernel
theorem sbd7_6_9 : ∀ q ∈ blkd7_6_9, subd7_6 q = true := by
  unfold blkd7_6_9
  exact List.forall_mem_cons.2 ⟨subd7_6_288, List.forall_mem_cons.2 ⟨subd7_6_289, List.forall_mem_cons.2 ⟨subd7_6_290, List.forall_mem_cons.2 ⟨subd7_6_291, List.forall_mem_cons.2 ⟨subd7_6_292, List.forall_mem_cons.2 ⟨subd7_6_293, List.forall_mem_cons.2 ⟨subd7_6_294, List.forall_mem_cons.2 ⟨subd7_6_295, List.forall_mem_cons.2 ⟨subd7_6_296, List.forall_mem_cons.2 ⟨subd7_6_297, List.forall_mem_cons.2 ⟨subd7_6_298, List.forall_mem_cons.2 ⟨subd7_6_299, List.forall_mem_cons.2 ⟨subd7_6_300, List.forall_mem_cons.2 ⟨subd7_6_301, List.forall_mem_cons.2 ⟨subd7_6_302, List.forall_mem_cons.2 ⟨subd7_6_303, List.forall_mem_cons.2 ⟨subd7_6_304, List.forall_mem_cons.2 ⟨subd7_6_305, List.forall_mem_cons.2 ⟨subd7_6_306, List.forall_mem_cons.2 ⟨subd7_6_307, List.forall_mem_cons.2 ⟨subd7_6_308, List.forall_mem_cons.2 ⟨subd7_6_309, List.forall_mem_cons.2 ⟨subd7_6_310, List.forall_mem_cons.2 ⟨subd7_6_311, List.forall_mem_cons.2 ⟨subd7_6_312, List.forall_mem_cons.2 ⟨subd7_6_313, List.forall_mem_cons.2 ⟨subd7_6_314, List.forall_mem_cons.2 ⟨subd7_6_315, List.forall_mem_cons.2 ⟨subd7_6_316, List.forall_mem_cons.2 ⟨subd7_6_317, List.forall_mem_cons.2 ⟨subd7_6_318, List.forall_mem_cons.2 ⟨subd7_6_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
