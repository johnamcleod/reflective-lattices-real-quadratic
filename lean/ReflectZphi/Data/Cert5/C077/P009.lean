import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_3_0 : subd8_3 [-6] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-5, -5] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-5, -4] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-5, -3] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [-5, -2] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [-5, -1] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [-5, 0] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [-5, 1] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [-5, 2] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [-5, 3] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [-5, 4] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [-4, -6] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [-4, -5] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [-4, -4] = true := by decide +kernel
theorem subd8_3_14 : subd8_3 [-4, -3] = true := by decide +kernel
theorem subd8_3_15 : subd8_3 [-4, -2] = true := by decide +kernel
theorem subd8_3_16 : subd8_3 [-4, -1] = true := by decide +kernel
theorem subd8_3_17 : subd8_3 [-4, 0] = true := by decide +kernel
theorem subd8_3_18 : subd8_3 [-4, 1] = true := by decide +kernel
theorem subd8_3_19 : subd8_3 [-4, 2] = true := by decide +kernel
theorem subd8_3_20 : subd8_3 [-4, 3] = true := by decide +kernel
theorem subd8_3_21 : subd8_3 [-4, 4] = true := by decide +kernel
theorem subd8_3_22 : subd8_3 [-4, 5] = true := by decide +kernel
theorem subd8_3_23 : subd8_3 [-3, -7] = true := by decide +kernel
theorem subd8_3_24 : subd8_3 [-3, -6] = true := by decide +kernel
theorem subd8_3_25 : subd8_3 [-3, -5] = true := by decide +kernel
theorem subd8_3_26 : subd8_3 [-3, -4] = true := by decide +kernel
theorem subd8_3_27 : subd8_3 [-3, -3] = true := by decide +kernel
theorem subd8_3_28 : subd8_3 [-3, -2] = true := by decide +kernel
theorem subd8_3_29 : subd8_3 [-3, -1] = true := by decide +kernel
theorem subd8_3_30 : subd8_3 [-3, 0] = true := by decide +kernel
theorem subd8_3_31 : subd8_3 [-3, 1] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_cons.2 ⟨subd8_3_14, List.forall_mem_cons.2 ⟨subd8_3_15, List.forall_mem_cons.2 ⟨subd8_3_16, List.forall_mem_cons.2 ⟨subd8_3_17, List.forall_mem_cons.2 ⟨subd8_3_18, List.forall_mem_cons.2 ⟨subd8_3_19, List.forall_mem_cons.2 ⟨subd8_3_20, List.forall_mem_cons.2 ⟨subd8_3_21, List.forall_mem_cons.2 ⟨subd8_3_22, List.forall_mem_cons.2 ⟨subd8_3_23, List.forall_mem_cons.2 ⟨subd8_3_24, List.forall_mem_cons.2 ⟨subd8_3_25, List.forall_mem_cons.2 ⟨subd8_3_26, List.forall_mem_cons.2 ⟨subd8_3_27, List.forall_mem_cons.2 ⟨subd8_3_28, List.forall_mem_cons.2 ⟨subd8_3_29, List.forall_mem_cons.2 ⟨subd8_3_30, List.forall_mem_cons.2 ⟨subd8_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_32 : subd8_3 [-3, 2] = true := by decide +kernel
theorem subd8_3_33 : subd8_3 [-3, 3] = true := by decide +kernel
theorem subd8_3_34 : subd8_3 [-3, 4] = true := by decide +kernel
theorem subd8_3_35 : subd8_3 [-3, 5] = true := by decide +kernel
theorem subd8_3_36 : subd8_3 [-3, 6] = true := by decide +kernel
theorem subd8_3_37 : subd8_3 [-2, -7] = true := by decide +kernel
theorem subd8_3_38 : subd8_3 [-2, -6] = true := by decide +kernel
theorem subd8_3_39 : subd8_3 [-2, -5] = true := by decide +kernel
theorem subd8_3_40 : subd8_3 [-2, -4] = true := by decide +kernel
theorem subd8_3_41 : subd8_3 [-2, -3] = true := by decide +kernel
theorem subd8_3_42 : subd8_3 [-2, -2] = true := by decide +kernel
theorem subd8_3_43 : subd8_3 [-2, -1, -7] = true := by decide +kernel
theorem subd8_3_44 : subd8_3 [-2, -1, -6] = true := by decide +kernel
theorem subd8_3_45 : subd8_3 [-2, -1, -5] = true := by decide +kernel
theorem subd8_3_46 : subd8_3 [-2, -1, -4] = true := by decide +kernel
theorem subd8_3_47 : subd8_3 [-2, -1, -3] = true := by decide +kernel
theorem subd8_3_48 : subd8_3 [-2, -1, -2] = true := by decide +kernel
theorem subd8_3_49 : subd8_3 [-2, -1, -1] = true := by decide +kernel
theorem subd8_3_50 : subd8_3 [-2, -1, 0] = true := by decide +kernel
theorem subd8_3_51 : subd8_3 [-2, -1, 1] = true := by decide +kernel
theorem subd8_3_52 : subd8_3 [-2, -1, 2] = true := by decide +kernel
theorem subd8_3_53 : subd8_3 [-2, -1, 3] = true := by decide +kernel
theorem subd8_3_54 : subd8_3 [-2, -1, 4] = true := by decide +kernel
theorem subd8_3_55 : subd8_3 [-2, -1, 5] = true := by decide +kernel
theorem subd8_3_56 : subd8_3 [-2, 0, -7] = true := by decide +kernel
theorem subd8_3_57 : subd8_3 [-2, 0, -6] = true := by decide +kernel
theorem subd8_3_58 : subd8_3 [-2, 0, -5] = true := by decide +kernel
theorem subd8_3_59 : subd8_3 [-2, 0, -4] = true := by decide +kernel
theorem subd8_3_60 : subd8_3 [-2, 0, -3] = true := by decide +kernel
theorem subd8_3_61 : subd8_3 [-2, 0, -2] = true := by decide +kernel
theorem subd8_3_62 : subd8_3 [-2, 0, -1] = true := by decide +kernel
theorem subd8_3_63 : subd8_3 [-2, 0, 0] = true := by decide +kernel
theorem sbd8_3_1 : ∀ q ∈ blkd8_3_1, subd8_3 q = true := by
  unfold blkd8_3_1
  exact List.forall_mem_cons.2 ⟨subd8_3_32, List.forall_mem_cons.2 ⟨subd8_3_33, List.forall_mem_cons.2 ⟨subd8_3_34, List.forall_mem_cons.2 ⟨subd8_3_35, List.forall_mem_cons.2 ⟨subd8_3_36, List.forall_mem_cons.2 ⟨subd8_3_37, List.forall_mem_cons.2 ⟨subd8_3_38, List.forall_mem_cons.2 ⟨subd8_3_39, List.forall_mem_cons.2 ⟨subd8_3_40, List.forall_mem_cons.2 ⟨subd8_3_41, List.forall_mem_cons.2 ⟨subd8_3_42, List.forall_mem_cons.2 ⟨subd8_3_43, List.forall_mem_cons.2 ⟨subd8_3_44, List.forall_mem_cons.2 ⟨subd8_3_45, List.forall_mem_cons.2 ⟨subd8_3_46, List.forall_mem_cons.2 ⟨subd8_3_47, List.forall_mem_cons.2 ⟨subd8_3_48, List.forall_mem_cons.2 ⟨subd8_3_49, List.forall_mem_cons.2 ⟨subd8_3_50, List.forall_mem_cons.2 ⟨subd8_3_51, List.forall_mem_cons.2 ⟨subd8_3_52, List.forall_mem_cons.2 ⟨subd8_3_53, List.forall_mem_cons.2 ⟨subd8_3_54, List.forall_mem_cons.2 ⟨subd8_3_55, List.forall_mem_cons.2 ⟨subd8_3_56, List.forall_mem_cons.2 ⟨subd8_3_57, List.forall_mem_cons.2 ⟨subd8_3_58, List.forall_mem_cons.2 ⟨subd8_3_59, List.forall_mem_cons.2 ⟨subd8_3_60, List.forall_mem_cons.2 ⟨subd8_3_61, List.forall_mem_cons.2 ⟨subd8_3_62, List.forall_mem_cons.2 ⟨subd8_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_64 : subd8_3 [-2, 0, 1] = true := by decide +kernel
theorem subd8_3_65 : subd8_3 [-2, 0, 2] = true := by decide +kernel
theorem subd8_3_66 : subd8_3 [-2, 0, 3] = true := by decide +kernel
theorem subd8_3_67 : subd8_3 [-2, 0, 4] = true := by decide +kernel
theorem subd8_3_68 : subd8_3 [-2, 0, 5] = true := by decide +kernel
theorem subd8_3_69 : subd8_3 [-2, 1, -6] = true := by decide +kernel
theorem subd8_3_70 : subd8_3 [-2, 1, -5] = true := by decide +kernel
theorem subd8_3_71 : subd8_3 [-2, 1, -4] = true := by decide +kernel
theorem subd8_3_72 : subd8_3 [-2, 1, -3] = true := by decide +kernel
theorem subd8_3_73 : subd8_3 [-2, 1, -2] = true := by decide +kernel
theorem subd8_3_74 : subd8_3 [-2, 1, -1] = true := by decide +kernel
theorem subd8_3_75 : subd8_3 [-2, 1, 0] = true := by decide +kernel
theorem subd8_3_76 : subd8_3 [-2, 1, 1] = true := by decide +kernel
theorem subd8_3_77 : subd8_3 [-2, 1, 2] = true := by decide +kernel
theorem subd8_3_78 : subd8_3 [-2, 1, 3] = true := by decide +kernel
theorem subd8_3_79 : subd8_3 [-2, 1, 4] = true := by decide +kernel
theorem subd8_3_80 : subd8_3 [-2, 1, 5] = true := by decide +kernel
theorem subd8_3_81 : subd8_3 [-2, 2] = true := by decide +kernel
theorem subd8_3_82 : subd8_3 [-2, 3] = true := by decide +kernel
theorem subd8_3_83 : subd8_3 [-2, 4] = true := by decide +kernel
theorem subd8_3_84 : subd8_3 [-2, 5] = true := by decide +kernel
theorem subd8_3_85 : subd8_3 [-2, 6] = true := by decide +kernel
theorem subd8_3_86 : subd8_3 [-1, -8] = true := by decide +kernel
theorem subd8_3_87 : subd8_3 [-1, -7] = true := by decide +kernel
theorem subd8_3_88 : subd8_3 [-1, -6] = true := by decide +kernel
theorem subd8_3_89 : subd8_3 [-1, -5] = true := by decide +kernel
theorem subd8_3_90 : subd8_3 [-1, -4] = true := by decide +kernel
theorem subd8_3_91 : subd8_3 [-1, -3] = true := by decide +kernel
theorem subd8_3_92 : subd8_3 [-1, -2, -7] = true := by decide +kernel
theorem subd8_3_93 : subd8_3 [-1, -2, -6] = true := by decide +kernel
theorem subd8_3_94 : subd8_3 [-1, -2, -5] = true := by decide +kernel
theorem subd8_3_95 : subd8_3 [-1, -2, -4] = true := by decide +kernel
theorem sbd8_3_2 : ∀ q ∈ blkd8_3_2, subd8_3 q = true := by
  unfold blkd8_3_2
  exact List.forall_mem_cons.2 ⟨subd8_3_64, List.forall_mem_cons.2 ⟨subd8_3_65, List.forall_mem_cons.2 ⟨subd8_3_66, List.forall_mem_cons.2 ⟨subd8_3_67, List.forall_mem_cons.2 ⟨subd8_3_68, List.forall_mem_cons.2 ⟨subd8_3_69, List.forall_mem_cons.2 ⟨subd8_3_70, List.forall_mem_cons.2 ⟨subd8_3_71, List.forall_mem_cons.2 ⟨subd8_3_72, List.forall_mem_cons.2 ⟨subd8_3_73, List.forall_mem_cons.2 ⟨subd8_3_74, List.forall_mem_cons.2 ⟨subd8_3_75, List.forall_mem_cons.2 ⟨subd8_3_76, List.forall_mem_cons.2 ⟨subd8_3_77, List.forall_mem_cons.2 ⟨subd8_3_78, List.forall_mem_cons.2 ⟨subd8_3_79, List.forall_mem_cons.2 ⟨subd8_3_80, List.forall_mem_cons.2 ⟨subd8_3_81, List.forall_mem_cons.2 ⟨subd8_3_82, List.forall_mem_cons.2 ⟨subd8_3_83, List.forall_mem_cons.2 ⟨subd8_3_84, List.forall_mem_cons.2 ⟨subd8_3_85, List.forall_mem_cons.2 ⟨subd8_3_86, List.forall_mem_cons.2 ⟨subd8_3_87, List.forall_mem_cons.2 ⟨subd8_3_88, List.forall_mem_cons.2 ⟨subd8_3_89, List.forall_mem_cons.2 ⟨subd8_3_90, List.forall_mem_cons.2 ⟨subd8_3_91, List.forall_mem_cons.2 ⟨subd8_3_92, List.forall_mem_cons.2 ⟨subd8_3_93, List.forall_mem_cons.2 ⟨subd8_3_94, List.forall_mem_cons.2 ⟨subd8_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_96 : subd8_3 [-1, -2, -3] = true := by decide +kernel
theorem subd8_3_97 : subd8_3 [-1, -2, -2] = true := by decide +kernel
theorem subd8_3_98 : subd8_3 [-1, -2, -1] = true := by decide +kernel
theorem subd8_3_99 : subd8_3 [-1, -2, 0] = true := by decide +kernel
theorem subd8_3_100 : subd8_3 [-1, -2, 1] = true := by decide +kernel
theorem subd8_3_101 : subd8_3 [-1, -2, 2] = true := by decide +kernel
theorem subd8_3_102 : subd8_3 [-1, -2, 3] = true := by decide +kernel
theorem subd8_3_103 : subd8_3 [-1, -2, 4] = true := by decide +kernel
theorem subd8_3_104 : subd8_3 [-1, -2, 5] = true := by decide +kernel
theorem subd8_3_105 : subd8_3 [-1, -1, -7] = true := by decide +kernel
theorem subd8_3_106 : subd8_3 [-1, -1, -6] = true := by decide +kernel
theorem subd8_3_107 : subd8_3 [-1, -1, -5] = true := by decide +kernel
theorem subd8_3_108 : subd8_3 [-1, -1, -4] = true := by decide +kernel
theorem subd8_3_109 : subd8_3 [-1, -1, -3] = true := by decide +kernel
theorem subd8_3_110 : subd8_3 [-1, -1, -2] = true := by decide +kernel
theorem subd8_3_111 : subd8_3 [-1, -1, -1] = true := by decide +kernel
theorem subd8_3_112 : subd8_3 [-1, -1, 0] = true := by decide +kernel
theorem subd8_3_113 : subd8_3 [-1, -1, 1] = true := by decide +kernel
theorem subd8_3_114 : subd8_3 [-1, -1, 2] = true := by decide +kernel
theorem subd8_3_115 : subd8_3 [-1, -1, 3] = true := by decide +kernel
theorem subd8_3_116 : subd8_3 [-1, -1, 4] = true := by decide +kernel
theorem subd8_3_117 : subd8_3 [-1, -1, 5] = true := by decide +kernel
theorem subd8_3_118 : subd8_3 [-1, 0, -7] = true := by decide +kernel
theorem subd8_3_119 : subd8_3 [-1, 0, -6] = true := by decide +kernel
theorem subd8_3_120 : subd8_3 [-1, 0, -5] = true := by decide +kernel
theorem subd8_3_121 : subd8_3 [-1, 0, -4] = true := by decide +kernel
theorem subd8_3_122 : subd8_3 [-1, 0, -3] = true := by decide +kernel
theorem subd8_3_123 : subd8_3 [-1, 0, -2] = true := by decide +kernel
theorem subd8_3_124 : subd8_3 [-1, 0, -1] = true := by decide +kernel
theorem subd8_3_125 : subd8_3 [-1, 0, 0] = true := by decide +kernel
theorem subd8_3_126 : subd8_3 [-1, 0, 1] = true := by decide +kernel
theorem subd8_3_127 : subd8_3 [-1, 0, 2] = true := by decide +kernel
theorem sbd8_3_3 : ∀ q ∈ blkd8_3_3, subd8_3 q = true := by
  unfold blkd8_3_3
  exact List.forall_mem_cons.2 ⟨subd8_3_96, List.forall_mem_cons.2 ⟨subd8_3_97, List.forall_mem_cons.2 ⟨subd8_3_98, List.forall_mem_cons.2 ⟨subd8_3_99, List.forall_mem_cons.2 ⟨subd8_3_100, List.forall_mem_cons.2 ⟨subd8_3_101, List.forall_mem_cons.2 ⟨subd8_3_102, List.forall_mem_cons.2 ⟨subd8_3_103, List.forall_mem_cons.2 ⟨subd8_3_104, List.forall_mem_cons.2 ⟨subd8_3_105, List.forall_mem_cons.2 ⟨subd8_3_106, List.forall_mem_cons.2 ⟨subd8_3_107, List.forall_mem_cons.2 ⟨subd8_3_108, List.forall_mem_cons.2 ⟨subd8_3_109, List.forall_mem_cons.2 ⟨subd8_3_110, List.forall_mem_cons.2 ⟨subd8_3_111, List.forall_mem_cons.2 ⟨subd8_3_112, List.forall_mem_cons.2 ⟨subd8_3_113, List.forall_mem_cons.2 ⟨subd8_3_114, List.forall_mem_cons.2 ⟨subd8_3_115, List.forall_mem_cons.2 ⟨subd8_3_116, List.forall_mem_cons.2 ⟨subd8_3_117, List.forall_mem_cons.2 ⟨subd8_3_118, List.forall_mem_cons.2 ⟨subd8_3_119, List.forall_mem_cons.2 ⟨subd8_3_120, List.forall_mem_cons.2 ⟨subd8_3_121, List.forall_mem_cons.2 ⟨subd8_3_122, List.forall_mem_cons.2 ⟨subd8_3_123, List.forall_mem_cons.2 ⟨subd8_3_124, List.forall_mem_cons.2 ⟨subd8_3_125, List.forall_mem_cons.2 ⟨subd8_3_126, List.forall_mem_cons.2 ⟨subd8_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_128 : subd8_3 [-1, 0, 3] = true := by decide +kernel
theorem subd8_3_129 : subd8_3 [-1, 0, 4] = true := by decide +kernel
theorem subd8_3_130 : subd8_3 [-1, 0, 5] = true := by decide +kernel
theorem subd8_3_131 : subd8_3 [-1, 0, 6] = true := by decide +kernel
theorem subd8_3_132 : subd8_3 [-1, 1, -7] = true := by decide +kernel
theorem subd8_3_133 : subd8_3 [-1, 1, -6] = true := by decide +kernel
theorem subd8_3_134 : subd8_3 [-1, 1, -5] = true := by decide +kernel
theorem subd8_3_135 : subd8_3 [-1, 1, -4] = true := by decide +kernel
theorem subd8_3_136 : subd8_3 [-1, 1, -3] = true := by decide +kernel
theorem subd8_3_137 : subd8_3 [-1, 1, -2] = true := by decide +kernel
theorem subd8_3_138 : subd8_3 [-1, 1, -1] = true := by decide +kernel
theorem subd8_3_139 : subd8_3 [-1, 1, 0] = true := by decide +kernel
theorem subd8_3_140 : subd8_3 [-1, 1, 1] = true := by decide +kernel
theorem subd8_3_141 : subd8_3 [-1, 1, 2] = true := by decide +kernel
theorem subd8_3_142 : subd8_3 [-1, 1, 3] = true := by decide +kernel
theorem subd8_3_143 : subd8_3 [-1, 1, 4] = true := by decide +kernel
theorem subd8_3_144 : subd8_3 [-1, 1, 5] = true := by decide +kernel
theorem subd8_3_145 : subd8_3 [-1, 1, 6] = true := by decide +kernel
theorem subd8_3_146 : subd8_3 [-1, 2, -6] = true := by decide +kernel
theorem subd8_3_147 : subd8_3 [-1, 2, -5] = true := by decide +kernel
theorem subd8_3_148 : subd8_3 [-1, 2, -4] = true := by decide +kernel
theorem subd8_3_149 : subd8_3 [-1, 2, -3] = true := by decide +kernel
theorem subd8_3_150 : subd8_3 [-1, 2, -2] = true := by decide +kernel
theorem subd8_3_151 : subd8_3 [-1, 2, -1] = true := by decide +kernel
theorem subd8_3_152 : subd8_3 [-1, 2, 0] = true := by decide +kernel
theorem subd8_3_153 : subd8_3 [-1, 2, 1] = true := by decide +kernel
theorem subd8_3_154 : subd8_3 [-1, 2, 2] = true := by decide +kernel
theorem subd8_3_155 : subd8_3 [-1, 2, 3] = true := by decide +kernel
theorem subd8_3_156 : subd8_3 [-1, 2, 4] = true := by decide +kernel
theorem subd8_3_157 : subd8_3 [-1, 2, 5] = true := by decide +kernel
theorem subd8_3_158 : subd8_3 [-1, 2, 6] = true := by decide +kernel
theorem subd8_3_159 : subd8_3 [-1, 3] = true := by decide +kernel
theorem sbd8_3_4 : ∀ q ∈ blkd8_3_4, subd8_3 q = true := by
  unfold blkd8_3_4
  exact List.forall_mem_cons.2 ⟨subd8_3_128, List.forall_mem_cons.2 ⟨subd8_3_129, List.forall_mem_cons.2 ⟨subd8_3_130, List.forall_mem_cons.2 ⟨subd8_3_131, List.forall_mem_cons.2 ⟨subd8_3_132, List.forall_mem_cons.2 ⟨subd8_3_133, List.forall_mem_cons.2 ⟨subd8_3_134, List.forall_mem_cons.2 ⟨subd8_3_135, List.forall_mem_cons.2 ⟨subd8_3_136, List.forall_mem_cons.2 ⟨subd8_3_137, List.forall_mem_cons.2 ⟨subd8_3_138, List.forall_mem_cons.2 ⟨subd8_3_139, List.forall_mem_cons.2 ⟨subd8_3_140, List.forall_mem_cons.2 ⟨subd8_3_141, List.forall_mem_cons.2 ⟨subd8_3_142, List.forall_mem_cons.2 ⟨subd8_3_143, List.forall_mem_cons.2 ⟨subd8_3_144, List.forall_mem_cons.2 ⟨subd8_3_145, List.forall_mem_cons.2 ⟨subd8_3_146, List.forall_mem_cons.2 ⟨subd8_3_147, List.forall_mem_cons.2 ⟨subd8_3_148, List.forall_mem_cons.2 ⟨subd8_3_149, List.forall_mem_cons.2 ⟨subd8_3_150, List.forall_mem_cons.2 ⟨subd8_3_151, List.forall_mem_cons.2 ⟨subd8_3_152, List.forall_mem_cons.2 ⟨subd8_3_153, List.forall_mem_cons.2 ⟨subd8_3_154, List.forall_mem_cons.2 ⟨subd8_3_155, List.forall_mem_cons.2 ⟨subd8_3_156, List.forall_mem_cons.2 ⟨subd8_3_157, List.forall_mem_cons.2 ⟨subd8_3_158, List.forall_mem_cons.2 ⟨subd8_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_160 : subd8_3 [-1, 4] = true := by decide +kernel
theorem subd8_3_161 : subd8_3 [-1, 5] = true := by decide +kernel
theorem subd8_3_162 : subd8_3 [-1, 6] = true := by decide +kernel
theorem subd8_3_163 : subd8_3 [-1, 7] = true := by decide +kernel
theorem subd8_3_164 : subd8_3 [0, -8] = true := by decide +kernel
theorem subd8_3_165 : subd8_3 [0, -7] = true := by decide +kernel
theorem subd8_3_166 : subd8_3 [0, -6] = true := by decide +kernel
theorem subd8_3_167 : subd8_3 [0, -5] = true := by decide +kernel
theorem subd8_3_168 : subd8_3 [0, -4] = true := by decide +kernel
theorem subd8_3_169 : subd8_3 [0, -3] = true := by decide +kernel
theorem subd8_3_170 : subd8_3 [0, -2, -7] = true := by decide +kernel
theorem subd8_3_171 : subd8_3 [0, -2, -6] = true := by decide +kernel
theorem subd8_3_172 : subd8_3 [0, -2, -5] = true := by decide +kernel
theorem subd8_3_173 : subd8_3 [0, -2, -4] = true := by decide +kernel
theorem subd8_3_174 : subd8_3 [0, -2, -3] = true := by decide +kernel
theorem subd8_3_175 : subd8_3 [0, -2, -2] = true := by decide +kernel
theorem subd8_3_176 : subd8_3 [0, -2, -1] = true := by decide +kernel
theorem subd8_3_177 : subd8_3 [0, -2, 0] = true := by decide +kernel
theorem subd8_3_178 : subd8_3 [0, -2, 1] = true := by decide +kernel
theorem subd8_3_179 : subd8_3 [0, -2, 2] = true := by decide +kernel
theorem subd8_3_180 : subd8_3 [0, -2, 3] = true := by decide +kernel
theorem subd8_3_181 : subd8_3 [0, -2, 4] = true := by decide +kernel
theorem subd8_3_182 : subd8_3 [0, -2, 5] = true := by decide +kernel
theorem subd8_3_183 : subd8_3 [0, -1, -7] = true := by decide +kernel
theorem subd8_3_184 : subd8_3 [0, -1, -6] = true := by decide +kernel
theorem subd8_3_185 : subd8_3 [0, -1, -5] = true := by decide +kernel
theorem subd8_3_186 : subd8_3 [0, -1, -4] = true := by decide +kernel
theorem subd8_3_187 : subd8_3 [0, -1, -3] = true := by decide +kernel
theorem subd8_3_188 : subd8_3 [0, -1, -2] = true := by decide +kernel
theorem subd8_3_189 : subd8_3 [0, -1, -1] = true := by decide +kernel
theorem subd8_3_190 : subd8_3 [0, -1, 0] = true := by decide +kernel
theorem subd8_3_191 : subd8_3 [0, -1, 1] = true := by decide +kernel
theorem sbd8_3_5 : ∀ q ∈ blkd8_3_5, subd8_3 q = true := by
  unfold blkd8_3_5
  exact List.forall_mem_cons.2 ⟨subd8_3_160, List.forall_mem_cons.2 ⟨subd8_3_161, List.forall_mem_cons.2 ⟨subd8_3_162, List.forall_mem_cons.2 ⟨subd8_3_163, List.forall_mem_cons.2 ⟨subd8_3_164, List.forall_mem_cons.2 ⟨subd8_3_165, List.forall_mem_cons.2 ⟨subd8_3_166, List.forall_mem_cons.2 ⟨subd8_3_167, List.forall_mem_cons.2 ⟨subd8_3_168, List.forall_mem_cons.2 ⟨subd8_3_169, List.forall_mem_cons.2 ⟨subd8_3_170, List.forall_mem_cons.2 ⟨subd8_3_171, List.forall_mem_cons.2 ⟨subd8_3_172, List.forall_mem_cons.2 ⟨subd8_3_173, List.forall_mem_cons.2 ⟨subd8_3_174, List.forall_mem_cons.2 ⟨subd8_3_175, List.forall_mem_cons.2 ⟨subd8_3_176, List.forall_mem_cons.2 ⟨subd8_3_177, List.forall_mem_cons.2 ⟨subd8_3_178, List.forall_mem_cons.2 ⟨subd8_3_179, List.forall_mem_cons.2 ⟨subd8_3_180, List.forall_mem_cons.2 ⟨subd8_3_181, List.forall_mem_cons.2 ⟨subd8_3_182, List.forall_mem_cons.2 ⟨subd8_3_183, List.forall_mem_cons.2 ⟨subd8_3_184, List.forall_mem_cons.2 ⟨subd8_3_185, List.forall_mem_cons.2 ⟨subd8_3_186, List.forall_mem_cons.2 ⟨subd8_3_187, List.forall_mem_cons.2 ⟨subd8_3_188, List.forall_mem_cons.2 ⟨subd8_3_189, List.forall_mem_cons.2 ⟨subd8_3_190, List.forall_mem_cons.2 ⟨subd8_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_192 : subd8_3 [0, -1, 2] = true := by decide +kernel
theorem subd8_3_193 : subd8_3 [0, -1, 3] = true := by decide +kernel
theorem subd8_3_194 : subd8_3 [0, -1, 4] = true := by decide +kernel
theorem subd8_3_195 : subd8_3 [0, -1, 5] = true := by decide +kernel
theorem subd8_3_196 : subd8_3 [0, 0, -7] = true := by decide +kernel
theorem subd8_3_197 : subd8_3 [0, 0, -6] = true := by decide +kernel
theorem subd8_3_198 : subd8_3 [0, 0, -5] = true := by decide +kernel
theorem subd8_3_199 : subd8_3 [0, 0, -4] = true := by decide +kernel
theorem subd8_3_200 : subd8_3 [0, 0, -3] = true := by decide +kernel
theorem subd8_3_201 : subd8_3 [0, 0, -2] = true := by decide +kernel
theorem subd8_3_202 : subd8_3 [0, 0, -1] = true := by decide +kernel
theorem subd8_3_203 : subd8_3 [0, 0, 0] = true := by decide +kernel
theorem subd8_3_204 : subd8_3 [0, 0, 1] = true := by decide +kernel
theorem subd8_3_205 : subd8_3 [0, 0, 2] = true := by decide +kernel
theorem subd8_3_206 : subd8_3 [0, 0, 3] = true := by decide +kernel
theorem subd8_3_207 : subd8_3 [0, 0, 4] = true := by decide +kernel
theorem subd8_3_208 : subd8_3 [0, 0, 5] = true := by decide +kernel
theorem subd8_3_209 : subd8_3 [0, 0, 6] = true := by decide +kernel
theorem subd8_3_210 : subd8_3 [0, 1, -6] = true := by decide +kernel
theorem subd8_3_211 : subd8_3 [0, 1, -5] = true := by decide +kernel
theorem subd8_3_212 : subd8_3 [0, 1, -4] = true := by decide +kernel
theorem subd8_3_213 : subd8_3 [0, 1, -3] = true := by decide +kernel
theorem subd8_3_214 : subd8_3 [0, 1, -2] = true := by decide +kernel
theorem subd8_3_215 : subd8_3 [0, 1, -1] = true := by decide +kernel
theorem subd8_3_216 : subd8_3 [0, 1, 0] = true := by decide +kernel
theorem subd8_3_217 : subd8_3 [0, 1, 1] = true := by decide +kernel
theorem subd8_3_218 : subd8_3 [0, 1, 2] = true := by decide +kernel
theorem subd8_3_219 : subd8_3 [0, 1, 3] = true := by decide +kernel
theorem subd8_3_220 : subd8_3 [0, 1, 4] = true := by decide +kernel
theorem subd8_3_221 : subd8_3 [0, 1, 5] = true := by decide +kernel
theorem subd8_3_222 : subd8_3 [0, 1, 6] = true := by decide +kernel
theorem subd8_3_223 : subd8_3 [0, 2, -6] = true := by decide +kernel
theorem sbd8_3_6 : ∀ q ∈ blkd8_3_6, subd8_3 q = true := by
  unfold blkd8_3_6
  exact List.forall_mem_cons.2 ⟨subd8_3_192, List.forall_mem_cons.2 ⟨subd8_3_193, List.forall_mem_cons.2 ⟨subd8_3_194, List.forall_mem_cons.2 ⟨subd8_3_195, List.forall_mem_cons.2 ⟨subd8_3_196, List.forall_mem_cons.2 ⟨subd8_3_197, List.forall_mem_cons.2 ⟨subd8_3_198, List.forall_mem_cons.2 ⟨subd8_3_199, List.forall_mem_cons.2 ⟨subd8_3_200, List.forall_mem_cons.2 ⟨subd8_3_201, List.forall_mem_cons.2 ⟨subd8_3_202, List.forall_mem_cons.2 ⟨subd8_3_203, List.forall_mem_cons.2 ⟨subd8_3_204, List.forall_mem_cons.2 ⟨subd8_3_205, List.forall_mem_cons.2 ⟨subd8_3_206, List.forall_mem_cons.2 ⟨subd8_3_207, List.forall_mem_cons.2 ⟨subd8_3_208, List.forall_mem_cons.2 ⟨subd8_3_209, List.forall_mem_cons.2 ⟨subd8_3_210, List.forall_mem_cons.2 ⟨subd8_3_211, List.forall_mem_cons.2 ⟨subd8_3_212, List.forall_mem_cons.2 ⟨subd8_3_213, List.forall_mem_cons.2 ⟨subd8_3_214, List.forall_mem_cons.2 ⟨subd8_3_215, List.forall_mem_cons.2 ⟨subd8_3_216, List.forall_mem_cons.2 ⟨subd8_3_217, List.forall_mem_cons.2 ⟨subd8_3_218, List.forall_mem_cons.2 ⟨subd8_3_219, List.forall_mem_cons.2 ⟨subd8_3_220, List.forall_mem_cons.2 ⟨subd8_3_221, List.forall_mem_cons.2 ⟨subd8_3_222, List.forall_mem_cons.2 ⟨subd8_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
