import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_0_32 : subd9_0 [-4, -1, -7] = true := by decide +kernel
theorem subd9_0_33 : subd9_0 [-4, -1, -6] = true := by decide +kernel
theorem subd9_0_34 : subd9_0 [-4, -1, -5] = true := by decide +kernel
theorem subd9_0_35 : subd9_0 [-4, -1, -4] = true := by decide +kernel
theorem subd9_0_36 : subd9_0 [-4, -1, -3] = true := by decide +kernel
theorem subd9_0_37 : subd9_0 [-4, -1, -2] = true := by decide +kernel
theorem subd9_0_38 : subd9_0 [-4, -1, -1] = true := by decide +kernel
theorem subd9_0_39 : subd9_0 [-4, -1, 0] = true := by decide +kernel
theorem subd9_0_40 : subd9_0 [-4, -1, 1] = true := by decide +kernel
theorem subd9_0_41 : subd9_0 [-4, -1, 2] = true := by decide +kernel
theorem subd9_0_42 : subd9_0 [-4, -1, 3] = true := by decide +kernel
theorem subd9_0_43 : subd9_0 [-4, -1, 4] = true := by decide +kernel
theorem subd9_0_44 : subd9_0 [-4, -1, 5] = true := by decide +kernel
theorem subd9_0_45 : subd9_0 [-4, 0] = true := by decide +kernel
theorem subd9_0_46 : subd9_0 [-4, 1] = true := by decide +kernel
theorem subd9_0_47 : subd9_0 [-4, 2] = true := by decide +kernel
theorem subd9_0_48 : subd9_0 [-3, -7] = true := by decide +kernel
theorem subd9_0_49 : subd9_0 [-3, -6] = true := by decide +kernel
theorem subd9_0_50 : subd9_0 [-3, -5] = true := by decide +kernel
theorem subd9_0_51 : subd9_0 [-3, -4, -7] = true := by decide +kernel
theorem subd9_0_52 : subd9_0 [-3, -4, -6] = true := by decide +kernel
theorem subd9_0_53 : subd9_0 [-3, -4, -5] = true := by decide +kernel
theorem subd9_0_54 : subd9_0 [-3, -4, -4] = true := by decide +kernel
theorem subd9_0_55 : subd9_0 [-3, -4, -3] = true := by decide +kernel
theorem subd9_0_56 : subd9_0 [-3, -4, -2] = true := by decide +kernel
theorem subd9_0_57 : subd9_0 [-3, -4, -1] = true := by decide +kernel
theorem subd9_0_58 : subd9_0 [-3, -4, 0] = true := by decide +kernel
theorem subd9_0_59 : subd9_0 [-3, -4, 1] = true := by decide +kernel
theorem subd9_0_60 : subd9_0 [-3, -4, 2] = true := by decide +kernel
theorem subd9_0_61 : subd9_0 [-3, -4, 3] = true := by decide +kernel
theorem subd9_0_62 : subd9_0 [-3, -4, 4] = true := by decide +kernel
theorem subd9_0_63 : subd9_0 [-3, -4, 5] = true := by decide +kernel
theorem sbd9_0_1 : ∀ q ∈ blkd9_0_1, subd9_0 q = true := by
  unfold blkd9_0_1
  exact List.forall_mem_cons.2 ⟨subd9_0_32, List.forall_mem_cons.2 ⟨subd9_0_33, List.forall_mem_cons.2 ⟨subd9_0_34, List.forall_mem_cons.2 ⟨subd9_0_35, List.forall_mem_cons.2 ⟨subd9_0_36, List.forall_mem_cons.2 ⟨subd9_0_37, List.forall_mem_cons.2 ⟨subd9_0_38, List.forall_mem_cons.2 ⟨subd9_0_39, List.forall_mem_cons.2 ⟨subd9_0_40, List.forall_mem_cons.2 ⟨subd9_0_41, List.forall_mem_cons.2 ⟨subd9_0_42, List.forall_mem_cons.2 ⟨subd9_0_43, List.forall_mem_cons.2 ⟨subd9_0_44, List.forall_mem_cons.2 ⟨subd9_0_45, List.forall_mem_cons.2 ⟨subd9_0_46, List.forall_mem_cons.2 ⟨subd9_0_47, List.forall_mem_cons.2 ⟨subd9_0_48, List.forall_mem_cons.2 ⟨subd9_0_49, List.forall_mem_cons.2 ⟨subd9_0_50, List.forall_mem_cons.2 ⟨subd9_0_51, List.forall_mem_cons.2 ⟨subd9_0_52, List.forall_mem_cons.2 ⟨subd9_0_53, List.forall_mem_cons.2 ⟨subd9_0_54, List.forall_mem_cons.2 ⟨subd9_0_55, List.forall_mem_cons.2 ⟨subd9_0_56, List.forall_mem_cons.2 ⟨subd9_0_57, List.forall_mem_cons.2 ⟨subd9_0_58, List.forall_mem_cons.2 ⟨subd9_0_59, List.forall_mem_cons.2 ⟨subd9_0_60, List.forall_mem_cons.2 ⟨subd9_0_61, List.forall_mem_cons.2 ⟨subd9_0_62, List.forall_mem_cons.2 ⟨subd9_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_64 : subd9_0 [-3, -4, 6] = true := by decide +kernel
theorem subd9_0_65 : subd9_0 [-3, -4, 7] = true := by decide +kernel
theorem subd9_0_66 : subd9_0 [-3, -3, -8] = true := by decide +kernel
theorem subd9_0_67 : subd9_0 [-3, -3, -7] = true := by decide +kernel
theorem subd9_0_68 : subd9_0 [-3, -3, -6] = true := by decide +kernel
theorem subd9_0_69 : subd9_0 [-3, -3, -5] = true := by decide +kernel
theorem subd9_0_70 : subd9_0 [-3, -3, -4] = true := by decide +kernel
theorem subd9_0_71 : subd9_0 [-3, -3, -3] = true := by decide +kernel
theorem subd9_0_72 : subd9_0 [-3, -3, -2] = true := by decide +kernel
theorem subd9_0_73 : subd9_0 [-3, -3, -1] = true := by decide +kernel
theorem subd9_0_74 : subd9_0 [-3, -3, 0] = true := by decide +kernel
theorem subd9_0_75 : subd9_0 [-3, -3, 1] = true := by decide +kernel
theorem subd9_0_76 : subd9_0 [-3, -3, 2] = true := by decide +kernel
theorem subd9_0_77 : subd9_0 [-3, -3, 3] = true := by decide +kernel
theorem subd9_0_78 : subd9_0 [-3, -3, 4] = true := by decide +kernel
theorem subd9_0_79 : subd9_0 [-3, -3, 5] = true := by decide +kernel
theorem subd9_0_80 : subd9_0 [-3, -3, 6] = true := by decide +kernel
theorem subd9_0_81 : subd9_0 [-3, -3, 7] = true := by decide +kernel
theorem subd9_0_82 : subd9_0 [-3, -2, -9] = true := by decide +kernel
theorem subd9_0_83 : subd9_0 [-3, -2, -8] = true := by decide +kernel
theorem subd9_0_84 : subd9_0 [-3, -2, -7] = true := by decide +kernel
theorem subd9_0_85 : subd9_0 [-3, -2, -6] = true := by decide +kernel
theorem subd9_0_86 : subd9_0 [-3, -2, -5] = true := by decide +kernel
theorem subd9_0_87 : subd9_0 [-3, -2, -4] = true := by decide +kernel
theorem subd9_0_88 : subd9_0 [-3, -2, -3] = true := by decide +kernel
theorem subd9_0_89 : subd9_0 [-3, -2, -2] = true := by decide +kernel
theorem subd9_0_90 : subd9_0 [-3, -2, -1] = true := by decide +kernel
theorem subd9_0_91 : subd9_0 [-3, -2, 0] = true := by decide +kernel
theorem subd9_0_92 : subd9_0 [-3, -2, 1] = true := by decide +kernel
theorem subd9_0_93 : subd9_0 [-3, -2, 2] = true := by decide +kernel
theorem subd9_0_94 : subd9_0 [-3, -2, 3] = true := by decide +kernel
theorem subd9_0_95 : subd9_0 [-3, -2, 4] = true := by decide +kernel
theorem sbd9_0_2 : ∀ q ∈ blkd9_0_2, subd9_0 q = true := by
  unfold blkd9_0_2
  exact List.forall_mem_cons.2 ⟨subd9_0_64, List.forall_mem_cons.2 ⟨subd9_0_65, List.forall_mem_cons.2 ⟨subd9_0_66, List.forall_mem_cons.2 ⟨subd9_0_67, List.forall_mem_cons.2 ⟨subd9_0_68, List.forall_mem_cons.2 ⟨subd9_0_69, List.forall_mem_cons.2 ⟨subd9_0_70, List.forall_mem_cons.2 ⟨subd9_0_71, List.forall_mem_cons.2 ⟨subd9_0_72, List.forall_mem_cons.2 ⟨subd9_0_73, List.forall_mem_cons.2 ⟨subd9_0_74, List.forall_mem_cons.2 ⟨subd9_0_75, List.forall_mem_cons.2 ⟨subd9_0_76, List.forall_mem_cons.2 ⟨subd9_0_77, List.forall_mem_cons.2 ⟨subd9_0_78, List.forall_mem_cons.2 ⟨subd9_0_79, List.forall_mem_cons.2 ⟨subd9_0_80, List.forall_mem_cons.2 ⟨subd9_0_81, List.forall_mem_cons.2 ⟨subd9_0_82, List.forall_mem_cons.2 ⟨subd9_0_83, List.forall_mem_cons.2 ⟨subd9_0_84, List.forall_mem_cons.2 ⟨subd9_0_85, List.forall_mem_cons.2 ⟨subd9_0_86, List.forall_mem_cons.2 ⟨subd9_0_87, List.forall_mem_cons.2 ⟨subd9_0_88, List.forall_mem_cons.2 ⟨subd9_0_89, List.forall_mem_cons.2 ⟨subd9_0_90, List.forall_mem_cons.2 ⟨subd9_0_91, List.forall_mem_cons.2 ⟨subd9_0_92, List.forall_mem_cons.2 ⟨subd9_0_93, List.forall_mem_cons.2 ⟨subd9_0_94, List.forall_mem_cons.2 ⟨subd9_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_96 : subd9_0 [-3, -2, 5] = true := by decide +kernel
theorem subd9_0_97 : subd9_0 [-3, -2, 6] = true := by decide +kernel
theorem subd9_0_98 : subd9_0 [-3, -2, 7] = true := by decide +kernel
theorem subd9_0_99 : subd9_0 [-3, -1, -10] = true := by decide +kernel
theorem subd9_0_100 : subd9_0 [-3, -1, -9] = true := by decide +kernel
theorem subd9_0_101 : subd9_0 [-3, -1, -8] = true := by decide +kernel
theorem subd9_0_102 : subd9_0 [-3, -1, -7] = true := by decide +kernel
theorem subd9_0_103 : subd9_0 [-3, -1, -6] = true := by decide +kernel
theorem subd9_0_104 : subd9_0 [-3, -1, -5] = true := by decide +kernel
theorem subd9_0_105 : subd9_0 [-3, -1, -4] = true := by decide +kernel
theorem subd9_0_106 : subd9_0 [-3, -1, -3] = true := by decide +kernel
theorem subd9_0_107 : subd9_0 [-3, -1, -2] = true := by decide +kernel
theorem subd9_0_108 : subd9_0 [-3, -1, -1] = true := by decide +kernel
theorem subd9_0_109 : subd9_0 [-3, -1, 0] = true := by decide +kernel
theorem subd9_0_110 : subd9_0 [-3, -1, 1] = true := by decide +kernel
theorem subd9_0_111 : subd9_0 [-3, -1, 2] = true := by decide +kernel
theorem subd9_0_112 : subd9_0 [-3, -1, 3] = true := by decide +kernel
theorem subd9_0_113 : subd9_0 [-3, -1, 4] = true := by decide +kernel
theorem subd9_0_114 : subd9_0 [-3, -1, 5] = true := by decide +kernel
theorem subd9_0_115 : subd9_0 [-3, -1, 6] = true := by decide +kernel
theorem subd9_0_116 : subd9_0 [-3, -1, 7] = true := by decide +kernel
theorem subd9_0_117 : subd9_0 [-3, 0, -10] = true := by decide +kernel
theorem subd9_0_118 : subd9_0 [-3, 0, -9] = true := by decide +kernel
theorem subd9_0_119 : subd9_0 [-3, 0, -8] = true := by decide +kernel
theorem subd9_0_120 : subd9_0 [-3, 0, -7] = true := by decide +kernel
theorem subd9_0_121 : subd9_0 [-3, 0, -6] = true := by decide +kernel
theorem subd9_0_122 : subd9_0 [-3, 0, -5] = true := by decide +kernel
theorem subd9_0_123 : subd9_0 [-3, 0, -4] = true := by decide +kernel
theorem subd9_0_124 : subd9_0 [-3, 0, -3] = true := by decide +kernel
theorem subd9_0_125 : subd9_0 [-3, 0, -2] = true := by decide +kernel
theorem subd9_0_126 : subd9_0 [-3, 0, -1] = true := by decide +kernel
theorem subd9_0_127 : subd9_0 [-3, 0, 0] = true := by decide +kernel
theorem sbd9_0_3 : ∀ q ∈ blkd9_0_3, subd9_0 q = true := by
  unfold blkd9_0_3
  exact List.forall_mem_cons.2 ⟨subd9_0_96, List.forall_mem_cons.2 ⟨subd9_0_97, List.forall_mem_cons.2 ⟨subd9_0_98, List.forall_mem_cons.2 ⟨subd9_0_99, List.forall_mem_cons.2 ⟨subd9_0_100, List.forall_mem_cons.2 ⟨subd9_0_101, List.forall_mem_cons.2 ⟨subd9_0_102, List.forall_mem_cons.2 ⟨subd9_0_103, List.forall_mem_cons.2 ⟨subd9_0_104, List.forall_mem_cons.2 ⟨subd9_0_105, List.forall_mem_cons.2 ⟨subd9_0_106, List.forall_mem_cons.2 ⟨subd9_0_107, List.forall_mem_cons.2 ⟨subd9_0_108, List.forall_mem_cons.2 ⟨subd9_0_109, List.forall_mem_cons.2 ⟨subd9_0_110, List.forall_mem_cons.2 ⟨subd9_0_111, List.forall_mem_cons.2 ⟨subd9_0_112, List.forall_mem_cons.2 ⟨subd9_0_113, List.forall_mem_cons.2 ⟨subd9_0_114, List.forall_mem_cons.2 ⟨subd9_0_115, List.forall_mem_cons.2 ⟨subd9_0_116, List.forall_mem_cons.2 ⟨subd9_0_117, List.forall_mem_cons.2 ⟨subd9_0_118, List.forall_mem_cons.2 ⟨subd9_0_119, List.forall_mem_cons.2 ⟨subd9_0_120, List.forall_mem_cons.2 ⟨subd9_0_121, List.forall_mem_cons.2 ⟨subd9_0_122, List.forall_mem_cons.2 ⟨subd9_0_123, List.forall_mem_cons.2 ⟨subd9_0_124, List.forall_mem_cons.2 ⟨subd9_0_125, List.forall_mem_cons.2 ⟨subd9_0_126, List.forall_mem_cons.2 ⟨subd9_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_128 : subd9_0 [-3, 0, 1] = true := by decide +kernel
theorem subd9_0_129 : subd9_0 [-3, 0, 2] = true := by decide +kernel
theorem subd9_0_130 : subd9_0 [-3, 0, 3] = true := by decide +kernel
theorem subd9_0_131 : subd9_0 [-3, 0, 4] = true := by decide +kernel
theorem subd9_0_132 : subd9_0 [-3, 0, 5] = true := by decide +kernel
theorem subd9_0_133 : subd9_0 [-3, 0, 6] = true := by decide +kernel
theorem subd9_0_134 : subd9_0 [-3, 1, -10] = true := by decide +kernel
theorem subd9_0_135 : subd9_0 [-3, 1, -9] = true := by decide +kernel
theorem subd9_0_136 : subd9_0 [-3, 1, -8] = true := by decide +kernel
theorem subd9_0_137 : subd9_0 [-3, 1, -7] = true := by decide +kernel
theorem subd9_0_138 : subd9_0 [-3, 1, -6] = true := by decide +kernel
theorem subd9_0_139 : subd9_0 [-3, 1, -5] = true := by decide +kernel
theorem subd9_0_140 : subd9_0 [-3, 1, -4] = true := by decide +kernel
theorem subd9_0_141 : subd9_0 [-3, 1, -3] = true := by decide +kernel
theorem subd9_0_142 : subd9_0 [-3, 1, -2] = true := by decide +kernel
theorem subd9_0_143 : subd9_0 [-3, 1, -1] = true := by decide +kernel
theorem subd9_0_144 : subd9_0 [-3, 1, 0] = true := by decide +kernel
theorem subd9_0_145 : subd9_0 [-3, 1, 1] = true := by decide +kernel
theorem subd9_0_146 : subd9_0 [-3, 1, 2] = true := by decide +kernel
theorem subd9_0_147 : subd9_0 [-3, 1, 3] = true := by decide +kernel
theorem subd9_0_148 : subd9_0 [-3, 1, 4] = true := by decide +kernel
theorem subd9_0_149 : subd9_0 [-3, 1, 5] = true := by decide +kernel
theorem subd9_0_150 : subd9_0 [-3, 2] = true := by decide +kernel
theorem subd9_0_151 : subd9_0 [-3, 3] = true := by decide +kernel
theorem subd9_0_152 : subd9_0 [-2, -7] = true := by decide +kernel
theorem subd9_0_153 : subd9_0 [-2, -6] = true := by decide +kernel
theorem subd9_0_154 : subd9_0 [-2, -5, -5] = true := by decide +kernel
theorem subd9_0_155 : subd9_0 [-2, -5, -4] = true := by decide +kernel
theorem subd9_0_156 : subd9_0 [-2, -5, -3] = true := by decide +kernel
theorem subd9_0_157 : subd9_0 [-2, -5, -2] = true := by decide +kernel
theorem subd9_0_158 : subd9_0 [-2, -5, -1] = true := by decide +kernel
theorem subd9_0_159 : subd9_0 [-2, -5, 0] = true := by decide +kernel
theorem sbd9_0_4 : ∀ q ∈ blkd9_0_4, subd9_0 q = true := by
  unfold blkd9_0_4
  exact List.forall_mem_cons.2 ⟨subd9_0_128, List.forall_mem_cons.2 ⟨subd9_0_129, List.forall_mem_cons.2 ⟨subd9_0_130, List.forall_mem_cons.2 ⟨subd9_0_131, List.forall_mem_cons.2 ⟨subd9_0_132, List.forall_mem_cons.2 ⟨subd9_0_133, List.forall_mem_cons.2 ⟨subd9_0_134, List.forall_mem_cons.2 ⟨subd9_0_135, List.forall_mem_cons.2 ⟨subd9_0_136, List.forall_mem_cons.2 ⟨subd9_0_137, List.forall_mem_cons.2 ⟨subd9_0_138, List.forall_mem_cons.2 ⟨subd9_0_139, List.forall_mem_cons.2 ⟨subd9_0_140, List.forall_mem_cons.2 ⟨subd9_0_141, List.forall_mem_cons.2 ⟨subd9_0_142, List.forall_mem_cons.2 ⟨subd9_0_143, List.forall_mem_cons.2 ⟨subd9_0_144, List.forall_mem_cons.2 ⟨subd9_0_145, List.forall_mem_cons.2 ⟨subd9_0_146, List.forall_mem_cons.2 ⟨subd9_0_147, List.forall_mem_cons.2 ⟨subd9_0_148, List.forall_mem_cons.2 ⟨subd9_0_149, List.forall_mem_cons.2 ⟨subd9_0_150, List.forall_mem_cons.2 ⟨subd9_0_151, List.forall_mem_cons.2 ⟨subd9_0_152, List.forall_mem_cons.2 ⟨subd9_0_153, List.forall_mem_cons.2 ⟨subd9_0_154, List.forall_mem_cons.2 ⟨subd9_0_155, List.forall_mem_cons.2 ⟨subd9_0_156, List.forall_mem_cons.2 ⟨subd9_0_157, List.forall_mem_cons.2 ⟨subd9_0_158, List.forall_mem_cons.2 ⟨subd9_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_160 : subd9_0 [-2, -5, 1] = true := by decide +kernel
theorem subd9_0_161 : subd9_0 [-2, -5, 2] = true := by decide +kernel
theorem subd9_0_162 : subd9_0 [-2, -5, 3] = true := by decide +kernel
theorem subd9_0_163 : subd9_0 [-2, -5, 4] = true := by decide +kernel
theorem subd9_0_164 : subd9_0 [-2, -5, 5] = true := by decide +kernel
theorem subd9_0_165 : subd9_0 [-2, -5, 6] = true := by decide +kernel
theorem subd9_0_166 : subd9_0 [-2, -5, 7] = true := by decide +kernel
theorem subd9_0_167 : subd9_0 [-2, -4, -7] = true := by decide +kernel
theorem subd9_0_168 : subd9_0 [-2, -4, -6] = true := by decide +kernel
theorem subd9_0_169 : subd9_0 [-2, -4, -5] = true := by decide +kernel
theorem subd9_0_170 : subd9_0 [-2, -4, -4] = true := by decide +kernel
theorem subd9_0_171 : subd9_0 [-2, -4, -3] = true := by decide +kernel
theorem subd9_0_172 : subd9_0 [-2, -4, -2] = true := by decide +kernel
theorem subd9_0_173 : subd9_0 [-2, -4, -1] = true := by decide +kernel
theorem subd9_0_174 : subd9_0 [-2, -4, 0] = true := by decide +kernel
theorem subd9_0_175 : subd9_0 [-2, -4, 1] = true := by decide +kernel
theorem subd9_0_176 : subd9_0 [-2, -4, 2] = true := by decide +kernel
theorem subd9_0_177 : subd9_0 [-2, -4, 3] = true := by decide +kernel
theorem subd9_0_178 : subd9_0 [-2, -4, 4] = true := by decide +kernel
theorem subd9_0_179 : subd9_0 [-2, -4, 5] = true := by decide +kernel
theorem subd9_0_180 : subd9_0 [-2, -4, 6] = true := by decide +kernel
theorem subd9_0_181 : subd9_0 [-2, -4, 7] = true := by decide +kernel
theorem subd9_0_182 : subd9_0 [-2, -4, 8] = true := by decide +kernel
theorem subd9_0_183 : subd9_0 [-2, -3, -9] = true := by decide +kernel
theorem subd9_0_184 : subd9_0 [-2, -3, -8] = true := by decide +kernel
theorem subd9_0_185 : subd9_0 [-2, -3, -7] = true := by decide +kernel
theorem subd9_0_186 : subd9_0 [-2, -3, -6] = true := by decide +kernel
theorem subd9_0_187 : subd9_0 [-2, -3, -5] = true := by decide +kernel
theorem subd9_0_188 : subd9_0 [-2, -3, -4] = true := by decide +kernel
theorem subd9_0_189 : subd9_0 [-2, -3, -3] = true := by decide +kernel
theorem subd9_0_190 : subd9_0 [-2, -3, -2] = true := by decide +kernel
theorem subd9_0_191 : subd9_0 [-2, -3, -1] = true := by decide +kernel
theorem sbd9_0_5 : ∀ q ∈ blkd9_0_5, subd9_0 q = true := by
  unfold blkd9_0_5
  exact List.forall_mem_cons.2 ⟨subd9_0_160, List.forall_mem_cons.2 ⟨subd9_0_161, List.forall_mem_cons.2 ⟨subd9_0_162, List.forall_mem_cons.2 ⟨subd9_0_163, List.forall_mem_cons.2 ⟨subd9_0_164, List.forall_mem_cons.2 ⟨subd9_0_165, List.forall_mem_cons.2 ⟨subd9_0_166, List.forall_mem_cons.2 ⟨subd9_0_167, List.forall_mem_cons.2 ⟨subd9_0_168, List.forall_mem_cons.2 ⟨subd9_0_169, List.forall_mem_cons.2 ⟨subd9_0_170, List.forall_mem_cons.2 ⟨subd9_0_171, List.forall_mem_cons.2 ⟨subd9_0_172, List.forall_mem_cons.2 ⟨subd9_0_173, List.forall_mem_cons.2 ⟨subd9_0_174, List.forall_mem_cons.2 ⟨subd9_0_175, List.forall_mem_cons.2 ⟨subd9_0_176, List.forall_mem_cons.2 ⟨subd9_0_177, List.forall_mem_cons.2 ⟨subd9_0_178, List.forall_mem_cons.2 ⟨subd9_0_179, List.forall_mem_cons.2 ⟨subd9_0_180, List.forall_mem_cons.2 ⟨subd9_0_181, List.forall_mem_cons.2 ⟨subd9_0_182, List.forall_mem_cons.2 ⟨subd9_0_183, List.forall_mem_cons.2 ⟨subd9_0_184, List.forall_mem_cons.2 ⟨subd9_0_185, List.forall_mem_cons.2 ⟨subd9_0_186, List.forall_mem_cons.2 ⟨subd9_0_187, List.forall_mem_cons.2 ⟨subd9_0_188, List.forall_mem_cons.2 ⟨subd9_0_189, List.forall_mem_cons.2 ⟨subd9_0_190, List.forall_mem_cons.2 ⟨subd9_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_192 : subd9_0 [-2, -3, 0] = true := by decide +kernel
theorem subd9_0_193 : subd9_0 [-2, -3, 1] = true := by decide +kernel
theorem subd9_0_194 : subd9_0 [-2, -3, 2] = true := by decide +kernel
theorem subd9_0_195 : subd9_0 [-2, -3, 3] = true := by decide +kernel
theorem subd9_0_196 : subd9_0 [-2, -3, 4] = true := by decide +kernel
theorem subd9_0_197 : subd9_0 [-2, -3, 5] = true := by decide +kernel
theorem subd9_0_198 : subd9_0 [-2, -3, 6] = true := by decide +kernel
theorem subd9_0_199 : subd9_0 [-2, -3, 7] = true := by decide +kernel
theorem subd9_0_200 : subd9_0 [-2, -3, 8] = true := by decide +kernel
theorem subd9_0_201 : subd9_0 [-2, -3, 9] = true := by decide +kernel
theorem subd9_0_202 : subd9_0 [-2, -2, -10] = true := by decide +kernel
theorem subd9_0_203 : subd9_0 [-2, -2, -9] = true := by decide +kernel
theorem subd9_0_204 : subd9_0 [-2, -2, -8] = true := by decide +kernel
theorem subd9_0_205 : subd9_0 [-2, -2, -7] = true := by decide +kernel
theorem subd9_0_206 : subd9_0 [-2, -2, -6] = true := by decide +kernel
theorem subd9_0_207 : subd9_0 [-2, -2, -5] = true := by decide +kernel
theorem subd9_0_208 : subd9_0 [-2, -2, -4] = true := by decide +kernel
theorem subd9_0_209 : subd9_0 [-2, -2, -3] = true := by decide +kernel
theorem subd9_0_210 : subd9_0 [-2, -2, -2] = true := by decide +kernel
theorem subd9_0_211 : subd9_0 [-2, -2, -1] = true := by decide +kernel
theorem subd9_0_212 : subd9_0 [-2, -2, 0] = true := by decide +kernel
theorem subd9_0_213 : subd9_0 [-2, -2, 1] = true := by decide +kernel
theorem subd9_0_214 : subd9_0 [-2, -2, 2] = true := by decide +kernel
theorem subd9_0_215 : subd9_0 [-2, -2, 3] = true := by decide +kernel
theorem subd9_0_216 : subd9_0 [-2, -2, 4] = true := by decide +kernel
theorem subd9_0_217 : subd9_0 [-2, -2, 5] = true := by decide +kernel
theorem subd9_0_218 : subd9_0 [-2, -2, 6] = true := by decide +kernel
theorem subd9_0_219 : subd9_0 [-2, -2, 7] = true := by decide +kernel
theorem subd9_0_220 : subd9_0 [-2, -2, 8] = true := by decide +kernel
theorem subd9_0_221 : subd9_0 [-2, -2, 9] = true := by decide +kernel
theorem subd9_0_222 : subd9_0 [-2, -1, -10] = true := by decide +kernel
theorem subd9_0_223 : subd9_0 [-2, -1, -9] = true := by decide +kernel
theorem sbd9_0_6 : ∀ q ∈ blkd9_0_6, subd9_0 q = true := by
  unfold blkd9_0_6
  exact List.forall_mem_cons.2 ⟨subd9_0_192, List.forall_mem_cons.2 ⟨subd9_0_193, List.forall_mem_cons.2 ⟨subd9_0_194, List.forall_mem_cons.2 ⟨subd9_0_195, List.forall_mem_cons.2 ⟨subd9_0_196, List.forall_mem_cons.2 ⟨subd9_0_197, List.forall_mem_cons.2 ⟨subd9_0_198, List.forall_mem_cons.2 ⟨subd9_0_199, List.forall_mem_cons.2 ⟨subd9_0_200, List.forall_mem_cons.2 ⟨subd9_0_201, List.forall_mem_cons.2 ⟨subd9_0_202, List.forall_mem_cons.2 ⟨subd9_0_203, List.forall_mem_cons.2 ⟨subd9_0_204, List.forall_mem_cons.2 ⟨subd9_0_205, List.forall_mem_cons.2 ⟨subd9_0_206, List.forall_mem_cons.2 ⟨subd9_0_207, List.forall_mem_cons.2 ⟨subd9_0_208, List.forall_mem_cons.2 ⟨subd9_0_209, List.forall_mem_cons.2 ⟨subd9_0_210, List.forall_mem_cons.2 ⟨subd9_0_211, List.forall_mem_cons.2 ⟨subd9_0_212, List.forall_mem_cons.2 ⟨subd9_0_213, List.forall_mem_cons.2 ⟨subd9_0_214, List.forall_mem_cons.2 ⟨subd9_0_215, List.forall_mem_cons.2 ⟨subd9_0_216, List.forall_mem_cons.2 ⟨subd9_0_217, List.forall_mem_cons.2 ⟨subd9_0_218, List.forall_mem_cons.2 ⟨subd9_0_219, List.forall_mem_cons.2 ⟨subd9_0_220, List.forall_mem_cons.2 ⟨subd9_0_221, List.forall_mem_cons.2 ⟨subd9_0_222, List.forall_mem_cons.2 ⟨subd9_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_224 : subd9_0 [-2, -1, -8] = true := by decide +kernel
theorem subd9_0_225 : subd9_0 [-2, -1, -7] = true := by decide +kernel
theorem subd9_0_226 : subd9_0 [-2, -1, -6] = true := by decide +kernel
theorem subd9_0_227 : subd9_0 [-2, -1, -5] = true := by decide +kernel
theorem subd9_0_228 : subd9_0 [-2, -1, -4] = true := by decide +kernel
theorem subd9_0_229 : subd9_0 [-2, -1, -3] = true := by decide +kernel
theorem subd9_0_230 : subd9_0 [-2, -1, -2] = true := by decide +kernel
theorem subd9_0_231 : subd9_0 [-2, -1, -1] = true := by decide +kernel
theorem subd9_0_232 : subd9_0 [-2, -1, 0] = true := by decide +kernel
theorem subd9_0_233 : subd9_0 [-2, -1, 1] = true := by decide +kernel
theorem subd9_0_234 : subd9_0 [-2, -1, 2] = true := by decide +kernel
theorem subd9_0_235 : subd9_0 [-2, -1, 3] = true := by decide +kernel
theorem subd9_0_236 : subd9_0 [-2, -1, 4] = true := by decide +kernel
theorem subd9_0_237 : subd9_0 [-2, -1, 5] = true := by decide +kernel
theorem subd9_0_238 : subd9_0 [-2, -1, 6] = true := by decide +kernel
theorem subd9_0_239 : subd9_0 [-2, -1, 7] = true := by decide +kernel
theorem subd9_0_240 : subd9_0 [-2, -1, 8] = true := by decide +kernel
theorem subd9_0_241 : subd9_0 [-2, 0, -11] = true := by decide +kernel
theorem subd9_0_242 : subd9_0 [-2, 0, -10] = true := by decide +kernel
theorem subd9_0_243 : subd9_0 [-2, 0, -9] = true := by decide +kernel
theorem subd9_0_244 : subd9_0 [-2, 0, -8] = true := by decide +kernel
theorem subd9_0_245 : subd9_0 [-2, 0, -7] = true := by decide +kernel
theorem subd9_0_246 : subd9_0 [-2, 0, -6] = true := by decide +kernel
theorem subd9_0_247 : subd9_0 [-2, 0, -5] = true := by decide +kernel
theorem subd9_0_248 : subd9_0 [-2, 0, -4] = true := by decide +kernel
theorem subd9_0_249 : subd9_0 [-2, 0, -3] = true := by decide +kernel
theorem subd9_0_250 : subd9_0 [-2, 0, -2] = true := by decide +kernel
theorem subd9_0_251 : subd9_0 [-2, 0, -1] = true := by decide +kernel
theorem subd9_0_252 : subd9_0 [-2, 0, 0] = true := by decide +kernel
theorem subd9_0_253 : subd9_0 [-2, 0, 1] = true := by decide +kernel
theorem subd9_0_254 : subd9_0 [-2, 0, 2] = true := by decide +kernel
theorem subd9_0_255 : subd9_0 [-2, 0, 3] = true := by decide +kernel
theorem sbd9_0_7 : ∀ q ∈ blkd9_0_7, subd9_0 q = true := by
  unfold blkd9_0_7
  exact List.forall_mem_cons.2 ⟨subd9_0_224, List.forall_mem_cons.2 ⟨subd9_0_225, List.forall_mem_cons.2 ⟨subd9_0_226, List.forall_mem_cons.2 ⟨subd9_0_227, List.forall_mem_cons.2 ⟨subd9_0_228, List.forall_mem_cons.2 ⟨subd9_0_229, List.forall_mem_cons.2 ⟨subd9_0_230, List.forall_mem_cons.2 ⟨subd9_0_231, List.forall_mem_cons.2 ⟨subd9_0_232, List.forall_mem_cons.2 ⟨subd9_0_233, List.forall_mem_cons.2 ⟨subd9_0_234, List.forall_mem_cons.2 ⟨subd9_0_235, List.forall_mem_cons.2 ⟨subd9_0_236, List.forall_mem_cons.2 ⟨subd9_0_237, List.forall_mem_cons.2 ⟨subd9_0_238, List.forall_mem_cons.2 ⟨subd9_0_239, List.forall_mem_cons.2 ⟨subd9_0_240, List.forall_mem_cons.2 ⟨subd9_0_241, List.forall_mem_cons.2 ⟨subd9_0_242, List.forall_mem_cons.2 ⟨subd9_0_243, List.forall_mem_cons.2 ⟨subd9_0_244, List.forall_mem_cons.2 ⟨subd9_0_245, List.forall_mem_cons.2 ⟨subd9_0_246, List.forall_mem_cons.2 ⟨subd9_0_247, List.forall_mem_cons.2 ⟨subd9_0_248, List.forall_mem_cons.2 ⟨subd9_0_249, List.forall_mem_cons.2 ⟨subd9_0_250, List.forall_mem_cons.2 ⟨subd9_0_251, List.forall_mem_cons.2 ⟨subd9_0_252, List.forall_mem_cons.2 ⟨subd9_0_253, List.forall_mem_cons.2 ⟨subd9_0_254, List.forall_mem_cons.2 ⟨subd9_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_256 : subd9_0 [-2, 0, 4] = true := by decide +kernel
theorem subd9_0_257 : subd9_0 [-2, 0, 5] = true := by decide +kernel
theorem subd9_0_258 : subd9_0 [-2, 0, 6] = true := by decide +kernel
theorem subd9_0_259 : subd9_0 [-2, 0, 7] = true := by decide +kernel
theorem subd9_0_260 : subd9_0 [-2, 0, 8] = true := by decide +kernel
theorem subd9_0_261 : subd9_0 [-2, 1, -11] = true := by decide +kernel
theorem subd9_0_262 : subd9_0 [-2, 1, -10] = true := by decide +kernel
theorem subd9_0_263 : subd9_0 [-2, 1, -9] = true := by decide +kernel
theorem subd9_0_264 : subd9_0 [-2, 1, -8] = true := by decide +kernel
theorem subd9_0_265 : subd9_0 [-2, 1, -7] = true := by decide +kernel
theorem subd9_0_266 : subd9_0 [-2, 1, -6] = true := by decide +kernel
theorem subd9_0_267 : subd9_0 [-2, 1, -5] = true := by decide +kernel
theorem subd9_0_268 : subd9_0 [-2, 1, -4] = true := by decide +kernel
theorem subd9_0_269 : subd9_0 [-2, 1, -3] = true := by decide +kernel
theorem subd9_0_270 : subd9_0 [-2, 1, -2] = true := by decide +kernel
theorem subd9_0_271 : subd9_0 [-2, 1, -1] = true := by decide +kernel
theorem subd9_0_272 : subd9_0 [-2, 1, 0] = true := by decide +kernel
theorem subd9_0_273 : subd9_0 [-2, 1, 1] = true := by decide +kernel
theorem subd9_0_274 : subd9_0 [-2, 1, 2] = true := by decide +kernel
theorem subd9_0_275 : subd9_0 [-2, 1, 3] = true := by decide +kernel
theorem subd9_0_276 : subd9_0 [-2, 1, 4] = true := by decide +kernel
theorem subd9_0_277 : subd9_0 [-2, 1, 5] = true := by decide +kernel
theorem subd9_0_278 : subd9_0 [-2, 1, 6] = true := by decide +kernel
theorem subd9_0_279 : subd9_0 [-2, 1, 7] = true := by decide +kernel
theorem subd9_0_280 : subd9_0 [-2, 2, -10] = true := by decide +kernel
theorem subd9_0_281 : subd9_0 [-2, 2, -9] = true := by decide +kernel
theorem subd9_0_282 : subd9_0 [-2, 2, -8] = true := by decide +kernel
theorem subd9_0_283 : subd9_0 [-2, 2, -7] = true := by decide +kernel
theorem subd9_0_284 : subd9_0 [-2, 2, -6] = true := by decide +kernel
theorem subd9_0_285 : subd9_0 [-2, 2, -5] = true := by decide +kernel
theorem subd9_0_286 : subd9_0 [-2, 2, -4] = true := by decide +kernel
theorem subd9_0_287 : subd9_0 [-2, 2, -3] = true := by decide +kernel
theorem sbd9_0_8 : ∀ q ∈ blkd9_0_8, subd9_0 q = true := by
  unfold blkd9_0_8
  exact List.forall_mem_cons.2 ⟨subd9_0_256, List.forall_mem_cons.2 ⟨subd9_0_257, List.forall_mem_cons.2 ⟨subd9_0_258, List.forall_mem_cons.2 ⟨subd9_0_259, List.forall_mem_cons.2 ⟨subd9_0_260, List.forall_mem_cons.2 ⟨subd9_0_261, List.forall_mem_cons.2 ⟨subd9_0_262, List.forall_mem_cons.2 ⟨subd9_0_263, List.forall_mem_cons.2 ⟨subd9_0_264, List.forall_mem_cons.2 ⟨subd9_0_265, List.forall_mem_cons.2 ⟨subd9_0_266, List.forall_mem_cons.2 ⟨subd9_0_267, List.forall_mem_cons.2 ⟨subd9_0_268, List.forall_mem_cons.2 ⟨subd9_0_269, List.forall_mem_cons.2 ⟨subd9_0_270, List.forall_mem_cons.2 ⟨subd9_0_271, List.forall_mem_cons.2 ⟨subd9_0_272, List.forall_mem_cons.2 ⟨subd9_0_273, List.forall_mem_cons.2 ⟨subd9_0_274, List.forall_mem_cons.2 ⟨subd9_0_275, List.forall_mem_cons.2 ⟨subd9_0_276, List.forall_mem_cons.2 ⟨subd9_0_277, List.forall_mem_cons.2 ⟨subd9_0_278, List.forall_mem_cons.2 ⟨subd9_0_279, List.forall_mem_cons.2 ⟨subd9_0_280, List.forall_mem_cons.2 ⟨subd9_0_281, List.forall_mem_cons.2 ⟨subd9_0_282, List.forall_mem_cons.2 ⟨subd9_0_283, List.forall_mem_cons.2 ⟨subd9_0_284, List.forall_mem_cons.2 ⟨subd9_0_285, List.forall_mem_cons.2 ⟨subd9_0_286, List.forall_mem_cons.2 ⟨subd9_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_288 : subd9_0 [-2, 2, -2] = true := by decide +kernel
theorem subd9_0_289 : subd9_0 [-2, 2, -1] = true := by decide +kernel
theorem subd9_0_290 : subd9_0 [-2, 2, 0] = true := by decide +kernel
theorem subd9_0_291 : subd9_0 [-2, 2, 1] = true := by decide +kernel
theorem subd9_0_292 : subd9_0 [-2, 2, 2] = true := by decide +kernel
theorem subd9_0_293 : subd9_0 [-2, 2, 3] = true := by decide +kernel
theorem subd9_0_294 : subd9_0 [-2, 2, 4] = true := by decide +kernel
theorem subd9_0_295 : subd9_0 [-2, 2, 5] = true := by decide +kernel
theorem subd9_0_296 : subd9_0 [-2, 3, -9] = true := by decide +kernel
theorem subd9_0_297 : subd9_0 [-2, 3, -8] = true := by decide +kernel
theorem subd9_0_298 : subd9_0 [-2, 3, -7] = true := by decide +kernel
theorem subd9_0_299 : subd9_0 [-2, 3, -6] = true := by decide +kernel
theorem subd9_0_300 : subd9_0 [-2, 3, -5] = true := by decide +kernel
theorem subd9_0_301 : subd9_0 [-2, 3, -4] = true := by decide +kernel
theorem subd9_0_302 : subd9_0 [-2, 3, -3] = true := by decide +kernel
theorem subd9_0_303 : subd9_0 [-2, 3, -2] = true := by decide +kernel
theorem subd9_0_304 : subd9_0 [-2, 3, -1] = true := by decide +kernel
theorem subd9_0_305 : subd9_0 [-2, 3, 0] = true := by decide +kernel
theorem subd9_0_306 : subd9_0 [-2, 3, 1] = true := by decide +kernel
theorem subd9_0_307 : subd9_0 [-2, 3, 2] = true := by decide +kernel
theorem subd9_0_308 : subd9_0 [-2, 3, 3] = true := by decide +kernel
theorem subd9_0_309 : subd9_0 [-2, 3, 4] = true := by decide +kernel
theorem subd9_0_310 : subd9_0 [-2, 4] = true := by decide +kernel
theorem subd9_0_311 : subd9_0 [-1, -7] = true := by decide +kernel
theorem subd9_0_312 : subd9_0 [-1, -6] = true := by decide +kernel
theorem subd9_0_313 : subd9_0 [-1, -5, -5] = true := by decide +kernel
theorem subd9_0_314 : subd9_0 [-1, -5, -4] = true := by decide +kernel
theorem subd9_0_315 : subd9_0 [-1, -5, -3] = true := by decide +kernel
theorem subd9_0_316 : subd9_0 [-1, -5, -2] = true := by decide +kernel
theorem subd9_0_317 : subd9_0 [-1, -5, -1] = true := by decide +kernel
theorem subd9_0_318 : subd9_0 [-1, -5, 0] = true := by decide +kernel
theorem subd9_0_319 : subd9_0 [-1, -5, 1] = true := by decide +kernel
theorem sbd9_0_9 : ∀ q ∈ blkd9_0_9, subd9_0 q = true := by
  unfold blkd9_0_9
  exact List.forall_mem_cons.2 ⟨subd9_0_288, List.forall_mem_cons.2 ⟨subd9_0_289, List.forall_mem_cons.2 ⟨subd9_0_290, List.forall_mem_cons.2 ⟨subd9_0_291, List.forall_mem_cons.2 ⟨subd9_0_292, List.forall_mem_cons.2 ⟨subd9_0_293, List.forall_mem_cons.2 ⟨subd9_0_294, List.forall_mem_cons.2 ⟨subd9_0_295, List.forall_mem_cons.2 ⟨subd9_0_296, List.forall_mem_cons.2 ⟨subd9_0_297, List.forall_mem_cons.2 ⟨subd9_0_298, List.forall_mem_cons.2 ⟨subd9_0_299, List.forall_mem_cons.2 ⟨subd9_0_300, List.forall_mem_cons.2 ⟨subd9_0_301, List.forall_mem_cons.2 ⟨subd9_0_302, List.forall_mem_cons.2 ⟨subd9_0_303, List.forall_mem_cons.2 ⟨subd9_0_304, List.forall_mem_cons.2 ⟨subd9_0_305, List.forall_mem_cons.2 ⟨subd9_0_306, List.forall_mem_cons.2 ⟨subd9_0_307, List.forall_mem_cons.2 ⟨subd9_0_308, List.forall_mem_cons.2 ⟨subd9_0_309, List.forall_mem_cons.2 ⟨subd9_0_310, List.forall_mem_cons.2 ⟨subd9_0_311, List.forall_mem_cons.2 ⟨subd9_0_312, List.forall_mem_cons.2 ⟨subd9_0_313, List.forall_mem_cons.2 ⟨subd9_0_314, List.forall_mem_cons.2 ⟨subd9_0_315, List.forall_mem_cons.2 ⟨subd9_0_316, List.forall_mem_cons.2 ⟨subd9_0_317, List.forall_mem_cons.2 ⟨subd9_0_318, List.forall_mem_cons.2 ⟨subd9_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_320 : subd9_0 [-1, -5, 2] = true := by decide +kernel
theorem subd9_0_321 : subd9_0 [-1, -5, 3] = true := by decide +kernel
theorem subd9_0_322 : subd9_0 [-1, -5, 4] = true := by decide +kernel
theorem subd9_0_323 : subd9_0 [-1, -5, 5] = true := by decide +kernel
theorem subd9_0_324 : subd9_0 [-1, -5, 6] = true := by decide +kernel
theorem subd9_0_325 : subd9_0 [-1, -5, 7] = true := by decide +kernel
theorem subd9_0_326 : subd9_0 [-1, -5, 8] = true := by decide +kernel
theorem subd9_0_327 : subd9_0 [-1, -4, -7] = true := by decide +kernel
theorem subd9_0_328 : subd9_0 [-1, -4, -6] = true := by decide +kernel
theorem subd9_0_329 : subd9_0 [-1, -4, -5] = true := by decide +kernel
theorem subd9_0_330 : subd9_0 [-1, -4, -4] = true := by decide +kernel
theorem subd9_0_331 : subd9_0 [-1, -4, -3] = true := by decide +kernel
theorem subd9_0_332 : subd9_0 [-1, -4, -2] = true := by decide +kernel
theorem subd9_0_333 : subd9_0 [-1, -4, -1] = true := by decide +kernel
theorem subd9_0_334 : subd9_0 [-1, -4, 0] = true := by decide +kernel
theorem subd9_0_335 : subd9_0 [-1, -4, 1] = true := by decide +kernel
theorem subd9_0_336 : subd9_0 [-1, -4, 2] = true := by decide +kernel
theorem subd9_0_337 : subd9_0 [-1, -4, 3] = true := by decide +kernel
theorem subd9_0_338 : subd9_0 [-1, -4, 4] = true := by decide +kernel
theorem subd9_0_339 : subd9_0 [-1, -4, 5] = true := by decide +kernel
theorem subd9_0_340 : subd9_0 [-1, -4, 6] = true := by decide +kernel
theorem subd9_0_341 : subd9_0 [-1, -4, 7] = true := by decide +kernel
theorem subd9_0_342 : subd9_0 [-1, -4, 8] = true := by decide +kernel
theorem subd9_0_343 : subd9_0 [-1, -4, 9] = true := by decide +kernel
theorem subd9_0_344 : subd9_0 [-1, -3, -8] = true := by decide +kernel
theorem subd9_0_345 : subd9_0 [-1, -3, -7] = true := by decide +kernel
theorem subd9_0_346 : subd9_0 [-1, -3, -6] = true := by decide +kernel
theorem subd9_0_347 : subd9_0 [-1, -3, -5] = true := by decide +kernel
theorem subd9_0_348 : subd9_0 [-1, -3, -4] = true := by decide +kernel
theorem subd9_0_349 : subd9_0 [-1, -3, -3] = true := by decide +kernel
theorem subd9_0_350 : subd9_0 [-1, -3, -2] = true := by decide +kernel
theorem subd9_0_351 : subd9_0 [-1, -3, -1] = true := by decide +kernel
theorem sbd9_0_10 : ∀ q ∈ blkd9_0_10, subd9_0 q = true := by
  unfold blkd9_0_10
  exact List.forall_mem_cons.2 ⟨subd9_0_320, List.forall_mem_cons.2 ⟨subd9_0_321, List.forall_mem_cons.2 ⟨subd9_0_322, List.forall_mem_cons.2 ⟨subd9_0_323, List.forall_mem_cons.2 ⟨subd9_0_324, List.forall_mem_cons.2 ⟨subd9_0_325, List.forall_mem_cons.2 ⟨subd9_0_326, List.forall_mem_cons.2 ⟨subd9_0_327, List.forall_mem_cons.2 ⟨subd9_0_328, List.forall_mem_cons.2 ⟨subd9_0_329, List.forall_mem_cons.2 ⟨subd9_0_330, List.forall_mem_cons.2 ⟨subd9_0_331, List.forall_mem_cons.2 ⟨subd9_0_332, List.forall_mem_cons.2 ⟨subd9_0_333, List.forall_mem_cons.2 ⟨subd9_0_334, List.forall_mem_cons.2 ⟨subd9_0_335, List.forall_mem_cons.2 ⟨subd9_0_336, List.forall_mem_cons.2 ⟨subd9_0_337, List.forall_mem_cons.2 ⟨subd9_0_338, List.forall_mem_cons.2 ⟨subd9_0_339, List.forall_mem_cons.2 ⟨subd9_0_340, List.forall_mem_cons.2 ⟨subd9_0_341, List.forall_mem_cons.2 ⟨subd9_0_342, List.forall_mem_cons.2 ⟨subd9_0_343, List.forall_mem_cons.2 ⟨subd9_0_344, List.forall_mem_cons.2 ⟨subd9_0_345, List.forall_mem_cons.2 ⟨subd9_0_346, List.forall_mem_cons.2 ⟨subd9_0_347, List.forall_mem_cons.2 ⟨subd9_0_348, List.forall_mem_cons.2 ⟨subd9_0_349, List.forall_mem_cons.2 ⟨subd9_0_350, List.forall_mem_cons.2 ⟨subd9_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_352 : subd9_0 [-1, -3, 0] = true := by decide +kernel
theorem subd9_0_353 : subd9_0 [-1, -3, 1] = true := by decide +kernel
theorem subd9_0_354 : subd9_0 [-1, -3, 2] = true := by decide +kernel
theorem subd9_0_355 : subd9_0 [-1, -3, 3] = true := by decide +kernel
theorem subd9_0_356 : subd9_0 [-1, -3, 4] = true := by decide +kernel
theorem subd9_0_357 : subd9_0 [-1, -3, 5] = true := by decide +kernel
theorem subd9_0_358 : subd9_0 [-1, -3, 6] = true := by decide +kernel
theorem subd9_0_359 : subd9_0 [-1, -3, 7] = true := by decide +kernel
theorem subd9_0_360 : subd9_0 [-1, -3, 8] = true := by decide +kernel
theorem subd9_0_361 : subd9_0 [-1, -3, 9] = true := by decide +kernel
theorem subd9_0_362 : subd9_0 [-1, -2, -10] = true := by decide +kernel
theorem subd9_0_363 : subd9_0 [-1, -2, -9] = true := by decide +kernel
theorem subd9_0_364 : subd9_0 [-1, -2, -8] = true := by decide +kernel
theorem subd9_0_365 : subd9_0 [-1, -2, -7] = true := by decide +kernel
theorem subd9_0_366 : subd9_0 [-1, -2, -6] = true := by decide +kernel
theorem subd9_0_367 : subd9_0 [-1, -2, -5] = true := by decide +kernel
theorem subd9_0_368 : subd9_0 [-1, -2, -4] = true := by decide +kernel
theorem subd9_0_369 : subd9_0 [-1, -2, -3] = true := by decide +kernel
theorem subd9_0_370 : subd9_0 [-1, -2, -2] = true := by decide +kernel
theorem subd9_0_371 : subd9_0 [-1, -2, -1] = true := by decide +kernel
theorem subd9_0_372 : subd9_0 [-1, -2, 0] = true := by decide +kernel
theorem subd9_0_373 : subd9_0 [-1, -2, 1] = true := by decide +kernel
theorem subd9_0_374 : subd9_0 [-1, -2, 2] = true := by decide +kernel
theorem subd9_0_375 : subd9_0 [-1, -2, 3] = true := by decide +kernel
theorem subd9_0_376 : subd9_0 [-1, -2, 4] = true := by decide +kernel
theorem subd9_0_377 : subd9_0 [-1, -2, 5] = true := by decide +kernel
theorem subd9_0_378 : subd9_0 [-1, -2, 6] = true := by decide +kernel
theorem subd9_0_379 : subd9_0 [-1, -2, 7] = true := by decide +kernel
theorem subd9_0_380 : subd9_0 [-1, -2, 8] = true := by decide +kernel
theorem subd9_0_381 : subd9_0 [-1, -2, 9] = true := by decide +kernel
theorem subd9_0_382 : subd9_0 [-1, -1, -10] = true := by decide +kernel
theorem subd9_0_383 : subd9_0 [-1, -1, -9] = true := by decide +kernel
theorem sbd9_0_11 : ∀ q ∈ blkd9_0_11, subd9_0 q = true := by
  unfold blkd9_0_11
  exact List.forall_mem_cons.2 ⟨subd9_0_352, List.forall_mem_cons.2 ⟨subd9_0_353, List.forall_mem_cons.2 ⟨subd9_0_354, List.forall_mem_cons.2 ⟨subd9_0_355, List.forall_mem_cons.2 ⟨subd9_0_356, List.forall_mem_cons.2 ⟨subd9_0_357, List.forall_mem_cons.2 ⟨subd9_0_358, List.forall_mem_cons.2 ⟨subd9_0_359, List.forall_mem_cons.2 ⟨subd9_0_360, List.forall_mem_cons.2 ⟨subd9_0_361, List.forall_mem_cons.2 ⟨subd9_0_362, List.forall_mem_cons.2 ⟨subd9_0_363, List.forall_mem_cons.2 ⟨subd9_0_364, List.forall_mem_cons.2 ⟨subd9_0_365, List.forall_mem_cons.2 ⟨subd9_0_366, List.forall_mem_cons.2 ⟨subd9_0_367, List.forall_mem_cons.2 ⟨subd9_0_368, List.forall_mem_cons.2 ⟨subd9_0_369, List.forall_mem_cons.2 ⟨subd9_0_370, List.forall_mem_cons.2 ⟨subd9_0_371, List.forall_mem_cons.2 ⟨subd9_0_372, List.forall_mem_cons.2 ⟨subd9_0_373, List.forall_mem_cons.2 ⟨subd9_0_374, List.forall_mem_cons.2 ⟨subd9_0_375, List.forall_mem_cons.2 ⟨subd9_0_376, List.forall_mem_cons.2 ⟨subd9_0_377, List.forall_mem_cons.2 ⟨subd9_0_378, List.forall_mem_cons.2 ⟨subd9_0_379, List.forall_mem_cons.2 ⟨subd9_0_380, List.forall_mem_cons.2 ⟨subd9_0_381, List.forall_mem_cons.2 ⟨subd9_0_382, List.forall_mem_cons.2 ⟨subd9_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_384 : subd9_0 [-1, -1, -8] = true := by decide +kernel
theorem subd9_0_385 : subd9_0 [-1, -1, -7] = true := by decide +kernel
theorem subd9_0_386 : subd9_0 [-1, -1, -6] = true := by decide +kernel
theorem subd9_0_387 : subd9_0 [-1, -1, -5] = true := by decide +kernel
theorem subd9_0_388 : subd9_0 [-1, -1, -4] = true := by decide +kernel
theorem subd9_0_389 : subd9_0 [-1, -1, -3] = true := by decide +kernel
theorem subd9_0_390 : subd9_0 [-1, -1, -2] = true := by decide +kernel
theorem subd9_0_391 : subd9_0 [-1, -1, -1] = true := by decide +kernel
theorem subd9_0_392 : subd9_0 [-1, -1, 0] = true := by decide +kernel
theorem subd9_0_393 : subd9_0 [-1, -1, 1] = true := by decide +kernel
theorem subd9_0_394 : subd9_0 [-1, -1, 2] = true := by decide +kernel
theorem subd9_0_395 : subd9_0 [-1, -1, 3] = true := by decide +kernel
theorem subd9_0_396 : subd9_0 [-1, -1, 4] = true := by decide +kernel
theorem subd9_0_397 : subd9_0 [-1, -1, 5] = true := by decide +kernel
theorem subd9_0_398 : subd9_0 [-1, -1, 6] = true := by decide +kernel
theorem subd9_0_399 : subd9_0 [-1, -1, 7] = true := by decide +kernel
theorem subd9_0_400 : subd9_0 [-1, -1, 8] = true := by decide +kernel
theorem subd9_0_401 : subd9_0 [-1, -1, 9] = true := by decide +kernel
theorem subd9_0_402 : subd9_0 [-1, 0, -11] = true := by decide +kernel
theorem subd9_0_403 : subd9_0 [-1, 0, -10] = true := by decide +kernel
theorem subd9_0_404 : subd9_0 [-1, 0, -9] = true := by decide +kernel
theorem subd9_0_405 : subd9_0 [-1, 0, -8] = true := by decide +kernel
theorem subd9_0_406 : subd9_0 [-1, 0, -7] = true := by decide +kernel
theorem subd9_0_407 : subd9_0 [-1, 0, -6] = true := by decide +kernel
theorem subd9_0_408 : subd9_0 [-1, 0, -5] = true := by decide +kernel
theorem subd9_0_409 : subd9_0 [-1, 0, -4] = true := by decide +kernel
theorem subd9_0_410 : subd9_0 [-1, 0, -3] = true := by decide +kernel
theorem subd9_0_411 : subd9_0 [-1, 0, -2] = true := by decide +kernel
theorem subd9_0_412 : subd9_0 [-1, 0, -1] = true := by decide +kernel
theorem subd9_0_413 : subd9_0 [-1, 0, 0] = true := by decide +kernel
theorem subd9_0_414 : subd9_0 [-1, 0, 1] = true := by decide +kernel
theorem subd9_0_415 : subd9_0 [-1, 0, 2] = true := by decide +kernel
theorem sbd9_0_12 : ∀ q ∈ blkd9_0_12, subd9_0 q = true := by
  unfold blkd9_0_12
  exact List.forall_mem_cons.2 ⟨subd9_0_384, List.forall_mem_cons.2 ⟨subd9_0_385, List.forall_mem_cons.2 ⟨subd9_0_386, List.forall_mem_cons.2 ⟨subd9_0_387, List.forall_mem_cons.2 ⟨subd9_0_388, List.forall_mem_cons.2 ⟨subd9_0_389, List.forall_mem_cons.2 ⟨subd9_0_390, List.forall_mem_cons.2 ⟨subd9_0_391, List.forall_mem_cons.2 ⟨subd9_0_392, List.forall_mem_cons.2 ⟨subd9_0_393, List.forall_mem_cons.2 ⟨subd9_0_394, List.forall_mem_cons.2 ⟨subd9_0_395, List.forall_mem_cons.2 ⟨subd9_0_396, List.forall_mem_cons.2 ⟨subd9_0_397, List.forall_mem_cons.2 ⟨subd9_0_398, List.forall_mem_cons.2 ⟨subd9_0_399, List.forall_mem_cons.2 ⟨subd9_0_400, List.forall_mem_cons.2 ⟨subd9_0_401, List.forall_mem_cons.2 ⟨subd9_0_402, List.forall_mem_cons.2 ⟨subd9_0_403, List.forall_mem_cons.2 ⟨subd9_0_404, List.forall_mem_cons.2 ⟨subd9_0_405, List.forall_mem_cons.2 ⟨subd9_0_406, List.forall_mem_cons.2 ⟨subd9_0_407, List.forall_mem_cons.2 ⟨subd9_0_408, List.forall_mem_cons.2 ⟨subd9_0_409, List.forall_mem_cons.2 ⟨subd9_0_410, List.forall_mem_cons.2 ⟨subd9_0_411, List.forall_mem_cons.2 ⟨subd9_0_412, List.forall_mem_cons.2 ⟨subd9_0_413, List.forall_mem_cons.2 ⟨subd9_0_414, List.forall_mem_cons.2 ⟨subd9_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_416 : subd9_0 [-1, 0, 3] = true := by decide +kernel
theorem subd9_0_417 : subd9_0 [-1, 0, 4] = true := by decide +kernel
theorem subd9_0_418 : subd9_0 [-1, 0, 5] = true := by decide +kernel
theorem subd9_0_419 : subd9_0 [-1, 0, 6] = true := by decide +kernel
theorem subd9_0_420 : subd9_0 [-1, 0, 7] = true := by decide +kernel
theorem subd9_0_421 : subd9_0 [-1, 0, 8] = true := by decide +kernel
theorem subd9_0_422 : subd9_0 [-1, 0, 9] = true := by decide +kernel
theorem subd9_0_423 : subd9_0 [-1, 1, -11] = true := by decide +kernel
theorem subd9_0_424 : subd9_0 [-1, 1, -10] = true := by decide +kernel
theorem subd9_0_425 : subd9_0 [-1, 1, -9] = true := by decide +kernel
theorem subd9_0_426 : subd9_0 [-1, 1, -8] = true := by decide +kernel
theorem subd9_0_427 : subd9_0 [-1, 1, -7] = true := by decide +kernel
theorem subd9_0_428 : subd9_0 [-1, 1, -6] = true := by decide +kernel
theorem subd9_0_429 : subd9_0 [-1, 1, -5] = true := by decide +kernel
theorem subd9_0_430 : subd9_0 [-1, 1, -4] = true := by decide +kernel
theorem subd9_0_431 : subd9_0 [-1, 1, -3] = true := by decide +kernel
theorem subd9_0_432 : subd9_0 [-1, 1, -2] = true := by decide +kernel
theorem subd9_0_433 : subd9_0 [-1, 1, -1] = true := by decide +kernel
theorem subd9_0_434 : subd9_0 [-1, 1, 0] = true := by decide +kernel
theorem subd9_0_435 : subd9_0 [-1, 1, 1] = true := by decide +kernel
theorem subd9_0_436 : subd9_0 [-1, 1, 2] = true := by decide +kernel
theorem subd9_0_437 : subd9_0 [-1, 1, 3] = true := by decide +kernel
theorem subd9_0_438 : subd9_0 [-1, 1, 4] = true := by decide +kernel
theorem subd9_0_439 : subd9_0 [-1, 1, 5] = true := by decide +kernel
theorem subd9_0_440 : subd9_0 [-1, 1, 6] = true := by decide +kernel
theorem subd9_0_441 : subd9_0 [-1, 1, 7] = true := by decide +kernel
theorem subd9_0_442 : subd9_0 [-1, 1, 8] = true := by decide +kernel
theorem subd9_0_443 : subd9_0 [-1, 2, -11] = true := by decide +kernel
theorem subd9_0_444 : subd9_0 [-1, 2, -10] = true := by decide +kernel
theorem subd9_0_445 : subd9_0 [-1, 2, -9] = true := by decide +kernel
theorem subd9_0_446 : subd9_0 [-1, 2, -8] = true := by decide +kernel
theorem subd9_0_447 : subd9_0 [-1, 2, -7] = true := by decide +kernel
theorem sbd9_0_13 : ∀ q ∈ blkd9_0_13, subd9_0 q = true := by
  unfold blkd9_0_13
  exact List.forall_mem_cons.2 ⟨subd9_0_416, List.forall_mem_cons.2 ⟨subd9_0_417, List.forall_mem_cons.2 ⟨subd9_0_418, List.forall_mem_cons.2 ⟨subd9_0_419, List.forall_mem_cons.2 ⟨subd9_0_420, List.forall_mem_cons.2 ⟨subd9_0_421, List.forall_mem_cons.2 ⟨subd9_0_422, List.forall_mem_cons.2 ⟨subd9_0_423, List.forall_mem_cons.2 ⟨subd9_0_424, List.forall_mem_cons.2 ⟨subd9_0_425, List.forall_mem_cons.2 ⟨subd9_0_426, List.forall_mem_cons.2 ⟨subd9_0_427, List.forall_mem_cons.2 ⟨subd9_0_428, List.forall_mem_cons.2 ⟨subd9_0_429, List.forall_mem_cons.2 ⟨subd9_0_430, List.forall_mem_cons.2 ⟨subd9_0_431, List.forall_mem_cons.2 ⟨subd9_0_432, List.forall_mem_cons.2 ⟨subd9_0_433, List.forall_mem_cons.2 ⟨subd9_0_434, List.forall_mem_cons.2 ⟨subd9_0_435, List.forall_mem_cons.2 ⟨subd9_0_436, List.forall_mem_cons.2 ⟨subd9_0_437, List.forall_mem_cons.2 ⟨subd9_0_438, List.forall_mem_cons.2 ⟨subd9_0_439, List.forall_mem_cons.2 ⟨subd9_0_440, List.forall_mem_cons.2 ⟨subd9_0_441, List.forall_mem_cons.2 ⟨subd9_0_442, List.forall_mem_cons.2 ⟨subd9_0_443, List.forall_mem_cons.2 ⟨subd9_0_444, List.forall_mem_cons.2 ⟨subd9_0_445, List.forall_mem_cons.2 ⟨subd9_0_446, List.forall_mem_cons.2 ⟨subd9_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_448 : subd9_0 [-1, 2, -6] = true := by decide +kernel
theorem subd9_0_449 : subd9_0 [-1, 2, -5] = true := by decide +kernel
theorem subd9_0_450 : subd9_0 [-1, 2, -4] = true := by decide +kernel
theorem subd9_0_451 : subd9_0 [-1, 2, -3] = true := by decide +kernel
theorem subd9_0_452 : subd9_0 [-1, 2, -2] = true := by decide +kernel
theorem subd9_0_453 : subd9_0 [-1, 2, -1] = true := by decide +kernel
theorem subd9_0_454 : subd9_0 [-1, 2, 0] = true := by decide +kernel
theorem subd9_0_455 : subd9_0 [-1, 2, 1] = true := by decide +kernel
theorem subd9_0_456 : subd9_0 [-1, 2, 2] = true := by decide +kernel
theorem subd9_0_457 : subd9_0 [-1, 2, 3] = true := by decide +kernel
theorem subd9_0_458 : subd9_0 [-1, 2, 4] = true := by decide +kernel
theorem subd9_0_459 : subd9_0 [-1, 2, 5] = true := by decide +kernel
theorem subd9_0_460 : subd9_0 [-1, 2, 6] = true := by decide +kernel
theorem subd9_0_461 : subd9_0 [-1, 2, 7] = true := by decide +kernel
theorem subd9_0_462 : subd9_0 [-1, 3, -10] = true := by decide +kernel
theorem subd9_0_463 : subd9_0 [-1, 3, -9] = true := by decide +kernel
theorem subd9_0_464 : subd9_0 [-1, 3, -8] = true := by decide +kernel
theorem subd9_0_465 : subd9_0 [-1, 3, -7] = true := by decide +kernel
theorem subd9_0_466 : subd9_0 [-1, 3, -6] = true := by decide +kernel
theorem subd9_0_467 : subd9_0 [-1, 3, -5] = true := by decide +kernel
theorem subd9_0_468 : subd9_0 [-1, 3, -4] = true := by decide +kernel
theorem subd9_0_469 : subd9_0 [-1, 3, -3] = true := by decide +kernel
theorem subd9_0_470 : subd9_0 [-1, 3, -2] = true := by decide +kernel
theorem subd9_0_471 : subd9_0 [-1, 3, -1] = true := by decide +kernel
theorem subd9_0_472 : subd9_0 [-1, 3, 0] = true := by decide +kernel
theorem subd9_0_473 : subd9_0 [-1, 3, 1] = true := by decide +kernel
theorem subd9_0_474 : subd9_0 [-1, 3, 2] = true := by decide +kernel
theorem subd9_0_475 : subd9_0 [-1, 3, 3] = true := by decide +kernel
theorem subd9_0_476 : subd9_0 [-1, 3, 4] = true := by decide +kernel
theorem subd9_0_477 : subd9_0 [-1, 3, 5] = true := by decide +kernel
theorem subd9_0_478 : subd9_0 [-1, 3, 6] = true := by decide +kernel
theorem subd9_0_479 : subd9_0 [-1, 4, -9] = true := by decide +kernel
theorem sbd9_0_14 : ∀ q ∈ blkd9_0_14, subd9_0 q = true := by
  unfold blkd9_0_14
  exact List.forall_mem_cons.2 ⟨subd9_0_448, List.forall_mem_cons.2 ⟨subd9_0_449, List.forall_mem_cons.2 ⟨subd9_0_450, List.forall_mem_cons.2 ⟨subd9_0_451, List.forall_mem_cons.2 ⟨subd9_0_452, List.forall_mem_cons.2 ⟨subd9_0_453, List.forall_mem_cons.2 ⟨subd9_0_454, List.forall_mem_cons.2 ⟨subd9_0_455, List.forall_mem_cons.2 ⟨subd9_0_456, List.forall_mem_cons.2 ⟨subd9_0_457, List.forall_mem_cons.2 ⟨subd9_0_458, List.forall_mem_cons.2 ⟨subd9_0_459, List.forall_mem_cons.2 ⟨subd9_0_460, List.forall_mem_cons.2 ⟨subd9_0_461, List.forall_mem_cons.2 ⟨subd9_0_462, List.forall_mem_cons.2 ⟨subd9_0_463, List.forall_mem_cons.2 ⟨subd9_0_464, List.forall_mem_cons.2 ⟨subd9_0_465, List.forall_mem_cons.2 ⟨subd9_0_466, List.forall_mem_cons.2 ⟨subd9_0_467, List.forall_mem_cons.2 ⟨subd9_0_468, List.forall_mem_cons.2 ⟨subd9_0_469, List.forall_mem_cons.2 ⟨subd9_0_470, List.forall_mem_cons.2 ⟨subd9_0_471, List.forall_mem_cons.2 ⟨subd9_0_472, List.forall_mem_cons.2 ⟨subd9_0_473, List.forall_mem_cons.2 ⟨subd9_0_474, List.forall_mem_cons.2 ⟨subd9_0_475, List.forall_mem_cons.2 ⟨subd9_0_476, List.forall_mem_cons.2 ⟨subd9_0_477, List.forall_mem_cons.2 ⟨subd9_0_478, List.forall_mem_cons.2 ⟨subd9_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
