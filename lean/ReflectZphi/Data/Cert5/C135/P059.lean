import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_1_32 : subd10_1 [-3, 1, -2] = true := by decide +kernel
theorem subd10_1_33 : subd10_1 [-3, 1, -1] = true := by decide +kernel
theorem subd10_1_34 : subd10_1 [-3, 1, 0] = true := by decide +kernel
theorem subd10_1_35 : subd10_1 [-3, 1, 1] = true := by decide +kernel
theorem subd10_1_36 : subd10_1 [-3, 1, 2] = true := by decide +kernel
theorem subd10_1_37 : subd10_1 [-3, 1, 3] = true := by decide +kernel
theorem subd10_1_38 : subd10_1 [-3, 1, 4] = true := by decide +kernel
theorem subd10_1_39 : subd10_1 [-3, 1, 5] = true := by decide +kernel
theorem subd10_1_40 : subd10_1 [-3, 1, 6] = true := by decide +kernel
theorem subd10_1_41 : subd10_1 [-3, 1, 7] = true := by decide +kernel
theorem subd10_1_42 : subd10_1 [-3, 2, -7] = true := by decide +kernel
theorem subd10_1_43 : subd10_1 [-3, 2, -6] = true := by decide +kernel
theorem subd10_1_44 : subd10_1 [-3, 2, -5] = true := by decide +kernel
theorem subd10_1_45 : subd10_1 [-3, 2, -4] = true := by decide +kernel
theorem subd10_1_46 : subd10_1 [-3, 2, -3] = true := by decide +kernel
theorem subd10_1_47 : subd10_1 [-3, 2, -2] = true := by decide +kernel
theorem subd10_1_48 : subd10_1 [-3, 2, -1] = true := by decide +kernel
theorem subd10_1_49 : subd10_1 [-3, 2, 0] = true := by decide +kernel
theorem subd10_1_50 : subd10_1 [-3, 2, 1] = true := by decide +kernel
theorem subd10_1_51 : subd10_1 [-3, 2, 2] = true := by decide +kernel
theorem subd10_1_52 : subd10_1 [-3, 2, 3] = true := by decide +kernel
theorem subd10_1_53 : subd10_1 [-3, 2, 4] = true := by decide +kernel
theorem subd10_1_54 : subd10_1 [-3, 2, 5] = true := by decide +kernel
theorem subd10_1_55 : subd10_1 [-3, 2, 6] = true := by decide +kernel
theorem subd10_1_56 : subd10_1 [-3, 2, 7] = true := by decide +kernel
theorem subd10_1_57 : subd10_1 [-3, 3, -6] = true := by decide +kernel
theorem subd10_1_58 : subd10_1 [-3, 3, -5] = true := by decide +kernel
theorem subd10_1_59 : subd10_1 [-3, 3, -4] = true := by decide +kernel
theorem subd10_1_60 : subd10_1 [-3, 3, -3] = true := by decide +kernel
theorem subd10_1_61 : subd10_1 [-3, 3, -2] = true := by decide +kernel
theorem subd10_1_62 : subd10_1 [-3, 3, -1] = true := by decide +kernel
theorem subd10_1_63 : subd10_1 [-3, 3, 0] = true := by decide +kernel
theorem sbd10_1_1 : ∀ q ∈ blkd10_1_1, subd10_1 q = true := by
  unfold blkd10_1_1
  exact List.forall_mem_cons.2 ⟨subd10_1_32, List.forall_mem_cons.2 ⟨subd10_1_33, List.forall_mem_cons.2 ⟨subd10_1_34, List.forall_mem_cons.2 ⟨subd10_1_35, List.forall_mem_cons.2 ⟨subd10_1_36, List.forall_mem_cons.2 ⟨subd10_1_37, List.forall_mem_cons.2 ⟨subd10_1_38, List.forall_mem_cons.2 ⟨subd10_1_39, List.forall_mem_cons.2 ⟨subd10_1_40, List.forall_mem_cons.2 ⟨subd10_1_41, List.forall_mem_cons.2 ⟨subd10_1_42, List.forall_mem_cons.2 ⟨subd10_1_43, List.forall_mem_cons.2 ⟨subd10_1_44, List.forall_mem_cons.2 ⟨subd10_1_45, List.forall_mem_cons.2 ⟨subd10_1_46, List.forall_mem_cons.2 ⟨subd10_1_47, List.forall_mem_cons.2 ⟨subd10_1_48, List.forall_mem_cons.2 ⟨subd10_1_49, List.forall_mem_cons.2 ⟨subd10_1_50, List.forall_mem_cons.2 ⟨subd10_1_51, List.forall_mem_cons.2 ⟨subd10_1_52, List.forall_mem_cons.2 ⟨subd10_1_53, List.forall_mem_cons.2 ⟨subd10_1_54, List.forall_mem_cons.2 ⟨subd10_1_55, List.forall_mem_cons.2 ⟨subd10_1_56, List.forall_mem_cons.2 ⟨subd10_1_57, List.forall_mem_cons.2 ⟨subd10_1_58, List.forall_mem_cons.2 ⟨subd10_1_59, List.forall_mem_cons.2 ⟨subd10_1_60, List.forall_mem_cons.2 ⟨subd10_1_61, List.forall_mem_cons.2 ⟨subd10_1_62, List.forall_mem_cons.2 ⟨subd10_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_64 : subd10_1 [-3, 3, 1] = true := by decide +kernel
theorem subd10_1_65 : subd10_1 [-3, 3, 2] = true := by decide +kernel
theorem subd10_1_66 : subd10_1 [-3, 3, 3] = true := by decide +kernel
theorem subd10_1_67 : subd10_1 [-3, 3, 4] = true := by decide +kernel
theorem subd10_1_68 : subd10_1 [-3, 3, 5] = true := by decide +kernel
theorem subd10_1_69 : subd10_1 [-3, 3, 6] = true := by decide +kernel
theorem subd10_1_70 : subd10_1 [-3, 4] = true := by decide +kernel
theorem subd10_1_71 : subd10_1 [-3, 5] = true := by decide +kernel
theorem subd10_1_72 : subd10_1 [-2, -5] = true := by decide +kernel
theorem subd10_1_73 : subd10_1 [-2, -4] = true := by decide +kernel
theorem subd10_1_74 : subd10_1 [-2, -3] = true := by decide +kernel
theorem subd10_1_75 : subd10_1 [-2, -2, -6] = true := by decide +kernel
theorem subd10_1_76 : subd10_1 [-2, -2, -5] = true := by decide +kernel
theorem subd10_1_77 : subd10_1 [-2, -2, -4] = true := by decide +kernel
theorem subd10_1_78 : subd10_1 [-2, -2, -3] = true := by decide +kernel
theorem subd10_1_79 : subd10_1 [-2, -2, -2] = true := by decide +kernel
theorem subd10_1_80 : subd10_1 [-2, -2, -1] = true := by decide +kernel
theorem subd10_1_81 : subd10_1 [-2, -2, 0] = true := by decide +kernel
theorem subd10_1_82 : subd10_1 [-2, -2, 1] = true := by decide +kernel
theorem subd10_1_83 : subd10_1 [-2, -2, 2] = true := by decide +kernel
theorem subd10_1_84 : subd10_1 [-2, -2, 3] = true := by decide +kernel
theorem subd10_1_85 : subd10_1 [-2, -2, 4] = true := by decide +kernel
theorem subd10_1_86 : subd10_1 [-2, -2, 5] = true := by decide +kernel
theorem subd10_1_87 : subd10_1 [-2, -2, 6] = true := by decide +kernel
theorem subd10_1_88 : subd10_1 [-2, -2, 7] = true := by decide +kernel
theorem subd10_1_89 : subd10_1 [-2, -1, -7] = true := by decide +kernel
theorem subd10_1_90 : subd10_1 [-2, -1, -6] = true := by decide +kernel
theorem subd10_1_91 : subd10_1 [-2, -1, -5] = true := by decide +kernel
theorem subd10_1_92 : subd10_1 [-2, -1, -4] = true := by decide +kernel
theorem subd10_1_93 : subd10_1 [-2, -1, -3] = true := by decide +kernel
theorem subd10_1_94 : subd10_1 [-2, -1, -2] = true := by decide +kernel
theorem subd10_1_95 : subd10_1 [-2, -1, -1] = true := by decide +kernel
theorem sbd10_1_2 : ∀ q ∈ blkd10_1_2, subd10_1 q = true := by
  unfold blkd10_1_2
  exact List.forall_mem_cons.2 ⟨subd10_1_64, List.forall_mem_cons.2 ⟨subd10_1_65, List.forall_mem_cons.2 ⟨subd10_1_66, List.forall_mem_cons.2 ⟨subd10_1_67, List.forall_mem_cons.2 ⟨subd10_1_68, List.forall_mem_cons.2 ⟨subd10_1_69, List.forall_mem_cons.2 ⟨subd10_1_70, List.forall_mem_cons.2 ⟨subd10_1_71, List.forall_mem_cons.2 ⟨subd10_1_72, List.forall_mem_cons.2 ⟨subd10_1_73, List.forall_mem_cons.2 ⟨subd10_1_74, List.forall_mem_cons.2 ⟨subd10_1_75, List.forall_mem_cons.2 ⟨subd10_1_76, List.forall_mem_cons.2 ⟨subd10_1_77, List.forall_mem_cons.2 ⟨subd10_1_78, List.forall_mem_cons.2 ⟨subd10_1_79, List.forall_mem_cons.2 ⟨subd10_1_80, List.forall_mem_cons.2 ⟨subd10_1_81, List.forall_mem_cons.2 ⟨subd10_1_82, List.forall_mem_cons.2 ⟨subd10_1_83, List.forall_mem_cons.2 ⟨subd10_1_84, List.forall_mem_cons.2 ⟨subd10_1_85, List.forall_mem_cons.2 ⟨subd10_1_86, List.forall_mem_cons.2 ⟨subd10_1_87, List.forall_mem_cons.2 ⟨subd10_1_88, List.forall_mem_cons.2 ⟨subd10_1_89, List.forall_mem_cons.2 ⟨subd10_1_90, List.forall_mem_cons.2 ⟨subd10_1_91, List.forall_mem_cons.2 ⟨subd10_1_92, List.forall_mem_cons.2 ⟨subd10_1_93, List.forall_mem_cons.2 ⟨subd10_1_94, List.forall_mem_cons.2 ⟨subd10_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_96 : subd10_1 [-2, -1, 0] = true := by decide +kernel
theorem subd10_1_97 : subd10_1 [-2, -1, 1] = true := by decide +kernel
theorem subd10_1_98 : subd10_1 [-2, -1, 2] = true := by decide +kernel
theorem subd10_1_99 : subd10_1 [-2, -1, 3] = true := by decide +kernel
theorem subd10_1_100 : subd10_1 [-2, -1, 4] = true := by decide +kernel
theorem subd10_1_101 : subd10_1 [-2, -1, 5] = true := by decide +kernel
theorem subd10_1_102 : subd10_1 [-2, -1, 6] = true := by decide +kernel
theorem subd10_1_103 : subd10_1 [-2, -1, 7] = true := by decide +kernel
theorem subd10_1_104 : subd10_1 [-2, -1, 8] = true := by decide +kernel
theorem subd10_1_105 : subd10_1 [-2, 0, -7] = true := by decide +kernel
theorem subd10_1_106 : subd10_1 [-2, 0, -6] = true := by decide +kernel
theorem subd10_1_107 : subd10_1 [-2, 0, -5] = true := by decide +kernel
theorem subd10_1_108 : subd10_1 [-2, 0, -4] = true := by decide +kernel
theorem subd10_1_109 : subd10_1 [-2, 0, -3] = true := by decide +kernel
theorem subd10_1_110 : subd10_1 [-2, 0, -2] = true := by decide +kernel
theorem subd10_1_111 : subd10_1 [-2, 0, -1] = true := by decide +kernel
theorem subd10_1_112 : subd10_1 [-2, 0, 0] = true := by decide +kernel
theorem subd10_1_113 : subd10_1 [-2, 0, 1] = true := by decide +kernel
theorem subd10_1_114 : subd10_1 [-2, 0, 2] = true := by decide +kernel
theorem subd10_1_115 : subd10_1 [-2, 0, 3] = true := by decide +kernel
theorem subd10_1_116 : subd10_1 [-2, 0, 4] = true := by decide +kernel
theorem subd10_1_117 : subd10_1 [-2, 0, 5] = true := by decide +kernel
theorem subd10_1_118 : subd10_1 [-2, 0, 6] = true := by decide +kernel
theorem subd10_1_119 : subd10_1 [-2, 0, 7] = true := by decide +kernel
theorem subd10_1_120 : subd10_1 [-2, 0, 8] = true := by decide +kernel
theorem subd10_1_121 : subd10_1 [-2, 1, -8] = true := by decide +kernel
theorem subd10_1_122 : subd10_1 [-2, 1, -7] = true := by decide +kernel
theorem subd10_1_123 : subd10_1 [-2, 1, -6] = true := by decide +kernel
theorem subd10_1_124 : subd10_1 [-2, 1, -5] = true := by decide +kernel
theorem subd10_1_125 : subd10_1 [-2, 1, -4] = true := by decide +kernel
theorem subd10_1_126 : subd10_1 [-2, 1, -3] = true := by decide +kernel
theorem subd10_1_127 : subd10_1 [-2, 1, -2] = true := by decide +kernel
theorem sbd10_1_3 : ∀ q ∈ blkd10_1_3, subd10_1 q = true := by
  unfold blkd10_1_3
  exact List.forall_mem_cons.2 ⟨subd10_1_96, List.forall_mem_cons.2 ⟨subd10_1_97, List.forall_mem_cons.2 ⟨subd10_1_98, List.forall_mem_cons.2 ⟨subd10_1_99, List.forall_mem_cons.2 ⟨subd10_1_100, List.forall_mem_cons.2 ⟨subd10_1_101, List.forall_mem_cons.2 ⟨subd10_1_102, List.forall_mem_cons.2 ⟨subd10_1_103, List.forall_mem_cons.2 ⟨subd10_1_104, List.forall_mem_cons.2 ⟨subd10_1_105, List.forall_mem_cons.2 ⟨subd10_1_106, List.forall_mem_cons.2 ⟨subd10_1_107, List.forall_mem_cons.2 ⟨subd10_1_108, List.forall_mem_cons.2 ⟨subd10_1_109, List.forall_mem_cons.2 ⟨subd10_1_110, List.forall_mem_cons.2 ⟨subd10_1_111, List.forall_mem_cons.2 ⟨subd10_1_112, List.forall_mem_cons.2 ⟨subd10_1_113, List.forall_mem_cons.2 ⟨subd10_1_114, List.forall_mem_cons.2 ⟨subd10_1_115, List.forall_mem_cons.2 ⟨subd10_1_116, List.forall_mem_cons.2 ⟨subd10_1_117, List.forall_mem_cons.2 ⟨subd10_1_118, List.forall_mem_cons.2 ⟨subd10_1_119, List.forall_mem_cons.2 ⟨subd10_1_120, List.forall_mem_cons.2 ⟨subd10_1_121, List.forall_mem_cons.2 ⟨subd10_1_122, List.forall_mem_cons.2 ⟨subd10_1_123, List.forall_mem_cons.2 ⟨subd10_1_124, List.forall_mem_cons.2 ⟨subd10_1_125, List.forall_mem_cons.2 ⟨subd10_1_126, List.forall_mem_cons.2 ⟨subd10_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_128 : subd10_1 [-2, 1, -1] = true := by decide +kernel
theorem subd10_1_129 : subd10_1 [-2, 1, 0] = true := by decide +kernel
theorem subd10_1_130 : subd10_1 [-2, 1, 1] = true := by decide +kernel
theorem subd10_1_131 : subd10_1 [-2, 1, 2] = true := by decide +kernel
theorem subd10_1_132 : subd10_1 [-2, 1, 3] = true := by decide +kernel
theorem subd10_1_133 : subd10_1 [-2, 1, 4] = true := by decide +kernel
theorem subd10_1_134 : subd10_1 [-2, 1, 5] = true := by decide +kernel
theorem subd10_1_135 : subd10_1 [-2, 1, 6] = true := by decide +kernel
theorem subd10_1_136 : subd10_1 [-2, 1, 7] = true := by decide +kernel
theorem subd10_1_137 : subd10_1 [-2, 1, 8] = true := by decide +kernel
theorem subd10_1_138 : subd10_1 [-2, 2, -8] = true := by decide +kernel
theorem subd10_1_139 : subd10_1 [-2, 2, -7] = true := by decide +kernel
theorem subd10_1_140 : subd10_1 [-2, 2, -6] = true := by decide +kernel
theorem subd10_1_141 : subd10_1 [-2, 2, -5] = true := by decide +kernel
theorem subd10_1_142 : subd10_1 [-2, 2, -4] = true := by decide +kernel
theorem subd10_1_143 : subd10_1 [-2, 2, -3] = true := by decide +kernel
theorem subd10_1_144 : subd10_1 [-2, 2, -2] = true := by decide +kernel
theorem subd10_1_145 : subd10_1 [-2, 2, -1] = true := by decide +kernel
theorem subd10_1_146 : subd10_1 [-2, 2, 0] = true := by decide +kernel
theorem subd10_1_147 : subd10_1 [-2, 2, 1] = true := by decide +kernel
theorem subd10_1_148 : subd10_1 [-2, 2, 2] = true := by decide +kernel
theorem subd10_1_149 : subd10_1 [-2, 2, 3] = true := by decide +kernel
theorem subd10_1_150 : subd10_1 [-2, 2, 4] = true := by decide +kernel
theorem subd10_1_151 : subd10_1 [-2, 2, 5] = true := by decide +kernel
theorem subd10_1_152 : subd10_1 [-2, 2, 6] = true := by decide +kernel
theorem subd10_1_153 : subd10_1 [-2, 2, 7] = true := by decide +kernel
theorem subd10_1_154 : subd10_1 [-2, 3, -7] = true := by decide +kernel
theorem subd10_1_155 : subd10_1 [-2, 3, -6] = true := by decide +kernel
theorem subd10_1_156 : subd10_1 [-2, 3, -5] = true := by decide +kernel
theorem subd10_1_157 : subd10_1 [-2, 3, -4] = true := by decide +kernel
theorem subd10_1_158 : subd10_1 [-2, 3, -3] = true := by decide +kernel
theorem subd10_1_159 : subd10_1 [-2, 3, -2] = true := by decide +kernel
theorem sbd10_1_4 : ∀ q ∈ blkd10_1_4, subd10_1 q = true := by
  unfold blkd10_1_4
  exact List.forall_mem_cons.2 ⟨subd10_1_128, List.forall_mem_cons.2 ⟨subd10_1_129, List.forall_mem_cons.2 ⟨subd10_1_130, List.forall_mem_cons.2 ⟨subd10_1_131, List.forall_mem_cons.2 ⟨subd10_1_132, List.forall_mem_cons.2 ⟨subd10_1_133, List.forall_mem_cons.2 ⟨subd10_1_134, List.forall_mem_cons.2 ⟨subd10_1_135, List.forall_mem_cons.2 ⟨subd10_1_136, List.forall_mem_cons.2 ⟨subd10_1_137, List.forall_mem_cons.2 ⟨subd10_1_138, List.forall_mem_cons.2 ⟨subd10_1_139, List.forall_mem_cons.2 ⟨subd10_1_140, List.forall_mem_cons.2 ⟨subd10_1_141, List.forall_mem_cons.2 ⟨subd10_1_142, List.forall_mem_cons.2 ⟨subd10_1_143, List.forall_mem_cons.2 ⟨subd10_1_144, List.forall_mem_cons.2 ⟨subd10_1_145, List.forall_mem_cons.2 ⟨subd10_1_146, List.forall_mem_cons.2 ⟨subd10_1_147, List.forall_mem_cons.2 ⟨subd10_1_148, List.forall_mem_cons.2 ⟨subd10_1_149, List.forall_mem_cons.2 ⟨subd10_1_150, List.forall_mem_cons.2 ⟨subd10_1_151, List.forall_mem_cons.2 ⟨subd10_1_152, List.forall_mem_cons.2 ⟨subd10_1_153, List.forall_mem_cons.2 ⟨subd10_1_154, List.forall_mem_cons.2 ⟨subd10_1_155, List.forall_mem_cons.2 ⟨subd10_1_156, List.forall_mem_cons.2 ⟨subd10_1_157, List.forall_mem_cons.2 ⟨subd10_1_158, List.forall_mem_cons.2 ⟨subd10_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_160 : subd10_1 [-2, 3, -1] = true := by decide +kernel
theorem subd10_1_161 : subd10_1 [-2, 3, 0] = true := by decide +kernel
theorem subd10_1_162 : subd10_1 [-2, 3, 1] = true := by decide +kernel
theorem subd10_1_163 : subd10_1 [-2, 3, 2] = true := by decide +kernel
theorem subd10_1_164 : subd10_1 [-2, 3, 3] = true := by decide +kernel
theorem subd10_1_165 : subd10_1 [-2, 3, 4] = true := by decide +kernel
theorem subd10_1_166 : subd10_1 [-2, 3, 5] = true := by decide +kernel
theorem subd10_1_167 : subd10_1 [-2, 3, 6] = true := by decide +kernel
theorem subd10_1_168 : subd10_1 [-2, 4, -7] = true := by decide +kernel
theorem subd10_1_169 : subd10_1 [-2, 4, -6] = true := by decide +kernel
theorem subd10_1_170 : subd10_1 [-2, 4, -5] = true := by decide +kernel
theorem subd10_1_171 : subd10_1 [-2, 4, -4] = true := by decide +kernel
theorem subd10_1_172 : subd10_1 [-2, 4, -3] = true := by decide +kernel
theorem subd10_1_173 : subd10_1 [-2, 4, -2] = true := by decide +kernel
theorem subd10_1_174 : subd10_1 [-2, 4, -1] = true := by decide +kernel
theorem subd10_1_175 : subd10_1 [-2, 4, 0] = true := by decide +kernel
theorem subd10_1_176 : subd10_1 [-2, 4, 1] = true := by decide +kernel
theorem subd10_1_177 : subd10_1 [-2, 4, 2] = true := by decide +kernel
theorem subd10_1_178 : subd10_1 [-2, 4, 3] = true := by decide +kernel
theorem subd10_1_179 : subd10_1 [-2, 4, 4] = true := by decide +kernel
theorem subd10_1_180 : subd10_1 [-2, 4, 5] = true := by decide +kernel
theorem subd10_1_181 : subd10_1 [-2, 5] = true := by decide +kernel
theorem subd10_1_182 : subd10_1 [-2, 6] = true := by decide +kernel
theorem subd10_1_183 : subd10_1 [-1, -6] = true := by decide +kernel
theorem subd10_1_184 : subd10_1 [-1, -5] = true := by decide +kernel
theorem subd10_1_185 : subd10_1 [-1, -4] = true := by decide +kernel
theorem subd10_1_186 : subd10_1 [-1, -3, -6] = true := by decide +kernel
theorem subd10_1_187 : subd10_1 [-1, -3, -5] = true := by decide +kernel
theorem subd10_1_188 : subd10_1 [-1, -3, -4] = true := by decide +kernel
theorem subd10_1_189 : subd10_1 [-1, -3, -3] = true := by decide +kernel
theorem subd10_1_190 : subd10_1 [-1, -3, -2] = true := by decide +kernel
theorem subd10_1_191 : subd10_1 [-1, -3, -1] = true := by decide +kernel
theorem sbd10_1_5 : ∀ q ∈ blkd10_1_5, subd10_1 q = true := by
  unfold blkd10_1_5
  exact List.forall_mem_cons.2 ⟨subd10_1_160, List.forall_mem_cons.2 ⟨subd10_1_161, List.forall_mem_cons.2 ⟨subd10_1_162, List.forall_mem_cons.2 ⟨subd10_1_163, List.forall_mem_cons.2 ⟨subd10_1_164, List.forall_mem_cons.2 ⟨subd10_1_165, List.forall_mem_cons.2 ⟨subd10_1_166, List.forall_mem_cons.2 ⟨subd10_1_167, List.forall_mem_cons.2 ⟨subd10_1_168, List.forall_mem_cons.2 ⟨subd10_1_169, List.forall_mem_cons.2 ⟨subd10_1_170, List.forall_mem_cons.2 ⟨subd10_1_171, List.forall_mem_cons.2 ⟨subd10_1_172, List.forall_mem_cons.2 ⟨subd10_1_173, List.forall_mem_cons.2 ⟨subd10_1_174, List.forall_mem_cons.2 ⟨subd10_1_175, List.forall_mem_cons.2 ⟨subd10_1_176, List.forall_mem_cons.2 ⟨subd10_1_177, List.forall_mem_cons.2 ⟨subd10_1_178, List.forall_mem_cons.2 ⟨subd10_1_179, List.forall_mem_cons.2 ⟨subd10_1_180, List.forall_mem_cons.2 ⟨subd10_1_181, List.forall_mem_cons.2 ⟨subd10_1_182, List.forall_mem_cons.2 ⟨subd10_1_183, List.forall_mem_cons.2 ⟨subd10_1_184, List.forall_mem_cons.2 ⟨subd10_1_185, List.forall_mem_cons.2 ⟨subd10_1_186, List.forall_mem_cons.2 ⟨subd10_1_187, List.forall_mem_cons.2 ⟨subd10_1_188, List.forall_mem_cons.2 ⟨subd10_1_189, List.forall_mem_cons.2 ⟨subd10_1_190, List.forall_mem_cons.2 ⟨subd10_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_192 : subd10_1 [-1, -3, 0] = true := by decide +kernel
theorem subd10_1_193 : subd10_1 [-1, -3, 1] = true := by decide +kernel
theorem subd10_1_194 : subd10_1 [-1, -3, 2] = true := by decide +kernel
theorem subd10_1_195 : subd10_1 [-1, -3, 3] = true := by decide +kernel
theorem subd10_1_196 : subd10_1 [-1, -3, 4] = true := by decide +kernel
theorem subd10_1_197 : subd10_1 [-1, -3, 5] = true := by decide +kernel
theorem subd10_1_198 : subd10_1 [-1, -3, 6] = true := by decide +kernel
theorem subd10_1_199 : subd10_1 [-1, -3, 7] = true := by decide +kernel
theorem subd10_1_200 : subd10_1 [-1, -2, -7] = true := by decide +kernel
theorem subd10_1_201 : subd10_1 [-1, -2, -6] = true := by decide +kernel
theorem subd10_1_202 : subd10_1 [-1, -2, -5] = true := by decide +kernel
theorem subd10_1_203 : subd10_1 [-1, -2, -4] = true := by decide +kernel
theorem subd10_1_204 : subd10_1 [-1, -2, -3] = true := by decide +kernel
theorem subd10_1_205 : subd10_1 [-1, -2, -2] = true := by decide +kernel
theorem subd10_1_206 : subd10_1 [-1, -2, -1] = true := by decide +kernel
theorem subd10_1_207 : subd10_1 [-1, -2, 0] = true := by decide +kernel
theorem subd10_1_208 : subd10_1 [-1, -2, 1] = true := by decide +kernel
theorem subd10_1_209 : subd10_1 [-1, -2, 2] = true := by decide +kernel
theorem subd10_1_210 : subd10_1 [-1, -2, 3] = true := by decide +kernel
theorem subd10_1_211 : subd10_1 [-1, -2, 4] = true := by decide +kernel
theorem subd10_1_212 : subd10_1 [-1, -2, 5] = true := by decide +kernel
theorem subd10_1_213 : subd10_1 [-1, -2, 6] = true := by decide +kernel
theorem subd10_1_214 : subd10_1 [-1, -2, 7] = true := by decide +kernel
theorem subd10_1_215 : subd10_1 [-1, -2, 8] = true := by decide +kernel
theorem subd10_1_216 : subd10_1 [-1, -1, -8] = true := by decide +kernel
theorem subd10_1_217 : subd10_1 [-1, -1, -7] = true := by decide +kernel
theorem subd10_1_218 : subd10_1 [-1, -1, -6] = true := by decide +kernel
theorem subd10_1_219 : subd10_1 [-1, -1, -5] = true := by decide +kernel
theorem subd10_1_220 : subd10_1 [-1, -1, -4] = true := by decide +kernel
theorem subd10_1_221 : subd10_1 [-1, -1, -3] = true := by decide +kernel
theorem subd10_1_222 : subd10_1 [-1, -1, -2] = true := by decide +kernel
theorem subd10_1_223 : subd10_1 [-1, -1, -1] = true := by decide +kernel
theorem sbd10_1_6 : ∀ q ∈ blkd10_1_6, subd10_1 q = true := by
  unfold blkd10_1_6
  exact List.forall_mem_cons.2 ⟨subd10_1_192, List.forall_mem_cons.2 ⟨subd10_1_193, List.forall_mem_cons.2 ⟨subd10_1_194, List.forall_mem_cons.2 ⟨subd10_1_195, List.forall_mem_cons.2 ⟨subd10_1_196, List.forall_mem_cons.2 ⟨subd10_1_197, List.forall_mem_cons.2 ⟨subd10_1_198, List.forall_mem_cons.2 ⟨subd10_1_199, List.forall_mem_cons.2 ⟨subd10_1_200, List.forall_mem_cons.2 ⟨subd10_1_201, List.forall_mem_cons.2 ⟨subd10_1_202, List.forall_mem_cons.2 ⟨subd10_1_203, List.forall_mem_cons.2 ⟨subd10_1_204, List.forall_mem_cons.2 ⟨subd10_1_205, List.forall_mem_cons.2 ⟨subd10_1_206, List.forall_mem_cons.2 ⟨subd10_1_207, List.forall_mem_cons.2 ⟨subd10_1_208, List.forall_mem_cons.2 ⟨subd10_1_209, List.forall_mem_cons.2 ⟨subd10_1_210, List.forall_mem_cons.2 ⟨subd10_1_211, List.forall_mem_cons.2 ⟨subd10_1_212, List.forall_mem_cons.2 ⟨subd10_1_213, List.forall_mem_cons.2 ⟨subd10_1_214, List.forall_mem_cons.2 ⟨subd10_1_215, List.forall_mem_cons.2 ⟨subd10_1_216, List.forall_mem_cons.2 ⟨subd10_1_217, List.forall_mem_cons.2 ⟨subd10_1_218, List.forall_mem_cons.2 ⟨subd10_1_219, List.forall_mem_cons.2 ⟨subd10_1_220, List.forall_mem_cons.2 ⟨subd10_1_221, List.forall_mem_cons.2 ⟨subd10_1_222, List.forall_mem_cons.2 ⟨subd10_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_224 : subd10_1 [-1, -1, 0] = true := by decide +kernel
theorem subd10_1_225 : subd10_1 [-1, -1, 1] = true := by decide +kernel
theorem subd10_1_226 : subd10_1 [-1, -1, 2] = true := by decide +kernel
theorem subd10_1_227 : subd10_1 [-1, -1, 3] = true := by decide +kernel
theorem subd10_1_228 : subd10_1 [-1, -1, 4] = true := by decide +kernel
theorem subd10_1_229 : subd10_1 [-1, -1, 5] = true := by decide +kernel
theorem subd10_1_230 : subd10_1 [-1, -1, 6] = true := by decide +kernel
theorem subd10_1_231 : subd10_1 [-1, -1, 7] = true := by decide +kernel
theorem subd10_1_232 : subd10_1 [-1, -1, 8] = true := by decide +kernel
theorem subd10_1_233 : subd10_1 [-1, 0, -8] = true := by decide +kernel
theorem subd10_1_234 : subd10_1 [-1, 0, -7] = true := by decide +kernel
theorem subd10_1_235 : subd10_1 [-1, 0, -6] = true := by decide +kernel
theorem subd10_1_236 : subd10_1 [-1, 0, -5] = true := by decide +kernel
theorem subd10_1_237 : subd10_1 [-1, 0, -4] = true := by decide +kernel
theorem subd10_1_238 : subd10_1 [-1, 0, -3] = true := by decide +kernel
theorem subd10_1_239 : subd10_1 [-1, 0, -2] = true := by decide +kernel
theorem subd10_1_240 : subd10_1 [-1, 0, -1] = true := by decide +kernel
theorem subd10_1_241 : subd10_1 [-1, 0, 0] = true := by decide +kernel
theorem subd10_1_242 : subd10_1 [-1, 0, 1] = true := by decide +kernel
theorem subd10_1_243 : subd10_1 [-1, 0, 2] = true := by decide +kernel
theorem subd10_1_244 : subd10_1 [-1, 0, 3] = true := by decide +kernel
theorem subd10_1_245 : subd10_1 [-1, 0, 4] = true := by decide +kernel
theorem subd10_1_246 : subd10_1 [-1, 0, 5] = true := by decide +kernel
theorem subd10_1_247 : subd10_1 [-1, 0, 6] = true := by decide +kernel
theorem subd10_1_248 : subd10_1 [-1, 0, 7] = true := by decide +kernel
theorem subd10_1_249 : subd10_1 [-1, 0, 8] = true := by decide +kernel
theorem subd10_1_250 : subd10_1 [-1, 1, -8] = true := by decide +kernel
theorem subd10_1_251 : subd10_1 [-1, 1, -7] = true := by decide +kernel
theorem subd10_1_252 : subd10_1 [-1, 1, -6] = true := by decide +kernel
theorem subd10_1_253 : subd10_1 [-1, 1, -5] = true := by decide +kernel
theorem subd10_1_254 : subd10_1 [-1, 1, -4] = true := by decide +kernel
theorem subd10_1_255 : subd10_1 [-1, 1, -3] = true := by decide +kernel
theorem sbd10_1_7 : ∀ q ∈ blkd10_1_7, subd10_1 q = true := by
  unfold blkd10_1_7
  exact List.forall_mem_cons.2 ⟨subd10_1_224, List.forall_mem_cons.2 ⟨subd10_1_225, List.forall_mem_cons.2 ⟨subd10_1_226, List.forall_mem_cons.2 ⟨subd10_1_227, List.forall_mem_cons.2 ⟨subd10_1_228, List.forall_mem_cons.2 ⟨subd10_1_229, List.forall_mem_cons.2 ⟨subd10_1_230, List.forall_mem_cons.2 ⟨subd10_1_231, List.forall_mem_cons.2 ⟨subd10_1_232, List.forall_mem_cons.2 ⟨subd10_1_233, List.forall_mem_cons.2 ⟨subd10_1_234, List.forall_mem_cons.2 ⟨subd10_1_235, List.forall_mem_cons.2 ⟨subd10_1_236, List.forall_mem_cons.2 ⟨subd10_1_237, List.forall_mem_cons.2 ⟨subd10_1_238, List.forall_mem_cons.2 ⟨subd10_1_239, List.forall_mem_cons.2 ⟨subd10_1_240, List.forall_mem_cons.2 ⟨subd10_1_241, List.forall_mem_cons.2 ⟨subd10_1_242, List.forall_mem_cons.2 ⟨subd10_1_243, List.forall_mem_cons.2 ⟨subd10_1_244, List.forall_mem_cons.2 ⟨subd10_1_245, List.forall_mem_cons.2 ⟨subd10_1_246, List.forall_mem_cons.2 ⟨subd10_1_247, List.forall_mem_cons.2 ⟨subd10_1_248, List.forall_mem_cons.2 ⟨subd10_1_249, List.forall_mem_cons.2 ⟨subd10_1_250, List.forall_mem_cons.2 ⟨subd10_1_251, List.forall_mem_cons.2 ⟨subd10_1_252, List.forall_mem_cons.2 ⟨subd10_1_253, List.forall_mem_cons.2 ⟨subd10_1_254, List.forall_mem_cons.2 ⟨subd10_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_256 : subd10_1 [-1, 1, -2] = true := by decide +kernel
theorem subd10_1_257 : subd10_1 [-1, 1, -1] = true := by decide +kernel
theorem subd10_1_258 : subd10_1 [-1, 1, 0] = true := by decide +kernel
theorem subd10_1_259 : subd10_1 [-1, 1, 1] = true := by decide +kernel
theorem subd10_1_260 : subd10_1 [-1, 1, 2] = true := by decide +kernel
theorem subd10_1_261 : subd10_1 [-1, 1, 3] = true := by decide +kernel
theorem subd10_1_262 : subd10_1 [-1, 1, 4] = true := by decide +kernel
theorem subd10_1_263 : subd10_1 [-1, 1, 5] = true := by decide +kernel
theorem subd10_1_264 : subd10_1 [-1, 1, 6] = true := by decide +kernel
theorem subd10_1_265 : subd10_1 [-1, 1, 7] = true := by decide +kernel
theorem subd10_1_266 : subd10_1 [-1, 1, 8] = true := by decide +kernel
theorem subd10_1_267 : subd10_1 [-1, 2, -8] = true := by decide +kernel
theorem subd10_1_268 : subd10_1 [-1, 2, -7] = true := by decide +kernel
theorem subd10_1_269 : subd10_1 [-1, 2, -6] = true := by decide +kernel
theorem subd10_1_270 : subd10_1 [-1, 2, -5] = true := by decide +kernel
theorem subd10_1_271 : subd10_1 [-1, 2, -4] = true := by decide +kernel
theorem subd10_1_272 : subd10_1 [-1, 2, -3] = true := by decide +kernel
theorem subd10_1_273 : subd10_1 [-1, 2, -2] = true := by decide +kernel
theorem subd10_1_274 : subd10_1 [-1, 2, -1] = true := by decide +kernel
theorem subd10_1_275 : subd10_1 [-1, 2, 0] = true := by decide +kernel
theorem subd10_1_276 : subd10_1 [-1, 2, 1] = true := by decide +kernel
theorem subd10_1_277 : subd10_1 [-1, 2, 2] = true := by decide +kernel
theorem subd10_1_278 : subd10_1 [-1, 2, 3] = true := by decide +kernel
theorem subd10_1_279 : subd10_1 [-1, 2, 4] = true := by decide +kernel
theorem subd10_1_280 : subd10_1 [-1, 2, 5] = true := by decide +kernel
theorem subd10_1_281 : subd10_1 [-1, 2, 6] = true := by decide +kernel
theorem subd10_1_282 : subd10_1 [-1, 2, 7] = true := by decide +kernel
theorem subd10_1_283 : subd10_1 [-1, 3, -8] = true := by decide +kernel
theorem subd10_1_284 : subd10_1 [-1, 3, -7] = true := by decide +kernel
theorem subd10_1_285 : subd10_1 [-1, 3, -6] = true := by decide +kernel
theorem subd10_1_286 : subd10_1 [-1, 3, -5] = true := by decide +kernel
theorem subd10_1_287 : subd10_1 [-1, 3, -4] = true := by decide +kernel
theorem sbd10_1_8 : ∀ q ∈ blkd10_1_8, subd10_1 q = true := by
  unfold blkd10_1_8
  exact List.forall_mem_cons.2 ⟨subd10_1_256, List.forall_mem_cons.2 ⟨subd10_1_257, List.forall_mem_cons.2 ⟨subd10_1_258, List.forall_mem_cons.2 ⟨subd10_1_259, List.forall_mem_cons.2 ⟨subd10_1_260, List.forall_mem_cons.2 ⟨subd10_1_261, List.forall_mem_cons.2 ⟨subd10_1_262, List.forall_mem_cons.2 ⟨subd10_1_263, List.forall_mem_cons.2 ⟨subd10_1_264, List.forall_mem_cons.2 ⟨subd10_1_265, List.forall_mem_cons.2 ⟨subd10_1_266, List.forall_mem_cons.2 ⟨subd10_1_267, List.forall_mem_cons.2 ⟨subd10_1_268, List.forall_mem_cons.2 ⟨subd10_1_269, List.forall_mem_cons.2 ⟨subd10_1_270, List.forall_mem_cons.2 ⟨subd10_1_271, List.forall_mem_cons.2 ⟨subd10_1_272, List.forall_mem_cons.2 ⟨subd10_1_273, List.forall_mem_cons.2 ⟨subd10_1_274, List.forall_mem_cons.2 ⟨subd10_1_275, List.forall_mem_cons.2 ⟨subd10_1_276, List.forall_mem_cons.2 ⟨subd10_1_277, List.forall_mem_cons.2 ⟨subd10_1_278, List.forall_mem_cons.2 ⟨subd10_1_279, List.forall_mem_cons.2 ⟨subd10_1_280, List.forall_mem_cons.2 ⟨subd10_1_281, List.forall_mem_cons.2 ⟨subd10_1_282, List.forall_mem_cons.2 ⟨subd10_1_283, List.forall_mem_cons.2 ⟨subd10_1_284, List.forall_mem_cons.2 ⟨subd10_1_285, List.forall_mem_cons.2 ⟨subd10_1_286, List.forall_mem_cons.2 ⟨subd10_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_288 : subd10_1 [-1, 3, -3] = true := by decide +kernel
theorem subd10_1_289 : subd10_1 [-1, 3, -2] = true := by decide +kernel
theorem subd10_1_290 : subd10_1 [-1, 3, -1] = true := by decide +kernel
theorem subd10_1_291 : subd10_1 [-1, 3, 0] = true := by decide +kernel
theorem subd10_1_292 : subd10_1 [-1, 3, 1] = true := by decide +kernel
theorem subd10_1_293 : subd10_1 [-1, 3, 2] = true := by decide +kernel
theorem subd10_1_294 : subd10_1 [-1, 3, 3] = true := by decide +kernel
theorem subd10_1_295 : subd10_1 [-1, 3, 4] = true := by decide +kernel
theorem subd10_1_296 : subd10_1 [-1, 3, 5] = true := by decide +kernel
theorem subd10_1_297 : subd10_1 [-1, 3, 6] = true := by decide +kernel
theorem subd10_1_298 : subd10_1 [-1, 4, -8] = true := by decide +kernel
theorem subd10_1_299 : subd10_1 [-1, 4, -7] = true := by decide +kernel
theorem subd10_1_300 : subd10_1 [-1, 4, -6] = true := by decide +kernel
theorem subd10_1_301 : subd10_1 [-1, 4, -5] = true := by decide +kernel
theorem subd10_1_302 : subd10_1 [-1, 4, -4] = true := by decide +kernel
theorem subd10_1_303 : subd10_1 [-1, 4, -3] = true := by decide +kernel
theorem subd10_1_304 : subd10_1 [-1, 4, -2] = true := by decide +kernel
theorem subd10_1_305 : subd10_1 [-1, 4, -1] = true := by decide +kernel
theorem subd10_1_306 : subd10_1 [-1, 4, 0] = true := by decide +kernel
theorem subd10_1_307 : subd10_1 [-1, 4, 1] = true := by decide +kernel
theorem subd10_1_308 : subd10_1 [-1, 4, 2] = true := by decide +kernel
theorem subd10_1_309 : subd10_1 [-1, 4, 3] = true := by decide +kernel
theorem subd10_1_310 : subd10_1 [-1, 4, 4] = true := by decide +kernel
theorem subd10_1_311 : subd10_1 [-1, 4, 5] = true := by decide +kernel
theorem subd10_1_312 : subd10_1 [-1, 5] = true := by decide +kernel
theorem subd10_1_313 : subd10_1 [-1, 6] = true := by decide +kernel
theorem subd10_1_314 : subd10_1 [0, -6] = true := by decide +kernel
theorem subd10_1_315 : subd10_1 [0, -5] = true := by decide +kernel
theorem subd10_1_316 : subd10_1 [0, -4] = true := by decide +kernel
theorem subd10_1_317 : subd10_1 [0, -3, -7] = true := by decide +kernel
theorem subd10_1_318 : subd10_1 [0, -3, -6] = true := by decide +kernel
theorem subd10_1_319 : subd10_1 [0, -3, -5] = true := by decide +kernel
theorem sbd10_1_9 : ∀ q ∈ blkd10_1_9, subd10_1 q = true := by
  unfold blkd10_1_9
  exact List.forall_mem_cons.2 ⟨subd10_1_288, List.forall_mem_cons.2 ⟨subd10_1_289, List.forall_mem_cons.2 ⟨subd10_1_290, List.forall_mem_cons.2 ⟨subd10_1_291, List.forall_mem_cons.2 ⟨subd10_1_292, List.forall_mem_cons.2 ⟨subd10_1_293, List.forall_mem_cons.2 ⟨subd10_1_294, List.forall_mem_cons.2 ⟨subd10_1_295, List.forall_mem_cons.2 ⟨subd10_1_296, List.forall_mem_cons.2 ⟨subd10_1_297, List.forall_mem_cons.2 ⟨subd10_1_298, List.forall_mem_cons.2 ⟨subd10_1_299, List.forall_mem_cons.2 ⟨subd10_1_300, List.forall_mem_cons.2 ⟨subd10_1_301, List.forall_mem_cons.2 ⟨subd10_1_302, List.forall_mem_cons.2 ⟨subd10_1_303, List.forall_mem_cons.2 ⟨subd10_1_304, List.forall_mem_cons.2 ⟨subd10_1_305, List.forall_mem_cons.2 ⟨subd10_1_306, List.forall_mem_cons.2 ⟨subd10_1_307, List.forall_mem_cons.2 ⟨subd10_1_308, List.forall_mem_cons.2 ⟨subd10_1_309, List.forall_mem_cons.2 ⟨subd10_1_310, List.forall_mem_cons.2 ⟨subd10_1_311, List.forall_mem_cons.2 ⟨subd10_1_312, List.forall_mem_cons.2 ⟨subd10_1_313, List.forall_mem_cons.2 ⟨subd10_1_314, List.forall_mem_cons.2 ⟨subd10_1_315, List.forall_mem_cons.2 ⟨subd10_1_316, List.forall_mem_cons.2 ⟨subd10_1_317, List.forall_mem_cons.2 ⟨subd10_1_318, List.forall_mem_cons.2 ⟨subd10_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_320 : subd10_1 [0, -3, -4] = true := by decide +kernel
theorem subd10_1_321 : subd10_1 [0, -3, -3] = true := by decide +kernel
theorem subd10_1_322 : subd10_1 [0, -3, -2] = true := by decide +kernel
theorem subd10_1_323 : subd10_1 [0, -3, -1] = true := by decide +kernel
theorem subd10_1_324 : subd10_1 [0, -3, 0] = true := by decide +kernel
theorem subd10_1_325 : subd10_1 [0, -3, 1] = true := by decide +kernel
theorem subd10_1_326 : subd10_1 [0, -3, 2] = true := by decide +kernel
theorem subd10_1_327 : subd10_1 [0, -3, 3] = true := by decide +kernel
theorem subd10_1_328 : subd10_1 [0, -3, 4] = true := by decide +kernel
theorem subd10_1_329 : subd10_1 [0, -3, 5] = true := by decide +kernel
theorem subd10_1_330 : subd10_1 [0, -3, 6] = true := by decide +kernel
theorem subd10_1_331 : subd10_1 [0, -3, 7] = true := by decide +kernel
theorem subd10_1_332 : subd10_1 [0, -2, -8] = true := by decide +kernel
theorem subd10_1_333 : subd10_1 [0, -2, -7] = true := by decide +kernel
theorem subd10_1_334 : subd10_1 [0, -2, -6] = true := by decide +kernel
theorem subd10_1_335 : subd10_1 [0, -2, -5] = true := by decide +kernel
theorem subd10_1_336 : subd10_1 [0, -2, -4] = true := by decide +kernel
theorem subd10_1_337 : subd10_1 [0, -2, -3] = true := by decide +kernel
theorem subd10_1_338 : subd10_1 [0, -2, -2] = true := by decide +kernel
theorem subd10_1_339 : subd10_1 [0, -2, -1] = true := by decide +kernel
theorem subd10_1_340 : subd10_1 [0, -2, 0] = true := by decide +kernel
theorem subd10_1_341 : subd10_1 [0, -2, 1] = true := by decide +kernel
theorem subd10_1_342 : subd10_1 [0, -2, 2] = true := by decide +kernel
theorem subd10_1_343 : subd10_1 [0, -2, 3] = true := by decide +kernel
theorem subd10_1_344 : subd10_1 [0, -2, 4] = true := by decide +kernel
theorem subd10_1_345 : subd10_1 [0, -2, 5] = true := by decide +kernel
theorem subd10_1_346 : subd10_1 [0, -2, 6] = true := by decide +kernel
theorem subd10_1_347 : subd10_1 [0, -2, 7] = true := by decide +kernel
theorem subd10_1_348 : subd10_1 [0, -2, 8] = true := by decide +kernel
theorem subd10_1_349 : subd10_1 [0, -1, -8] = true := by decide +kernel
theorem subd10_1_350 : subd10_1 [0, -1, -7] = true := by decide +kernel
theorem subd10_1_351 : subd10_1 [0, -1, -6] = true := by decide +kernel
theorem sbd10_1_10 : ∀ q ∈ blkd10_1_10, subd10_1 q = true := by
  unfold blkd10_1_10
  exact List.forall_mem_cons.2 ⟨subd10_1_320, List.forall_mem_cons.2 ⟨subd10_1_321, List.forall_mem_cons.2 ⟨subd10_1_322, List.forall_mem_cons.2 ⟨subd10_1_323, List.forall_mem_cons.2 ⟨subd10_1_324, List.forall_mem_cons.2 ⟨subd10_1_325, List.forall_mem_cons.2 ⟨subd10_1_326, List.forall_mem_cons.2 ⟨subd10_1_327, List.forall_mem_cons.2 ⟨subd10_1_328, List.forall_mem_cons.2 ⟨subd10_1_329, List.forall_mem_cons.2 ⟨subd10_1_330, List.forall_mem_cons.2 ⟨subd10_1_331, List.forall_mem_cons.2 ⟨subd10_1_332, List.forall_mem_cons.2 ⟨subd10_1_333, List.forall_mem_cons.2 ⟨subd10_1_334, List.forall_mem_cons.2 ⟨subd10_1_335, List.forall_mem_cons.2 ⟨subd10_1_336, List.forall_mem_cons.2 ⟨subd10_1_337, List.forall_mem_cons.2 ⟨subd10_1_338, List.forall_mem_cons.2 ⟨subd10_1_339, List.forall_mem_cons.2 ⟨subd10_1_340, List.forall_mem_cons.2 ⟨subd10_1_341, List.forall_mem_cons.2 ⟨subd10_1_342, List.forall_mem_cons.2 ⟨subd10_1_343, List.forall_mem_cons.2 ⟨subd10_1_344, List.forall_mem_cons.2 ⟨subd10_1_345, List.forall_mem_cons.2 ⟨subd10_1_346, List.forall_mem_cons.2 ⟨subd10_1_347, List.forall_mem_cons.2 ⟨subd10_1_348, List.forall_mem_cons.2 ⟨subd10_1_349, List.forall_mem_cons.2 ⟨subd10_1_350, List.forall_mem_cons.2 ⟨subd10_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_352 : subd10_1 [0, -1, -5] = true := by decide +kernel
theorem subd10_1_353 : subd10_1 [0, -1, -4] = true := by decide +kernel
theorem subd10_1_354 : subd10_1 [0, -1, -3] = true := by decide +kernel
theorem subd10_1_355 : subd10_1 [0, -1, -2] = true := by decide +kernel
theorem subd10_1_356 : subd10_1 [0, -1, -1] = true := by decide +kernel
theorem subd10_1_357 : subd10_1 [0, -1, 0] = true := by decide +kernel
theorem subd10_1_358 : subd10_1 [0, -1, 1] = true := by decide +kernel
theorem subd10_1_359 : subd10_1 [0, -1, 2] = true := by decide +kernel
theorem subd10_1_360 : subd10_1 [0, -1, 3] = true := by decide +kernel
theorem subd10_1_361 : subd10_1 [0, -1, 4] = true := by decide +kernel
theorem subd10_1_362 : subd10_1 [0, -1, 5] = true := by decide +kernel
theorem subd10_1_363 : subd10_1 [0, -1, 6] = true := by decide +kernel
theorem subd10_1_364 : subd10_1 [0, -1, 7] = true := by decide +kernel
theorem subd10_1_365 : subd10_1 [0, -1, 8] = true := by decide +kernel
theorem subd10_1_366 : subd10_1 [0, 0, -9] = true := by decide +kernel
theorem subd10_1_367 : subd10_1 [0, 0, -8] = true := by decide +kernel
theorem subd10_1_368 : subd10_1 [0, 0, -7] = true := by decide +kernel
theorem subd10_1_369 : subd10_1 [0, 0, -6] = true := by decide +kernel
theorem subd10_1_370 : subd10_1 [0, 0, -5] = true := by decide +kernel
theorem subd10_1_371 : subd10_1 [0, 0, -4] = true := by decide +kernel
theorem subd10_1_372 : subd10_1 [0, 0, -3] = true := by decide +kernel
theorem subd10_1_373 : subd10_1 [0, 0, -2] = true := by decide +kernel
theorem subd10_1_374 : subd10_1 [0, 0, -1] = true := by decide +kernel
theorem subd10_1_375 : subd10_1 [0, 0, 0] = true := by decide +kernel
theorem subd10_1_376 : subd10_1 [0, 0, 1] = true := by decide +kernel
theorem subd10_1_377 : subd10_1 [0, 0, 2] = true := by decide +kernel
theorem subd10_1_378 : subd10_1 [0, 0, 3] = true := by decide +kernel
theorem subd10_1_379 : subd10_1 [0, 0, 4] = true := by decide +kernel
theorem subd10_1_380 : subd10_1 [0, 0, 5] = true := by decide +kernel
theorem subd10_1_381 : subd10_1 [0, 0, 6] = true := by decide +kernel
theorem subd10_1_382 : subd10_1 [0, 0, 7] = true := by decide +kernel
theorem subd10_1_383 : subd10_1 [0, 0, 8] = true := by decide +kernel
theorem sbd10_1_11 : ∀ q ∈ blkd10_1_11, subd10_1 q = true := by
  unfold blkd10_1_11
  exact List.forall_mem_cons.2 ⟨subd10_1_352, List.forall_mem_cons.2 ⟨subd10_1_353, List.forall_mem_cons.2 ⟨subd10_1_354, List.forall_mem_cons.2 ⟨subd10_1_355, List.forall_mem_cons.2 ⟨subd10_1_356, List.forall_mem_cons.2 ⟨subd10_1_357, List.forall_mem_cons.2 ⟨subd10_1_358, List.forall_mem_cons.2 ⟨subd10_1_359, List.forall_mem_cons.2 ⟨subd10_1_360, List.forall_mem_cons.2 ⟨subd10_1_361, List.forall_mem_cons.2 ⟨subd10_1_362, List.forall_mem_cons.2 ⟨subd10_1_363, List.forall_mem_cons.2 ⟨subd10_1_364, List.forall_mem_cons.2 ⟨subd10_1_365, List.forall_mem_cons.2 ⟨subd10_1_366, List.forall_mem_cons.2 ⟨subd10_1_367, List.forall_mem_cons.2 ⟨subd10_1_368, List.forall_mem_cons.2 ⟨subd10_1_369, List.forall_mem_cons.2 ⟨subd10_1_370, List.forall_mem_cons.2 ⟨subd10_1_371, List.forall_mem_cons.2 ⟨subd10_1_372, List.forall_mem_cons.2 ⟨subd10_1_373, List.forall_mem_cons.2 ⟨subd10_1_374, List.forall_mem_cons.2 ⟨subd10_1_375, List.forall_mem_cons.2 ⟨subd10_1_376, List.forall_mem_cons.2 ⟨subd10_1_377, List.forall_mem_cons.2 ⟨subd10_1_378, List.forall_mem_cons.2 ⟨subd10_1_379, List.forall_mem_cons.2 ⟨subd10_1_380, List.forall_mem_cons.2 ⟨subd10_1_381, List.forall_mem_cons.2 ⟨subd10_1_382, List.forall_mem_cons.2 ⟨subd10_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_384 : subd10_1 [0, 1, -9] = true := by decide +kernel
theorem subd10_1_385 : subd10_1 [0, 1, -8] = true := by decide +kernel
theorem subd10_1_386 : subd10_1 [0, 1, -7] = true := by decide +kernel
theorem subd10_1_387 : subd10_1 [0, 1, -6] = true := by decide +kernel
theorem subd10_1_388 : subd10_1 [0, 1, -5] = true := by decide +kernel
theorem subd10_1_389 : subd10_1 [0, 1, -4] = true := by decide +kernel
theorem subd10_1_390 : subd10_1 [0, 1, -3] = true := by decide +kernel
theorem subd10_1_391 : subd10_1 [0, 1, -2] = true := by decide +kernel
theorem subd10_1_392 : subd10_1 [0, 1, -1] = true := by decide +kernel
theorem subd10_1_393 : subd10_1 [0, 1, 0] = true := by decide +kernel
theorem subd10_1_394 : subd10_1 [0, 1, 1] = true := by decide +kernel
theorem subd10_1_395 : subd10_1 [0, 1, 2] = true := by decide +kernel
theorem subd10_1_396 : subd10_1 [0, 1, 3] = true := by decide +kernel
theorem subd10_1_397 : subd10_1 [0, 1, 4] = true := by decide +kernel
theorem subd10_1_398 : subd10_1 [0, 1, 5] = true := by decide +kernel
theorem subd10_1_399 : subd10_1 [0, 1, 6] = true := by decide +kernel
theorem subd10_1_400 : subd10_1 [0, 1, 7] = true := by decide +kernel
theorem subd10_1_401 : subd10_1 [0, 2, -9] = true := by decide +kernel
theorem subd10_1_402 : subd10_1 [0, 2, -8] = true := by decide +kernel
theorem subd10_1_403 : subd10_1 [0, 2, -7] = true := by decide +kernel
theorem subd10_1_404 : subd10_1 [0, 2, -6] = true := by decide +kernel
theorem subd10_1_405 : subd10_1 [0, 2, -5] = true := by decide +kernel
theorem subd10_1_406 : subd10_1 [0, 2, -4] = true := by decide +kernel
theorem subd10_1_407 : subd10_1 [0, 2, -3] = true := by decide +kernel
theorem subd10_1_408 : subd10_1 [0, 2, -2] = true := by decide +kernel
theorem subd10_1_409 : subd10_1 [0, 2, -1] = true := by decide +kernel
theorem subd10_1_410 : subd10_1 [0, 2, 0] = true := by decide +kernel
theorem subd10_1_411 : subd10_1 [0, 2, 1] = true := by decide +kernel
theorem subd10_1_412 : subd10_1 [0, 2, 2] = true := by decide +kernel
theorem subd10_1_413 : subd10_1 [0, 2, 3] = true := by decide +kernel
theorem subd10_1_414 : subd10_1 [0, 2, 4] = true := by decide +kernel
theorem subd10_1_415 : subd10_1 [0, 2, 5] = true := by decide +kernel
theorem sbd10_1_12 : ∀ q ∈ blkd10_1_12, subd10_1 q = true := by
  unfold blkd10_1_12
  exact List.forall_mem_cons.2 ⟨subd10_1_384, List.forall_mem_cons.2 ⟨subd10_1_385, List.forall_mem_cons.2 ⟨subd10_1_386, List.forall_mem_cons.2 ⟨subd10_1_387, List.forall_mem_cons.2 ⟨subd10_1_388, List.forall_mem_cons.2 ⟨subd10_1_389, List.forall_mem_cons.2 ⟨subd10_1_390, List.forall_mem_cons.2 ⟨subd10_1_391, List.forall_mem_cons.2 ⟨subd10_1_392, List.forall_mem_cons.2 ⟨subd10_1_393, List.forall_mem_cons.2 ⟨subd10_1_394, List.forall_mem_cons.2 ⟨subd10_1_395, List.forall_mem_cons.2 ⟨subd10_1_396, List.forall_mem_cons.2 ⟨subd10_1_397, List.forall_mem_cons.2 ⟨subd10_1_398, List.forall_mem_cons.2 ⟨subd10_1_399, List.forall_mem_cons.2 ⟨subd10_1_400, List.forall_mem_cons.2 ⟨subd10_1_401, List.forall_mem_cons.2 ⟨subd10_1_402, List.forall_mem_cons.2 ⟨subd10_1_403, List.forall_mem_cons.2 ⟨subd10_1_404, List.forall_mem_cons.2 ⟨subd10_1_405, List.forall_mem_cons.2 ⟨subd10_1_406, List.forall_mem_cons.2 ⟨subd10_1_407, List.forall_mem_cons.2 ⟨subd10_1_408, List.forall_mem_cons.2 ⟨subd10_1_409, List.forall_mem_cons.2 ⟨subd10_1_410, List.forall_mem_cons.2 ⟨subd10_1_411, List.forall_mem_cons.2 ⟨subd10_1_412, List.forall_mem_cons.2 ⟨subd10_1_413, List.forall_mem_cons.2 ⟨subd10_1_414, List.forall_mem_cons.2 ⟨subd10_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_416 : subd10_1 [0, 2, 6] = true := by decide +kernel
theorem subd10_1_417 : subd10_1 [0, 2, 7] = true := by decide +kernel
theorem subd10_1_418 : subd10_1 [0, 3, -8] = true := by decide +kernel
theorem subd10_1_419 : subd10_1 [0, 3, -7] = true := by decide +kernel
theorem subd10_1_420 : subd10_1 [0, 3, -6] = true := by decide +kernel
theorem subd10_1_421 : subd10_1 [0, 3, -5] = true := by decide +kernel
theorem subd10_1_422 : subd10_1 [0, 3, -4] = true := by decide +kernel
theorem subd10_1_423 : subd10_1 [0, 3, -3] = true := by decide +kernel
theorem subd10_1_424 : subd10_1 [0, 3, -2] = true := by decide +kernel
theorem subd10_1_425 : subd10_1 [0, 3, -1] = true := by decide +kernel
theorem subd10_1_426 : subd10_1 [0, 3, 0] = true := by decide +kernel
theorem subd10_1_427 : subd10_1 [0, 3, 1] = true := by decide +kernel
theorem subd10_1_428 : subd10_1 [0, 3, 2] = true := by decide +kernel
theorem subd10_1_429 : subd10_1 [0, 3, 3] = true := by decide +kernel
theorem subd10_1_430 : subd10_1 [0, 3, 4] = true := by decide +kernel
theorem subd10_1_431 : subd10_1 [0, 3, 5] = true := by decide +kernel
theorem subd10_1_432 : subd10_1 [0, 3, 6] = true := by decide +kernel
theorem subd10_1_433 : subd10_1 [0, 4] = true := by decide +kernel
theorem subd10_1_434 : subd10_1 [0, 5] = true := by decide +kernel
theorem subd10_1_435 : subd10_1 [1, -7] = true := by decide +kernel
theorem subd10_1_436 : subd10_1 [1, -6] = true := by decide +kernel
theorem subd10_1_437 : subd10_1 [1, -5] = true := by decide +kernel
theorem subd10_1_438 : subd10_1 [1, -4, -6] = true := by decide +kernel
theorem subd10_1_439 : subd10_1 [1, -4, -5] = true := by decide +kernel
theorem subd10_1_440 : subd10_1 [1, -4, -4] = true := by decide +kernel
theorem subd10_1_441 : subd10_1 [1, -4, -3] = true := by decide +kernel
theorem subd10_1_442 : subd10_1 [1, -4, -2] = true := by decide +kernel
theorem subd10_1_443 : subd10_1 [1, -4, -1] = true := by decide +kernel
theorem subd10_1_444 : subd10_1 [1, -4, 0] = true := by decide +kernel
theorem subd10_1_445 : subd10_1 [1, -4, 1] = true := by decide +kernel
theorem subd10_1_446 : subd10_1 [1, -4, 2] = true := by decide +kernel
theorem subd10_1_447 : subd10_1 [1, -4, 3] = true := by decide +kernel
theorem sbd10_1_13 : ∀ q ∈ blkd10_1_13, subd10_1 q = true := by
  unfold blkd10_1_13
  exact List.forall_mem_cons.2 ⟨subd10_1_416, List.forall_mem_cons.2 ⟨subd10_1_417, List.forall_mem_cons.2 ⟨subd10_1_418, List.forall_mem_cons.2 ⟨subd10_1_419, List.forall_mem_cons.2 ⟨subd10_1_420, List.forall_mem_cons.2 ⟨subd10_1_421, List.forall_mem_cons.2 ⟨subd10_1_422, List.forall_mem_cons.2 ⟨subd10_1_423, List.forall_mem_cons.2 ⟨subd10_1_424, List.forall_mem_cons.2 ⟨subd10_1_425, List.forall_mem_cons.2 ⟨subd10_1_426, List.forall_mem_cons.2 ⟨subd10_1_427, List.forall_mem_cons.2 ⟨subd10_1_428, List.forall_mem_cons.2 ⟨subd10_1_429, List.forall_mem_cons.2 ⟨subd10_1_430, List.forall_mem_cons.2 ⟨subd10_1_431, List.forall_mem_cons.2 ⟨subd10_1_432, List.forall_mem_cons.2 ⟨subd10_1_433, List.forall_mem_cons.2 ⟨subd10_1_434, List.forall_mem_cons.2 ⟨subd10_1_435, List.forall_mem_cons.2 ⟨subd10_1_436, List.forall_mem_cons.2 ⟨subd10_1_437, List.forall_mem_cons.2 ⟨subd10_1_438, List.forall_mem_cons.2 ⟨subd10_1_439, List.forall_mem_cons.2 ⟨subd10_1_440, List.forall_mem_cons.2 ⟨subd10_1_441, List.forall_mem_cons.2 ⟨subd10_1_442, List.forall_mem_cons.2 ⟨subd10_1_443, List.forall_mem_cons.2 ⟨subd10_1_444, List.forall_mem_cons.2 ⟨subd10_1_445, List.forall_mem_cons.2 ⟨subd10_1_446, List.forall_mem_cons.2 ⟨subd10_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_448 : subd10_1 [1, -4, 4] = true := by decide +kernel
theorem subd10_1_449 : subd10_1 [1, -4, 5] = true := by decide +kernel
theorem subd10_1_450 : subd10_1 [1, -4, 6] = true := by decide +kernel
theorem subd10_1_451 : subd10_1 [1, -4, 7] = true := by decide +kernel
theorem subd10_1_452 : subd10_1 [1, -3, -7] = true := by decide +kernel
theorem subd10_1_453 : subd10_1 [1, -3, -6] = true := by decide +kernel
theorem subd10_1_454 : subd10_1 [1, -3, -5] = true := by decide +kernel
theorem subd10_1_455 : subd10_1 [1, -3, -4] = true := by decide +kernel
theorem subd10_1_456 : subd10_1 [1, -3, -3] = true := by decide +kernel
theorem subd10_1_457 : subd10_1 [1, -3, -2] = true := by decide +kernel
theorem subd10_1_458 : subd10_1 [1, -3, -1] = true := by decide +kernel
theorem subd10_1_459 : subd10_1 [1, -3, 0] = true := by decide +kernel
theorem subd10_1_460 : subd10_1 [1, -3, 1] = true := by decide +kernel
theorem subd10_1_461 : subd10_1 [1, -3, 2] = true := by decide +kernel
theorem subd10_1_462 : subd10_1 [1, -3, 3] = true := by decide +kernel
theorem subd10_1_463 : subd10_1 [1, -3, 4] = true := by decide +kernel
theorem subd10_1_464 : subd10_1 [1, -3, 5] = true := by decide +kernel
theorem subd10_1_465 : subd10_1 [1, -3, 6] = true := by decide +kernel
theorem subd10_1_466 : subd10_1 [1, -3, 7] = true := by decide +kernel
theorem subd10_1_467 : subd10_1 [1, -2, -8] = true := by decide +kernel
theorem subd10_1_468 : subd10_1 [1, -2, -7] = true := by decide +kernel
theorem subd10_1_469 : subd10_1 [1, -2, -6] = true := by decide +kernel
theorem subd10_1_470 : subd10_1 [1, -2, -5] = true := by decide +kernel
theorem subd10_1_471 : subd10_1 [1, -2, -4] = true := by decide +kernel
theorem subd10_1_472 : subd10_1 [1, -2, -3] = true := by decide +kernel
theorem subd10_1_473 : subd10_1 [1, -2, -2] = true := by decide +kernel
theorem subd10_1_474 : subd10_1 [1, -2, -1] = true := by decide +kernel
theorem subd10_1_475 : subd10_1 [1, -2, 0] = true := by decide +kernel
theorem subd10_1_476 : subd10_1 [1, -2, 1] = true := by decide +kernel
theorem subd10_1_477 : subd10_1 [1, -2, 2] = true := by decide +kernel
theorem subd10_1_478 : subd10_1 [1, -2, 3] = true := by decide +kernel
theorem subd10_1_479 : subd10_1 [1, -2, 4] = true := by decide +kernel
theorem sbd10_1_14 : ∀ q ∈ blkd10_1_14, subd10_1 q = true := by
  unfold blkd10_1_14
  exact List.forall_mem_cons.2 ⟨subd10_1_448, List.forall_mem_cons.2 ⟨subd10_1_449, List.forall_mem_cons.2 ⟨subd10_1_450, List.forall_mem_cons.2 ⟨subd10_1_451, List.forall_mem_cons.2 ⟨subd10_1_452, List.forall_mem_cons.2 ⟨subd10_1_453, List.forall_mem_cons.2 ⟨subd10_1_454, List.forall_mem_cons.2 ⟨subd10_1_455, List.forall_mem_cons.2 ⟨subd10_1_456, List.forall_mem_cons.2 ⟨subd10_1_457, List.forall_mem_cons.2 ⟨subd10_1_458, List.forall_mem_cons.2 ⟨subd10_1_459, List.forall_mem_cons.2 ⟨subd10_1_460, List.forall_mem_cons.2 ⟨subd10_1_461, List.forall_mem_cons.2 ⟨subd10_1_462, List.forall_mem_cons.2 ⟨subd10_1_463, List.forall_mem_cons.2 ⟨subd10_1_464, List.forall_mem_cons.2 ⟨subd10_1_465, List.forall_mem_cons.2 ⟨subd10_1_466, List.forall_mem_cons.2 ⟨subd10_1_467, List.forall_mem_cons.2 ⟨subd10_1_468, List.forall_mem_cons.2 ⟨subd10_1_469, List.forall_mem_cons.2 ⟨subd10_1_470, List.forall_mem_cons.2 ⟨subd10_1_471, List.forall_mem_cons.2 ⟨subd10_1_472, List.forall_mem_cons.2 ⟨subd10_1_473, List.forall_mem_cons.2 ⟨subd10_1_474, List.forall_mem_cons.2 ⟨subd10_1_475, List.forall_mem_cons.2 ⟨subd10_1_476, List.forall_mem_cons.2 ⟨subd10_1_477, List.forall_mem_cons.2 ⟨subd10_1_478, List.forall_mem_cons.2 ⟨subd10_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_480 : subd10_1 [1, -2, 5] = true := by decide +kernel
theorem subd10_1_481 : subd10_1 [1, -2, 6] = true := by decide +kernel
theorem subd10_1_482 : subd10_1 [1, -2, 7] = true := by decide +kernel
theorem subd10_1_483 : subd10_1 [1, -1, -9] = true := by decide +kernel
theorem subd10_1_484 : subd10_1 [1, -1, -8] = true := by decide +kernel
theorem subd10_1_485 : subd10_1 [1, -1, -7] = true := by decide +kernel
theorem subd10_1_486 : subd10_1 [1, -1, -6] = true := by decide +kernel
theorem subd10_1_487 : subd10_1 [1, -1, -5] = true := by decide +kernel
theorem subd10_1_488 : subd10_1 [1, -1, -4] = true := by decide +kernel
theorem subd10_1_489 : subd10_1 [1, -1, -3] = true := by decide +kernel
theorem subd10_1_490 : subd10_1 [1, -1, -2] = true := by decide +kernel
theorem subd10_1_491 : subd10_1 [1, -1, -1] = true := by decide +kernel
theorem subd10_1_492 : subd10_1 [1, -1, 0] = true := by decide +kernel
theorem subd10_1_493 : subd10_1 [1, -1, 1] = true := by decide +kernel
theorem subd10_1_494 : subd10_1 [1, -1, 2] = true := by decide +kernel
theorem subd10_1_495 : subd10_1 [1, -1, 3] = true := by decide +kernel
theorem subd10_1_496 : subd10_1 [1, -1, 4] = true := by decide +kernel
theorem subd10_1_497 : subd10_1 [1, -1, 5] = true := by decide +kernel
theorem subd10_1_498 : subd10_1 [1, -1, 6] = true := by decide +kernel
theorem subd10_1_499 : subd10_1 [1, -1, 7] = true := by decide +kernel
theorem subd10_1_500 : subd10_1 [1, 0, -9] = true := by decide +kernel
theorem subd10_1_501 : subd10_1 [1, 0, -8] = true := by decide +kernel
theorem subd10_1_502 : subd10_1 [1, 0, -7] = true := by decide +kernel
theorem subd10_1_503 : subd10_1 [1, 0, -6] = true := by decide +kernel
theorem subd10_1_504 : subd10_1 [1, 0, -5] = true := by decide +kernel
theorem subd10_1_505 : subd10_1 [1, 0, -4] = true := by decide +kernel
theorem subd10_1_506 : subd10_1 [1, 0, -3] = true := by decide +kernel
theorem subd10_1_507 : subd10_1 [1, 0, -2] = true := by decide +kernel
theorem subd10_1_508 : subd10_1 [1, 0, -1] = true := by decide +kernel
theorem subd10_1_509 : subd10_1 [1, 0, 0] = true := by decide +kernel
theorem subd10_1_510 : subd10_1 [1, 0, 1] = true := by decide +kernel
theorem subd10_1_511 : subd10_1 [1, 0, 2] = true := by decide +kernel
theorem sbd10_1_15 : ∀ q ∈ blkd10_1_15, subd10_1 q = true := by
  unfold blkd10_1_15
  exact List.forall_mem_cons.2 ⟨subd10_1_480, List.forall_mem_cons.2 ⟨subd10_1_481, List.forall_mem_cons.2 ⟨subd10_1_482, List.forall_mem_cons.2 ⟨subd10_1_483, List.forall_mem_cons.2 ⟨subd10_1_484, List.forall_mem_cons.2 ⟨subd10_1_485, List.forall_mem_cons.2 ⟨subd10_1_486, List.forall_mem_cons.2 ⟨subd10_1_487, List.forall_mem_cons.2 ⟨subd10_1_488, List.forall_mem_cons.2 ⟨subd10_1_489, List.forall_mem_cons.2 ⟨subd10_1_490, List.forall_mem_cons.2 ⟨subd10_1_491, List.forall_mem_cons.2 ⟨subd10_1_492, List.forall_mem_cons.2 ⟨subd10_1_493, List.forall_mem_cons.2 ⟨subd10_1_494, List.forall_mem_cons.2 ⟨subd10_1_495, List.forall_mem_cons.2 ⟨subd10_1_496, List.forall_mem_cons.2 ⟨subd10_1_497, List.forall_mem_cons.2 ⟨subd10_1_498, List.forall_mem_cons.2 ⟨subd10_1_499, List.forall_mem_cons.2 ⟨subd10_1_500, List.forall_mem_cons.2 ⟨subd10_1_501, List.forall_mem_cons.2 ⟨subd10_1_502, List.forall_mem_cons.2 ⟨subd10_1_503, List.forall_mem_cons.2 ⟨subd10_1_504, List.forall_mem_cons.2 ⟨subd10_1_505, List.forall_mem_cons.2 ⟨subd10_1_506, List.forall_mem_cons.2 ⟨subd10_1_507, List.forall_mem_cons.2 ⟨subd10_1_508, List.forall_mem_cons.2 ⟨subd10_1_509, List.forall_mem_cons.2 ⟨subd10_1_510, List.forall_mem_cons.2 ⟨subd10_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
