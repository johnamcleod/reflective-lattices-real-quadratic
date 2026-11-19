import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_9_64 : subd6_9 [-3, 0, 4] = true := by decide +kernel
theorem subd6_9_65 : subd6_9 [-3, 0, 5] = true := by decide +kernel
theorem subd6_9_66 : subd6_9 [-3, 1, -9] = true := by decide +kernel
theorem subd6_9_67 : subd6_9 [-3, 1, -8] = true := by decide +kernel
theorem subd6_9_68 : subd6_9 [-3, 1, -7] = true := by decide +kernel
theorem subd6_9_69 : subd6_9 [-3, 1, -6] = true := by decide +kernel
theorem subd6_9_70 : subd6_9 [-3, 1, -5] = true := by decide +kernel
theorem subd6_9_71 : subd6_9 [-3, 1, -4] = true := by decide +kernel
theorem subd6_9_72 : subd6_9 [-3, 1, -3] = true := by decide +kernel
theorem subd6_9_73 : subd6_9 [-3, 1, -2] = true := by decide +kernel
theorem subd6_9_74 : subd6_9 [-3, 1, -1] = true := by decide +kernel
theorem subd6_9_75 : subd6_9 [-3, 1, 0] = true := by decide +kernel
theorem subd6_9_76 : subd6_9 [-3, 1, 1] = true := by decide +kernel
theorem subd6_9_77 : subd6_9 [-3, 1, 2] = true := by decide +kernel
theorem subd6_9_78 : subd6_9 [-3, 1, 3] = true := by decide +kernel
theorem subd6_9_79 : subd6_9 [-3, 1, 4] = true := by decide +kernel
theorem subd6_9_80 : subd6_9 [-3, 1, 5] = true := by decide +kernel
theorem subd6_9_81 : subd6_9 [-3, 2, -9] = true := by decide +kernel
theorem subd6_9_82 : subd6_9 [-3, 2, -8] = true := by decide +kernel
theorem subd6_9_83 : subd6_9 [-3, 2, -7] = true := by decide +kernel
theorem subd6_9_84 : subd6_9 [-3, 2, -6] = true := by decide +kernel
theorem subd6_9_85 : subd6_9 [-3, 2, -5] = true := by decide +kernel
theorem subd6_9_86 : subd6_9 [-3, 2, -4] = true := by decide +kernel
theorem subd6_9_87 : subd6_9 [-3, 2, -3] = true := by decide +kernel
theorem subd6_9_88 : subd6_9 [-3, 2, -2] = true := by decide +kernel
theorem subd6_9_89 : subd6_9 [-3, 2, -1] = true := by decide +kernel
theorem subd6_9_90 : subd6_9 [-3, 2, 0] = true := by decide +kernel
theorem subd6_9_91 : subd6_9 [-3, 2, 1] = true := by decide +kernel
theorem subd6_9_92 : subd6_9 [-3, 2, 2] = true := by decide +kernel
theorem subd6_9_93 : subd6_9 [-3, 2, 3] = true := by decide +kernel
theorem subd6_9_94 : subd6_9 [-3, 2, 4] = true := by decide +kernel
theorem subd6_9_95 : subd6_9 [-3, 3] = true := by decide +kernel
theorem sbd6_9_2 : ∀ q ∈ blkd6_9_2, subd6_9 q = true := by
  unfold blkd6_9_2
  exact List.forall_mem_cons.2 ⟨subd6_9_64, List.forall_mem_cons.2 ⟨subd6_9_65, List.forall_mem_cons.2 ⟨subd6_9_66, List.forall_mem_cons.2 ⟨subd6_9_67, List.forall_mem_cons.2 ⟨subd6_9_68, List.forall_mem_cons.2 ⟨subd6_9_69, List.forall_mem_cons.2 ⟨subd6_9_70, List.forall_mem_cons.2 ⟨subd6_9_71, List.forall_mem_cons.2 ⟨subd6_9_72, List.forall_mem_cons.2 ⟨subd6_9_73, List.forall_mem_cons.2 ⟨subd6_9_74, List.forall_mem_cons.2 ⟨subd6_9_75, List.forall_mem_cons.2 ⟨subd6_9_76, List.forall_mem_cons.2 ⟨subd6_9_77, List.forall_mem_cons.2 ⟨subd6_9_78, List.forall_mem_cons.2 ⟨subd6_9_79, List.forall_mem_cons.2 ⟨subd6_9_80, List.forall_mem_cons.2 ⟨subd6_9_81, List.forall_mem_cons.2 ⟨subd6_9_82, List.forall_mem_cons.2 ⟨subd6_9_83, List.forall_mem_cons.2 ⟨subd6_9_84, List.forall_mem_cons.2 ⟨subd6_9_85, List.forall_mem_cons.2 ⟨subd6_9_86, List.forall_mem_cons.2 ⟨subd6_9_87, List.forall_mem_cons.2 ⟨subd6_9_88, List.forall_mem_cons.2 ⟨subd6_9_89, List.forall_mem_cons.2 ⟨subd6_9_90, List.forall_mem_cons.2 ⟨subd6_9_91, List.forall_mem_cons.2 ⟨subd6_9_92, List.forall_mem_cons.2 ⟨subd6_9_93, List.forall_mem_cons.2 ⟨subd6_9_94, List.forall_mem_cons.2 ⟨subd6_9_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_96 : subd6_9 [-3, 4] = true := by decide +kernel
theorem subd6_9_97 : subd6_9 [-3, 5] = true := by decide +kernel
theorem subd6_9_98 : subd6_9 [-2, -6] = true := by decide +kernel
theorem subd6_9_99 : subd6_9 [-2, -5] = true := by decide +kernel
theorem subd6_9_100 : subd6_9 [-2, -4] = true := by decide +kernel
theorem subd6_9_101 : subd6_9 [-2, -3, -7] = true := by decide +kernel
theorem subd6_9_102 : subd6_9 [-2, -3, -6] = true := by decide +kernel
theorem subd6_9_103 : subd6_9 [-2, -3, -5] = true := by decide +kernel
theorem subd6_9_104 : subd6_9 [-2, -3, -4] = true := by decide +kernel
theorem subd6_9_105 : subd6_9 [-2, -3, -3] = true := by decide +kernel
theorem subd6_9_106 : subd6_9 [-2, -3, -2] = true := by decide +kernel
theorem subd6_9_107 : subd6_9 [-2, -3, -1] = true := by decide +kernel
theorem subd6_9_108 : subd6_9 [-2, -3, 0] = true := by decide +kernel
theorem subd6_9_109 : subd6_9 [-2, -3, 1] = true := by decide +kernel
theorem subd6_9_110 : subd6_9 [-2, -3, 2] = true := by decide +kernel
theorem subd6_9_111 : subd6_9 [-2, -3, 3] = true := by decide +kernel
theorem subd6_9_112 : subd6_9 [-2, -3, 4] = true := by decide +kernel
theorem subd6_9_113 : subd6_9 [-2, -3, 5] = true := by decide +kernel
theorem subd6_9_114 : subd6_9 [-2, -3, 6] = true := by decide +kernel
theorem subd6_9_115 : subd6_9 [-2, -2, -8] = true := by decide +kernel
theorem subd6_9_116 : subd6_9 [-2, -2, -7] = true := by decide +kernel
theorem subd6_9_117 : subd6_9 [-2, -2, -6] = true := by decide +kernel
theorem subd6_9_118 : subd6_9 [-2, -2, -5] = true := by decide +kernel
theorem subd6_9_119 : subd6_9 [-2, -2, -4] = true := by decide +kernel
theorem subd6_9_120 : subd6_9 [-2, -2, -3] = true := by decide +kernel
theorem subd6_9_121 : subd6_9 [-2, -2, -2] = true := by decide +kernel
theorem subd6_9_122 : subd6_9 [-2, -2, -1] = true := by decide +kernel
theorem subd6_9_123 : subd6_9 [-2, -2, 0] = true := by decide +kernel
theorem subd6_9_124 : subd6_9 [-2, -2, 1] = true := by decide +kernel
theorem subd6_9_125 : subd6_9 [-2, -2, 2] = true := by decide +kernel
theorem subd6_9_126 : subd6_9 [-2, -2, 3] = true := by decide +kernel
theorem subd6_9_127 : subd6_9 [-2, -2, 4] = true := by decide +kernel
theorem sbd6_9_3 : ∀ q ∈ blkd6_9_3, subd6_9 q = true := by
  unfold blkd6_9_3
  exact List.forall_mem_cons.2 ⟨subd6_9_96, List.forall_mem_cons.2 ⟨subd6_9_97, List.forall_mem_cons.2 ⟨subd6_9_98, List.forall_mem_cons.2 ⟨subd6_9_99, List.forall_mem_cons.2 ⟨subd6_9_100, List.forall_mem_cons.2 ⟨subd6_9_101, List.forall_mem_cons.2 ⟨subd6_9_102, List.forall_mem_cons.2 ⟨subd6_9_103, List.forall_mem_cons.2 ⟨subd6_9_104, List.forall_mem_cons.2 ⟨subd6_9_105, List.forall_mem_cons.2 ⟨subd6_9_106, List.forall_mem_cons.2 ⟨subd6_9_107, List.forall_mem_cons.2 ⟨subd6_9_108, List.forall_mem_cons.2 ⟨subd6_9_109, List.forall_mem_cons.2 ⟨subd6_9_110, List.forall_mem_cons.2 ⟨subd6_9_111, List.forall_mem_cons.2 ⟨subd6_9_112, List.forall_mem_cons.2 ⟨subd6_9_113, List.forall_mem_cons.2 ⟨subd6_9_114, List.forall_mem_cons.2 ⟨subd6_9_115, List.forall_mem_cons.2 ⟨subd6_9_116, List.forall_mem_cons.2 ⟨subd6_9_117, List.forall_mem_cons.2 ⟨subd6_9_118, List.forall_mem_cons.2 ⟨subd6_9_119, List.forall_mem_cons.2 ⟨subd6_9_120, List.forall_mem_cons.2 ⟨subd6_9_121, List.forall_mem_cons.2 ⟨subd6_9_122, List.forall_mem_cons.2 ⟨subd6_9_123, List.forall_mem_cons.2 ⟨subd6_9_124, List.forall_mem_cons.2 ⟨subd6_9_125, List.forall_mem_cons.2 ⟨subd6_9_126, List.forall_mem_cons.2 ⟨subd6_9_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_128 : subd6_9 [-2, -2, 5] = true := by decide +kernel
theorem subd6_9_129 : subd6_9 [-2, -2, 6] = true := by decide +kernel
theorem subd6_9_130 : subd6_9 [-2, -1, -9] = true := by decide +kernel
theorem subd6_9_131 : subd6_9 [-2, -1, -8] = true := by decide +kernel
theorem subd6_9_132 : subd6_9 [-2, -1, -7] = true := by decide +kernel
theorem subd6_9_133 : subd6_9 [-2, -1, -6] = true := by decide +kernel
theorem subd6_9_134 : subd6_9 [-2, -1, -5] = true := by decide +kernel
theorem subd6_9_135 : subd6_9 [-2, -1, -4] = true := by decide +kernel
theorem subd6_9_136 : subd6_9 [-2, -1, -3] = true := by decide +kernel
theorem subd6_9_137 : subd6_9 [-2, -1, -2] = true := by decide +kernel
theorem subd6_9_138 : subd6_9 [-2, -1, -1] = true := by decide +kernel
theorem subd6_9_139 : subd6_9 [-2, -1, 0] = true := by decide +kernel
theorem subd6_9_140 : subd6_9 [-2, -1, 1] = true := by decide +kernel
theorem subd6_9_141 : subd6_9 [-2, -1, 2] = true := by decide +kernel
theorem subd6_9_142 : subd6_9 [-2, -1, 3] = true := by decide +kernel
theorem subd6_9_143 : subd6_9 [-2, -1, 4] = true := by decide +kernel
theorem subd6_9_144 : subd6_9 [-2, -1, 5] = true := by decide +kernel
theorem subd6_9_145 : subd6_9 [-2, -1, 6] = true := by decide +kernel
theorem subd6_9_146 : subd6_9 [-2, 0, -9] = true := by decide +kernel
theorem subd6_9_147 : subd6_9 [-2, 0, -8] = true := by decide +kernel
theorem subd6_9_148 : subd6_9 [-2, 0, -7] = true := by decide +kernel
theorem subd6_9_149 : subd6_9 [-2, 0, -6] = true := by decide +kernel
theorem subd6_9_150 : subd6_9 [-2, 0, -5] = true := by decide +kernel
theorem subd6_9_151 : subd6_9 [-2, 0, -4] = true := by decide +kernel
theorem subd6_9_152 : subd6_9 [-2, 0, -3] = true := by decide +kernel
theorem subd6_9_153 : subd6_9 [-2, 0, -2] = true := by decide +kernel
theorem subd6_9_154 : subd6_9 [-2, 0, -1] = true := by decide +kernel
theorem subd6_9_155 : subd6_9 [-2, 0, 0] = true := by decide +kernel
theorem subd6_9_156 : subd6_9 [-2, 0, 1] = true := by decide +kernel
theorem subd6_9_157 : subd6_9 [-2, 0, 2] = true := by decide +kernel
theorem subd6_9_158 : subd6_9 [-2, 0, 3] = true := by decide +kernel
theorem subd6_9_159 : subd6_9 [-2, 0, 4] = true := by decide +kernel
theorem sbd6_9_4 : ∀ q ∈ blkd6_9_4, subd6_9 q = true := by
  unfold blkd6_9_4
  exact List.forall_mem_cons.2 ⟨subd6_9_128, List.forall_mem_cons.2 ⟨subd6_9_129, List.forall_mem_cons.2 ⟨subd6_9_130, List.forall_mem_cons.2 ⟨subd6_9_131, List.forall_mem_cons.2 ⟨subd6_9_132, List.forall_mem_cons.2 ⟨subd6_9_133, List.forall_mem_cons.2 ⟨subd6_9_134, List.forall_mem_cons.2 ⟨subd6_9_135, List.forall_mem_cons.2 ⟨subd6_9_136, List.forall_mem_cons.2 ⟨subd6_9_137, List.forall_mem_cons.2 ⟨subd6_9_138, List.forall_mem_cons.2 ⟨subd6_9_139, List.forall_mem_cons.2 ⟨subd6_9_140, List.forall_mem_cons.2 ⟨subd6_9_141, List.forall_mem_cons.2 ⟨subd6_9_142, List.forall_mem_cons.2 ⟨subd6_9_143, List.forall_mem_cons.2 ⟨subd6_9_144, List.forall_mem_cons.2 ⟨subd6_9_145, List.forall_mem_cons.2 ⟨subd6_9_146, List.forall_mem_cons.2 ⟨subd6_9_147, List.forall_mem_cons.2 ⟨subd6_9_148, List.forall_mem_cons.2 ⟨subd6_9_149, List.forall_mem_cons.2 ⟨subd6_9_150, List.forall_mem_cons.2 ⟨subd6_9_151, List.forall_mem_cons.2 ⟨subd6_9_152, List.forall_mem_cons.2 ⟨subd6_9_153, List.forall_mem_cons.2 ⟨subd6_9_154, List.forall_mem_cons.2 ⟨subd6_9_155, List.forall_mem_cons.2 ⟨subd6_9_156, List.forall_mem_cons.2 ⟨subd6_9_157, List.forall_mem_cons.2 ⟨subd6_9_158, List.forall_mem_cons.2 ⟨subd6_9_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_160 : subd6_9 [-2, 0, 5] = true := by decide +kernel
theorem subd6_9_161 : subd6_9 [-2, 0, 6] = true := by decide +kernel
theorem subd6_9_162 : subd6_9 [-2, 1, -9] = true := by decide +kernel
theorem subd6_9_163 : subd6_9 [-2, 1, -8] = true := by decide +kernel
theorem subd6_9_164 : subd6_9 [-2, 1, -7] = true := by decide +kernel
theorem subd6_9_165 : subd6_9 [-2, 1, -6] = true := by decide +kernel
theorem subd6_9_166 : subd6_9 [-2, 1, -5] = true := by decide +kernel
theorem subd6_9_167 : subd6_9 [-2, 1, -4] = true := by decide +kernel
theorem subd6_9_168 : subd6_9 [-2, 1, -3] = true := by decide +kernel
theorem subd6_9_169 : subd6_9 [-2, 1, -2] = true := by decide +kernel
theorem subd6_9_170 : subd6_9 [-2, 1, -1] = true := by decide +kernel
theorem subd6_9_171 : subd6_9 [-2, 1, 0] = true := by decide +kernel
theorem subd6_9_172 : subd6_9 [-2, 1, 1] = true := by decide +kernel
theorem subd6_9_173 : subd6_9 [-2, 1, 2] = true := by decide +kernel
theorem subd6_9_174 : subd6_9 [-2, 1, 3] = true := by decide +kernel
theorem subd6_9_175 : subd6_9 [-2, 1, 4] = true := by decide +kernel
theorem subd6_9_176 : subd6_9 [-2, 1, 5] = true := by decide +kernel
theorem subd6_9_177 : subd6_9 [-2, 1, 6] = true := by decide +kernel
theorem subd6_9_178 : subd6_9 [-2, 2, -9] = true := by decide +kernel
theorem subd6_9_179 : subd6_9 [-2, 2, -8] = true := by decide +kernel
theorem subd6_9_180 : subd6_9 [-2, 2, -7] = true := by decide +kernel
theorem subd6_9_181 : subd6_9 [-2, 2, -6] = true := by decide +kernel
theorem subd6_9_182 : subd6_9 [-2, 2, -5] = true := by decide +kernel
theorem subd6_9_183 : subd6_9 [-2, 2, -4] = true := by decide +kernel
theorem subd6_9_184 : subd6_9 [-2, 2, -3] = true := by decide +kernel
theorem subd6_9_185 : subd6_9 [-2, 2, -2] = true := by decide +kernel
theorem subd6_9_186 : subd6_9 [-2, 2, -1] = true := by decide +kernel
theorem subd6_9_187 : subd6_9 [-2, 2, 0] = true := by decide +kernel
theorem subd6_9_188 : subd6_9 [-2, 2, 1] = true := by decide +kernel
theorem subd6_9_189 : subd6_9 [-2, 2, 2] = true := by decide +kernel
theorem subd6_9_190 : subd6_9 [-2, 2, 3] = true := by decide +kernel
theorem subd6_9_191 : subd6_9 [-2, 2, 4] = true := by decide +kernel
theorem sbd6_9_5 : ∀ q ∈ blkd6_9_5, subd6_9 q = true := by
  unfold blkd6_9_5
  exact List.forall_mem_cons.2 ⟨subd6_9_160, List.forall_mem_cons.2 ⟨subd6_9_161, List.forall_mem_cons.2 ⟨subd6_9_162, List.forall_mem_cons.2 ⟨subd6_9_163, List.forall_mem_cons.2 ⟨subd6_9_164, List.forall_mem_cons.2 ⟨subd6_9_165, List.forall_mem_cons.2 ⟨subd6_9_166, List.forall_mem_cons.2 ⟨subd6_9_167, List.forall_mem_cons.2 ⟨subd6_9_168, List.forall_mem_cons.2 ⟨subd6_9_169, List.forall_mem_cons.2 ⟨subd6_9_170, List.forall_mem_cons.2 ⟨subd6_9_171, List.forall_mem_cons.2 ⟨subd6_9_172, List.forall_mem_cons.2 ⟨subd6_9_173, List.forall_mem_cons.2 ⟨subd6_9_174, List.forall_mem_cons.2 ⟨subd6_9_175, List.forall_mem_cons.2 ⟨subd6_9_176, List.forall_mem_cons.2 ⟨subd6_9_177, List.forall_mem_cons.2 ⟨subd6_9_178, List.forall_mem_cons.2 ⟨subd6_9_179, List.forall_mem_cons.2 ⟨subd6_9_180, List.forall_mem_cons.2 ⟨subd6_9_181, List.forall_mem_cons.2 ⟨subd6_9_182, List.forall_mem_cons.2 ⟨subd6_9_183, List.forall_mem_cons.2 ⟨subd6_9_184, List.forall_mem_cons.2 ⟨subd6_9_185, List.forall_mem_cons.2 ⟨subd6_9_186, List.forall_mem_cons.2 ⟨subd6_9_187, List.forall_mem_cons.2 ⟨subd6_9_188, List.forall_mem_cons.2 ⟨subd6_9_189, List.forall_mem_cons.2 ⟨subd6_9_190, List.forall_mem_cons.2 ⟨subd6_9_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_192 : subd6_9 [-2, 2, 5] = true := by decide +kernel
theorem subd6_9_193 : subd6_9 [-2, 3, -9] = true := by decide +kernel
theorem subd6_9_194 : subd6_9 [-2, 3, -8] = true := by decide +kernel
theorem subd6_9_195 : subd6_9 [-2, 3, -7] = true := by decide +kernel
theorem subd6_9_196 : subd6_9 [-2, 3, -6] = true := by decide +kernel
theorem subd6_9_197 : subd6_9 [-2, 3, -5] = true := by decide +kernel
theorem subd6_9_198 : subd6_9 [-2, 3, -4] = true := by decide +kernel
theorem subd6_9_199 : subd6_9 [-2, 3, -3] = true := by decide +kernel
theorem subd6_9_200 : subd6_9 [-2, 3, -2] = true := by decide +kernel
theorem subd6_9_201 : subd6_9 [-2, 3, -1] = true := by decide +kernel
theorem subd6_9_202 : subd6_9 [-2, 3, 0] = true := by decide +kernel
theorem subd6_9_203 : subd6_9 [-2, 3, 1] = true := by decide +kernel
theorem subd6_9_204 : subd6_9 [-2, 3, 2] = true := by decide +kernel
theorem subd6_9_205 : subd6_9 [-2, 3, 3] = true := by decide +kernel
theorem subd6_9_206 : subd6_9 [-2, 3, 4] = true := by decide +kernel
theorem subd6_9_207 : subd6_9 [-2, 4] = true := by decide +kernel
theorem subd6_9_208 : subd6_9 [-2, 5] = true := by decide +kernel
theorem subd6_9_209 : subd6_9 [-1, -6] = true := by decide +kernel
theorem subd6_9_210 : subd6_9 [-1, -5] = true := by decide +kernel
theorem subd6_9_211 : subd6_9 [-1, -4] = true := by decide +kernel
theorem subd6_9_212 : subd6_9 [-1, -3, -7] = true := by decide +kernel
theorem subd6_9_213 : subd6_9 [-1, -3, -6] = true := by decide +kernel
theorem subd6_9_214 : subd6_9 [-1, -3, -5] = true := by decide +kernel
theorem subd6_9_215 : subd6_9 [-1, -3, -4] = true := by decide +kernel
theorem subd6_9_216 : subd6_9 [-1, -3, -3] = true := by decide +kernel
theorem subd6_9_217 : subd6_9 [-1, -3, -2] = true := by decide +kernel
theorem subd6_9_218 : subd6_9 [-1, -3, -1] = true := by decide +kernel
theorem subd6_9_219 : subd6_9 [-1, -3, 0] = true := by decide +kernel
theorem subd6_9_220 : subd6_9 [-1, -3, 1] = true := by decide +kernel
theorem subd6_9_221 : subd6_9 [-1, -3, 2] = true := by decide +kernel
theorem subd6_9_222 : subd6_9 [-1, -3, 3] = true := by decide +kernel
theorem subd6_9_223 : subd6_9 [-1, -3, 4] = true := by decide +kernel
theorem sbd6_9_6 : ∀ q ∈ blkd6_9_6, subd6_9 q = true := by
  unfold blkd6_9_6
  exact List.forall_mem_cons.2 ⟨subd6_9_192, List.forall_mem_cons.2 ⟨subd6_9_193, List.forall_mem_cons.2 ⟨subd6_9_194, List.forall_mem_cons.2 ⟨subd6_9_195, List.forall_mem_cons.2 ⟨subd6_9_196, List.forall_mem_cons.2 ⟨subd6_9_197, List.forall_mem_cons.2 ⟨subd6_9_198, List.forall_mem_cons.2 ⟨subd6_9_199, List.forall_mem_cons.2 ⟨subd6_9_200, List.forall_mem_cons.2 ⟨subd6_9_201, List.forall_mem_cons.2 ⟨subd6_9_202, List.forall_mem_cons.2 ⟨subd6_9_203, List.forall_mem_cons.2 ⟨subd6_9_204, List.forall_mem_cons.2 ⟨subd6_9_205, List.forall_mem_cons.2 ⟨subd6_9_206, List.forall_mem_cons.2 ⟨subd6_9_207, List.forall_mem_cons.2 ⟨subd6_9_208, List.forall_mem_cons.2 ⟨subd6_9_209, List.forall_mem_cons.2 ⟨subd6_9_210, List.forall_mem_cons.2 ⟨subd6_9_211, List.forall_mem_cons.2 ⟨subd6_9_212, List.forall_mem_cons.2 ⟨subd6_9_213, List.forall_mem_cons.2 ⟨subd6_9_214, List.forall_mem_cons.2 ⟨subd6_9_215, List.forall_mem_cons.2 ⟨subd6_9_216, List.forall_mem_cons.2 ⟨subd6_9_217, List.forall_mem_cons.2 ⟨subd6_9_218, List.forall_mem_cons.2 ⟨subd6_9_219, List.forall_mem_cons.2 ⟨subd6_9_220, List.forall_mem_cons.2 ⟨subd6_9_221, List.forall_mem_cons.2 ⟨subd6_9_222, List.forall_mem_cons.2 ⟨subd6_9_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_224 : subd6_9 [-1, -3, 5] = true := by decide +kernel
theorem subd6_9_225 : subd6_9 [-1, -3, 6] = true := by decide +kernel
theorem subd6_9_226 : subd6_9 [-1, -3, 7] = true := by decide +kernel
theorem subd6_9_227 : subd6_9 [-1, -2, -8] = true := by decide +kernel
theorem subd6_9_228 : subd6_9 [-1, -2, -7] = true := by decide +kernel
theorem subd6_9_229 : subd6_9 [-1, -2, -6] = true := by decide +kernel
theorem subd6_9_230 : subd6_9 [-1, -2, -5] = true := by decide +kernel
theorem subd6_9_231 : subd6_9 [-1, -2, -4] = true := by decide +kernel
theorem subd6_9_232 : subd6_9 [-1, -2, -3] = true := by decide +kernel
theorem subd6_9_233 : subd6_9 [-1, -2, -2] = true := by decide +kernel
theorem subd6_9_234 : subd6_9 [-1, -2, -1] = true := by decide +kernel
theorem subd6_9_235 : subd6_9 [-1, -2, 0] = true := by decide +kernel
theorem subd6_9_236 : subd6_9 [-1, -2, 1] = true := by decide +kernel
theorem subd6_9_237 : subd6_9 [-1, -2, 2] = true := by decide +kernel
theorem subd6_9_238 : subd6_9 [-1, -2, 3] = true := by decide +kernel
theorem subd6_9_239 : subd6_9 [-1, -2, 4] = true := by decide +kernel
theorem subd6_9_240 : subd6_9 [-1, -2, 5] = true := by decide +kernel
theorem subd6_9_241 : subd6_9 [-1, -2, 6] = true := by decide +kernel
theorem subd6_9_242 : subd6_9 [-1, -2, 7] = true := by decide +kernel
theorem subd6_9_243 : subd6_9 [-1, -1, -9] = true := by decide +kernel
theorem subd6_9_244 : subd6_9 [-1, -1, -8] = true := by decide +kernel
theorem subd6_9_245 : subd6_9 [-1, -1, -7] = true := by decide +kernel
theorem subd6_9_246 : subd6_9 [-1, -1, -6] = true := by decide +kernel
theorem subd6_9_247 : subd6_9 [-1, -1, -5] = true := by decide +kernel
theorem subd6_9_248 : subd6_9 [-1, -1, -4] = true := by decide +kernel
theorem subd6_9_249 : subd6_9 [-1, -1, -3] = true := by decide +kernel
theorem subd6_9_250 : subd6_9 [-1, -1, -2] = true := by decide +kernel
theorem subd6_9_251 : subd6_9 [-1, -1, -1] = true := by decide +kernel
theorem subd6_9_252 : subd6_9 [-1, -1, 0] = true := by decide +kernel
theorem subd6_9_253 : subd6_9 [-1, -1, 1] = true := by decide +kernel
theorem subd6_9_254 : subd6_9 [-1, -1, 2] = true := by decide +kernel
theorem subd6_9_255 : subd6_9 [-1, -1, 3] = true := by decide +kernel
theorem sbd6_9_7 : ∀ q ∈ blkd6_9_7, subd6_9 q = true := by
  unfold blkd6_9_7
  exact List.forall_mem_cons.2 ⟨subd6_9_224, List.forall_mem_cons.2 ⟨subd6_9_225, List.forall_mem_cons.2 ⟨subd6_9_226, List.forall_mem_cons.2 ⟨subd6_9_227, List.forall_mem_cons.2 ⟨subd6_9_228, List.forall_mem_cons.2 ⟨subd6_9_229, List.forall_mem_cons.2 ⟨subd6_9_230, List.forall_mem_cons.2 ⟨subd6_9_231, List.forall_mem_cons.2 ⟨subd6_9_232, List.forall_mem_cons.2 ⟨subd6_9_233, List.forall_mem_cons.2 ⟨subd6_9_234, List.forall_mem_cons.2 ⟨subd6_9_235, List.forall_mem_cons.2 ⟨subd6_9_236, List.forall_mem_cons.2 ⟨subd6_9_237, List.forall_mem_cons.2 ⟨subd6_9_238, List.forall_mem_cons.2 ⟨subd6_9_239, List.forall_mem_cons.2 ⟨subd6_9_240, List.forall_mem_cons.2 ⟨subd6_9_241, List.forall_mem_cons.2 ⟨subd6_9_242, List.forall_mem_cons.2 ⟨subd6_9_243, List.forall_mem_cons.2 ⟨subd6_9_244, List.forall_mem_cons.2 ⟨subd6_9_245, List.forall_mem_cons.2 ⟨subd6_9_246, List.forall_mem_cons.2 ⟨subd6_9_247, List.forall_mem_cons.2 ⟨subd6_9_248, List.forall_mem_cons.2 ⟨subd6_9_249, List.forall_mem_cons.2 ⟨subd6_9_250, List.forall_mem_cons.2 ⟨subd6_9_251, List.forall_mem_cons.2 ⟨subd6_9_252, List.forall_mem_cons.2 ⟨subd6_9_253, List.forall_mem_cons.2 ⟨subd6_9_254, List.forall_mem_cons.2 ⟨subd6_9_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_256 : subd6_9 [-1, -1, 4] = true := by decide +kernel
theorem subd6_9_257 : subd6_9 [-1, -1, 5] = true := by decide +kernel
theorem subd6_9_258 : subd6_9 [-1, -1, 6] = true := by decide +kernel
theorem subd6_9_259 : subd6_9 [-1, -1, 7] = true := by decide +kernel
theorem subd6_9_260 : subd6_9 [-1, 0, -9] = true := by decide +kernel
theorem subd6_9_261 : subd6_9 [-1, 0, -8] = true := by decide +kernel
theorem subd6_9_262 : subd6_9 [-1, 0, -7] = true := by decide +kernel
theorem subd6_9_263 : subd6_9 [-1, 0, -6] = true := by decide +kernel
theorem subd6_9_264 : subd6_9 [-1, 0, -5] = true := by decide +kernel
theorem subd6_9_265 : subd6_9 [-1, 0, -4] = true := by decide +kernel
theorem subd6_9_266 : subd6_9 [-1, 0, -3] = true := by decide +kernel
theorem subd6_9_267 : subd6_9 [-1, 0, -2] = true := by decide +kernel
theorem subd6_9_268 : subd6_9 [-1, 0, -1] = true := by decide +kernel
theorem subd6_9_269 : subd6_9 [-1, 0, 0] = true := by decide +kernel
theorem subd6_9_270 : subd6_9 [-1, 0, 1] = true := by decide +kernel
theorem subd6_9_271 : subd6_9 [-1, 0, 2] = true := by decide +kernel
theorem subd6_9_272 : subd6_9 [-1, 0, 3] = true := by decide +kernel
theorem subd6_9_273 : subd6_9 [-1, 0, 4] = true := by decide +kernel
theorem subd6_9_274 : subd6_9 [-1, 0, 5] = true := by decide +kernel
theorem subd6_9_275 : subd6_9 [-1, 0, 6] = true := by decide +kernel
theorem subd6_9_276 : subd6_9 [-1, 0, 7] = true := by decide +kernel
theorem subd6_9_277 : subd6_9 [-1, 1, -9] = true := by decide +kernel
theorem subd6_9_278 : subd6_9 [-1, 1, -8] = true := by decide +kernel
theorem subd6_9_279 : subd6_9 [-1, 1, -7] = true := by decide +kernel
theorem subd6_9_280 : subd6_9 [-1, 1, -6] = true := by decide +kernel
theorem subd6_9_281 : subd6_9 [-1, 1, -5] = true := by decide +kernel
theorem subd6_9_282 : subd6_9 [-1, 1, -4] = true := by decide +kernel
theorem subd6_9_283 : subd6_9 [-1, 1, -3] = true := by decide +kernel
theorem subd6_9_284 : subd6_9 [-1, 1, -2] = true := by decide +kernel
theorem subd6_9_285 : subd6_9 [-1, 1, -1] = true := by decide +kernel
theorem subd6_9_286 : subd6_9 [-1, 1, 0] = true := by decide +kernel
theorem subd6_9_287 : subd6_9 [-1, 1, 1] = true := by decide +kernel
theorem sbd6_9_8 : ∀ q ∈ blkd6_9_8, subd6_9 q = true := by
  unfold blkd6_9_8
  exact List.forall_mem_cons.2 ⟨subd6_9_256, List.forall_mem_cons.2 ⟨subd6_9_257, List.forall_mem_cons.2 ⟨subd6_9_258, List.forall_mem_cons.2 ⟨subd6_9_259, List.forall_mem_cons.2 ⟨subd6_9_260, List.forall_mem_cons.2 ⟨subd6_9_261, List.forall_mem_cons.2 ⟨subd6_9_262, List.forall_mem_cons.2 ⟨subd6_9_263, List.forall_mem_cons.2 ⟨subd6_9_264, List.forall_mem_cons.2 ⟨subd6_9_265, List.forall_mem_cons.2 ⟨subd6_9_266, List.forall_mem_cons.2 ⟨subd6_9_267, List.forall_mem_cons.2 ⟨subd6_9_268, List.forall_mem_cons.2 ⟨subd6_9_269, List.forall_mem_cons.2 ⟨subd6_9_270, List.forall_mem_cons.2 ⟨subd6_9_271, List.forall_mem_cons.2 ⟨subd6_9_272, List.forall_mem_cons.2 ⟨subd6_9_273, List.forall_mem_cons.2 ⟨subd6_9_274, List.forall_mem_cons.2 ⟨subd6_9_275, List.forall_mem_cons.2 ⟨subd6_9_276, List.forall_mem_cons.2 ⟨subd6_9_277, List.forall_mem_cons.2 ⟨subd6_9_278, List.forall_mem_cons.2 ⟨subd6_9_279, List.forall_mem_cons.2 ⟨subd6_9_280, List.forall_mem_cons.2 ⟨subd6_9_281, List.forall_mem_cons.2 ⟨subd6_9_282, List.forall_mem_cons.2 ⟨subd6_9_283, List.forall_mem_cons.2 ⟨subd6_9_284, List.forall_mem_cons.2 ⟨subd6_9_285, List.forall_mem_cons.2 ⟨subd6_9_286, List.forall_mem_cons.2 ⟨subd6_9_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_288 : subd6_9 [-1, 1, 2] = true := by decide +kernel
theorem subd6_9_289 : subd6_9 [-1, 1, 3] = true := by decide +kernel
theorem subd6_9_290 : subd6_9 [-1, 1, 4] = true := by decide +kernel
theorem subd6_9_291 : subd6_9 [-1, 1, 5] = true := by decide +kernel
theorem subd6_9_292 : subd6_9 [-1, 1, 6] = true := by decide +kernel
theorem subd6_9_293 : subd6_9 [-1, 1, 7] = true := by decide +kernel
theorem subd6_9_294 : subd6_9 [-1, 2, -9] = true := by decide +kernel
theorem subd6_9_295 : subd6_9 [-1, 2, -8] = true := by decide +kernel
theorem subd6_9_296 : subd6_9 [-1, 2, -7] = true := by decide +kernel
theorem subd6_9_297 : subd6_9 [-1, 2, -6] = true := by decide +kernel
theorem subd6_9_298 : subd6_9 [-1, 2, -5] = true := by decide +kernel
theorem subd6_9_299 : subd6_9 [-1, 2, -4] = true := by decide +kernel
theorem subd6_9_300 : subd6_9 [-1, 2, -3] = true := by decide +kernel
theorem subd6_9_301 : subd6_9 [-1, 2, -2] = true := by decide +kernel
theorem subd6_9_302 : subd6_9 [-1, 2, -1] = true := by decide +kernel
theorem subd6_9_303 : subd6_9 [-1, 2, 0] = true := by decide +kernel
theorem subd6_9_304 : subd6_9 [-1, 2, 1] = true := by decide +kernel
theorem subd6_9_305 : subd6_9 [-1, 2, 2] = true := by decide +kernel
theorem subd6_9_306 : subd6_9 [-1, 2, 3] = true := by decide +kernel
theorem subd6_9_307 : subd6_9 [-1, 2, 4] = true := by decide +kernel
theorem subd6_9_308 : subd6_9 [-1, 2, 5] = true := by decide +kernel
theorem subd6_9_309 : subd6_9 [-1, 2, 6] = true := by decide +kernel
theorem subd6_9_310 : subd6_9 [-1, 3, -9] = true := by decide +kernel
theorem subd6_9_311 : subd6_9 [-1, 3, -8] = true := by decide +kernel
theorem subd6_9_312 : subd6_9 [-1, 3, -7] = true := by decide +kernel
theorem subd6_9_313 : subd6_9 [-1, 3, -6] = true := by decide +kernel
theorem subd6_9_314 : subd6_9 [-1, 3, -5] = true := by decide +kernel
theorem subd6_9_315 : subd6_9 [-1, 3, -4] = true := by decide +kernel
theorem subd6_9_316 : subd6_9 [-1, 3, -3] = true := by decide +kernel
theorem subd6_9_317 : subd6_9 [-1, 3, -2] = true := by decide +kernel
theorem subd6_9_318 : subd6_9 [-1, 3, -1] = true := by decide +kernel
theorem subd6_9_319 : subd6_9 [-1, 3, 0] = true := by decide +kernel
theorem sbd6_9_9 : ∀ q ∈ blkd6_9_9, subd6_9 q = true := by
  unfold blkd6_9_9
  exact List.forall_mem_cons.2 ⟨subd6_9_288, List.forall_mem_cons.2 ⟨subd6_9_289, List.forall_mem_cons.2 ⟨subd6_9_290, List.forall_mem_cons.2 ⟨subd6_9_291, List.forall_mem_cons.2 ⟨subd6_9_292, List.forall_mem_cons.2 ⟨subd6_9_293, List.forall_mem_cons.2 ⟨subd6_9_294, List.forall_mem_cons.2 ⟨subd6_9_295, List.forall_mem_cons.2 ⟨subd6_9_296, List.forall_mem_cons.2 ⟨subd6_9_297, List.forall_mem_cons.2 ⟨subd6_9_298, List.forall_mem_cons.2 ⟨subd6_9_299, List.forall_mem_cons.2 ⟨subd6_9_300, List.forall_mem_cons.2 ⟨subd6_9_301, List.forall_mem_cons.2 ⟨subd6_9_302, List.forall_mem_cons.2 ⟨subd6_9_303, List.forall_mem_cons.2 ⟨subd6_9_304, List.forall_mem_cons.2 ⟨subd6_9_305, List.forall_mem_cons.2 ⟨subd6_9_306, List.forall_mem_cons.2 ⟨subd6_9_307, List.forall_mem_cons.2 ⟨subd6_9_308, List.forall_mem_cons.2 ⟨subd6_9_309, List.forall_mem_cons.2 ⟨subd6_9_310, List.forall_mem_cons.2 ⟨subd6_9_311, List.forall_mem_cons.2 ⟨subd6_9_312, List.forall_mem_cons.2 ⟨subd6_9_313, List.forall_mem_cons.2 ⟨subd6_9_314, List.forall_mem_cons.2 ⟨subd6_9_315, List.forall_mem_cons.2 ⟨subd6_9_316, List.forall_mem_cons.2 ⟨subd6_9_317, List.forall_mem_cons.2 ⟨subd6_9_318, List.forall_mem_cons.2 ⟨subd6_9_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_320 : subd6_9 [-1, 3, 1] = true := by decide +kernel
theorem subd6_9_321 : subd6_9 [-1, 3, 2] = true := by decide +kernel
theorem subd6_9_322 : subd6_9 [-1, 3, 3] = true := by decide +kernel
theorem subd6_9_323 : subd6_9 [-1, 3, 4] = true := by decide +kernel
theorem subd6_9_324 : subd6_9 [-1, 3, 5] = true := by decide +kernel
theorem subd6_9_325 : subd6_9 [-1, 4] = true := by decide +kernel
theorem subd6_9_326 : subd6_9 [-1, 5] = true := by decide +kernel
theorem subd6_9_327 : subd6_9 [0, -6] = true := by decide +kernel
theorem subd6_9_328 : subd6_9 [0, -5] = true := by decide +kernel
theorem subd6_9_329 : subd6_9 [0, -4] = true := by decide +kernel
theorem subd6_9_330 : subd6_9 [0, -3, -7] = true := by decide +kernel
theorem subd6_9_331 : subd6_9 [0, -3, -6] = true := by decide +kernel
theorem subd6_9_332 : subd6_9 [0, -3, -5] = true := by decide +kernel
theorem subd6_9_333 : subd6_9 [0, -3, -4] = true := by decide +kernel
theorem subd6_9_334 : subd6_9 [0, -3, -3] = true := by decide +kernel
theorem subd6_9_335 : subd6_9 [0, -3, -2] = true := by decide +kernel
theorem subd6_9_336 : subd6_9 [0, -3, -1] = true := by decide +kernel
theorem subd6_9_337 : subd6_9 [0, -3, 0] = true := by decide +kernel
theorem subd6_9_338 : subd6_9 [0, -3, 1] = true := by decide +kernel
theorem subd6_9_339 : subd6_9 [0, -3, 2] = true := by decide +kernel
theorem subd6_9_340 : subd6_9 [0, -3, 3] = true := by decide +kernel
theorem subd6_9_341 : subd6_9 [0, -3, 4] = true := by decide +kernel
theorem subd6_9_342 : subd6_9 [0, -3, 5] = true := by decide +kernel
theorem subd6_9_343 : subd6_9 [0, -3, 6] = true := by decide +kernel
theorem subd6_9_344 : subd6_9 [0, -3, 7] = true := by decide +kernel
theorem subd6_9_345 : subd6_9 [0, -3, 8] = true := by decide +kernel
theorem subd6_9_346 : subd6_9 [0, -2, -8] = true := by decide +kernel
theorem subd6_9_347 : subd6_9 [0, -2, -7] = true := by decide +kernel
theorem subd6_9_348 : subd6_9 [0, -2, -6] = true := by decide +kernel
theorem subd6_9_349 : subd6_9 [0, -2, -5] = true := by decide +kernel
theorem subd6_9_350 : subd6_9 [0, -2, -4] = true := by decide +kernel
theorem subd6_9_351 : subd6_9 [0, -2, -3] = true := by decide +kernel
theorem sbd6_9_10 : ∀ q ∈ blkd6_9_10, subd6_9 q = true := by
  unfold blkd6_9_10
  exact List.forall_mem_cons.2 ⟨subd6_9_320, List.forall_mem_cons.2 ⟨subd6_9_321, List.forall_mem_cons.2 ⟨subd6_9_322, List.forall_mem_cons.2 ⟨subd6_9_323, List.forall_mem_cons.2 ⟨subd6_9_324, List.forall_mem_cons.2 ⟨subd6_9_325, List.forall_mem_cons.2 ⟨subd6_9_326, List.forall_mem_cons.2 ⟨subd6_9_327, List.forall_mem_cons.2 ⟨subd6_9_328, List.forall_mem_cons.2 ⟨subd6_9_329, List.forall_mem_cons.2 ⟨subd6_9_330, List.forall_mem_cons.2 ⟨subd6_9_331, List.forall_mem_cons.2 ⟨subd6_9_332, List.forall_mem_cons.2 ⟨subd6_9_333, List.forall_mem_cons.2 ⟨subd6_9_334, List.forall_mem_cons.2 ⟨subd6_9_335, List.forall_mem_cons.2 ⟨subd6_9_336, List.forall_mem_cons.2 ⟨subd6_9_337, List.forall_mem_cons.2 ⟨subd6_9_338, List.forall_mem_cons.2 ⟨subd6_9_339, List.forall_mem_cons.2 ⟨subd6_9_340, List.forall_mem_cons.2 ⟨subd6_9_341, List.forall_mem_cons.2 ⟨subd6_9_342, List.forall_mem_cons.2 ⟨subd6_9_343, List.forall_mem_cons.2 ⟨subd6_9_344, List.forall_mem_cons.2 ⟨subd6_9_345, List.forall_mem_cons.2 ⟨subd6_9_346, List.forall_mem_cons.2 ⟨subd6_9_347, List.forall_mem_cons.2 ⟨subd6_9_348, List.forall_mem_cons.2 ⟨subd6_9_349, List.forall_mem_cons.2 ⟨subd6_9_350, List.forall_mem_cons.2 ⟨subd6_9_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_352 : subd6_9 [0, -2, -2] = true := by decide +kernel
theorem subd6_9_353 : subd6_9 [0, -2, -1] = true := by decide +kernel
theorem subd6_9_354 : subd6_9 [0, -2, 0] = true := by decide +kernel
theorem subd6_9_355 : subd6_9 [0, -2, 1] = true := by decide +kernel
theorem subd6_9_356 : subd6_9 [0, -2, 2] = true := by decide +kernel
theorem subd6_9_357 : subd6_9 [0, -2, 3] = true := by decide +kernel
theorem subd6_9_358 : subd6_9 [0, -2, 4] = true := by decide +kernel
theorem subd6_9_359 : subd6_9 [0, -2, 5] = true := by decide +kernel
theorem subd6_9_360 : subd6_9 [0, -2, 6] = true := by decide +kernel
theorem subd6_9_361 : subd6_9 [0, -2, 7] = true := by decide +kernel
theorem subd6_9_362 : subd6_9 [0, -2, 8] = true := by decide +kernel
theorem subd6_9_363 : subd6_9 [0, -1, -8] = true := by decide +kernel
theorem subd6_9_364 : subd6_9 [0, -1, -7] = true := by decide +kernel
theorem subd6_9_365 : subd6_9 [0, -1, -6] = true := by decide +kernel
theorem subd6_9_366 : subd6_9 [0, -1, -5] = true := by decide +kernel
theorem subd6_9_367 : subd6_9 [0, -1, -4] = true := by decide +kernel
theorem subd6_9_368 : subd6_9 [0, -1, -3] = true := by decide +kernel
theorem subd6_9_369 : subd6_9 [0, -1, -2] = true := by decide +kernel
theorem subd6_9_370 : subd6_9 [0, -1, -1] = true := by decide +kernel
theorem subd6_9_371 : subd6_9 [0, -1, 0] = true := by decide +kernel
theorem subd6_9_372 : subd6_9 [0, -1, 1] = true := by decide +kernel
theorem subd6_9_373 : subd6_9 [0, -1, 2] = true := by decide +kernel
theorem subd6_9_374 : subd6_9 [0, -1, 3] = true := by decide +kernel
theorem subd6_9_375 : subd6_9 [0, -1, 4] = true := by decide +kernel
theorem subd6_9_376 : subd6_9 [0, -1, 5] = true := by decide +kernel
theorem subd6_9_377 : subd6_9 [0, -1, 6] = true := by decide +kernel
theorem subd6_9_378 : subd6_9 [0, -1, 7] = true := by decide +kernel
theorem subd6_9_379 : subd6_9 [0, -1, 8] = true := by decide +kernel
theorem subd6_9_380 : subd6_9 [0, 0, -9] = true := by decide +kernel
theorem subd6_9_381 : subd6_9 [0, 0, -8] = true := by decide +kernel
theorem subd6_9_382 : subd6_9 [0, 0, -7] = true := by decide +kernel
theorem subd6_9_383 : subd6_9 [0, 0, -6] = true := by decide +kernel
theorem sbd6_9_11 : ∀ q ∈ blkd6_9_11, subd6_9 q = true := by
  unfold blkd6_9_11
  exact List.forall_mem_cons.2 ⟨subd6_9_352, List.forall_mem_cons.2 ⟨subd6_9_353, List.forall_mem_cons.2 ⟨subd6_9_354, List.forall_mem_cons.2 ⟨subd6_9_355, List.forall_mem_cons.2 ⟨subd6_9_356, List.forall_mem_cons.2 ⟨subd6_9_357, List.forall_mem_cons.2 ⟨subd6_9_358, List.forall_mem_cons.2 ⟨subd6_9_359, List.forall_mem_cons.2 ⟨subd6_9_360, List.forall_mem_cons.2 ⟨subd6_9_361, List.forall_mem_cons.2 ⟨subd6_9_362, List.forall_mem_cons.2 ⟨subd6_9_363, List.forall_mem_cons.2 ⟨subd6_9_364, List.forall_mem_cons.2 ⟨subd6_9_365, List.forall_mem_cons.2 ⟨subd6_9_366, List.forall_mem_cons.2 ⟨subd6_9_367, List.forall_mem_cons.2 ⟨subd6_9_368, List.forall_mem_cons.2 ⟨subd6_9_369, List.forall_mem_cons.2 ⟨subd6_9_370, List.forall_mem_cons.2 ⟨subd6_9_371, List.forall_mem_cons.2 ⟨subd6_9_372, List.forall_mem_cons.2 ⟨subd6_9_373, List.forall_mem_cons.2 ⟨subd6_9_374, List.forall_mem_cons.2 ⟨subd6_9_375, List.forall_mem_cons.2 ⟨subd6_9_376, List.forall_mem_cons.2 ⟨subd6_9_377, List.forall_mem_cons.2 ⟨subd6_9_378, List.forall_mem_cons.2 ⟨subd6_9_379, List.forall_mem_cons.2 ⟨subd6_9_380, List.forall_mem_cons.2 ⟨subd6_9_381, List.forall_mem_cons.2 ⟨subd6_9_382, List.forall_mem_cons.2 ⟨subd6_9_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_384 : subd6_9 [0, 0, -5] = true := by decide +kernel
theorem subd6_9_385 : subd6_9 [0, 0, -4] = true := by decide +kernel
theorem subd6_9_386 : subd6_9 [0, 0, -3] = true := by decide +kernel
theorem subd6_9_387 : subd6_9 [0, 0, -2] = true := by decide +kernel
theorem subd6_9_388 : subd6_9 [0, 0, -1] = true := by decide +kernel
theorem subd6_9_389 : subd6_9 [0, 0, 0] = true := by decide +kernel
theorem subd6_9_390 : subd6_9 [0, 0, 1] = true := by decide +kernel
theorem subd6_9_391 : subd6_9 [0, 0, 2] = true := by decide +kernel
theorem subd6_9_392 : subd6_9 [0, 0, 3] = true := by decide +kernel
theorem subd6_9_393 : subd6_9 [0, 0, 4] = true := by decide +kernel
theorem subd6_9_394 : subd6_9 [0, 0, 5] = true := by decide +kernel
theorem subd6_9_395 : subd6_9 [0, 0, 6] = true := by decide +kernel
theorem subd6_9_396 : subd6_9 [0, 0, 7] = true := by decide +kernel
theorem subd6_9_397 : subd6_9 [0, 0, 8] = true := by decide +kernel
theorem subd6_9_398 : subd6_9 [0, 1, -9] = true := by decide +kernel
theorem subd6_9_399 : subd6_9 [0, 1, -8] = true := by decide +kernel
theorem subd6_9_400 : subd6_9 [0, 1, -7] = true := by decide +kernel
theorem subd6_9_401 : subd6_9 [0, 1, -6] = true := by decide +kernel
theorem subd6_9_402 : subd6_9 [0, 1, -5] = true := by decide +kernel
theorem subd6_9_403 : subd6_9 [0, 1, -4] = true := by decide +kernel
theorem subd6_9_404 : subd6_9 [0, 1, -3] = true := by decide +kernel
theorem subd6_9_405 : subd6_9 [0, 1, -2] = true := by decide +kernel
theorem subd6_9_406 : subd6_9 [0, 1, -1] = true := by decide +kernel
theorem subd6_9_407 : subd6_9 [0, 1, 0] = true := by decide +kernel
theorem subd6_9_408 : subd6_9 [0, 1, 1] = true := by decide +kernel
theorem subd6_9_409 : subd6_9 [0, 1, 2] = true := by decide +kernel
theorem subd6_9_410 : subd6_9 [0, 1, 3] = true := by decide +kernel
theorem subd6_9_411 : subd6_9 [0, 1, 4] = true := by decide +kernel
theorem subd6_9_412 : subd6_9 [0, 1, 5] = true := by decide +kernel
theorem subd6_9_413 : subd6_9 [0, 1, 6] = true := by decide +kernel
theorem subd6_9_414 : subd6_9 [0, 1, 7] = true := by decide +kernel
theorem subd6_9_415 : subd6_9 [0, 2, -9] = true := by decide +kernel
theorem sbd6_9_12 : ∀ q ∈ blkd6_9_12, subd6_9 q = true := by
  unfold blkd6_9_12
  exact List.forall_mem_cons.2 ⟨subd6_9_384, List.forall_mem_cons.2 ⟨subd6_9_385, List.forall_mem_cons.2 ⟨subd6_9_386, List.forall_mem_cons.2 ⟨subd6_9_387, List.forall_mem_cons.2 ⟨subd6_9_388, List.forall_mem_cons.2 ⟨subd6_9_389, List.forall_mem_cons.2 ⟨subd6_9_390, List.forall_mem_cons.2 ⟨subd6_9_391, List.forall_mem_cons.2 ⟨subd6_9_392, List.forall_mem_cons.2 ⟨subd6_9_393, List.forall_mem_cons.2 ⟨subd6_9_394, List.forall_mem_cons.2 ⟨subd6_9_395, List.forall_mem_cons.2 ⟨subd6_9_396, List.forall_mem_cons.2 ⟨subd6_9_397, List.forall_mem_cons.2 ⟨subd6_9_398, List.forall_mem_cons.2 ⟨subd6_9_399, List.forall_mem_cons.2 ⟨subd6_9_400, List.forall_mem_cons.2 ⟨subd6_9_401, List.forall_mem_cons.2 ⟨subd6_9_402, List.forall_mem_cons.2 ⟨subd6_9_403, List.forall_mem_cons.2 ⟨subd6_9_404, List.forall_mem_cons.2 ⟨subd6_9_405, List.forall_mem_cons.2 ⟨subd6_9_406, List.forall_mem_cons.2 ⟨subd6_9_407, List.forall_mem_cons.2 ⟨subd6_9_408, List.forall_mem_cons.2 ⟨subd6_9_409, List.forall_mem_cons.2 ⟨subd6_9_410, List.forall_mem_cons.2 ⟨subd6_9_411, List.forall_mem_cons.2 ⟨subd6_9_412, List.forall_mem_cons.2 ⟨subd6_9_413, List.forall_mem_cons.2 ⟨subd6_9_414, List.forall_mem_cons.2 ⟨subd6_9_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_416 : subd6_9 [0, 2, -8] = true := by decide +kernel
theorem subd6_9_417 : subd6_9 [0, 2, -7] = true := by decide +kernel
theorem subd6_9_418 : subd6_9 [0, 2, -6] = true := by decide +kernel
theorem subd6_9_419 : subd6_9 [0, 2, -5] = true := by decide +kernel
theorem subd6_9_420 : subd6_9 [0, 2, -4] = true := by decide +kernel
theorem subd6_9_421 : subd6_9 [0, 2, -3] = true := by decide +kernel
theorem subd6_9_422 : subd6_9 [0, 2, -2] = true := by decide +kernel
theorem subd6_9_423 : subd6_9 [0, 2, -1] = true := by decide +kernel
theorem subd6_9_424 : subd6_9 [0, 2, 0] = true := by decide +kernel
theorem subd6_9_425 : subd6_9 [0, 2, 1] = true := by decide +kernel
theorem subd6_9_426 : subd6_9 [0, 2, 2] = true := by decide +kernel
theorem subd6_9_427 : subd6_9 [0, 2, 3] = true := by decide +kernel
theorem subd6_9_428 : subd6_9 [0, 2, 4] = true := by decide +kernel
theorem subd6_9_429 : subd6_9 [0, 2, 5] = true := by decide +kernel
theorem subd6_9_430 : subd6_9 [0, 2, 6] = true := by decide +kernel
theorem subd6_9_431 : subd6_9 [0, 2, 7] = true := by decide +kernel
theorem subd6_9_432 : subd6_9 [0, 3, -9] = true := by decide +kernel
theorem subd6_9_433 : subd6_9 [0, 3, -8] = true := by decide +kernel
theorem subd6_9_434 : subd6_9 [0, 3, -7] = true := by decide +kernel
theorem subd6_9_435 : subd6_9 [0, 3, -6] = true := by decide +kernel
theorem subd6_9_436 : subd6_9 [0, 3, -5] = true := by decide +kernel
theorem subd6_9_437 : subd6_9 [0, 3, -4] = true := by decide +kernel
theorem subd6_9_438 : subd6_9 [0, 3, -3] = true := by decide +kernel
theorem subd6_9_439 : subd6_9 [0, 3, -2] = true := by decide +kernel
theorem subd6_9_440 : subd6_9 [0, 3, -1] = true := by decide +kernel
theorem subd6_9_441 : subd6_9 [0, 3, 0] = true := by decide +kernel
theorem subd6_9_442 : subd6_9 [0, 3, 1] = true := by decide +kernel
theorem subd6_9_443 : subd6_9 [0, 3, 2] = true := by decide +kernel
theorem subd6_9_444 : subd6_9 [0, 3, 3] = true := by decide +kernel
theorem subd6_9_445 : subd6_9 [0, 3, 4] = true := by decide +kernel
theorem subd6_9_446 : subd6_9 [0, 3, 5] = true := by decide +kernel
theorem subd6_9_447 : subd6_9 [0, 3, 6] = true := by decide +kernel
theorem sbd6_9_13 : ∀ q ∈ blkd6_9_13, subd6_9 q = true := by
  unfold blkd6_9_13
  exact List.forall_mem_cons.2 ⟨subd6_9_416, List.forall_mem_cons.2 ⟨subd6_9_417, List.forall_mem_cons.2 ⟨subd6_9_418, List.forall_mem_cons.2 ⟨subd6_9_419, List.forall_mem_cons.2 ⟨subd6_9_420, List.forall_mem_cons.2 ⟨subd6_9_421, List.forall_mem_cons.2 ⟨subd6_9_422, List.forall_mem_cons.2 ⟨subd6_9_423, List.forall_mem_cons.2 ⟨subd6_9_424, List.forall_mem_cons.2 ⟨subd6_9_425, List.forall_mem_cons.2 ⟨subd6_9_426, List.forall_mem_cons.2 ⟨subd6_9_427, List.forall_mem_cons.2 ⟨subd6_9_428, List.forall_mem_cons.2 ⟨subd6_9_429, List.forall_mem_cons.2 ⟨subd6_9_430, List.forall_mem_cons.2 ⟨subd6_9_431, List.forall_mem_cons.2 ⟨subd6_9_432, List.forall_mem_cons.2 ⟨subd6_9_433, List.forall_mem_cons.2 ⟨subd6_9_434, List.forall_mem_cons.2 ⟨subd6_9_435, List.forall_mem_cons.2 ⟨subd6_9_436, List.forall_mem_cons.2 ⟨subd6_9_437, List.forall_mem_cons.2 ⟨subd6_9_438, List.forall_mem_cons.2 ⟨subd6_9_439, List.forall_mem_cons.2 ⟨subd6_9_440, List.forall_mem_cons.2 ⟨subd6_9_441, List.forall_mem_cons.2 ⟨subd6_9_442, List.forall_mem_cons.2 ⟨subd6_9_443, List.forall_mem_cons.2 ⟨subd6_9_444, List.forall_mem_cons.2 ⟨subd6_9_445, List.forall_mem_cons.2 ⟨subd6_9_446, List.forall_mem_cons.2 ⟨subd6_9_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_448 : subd6_9 [0, 4] = true := by decide +kernel
theorem subd6_9_449 : subd6_9 [0, 5] = true := by decide +kernel
theorem subd6_9_450 : subd6_9 [1, -6] = true := by decide +kernel
theorem subd6_9_451 : subd6_9 [1, -5] = true := by decide +kernel
theorem subd6_9_452 : subd6_9 [1, -4] = true := by decide +kernel
theorem subd6_9_453 : subd6_9 [1, -3, -6] = true := by decide +kernel
theorem subd6_9_454 : subd6_9 [1, -3, -5] = true := by decide +kernel
theorem subd6_9_455 : subd6_9 [1, -3, -4] = true := by decide +kernel
theorem subd6_9_456 : subd6_9 [1, -3, -3] = true := by decide +kernel
theorem subd6_9_457 : subd6_9 [1, -3, -2] = true := by decide +kernel
theorem subd6_9_458 : subd6_9 [1, -3, -1] = true := by decide +kernel
theorem subd6_9_459 : subd6_9 [1, -3, 0] = true := by decide +kernel
theorem subd6_9_460 : subd6_9 [1, -3, 1] = true := by decide +kernel
theorem subd6_9_461 : subd6_9 [1, -3, 2] = true := by decide +kernel
theorem subd6_9_462 : subd6_9 [1, -3, 3] = true := by decide +kernel
theorem subd6_9_463 : subd6_9 [1, -3, 4] = true := by decide +kernel
theorem subd6_9_464 : subd6_9 [1, -3, 5] = true := by decide +kernel
theorem subd6_9_465 : subd6_9 [1, -3, 6] = true := by decide +kernel
theorem subd6_9_466 : subd6_9 [1, -3, 7] = true := by decide +kernel
theorem subd6_9_467 : subd6_9 [1, -3, 8] = true := by decide +kernel
theorem subd6_9_468 : subd6_9 [1, -2, -7] = true := by decide +kernel
theorem subd6_9_469 : subd6_9 [1, -2, -6] = true := by decide +kernel
theorem subd6_9_470 : subd6_9 [1, -2, -5] = true := by decide +kernel
theorem subd6_9_471 : subd6_9 [1, -2, -4] = true := by decide +kernel
theorem subd6_9_472 : subd6_9 [1, -2, -3] = true := by decide +kernel
theorem subd6_9_473 : subd6_9 [1, -2, -2] = true := by decide +kernel
theorem subd6_9_474 : subd6_9 [1, -2, -1] = true := by decide +kernel
theorem subd6_9_475 : subd6_9 [1, -2, 0] = true := by decide +kernel
theorem subd6_9_476 : subd6_9 [1, -2, 1] = true := by decide +kernel
theorem subd6_9_477 : subd6_9 [1, -2, 2] = true := by decide +kernel
theorem subd6_9_478 : subd6_9 [1, -2, 3] = true := by decide +kernel
theorem subd6_9_479 : subd6_9 [1, -2, 4] = true := by decide +kernel
theorem sbd6_9_14 : ∀ q ∈ blkd6_9_14, subd6_9 q = true := by
  unfold blkd6_9_14
  exact List.forall_mem_cons.2 ⟨subd6_9_448, List.forall_mem_cons.2 ⟨subd6_9_449, List.forall_mem_cons.2 ⟨subd6_9_450, List.forall_mem_cons.2 ⟨subd6_9_451, List.forall_mem_cons.2 ⟨subd6_9_452, List.forall_mem_cons.2 ⟨subd6_9_453, List.forall_mem_cons.2 ⟨subd6_9_454, List.forall_mem_cons.2 ⟨subd6_9_455, List.forall_mem_cons.2 ⟨subd6_9_456, List.forall_mem_cons.2 ⟨subd6_9_457, List.forall_mem_cons.2 ⟨subd6_9_458, List.forall_mem_cons.2 ⟨subd6_9_459, List.forall_mem_cons.2 ⟨subd6_9_460, List.forall_mem_cons.2 ⟨subd6_9_461, List.forall_mem_cons.2 ⟨subd6_9_462, List.forall_mem_cons.2 ⟨subd6_9_463, List.forall_mem_cons.2 ⟨subd6_9_464, List.forall_mem_cons.2 ⟨subd6_9_465, List.forall_mem_cons.2 ⟨subd6_9_466, List.forall_mem_cons.2 ⟨subd6_9_467, List.forall_mem_cons.2 ⟨subd6_9_468, List.forall_mem_cons.2 ⟨subd6_9_469, List.forall_mem_cons.2 ⟨subd6_9_470, List.forall_mem_cons.2 ⟨subd6_9_471, List.forall_mem_cons.2 ⟨subd6_9_472, List.forall_mem_cons.2 ⟨subd6_9_473, List.forall_mem_cons.2 ⟨subd6_9_474, List.forall_mem_cons.2 ⟨subd6_9_475, List.forall_mem_cons.2 ⟨subd6_9_476, List.forall_mem_cons.2 ⟨subd6_9_477, List.forall_mem_cons.2 ⟨subd6_9_478, List.forall_mem_cons.2 ⟨subd6_9_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_480 : subd6_9 [1, -2, 5] = true := by decide +kernel
theorem subd6_9_481 : subd6_9 [1, -2, 6] = true := by decide +kernel
theorem subd6_9_482 : subd6_9 [1, -2, 7] = true := by decide +kernel
theorem subd6_9_483 : subd6_9 [1, -2, 8] = true := by decide +kernel
theorem subd6_9_484 : subd6_9 [1, -1, -8] = true := by decide +kernel
theorem subd6_9_485 : subd6_9 [1, -1, -7] = true := by decide +kernel
theorem subd6_9_486 : subd6_9 [1, -1, -6] = true := by decide +kernel
theorem subd6_9_487 : subd6_9 [1, -1, -5] = true := by decide +kernel
theorem subd6_9_488 : subd6_9 [1, -1, -4] = true := by decide +kernel
theorem subd6_9_489 : subd6_9 [1, -1, -3] = true := by decide +kernel
theorem subd6_9_490 : subd6_9 [1, -1, -2] = true := by decide +kernel
theorem subd6_9_491 : subd6_9 [1, -1, -1] = true := by decide +kernel
theorem subd6_9_492 : subd6_9 [1, -1, 0] = true := by decide +kernel
theorem subd6_9_493 : subd6_9 [1, -1, 1] = true := by decide +kernel
theorem subd6_9_494 : subd6_9 [1, -1, 2] = true := by decide +kernel
theorem subd6_9_495 : subd6_9 [1, -1, 3] = true := by decide +kernel
theorem subd6_9_496 : subd6_9 [1, -1, 4] = true := by decide +kernel
theorem subd6_9_497 : subd6_9 [1, -1, 5] = true := by decide +kernel
theorem subd6_9_498 : subd6_9 [1, -1, 6] = true := by decide +kernel
theorem subd6_9_499 : subd6_9 [1, -1, 7] = true := by decide +kernel
theorem subd6_9_500 : subd6_9 [1, -1, 8] = true := by decide +kernel
theorem subd6_9_501 : subd6_9 [1, 0, -8] = true := by decide +kernel
theorem subd6_9_502 : subd6_9 [1, 0, -7] = true := by decide +kernel
theorem subd6_9_503 : subd6_9 [1, 0, -6] = true := by decide +kernel
theorem subd6_9_504 : subd6_9 [1, 0, -5] = true := by decide +kernel
theorem subd6_9_505 : subd6_9 [1, 0, -4] = true := by decide +kernel
theorem subd6_9_506 : subd6_9 [1, 0, -3] = true := by decide +kernel
theorem subd6_9_507 : subd6_9 [1, 0, -2] = true := by decide +kernel
theorem subd6_9_508 : subd6_9 [1, 0, -1] = true := by decide +kernel
theorem subd6_9_509 : subd6_9 [1, 0, 0] = true := by decide +kernel
theorem subd6_9_510 : subd6_9 [1, 0, 1] = true := by decide +kernel
theorem subd6_9_511 : subd6_9 [1, 0, 2] = true := by decide +kernel
theorem sbd6_9_15 : ∀ q ∈ blkd6_9_15, subd6_9 q = true := by
  unfold blkd6_9_15
  exact List.forall_mem_cons.2 ⟨subd6_9_480, List.forall_mem_cons.2 ⟨subd6_9_481, List.forall_mem_cons.2 ⟨subd6_9_482, List.forall_mem_cons.2 ⟨subd6_9_483, List.forall_mem_cons.2 ⟨subd6_9_484, List.forall_mem_cons.2 ⟨subd6_9_485, List.forall_mem_cons.2 ⟨subd6_9_486, List.forall_mem_cons.2 ⟨subd6_9_487, List.forall_mem_cons.2 ⟨subd6_9_488, List.forall_mem_cons.2 ⟨subd6_9_489, List.forall_mem_cons.2 ⟨subd6_9_490, List.forall_mem_cons.2 ⟨subd6_9_491, List.forall_mem_cons.2 ⟨subd6_9_492, List.forall_mem_cons.2 ⟨subd6_9_493, List.forall_mem_cons.2 ⟨subd6_9_494, List.forall_mem_cons.2 ⟨subd6_9_495, List.forall_mem_cons.2 ⟨subd6_9_496, List.forall_mem_cons.2 ⟨subd6_9_497, List.forall_mem_cons.2 ⟨subd6_9_498, List.forall_mem_cons.2 ⟨subd6_9_499, List.forall_mem_cons.2 ⟨subd6_9_500, List.forall_mem_cons.2 ⟨subd6_9_501, List.forall_mem_cons.2 ⟨subd6_9_502, List.forall_mem_cons.2 ⟨subd6_9_503, List.forall_mem_cons.2 ⟨subd6_9_504, List.forall_mem_cons.2 ⟨subd6_9_505, List.forall_mem_cons.2 ⟨subd6_9_506, List.forall_mem_cons.2 ⟨subd6_9_507, List.forall_mem_cons.2 ⟨subd6_9_508, List.forall_mem_cons.2 ⟨subd6_9_509, List.forall_mem_cons.2 ⟨subd6_9_510, List.forall_mem_cons.2 ⟨subd6_9_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_512 : subd6_9 [1, 0, 3] = true := by decide +kernel
theorem subd6_9_513 : subd6_9 [1, 0, 4] = true := by decide +kernel
theorem subd6_9_514 : subd6_9 [1, 0, 5] = true := by decide +kernel
theorem subd6_9_515 : subd6_9 [1, 0, 6] = true := by decide +kernel
theorem subd6_9_516 : subd6_9 [1, 0, 7] = true := by decide +kernel
theorem subd6_9_517 : subd6_9 [1, 0, 8] = true := by decide +kernel
theorem subd6_9_518 : subd6_9 [1, 1, -8] = true := by decide +kernel
theorem subd6_9_519 : subd6_9 [1, 1, -7] = true := by decide +kernel
theorem subd6_9_520 : subd6_9 [1, 1, -6] = true := by decide +kernel
theorem subd6_9_521 : subd6_9 [1, 1, -5] = true := by decide +kernel
theorem subd6_9_522 : subd6_9 [1, 1, -4] = true := by decide +kernel
theorem subd6_9_523 : subd6_9 [1, 1, -3] = true := by decide +kernel
theorem subd6_9_524 : subd6_9 [1, 1, -2] = true := by decide +kernel
theorem subd6_9_525 : subd6_9 [1, 1, -1] = true := by decide +kernel
theorem subd6_9_526 : subd6_9 [1, 1, 0] = true := by decide +kernel
theorem subd6_9_527 : subd6_9 [1, 1, 1] = true := by decide +kernel
theorem subd6_9_528 : subd6_9 [1, 1, 2] = true := by decide +kernel
theorem subd6_9_529 : subd6_9 [1, 1, 3] = true := by decide +kernel
theorem subd6_9_530 : subd6_9 [1, 1, 4] = true := by decide +kernel
theorem subd6_9_531 : subd6_9 [1, 1, 5] = true := by decide +kernel
theorem subd6_9_532 : subd6_9 [1, 1, 6] = true := by decide +kernel
theorem subd6_9_533 : subd6_9 [1, 1, 7] = true := by decide +kernel
theorem subd6_9_534 : subd6_9 [1, 1, 8] = true := by decide +kernel
theorem subd6_9_535 : subd6_9 [1, 2, -8] = true := by decide +kernel
theorem subd6_9_536 : subd6_9 [1, 2, -7] = true := by decide +kernel
theorem subd6_9_537 : subd6_9 [1, 2, -6] = true := by decide +kernel
theorem subd6_9_538 : subd6_9 [1, 2, -5] = true := by decide +kernel
theorem subd6_9_539 : subd6_9 [1, 2, -4] = true := by decide +kernel
theorem subd6_9_540 : subd6_9 [1, 2, -3] = true := by decide +kernel
theorem subd6_9_541 : subd6_9 [1, 2, -2] = true := by decide +kernel
theorem subd6_9_542 : subd6_9 [1, 2, -1] = true := by decide +kernel
theorem subd6_9_543 : subd6_9 [1, 2, 0] = true := by decide +kernel
theorem sbd6_9_16 : ∀ q ∈ blkd6_9_16, subd6_9 q = true := by
  unfold blkd6_9_16
  exact List.forall_mem_cons.2 ⟨subd6_9_512, List.forall_mem_cons.2 ⟨subd6_9_513, List.forall_mem_cons.2 ⟨subd6_9_514, List.forall_mem_cons.2 ⟨subd6_9_515, List.forall_mem_cons.2 ⟨subd6_9_516, List.forall_mem_cons.2 ⟨subd6_9_517, List.forall_mem_cons.2 ⟨subd6_9_518, List.forall_mem_cons.2 ⟨subd6_9_519, List.forall_mem_cons.2 ⟨subd6_9_520, List.forall_mem_cons.2 ⟨subd6_9_521, List.forall_mem_cons.2 ⟨subd6_9_522, List.forall_mem_cons.2 ⟨subd6_9_523, List.forall_mem_cons.2 ⟨subd6_9_524, List.forall_mem_cons.2 ⟨subd6_9_525, List.forall_mem_cons.2 ⟨subd6_9_526, List.forall_mem_cons.2 ⟨subd6_9_527, List.forall_mem_cons.2 ⟨subd6_9_528, List.forall_mem_cons.2 ⟨subd6_9_529, List.forall_mem_cons.2 ⟨subd6_9_530, List.forall_mem_cons.2 ⟨subd6_9_531, List.forall_mem_cons.2 ⟨subd6_9_532, List.forall_mem_cons.2 ⟨subd6_9_533, List.forall_mem_cons.2 ⟨subd6_9_534, List.forall_mem_cons.2 ⟨subd6_9_535, List.forall_mem_cons.2 ⟨subd6_9_536, List.forall_mem_cons.2 ⟨subd6_9_537, List.forall_mem_cons.2 ⟨subd6_9_538, List.forall_mem_cons.2 ⟨subd6_9_539, List.forall_mem_cons.2 ⟨subd6_9_540, List.forall_mem_cons.2 ⟨subd6_9_541, List.forall_mem_cons.2 ⟨subd6_9_542, List.forall_mem_cons.2 ⟨subd6_9_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
