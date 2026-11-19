import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_14_64 : subd8_14 [-2, 1, 6] = true := by decide +kernel
theorem subd8_14_65 : subd8_14 [-2, 2, -7] = true := by decide +kernel
theorem subd8_14_66 : subd8_14 [-2, 2, -6] = true := by decide +kernel
theorem subd8_14_67 : subd8_14 [-2, 2, -5] = true := by decide +kernel
theorem subd8_14_68 : subd8_14 [-2, 2, -4] = true := by decide +kernel
theorem subd8_14_69 : subd8_14 [-2, 2, -3] = true := by decide +kernel
theorem subd8_14_70 : subd8_14 [-2, 2, -2] = true := by decide +kernel
theorem subd8_14_71 : subd8_14 [-2, 2, -1] = true := by decide +kernel
theorem subd8_14_72 : subd8_14 [-2, 2, 0] = true := by decide +kernel
theorem subd8_14_73 : subd8_14 [-2, 2, 1] = true := by decide +kernel
theorem subd8_14_74 : subd8_14 [-2, 2, 2] = true := by decide +kernel
theorem subd8_14_75 : subd8_14 [-2, 2, 3] = true := by decide +kernel
theorem subd8_14_76 : subd8_14 [-2, 2, 4] = true := by decide +kernel
theorem subd8_14_77 : subd8_14 [-2, 2, 5] = true := by decide +kernel
theorem subd8_14_78 : subd8_14 [-2, 3] = true := by decide +kernel
theorem subd8_14_79 : subd8_14 [-2, 4] = true := by decide +kernel
theorem subd8_14_80 : subd8_14 [-1, -5] = true := by decide +kernel
theorem subd8_14_81 : subd8_14 [-1, -4] = true := by decide +kernel
theorem subd8_14_82 : subd8_14 [-1, -3] = true := by decide +kernel
theorem subd8_14_83 : subd8_14 [-1, -2, -7] = true := by decide +kernel
theorem subd8_14_84 : subd8_14 [-1, -2, -6] = true := by decide +kernel
theorem subd8_14_85 : subd8_14 [-1, -2, -5] = true := by decide +kernel
theorem subd8_14_86 : subd8_14 [-1, -2, -4] = true := by decide +kernel
theorem subd8_14_87 : subd8_14 [-1, -2, -3] = true := by decide +kernel
theorem subd8_14_88 : subd8_14 [-1, -2, -2] = true := by decide +kernel
theorem subd8_14_89 : subd8_14 [-1, -2, -1] = true := by decide +kernel
theorem subd8_14_90 : subd8_14 [-1, -2, 0] = true := by decide +kernel
theorem subd8_14_91 : subd8_14 [-1, -2, 1] = true := by decide +kernel
theorem subd8_14_92 : subd8_14 [-1, -2, 2] = true := by decide +kernel
theorem subd8_14_93 : subd8_14 [-1, -2, 3] = true := by decide +kernel
theorem subd8_14_94 : subd8_14 [-1, -2, 4] = true := by decide +kernel
theorem subd8_14_95 : subd8_14 [-1, -2, 5] = true := by decide +kernel
theorem sbd8_14_2 : ∀ q ∈ blkd8_14_2, subd8_14 q = true := by
  unfold blkd8_14_2
  exact List.forall_mem_cons.2 ⟨subd8_14_64, List.forall_mem_cons.2 ⟨subd8_14_65, List.forall_mem_cons.2 ⟨subd8_14_66, List.forall_mem_cons.2 ⟨subd8_14_67, List.forall_mem_cons.2 ⟨subd8_14_68, List.forall_mem_cons.2 ⟨subd8_14_69, List.forall_mem_cons.2 ⟨subd8_14_70, List.forall_mem_cons.2 ⟨subd8_14_71, List.forall_mem_cons.2 ⟨subd8_14_72, List.forall_mem_cons.2 ⟨subd8_14_73, List.forall_mem_cons.2 ⟨subd8_14_74, List.forall_mem_cons.2 ⟨subd8_14_75, List.forall_mem_cons.2 ⟨subd8_14_76, List.forall_mem_cons.2 ⟨subd8_14_77, List.forall_mem_cons.2 ⟨subd8_14_78, List.forall_mem_cons.2 ⟨subd8_14_79, List.forall_mem_cons.2 ⟨subd8_14_80, List.forall_mem_cons.2 ⟨subd8_14_81, List.forall_mem_cons.2 ⟨subd8_14_82, List.forall_mem_cons.2 ⟨subd8_14_83, List.forall_mem_cons.2 ⟨subd8_14_84, List.forall_mem_cons.2 ⟨subd8_14_85, List.forall_mem_cons.2 ⟨subd8_14_86, List.forall_mem_cons.2 ⟨subd8_14_87, List.forall_mem_cons.2 ⟨subd8_14_88, List.forall_mem_cons.2 ⟨subd8_14_89, List.forall_mem_cons.2 ⟨subd8_14_90, List.forall_mem_cons.2 ⟨subd8_14_91, List.forall_mem_cons.2 ⟨subd8_14_92, List.forall_mem_cons.2 ⟨subd8_14_93, List.forall_mem_cons.2 ⟨subd8_14_94, List.forall_mem_cons.2 ⟨subd8_14_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_14_96 : subd8_14 [-1, -2, 6] = true := by decide +kernel
theorem subd8_14_97 : subd8_14 [-1, -1, -8] = true := by decide +kernel
theorem subd8_14_98 : subd8_14 [-1, -1, -7] = true := by decide +kernel
theorem subd8_14_99 : subd8_14 [-1, -1, -6] = true := by decide +kernel
theorem subd8_14_100 : subd8_14 [-1, -1, -5] = true := by decide +kernel
theorem subd8_14_101 : subd8_14 [-1, -1, -4] = true := by decide +kernel
theorem subd8_14_102 : subd8_14 [-1, -1, -3] = true := by decide +kernel
theorem subd8_14_103 : subd8_14 [-1, -1, -2] = true := by decide +kernel
theorem subd8_14_104 : subd8_14 [-1, -1, -1] = true := by decide +kernel
theorem subd8_14_105 : subd8_14 [-1, -1, 0] = true := by decide +kernel
theorem subd8_14_106 : subd8_14 [-1, -1, 1] = true := by decide +kernel
theorem subd8_14_107 : subd8_14 [-1, -1, 2] = true := by decide +kernel
theorem subd8_14_108 : subd8_14 [-1, -1, 3] = true := by decide +kernel
theorem subd8_14_109 : subd8_14 [-1, -1, 4] = true := by decide +kernel
theorem subd8_14_110 : subd8_14 [-1, -1, 5] = true := by decide +kernel
theorem subd8_14_111 : subd8_14 [-1, -1, 6] = true := by decide +kernel
theorem subd8_14_112 : subd8_14 [-1, 0, -8] = true := by decide +kernel
theorem subd8_14_113 : subd8_14 [-1, 0, -7] = true := by decide +kernel
theorem subd8_14_114 : subd8_14 [-1, 0, -6] = true := by decide +kernel
theorem subd8_14_115 : subd8_14 [-1, 0, -5] = true := by decide +kernel
theorem subd8_14_116 : subd8_14 [-1, 0, -4] = true := by decide +kernel
theorem subd8_14_117 : subd8_14 [-1, 0, -3] = true := by decide +kernel
theorem subd8_14_118 : subd8_14 [-1, 0, -2] = true := by decide +kernel
theorem subd8_14_119 : subd8_14 [-1, 0, -1] = true := by decide +kernel
theorem subd8_14_120 : subd8_14 [-1, 0, 0] = true := by decide +kernel
theorem subd8_14_121 : subd8_14 [-1, 0, 1] = true := by decide +kernel
theorem subd8_14_122 : subd8_14 [-1, 0, 2] = true := by decide +kernel
theorem subd8_14_123 : subd8_14 [-1, 0, 3] = true := by decide +kernel
theorem subd8_14_124 : subd8_14 [-1, 0, 4] = true := by decide +kernel
theorem subd8_14_125 : subd8_14 [-1, 0, 5] = true := by decide +kernel
theorem subd8_14_126 : subd8_14 [-1, 0, 6] = true := by decide +kernel
theorem subd8_14_127 : subd8_14 [-1, 0, 7] = true := by decide +kernel
theorem sbd8_14_3 : ∀ q ∈ blkd8_14_3, subd8_14 q = true := by
  unfold blkd8_14_3
  exact List.forall_mem_cons.2 ⟨subd8_14_96, List.forall_mem_cons.2 ⟨subd8_14_97, List.forall_mem_cons.2 ⟨subd8_14_98, List.forall_mem_cons.2 ⟨subd8_14_99, List.forall_mem_cons.2 ⟨subd8_14_100, List.forall_mem_cons.2 ⟨subd8_14_101, List.forall_mem_cons.2 ⟨subd8_14_102, List.forall_mem_cons.2 ⟨subd8_14_103, List.forall_mem_cons.2 ⟨subd8_14_104, List.forall_mem_cons.2 ⟨subd8_14_105, List.forall_mem_cons.2 ⟨subd8_14_106, List.forall_mem_cons.2 ⟨subd8_14_107, List.forall_mem_cons.2 ⟨subd8_14_108, List.forall_mem_cons.2 ⟨subd8_14_109, List.forall_mem_cons.2 ⟨subd8_14_110, List.forall_mem_cons.2 ⟨subd8_14_111, List.forall_mem_cons.2 ⟨subd8_14_112, List.forall_mem_cons.2 ⟨subd8_14_113, List.forall_mem_cons.2 ⟨subd8_14_114, List.forall_mem_cons.2 ⟨subd8_14_115, List.forall_mem_cons.2 ⟨subd8_14_116, List.forall_mem_cons.2 ⟨subd8_14_117, List.forall_mem_cons.2 ⟨subd8_14_118, List.forall_mem_cons.2 ⟨subd8_14_119, List.forall_mem_cons.2 ⟨subd8_14_120, List.forall_mem_cons.2 ⟨subd8_14_121, List.forall_mem_cons.2 ⟨subd8_14_122, List.forall_mem_cons.2 ⟨subd8_14_123, List.forall_mem_cons.2 ⟨subd8_14_124, List.forall_mem_cons.2 ⟨subd8_14_125, List.forall_mem_cons.2 ⟨subd8_14_126, List.forall_mem_cons.2 ⟨subd8_14_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_14_128 : subd8_14 [-1, 1, -8] = true := by decide +kernel
theorem subd8_14_129 : subd8_14 [-1, 1, -7] = true := by decide +kernel
theorem subd8_14_130 : subd8_14 [-1, 1, -6] = true := by decide +kernel
theorem subd8_14_131 : subd8_14 [-1, 1, -5] = true := by decide +kernel
theorem subd8_14_132 : subd8_14 [-1, 1, -4] = true := by decide +kernel
theorem subd8_14_133 : subd8_14 [-1, 1, -3] = true := by decide +kernel
theorem subd8_14_134 : subd8_14 [-1, 1, -2] = true := by decide +kernel
theorem subd8_14_135 : subd8_14 [-1, 1, -1] = true := by decide +kernel
theorem subd8_14_136 : subd8_14 [-1, 1, 0] = true := by decide +kernel
theorem subd8_14_137 : subd8_14 [-1, 1, 1] = true := by decide +kernel
theorem subd8_14_138 : subd8_14 [-1, 1, 2] = true := by decide +kernel
theorem subd8_14_139 : subd8_14 [-1, 1, 3] = true := by decide +kernel
theorem subd8_14_140 : subd8_14 [-1, 1, 4] = true := by decide +kernel
theorem subd8_14_141 : subd8_14 [-1, 1, 5] = true := by decide +kernel
theorem subd8_14_142 : subd8_14 [-1, 1, 6] = true := by decide +kernel
theorem subd8_14_143 : subd8_14 [-1, 2, -7] = true := by decide +kernel
theorem subd8_14_144 : subd8_14 [-1, 2, -6] = true := by decide +kernel
theorem subd8_14_145 : subd8_14 [-1, 2, -5] = true := by decide +kernel
theorem subd8_14_146 : subd8_14 [-1, 2, -4] = true := by decide +kernel
theorem subd8_14_147 : subd8_14 [-1, 2, -3] = true := by decide +kernel
theorem subd8_14_148 : subd8_14 [-1, 2, -2] = true := by decide +kernel
theorem subd8_14_149 : subd8_14 [-1, 2, -1] = true := by decide +kernel
theorem subd8_14_150 : subd8_14 [-1, 2, 0] = true := by decide +kernel
theorem subd8_14_151 : subd8_14 [-1, 2, 1] = true := by decide +kernel
theorem subd8_14_152 : subd8_14 [-1, 2, 2] = true := by decide +kernel
theorem subd8_14_153 : subd8_14 [-1, 2, 3] = true := by decide +kernel
theorem subd8_14_154 : subd8_14 [-1, 2, 4] = true := by decide +kernel
theorem subd8_14_155 : subd8_14 [-1, 2, 5] = true := by decide +kernel
theorem subd8_14_156 : subd8_14 [-1, 2, 6] = true := by decide +kernel
theorem subd8_14_157 : subd8_14 [-1, 3] = true := by decide +kernel
theorem subd8_14_158 : subd8_14 [-1, 4] = true := by decide +kernel
theorem subd8_14_159 : subd8_14 [0, -5] = true := by decide +kernel
theorem sbd8_14_4 : ∀ q ∈ blkd8_14_4, subd8_14 q = true := by
  unfold blkd8_14_4
  exact List.forall_mem_cons.2 ⟨subd8_14_128, List.forall_mem_cons.2 ⟨subd8_14_129, List.forall_mem_cons.2 ⟨subd8_14_130, List.forall_mem_cons.2 ⟨subd8_14_131, List.forall_mem_cons.2 ⟨subd8_14_132, List.forall_mem_cons.2 ⟨subd8_14_133, List.forall_mem_cons.2 ⟨subd8_14_134, List.forall_mem_cons.2 ⟨subd8_14_135, List.forall_mem_cons.2 ⟨subd8_14_136, List.forall_mem_cons.2 ⟨subd8_14_137, List.forall_mem_cons.2 ⟨subd8_14_138, List.forall_mem_cons.2 ⟨subd8_14_139, List.forall_mem_cons.2 ⟨subd8_14_140, List.forall_mem_cons.2 ⟨subd8_14_141, List.forall_mem_cons.2 ⟨subd8_14_142, List.forall_mem_cons.2 ⟨subd8_14_143, List.forall_mem_cons.2 ⟨subd8_14_144, List.forall_mem_cons.2 ⟨subd8_14_145, List.forall_mem_cons.2 ⟨subd8_14_146, List.forall_mem_cons.2 ⟨subd8_14_147, List.forall_mem_cons.2 ⟨subd8_14_148, List.forall_mem_cons.2 ⟨subd8_14_149, List.forall_mem_cons.2 ⟨subd8_14_150, List.forall_mem_cons.2 ⟨subd8_14_151, List.forall_mem_cons.2 ⟨subd8_14_152, List.forall_mem_cons.2 ⟨subd8_14_153, List.forall_mem_cons.2 ⟨subd8_14_154, List.forall_mem_cons.2 ⟨subd8_14_155, List.forall_mem_cons.2 ⟨subd8_14_156, List.forall_mem_cons.2 ⟨subd8_14_157, List.forall_mem_cons.2 ⟨subd8_14_158, List.forall_mem_cons.2 ⟨subd8_14_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_14_160 : subd8_14 [0, -4] = true := by decide +kernel
theorem subd8_14_161 : subd8_14 [0, -3] = true := by decide +kernel
theorem subd8_14_162 : subd8_14 [0, -2, -7] = true := by decide +kernel
theorem subd8_14_163 : subd8_14 [0, -2, -6] = true := by decide +kernel
theorem subd8_14_164 : subd8_14 [0, -2, -5] = true := by decide +kernel
theorem subd8_14_165 : subd8_14 [0, -2, -4] = true := by decide +kernel
theorem subd8_14_166 : subd8_14 [0, -2, -3] = true := by decide +kernel
theorem subd8_14_167 : subd8_14 [0, -2, -2] = true := by decide +kernel
theorem subd8_14_168 : subd8_14 [0, -2, -1] = true := by decide +kernel
theorem subd8_14_169 : subd8_14 [0, -2, 0] = true := by decide +kernel
theorem subd8_14_170 : subd8_14 [0, -2, 1] = true := by decide +kernel
theorem subd8_14_171 : subd8_14 [0, -2, 2] = true := by decide +kernel
theorem subd8_14_172 : subd8_14 [0, -2, 3] = true := by decide +kernel
theorem subd8_14_173 : subd8_14 [0, -2, 4] = true := by decide +kernel
theorem subd8_14_174 : subd8_14 [0, -2, 5] = true := by decide +kernel
theorem subd8_14_175 : subd8_14 [0, -2, 6] = true := by decide +kernel
theorem subd8_14_176 : subd8_14 [0, -1, -8] = true := by decide +kernel
theorem subd8_14_177 : subd8_14 [0, -1, -7] = true := by decide +kernel
theorem subd8_14_178 : subd8_14 [0, -1, -6] = true := by decide +kernel
theorem subd8_14_179 : subd8_14 [0, -1, -5] = true := by decide +kernel
theorem subd8_14_180 : subd8_14 [0, -1, -4] = true := by decide +kernel
theorem subd8_14_181 : subd8_14 [0, -1, -3] = true := by decide +kernel
theorem subd8_14_182 : subd8_14 [0, -1, -2] = true := by decide +kernel
theorem subd8_14_183 : subd8_14 [0, -1, -1] = true := by decide +kernel
theorem subd8_14_184 : subd8_14 [0, -1, 0] = true := by decide +kernel
theorem subd8_14_185 : subd8_14 [0, -1, 1] = true := by decide +kernel
theorem subd8_14_186 : subd8_14 [0, -1, 2] = true := by decide +kernel
theorem subd8_14_187 : subd8_14 [0, -1, 3] = true := by decide +kernel
theorem subd8_14_188 : subd8_14 [0, -1, 4] = true := by decide +kernel
theorem subd8_14_189 : subd8_14 [0, -1, 5] = true := by decide +kernel
theorem subd8_14_190 : subd8_14 [0, -1, 6] = true := by decide +kernel
theorem subd8_14_191 : subd8_14 [0, -1, 7] = true := by decide +kernel
theorem sbd8_14_5 : ∀ q ∈ blkd8_14_5, subd8_14 q = true := by
  unfold blkd8_14_5
  exact List.forall_mem_cons.2 ⟨subd8_14_160, List.forall_mem_cons.2 ⟨subd8_14_161, List.forall_mem_cons.2 ⟨subd8_14_162, List.forall_mem_cons.2 ⟨subd8_14_163, List.forall_mem_cons.2 ⟨subd8_14_164, List.forall_mem_cons.2 ⟨subd8_14_165, List.forall_mem_cons.2 ⟨subd8_14_166, List.forall_mem_cons.2 ⟨subd8_14_167, List.forall_mem_cons.2 ⟨subd8_14_168, List.forall_mem_cons.2 ⟨subd8_14_169, List.forall_mem_cons.2 ⟨subd8_14_170, List.forall_mem_cons.2 ⟨subd8_14_171, List.forall_mem_cons.2 ⟨subd8_14_172, List.forall_mem_cons.2 ⟨subd8_14_173, List.forall_mem_cons.2 ⟨subd8_14_174, List.forall_mem_cons.2 ⟨subd8_14_175, List.forall_mem_cons.2 ⟨subd8_14_176, List.forall_mem_cons.2 ⟨subd8_14_177, List.forall_mem_cons.2 ⟨subd8_14_178, List.forall_mem_cons.2 ⟨subd8_14_179, List.forall_mem_cons.2 ⟨subd8_14_180, List.forall_mem_cons.2 ⟨subd8_14_181, List.forall_mem_cons.2 ⟨subd8_14_182, List.forall_mem_cons.2 ⟨subd8_14_183, List.forall_mem_cons.2 ⟨subd8_14_184, List.forall_mem_cons.2 ⟨subd8_14_185, List.forall_mem_cons.2 ⟨subd8_14_186, List.forall_mem_cons.2 ⟨subd8_14_187, List.forall_mem_cons.2 ⟨subd8_14_188, List.forall_mem_cons.2 ⟨subd8_14_189, List.forall_mem_cons.2 ⟨subd8_14_190, List.forall_mem_cons.2 ⟨subd8_14_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_14_192 : subd8_14 [0, 0, -8] = true := by decide +kernel
theorem subd8_14_193 : subd8_14 [0, 0, -7] = true := by decide +kernel
theorem subd8_14_194 : subd8_14 [0, 0, -6] = true := by decide +kernel
theorem subd8_14_195 : subd8_14 [0, 0, -5] = true := by decide +kernel
theorem subd8_14_196 : subd8_14 [0, 0, -4] = true := by decide +kernel
theorem subd8_14_197 : subd8_14 [0, 0, -3] = true := by decide +kernel
theorem subd8_14_198 : subd8_14 [0, 0, -2] = true := by decide +kernel
theorem subd8_14_199 : subd8_14 [0, 0, -1] = true := by decide +kernel
theorem subd8_14_200 : subd8_14 [0, 0, 0] = true := by decide +kernel
theorem subd8_14_201 : subd8_14 [0, 0, 1] = true := by decide +kernel
theorem subd8_14_202 : subd8_14 [0, 0, 2] = true := by decide +kernel
theorem subd8_14_203 : subd8_14 [0, 0, 3] = true := by decide +kernel
theorem subd8_14_204 : subd8_14 [0, 0, 4] = true := by decide +kernel
theorem subd8_14_205 : subd8_14 [0, 0, 5] = true := by decide +kernel
theorem subd8_14_206 : subd8_14 [0, 0, 6] = true := by decide +kernel
theorem subd8_14_207 : subd8_14 [0, 0, 7] = true := by decide +kernel
theorem subd8_14_208 : subd8_14 [0, 1, -8] = true := by decide +kernel
theorem subd8_14_209 : subd8_14 [0, 1, -7] = true := by decide +kernel
theorem subd8_14_210 : subd8_14 [0, 1, -6] = true := by decide +kernel
theorem subd8_14_211 : subd8_14 [0, 1, -5] = true := by decide +kernel
theorem subd8_14_212 : subd8_14 [0, 1, -4] = true := by decide +kernel
theorem subd8_14_213 : subd8_14 [0, 1, -3] = true := by decide +kernel
theorem subd8_14_214 : subd8_14 [0, 1, -2] = true := by decide +kernel
theorem subd8_14_215 : subd8_14 [0, 1, -1] = true := by decide +kernel
theorem subd8_14_216 : subd8_14 [0, 1, 0] = true := by decide +kernel
theorem subd8_14_217 : subd8_14 [0, 1, 1] = true := by decide +kernel
theorem subd8_14_218 : subd8_14 [0, 1, 2] = true := by decide +kernel
theorem subd8_14_219 : subd8_14 [0, 1, 3] = true := by decide +kernel
theorem subd8_14_220 : subd8_14 [0, 1, 4] = true := by decide +kernel
theorem subd8_14_221 : subd8_14 [0, 1, 5] = true := by decide +kernel
theorem subd8_14_222 : subd8_14 [0, 1, 6] = true := by decide +kernel
theorem subd8_14_223 : subd8_14 [0, 1, 7] = true := by decide +kernel
theorem sbd8_14_6 : ∀ q ∈ blkd8_14_6, subd8_14 q = true := by
  unfold blkd8_14_6
  exact List.forall_mem_cons.2 ⟨subd8_14_192, List.forall_mem_cons.2 ⟨subd8_14_193, List.forall_mem_cons.2 ⟨subd8_14_194, List.forall_mem_cons.2 ⟨subd8_14_195, List.forall_mem_cons.2 ⟨subd8_14_196, List.forall_mem_cons.2 ⟨subd8_14_197, List.forall_mem_cons.2 ⟨subd8_14_198, List.forall_mem_cons.2 ⟨subd8_14_199, List.forall_mem_cons.2 ⟨subd8_14_200, List.forall_mem_cons.2 ⟨subd8_14_201, List.forall_mem_cons.2 ⟨subd8_14_202, List.forall_mem_cons.2 ⟨subd8_14_203, List.forall_mem_cons.2 ⟨subd8_14_204, List.forall_mem_cons.2 ⟨subd8_14_205, List.forall_mem_cons.2 ⟨subd8_14_206, List.forall_mem_cons.2 ⟨subd8_14_207, List.forall_mem_cons.2 ⟨subd8_14_208, List.forall_mem_cons.2 ⟨subd8_14_209, List.forall_mem_cons.2 ⟨subd8_14_210, List.forall_mem_cons.2 ⟨subd8_14_211, List.forall_mem_cons.2 ⟨subd8_14_212, List.forall_mem_cons.2 ⟨subd8_14_213, List.forall_mem_cons.2 ⟨subd8_14_214, List.forall_mem_cons.2 ⟨subd8_14_215, List.forall_mem_cons.2 ⟨subd8_14_216, List.forall_mem_cons.2 ⟨subd8_14_217, List.forall_mem_cons.2 ⟨subd8_14_218, List.forall_mem_cons.2 ⟨subd8_14_219, List.forall_mem_cons.2 ⟨subd8_14_220, List.forall_mem_cons.2 ⟨subd8_14_221, List.forall_mem_cons.2 ⟨subd8_14_222, List.forall_mem_cons.2 ⟨subd8_14_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_14_224 : subd8_14 [0, 2, -7] = true := by decide +kernel
theorem subd8_14_225 : subd8_14 [0, 2, -6] = true := by decide +kernel
theorem subd8_14_226 : subd8_14 [0, 2, -5] = true := by decide +kernel
theorem subd8_14_227 : subd8_14 [0, 2, -4] = true := by decide +kernel
theorem subd8_14_228 : subd8_14 [0, 2, -3] = true := by decide +kernel
theorem subd8_14_229 : subd8_14 [0, 2, -2] = true := by decide +kernel
theorem subd8_14_230 : subd8_14 [0, 2, -1] = true := by decide +kernel
theorem subd8_14_231 : subd8_14 [0, 2, 0] = true := by decide +kernel
theorem subd8_14_232 : subd8_14 [0, 2, 1] = true := by decide +kernel
theorem subd8_14_233 : subd8_14 [0, 2, 2] = true := by decide +kernel
theorem subd8_14_234 : subd8_14 [0, 2, 3] = true := by decide +kernel
theorem subd8_14_235 : subd8_14 [0, 2, 4] = true := by decide +kernel
theorem subd8_14_236 : subd8_14 [0, 2, 5] = true := by decide +kernel
theorem subd8_14_237 : subd8_14 [0, 2, 6] = true := by decide +kernel
theorem subd8_14_238 : subd8_14 [0, 3] = true := by decide +kernel
theorem subd8_14_239 : subd8_14 [0, 4] = true := by decide +kernel
theorem subd8_14_240 : subd8_14 [1, -5] = true := by decide +kernel
theorem subd8_14_241 : subd8_14 [1, -4] = true := by decide +kernel
theorem subd8_14_242 : subd8_14 [1, -3] = true := by decide +kernel
theorem subd8_14_243 : subd8_14 [1, -2, -7] = true := by decide +kernel
theorem subd8_14_244 : subd8_14 [1, -2, -6] = true := by decide +kernel
theorem subd8_14_245 : subd8_14 [1, -2, -5] = true := by decide +kernel
theorem subd8_14_246 : subd8_14 [1, -2, -4] = true := by decide +kernel
theorem subd8_14_247 : subd8_14 [1, -2, -3] = true := by decide +kernel
theorem subd8_14_248 : subd8_14 [1, -2, -2] = true := by decide +kernel
theorem subd8_14_249 : subd8_14 [1, -2, -1] = true := by decide +kernel
theorem subd8_14_250 : subd8_14 [1, -2, 0] = true := by decide +kernel
theorem subd8_14_251 : subd8_14 [1, -2, 1] = true := by decide +kernel
theorem subd8_14_252 : subd8_14 [1, -2, 2] = true := by decide +kernel
theorem subd8_14_253 : subd8_14 [1, -2, 3] = true := by decide +kernel
theorem subd8_14_254 : subd8_14 [1, -2, 4] = true := by decide +kernel
theorem subd8_14_255 : subd8_14 [1, -2, 5] = true := by decide +kernel
theorem sbd8_14_7 : ∀ q ∈ blkd8_14_7, subd8_14 q = true := by
  unfold blkd8_14_7
  exact List.forall_mem_cons.2 ⟨subd8_14_224, List.forall_mem_cons.2 ⟨subd8_14_225, List.forall_mem_cons.2 ⟨subd8_14_226, List.forall_mem_cons.2 ⟨subd8_14_227, List.forall_mem_cons.2 ⟨subd8_14_228, List.forall_mem_cons.2 ⟨subd8_14_229, List.forall_mem_cons.2 ⟨subd8_14_230, List.forall_mem_cons.2 ⟨subd8_14_231, List.forall_mem_cons.2 ⟨subd8_14_232, List.forall_mem_cons.2 ⟨subd8_14_233, List.forall_mem_cons.2 ⟨subd8_14_234, List.forall_mem_cons.2 ⟨subd8_14_235, List.forall_mem_cons.2 ⟨subd8_14_236, List.forall_mem_cons.2 ⟨subd8_14_237, List.forall_mem_cons.2 ⟨subd8_14_238, List.forall_mem_cons.2 ⟨subd8_14_239, List.forall_mem_cons.2 ⟨subd8_14_240, List.forall_mem_cons.2 ⟨subd8_14_241, List.forall_mem_cons.2 ⟨subd8_14_242, List.forall_mem_cons.2 ⟨subd8_14_243, List.forall_mem_cons.2 ⟨subd8_14_244, List.forall_mem_cons.2 ⟨subd8_14_245, List.forall_mem_cons.2 ⟨subd8_14_246, List.forall_mem_cons.2 ⟨subd8_14_247, List.forall_mem_cons.2 ⟨subd8_14_248, List.forall_mem_cons.2 ⟨subd8_14_249, List.forall_mem_cons.2 ⟨subd8_14_250, List.forall_mem_cons.2 ⟨subd8_14_251, List.forall_mem_cons.2 ⟨subd8_14_252, List.forall_mem_cons.2 ⟨subd8_14_253, List.forall_mem_cons.2 ⟨subd8_14_254, List.forall_mem_cons.2 ⟨subd8_14_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_14_256 : subd8_14 [1, -2, 6] = true := by decide +kernel
theorem subd8_14_257 : subd8_14 [1, -1, -7] = true := by decide +kernel
theorem subd8_14_258 : subd8_14 [1, -1, -6] = true := by decide +kernel
theorem subd8_14_259 : subd8_14 [1, -1, -5] = true := by decide +kernel
theorem subd8_14_260 : subd8_14 [1, -1, -4] = true := by decide +kernel
theorem subd8_14_261 : subd8_14 [1, -1, -3] = true := by decide +kernel
theorem subd8_14_262 : subd8_14 [1, -1, -2] = true := by decide +kernel
theorem subd8_14_263 : subd8_14 [1, -1, -1] = true := by decide +kernel
theorem subd8_14_264 : subd8_14 [1, -1, 0] = true := by decide +kernel
theorem subd8_14_265 : subd8_14 [1, -1, 1] = true := by decide +kernel
theorem subd8_14_266 : subd8_14 [1, -1, 2] = true := by decide +kernel
theorem subd8_14_267 : subd8_14 [1, -1, 3] = true := by decide +kernel
theorem subd8_14_268 : subd8_14 [1, -1, 4] = true := by decide +kernel
theorem subd8_14_269 : subd8_14 [1, -1, 5] = true := by decide +kernel
theorem subd8_14_270 : subd8_14 [1, -1, 6] = true := by decide +kernel
theorem subd8_14_271 : subd8_14 [1, -1, 7] = true := by decide +kernel
theorem subd8_14_272 : subd8_14 [1, 0, -8] = true := by decide +kernel
theorem subd8_14_273 : subd8_14 [1, 0, -7] = true := by decide +kernel
theorem subd8_14_274 : subd8_14 [1, 0, -6] = true := by decide +kernel
theorem subd8_14_275 : subd8_14 [1, 0, -5] = true := by decide +kernel
theorem subd8_14_276 : subd8_14 [1, 0, -4] = true := by decide +kernel
theorem subd8_14_277 : subd8_14 [1, 0, -3] = true := by decide +kernel
theorem subd8_14_278 : subd8_14 [1, 0, -2] = true := by decide +kernel
theorem subd8_14_279 : subd8_14 [1, 0, -1] = true := by decide +kernel
theorem subd8_14_280 : subd8_14 [1, 0, 0] = true := by decide +kernel
theorem subd8_14_281 : subd8_14 [1, 0, 1] = true := by decide +kernel
theorem subd8_14_282 : subd8_14 [1, 0, 2] = true := by decide +kernel
theorem subd8_14_283 : subd8_14 [1, 0, 3] = true := by decide +kernel
theorem subd8_14_284 : subd8_14 [1, 0, 4] = true := by decide +kernel
theorem subd8_14_285 : subd8_14 [1, 0, 5] = true := by decide +kernel
theorem subd8_14_286 : subd8_14 [1, 0, 6] = true := by decide +kernel
theorem subd8_14_287 : subd8_14 [1, 0, 7] = true := by decide +kernel
theorem sbd8_14_8 : ∀ q ∈ blkd8_14_8, subd8_14 q = true := by
  unfold blkd8_14_8
  exact List.forall_mem_cons.2 ⟨subd8_14_256, List.forall_mem_cons.2 ⟨subd8_14_257, List.forall_mem_cons.2 ⟨subd8_14_258, List.forall_mem_cons.2 ⟨subd8_14_259, List.forall_mem_cons.2 ⟨subd8_14_260, List.forall_mem_cons.2 ⟨subd8_14_261, List.forall_mem_cons.2 ⟨subd8_14_262, List.forall_mem_cons.2 ⟨subd8_14_263, List.forall_mem_cons.2 ⟨subd8_14_264, List.forall_mem_cons.2 ⟨subd8_14_265, List.forall_mem_cons.2 ⟨subd8_14_266, List.forall_mem_cons.2 ⟨subd8_14_267, List.forall_mem_cons.2 ⟨subd8_14_268, List.forall_mem_cons.2 ⟨subd8_14_269, List.forall_mem_cons.2 ⟨subd8_14_270, List.forall_mem_cons.2 ⟨subd8_14_271, List.forall_mem_cons.2 ⟨subd8_14_272, List.forall_mem_cons.2 ⟨subd8_14_273, List.forall_mem_cons.2 ⟨subd8_14_274, List.forall_mem_cons.2 ⟨subd8_14_275, List.forall_mem_cons.2 ⟨subd8_14_276, List.forall_mem_cons.2 ⟨subd8_14_277, List.forall_mem_cons.2 ⟨subd8_14_278, List.forall_mem_cons.2 ⟨subd8_14_279, List.forall_mem_cons.2 ⟨subd8_14_280, List.forall_mem_cons.2 ⟨subd8_14_281, List.forall_mem_cons.2 ⟨subd8_14_282, List.forall_mem_cons.2 ⟨subd8_14_283, List.forall_mem_cons.2 ⟨subd8_14_284, List.forall_mem_cons.2 ⟨subd8_14_285, List.forall_mem_cons.2 ⟨subd8_14_286, List.forall_mem_cons.2 ⟨subd8_14_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_14_288 : subd8_14 [1, 1, -7] = true := by decide +kernel
theorem subd8_14_289 : subd8_14 [1, 1, -6] = true := by decide +kernel
theorem subd8_14_290 : subd8_14 [1, 1, -5] = true := by decide +kernel
theorem subd8_14_291 : subd8_14 [1, 1, -4] = true := by decide +kernel
theorem subd8_14_292 : subd8_14 [1, 1, -3] = true := by decide +kernel
theorem subd8_14_293 : subd8_14 [1, 1, -2] = true := by decide +kernel
theorem subd8_14_294 : subd8_14 [1, 1, -1] = true := by decide +kernel
theorem subd8_14_295 : subd8_14 [1, 1, 0] = true := by decide +kernel
theorem subd8_14_296 : subd8_14 [1, 1, 1] = true := by decide +kernel
theorem subd8_14_297 : subd8_14 [1, 1, 2] = true := by decide +kernel
theorem subd8_14_298 : subd8_14 [1, 1, 3] = true := by decide +kernel
theorem subd8_14_299 : subd8_14 [1, 1, 4] = true := by decide +kernel
theorem subd8_14_300 : subd8_14 [1, 1, 5] = true := by decide +kernel
theorem subd8_14_301 : subd8_14 [1, 1, 6] = true := by decide +kernel
theorem subd8_14_302 : subd8_14 [1, 1, 7] = true := by decide +kernel
theorem subd8_14_303 : subd8_14 [1, 2, -7] = true := by decide +kernel
theorem subd8_14_304 : subd8_14 [1, 2, -6] = true := by decide +kernel
theorem subd8_14_305 : subd8_14 [1, 2, -5] = true := by decide +kernel
theorem subd8_14_306 : subd8_14 [1, 2, -4] = true := by decide +kernel
theorem subd8_14_307 : subd8_14 [1, 2, -3] = true := by decide +kernel
theorem subd8_14_308 : subd8_14 [1, 2, -2] = true := by decide +kernel
theorem subd8_14_309 : subd8_14 [1, 2, -1] = true := by decide +kernel
theorem subd8_14_310 : subd8_14 [1, 2, 0] = true := by decide +kernel
theorem subd8_14_311 : subd8_14 [1, 2, 1] = true := by decide +kernel
theorem subd8_14_312 : subd8_14 [1, 2, 2] = true := by decide +kernel
theorem subd8_14_313 : subd8_14 [1, 2, 3] = true := by decide +kernel
theorem subd8_14_314 : subd8_14 [1, 2, 4] = true := by decide +kernel
theorem subd8_14_315 : subd8_14 [1, 2, 5] = true := by decide +kernel
theorem subd8_14_316 : subd8_14 [1, 2, 6] = true := by decide +kernel
theorem subd8_14_317 : subd8_14 [1, 3] = true := by decide +kernel
theorem subd8_14_318 : subd8_14 [1, 4] = true := by decide +kernel
theorem subd8_14_319 : subd8_14 [2, -5] = true := by decide +kernel
theorem sbd8_14_9 : ∀ q ∈ blkd8_14_9, subd8_14 q = true := by
  unfold blkd8_14_9
  exact List.forall_mem_cons.2 ⟨subd8_14_288, List.forall_mem_cons.2 ⟨subd8_14_289, List.forall_mem_cons.2 ⟨subd8_14_290, List.forall_mem_cons.2 ⟨subd8_14_291, List.forall_mem_cons.2 ⟨subd8_14_292, List.forall_mem_cons.2 ⟨subd8_14_293, List.forall_mem_cons.2 ⟨subd8_14_294, List.forall_mem_cons.2 ⟨subd8_14_295, List.forall_mem_cons.2 ⟨subd8_14_296, List.forall_mem_cons.2 ⟨subd8_14_297, List.forall_mem_cons.2 ⟨subd8_14_298, List.forall_mem_cons.2 ⟨subd8_14_299, List.forall_mem_cons.2 ⟨subd8_14_300, List.forall_mem_cons.2 ⟨subd8_14_301, List.forall_mem_cons.2 ⟨subd8_14_302, List.forall_mem_cons.2 ⟨subd8_14_303, List.forall_mem_cons.2 ⟨subd8_14_304, List.forall_mem_cons.2 ⟨subd8_14_305, List.forall_mem_cons.2 ⟨subd8_14_306, List.forall_mem_cons.2 ⟨subd8_14_307, List.forall_mem_cons.2 ⟨subd8_14_308, List.forall_mem_cons.2 ⟨subd8_14_309, List.forall_mem_cons.2 ⟨subd8_14_310, List.forall_mem_cons.2 ⟨subd8_14_311, List.forall_mem_cons.2 ⟨subd8_14_312, List.forall_mem_cons.2 ⟨subd8_14_313, List.forall_mem_cons.2 ⟨subd8_14_314, List.forall_mem_cons.2 ⟨subd8_14_315, List.forall_mem_cons.2 ⟨subd8_14_316, List.forall_mem_cons.2 ⟨subd8_14_317, List.forall_mem_cons.2 ⟨subd8_14_318, List.forall_mem_cons.2 ⟨subd8_14_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_14_320 : subd8_14 [2, -4] = true := by decide +kernel
theorem subd8_14_321 : subd8_14 [2, -3] = true := by decide +kernel
theorem subd8_14_322 : subd8_14 [2, -2, -6] = true := by decide +kernel
theorem subd8_14_323 : subd8_14 [2, -2, -5] = true := by decide +kernel
theorem subd8_14_324 : subd8_14 [2, -2, -4] = true := by decide +kernel
theorem subd8_14_325 : subd8_14 [2, -2, -3] = true := by decide +kernel
theorem subd8_14_326 : subd8_14 [2, -2, -2] = true := by decide +kernel
theorem subd8_14_327 : subd8_14 [2, -2, -1] = true := by decide +kernel
theorem subd8_14_328 : subd8_14 [2, -2, 0] = true := by decide +kernel
theorem subd8_14_329 : subd8_14 [2, -2, 1] = true := by decide +kernel
theorem subd8_14_330 : subd8_14 [2, -2, 2] = true := by decide +kernel
theorem subd8_14_331 : subd8_14 [2, -2, 3] = true := by decide +kernel
theorem subd8_14_332 : subd8_14 [2, -2, 4] = true := by decide +kernel
theorem subd8_14_333 : subd8_14 [2, -2, 5] = true := by decide +kernel
theorem subd8_14_334 : subd8_14 [2, -2, 6] = true := by decide +kernel
theorem subd8_14_335 : subd8_14 [2, -1, -7] = true := by decide +kernel
theorem subd8_14_336 : subd8_14 [2, -1, -6] = true := by decide +kernel
theorem subd8_14_337 : subd8_14 [2, -1, -5] = true := by decide +kernel
theorem subd8_14_338 : subd8_14 [2, -1, -4] = true := by decide +kernel
theorem subd8_14_339 : subd8_14 [2, -1, -3] = true := by decide +kernel
theorem subd8_14_340 : subd8_14 [2, -1, -2] = true := by decide +kernel
theorem subd8_14_341 : subd8_14 [2, -1, -1] = true := by decide +kernel
theorem subd8_14_342 : subd8_14 [2, -1, 0] = true := by decide +kernel
theorem subd8_14_343 : subd8_14 [2, -1, 1] = true := by decide +kernel
theorem subd8_14_344 : subd8_14 [2, -1, 2] = true := by decide +kernel
theorem subd8_14_345 : subd8_14 [2, -1, 3] = true := by decide +kernel
theorem subd8_14_346 : subd8_14 [2, -1, 4] = true := by decide +kernel
theorem subd8_14_347 : subd8_14 [2, -1, 5] = true := by decide +kernel
theorem subd8_14_348 : subd8_14 [2, -1, 6] = true := by decide +kernel
theorem subd8_14_349 : subd8_14 [2, -1, 7] = true := by decide +kernel
theorem subd8_14_350 : subd8_14 [2, 0, -7] = true := by decide +kernel
theorem subd8_14_351 : subd8_14 [2, 0, -6] = true := by decide +kernel
theorem sbd8_14_10 : ∀ q ∈ blkd8_14_10, subd8_14 q = true := by
  unfold blkd8_14_10
  exact List.forall_mem_cons.2 ⟨subd8_14_320, List.forall_mem_cons.2 ⟨subd8_14_321, List.forall_mem_cons.2 ⟨subd8_14_322, List.forall_mem_cons.2 ⟨subd8_14_323, List.forall_mem_cons.2 ⟨subd8_14_324, List.forall_mem_cons.2 ⟨subd8_14_325, List.forall_mem_cons.2 ⟨subd8_14_326, List.forall_mem_cons.2 ⟨subd8_14_327, List.forall_mem_cons.2 ⟨subd8_14_328, List.forall_mem_cons.2 ⟨subd8_14_329, List.forall_mem_cons.2 ⟨subd8_14_330, List.forall_mem_cons.2 ⟨subd8_14_331, List.forall_mem_cons.2 ⟨subd8_14_332, List.forall_mem_cons.2 ⟨subd8_14_333, List.forall_mem_cons.2 ⟨subd8_14_334, List.forall_mem_cons.2 ⟨subd8_14_335, List.forall_mem_cons.2 ⟨subd8_14_336, List.forall_mem_cons.2 ⟨subd8_14_337, List.forall_mem_cons.2 ⟨subd8_14_338, List.forall_mem_cons.2 ⟨subd8_14_339, List.forall_mem_cons.2 ⟨subd8_14_340, List.forall_mem_cons.2 ⟨subd8_14_341, List.forall_mem_cons.2 ⟨subd8_14_342, List.forall_mem_cons.2 ⟨subd8_14_343, List.forall_mem_cons.2 ⟨subd8_14_344, List.forall_mem_cons.2 ⟨subd8_14_345, List.forall_mem_cons.2 ⟨subd8_14_346, List.forall_mem_cons.2 ⟨subd8_14_347, List.forall_mem_cons.2 ⟨subd8_14_348, List.forall_mem_cons.2 ⟨subd8_14_349, List.forall_mem_cons.2 ⟨subd8_14_350, List.forall_mem_cons.2 ⟨subd8_14_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_14_352 : subd8_14 [2, 0, -5] = true := by decide +kernel
theorem subd8_14_353 : subd8_14 [2, 0, -4] = true := by decide +kernel
theorem subd8_14_354 : subd8_14 [2, 0, -3] = true := by decide +kernel
theorem subd8_14_355 : subd8_14 [2, 0, -2] = true := by decide +kernel
theorem subd8_14_356 : subd8_14 [2, 0, -1] = true := by decide +kernel
theorem subd8_14_357 : subd8_14 [2, 0, 0] = true := by decide +kernel
theorem subd8_14_358 : subd8_14 [2, 0, 1] = true := by decide +kernel
theorem subd8_14_359 : subd8_14 [2, 0, 2] = true := by decide +kernel
theorem subd8_14_360 : subd8_14 [2, 0, 3] = true := by decide +kernel
theorem subd8_14_361 : subd8_14 [2, 0, 4] = true := by decide +kernel
theorem subd8_14_362 : subd8_14 [2, 0, 5] = true := by decide +kernel
theorem subd8_14_363 : subd8_14 [2, 0, 6] = true := by decide +kernel
theorem subd8_14_364 : subd8_14 [2, 0, 7] = true := by decide +kernel
theorem subd8_14_365 : subd8_14 [2, 1, -6] = true := by decide +kernel
theorem subd8_14_366 : subd8_14 [2, 1, -5] = true := by decide +kernel
theorem subd8_14_367 : subd8_14 [2, 1, -4] = true := by decide +kernel
theorem subd8_14_368 : subd8_14 [2, 1, -3] = true := by decide +kernel
theorem subd8_14_369 : subd8_14 [2, 1, -2] = true := by decide +kernel
theorem subd8_14_370 : subd8_14 [2, 1, -1] = true := by decide +kernel
theorem subd8_14_371 : subd8_14 [2, 1, 0] = true := by decide +kernel
theorem subd8_14_372 : subd8_14 [2, 1, 1] = true := by decide +kernel
theorem subd8_14_373 : subd8_14 [2, 1, 2] = true := by decide +kernel
theorem subd8_14_374 : subd8_14 [2, 1, 3] = true := by decide +kernel
theorem subd8_14_375 : subd8_14 [2, 1, 4] = true := by decide +kernel
theorem subd8_14_376 : subd8_14 [2, 1, 5] = true := by decide +kernel
theorem subd8_14_377 : subd8_14 [2, 1, 6] = true := by decide +kernel
theorem subd8_14_378 : subd8_14 [2, 1, 7] = true := by decide +kernel
theorem subd8_14_379 : subd8_14 [2, 2] = true := by decide +kernel
theorem subd8_14_380 : subd8_14 [2, 3] = true := by decide +kernel
theorem subd8_14_381 : subd8_14 [2, 4] = true := by decide +kernel
theorem subd8_14_382 : subd8_14 [3, -5] = true := by decide +kernel
theorem subd8_14_383 : subd8_14 [3, -4] = true := by decide +kernel
theorem sbd8_14_11 : ∀ q ∈ blkd8_14_11, subd8_14 q = true := by
  unfold blkd8_14_11
  exact List.forall_mem_cons.2 ⟨subd8_14_352, List.forall_mem_cons.2 ⟨subd8_14_353, List.forall_mem_cons.2 ⟨subd8_14_354, List.forall_mem_cons.2 ⟨subd8_14_355, List.forall_mem_cons.2 ⟨subd8_14_356, List.forall_mem_cons.2 ⟨subd8_14_357, List.forall_mem_cons.2 ⟨subd8_14_358, List.forall_mem_cons.2 ⟨subd8_14_359, List.forall_mem_cons.2 ⟨subd8_14_360, List.forall_mem_cons.2 ⟨subd8_14_361, List.forall_mem_cons.2 ⟨subd8_14_362, List.forall_mem_cons.2 ⟨subd8_14_363, List.forall_mem_cons.2 ⟨subd8_14_364, List.forall_mem_cons.2 ⟨subd8_14_365, List.forall_mem_cons.2 ⟨subd8_14_366, List.forall_mem_cons.2 ⟨subd8_14_367, List.forall_mem_cons.2 ⟨subd8_14_368, List.forall_mem_cons.2 ⟨subd8_14_369, List.forall_mem_cons.2 ⟨subd8_14_370, List.forall_mem_cons.2 ⟨subd8_14_371, List.forall_mem_cons.2 ⟨subd8_14_372, List.forall_mem_cons.2 ⟨subd8_14_373, List.forall_mem_cons.2 ⟨subd8_14_374, List.forall_mem_cons.2 ⟨subd8_14_375, List.forall_mem_cons.2 ⟨subd8_14_376, List.forall_mem_cons.2 ⟨subd8_14_377, List.forall_mem_cons.2 ⟨subd8_14_378, List.forall_mem_cons.2 ⟨subd8_14_379, List.forall_mem_cons.2 ⟨subd8_14_380, List.forall_mem_cons.2 ⟨subd8_14_381, List.forall_mem_cons.2 ⟨subd8_14_382, List.forall_mem_cons.2 ⟨subd8_14_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_14_384 : subd8_14 [3, -3] = true := by decide +kernel
theorem subd8_14_385 : subd8_14 [3, -2] = true := by decide +kernel
theorem subd8_14_386 : subd8_14 [3, -1] = true := by decide +kernel
theorem subd8_14_387 : subd8_14 [3, 0] = true := by decide +kernel
theorem subd8_14_388 : subd8_14 [3, 1] = true := by decide +kernel
theorem subd8_14_389 : subd8_14 [3, 2] = true := by decide +kernel
theorem subd8_14_390 : subd8_14 [3, 3] = true := by decide +kernel
theorem subd8_14_391 : subd8_14 [4, -4] = true := by decide +kernel
theorem subd8_14_392 : subd8_14 [4, -3] = true := by decide +kernel
theorem subd8_14_393 : subd8_14 [4, -2] = true := by decide +kernel
theorem subd8_14_394 : subd8_14 [4, -1] = true := by decide +kernel
theorem subd8_14_395 : subd8_14 [4, 0] = true := by decide +kernel
theorem subd8_14_396 : subd8_14 [4, 1] = true := by decide +kernel
theorem subd8_14_397 : subd8_14 [4, 2] = true := by decide +kernel
theorem subd8_14_398 : subd8_14 [5] = true := by decide +kernel
theorem sbd8_14_12 : ∀ q ∈ blkd8_14_12, subd8_14 q = true := by
  unfold blkd8_14_12
  exact List.forall_mem_cons.2 ⟨subd8_14_384, List.forall_mem_cons.2 ⟨subd8_14_385, List.forall_mem_cons.2 ⟨subd8_14_386, List.forall_mem_cons.2 ⟨subd8_14_387, List.forall_mem_cons.2 ⟨subd8_14_388, List.forall_mem_cons.2 ⟨subd8_14_389, List.forall_mem_cons.2 ⟨subd8_14_390, List.forall_mem_cons.2 ⟨subd8_14_391, List.forall_mem_cons.2 ⟨subd8_14_392, List.forall_mem_cons.2 ⟨subd8_14_393, List.forall_mem_cons.2 ⟨subd8_14_394, List.forall_mem_cons.2 ⟨subd8_14_395, List.forall_mem_cons.2 ⟨subd8_14_396, List.forall_mem_cons.2 ⟨subd8_14_397, List.forall_mem_cons.2 ⟨subd8_14_398, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
