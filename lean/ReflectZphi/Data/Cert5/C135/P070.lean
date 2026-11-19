import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_7_64 : subd10_7 [-1, 0, -2] = true := by decide +kernel
theorem subd10_7_65 : subd10_7 [-1, 0, -1] = true := by decide +kernel
theorem subd10_7_66 : subd10_7 [-1, 0, 0] = true := by decide +kernel
theorem subd10_7_67 : subd10_7 [-1, 0, 1] = true := by decide +kernel
theorem subd10_7_68 : subd10_7 [-1, 0, 2] = true := by decide +kernel
theorem subd10_7_69 : subd10_7 [-1, 0, 3] = true := by decide +kernel
theorem subd10_7_70 : subd10_7 [-1, 0, 4] = true := by decide +kernel
theorem subd10_7_71 : subd10_7 [-1, 0, 5] = true := by decide +kernel
theorem subd10_7_72 : subd10_7 [-1, 0, 6] = true := by decide +kernel
theorem subd10_7_73 : subd10_7 [-1, 0, 7] = true := by decide +kernel
theorem subd10_7_74 : subd10_7 [-1, 0, 8] = true := by decide +kernel
theorem subd10_7_75 : subd10_7 [-1, 0, 9] = true := by decide +kernel
theorem subd10_7_76 : subd10_7 [-1, 1, -9] = true := by decide +kernel
theorem subd10_7_77 : subd10_7 [-1, 1, -8] = true := by decide +kernel
theorem subd10_7_78 : subd10_7 [-1, 1, -7] = true := by decide +kernel
theorem subd10_7_79 : subd10_7 [-1, 1, -6] = true := by decide +kernel
theorem subd10_7_80 : subd10_7 [-1, 1, -5] = true := by decide +kernel
theorem subd10_7_81 : subd10_7 [-1, 1, -4] = true := by decide +kernel
theorem subd10_7_82 : subd10_7 [-1, 1, -3] = true := by decide +kernel
theorem subd10_7_83 : subd10_7 [-1, 1, -2] = true := by decide +kernel
theorem subd10_7_84 : subd10_7 [-1, 1, -1] = true := by decide +kernel
theorem subd10_7_85 : subd10_7 [-1, 1, 0] = true := by decide +kernel
theorem subd10_7_86 : subd10_7 [-1, 1, 1] = true := by decide +kernel
theorem subd10_7_87 : subd10_7 [-1, 1, 2] = true := by decide +kernel
theorem subd10_7_88 : subd10_7 [-1, 1, 3] = true := by decide +kernel
theorem subd10_7_89 : subd10_7 [-1, 1, 4] = true := by decide +kernel
theorem subd10_7_90 : subd10_7 [-1, 1, 5] = true := by decide +kernel
theorem subd10_7_91 : subd10_7 [-1, 1, 6] = true := by decide +kernel
theorem subd10_7_92 : subd10_7 [-1, 1, 7] = true := by decide +kernel
theorem subd10_7_93 : subd10_7 [-1, 1, 8] = true := by decide +kernel
theorem subd10_7_94 : subd10_7 [-1, 2] = true := by decide +kernel
theorem subd10_7_95 : subd10_7 [0, -4] = true := by decide +kernel
theorem sbd10_7_2 : ∀ q ∈ blkd10_7_2, subd10_7 q = true := by
  unfold blkd10_7_2
  exact List.forall_mem_cons.2 ⟨subd10_7_64, List.forall_mem_cons.2 ⟨subd10_7_65, List.forall_mem_cons.2 ⟨subd10_7_66, List.forall_mem_cons.2 ⟨subd10_7_67, List.forall_mem_cons.2 ⟨subd10_7_68, List.forall_mem_cons.2 ⟨subd10_7_69, List.forall_mem_cons.2 ⟨subd10_7_70, List.forall_mem_cons.2 ⟨subd10_7_71, List.forall_mem_cons.2 ⟨subd10_7_72, List.forall_mem_cons.2 ⟨subd10_7_73, List.forall_mem_cons.2 ⟨subd10_7_74, List.forall_mem_cons.2 ⟨subd10_7_75, List.forall_mem_cons.2 ⟨subd10_7_76, List.forall_mem_cons.2 ⟨subd10_7_77, List.forall_mem_cons.2 ⟨subd10_7_78, List.forall_mem_cons.2 ⟨subd10_7_79, List.forall_mem_cons.2 ⟨subd10_7_80, List.forall_mem_cons.2 ⟨subd10_7_81, List.forall_mem_cons.2 ⟨subd10_7_82, List.forall_mem_cons.2 ⟨subd10_7_83, List.forall_mem_cons.2 ⟨subd10_7_84, List.forall_mem_cons.2 ⟨subd10_7_85, List.forall_mem_cons.2 ⟨subd10_7_86, List.forall_mem_cons.2 ⟨subd10_7_87, List.forall_mem_cons.2 ⟨subd10_7_88, List.forall_mem_cons.2 ⟨subd10_7_89, List.forall_mem_cons.2 ⟨subd10_7_90, List.forall_mem_cons.2 ⟨subd10_7_91, List.forall_mem_cons.2 ⟨subd10_7_92, List.forall_mem_cons.2 ⟨subd10_7_93, List.forall_mem_cons.2 ⟨subd10_7_94, List.forall_mem_cons.2 ⟨subd10_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_7_96 : subd10_7 [0, -3] = true := by decide +kernel
theorem subd10_7_97 : subd10_7 [0, -2, -9] = true := by decide +kernel
theorem subd10_7_98 : subd10_7 [0, -2, -8] = true := by decide +kernel
theorem subd10_7_99 : subd10_7 [0, -2, -7] = true := by decide +kernel
theorem subd10_7_100 : subd10_7 [0, -2, -6] = true := by decide +kernel
theorem subd10_7_101 : subd10_7 [0, -2, -5] = true := by decide +kernel
theorem subd10_7_102 : subd10_7 [0, -2, -4] = true := by decide +kernel
theorem subd10_7_103 : subd10_7 [0, -2, -3] = true := by decide +kernel
theorem subd10_7_104 : subd10_7 [0, -2, -2] = true := by decide +kernel
theorem subd10_7_105 : subd10_7 [0, -2, -1] = true := by decide +kernel
theorem subd10_7_106 : subd10_7 [0, -2, 0] = true := by decide +kernel
theorem subd10_7_107 : subd10_7 [0, -2, 1] = true := by decide +kernel
theorem subd10_7_108 : subd10_7 [0, -2, 2] = true := by decide +kernel
theorem subd10_7_109 : subd10_7 [0, -2, 3] = true := by decide +kernel
theorem subd10_7_110 : subd10_7 [0, -2, 4] = true := by decide +kernel
theorem subd10_7_111 : subd10_7 [0, -2, 5] = true := by decide +kernel
theorem subd10_7_112 : subd10_7 [0, -2, 6] = true := by decide +kernel
theorem subd10_7_113 : subd10_7 [0, -1, -10] = true := by decide +kernel
theorem subd10_7_114 : subd10_7 [0, -1, -9] = true := by decide +kernel
theorem subd10_7_115 : subd10_7 [0, -1, -8] = true := by decide +kernel
theorem subd10_7_116 : subd10_7 [0, -1, -7] = true := by decide +kernel
theorem subd10_7_117 : subd10_7 [0, -1, -6] = true := by decide +kernel
theorem subd10_7_118 : subd10_7 [0, -1, -5] = true := by decide +kernel
theorem subd10_7_119 : subd10_7 [0, -1, -4] = true := by decide +kernel
theorem subd10_7_120 : subd10_7 [0, -1, -3] = true := by decide +kernel
theorem subd10_7_121 : subd10_7 [0, -1, -2] = true := by decide +kernel
theorem subd10_7_122 : subd10_7 [0, -1, -1] = true := by decide +kernel
theorem subd10_7_123 : subd10_7 [0, -1, 0] = true := by decide +kernel
theorem subd10_7_124 : subd10_7 [0, -1, 1] = true := by decide +kernel
theorem subd10_7_125 : subd10_7 [0, -1, 2] = true := by decide +kernel
theorem subd10_7_126 : subd10_7 [0, -1, 3] = true := by decide +kernel
theorem subd10_7_127 : subd10_7 [0, -1, 4] = true := by decide +kernel
theorem sbd10_7_3 : ∀ q ∈ blkd10_7_3, subd10_7 q = true := by
  unfold blkd10_7_3
  exact List.forall_mem_cons.2 ⟨subd10_7_96, List.forall_mem_cons.2 ⟨subd10_7_97, List.forall_mem_cons.2 ⟨subd10_7_98, List.forall_mem_cons.2 ⟨subd10_7_99, List.forall_mem_cons.2 ⟨subd10_7_100, List.forall_mem_cons.2 ⟨subd10_7_101, List.forall_mem_cons.2 ⟨subd10_7_102, List.forall_mem_cons.2 ⟨subd10_7_103, List.forall_mem_cons.2 ⟨subd10_7_104, List.forall_mem_cons.2 ⟨subd10_7_105, List.forall_mem_cons.2 ⟨subd10_7_106, List.forall_mem_cons.2 ⟨subd10_7_107, List.forall_mem_cons.2 ⟨subd10_7_108, List.forall_mem_cons.2 ⟨subd10_7_109, List.forall_mem_cons.2 ⟨subd10_7_110, List.forall_mem_cons.2 ⟨subd10_7_111, List.forall_mem_cons.2 ⟨subd10_7_112, List.forall_mem_cons.2 ⟨subd10_7_113, List.forall_mem_cons.2 ⟨subd10_7_114, List.forall_mem_cons.2 ⟨subd10_7_115, List.forall_mem_cons.2 ⟨subd10_7_116, List.forall_mem_cons.2 ⟨subd10_7_117, List.forall_mem_cons.2 ⟨subd10_7_118, List.forall_mem_cons.2 ⟨subd10_7_119, List.forall_mem_cons.2 ⟨subd10_7_120, List.forall_mem_cons.2 ⟨subd10_7_121, List.forall_mem_cons.2 ⟨subd10_7_122, List.forall_mem_cons.2 ⟨subd10_7_123, List.forall_mem_cons.2 ⟨subd10_7_124, List.forall_mem_cons.2 ⟨subd10_7_125, List.forall_mem_cons.2 ⟨subd10_7_126, List.forall_mem_cons.2 ⟨subd10_7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_7_128 : subd10_7 [0, -1, 5] = true := by decide +kernel
theorem subd10_7_129 : subd10_7 [0, -1, 6] = true := by decide +kernel
theorem subd10_7_130 : subd10_7 [0, -1, 7] = true := by decide +kernel
theorem subd10_7_131 : subd10_7 [0, -1, 8] = true := by decide +kernel
theorem subd10_7_132 : subd10_7 [0, -1, 9] = true := by decide +kernel
theorem subd10_7_133 : subd10_7 [0, 0, -11] = true := by decide +kernel
theorem subd10_7_134 : subd10_7 [0, 0, -10] = true := by decide +kernel
theorem subd10_7_135 : subd10_7 [0, 0, -9] = true := by decide +kernel
theorem subd10_7_136 : subd10_7 [0, 0, -8] = true := by decide +kernel
theorem subd10_7_137 : subd10_7 [0, 0, -7] = true := by decide +kernel
theorem subd10_7_138 : subd10_7 [0, 0, -6] = true := by decide +kernel
theorem subd10_7_139 : subd10_7 [0, 0, -5] = true := by decide +kernel
theorem subd10_7_140 : subd10_7 [0, 0, -4] = true := by decide +kernel
theorem subd10_7_141 : subd10_7 [0, 0, -3] = true := by decide +kernel
theorem subd10_7_142 : subd10_7 [0, 0, -2] = true := by decide +kernel
theorem subd10_7_143 : subd10_7 [0, 0, -1] = true := by decide +kernel
theorem subd10_7_144 : subd10_7 [0, 0, 0] = true := by decide +kernel
theorem subd10_7_145 : subd10_7 [0, 0, 1] = true := by decide +kernel
theorem subd10_7_146 : subd10_7 [0, 0, 2] = true := by decide +kernel
theorem subd10_7_147 : subd10_7 [0, 0, 3] = true := by decide +kernel
theorem subd10_7_148 : subd10_7 [0, 0, 4] = true := by decide +kernel
theorem subd10_7_149 : subd10_7 [0, 0, 5] = true := by decide +kernel
theorem subd10_7_150 : subd10_7 [0, 0, 6] = true := by decide +kernel
theorem subd10_7_151 : subd10_7 [0, 0, 7] = true := by decide +kernel
theorem subd10_7_152 : subd10_7 [0, 0, 8] = true := by decide +kernel
theorem subd10_7_153 : subd10_7 [0, 0, 9] = true := by decide +kernel
theorem subd10_7_154 : subd10_7 [0, 0, 10] = true := by decide +kernel
theorem subd10_7_155 : subd10_7 [0, 1, -10] = true := by decide +kernel
theorem subd10_7_156 : subd10_7 [0, 1, -9] = true := by decide +kernel
theorem subd10_7_157 : subd10_7 [0, 1, -8] = true := by decide +kernel
theorem subd10_7_158 : subd10_7 [0, 1, -7] = true := by decide +kernel
theorem subd10_7_159 : subd10_7 [0, 1, -6] = true := by decide +kernel
theorem sbd10_7_4 : ∀ q ∈ blkd10_7_4, subd10_7 q = true := by
  unfold blkd10_7_4
  exact List.forall_mem_cons.2 ⟨subd10_7_128, List.forall_mem_cons.2 ⟨subd10_7_129, List.forall_mem_cons.2 ⟨subd10_7_130, List.forall_mem_cons.2 ⟨subd10_7_131, List.forall_mem_cons.2 ⟨subd10_7_132, List.forall_mem_cons.2 ⟨subd10_7_133, List.forall_mem_cons.2 ⟨subd10_7_134, List.forall_mem_cons.2 ⟨subd10_7_135, List.forall_mem_cons.2 ⟨subd10_7_136, List.forall_mem_cons.2 ⟨subd10_7_137, List.forall_mem_cons.2 ⟨subd10_7_138, List.forall_mem_cons.2 ⟨subd10_7_139, List.forall_mem_cons.2 ⟨subd10_7_140, List.forall_mem_cons.2 ⟨subd10_7_141, List.forall_mem_cons.2 ⟨subd10_7_142, List.forall_mem_cons.2 ⟨subd10_7_143, List.forall_mem_cons.2 ⟨subd10_7_144, List.forall_mem_cons.2 ⟨subd10_7_145, List.forall_mem_cons.2 ⟨subd10_7_146, List.forall_mem_cons.2 ⟨subd10_7_147, List.forall_mem_cons.2 ⟨subd10_7_148, List.forall_mem_cons.2 ⟨subd10_7_149, List.forall_mem_cons.2 ⟨subd10_7_150, List.forall_mem_cons.2 ⟨subd10_7_151, List.forall_mem_cons.2 ⟨subd10_7_152, List.forall_mem_cons.2 ⟨subd10_7_153, List.forall_mem_cons.2 ⟨subd10_7_154, List.forall_mem_cons.2 ⟨subd10_7_155, List.forall_mem_cons.2 ⟨subd10_7_156, List.forall_mem_cons.2 ⟨subd10_7_157, List.forall_mem_cons.2 ⟨subd10_7_158, List.forall_mem_cons.2 ⟨subd10_7_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_7_160 : subd10_7 [0, 1, -5] = true := by decide +kernel
theorem subd10_7_161 : subd10_7 [0, 1, -4] = true := by decide +kernel
theorem subd10_7_162 : subd10_7 [0, 1, -3] = true := by decide +kernel
theorem subd10_7_163 : subd10_7 [0, 1, -2] = true := by decide +kernel
theorem subd10_7_164 : subd10_7 [0, 1, -1] = true := by decide +kernel
theorem subd10_7_165 : subd10_7 [0, 1, 0] = true := by decide +kernel
theorem subd10_7_166 : subd10_7 [0, 1, 1] = true := by decide +kernel
theorem subd10_7_167 : subd10_7 [0, 1, 2] = true := by decide +kernel
theorem subd10_7_168 : subd10_7 [0, 1, 3] = true := by decide +kernel
theorem subd10_7_169 : subd10_7 [0, 1, 4] = true := by decide +kernel
theorem subd10_7_170 : subd10_7 [0, 1, 5] = true := by decide +kernel
theorem subd10_7_171 : subd10_7 [0, 1, 6] = true := by decide +kernel
theorem subd10_7_172 : subd10_7 [0, 1, 7] = true := by decide +kernel
theorem subd10_7_173 : subd10_7 [0, 1, 8] = true := by decide +kernel
theorem subd10_7_174 : subd10_7 [0, 1, 9] = true := by decide +kernel
theorem subd10_7_175 : subd10_7 [0, 2, -7] = true := by decide +kernel
theorem subd10_7_176 : subd10_7 [0, 2, -6] = true := by decide +kernel
theorem subd10_7_177 : subd10_7 [0, 2, -5] = true := by decide +kernel
theorem subd10_7_178 : subd10_7 [0, 2, -4] = true := by decide +kernel
theorem subd10_7_179 : subd10_7 [0, 2, -3] = true := by decide +kernel
theorem subd10_7_180 : subd10_7 [0, 2, -2] = true := by decide +kernel
theorem subd10_7_181 : subd10_7 [0, 2, -1] = true := by decide +kernel
theorem subd10_7_182 : subd10_7 [0, 2, 0] = true := by decide +kernel
theorem subd10_7_183 : subd10_7 [0, 2, 1] = true := by decide +kernel
theorem subd10_7_184 : subd10_7 [0, 2, 2] = true := by decide +kernel
theorem subd10_7_185 : subd10_7 [0, 2, 3] = true := by decide +kernel
theorem subd10_7_186 : subd10_7 [0, 2, 4] = true := by decide +kernel
theorem subd10_7_187 : subd10_7 [0, 2, 5] = true := by decide +kernel
theorem subd10_7_188 : subd10_7 [0, 2, 6] = true := by decide +kernel
theorem subd10_7_189 : subd10_7 [0, 2, 7] = true := by decide +kernel
theorem subd10_7_190 : subd10_7 [0, 2, 8] = true := by decide +kernel
theorem subd10_7_191 : subd10_7 [0, 3] = true := by decide +kernel
theorem sbd10_7_5 : ∀ q ∈ blkd10_7_5, subd10_7 q = true := by
  unfold blkd10_7_5
  exact List.forall_mem_cons.2 ⟨subd10_7_160, List.forall_mem_cons.2 ⟨subd10_7_161, List.forall_mem_cons.2 ⟨subd10_7_162, List.forall_mem_cons.2 ⟨subd10_7_163, List.forall_mem_cons.2 ⟨subd10_7_164, List.forall_mem_cons.2 ⟨subd10_7_165, List.forall_mem_cons.2 ⟨subd10_7_166, List.forall_mem_cons.2 ⟨subd10_7_167, List.forall_mem_cons.2 ⟨subd10_7_168, List.forall_mem_cons.2 ⟨subd10_7_169, List.forall_mem_cons.2 ⟨subd10_7_170, List.forall_mem_cons.2 ⟨subd10_7_171, List.forall_mem_cons.2 ⟨subd10_7_172, List.forall_mem_cons.2 ⟨subd10_7_173, List.forall_mem_cons.2 ⟨subd10_7_174, List.forall_mem_cons.2 ⟨subd10_7_175, List.forall_mem_cons.2 ⟨subd10_7_176, List.forall_mem_cons.2 ⟨subd10_7_177, List.forall_mem_cons.2 ⟨subd10_7_178, List.forall_mem_cons.2 ⟨subd10_7_179, List.forall_mem_cons.2 ⟨subd10_7_180, List.forall_mem_cons.2 ⟨subd10_7_181, List.forall_mem_cons.2 ⟨subd10_7_182, List.forall_mem_cons.2 ⟨subd10_7_183, List.forall_mem_cons.2 ⟨subd10_7_184, List.forall_mem_cons.2 ⟨subd10_7_185, List.forall_mem_cons.2 ⟨subd10_7_186, List.forall_mem_cons.2 ⟨subd10_7_187, List.forall_mem_cons.2 ⟨subd10_7_188, List.forall_mem_cons.2 ⟨subd10_7_189, List.forall_mem_cons.2 ⟨subd10_7_190, List.forall_mem_cons.2 ⟨subd10_7_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_7_192 : subd10_7 [1, -3] = true := by decide +kernel
theorem subd10_7_193 : subd10_7 [1, -2] = true := by decide +kernel
theorem subd10_7_194 : subd10_7 [1, -1, -9] = true := by decide +kernel
theorem subd10_7_195 : subd10_7 [1, -1, -8] = true := by decide +kernel
theorem subd10_7_196 : subd10_7 [1, -1, -7] = true := by decide +kernel
theorem subd10_7_197 : subd10_7 [1, -1, -6] = true := by decide +kernel
theorem subd10_7_198 : subd10_7 [1, -1, -5] = true := by decide +kernel
theorem subd10_7_199 : subd10_7 [1, -1, -4] = true := by decide +kernel
theorem subd10_7_200 : subd10_7 [1, -1, -3] = true := by decide +kernel
theorem subd10_7_201 : subd10_7 [1, -1, -2] = true := by decide +kernel
theorem subd10_7_202 : subd10_7 [1, -1, -1] = true := by decide +kernel
theorem subd10_7_203 : subd10_7 [1, -1, 0] = true := by decide +kernel
theorem subd10_7_204 : subd10_7 [1, -1, 1] = true := by decide +kernel
theorem subd10_7_205 : subd10_7 [1, -1, 2] = true := by decide +kernel
theorem subd10_7_206 : subd10_7 [1, -1, 3] = true := by decide +kernel
theorem subd10_7_207 : subd10_7 [1, -1, 4] = true := by decide +kernel
theorem subd10_7_208 : subd10_7 [1, -1, 5] = true := by decide +kernel
theorem subd10_7_209 : subd10_7 [1, -1, 6] = true := by decide +kernel
theorem subd10_7_210 : subd10_7 [1, -1, 7] = true := by decide +kernel
theorem subd10_7_211 : subd10_7 [1, -1, 8] = true := by decide +kernel
theorem subd10_7_212 : subd10_7 [1, 0, -10] = true := by decide +kernel
theorem subd10_7_213 : subd10_7 [1, 0, -9] = true := by decide +kernel
theorem subd10_7_214 : subd10_7 [1, 0, -8] = true := by decide +kernel
theorem subd10_7_215 : subd10_7 [1, 0, -7] = true := by decide +kernel
theorem subd10_7_216 : subd10_7 [1, 0, -6] = true := by decide +kernel
theorem subd10_7_217 : subd10_7 [1, 0, -5] = true := by decide +kernel
theorem subd10_7_218 : subd10_7 [1, 0, -4] = true := by decide +kernel
theorem subd10_7_219 : subd10_7 [1, 0, -3] = true := by decide +kernel
theorem subd10_7_220 : subd10_7 [1, 0, -2] = true := by decide +kernel
theorem subd10_7_221 : subd10_7 [1, 0, -1] = true := by decide +kernel
theorem subd10_7_222 : subd10_7 [1, 0, 0] = true := by decide +kernel
theorem subd10_7_223 : subd10_7 [1, 0, 1] = true := by decide +kernel
theorem sbd10_7_6 : ∀ q ∈ blkd10_7_6, subd10_7 q = true := by
  unfold blkd10_7_6
  exact List.forall_mem_cons.2 ⟨subd10_7_192, List.forall_mem_cons.2 ⟨subd10_7_193, List.forall_mem_cons.2 ⟨subd10_7_194, List.forall_mem_cons.2 ⟨subd10_7_195, List.forall_mem_cons.2 ⟨subd10_7_196, List.forall_mem_cons.2 ⟨subd10_7_197, List.forall_mem_cons.2 ⟨subd10_7_198, List.forall_mem_cons.2 ⟨subd10_7_199, List.forall_mem_cons.2 ⟨subd10_7_200, List.forall_mem_cons.2 ⟨subd10_7_201, List.forall_mem_cons.2 ⟨subd10_7_202, List.forall_mem_cons.2 ⟨subd10_7_203, List.forall_mem_cons.2 ⟨subd10_7_204, List.forall_mem_cons.2 ⟨subd10_7_205, List.forall_mem_cons.2 ⟨subd10_7_206, List.forall_mem_cons.2 ⟨subd10_7_207, List.forall_mem_cons.2 ⟨subd10_7_208, List.forall_mem_cons.2 ⟨subd10_7_209, List.forall_mem_cons.2 ⟨subd10_7_210, List.forall_mem_cons.2 ⟨subd10_7_211, List.forall_mem_cons.2 ⟨subd10_7_212, List.forall_mem_cons.2 ⟨subd10_7_213, List.forall_mem_cons.2 ⟨subd10_7_214, List.forall_mem_cons.2 ⟨subd10_7_215, List.forall_mem_cons.2 ⟨subd10_7_216, List.forall_mem_cons.2 ⟨subd10_7_217, List.forall_mem_cons.2 ⟨subd10_7_218, List.forall_mem_cons.2 ⟨subd10_7_219, List.forall_mem_cons.2 ⟨subd10_7_220, List.forall_mem_cons.2 ⟨subd10_7_221, List.forall_mem_cons.2 ⟨subd10_7_222, List.forall_mem_cons.2 ⟨subd10_7_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_7_224 : subd10_7 [1, 0, 2] = true := by decide +kernel
theorem subd10_7_225 : subd10_7 [1, 0, 3] = true := by decide +kernel
theorem subd10_7_226 : subd10_7 [1, 0, 4] = true := by decide +kernel
theorem subd10_7_227 : subd10_7 [1, 0, 5] = true := by decide +kernel
theorem subd10_7_228 : subd10_7 [1, 0, 6] = true := by decide +kernel
theorem subd10_7_229 : subd10_7 [1, 0, 7] = true := by decide +kernel
theorem subd10_7_230 : subd10_7 [1, 0, 8] = true := by decide +kernel
theorem subd10_7_231 : subd10_7 [1, 0, 9] = true := by decide +kernel
theorem subd10_7_232 : subd10_7 [1, 1, -9] = true := by decide +kernel
theorem subd10_7_233 : subd10_7 [1, 1, -8] = true := by decide +kernel
theorem subd10_7_234 : subd10_7 [1, 1, -7] = true := by decide +kernel
theorem subd10_7_235 : subd10_7 [1, 1, -6] = true := by decide +kernel
theorem subd10_7_236 : subd10_7 [1, 1, -5] = true := by decide +kernel
theorem subd10_7_237 : subd10_7 [1, 1, -4] = true := by decide +kernel
theorem subd10_7_238 : subd10_7 [1, 1, -3] = true := by decide +kernel
theorem subd10_7_239 : subd10_7 [1, 1, -2] = true := by decide +kernel
theorem subd10_7_240 : subd10_7 [1, 1, -1] = true := by decide +kernel
theorem subd10_7_241 : subd10_7 [1, 1, 0] = true := by decide +kernel
theorem subd10_7_242 : subd10_7 [1, 1, 1] = true := by decide +kernel
theorem subd10_7_243 : subd10_7 [1, 1, 2] = true := by decide +kernel
theorem subd10_7_244 : subd10_7 [1, 1, 3] = true := by decide +kernel
theorem subd10_7_245 : subd10_7 [1, 1, 4] = true := by decide +kernel
theorem subd10_7_246 : subd10_7 [1, 1, 5] = true := by decide +kernel
theorem subd10_7_247 : subd10_7 [1, 1, 6] = true := by decide +kernel
theorem subd10_7_248 : subd10_7 [1, 1, 7] = true := by decide +kernel
theorem subd10_7_249 : subd10_7 [1, 1, 8] = true := by decide +kernel
theorem subd10_7_250 : subd10_7 [1, 1, 9] = true := by decide +kernel
theorem subd10_7_251 : subd10_7 [1, 2, -7] = true := by decide +kernel
theorem subd10_7_252 : subd10_7 [1, 2, -6] = true := by decide +kernel
theorem subd10_7_253 : subd10_7 [1, 2, -5] = true := by decide +kernel
theorem subd10_7_254 : subd10_7 [1, 2, -4] = true := by decide +kernel
theorem subd10_7_255 : subd10_7 [1, 2, -3] = true := by decide +kernel
theorem sbd10_7_7 : ∀ q ∈ blkd10_7_7, subd10_7 q = true := by
  unfold blkd10_7_7
  exact List.forall_mem_cons.2 ⟨subd10_7_224, List.forall_mem_cons.2 ⟨subd10_7_225, List.forall_mem_cons.2 ⟨subd10_7_226, List.forall_mem_cons.2 ⟨subd10_7_227, List.forall_mem_cons.2 ⟨subd10_7_228, List.forall_mem_cons.2 ⟨subd10_7_229, List.forall_mem_cons.2 ⟨subd10_7_230, List.forall_mem_cons.2 ⟨subd10_7_231, List.forall_mem_cons.2 ⟨subd10_7_232, List.forall_mem_cons.2 ⟨subd10_7_233, List.forall_mem_cons.2 ⟨subd10_7_234, List.forall_mem_cons.2 ⟨subd10_7_235, List.forall_mem_cons.2 ⟨subd10_7_236, List.forall_mem_cons.2 ⟨subd10_7_237, List.forall_mem_cons.2 ⟨subd10_7_238, List.forall_mem_cons.2 ⟨subd10_7_239, List.forall_mem_cons.2 ⟨subd10_7_240, List.forall_mem_cons.2 ⟨subd10_7_241, List.forall_mem_cons.2 ⟨subd10_7_242, List.forall_mem_cons.2 ⟨subd10_7_243, List.forall_mem_cons.2 ⟨subd10_7_244, List.forall_mem_cons.2 ⟨subd10_7_245, List.forall_mem_cons.2 ⟨subd10_7_246, List.forall_mem_cons.2 ⟨subd10_7_247, List.forall_mem_cons.2 ⟨subd10_7_248, List.forall_mem_cons.2 ⟨subd10_7_249, List.forall_mem_cons.2 ⟨subd10_7_250, List.forall_mem_cons.2 ⟨subd10_7_251, List.forall_mem_cons.2 ⟨subd10_7_252, List.forall_mem_cons.2 ⟨subd10_7_253, List.forall_mem_cons.2 ⟨subd10_7_254, List.forall_mem_cons.2 ⟨subd10_7_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_7_256 : subd10_7 [1, 2, -2] = true := by decide +kernel
theorem subd10_7_257 : subd10_7 [1, 2, -1] = true := by decide +kernel
theorem subd10_7_258 : subd10_7 [1, 2, 0] = true := by decide +kernel
theorem subd10_7_259 : subd10_7 [1, 2, 1] = true := by decide +kernel
theorem subd10_7_260 : subd10_7 [1, 2, 2] = true := by decide +kernel
theorem subd10_7_261 : subd10_7 [1, 2, 3] = true := by decide +kernel
theorem subd10_7_262 : subd10_7 [1, 2, 4] = true := by decide +kernel
theorem subd10_7_263 : subd10_7 [1, 2, 5] = true := by decide +kernel
theorem subd10_7_264 : subd10_7 [1, 2, 6] = true := by decide +kernel
theorem subd10_7_265 : subd10_7 [1, 2, 7] = true := by decide +kernel
theorem subd10_7_266 : subd10_7 [2, -3] = true := by decide +kernel
theorem subd10_7_267 : subd10_7 [2, -2] = true := by decide +kernel
theorem subd10_7_268 : subd10_7 [2, -1] = true := by decide +kernel
theorem subd10_7_269 : subd10_7 [2, 0, -7] = true := by decide +kernel
theorem subd10_7_270 : subd10_7 [2, 0, -6] = true := by decide +kernel
theorem subd10_7_271 : subd10_7 [2, 0, -5] = true := by decide +kernel
theorem subd10_7_272 : subd10_7 [2, 0, -4] = true := by decide +kernel
theorem subd10_7_273 : subd10_7 [2, 0, -3] = true := by decide +kernel
theorem subd10_7_274 : subd10_7 [2, 0, -2] = true := by decide +kernel
theorem subd10_7_275 : subd10_7 [2, 0, -1] = true := by decide +kernel
theorem subd10_7_276 : subd10_7 [2, 0, 0] = true := by decide +kernel
theorem subd10_7_277 : subd10_7 [2, 0, 1] = true := by decide +kernel
theorem subd10_7_278 : subd10_7 [2, 0, 2] = true := by decide +kernel
theorem subd10_7_279 : subd10_7 [2, 0, 3] = true := by decide +kernel
theorem subd10_7_280 : subd10_7 [2, 0, 4] = true := by decide +kernel
theorem subd10_7_281 : subd10_7 [2, 0, 5] = true := by decide +kernel
theorem subd10_7_282 : subd10_7 [2, 0, 6] = true := by decide +kernel
theorem subd10_7_283 : subd10_7 [2, 0, 7] = true := by decide +kernel
theorem subd10_7_284 : subd10_7 [2, 0, 8] = true := by decide +kernel
theorem subd10_7_285 : subd10_7 [2, 1] = true := by decide +kernel
theorem subd10_7_286 : subd10_7 [2, 2] = true := by decide +kernel
theorem sbd10_7_8 : ∀ q ∈ blkd10_7_8, subd10_7 q = true := by
  unfold blkd10_7_8
  exact List.forall_mem_cons.2 ⟨subd10_7_256, List.forall_mem_cons.2 ⟨subd10_7_257, List.forall_mem_cons.2 ⟨subd10_7_258, List.forall_mem_cons.2 ⟨subd10_7_259, List.forall_mem_cons.2 ⟨subd10_7_260, List.forall_mem_cons.2 ⟨subd10_7_261, List.forall_mem_cons.2 ⟨subd10_7_262, List.forall_mem_cons.2 ⟨subd10_7_263, List.forall_mem_cons.2 ⟨subd10_7_264, List.forall_mem_cons.2 ⟨subd10_7_265, List.forall_mem_cons.2 ⟨subd10_7_266, List.forall_mem_cons.2 ⟨subd10_7_267, List.forall_mem_cons.2 ⟨subd10_7_268, List.forall_mem_cons.2 ⟨subd10_7_269, List.forall_mem_cons.2 ⟨subd10_7_270, List.forall_mem_cons.2 ⟨subd10_7_271, List.forall_mem_cons.2 ⟨subd10_7_272, List.forall_mem_cons.2 ⟨subd10_7_273, List.forall_mem_cons.2 ⟨subd10_7_274, List.forall_mem_cons.2 ⟨subd10_7_275, List.forall_mem_cons.2 ⟨subd10_7_276, List.forall_mem_cons.2 ⟨subd10_7_277, List.forall_mem_cons.2 ⟨subd10_7_278, List.forall_mem_cons.2 ⟨subd10_7_279, List.forall_mem_cons.2 ⟨subd10_7_280, List.forall_mem_cons.2 ⟨subd10_7_281, List.forall_mem_cons.2 ⟨subd10_7_282, List.forall_mem_cons.2 ⟨subd10_7_283, List.forall_mem_cons.2 ⟨subd10_7_284, List.forall_mem_cons.2 ⟨subd10_7_285, List.forall_mem_cons.2 ⟨subd10_7_286, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-2] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-1, -3] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-1, -2] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-1, -1] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-1, 0, -7] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-1, 0, -6] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [-1, 0, -5] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [-1, 0, -4] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [-1, 0, -3] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [-1, 0, -2] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [-1, 0, -1] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [-1, 0, 0] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [-1, 0, 1] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [-1, 0, 2] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [-1, 0, 3] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [-1, 0, 4] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [-1, 0, 5] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [-1, 1] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [-1, 2] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [0, -3] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [0, -2] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [0, -1, -7] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [0, -1, -6] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [0, -1, -5] = true := by decide +kernel
theorem subd11_0_24 : subd11_0 [0, -1, -4] = true := by decide +kernel
theorem subd11_0_25 : subd11_0 [0, -1, -3] = true := by decide +kernel
theorem subd11_0_26 : subd11_0 [0, -1, -2] = true := by decide +kernel
theorem subd11_0_27 : subd11_0 [0, -1, -1] = true := by decide +kernel
theorem subd11_0_28 : subd11_0 [0, -1, 0] = true := by decide +kernel
theorem subd11_0_29 : subd11_0 [0, -1, 1] = true := by decide +kernel
theorem subd11_0_30 : subd11_0 [0, -1, 2] = true := by decide +kernel
theorem subd11_0_31 : subd11_0 [0, -1, 3] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_cons.2 ⟨subd11_0_24, List.forall_mem_cons.2 ⟨subd11_0_25, List.forall_mem_cons.2 ⟨subd11_0_26, List.forall_mem_cons.2 ⟨subd11_0_27, List.forall_mem_cons.2 ⟨subd11_0_28, List.forall_mem_cons.2 ⟨subd11_0_29, List.forall_mem_cons.2 ⟨subd11_0_30, List.forall_mem_cons.2 ⟨subd11_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_32 : subd11_0 [0, -1, 4] = true := by decide +kernel
theorem subd11_0_33 : subd11_0 [0, -1, 5] = true := by decide +kernel
theorem subd11_0_34 : subd11_0 [0, -1, 6] = true := by decide +kernel
theorem subd11_0_35 : subd11_0 [0, 0, -8] = true := by decide +kernel
theorem subd11_0_36 : subd11_0 [0, 0, -7] = true := by decide +kernel
theorem subd11_0_37 : subd11_0 [0, 0, -6] = true := by decide +kernel
theorem subd11_0_38 : subd11_0 [0, 0, -5] = true := by decide +kernel
theorem subd11_0_39 : subd11_0 [0, 0, -4] = true := by decide +kernel
theorem subd11_0_40 : subd11_0 [0, 0, -3] = true := by decide +kernel
theorem subd11_0_41 : subd11_0 [0, 0, -2] = true := by decide +kernel
theorem subd11_0_42 : subd11_0 [0, 0, -1] = true := by decide +kernel
theorem subd11_0_43 : subd11_0 [0, 0, 0] = true := by decide +kernel
theorem subd11_0_44 : subd11_0 [0, 0, 1] = true := by decide +kernel
theorem subd11_0_45 : subd11_0 [0, 0, 2] = true := by decide +kernel
theorem subd11_0_46 : subd11_0 [0, 0, 3] = true := by decide +kernel
theorem subd11_0_47 : subd11_0 [0, 0, 4] = true := by decide +kernel
theorem subd11_0_48 : subd11_0 [0, 0, 5] = true := by decide +kernel
theorem subd11_0_49 : subd11_0 [0, 0, 6] = true := by decide +kernel
theorem subd11_0_50 : subd11_0 [0, 0, 7] = true := by decide +kernel
theorem subd11_0_51 : subd11_0 [0, 1, -7] = true := by decide +kernel
theorem subd11_0_52 : subd11_0 [0, 1, -6] = true := by decide +kernel
theorem subd11_0_53 : subd11_0 [0, 1, -5] = true := by decide +kernel
theorem subd11_0_54 : subd11_0 [0, 1, -4] = true := by decide +kernel
theorem subd11_0_55 : subd11_0 [0, 1, -3] = true := by decide +kernel
theorem subd11_0_56 : subd11_0 [0, 1, -2] = true := by decide +kernel
theorem subd11_0_57 : subd11_0 [0, 1, -1] = true := by decide +kernel
theorem subd11_0_58 : subd11_0 [0, 1, 0] = true := by decide +kernel
theorem subd11_0_59 : subd11_0 [0, 1, 1] = true := by decide +kernel
theorem subd11_0_60 : subd11_0 [0, 1, 2] = true := by decide +kernel
theorem subd11_0_61 : subd11_0 [0, 1, 3] = true := by decide +kernel
theorem subd11_0_62 : subd11_0 [0, 1, 4] = true := by decide +kernel
theorem subd11_0_63 : subd11_0 [0, 1, 5] = true := by decide +kernel
theorem sbd11_0_1 : ∀ q ∈ blkd11_0_1, subd11_0 q = true := by
  unfold blkd11_0_1
  exact List.forall_mem_cons.2 ⟨subd11_0_32, List.forall_mem_cons.2 ⟨subd11_0_33, List.forall_mem_cons.2 ⟨subd11_0_34, List.forall_mem_cons.2 ⟨subd11_0_35, List.forall_mem_cons.2 ⟨subd11_0_36, List.forall_mem_cons.2 ⟨subd11_0_37, List.forall_mem_cons.2 ⟨subd11_0_38, List.forall_mem_cons.2 ⟨subd11_0_39, List.forall_mem_cons.2 ⟨subd11_0_40, List.forall_mem_cons.2 ⟨subd11_0_41, List.forall_mem_cons.2 ⟨subd11_0_42, List.forall_mem_cons.2 ⟨subd11_0_43, List.forall_mem_cons.2 ⟨subd11_0_44, List.forall_mem_cons.2 ⟨subd11_0_45, List.forall_mem_cons.2 ⟨subd11_0_46, List.forall_mem_cons.2 ⟨subd11_0_47, List.forall_mem_cons.2 ⟨subd11_0_48, List.forall_mem_cons.2 ⟨subd11_0_49, List.forall_mem_cons.2 ⟨subd11_0_50, List.forall_mem_cons.2 ⟨subd11_0_51, List.forall_mem_cons.2 ⟨subd11_0_52, List.forall_mem_cons.2 ⟨subd11_0_53, List.forall_mem_cons.2 ⟨subd11_0_54, List.forall_mem_cons.2 ⟨subd11_0_55, List.forall_mem_cons.2 ⟨subd11_0_56, List.forall_mem_cons.2 ⟨subd11_0_57, List.forall_mem_cons.2 ⟨subd11_0_58, List.forall_mem_cons.2 ⟨subd11_0_59, List.forall_mem_cons.2 ⟨subd11_0_60, List.forall_mem_cons.2 ⟨subd11_0_61, List.forall_mem_cons.2 ⟨subd11_0_62, List.forall_mem_cons.2 ⟨subd11_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_64 : subd11_0 [0, 1, 6] = true := by decide +kernel
theorem subd11_0_65 : subd11_0 [0, 2] = true := by decide +kernel
theorem subd11_0_66 : subd11_0 [1, -3] = true := by decide +kernel
theorem subd11_0_67 : subd11_0 [1, -2] = true := by decide +kernel
theorem subd11_0_68 : subd11_0 [1, -1] = true := by decide +kernel
theorem subd11_0_69 : subd11_0 [1, 0, -6] = true := by decide +kernel
theorem subd11_0_70 : subd11_0 [1, 0, -5] = true := by decide +kernel
theorem subd11_0_71 : subd11_0 [1, 0, -4] = true := by decide +kernel
theorem subd11_0_72 : subd11_0 [1, 0, -3] = true := by decide +kernel
theorem subd11_0_73 : subd11_0 [1, 0, -2] = true := by decide +kernel
theorem subd11_0_74 : subd11_0 [1, 0, -1] = true := by decide +kernel
theorem subd11_0_75 : subd11_0 [1, 0, 0] = true := by decide +kernel
theorem subd11_0_76 : subd11_0 [1, 0, 1] = true := by decide +kernel
theorem subd11_0_77 : subd11_0 [1, 0, 2] = true := by decide +kernel
theorem subd11_0_78 : subd11_0 [1, 0, 3] = true := by decide +kernel
theorem subd11_0_79 : subd11_0 [1, 0, 4] = true := by decide +kernel
theorem subd11_0_80 : subd11_0 [1, 0, 5] = true := by decide +kernel
theorem subd11_0_81 : subd11_0 [1, 0, 6] = true := by decide +kernel
theorem subd11_0_82 : subd11_0 [1, 1] = true := by decide +kernel
theorem subd11_0_83 : subd11_0 [1, 2] = true := by decide +kernel
theorem subd11_0_84 : subd11_0 [2] = true := by decide +kernel
theorem sbd11_0_2 : ∀ q ∈ blkd11_0_2, subd11_0 q = true := by
  unfold blkd11_0_2
  exact List.forall_mem_cons.2 ⟨subd11_0_64, List.forall_mem_cons.2 ⟨subd11_0_65, List.forall_mem_cons.2 ⟨subd11_0_66, List.forall_mem_cons.2 ⟨subd11_0_67, List.forall_mem_cons.2 ⟨subd11_0_68, List.forall_mem_cons.2 ⟨subd11_0_69, List.forall_mem_cons.2 ⟨subd11_0_70, List.forall_mem_cons.2 ⟨subd11_0_71, List.forall_mem_cons.2 ⟨subd11_0_72, List.forall_mem_cons.2 ⟨subd11_0_73, List.forall_mem_cons.2 ⟨subd11_0_74, List.forall_mem_cons.2 ⟨subd11_0_75, List.forall_mem_cons.2 ⟨subd11_0_76, List.forall_mem_cons.2 ⟨subd11_0_77, List.forall_mem_cons.2 ⟨subd11_0_78, List.forall_mem_cons.2 ⟨subd11_0_79, List.forall_mem_cons.2 ⟨subd11_0_80, List.forall_mem_cons.2 ⟨subd11_0_81, List.forall_mem_cons.2 ⟨subd11_0_82, List.forall_mem_cons.2 ⟨subd11_0_83, List.forall_mem_cons.2 ⟨subd11_0_84, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-3] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-2, -4] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-2, -3] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-2, -2, -6] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-2, -2, -5] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-2, -2, -4] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-2, -2, -3] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-2, -2, -2] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-2, -2, -1] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [-2, -2, 0] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [-2, -2, 1] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [-2, -2, 2] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [-2, -2, 3] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [-2, -2, 4] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [-2, -2, 5] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [-2, -2, 6] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [-2, -1, -8] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [-2, -1, -7] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [-2, -1, -6] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [-2, -1, -5] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [-2, -1, -4] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [-2, -1, -3] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [-2, -1, -2] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [-2, -1, -1] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [-2, -1, 0] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [-2, -1, 1] = true := by decide +kernel
theorem subd11_1_26 : subd11_1 [-2, -1, 2] = true := by decide +kernel
theorem subd11_1_27 : subd11_1 [-2, -1, 3] = true := by decide +kernel
theorem subd11_1_28 : subd11_1 [-2, -1, 4] = true := by decide +kernel
theorem subd11_1_29 : subd11_1 [-2, -1, 5] = true := by decide +kernel
theorem subd11_1_30 : subd11_1 [-2, -1, 6] = true := by decide +kernel
theorem subd11_1_31 : subd11_1 [-2, -1, 7] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_cons.2 ⟨subd11_1_26, List.forall_mem_cons.2 ⟨subd11_1_27, List.forall_mem_cons.2 ⟨subd11_1_28, List.forall_mem_cons.2 ⟨subd11_1_29, List.forall_mem_cons.2 ⟨subd11_1_30, List.forall_mem_cons.2 ⟨subd11_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
