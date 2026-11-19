import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_6_64 : subd10_6 [-1, -1, -2] = true := by decide +kernel
theorem subd10_6_65 : subd10_6 [-1, -1, -1] = true := by decide +kernel
theorem subd10_6_66 : subd10_6 [-1, -1, 0] = true := by decide +kernel
theorem subd10_6_67 : subd10_6 [-1, -1, 1] = true := by decide +kernel
theorem subd10_6_68 : subd10_6 [-1, -1, 2] = true := by decide +kernel
theorem subd10_6_69 : subd10_6 [-1, -1, 3] = true := by decide +kernel
theorem subd10_6_70 : subd10_6 [-1, -1, 4] = true := by decide +kernel
theorem subd10_6_71 : subd10_6 [-1, -1, 5] = true := by decide +kernel
theorem subd10_6_72 : subd10_6 [-1, -1, 6] = true := by decide +kernel
theorem subd10_6_73 : subd10_6 [-1, -1, 7] = true := by decide +kernel
theorem subd10_6_74 : subd10_6 [-1, -1, 8] = true := by decide +kernel
theorem subd10_6_75 : subd10_6 [-1, 0, -9] = true := by decide +kernel
theorem subd10_6_76 : subd10_6 [-1, 0, -8] = true := by decide +kernel
theorem subd10_6_77 : subd10_6 [-1, 0, -7] = true := by decide +kernel
theorem subd10_6_78 : subd10_6 [-1, 0, -6] = true := by decide +kernel
theorem subd10_6_79 : subd10_6 [-1, 0, -5] = true := by decide +kernel
theorem subd10_6_80 : subd10_6 [-1, 0, -4] = true := by decide +kernel
theorem subd10_6_81 : subd10_6 [-1, 0, -3] = true := by decide +kernel
theorem subd10_6_82 : subd10_6 [-1, 0, -2] = true := by decide +kernel
theorem subd10_6_83 : subd10_6 [-1, 0, -1] = true := by decide +kernel
theorem subd10_6_84 : subd10_6 [-1, 0, 0] = true := by decide +kernel
theorem subd10_6_85 : subd10_6 [-1, 0, 1] = true := by decide +kernel
theorem subd10_6_86 : subd10_6 [-1, 0, 2] = true := by decide +kernel
theorem subd10_6_87 : subd10_6 [-1, 0, 3] = true := by decide +kernel
theorem subd10_6_88 : subd10_6 [-1, 0, 4] = true := by decide +kernel
theorem subd10_6_89 : subd10_6 [-1, 0, 5] = true := by decide +kernel
theorem subd10_6_90 : subd10_6 [-1, 0, 6] = true := by decide +kernel
theorem subd10_6_91 : subd10_6 [-1, 0, 7] = true := by decide +kernel
theorem subd10_6_92 : subd10_6 [-1, 0, 8] = true := by decide +kernel
theorem subd10_6_93 : subd10_6 [-1, 1, -9] = true := by decide +kernel
theorem subd10_6_94 : subd10_6 [-1, 1, -8] = true := by decide +kernel
theorem subd10_6_95 : subd10_6 [-1, 1, -7] = true := by decide +kernel
theorem sbd10_6_2 : ∀ q ∈ blkd10_6_2, subd10_6 q = true := by
  unfold blkd10_6_2
  exact List.forall_mem_cons.2 ⟨subd10_6_64, List.forall_mem_cons.2 ⟨subd10_6_65, List.forall_mem_cons.2 ⟨subd10_6_66, List.forall_mem_cons.2 ⟨subd10_6_67, List.forall_mem_cons.2 ⟨subd10_6_68, List.forall_mem_cons.2 ⟨subd10_6_69, List.forall_mem_cons.2 ⟨subd10_6_70, List.forall_mem_cons.2 ⟨subd10_6_71, List.forall_mem_cons.2 ⟨subd10_6_72, List.forall_mem_cons.2 ⟨subd10_6_73, List.forall_mem_cons.2 ⟨subd10_6_74, List.forall_mem_cons.2 ⟨subd10_6_75, List.forall_mem_cons.2 ⟨subd10_6_76, List.forall_mem_cons.2 ⟨subd10_6_77, List.forall_mem_cons.2 ⟨subd10_6_78, List.forall_mem_cons.2 ⟨subd10_6_79, List.forall_mem_cons.2 ⟨subd10_6_80, List.forall_mem_cons.2 ⟨subd10_6_81, List.forall_mem_cons.2 ⟨subd10_6_82, List.forall_mem_cons.2 ⟨subd10_6_83, List.forall_mem_cons.2 ⟨subd10_6_84, List.forall_mem_cons.2 ⟨subd10_6_85, List.forall_mem_cons.2 ⟨subd10_6_86, List.forall_mem_cons.2 ⟨subd10_6_87, List.forall_mem_cons.2 ⟨subd10_6_88, List.forall_mem_cons.2 ⟨subd10_6_89, List.forall_mem_cons.2 ⟨subd10_6_90, List.forall_mem_cons.2 ⟨subd10_6_91, List.forall_mem_cons.2 ⟨subd10_6_92, List.forall_mem_cons.2 ⟨subd10_6_93, List.forall_mem_cons.2 ⟨subd10_6_94, List.forall_mem_cons.2 ⟨subd10_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_96 : subd10_6 [-1, 1, -6] = true := by decide +kernel
theorem subd10_6_97 : subd10_6 [-1, 1, -5] = true := by decide +kernel
theorem subd10_6_98 : subd10_6 [-1, 1, -4] = true := by decide +kernel
theorem subd10_6_99 : subd10_6 [-1, 1, -3] = true := by decide +kernel
theorem subd10_6_100 : subd10_6 [-1, 1, -2] = true := by decide +kernel
theorem subd10_6_101 : subd10_6 [-1, 1, -1] = true := by decide +kernel
theorem subd10_6_102 : subd10_6 [-1, 1, 0] = true := by decide +kernel
theorem subd10_6_103 : subd10_6 [-1, 1, 1] = true := by decide +kernel
theorem subd10_6_104 : subd10_6 [-1, 1, 2] = true := by decide +kernel
theorem subd10_6_105 : subd10_6 [-1, 1, 3] = true := by decide +kernel
theorem subd10_6_106 : subd10_6 [-1, 1, 4] = true := by decide +kernel
theorem subd10_6_107 : subd10_6 [-1, 1, 5] = true := by decide +kernel
theorem subd10_6_108 : subd10_6 [-1, 1, 6] = true := by decide +kernel
theorem subd10_6_109 : subd10_6 [-1, 1, 7] = true := by decide +kernel
theorem subd10_6_110 : subd10_6 [-1, 1, 8] = true := by decide +kernel
theorem subd10_6_111 : subd10_6 [-1, 2, -8] = true := by decide +kernel
theorem subd10_6_112 : subd10_6 [-1, 2, -7] = true := by decide +kernel
theorem subd10_6_113 : subd10_6 [-1, 2, -6] = true := by decide +kernel
theorem subd10_6_114 : subd10_6 [-1, 2, -5] = true := by decide +kernel
theorem subd10_6_115 : subd10_6 [-1, 2, -4] = true := by decide +kernel
theorem subd10_6_116 : subd10_6 [-1, 2, -3] = true := by decide +kernel
theorem subd10_6_117 : subd10_6 [-1, 2, -2] = true := by decide +kernel
theorem subd10_6_118 : subd10_6 [-1, 2, -1] = true := by decide +kernel
theorem subd10_6_119 : subd10_6 [-1, 2, 0] = true := by decide +kernel
theorem subd10_6_120 : subd10_6 [-1, 2, 1] = true := by decide +kernel
theorem subd10_6_121 : subd10_6 [-1, 2, 2] = true := by decide +kernel
theorem subd10_6_122 : subd10_6 [-1, 2, 3] = true := by decide +kernel
theorem subd10_6_123 : subd10_6 [-1, 2, 4] = true := by decide +kernel
theorem subd10_6_124 : subd10_6 [-1, 2, 5] = true := by decide +kernel
theorem subd10_6_125 : subd10_6 [-1, 2, 6] = true := by decide +kernel
theorem subd10_6_126 : subd10_6 [-1, 3] = true := by decide +kernel
theorem subd10_6_127 : subd10_6 [0, -4] = true := by decide +kernel
theorem sbd10_6_3 : ∀ q ∈ blkd10_6_3, subd10_6 q = true := by
  unfold blkd10_6_3
  exact List.forall_mem_cons.2 ⟨subd10_6_96, List.forall_mem_cons.2 ⟨subd10_6_97, List.forall_mem_cons.2 ⟨subd10_6_98, List.forall_mem_cons.2 ⟨subd10_6_99, List.forall_mem_cons.2 ⟨subd10_6_100, List.forall_mem_cons.2 ⟨subd10_6_101, List.forall_mem_cons.2 ⟨subd10_6_102, List.forall_mem_cons.2 ⟨subd10_6_103, List.forall_mem_cons.2 ⟨subd10_6_104, List.forall_mem_cons.2 ⟨subd10_6_105, List.forall_mem_cons.2 ⟨subd10_6_106, List.forall_mem_cons.2 ⟨subd10_6_107, List.forall_mem_cons.2 ⟨subd10_6_108, List.forall_mem_cons.2 ⟨subd10_6_109, List.forall_mem_cons.2 ⟨subd10_6_110, List.forall_mem_cons.2 ⟨subd10_6_111, List.forall_mem_cons.2 ⟨subd10_6_112, List.forall_mem_cons.2 ⟨subd10_6_113, List.forall_mem_cons.2 ⟨subd10_6_114, List.forall_mem_cons.2 ⟨subd10_6_115, List.forall_mem_cons.2 ⟨subd10_6_116, List.forall_mem_cons.2 ⟨subd10_6_117, List.forall_mem_cons.2 ⟨subd10_6_118, List.forall_mem_cons.2 ⟨subd10_6_119, List.forall_mem_cons.2 ⟨subd10_6_120, List.forall_mem_cons.2 ⟨subd10_6_121, List.forall_mem_cons.2 ⟨subd10_6_122, List.forall_mem_cons.2 ⟨subd10_6_123, List.forall_mem_cons.2 ⟨subd10_6_124, List.forall_mem_cons.2 ⟨subd10_6_125, List.forall_mem_cons.2 ⟨subd10_6_126, List.forall_mem_cons.2 ⟨subd10_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_128 : subd10_6 [0, -3] = true := by decide +kernel
theorem subd10_6_129 : subd10_6 [0, -2, -7] = true := by decide +kernel
theorem subd10_6_130 : subd10_6 [0, -2, -6] = true := by decide +kernel
theorem subd10_6_131 : subd10_6 [0, -2, -5] = true := by decide +kernel
theorem subd10_6_132 : subd10_6 [0, -2, -4] = true := by decide +kernel
theorem subd10_6_133 : subd10_6 [0, -2, -3] = true := by decide +kernel
theorem subd10_6_134 : subd10_6 [0, -2, -2] = true := by decide +kernel
theorem subd10_6_135 : subd10_6 [0, -2, -1] = true := by decide +kernel
theorem subd10_6_136 : subd10_6 [0, -2, 0] = true := by decide +kernel
theorem subd10_6_137 : subd10_6 [0, -2, 1] = true := by decide +kernel
theorem subd10_6_138 : subd10_6 [0, -2, 2] = true := by decide +kernel
theorem subd10_6_139 : subd10_6 [0, -2, 3] = true := by decide +kernel
theorem subd10_6_140 : subd10_6 [0, -2, 4] = true := by decide +kernel
theorem subd10_6_141 : subd10_6 [0, -2, 5] = true := by decide +kernel
theorem subd10_6_142 : subd10_6 [0, -2, 6] = true := by decide +kernel
theorem subd10_6_143 : subd10_6 [0, -2, 7] = true := by decide +kernel
theorem subd10_6_144 : subd10_6 [0, -2, 8] = true := by decide +kernel
theorem subd10_6_145 : subd10_6 [0, -1, -9] = true := by decide +kernel
theorem subd10_6_146 : subd10_6 [0, -1, -8] = true := by decide +kernel
theorem subd10_6_147 : subd10_6 [0, -1, -7] = true := by decide +kernel
theorem subd10_6_148 : subd10_6 [0, -1, -6] = true := by decide +kernel
theorem subd10_6_149 : subd10_6 [0, -1, -5] = true := by decide +kernel
theorem subd10_6_150 : subd10_6 [0, -1, -4] = true := by decide +kernel
theorem subd10_6_151 : subd10_6 [0, -1, -3] = true := by decide +kernel
theorem subd10_6_152 : subd10_6 [0, -1, -2] = true := by decide +kernel
theorem subd10_6_153 : subd10_6 [0, -1, -1] = true := by decide +kernel
theorem subd10_6_154 : subd10_6 [0, -1, 0] = true := by decide +kernel
theorem subd10_6_155 : subd10_6 [0, -1, 1] = true := by decide +kernel
theorem subd10_6_156 : subd10_6 [0, -1, 2] = true := by decide +kernel
theorem subd10_6_157 : subd10_6 [0, -1, 3] = true := by decide +kernel
theorem subd10_6_158 : subd10_6 [0, -1, 4] = true := by decide +kernel
theorem subd10_6_159 : subd10_6 [0, -1, 5] = true := by decide +kernel
theorem sbd10_6_4 : ∀ q ∈ blkd10_6_4, subd10_6 q = true := by
  unfold blkd10_6_4
  exact List.forall_mem_cons.2 ⟨subd10_6_128, List.forall_mem_cons.2 ⟨subd10_6_129, List.forall_mem_cons.2 ⟨subd10_6_130, List.forall_mem_cons.2 ⟨subd10_6_131, List.forall_mem_cons.2 ⟨subd10_6_132, List.forall_mem_cons.2 ⟨subd10_6_133, List.forall_mem_cons.2 ⟨subd10_6_134, List.forall_mem_cons.2 ⟨subd10_6_135, List.forall_mem_cons.2 ⟨subd10_6_136, List.forall_mem_cons.2 ⟨subd10_6_137, List.forall_mem_cons.2 ⟨subd10_6_138, List.forall_mem_cons.2 ⟨subd10_6_139, List.forall_mem_cons.2 ⟨subd10_6_140, List.forall_mem_cons.2 ⟨subd10_6_141, List.forall_mem_cons.2 ⟨subd10_6_142, List.forall_mem_cons.2 ⟨subd10_6_143, List.forall_mem_cons.2 ⟨subd10_6_144, List.forall_mem_cons.2 ⟨subd10_6_145, List.forall_mem_cons.2 ⟨subd10_6_146, List.forall_mem_cons.2 ⟨subd10_6_147, List.forall_mem_cons.2 ⟨subd10_6_148, List.forall_mem_cons.2 ⟨subd10_6_149, List.forall_mem_cons.2 ⟨subd10_6_150, List.forall_mem_cons.2 ⟨subd10_6_151, List.forall_mem_cons.2 ⟨subd10_6_152, List.forall_mem_cons.2 ⟨subd10_6_153, List.forall_mem_cons.2 ⟨subd10_6_154, List.forall_mem_cons.2 ⟨subd10_6_155, List.forall_mem_cons.2 ⟨subd10_6_156, List.forall_mem_cons.2 ⟨subd10_6_157, List.forall_mem_cons.2 ⟨subd10_6_158, List.forall_mem_cons.2 ⟨subd10_6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_160 : subd10_6 [0, -1, 6] = true := by decide +kernel
theorem subd10_6_161 : subd10_6 [0, -1, 7] = true := by decide +kernel
theorem subd10_6_162 : subd10_6 [0, -1, 8] = true := by decide +kernel
theorem subd10_6_163 : subd10_6 [0, 0, -9] = true := by decide +kernel
theorem subd10_6_164 : subd10_6 [0, 0, -8] = true := by decide +kernel
theorem subd10_6_165 : subd10_6 [0, 0, -7] = true := by decide +kernel
theorem subd10_6_166 : subd10_6 [0, 0, -6] = true := by decide +kernel
theorem subd10_6_167 : subd10_6 [0, 0, -5] = true := by decide +kernel
theorem subd10_6_168 : subd10_6 [0, 0, -4] = true := by decide +kernel
theorem subd10_6_169 : subd10_6 [0, 0, -3] = true := by decide +kernel
theorem subd10_6_170 : subd10_6 [0, 0, -2] = true := by decide +kernel
theorem subd10_6_171 : subd10_6 [0, 0, -1] = true := by decide +kernel
theorem subd10_6_172 : subd10_6 [0, 0, 0] = true := by decide +kernel
theorem subd10_6_173 : subd10_6 [0, 0, 1] = true := by decide +kernel
theorem subd10_6_174 : subd10_6 [0, 0, 2] = true := by decide +kernel
theorem subd10_6_175 : subd10_6 [0, 0, 3] = true := by decide +kernel
theorem subd10_6_176 : subd10_6 [0, 0, 4] = true := by decide +kernel
theorem subd10_6_177 : subd10_6 [0, 0, 5] = true := by decide +kernel
theorem subd10_6_178 : subd10_6 [0, 0, 6] = true := by decide +kernel
theorem subd10_6_179 : subd10_6 [0, 0, 7] = true := by decide +kernel
theorem subd10_6_180 : subd10_6 [0, 0, 8] = true := by decide +kernel
theorem subd10_6_181 : subd10_6 [0, 1, -9] = true := by decide +kernel
theorem subd10_6_182 : subd10_6 [0, 1, -8] = true := by decide +kernel
theorem subd10_6_183 : subd10_6 [0, 1, -7] = true := by decide +kernel
theorem subd10_6_184 : subd10_6 [0, 1, -6] = true := by decide +kernel
theorem subd10_6_185 : subd10_6 [0, 1, -5] = true := by decide +kernel
theorem subd10_6_186 : subd10_6 [0, 1, -4] = true := by decide +kernel
theorem subd10_6_187 : subd10_6 [0, 1, -3] = true := by decide +kernel
theorem subd10_6_188 : subd10_6 [0, 1, -2] = true := by decide +kernel
theorem subd10_6_189 : subd10_6 [0, 1, -1] = true := by decide +kernel
theorem subd10_6_190 : subd10_6 [0, 1, 0] = true := by decide +kernel
theorem subd10_6_191 : subd10_6 [0, 1, 1] = true := by decide +kernel
theorem sbd10_6_5 : ∀ q ∈ blkd10_6_5, subd10_6 q = true := by
  unfold blkd10_6_5
  exact List.forall_mem_cons.2 ⟨subd10_6_160, List.forall_mem_cons.2 ⟨subd10_6_161, List.forall_mem_cons.2 ⟨subd10_6_162, List.forall_mem_cons.2 ⟨subd10_6_163, List.forall_mem_cons.2 ⟨subd10_6_164, List.forall_mem_cons.2 ⟨subd10_6_165, List.forall_mem_cons.2 ⟨subd10_6_166, List.forall_mem_cons.2 ⟨subd10_6_167, List.forall_mem_cons.2 ⟨subd10_6_168, List.forall_mem_cons.2 ⟨subd10_6_169, List.forall_mem_cons.2 ⟨subd10_6_170, List.forall_mem_cons.2 ⟨subd10_6_171, List.forall_mem_cons.2 ⟨subd10_6_172, List.forall_mem_cons.2 ⟨subd10_6_173, List.forall_mem_cons.2 ⟨subd10_6_174, List.forall_mem_cons.2 ⟨subd10_6_175, List.forall_mem_cons.2 ⟨subd10_6_176, List.forall_mem_cons.2 ⟨subd10_6_177, List.forall_mem_cons.2 ⟨subd10_6_178, List.forall_mem_cons.2 ⟨subd10_6_179, List.forall_mem_cons.2 ⟨subd10_6_180, List.forall_mem_cons.2 ⟨subd10_6_181, List.forall_mem_cons.2 ⟨subd10_6_182, List.forall_mem_cons.2 ⟨subd10_6_183, List.forall_mem_cons.2 ⟨subd10_6_184, List.forall_mem_cons.2 ⟨subd10_6_185, List.forall_mem_cons.2 ⟨subd10_6_186, List.forall_mem_cons.2 ⟨subd10_6_187, List.forall_mem_cons.2 ⟨subd10_6_188, List.forall_mem_cons.2 ⟨subd10_6_189, List.forall_mem_cons.2 ⟨subd10_6_190, List.forall_mem_cons.2 ⟨subd10_6_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_192 : subd10_6 [0, 1, 2] = true := by decide +kernel
theorem subd10_6_193 : subd10_6 [0, 1, 3] = true := by decide +kernel
theorem subd10_6_194 : subd10_6 [0, 1, 4] = true := by decide +kernel
theorem subd10_6_195 : subd10_6 [0, 1, 5] = true := by decide +kernel
theorem subd10_6_196 : subd10_6 [0, 1, 6] = true := by decide +kernel
theorem subd10_6_197 : subd10_6 [0, 1, 7] = true := by decide +kernel
theorem subd10_6_198 : subd10_6 [0, 1, 8] = true := by decide +kernel
theorem subd10_6_199 : subd10_6 [0, 2, -9] = true := by decide +kernel
theorem subd10_6_200 : subd10_6 [0, 2, -8] = true := by decide +kernel
theorem subd10_6_201 : subd10_6 [0, 2, -7] = true := by decide +kernel
theorem subd10_6_202 : subd10_6 [0, 2, -6] = true := by decide +kernel
theorem subd10_6_203 : subd10_6 [0, 2, -5] = true := by decide +kernel
theorem subd10_6_204 : subd10_6 [0, 2, -4] = true := by decide +kernel
theorem subd10_6_205 : subd10_6 [0, 2, -3] = true := by decide +kernel
theorem subd10_6_206 : subd10_6 [0, 2, -2] = true := by decide +kernel
theorem subd10_6_207 : subd10_6 [0, 2, -1] = true := by decide +kernel
theorem subd10_6_208 : subd10_6 [0, 2, 0] = true := by decide +kernel
theorem subd10_6_209 : subd10_6 [0, 2, 1] = true := by decide +kernel
theorem subd10_6_210 : subd10_6 [0, 2, 2] = true := by decide +kernel
theorem subd10_6_211 : subd10_6 [0, 2, 3] = true := by decide +kernel
theorem subd10_6_212 : subd10_6 [0, 2, 4] = true := by decide +kernel
theorem subd10_6_213 : subd10_6 [0, 2, 5] = true := by decide +kernel
theorem subd10_6_214 : subd10_6 [0, 2, 6] = true := by decide +kernel
theorem subd10_6_215 : subd10_6 [0, 3] = true := by decide +kernel
theorem subd10_6_216 : subd10_6 [1, -4] = true := by decide +kernel
theorem subd10_6_217 : subd10_6 [1, -3] = true := by decide +kernel
theorem subd10_6_218 : subd10_6 [1, -2, -7] = true := by decide +kernel
theorem subd10_6_219 : subd10_6 [1, -2, -6] = true := by decide +kernel
theorem subd10_6_220 : subd10_6 [1, -2, -5] = true := by decide +kernel
theorem subd10_6_221 : subd10_6 [1, -2, -4] = true := by decide +kernel
theorem subd10_6_222 : subd10_6 [1, -2, -3] = true := by decide +kernel
theorem subd10_6_223 : subd10_6 [1, -2, -2] = true := by decide +kernel
theorem sbd10_6_6 : ∀ q ∈ blkd10_6_6, subd10_6 q = true := by
  unfold blkd10_6_6
  exact List.forall_mem_cons.2 ⟨subd10_6_192, List.forall_mem_cons.2 ⟨subd10_6_193, List.forall_mem_cons.2 ⟨subd10_6_194, List.forall_mem_cons.2 ⟨subd10_6_195, List.forall_mem_cons.2 ⟨subd10_6_196, List.forall_mem_cons.2 ⟨subd10_6_197, List.forall_mem_cons.2 ⟨subd10_6_198, List.forall_mem_cons.2 ⟨subd10_6_199, List.forall_mem_cons.2 ⟨subd10_6_200, List.forall_mem_cons.2 ⟨subd10_6_201, List.forall_mem_cons.2 ⟨subd10_6_202, List.forall_mem_cons.2 ⟨subd10_6_203, List.forall_mem_cons.2 ⟨subd10_6_204, List.forall_mem_cons.2 ⟨subd10_6_205, List.forall_mem_cons.2 ⟨subd10_6_206, List.forall_mem_cons.2 ⟨subd10_6_207, List.forall_mem_cons.2 ⟨subd10_6_208, List.forall_mem_cons.2 ⟨subd10_6_209, List.forall_mem_cons.2 ⟨subd10_6_210, List.forall_mem_cons.2 ⟨subd10_6_211, List.forall_mem_cons.2 ⟨subd10_6_212, List.forall_mem_cons.2 ⟨subd10_6_213, List.forall_mem_cons.2 ⟨subd10_6_214, List.forall_mem_cons.2 ⟨subd10_6_215, List.forall_mem_cons.2 ⟨subd10_6_216, List.forall_mem_cons.2 ⟨subd10_6_217, List.forall_mem_cons.2 ⟨subd10_6_218, List.forall_mem_cons.2 ⟨subd10_6_219, List.forall_mem_cons.2 ⟨subd10_6_220, List.forall_mem_cons.2 ⟨subd10_6_221, List.forall_mem_cons.2 ⟨subd10_6_222, List.forall_mem_cons.2 ⟨subd10_6_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_224 : subd10_6 [1, -2, -1] = true := by decide +kernel
theorem subd10_6_225 : subd10_6 [1, -2, 0] = true := by decide +kernel
theorem subd10_6_226 : subd10_6 [1, -2, 1] = true := by decide +kernel
theorem subd10_6_227 : subd10_6 [1, -2, 2] = true := by decide +kernel
theorem subd10_6_228 : subd10_6 [1, -2, 3] = true := by decide +kernel
theorem subd10_6_229 : subd10_6 [1, -2, 4] = true := by decide +kernel
theorem subd10_6_230 : subd10_6 [1, -2, 5] = true := by decide +kernel
theorem subd10_6_231 : subd10_6 [1, -2, 6] = true := by decide +kernel
theorem subd10_6_232 : subd10_6 [1, -2, 7] = true := by decide +kernel
theorem subd10_6_233 : subd10_6 [1, -1, -9] = true := by decide +kernel
theorem subd10_6_234 : subd10_6 [1, -1, -8] = true := by decide +kernel
theorem subd10_6_235 : subd10_6 [1, -1, -7] = true := by decide +kernel
theorem subd10_6_236 : subd10_6 [1, -1, -6] = true := by decide +kernel
theorem subd10_6_237 : subd10_6 [1, -1, -5] = true := by decide +kernel
theorem subd10_6_238 : subd10_6 [1, -1, -4] = true := by decide +kernel
theorem subd10_6_239 : subd10_6 [1, -1, -3] = true := by decide +kernel
theorem subd10_6_240 : subd10_6 [1, -1, -2] = true := by decide +kernel
theorem subd10_6_241 : subd10_6 [1, -1, -1] = true := by decide +kernel
theorem subd10_6_242 : subd10_6 [1, -1, 0] = true := by decide +kernel
theorem subd10_6_243 : subd10_6 [1, -1, 1] = true := by decide +kernel
theorem subd10_6_244 : subd10_6 [1, -1, 2] = true := by decide +kernel
theorem subd10_6_245 : subd10_6 [1, -1, 3] = true := by decide +kernel
theorem subd10_6_246 : subd10_6 [1, -1, 4] = true := by decide +kernel
theorem subd10_6_247 : subd10_6 [1, -1, 5] = true := by decide +kernel
theorem subd10_6_248 : subd10_6 [1, -1, 6] = true := by decide +kernel
theorem subd10_6_249 : subd10_6 [1, -1, 7] = true := by decide +kernel
theorem subd10_6_250 : subd10_6 [1, -1, 8] = true := by decide +kernel
theorem subd10_6_251 : subd10_6 [1, 0, -9] = true := by decide +kernel
theorem subd10_6_252 : subd10_6 [1, 0, -8] = true := by decide +kernel
theorem subd10_6_253 : subd10_6 [1, 0, -7] = true := by decide +kernel
theorem subd10_6_254 : subd10_6 [1, 0, -6] = true := by decide +kernel
theorem subd10_6_255 : subd10_6 [1, 0, -5] = true := by decide +kernel
theorem sbd10_6_7 : ∀ q ∈ blkd10_6_7, subd10_6 q = true := by
  unfold blkd10_6_7
  exact List.forall_mem_cons.2 ⟨subd10_6_224, List.forall_mem_cons.2 ⟨subd10_6_225, List.forall_mem_cons.2 ⟨subd10_6_226, List.forall_mem_cons.2 ⟨subd10_6_227, List.forall_mem_cons.2 ⟨subd10_6_228, List.forall_mem_cons.2 ⟨subd10_6_229, List.forall_mem_cons.2 ⟨subd10_6_230, List.forall_mem_cons.2 ⟨subd10_6_231, List.forall_mem_cons.2 ⟨subd10_6_232, List.forall_mem_cons.2 ⟨subd10_6_233, List.forall_mem_cons.2 ⟨subd10_6_234, List.forall_mem_cons.2 ⟨subd10_6_235, List.forall_mem_cons.2 ⟨subd10_6_236, List.forall_mem_cons.2 ⟨subd10_6_237, List.forall_mem_cons.2 ⟨subd10_6_238, List.forall_mem_cons.2 ⟨subd10_6_239, List.forall_mem_cons.2 ⟨subd10_6_240, List.forall_mem_cons.2 ⟨subd10_6_241, List.forall_mem_cons.2 ⟨subd10_6_242, List.forall_mem_cons.2 ⟨subd10_6_243, List.forall_mem_cons.2 ⟨subd10_6_244, List.forall_mem_cons.2 ⟨subd10_6_245, List.forall_mem_cons.2 ⟨subd10_6_246, List.forall_mem_cons.2 ⟨subd10_6_247, List.forall_mem_cons.2 ⟨subd10_6_248, List.forall_mem_cons.2 ⟨subd10_6_249, List.forall_mem_cons.2 ⟨subd10_6_250, List.forall_mem_cons.2 ⟨subd10_6_251, List.forall_mem_cons.2 ⟨subd10_6_252, List.forall_mem_cons.2 ⟨subd10_6_253, List.forall_mem_cons.2 ⟨subd10_6_254, List.forall_mem_cons.2 ⟨subd10_6_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_256 : subd10_6 [1, 0, -4] = true := by decide +kernel
theorem subd10_6_257 : subd10_6 [1, 0, -3] = true := by decide +kernel
theorem subd10_6_258 : subd10_6 [1, 0, -2] = true := by decide +kernel
theorem subd10_6_259 : subd10_6 [1, 0, -1] = true := by decide +kernel
theorem subd10_6_260 : subd10_6 [1, 0, 0] = true := by decide +kernel
theorem subd10_6_261 : subd10_6 [1, 0, 1] = true := by decide +kernel
theorem subd10_6_262 : subd10_6 [1, 0, 2] = true := by decide +kernel
theorem subd10_6_263 : subd10_6 [1, 0, 3] = true := by decide +kernel
theorem subd10_6_264 : subd10_6 [1, 0, 4] = true := by decide +kernel
theorem subd10_6_265 : subd10_6 [1, 0, 5] = true := by decide +kernel
theorem subd10_6_266 : subd10_6 [1, 0, 6] = true := by decide +kernel
theorem subd10_6_267 : subd10_6 [1, 0, 7] = true := by decide +kernel
theorem subd10_6_268 : subd10_6 [1, 0, 8] = true := by decide +kernel
theorem subd10_6_269 : subd10_6 [1, 1, -9] = true := by decide +kernel
theorem subd10_6_270 : subd10_6 [1, 1, -8] = true := by decide +kernel
theorem subd10_6_271 : subd10_6 [1, 1, -7] = true := by decide +kernel
theorem subd10_6_272 : subd10_6 [1, 1, -6] = true := by decide +kernel
theorem subd10_6_273 : subd10_6 [1, 1, -5] = true := by decide +kernel
theorem subd10_6_274 : subd10_6 [1, 1, -4] = true := by decide +kernel
theorem subd10_6_275 : subd10_6 [1, 1, -3] = true := by decide +kernel
theorem subd10_6_276 : subd10_6 [1, 1, -2] = true := by decide +kernel
theorem subd10_6_277 : subd10_6 [1, 1, -1] = true := by decide +kernel
theorem subd10_6_278 : subd10_6 [1, 1, 0] = true := by decide +kernel
theorem subd10_6_279 : subd10_6 [1, 1, 1] = true := by decide +kernel
theorem subd10_6_280 : subd10_6 [1, 1, 2] = true := by decide +kernel
theorem subd10_6_281 : subd10_6 [1, 1, 3] = true := by decide +kernel
theorem subd10_6_282 : subd10_6 [1, 1, 4] = true := by decide +kernel
theorem subd10_6_283 : subd10_6 [1, 1, 5] = true := by decide +kernel
theorem subd10_6_284 : subd10_6 [1, 1, 6] = true := by decide +kernel
theorem subd10_6_285 : subd10_6 [1, 1, 7] = true := by decide +kernel
theorem subd10_6_286 : subd10_6 [1, 2, -8] = true := by decide +kernel
theorem subd10_6_287 : subd10_6 [1, 2, -7] = true := by decide +kernel
theorem sbd10_6_8 : ∀ q ∈ blkd10_6_8, subd10_6 q = true := by
  unfold blkd10_6_8
  exact List.forall_mem_cons.2 ⟨subd10_6_256, List.forall_mem_cons.2 ⟨subd10_6_257, List.forall_mem_cons.2 ⟨subd10_6_258, List.forall_mem_cons.2 ⟨subd10_6_259, List.forall_mem_cons.2 ⟨subd10_6_260, List.forall_mem_cons.2 ⟨subd10_6_261, List.forall_mem_cons.2 ⟨subd10_6_262, List.forall_mem_cons.2 ⟨subd10_6_263, List.forall_mem_cons.2 ⟨subd10_6_264, List.forall_mem_cons.2 ⟨subd10_6_265, List.forall_mem_cons.2 ⟨subd10_6_266, List.forall_mem_cons.2 ⟨subd10_6_267, List.forall_mem_cons.2 ⟨subd10_6_268, List.forall_mem_cons.2 ⟨subd10_6_269, List.forall_mem_cons.2 ⟨subd10_6_270, List.forall_mem_cons.2 ⟨subd10_6_271, List.forall_mem_cons.2 ⟨subd10_6_272, List.forall_mem_cons.2 ⟨subd10_6_273, List.forall_mem_cons.2 ⟨subd10_6_274, List.forall_mem_cons.2 ⟨subd10_6_275, List.forall_mem_cons.2 ⟨subd10_6_276, List.forall_mem_cons.2 ⟨subd10_6_277, List.forall_mem_cons.2 ⟨subd10_6_278, List.forall_mem_cons.2 ⟨subd10_6_279, List.forall_mem_cons.2 ⟨subd10_6_280, List.forall_mem_cons.2 ⟨subd10_6_281, List.forall_mem_cons.2 ⟨subd10_6_282, List.forall_mem_cons.2 ⟨subd10_6_283, List.forall_mem_cons.2 ⟨subd10_6_284, List.forall_mem_cons.2 ⟨subd10_6_285, List.forall_mem_cons.2 ⟨subd10_6_286, List.forall_mem_cons.2 ⟨subd10_6_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_288 : subd10_6 [1, 2, -6] = true := by decide +kernel
theorem subd10_6_289 : subd10_6 [1, 2, -5] = true := by decide +kernel
theorem subd10_6_290 : subd10_6 [1, 2, -4] = true := by decide +kernel
theorem subd10_6_291 : subd10_6 [1, 2, -3] = true := by decide +kernel
theorem subd10_6_292 : subd10_6 [1, 2, -2] = true := by decide +kernel
theorem subd10_6_293 : subd10_6 [1, 2, -1] = true := by decide +kernel
theorem subd10_6_294 : subd10_6 [1, 2, 0] = true := by decide +kernel
theorem subd10_6_295 : subd10_6 [1, 2, 1] = true := by decide +kernel
theorem subd10_6_296 : subd10_6 [1, 2, 2] = true := by decide +kernel
theorem subd10_6_297 : subd10_6 [1, 2, 3] = true := by decide +kernel
theorem subd10_6_298 : subd10_6 [1, 2, 4] = true := by decide +kernel
theorem subd10_6_299 : subd10_6 [1, 2, 5] = true := by decide +kernel
theorem subd10_6_300 : subd10_6 [1, 2, 6] = true := by decide +kernel
theorem subd10_6_301 : subd10_6 [1, 3] = true := by decide +kernel
theorem subd10_6_302 : subd10_6 [2, -4] = true := by decide +kernel
theorem subd10_6_303 : subd10_6 [2, -3] = true := by decide +kernel
theorem subd10_6_304 : subd10_6 [2, -2] = true := by decide +kernel
theorem subd10_6_305 : subd10_6 [2, -1, -8] = true := by decide +kernel
theorem subd10_6_306 : subd10_6 [2, -1, -7] = true := by decide +kernel
theorem subd10_6_307 : subd10_6 [2, -1, -6] = true := by decide +kernel
theorem subd10_6_308 : subd10_6 [2, -1, -5] = true := by decide +kernel
theorem subd10_6_309 : subd10_6 [2, -1, -4] = true := by decide +kernel
theorem subd10_6_310 : subd10_6 [2, -1, -3] = true := by decide +kernel
theorem subd10_6_311 : subd10_6 [2, -1, -2] = true := by decide +kernel
theorem subd10_6_312 : subd10_6 [2, -1, -1] = true := by decide +kernel
theorem subd10_6_313 : subd10_6 [2, -1, 0] = true := by decide +kernel
theorem subd10_6_314 : subd10_6 [2, -1, 1] = true := by decide +kernel
theorem subd10_6_315 : subd10_6 [2, -1, 2] = true := by decide +kernel
theorem subd10_6_316 : subd10_6 [2, -1, 3] = true := by decide +kernel
theorem subd10_6_317 : subd10_6 [2, -1, 4] = true := by decide +kernel
theorem subd10_6_318 : subd10_6 [2, -1, 5] = true := by decide +kernel
theorem subd10_6_319 : subd10_6 [2, -1, 6] = true := by decide +kernel
theorem sbd10_6_9 : ∀ q ∈ blkd10_6_9, subd10_6 q = true := by
  unfold blkd10_6_9
  exact List.forall_mem_cons.2 ⟨subd10_6_288, List.forall_mem_cons.2 ⟨subd10_6_289, List.forall_mem_cons.2 ⟨subd10_6_290, List.forall_mem_cons.2 ⟨subd10_6_291, List.forall_mem_cons.2 ⟨subd10_6_292, List.forall_mem_cons.2 ⟨subd10_6_293, List.forall_mem_cons.2 ⟨subd10_6_294, List.forall_mem_cons.2 ⟨subd10_6_295, List.forall_mem_cons.2 ⟨subd10_6_296, List.forall_mem_cons.2 ⟨subd10_6_297, List.forall_mem_cons.2 ⟨subd10_6_298, List.forall_mem_cons.2 ⟨subd10_6_299, List.forall_mem_cons.2 ⟨subd10_6_300, List.forall_mem_cons.2 ⟨subd10_6_301, List.forall_mem_cons.2 ⟨subd10_6_302, List.forall_mem_cons.2 ⟨subd10_6_303, List.forall_mem_cons.2 ⟨subd10_6_304, List.forall_mem_cons.2 ⟨subd10_6_305, List.forall_mem_cons.2 ⟨subd10_6_306, List.forall_mem_cons.2 ⟨subd10_6_307, List.forall_mem_cons.2 ⟨subd10_6_308, List.forall_mem_cons.2 ⟨subd10_6_309, List.forall_mem_cons.2 ⟨subd10_6_310, List.forall_mem_cons.2 ⟨subd10_6_311, List.forall_mem_cons.2 ⟨subd10_6_312, List.forall_mem_cons.2 ⟨subd10_6_313, List.forall_mem_cons.2 ⟨subd10_6_314, List.forall_mem_cons.2 ⟨subd10_6_315, List.forall_mem_cons.2 ⟨subd10_6_316, List.forall_mem_cons.2 ⟨subd10_6_317, List.forall_mem_cons.2 ⟨subd10_6_318, List.forall_mem_cons.2 ⟨subd10_6_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_320 : subd10_6 [2, -1, 7] = true := by decide +kernel
theorem subd10_6_321 : subd10_6 [2, 0, -8] = true := by decide +kernel
theorem subd10_6_322 : subd10_6 [2, 0, -7] = true := by decide +kernel
theorem subd10_6_323 : subd10_6 [2, 0, -6] = true := by decide +kernel
theorem subd10_6_324 : subd10_6 [2, 0, -5] = true := by decide +kernel
theorem subd10_6_325 : subd10_6 [2, 0, -4] = true := by decide +kernel
theorem subd10_6_326 : subd10_6 [2, 0, -3] = true := by decide +kernel
theorem subd10_6_327 : subd10_6 [2, 0, -2] = true := by decide +kernel
theorem subd10_6_328 : subd10_6 [2, 0, -1] = true := by decide +kernel
theorem subd10_6_329 : subd10_6 [2, 0, 0] = true := by decide +kernel
theorem subd10_6_330 : subd10_6 [2, 0, 1] = true := by decide +kernel
theorem subd10_6_331 : subd10_6 [2, 0, 2] = true := by decide +kernel
theorem subd10_6_332 : subd10_6 [2, 0, 3] = true := by decide +kernel
theorem subd10_6_333 : subd10_6 [2, 0, 4] = true := by decide +kernel
theorem subd10_6_334 : subd10_6 [2, 0, 5] = true := by decide +kernel
theorem subd10_6_335 : subd10_6 [2, 0, 6] = true := by decide +kernel
theorem subd10_6_336 : subd10_6 [2, 1] = true := by decide +kernel
theorem subd10_6_337 : subd10_6 [2, 2] = true := by decide +kernel
theorem subd10_6_338 : subd10_6 [3, -3] = true := by decide +kernel
theorem subd10_6_339 : subd10_6 [3, -2] = true := by decide +kernel
theorem subd10_6_340 : subd10_6 [3, -1] = true := by decide +kernel
theorem subd10_6_341 : subd10_6 [3, 0] = true := by decide +kernel
theorem subd10_6_342 : subd10_6 [3, 1] = true := by decide +kernel
theorem sbd10_6_10 : ∀ q ∈ blkd10_6_10, subd10_6 q = true := by
  unfold blkd10_6_10
  exact List.forall_mem_cons.2 ⟨subd10_6_320, List.forall_mem_cons.2 ⟨subd10_6_321, List.forall_mem_cons.2 ⟨subd10_6_322, List.forall_mem_cons.2 ⟨subd10_6_323, List.forall_mem_cons.2 ⟨subd10_6_324, List.forall_mem_cons.2 ⟨subd10_6_325, List.forall_mem_cons.2 ⟨subd10_6_326, List.forall_mem_cons.2 ⟨subd10_6_327, List.forall_mem_cons.2 ⟨subd10_6_328, List.forall_mem_cons.2 ⟨subd10_6_329, List.forall_mem_cons.2 ⟨subd10_6_330, List.forall_mem_cons.2 ⟨subd10_6_331, List.forall_mem_cons.2 ⟨subd10_6_332, List.forall_mem_cons.2 ⟨subd10_6_333, List.forall_mem_cons.2 ⟨subd10_6_334, List.forall_mem_cons.2 ⟨subd10_6_335, List.forall_mem_cons.2 ⟨subd10_6_336, List.forall_mem_cons.2 ⟨subd10_6_337, List.forall_mem_cons.2 ⟨subd10_6_338, List.forall_mem_cons.2 ⟨subd10_6_339, List.forall_mem_cons.2 ⟨subd10_6_340, List.forall_mem_cons.2 ⟨subd10_6_341, List.forall_mem_cons.2 ⟨subd10_6_342, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_7 : ldCheck G d10_7.U d10_7.ms ldd10_7 = true := by decide +kernel
theorem pre_okd10_7 : subPre G cell10 d10_7 = true := by decide +kernel
theorem subd10_7_0 : subd10_7 [-4] = true := by decide +kernel
theorem subd10_7_1 : subd10_7 [-3, -4] = true := by decide +kernel
theorem subd10_7_2 : subd10_7 [-3, -3] = true := by decide +kernel
theorem subd10_7_3 : subd10_7 [-3, -2] = true := by decide +kernel
theorem subd10_7_4 : subd10_7 [-3, -1] = true := by decide +kernel
theorem subd10_7_5 : subd10_7 [-3, 0] = true := by decide +kernel
theorem subd10_7_6 : subd10_7 [-3, 1] = true := by decide +kernel
theorem subd10_7_7 : subd10_7 [-3, 2] = true := by decide +kernel
theorem subd10_7_8 : subd10_7 [-3, 3] = true := by decide +kernel
theorem subd10_7_9 : subd10_7 [-3, 4] = true := by decide +kernel
theorem subd10_7_10 : subd10_7 [-3, 5] = true := by decide +kernel
theorem subd10_7_11 : subd10_7 [-2, -5] = true := by decide +kernel
theorem subd10_7_12 : subd10_7 [-2, -4] = true := by decide +kernel
theorem subd10_7_13 : subd10_7 [-2, -3] = true := by decide +kernel
theorem subd10_7_14 : subd10_7 [-2, -2] = true := by decide +kernel
theorem subd10_7_15 : subd10_7 [-2, -1] = true := by decide +kernel
theorem subd10_7_16 : subd10_7 [-2, 0] = true := by decide +kernel
theorem subd10_7_17 : subd10_7 [-2, 1] = true := by decide +kernel
theorem subd10_7_18 : subd10_7 [-2, 2] = true := by decide +kernel
theorem subd10_7_19 : subd10_7 [-2, 3] = true := by decide +kernel
theorem subd10_7_20 : subd10_7 [-2, 4] = true := by decide +kernel
theorem subd10_7_21 : subd10_7 [-2, 5] = true := by decide +kernel
theorem subd10_7_22 : subd10_7 [-1, -6] = true := by decide +kernel
theorem subd10_7_23 : subd10_7 [-1, -5] = true := by decide +kernel
theorem subd10_7_24 : subd10_7 [-1, -4] = true := by decide +kernel
theorem subd10_7_25 : subd10_7 [-1, -3] = true := by decide +kernel
theorem subd10_7_26 : subd10_7 [-1, -2] = true := by decide +kernel
theorem subd10_7_27 : subd10_7 [-1, -1] = true := by decide +kernel
theorem subd10_7_28 : subd10_7 [-1, 0] = true := by decide +kernel
theorem subd10_7_29 : subd10_7 [-1, 1] = true := by decide +kernel
theorem subd10_7_30 : subd10_7 [-1, 2] = true := by decide +kernel
theorem subd10_7_31 : subd10_7 [-1, 3] = true := by decide +kernel
theorem sbd10_7_0 : ∀ q ∈ blkd10_7_0, subd10_7 q = true := by
  unfold blkd10_7_0
  exact List.forall_mem_cons.2 ⟨subd10_7_0, List.forall_mem_cons.2 ⟨subd10_7_1, List.forall_mem_cons.2 ⟨subd10_7_2, List.forall_mem_cons.2 ⟨subd10_7_3, List.forall_mem_cons.2 ⟨subd10_7_4, List.forall_mem_cons.2 ⟨subd10_7_5, List.forall_mem_cons.2 ⟨subd10_7_6, List.forall_mem_cons.2 ⟨subd10_7_7, List.forall_mem_cons.2 ⟨subd10_7_8, List.forall_mem_cons.2 ⟨subd10_7_9, List.forall_mem_cons.2 ⟨subd10_7_10, List.forall_mem_cons.2 ⟨subd10_7_11, List.forall_mem_cons.2 ⟨subd10_7_12, List.forall_mem_cons.2 ⟨subd10_7_13, List.forall_mem_cons.2 ⟨subd10_7_14, List.forall_mem_cons.2 ⟨subd10_7_15, List.forall_mem_cons.2 ⟨subd10_7_16, List.forall_mem_cons.2 ⟨subd10_7_17, List.forall_mem_cons.2 ⟨subd10_7_18, List.forall_mem_cons.2 ⟨subd10_7_19, List.forall_mem_cons.2 ⟨subd10_7_20, List.forall_mem_cons.2 ⟨subd10_7_21, List.forall_mem_cons.2 ⟨subd10_7_22, List.forall_mem_cons.2 ⟨subd10_7_23, List.forall_mem_cons.2 ⟨subd10_7_24, List.forall_mem_cons.2 ⟨subd10_7_25, List.forall_mem_cons.2 ⟨subd10_7_26, List.forall_mem_cons.2 ⟨subd10_7_27, List.forall_mem_cons.2 ⟨subd10_7_28, List.forall_mem_cons.2 ⟨subd10_7_29, List.forall_mem_cons.2 ⟨subd10_7_30, List.forall_mem_cons.2 ⟨subd10_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
