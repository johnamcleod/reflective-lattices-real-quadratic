import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_5_64 : subd3_5 [-1, 0, 1] = true := by decide +kernel
theorem subd3_5_65 : subd3_5 [-1, 0, 2] = true := by decide +kernel
theorem subd3_5_66 : subd3_5 [-1, 0, 3] = true := by decide +kernel
theorem subd3_5_67 : subd3_5 [-1, 0, 4] = true := by decide +kernel
theorem subd3_5_68 : subd3_5 [-1, 0, 5] = true := by decide +kernel
theorem subd3_5_69 : subd3_5 [-1, 0, 6] = true := by decide +kernel
theorem subd3_5_70 : subd3_5 [-1, 0, 7] = true := by decide +kernel
theorem subd3_5_71 : subd3_5 [-1, 1, -8] = true := by decide +kernel
theorem subd3_5_72 : subd3_5 [-1, 1, -7] = true := by decide +kernel
theorem subd3_5_73 : subd3_5 [-1, 1, -6] = true := by decide +kernel
theorem subd3_5_74 : subd3_5 [-1, 1, -5] = true := by decide +kernel
theorem subd3_5_75 : subd3_5 [-1, 1, -4] = true := by decide +kernel
theorem subd3_5_76 : subd3_5 [-1, 1, -3] = true := by decide +kernel
theorem subd3_5_77 : subd3_5 [-1, 1, -2] = true := by decide +kernel
theorem subd3_5_78 : subd3_5 [-1, 1, -1] = true := by decide +kernel
theorem subd3_5_79 : subd3_5 [-1, 1, 0] = true := by decide +kernel
theorem subd3_5_80 : subd3_5 [-1, 1, 1] = true := by decide +kernel
theorem subd3_5_81 : subd3_5 [-1, 1, 2] = true := by decide +kernel
theorem subd3_5_82 : subd3_5 [-1, 1, 3] = true := by decide +kernel
theorem subd3_5_83 : subd3_5 [-1, 1, 4] = true := by decide +kernel
theorem subd3_5_84 : subd3_5 [-1, 1, 5] = true := by decide +kernel
theorem subd3_5_85 : subd3_5 [-1, 1, 6] = true := by decide +kernel
theorem subd3_5_86 : subd3_5 [-1, 1, 7] = true := by decide +kernel
theorem subd3_5_87 : subd3_5 [-1, 2, -7] = true := by decide +kernel
theorem subd3_5_88 : subd3_5 [-1, 2, -6] = true := by decide +kernel
theorem subd3_5_89 : subd3_5 [-1, 2, -5] = true := by decide +kernel
theorem subd3_5_90 : subd3_5 [-1, 2, -4] = true := by decide +kernel
theorem subd3_5_91 : subd3_5 [-1, 2, -3] = true := by decide +kernel
theorem subd3_5_92 : subd3_5 [-1, 2, -2] = true := by decide +kernel
theorem subd3_5_93 : subd3_5 [-1, 2, -1] = true := by decide +kernel
theorem subd3_5_94 : subd3_5 [-1, 2, 0] = true := by decide +kernel
theorem subd3_5_95 : subd3_5 [-1, 2, 1] = true := by decide +kernel
theorem sbd3_5_2 : ∀ q ∈ blkd3_5_2, subd3_5 q = true := by
  unfold blkd3_5_2
  exact List.forall_mem_cons.2 ⟨subd3_5_64, List.forall_mem_cons.2 ⟨subd3_5_65, List.forall_mem_cons.2 ⟨subd3_5_66, List.forall_mem_cons.2 ⟨subd3_5_67, List.forall_mem_cons.2 ⟨subd3_5_68, List.forall_mem_cons.2 ⟨subd3_5_69, List.forall_mem_cons.2 ⟨subd3_5_70, List.forall_mem_cons.2 ⟨subd3_5_71, List.forall_mem_cons.2 ⟨subd3_5_72, List.forall_mem_cons.2 ⟨subd3_5_73, List.forall_mem_cons.2 ⟨subd3_5_74, List.forall_mem_cons.2 ⟨subd3_5_75, List.forall_mem_cons.2 ⟨subd3_5_76, List.forall_mem_cons.2 ⟨subd3_5_77, List.forall_mem_cons.2 ⟨subd3_5_78, List.forall_mem_cons.2 ⟨subd3_5_79, List.forall_mem_cons.2 ⟨subd3_5_80, List.forall_mem_cons.2 ⟨subd3_5_81, List.forall_mem_cons.2 ⟨subd3_5_82, List.forall_mem_cons.2 ⟨subd3_5_83, List.forall_mem_cons.2 ⟨subd3_5_84, List.forall_mem_cons.2 ⟨subd3_5_85, List.forall_mem_cons.2 ⟨subd3_5_86, List.forall_mem_cons.2 ⟨subd3_5_87, List.forall_mem_cons.2 ⟨subd3_5_88, List.forall_mem_cons.2 ⟨subd3_5_89, List.forall_mem_cons.2 ⟨subd3_5_90, List.forall_mem_cons.2 ⟨subd3_5_91, List.forall_mem_cons.2 ⟨subd3_5_92, List.forall_mem_cons.2 ⟨subd3_5_93, List.forall_mem_cons.2 ⟨subd3_5_94, List.forall_mem_cons.2 ⟨subd3_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_96 : subd3_5 [-1, 2, 2] = true := by decide +kernel
theorem subd3_5_97 : subd3_5 [-1, 2, 3] = true := by decide +kernel
theorem subd3_5_98 : subd3_5 [-1, 2, 4] = true := by decide +kernel
theorem subd3_5_99 : subd3_5 [-1, 2, 5] = true := by decide +kernel
theorem subd3_5_100 : subd3_5 [-1, 2, 6] = true := by decide +kernel
theorem subd3_5_101 : subd3_5 [-1, 3] = true := by decide +kernel
theorem subd3_5_102 : subd3_5 [0, -4] = true := by decide +kernel
theorem subd3_5_103 : subd3_5 [0, -3] = true := by decide +kernel
theorem subd3_5_104 : subd3_5 [0, -2, -7] = true := by decide +kernel
theorem subd3_5_105 : subd3_5 [0, -2, -6] = true := by decide +kernel
theorem subd3_5_106 : subd3_5 [0, -2, -5] = true := by decide +kernel
theorem subd3_5_107 : subd3_5 [0, -2, -4] = true := by decide +kernel
theorem subd3_5_108 : subd3_5 [0, -2, -3] = true := by decide +kernel
theorem subd3_5_109 : subd3_5 [0, -2, -2] = true := by decide +kernel
theorem subd3_5_110 : subd3_5 [0, -2, -1] = true := by decide +kernel
theorem subd3_5_111 : subd3_5 [0, -2, 0] = true := by decide +kernel
theorem subd3_5_112 : subd3_5 [0, -2, 1] = true := by decide +kernel
theorem subd3_5_113 : subd3_5 [0, -2, 2] = true := by decide +kernel
theorem subd3_5_114 : subd3_5 [0, -2, 3] = true := by decide +kernel
theorem subd3_5_115 : subd3_5 [0, -2, 4] = true := by decide +kernel
theorem subd3_5_116 : subd3_5 [0, -2, 5] = true := by decide +kernel
theorem subd3_5_117 : subd3_5 [0, -2, 6] = true := by decide +kernel
theorem subd3_5_118 : subd3_5 [0, -1, -8] = true := by decide +kernel
theorem subd3_5_119 : subd3_5 [0, -1, -7] = true := by decide +kernel
theorem subd3_5_120 : subd3_5 [0, -1, -6] = true := by decide +kernel
theorem subd3_5_121 : subd3_5 [0, -1, -5] = true := by decide +kernel
theorem subd3_5_122 : subd3_5 [0, -1, -4] = true := by decide +kernel
theorem subd3_5_123 : subd3_5 [0, -1, -3] = true := by decide +kernel
theorem subd3_5_124 : subd3_5 [0, -1, -2] = true := by decide +kernel
theorem subd3_5_125 : subd3_5 [0, -1, -1] = true := by decide +kernel
theorem subd3_5_126 : subd3_5 [0, -1, 0] = true := by decide +kernel
theorem subd3_5_127 : subd3_5 [0, -1, 1] = true := by decide +kernel
theorem sbd3_5_3 : ∀ q ∈ blkd3_5_3, subd3_5 q = true := by
  unfold blkd3_5_3
  exact List.forall_mem_cons.2 ⟨subd3_5_96, List.forall_mem_cons.2 ⟨subd3_5_97, List.forall_mem_cons.2 ⟨subd3_5_98, List.forall_mem_cons.2 ⟨subd3_5_99, List.forall_mem_cons.2 ⟨subd3_5_100, List.forall_mem_cons.2 ⟨subd3_5_101, List.forall_mem_cons.2 ⟨subd3_5_102, List.forall_mem_cons.2 ⟨subd3_5_103, List.forall_mem_cons.2 ⟨subd3_5_104, List.forall_mem_cons.2 ⟨subd3_5_105, List.forall_mem_cons.2 ⟨subd3_5_106, List.forall_mem_cons.2 ⟨subd3_5_107, List.forall_mem_cons.2 ⟨subd3_5_108, List.forall_mem_cons.2 ⟨subd3_5_109, List.forall_mem_cons.2 ⟨subd3_5_110, List.forall_mem_cons.2 ⟨subd3_5_111, List.forall_mem_cons.2 ⟨subd3_5_112, List.forall_mem_cons.2 ⟨subd3_5_113, List.forall_mem_cons.2 ⟨subd3_5_114, List.forall_mem_cons.2 ⟨subd3_5_115, List.forall_mem_cons.2 ⟨subd3_5_116, List.forall_mem_cons.2 ⟨subd3_5_117, List.forall_mem_cons.2 ⟨subd3_5_118, List.forall_mem_cons.2 ⟨subd3_5_119, List.forall_mem_cons.2 ⟨subd3_5_120, List.forall_mem_cons.2 ⟨subd3_5_121, List.forall_mem_cons.2 ⟨subd3_5_122, List.forall_mem_cons.2 ⟨subd3_5_123, List.forall_mem_cons.2 ⟨subd3_5_124, List.forall_mem_cons.2 ⟨subd3_5_125, List.forall_mem_cons.2 ⟨subd3_5_126, List.forall_mem_cons.2 ⟨subd3_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_128 : subd3_5 [0, -1, 2] = true := by decide +kernel
theorem subd3_5_129 : subd3_5 [0, -1, 3] = true := by decide +kernel
theorem subd3_5_130 : subd3_5 [0, -1, 4] = true := by decide +kernel
theorem subd3_5_131 : subd3_5 [0, -1, 5] = true := by decide +kernel
theorem subd3_5_132 : subd3_5 [0, -1, 6] = true := by decide +kernel
theorem subd3_5_133 : subd3_5 [0, -1, 7] = true := by decide +kernel
theorem subd3_5_134 : subd3_5 [0, 0, -8] = true := by decide +kernel
theorem subd3_5_135 : subd3_5 [0, 0, -7] = true := by decide +kernel
theorem subd3_5_136 : subd3_5 [0, 0, -6] = true := by decide +kernel
theorem subd3_5_137 : subd3_5 [0, 0, -5] = true := by decide +kernel
theorem subd3_5_138 : subd3_5 [0, 0, -4] = true := by decide +kernel
theorem subd3_5_139 : subd3_5 [0, 0, -3] = true := by decide +kernel
theorem subd3_5_140 : subd3_5 [0, 0, -2] = true := by decide +kernel
theorem subd3_5_141 : subd3_5 [0, 0, -1] = true := by decide +kernel
theorem subd3_5_142 : subd3_5 [0, 0, 0] = true := by decide +kernel
theorem subd3_5_143 : subd3_5 [0, 0, 1] = true := by decide +kernel
theorem subd3_5_144 : subd3_5 [0, 0, 2] = true := by decide +kernel
theorem subd3_5_145 : subd3_5 [0, 0, 3] = true := by decide +kernel
theorem subd3_5_146 : subd3_5 [0, 0, 4] = true := by decide +kernel
theorem subd3_5_147 : subd3_5 [0, 0, 5] = true := by decide +kernel
theorem subd3_5_148 : subd3_5 [0, 0, 6] = true := by decide +kernel
theorem subd3_5_149 : subd3_5 [0, 0, 7] = true := by decide +kernel
theorem subd3_5_150 : subd3_5 [0, 1, -8] = true := by decide +kernel
theorem subd3_5_151 : subd3_5 [0, 1, -7] = true := by decide +kernel
theorem subd3_5_152 : subd3_5 [0, 1, -6] = true := by decide +kernel
theorem subd3_5_153 : subd3_5 [0, 1, -5] = true := by decide +kernel
theorem subd3_5_154 : subd3_5 [0, 1, -4] = true := by decide +kernel
theorem subd3_5_155 : subd3_5 [0, 1, -3] = true := by decide +kernel
theorem subd3_5_156 : subd3_5 [0, 1, -2] = true := by decide +kernel
theorem subd3_5_157 : subd3_5 [0, 1, -1] = true := by decide +kernel
theorem subd3_5_158 : subd3_5 [0, 1, 0] = true := by decide +kernel
theorem subd3_5_159 : subd3_5 [0, 1, 1] = true := by decide +kernel
theorem sbd3_5_4 : ∀ q ∈ blkd3_5_4, subd3_5 q = true := by
  unfold blkd3_5_4
  exact List.forall_mem_cons.2 ⟨subd3_5_128, List.forall_mem_cons.2 ⟨subd3_5_129, List.forall_mem_cons.2 ⟨subd3_5_130, List.forall_mem_cons.2 ⟨subd3_5_131, List.forall_mem_cons.2 ⟨subd3_5_132, List.forall_mem_cons.2 ⟨subd3_5_133, List.forall_mem_cons.2 ⟨subd3_5_134, List.forall_mem_cons.2 ⟨subd3_5_135, List.forall_mem_cons.2 ⟨subd3_5_136, List.forall_mem_cons.2 ⟨subd3_5_137, List.forall_mem_cons.2 ⟨subd3_5_138, List.forall_mem_cons.2 ⟨subd3_5_139, List.forall_mem_cons.2 ⟨subd3_5_140, List.forall_mem_cons.2 ⟨subd3_5_141, List.forall_mem_cons.2 ⟨subd3_5_142, List.forall_mem_cons.2 ⟨subd3_5_143, List.forall_mem_cons.2 ⟨subd3_5_144, List.forall_mem_cons.2 ⟨subd3_5_145, List.forall_mem_cons.2 ⟨subd3_5_146, List.forall_mem_cons.2 ⟨subd3_5_147, List.forall_mem_cons.2 ⟨subd3_5_148, List.forall_mem_cons.2 ⟨subd3_5_149, List.forall_mem_cons.2 ⟨subd3_5_150, List.forall_mem_cons.2 ⟨subd3_5_151, List.forall_mem_cons.2 ⟨subd3_5_152, List.forall_mem_cons.2 ⟨subd3_5_153, List.forall_mem_cons.2 ⟨subd3_5_154, List.forall_mem_cons.2 ⟨subd3_5_155, List.forall_mem_cons.2 ⟨subd3_5_156, List.forall_mem_cons.2 ⟨subd3_5_157, List.forall_mem_cons.2 ⟨subd3_5_158, List.forall_mem_cons.2 ⟨subd3_5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_160 : subd3_5 [0, 1, 2] = true := by decide +kernel
theorem subd3_5_161 : subd3_5 [0, 1, 3] = true := by decide +kernel
theorem subd3_5_162 : subd3_5 [0, 1, 4] = true := by decide +kernel
theorem subd3_5_163 : subd3_5 [0, 1, 5] = true := by decide +kernel
theorem subd3_5_164 : subd3_5 [0, 1, 6] = true := by decide +kernel
theorem subd3_5_165 : subd3_5 [0, 1, 7] = true := by decide +kernel
theorem subd3_5_166 : subd3_5 [0, 2, -7] = true := by decide +kernel
theorem subd3_5_167 : subd3_5 [0, 2, -6] = true := by decide +kernel
theorem subd3_5_168 : subd3_5 [0, 2, -5] = true := by decide +kernel
theorem subd3_5_169 : subd3_5 [0, 2, -4] = true := by decide +kernel
theorem subd3_5_170 : subd3_5 [0, 2, -3] = true := by decide +kernel
theorem subd3_5_171 : subd3_5 [0, 2, -2] = true := by decide +kernel
theorem subd3_5_172 : subd3_5 [0, 2, -1] = true := by decide +kernel
theorem subd3_5_173 : subd3_5 [0, 2, 0] = true := by decide +kernel
theorem subd3_5_174 : subd3_5 [0, 2, 1] = true := by decide +kernel
theorem subd3_5_175 : subd3_5 [0, 2, 2] = true := by decide +kernel
theorem subd3_5_176 : subd3_5 [0, 2, 3] = true := by decide +kernel
theorem subd3_5_177 : subd3_5 [0, 2, 4] = true := by decide +kernel
theorem subd3_5_178 : subd3_5 [0, 2, 5] = true := by decide +kernel
theorem subd3_5_179 : subd3_5 [0, 2, 6] = true := by decide +kernel
theorem subd3_5_180 : subd3_5 [0, 3] = true := by decide +kernel
theorem subd3_5_181 : subd3_5 [1, -4] = true := by decide +kernel
theorem subd3_5_182 : subd3_5 [1, -3] = true := by decide +kernel
theorem subd3_5_183 : subd3_5 [1, -2, -7] = true := by decide +kernel
theorem subd3_5_184 : subd3_5 [1, -2, -6] = true := by decide +kernel
theorem subd3_5_185 : subd3_5 [1, -2, -5] = true := by decide +kernel
theorem subd3_5_186 : subd3_5 [1, -2, -4] = true := by decide +kernel
theorem subd3_5_187 : subd3_5 [1, -2, -3] = true := by decide +kernel
theorem subd3_5_188 : subd3_5 [1, -2, -2] = true := by decide +kernel
theorem subd3_5_189 : subd3_5 [1, -2, -1] = true := by decide +kernel
theorem subd3_5_190 : subd3_5 [1, -2, 0] = true := by decide +kernel
theorem subd3_5_191 : subd3_5 [1, -2, 1] = true := by decide +kernel
theorem sbd3_5_5 : ∀ q ∈ blkd3_5_5, subd3_5 q = true := by
  unfold blkd3_5_5
  exact List.forall_mem_cons.2 ⟨subd3_5_160, List.forall_mem_cons.2 ⟨subd3_5_161, List.forall_mem_cons.2 ⟨subd3_5_162, List.forall_mem_cons.2 ⟨subd3_5_163, List.forall_mem_cons.2 ⟨subd3_5_164, List.forall_mem_cons.2 ⟨subd3_5_165, List.forall_mem_cons.2 ⟨subd3_5_166, List.forall_mem_cons.2 ⟨subd3_5_167, List.forall_mem_cons.2 ⟨subd3_5_168, List.forall_mem_cons.2 ⟨subd3_5_169, List.forall_mem_cons.2 ⟨subd3_5_170, List.forall_mem_cons.2 ⟨subd3_5_171, List.forall_mem_cons.2 ⟨subd3_5_172, List.forall_mem_cons.2 ⟨subd3_5_173, List.forall_mem_cons.2 ⟨subd3_5_174, List.forall_mem_cons.2 ⟨subd3_5_175, List.forall_mem_cons.2 ⟨subd3_5_176, List.forall_mem_cons.2 ⟨subd3_5_177, List.forall_mem_cons.2 ⟨subd3_5_178, List.forall_mem_cons.2 ⟨subd3_5_179, List.forall_mem_cons.2 ⟨subd3_5_180, List.forall_mem_cons.2 ⟨subd3_5_181, List.forall_mem_cons.2 ⟨subd3_5_182, List.forall_mem_cons.2 ⟨subd3_5_183, List.forall_mem_cons.2 ⟨subd3_5_184, List.forall_mem_cons.2 ⟨subd3_5_185, List.forall_mem_cons.2 ⟨subd3_5_186, List.forall_mem_cons.2 ⟨subd3_5_187, List.forall_mem_cons.2 ⟨subd3_5_188, List.forall_mem_cons.2 ⟨subd3_5_189, List.forall_mem_cons.2 ⟨subd3_5_190, List.forall_mem_cons.2 ⟨subd3_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_192 : subd3_5 [1, -2, 2] = true := by decide +kernel
theorem subd3_5_193 : subd3_5 [1, -2, 3] = true := by decide +kernel
theorem subd3_5_194 : subd3_5 [1, -2, 4] = true := by decide +kernel
theorem subd3_5_195 : subd3_5 [1, -2, 5] = true := by decide +kernel
theorem subd3_5_196 : subd3_5 [1, -2, 6] = true := by decide +kernel
theorem subd3_5_197 : subd3_5 [1, -1, -8] = true := by decide +kernel
theorem subd3_5_198 : subd3_5 [1, -1, -7] = true := by decide +kernel
theorem subd3_5_199 : subd3_5 [1, -1, -6] = true := by decide +kernel
theorem subd3_5_200 : subd3_5 [1, -1, -5] = true := by decide +kernel
theorem subd3_5_201 : subd3_5 [1, -1, -4] = true := by decide +kernel
theorem subd3_5_202 : subd3_5 [1, -1, -3] = true := by decide +kernel
theorem subd3_5_203 : subd3_5 [1, -1, -2] = true := by decide +kernel
theorem subd3_5_204 : subd3_5 [1, -1, -1] = true := by decide +kernel
theorem subd3_5_205 : subd3_5 [1, -1, 0] = true := by decide +kernel
theorem subd3_5_206 : subd3_5 [1, -1, 1] = true := by decide +kernel
theorem subd3_5_207 : subd3_5 [1, -1, 2] = true := by decide +kernel
theorem subd3_5_208 : subd3_5 [1, -1, 3] = true := by decide +kernel
theorem subd3_5_209 : subd3_5 [1, -1, 4] = true := by decide +kernel
theorem subd3_5_210 : subd3_5 [1, -1, 5] = true := by decide +kernel
theorem subd3_5_211 : subd3_5 [1, -1, 6] = true := by decide +kernel
theorem subd3_5_212 : subd3_5 [1, -1, 7] = true := by decide +kernel
theorem subd3_5_213 : subd3_5 [1, 0, -8] = true := by decide +kernel
theorem subd3_5_214 : subd3_5 [1, 0, -7] = true := by decide +kernel
theorem subd3_5_215 : subd3_5 [1, 0, -6] = true := by decide +kernel
theorem subd3_5_216 : subd3_5 [1, 0, -5] = true := by decide +kernel
theorem subd3_5_217 : subd3_5 [1, 0, -4] = true := by decide +kernel
theorem subd3_5_218 : subd3_5 [1, 0, -3] = true := by decide +kernel
theorem subd3_5_219 : subd3_5 [1, 0, -2] = true := by decide +kernel
theorem subd3_5_220 : subd3_5 [1, 0, -1] = true := by decide +kernel
theorem subd3_5_221 : subd3_5 [1, 0, 0] = true := by decide +kernel
theorem subd3_5_222 : subd3_5 [1, 0, 1] = true := by decide +kernel
theorem subd3_5_223 : subd3_5 [1, 0, 2] = true := by decide +kernel
theorem sbd3_5_6 : ∀ q ∈ blkd3_5_6, subd3_5 q = true := by
  unfold blkd3_5_6
  exact List.forall_mem_cons.2 ⟨subd3_5_192, List.forall_mem_cons.2 ⟨subd3_5_193, List.forall_mem_cons.2 ⟨subd3_5_194, List.forall_mem_cons.2 ⟨subd3_5_195, List.forall_mem_cons.2 ⟨subd3_5_196, List.forall_mem_cons.2 ⟨subd3_5_197, List.forall_mem_cons.2 ⟨subd3_5_198, List.forall_mem_cons.2 ⟨subd3_5_199, List.forall_mem_cons.2 ⟨subd3_5_200, List.forall_mem_cons.2 ⟨subd3_5_201, List.forall_mem_cons.2 ⟨subd3_5_202, List.forall_mem_cons.2 ⟨subd3_5_203, List.forall_mem_cons.2 ⟨subd3_5_204, List.forall_mem_cons.2 ⟨subd3_5_205, List.forall_mem_cons.2 ⟨subd3_5_206, List.forall_mem_cons.2 ⟨subd3_5_207, List.forall_mem_cons.2 ⟨subd3_5_208, List.forall_mem_cons.2 ⟨subd3_5_209, List.forall_mem_cons.2 ⟨subd3_5_210, List.forall_mem_cons.2 ⟨subd3_5_211, List.forall_mem_cons.2 ⟨subd3_5_212, List.forall_mem_cons.2 ⟨subd3_5_213, List.forall_mem_cons.2 ⟨subd3_5_214, List.forall_mem_cons.2 ⟨subd3_5_215, List.forall_mem_cons.2 ⟨subd3_5_216, List.forall_mem_cons.2 ⟨subd3_5_217, List.forall_mem_cons.2 ⟨subd3_5_218, List.forall_mem_cons.2 ⟨subd3_5_219, List.forall_mem_cons.2 ⟨subd3_5_220, List.forall_mem_cons.2 ⟨subd3_5_221, List.forall_mem_cons.2 ⟨subd3_5_222, List.forall_mem_cons.2 ⟨subd3_5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_224 : subd3_5 [1, 0, 3] = true := by decide +kernel
theorem subd3_5_225 : subd3_5 [1, 0, 4] = true := by decide +kernel
theorem subd3_5_226 : subd3_5 [1, 0, 5] = true := by decide +kernel
theorem subd3_5_227 : subd3_5 [1, 0, 6] = true := by decide +kernel
theorem subd3_5_228 : subd3_5 [1, 0, 7] = true := by decide +kernel
theorem subd3_5_229 : subd3_5 [1, 1, -8] = true := by decide +kernel
theorem subd3_5_230 : subd3_5 [1, 1, -7] = true := by decide +kernel
theorem subd3_5_231 : subd3_5 [1, 1, -6] = true := by decide +kernel
theorem subd3_5_232 : subd3_5 [1, 1, -5] = true := by decide +kernel
theorem subd3_5_233 : subd3_5 [1, 1, -4] = true := by decide +kernel
theorem subd3_5_234 : subd3_5 [1, 1, -3] = true := by decide +kernel
theorem subd3_5_235 : subd3_5 [1, 1, -2] = true := by decide +kernel
theorem subd3_5_236 : subd3_5 [1, 1, -1] = true := by decide +kernel
theorem subd3_5_237 : subd3_5 [1, 1, 0] = true := by decide +kernel
theorem subd3_5_238 : subd3_5 [1, 1, 1] = true := by decide +kernel
theorem subd3_5_239 : subd3_5 [1, 1, 2] = true := by decide +kernel
theorem subd3_5_240 : subd3_5 [1, 1, 3] = true := by decide +kernel
theorem subd3_5_241 : subd3_5 [1, 1, 4] = true := by decide +kernel
theorem subd3_5_242 : subd3_5 [1, 1, 5] = true := by decide +kernel
theorem subd3_5_243 : subd3_5 [1, 1, 6] = true := by decide +kernel
theorem subd3_5_244 : subd3_5 [1, 2] = true := by decide +kernel
theorem subd3_5_245 : subd3_5 [1, 3] = true := by decide +kernel
theorem subd3_5_246 : subd3_5 [2, -4] = true := by decide +kernel
theorem subd3_5_247 : subd3_5 [2, -3] = true := by decide +kernel
theorem subd3_5_248 : subd3_5 [2, -2] = true := by decide +kernel
theorem subd3_5_249 : subd3_5 [2, -1, -7] = true := by decide +kernel
theorem subd3_5_250 : subd3_5 [2, -1, -6] = true := by decide +kernel
theorem subd3_5_251 : subd3_5 [2, -1, -5] = true := by decide +kernel
theorem subd3_5_252 : subd3_5 [2, -1, -4] = true := by decide +kernel
theorem subd3_5_253 : subd3_5 [2, -1, -3] = true := by decide +kernel
theorem subd3_5_254 : subd3_5 [2, -1, -2] = true := by decide +kernel
theorem subd3_5_255 : subd3_5 [2, -1, -1] = true := by decide +kernel
theorem sbd3_5_7 : ∀ q ∈ blkd3_5_7, subd3_5 q = true := by
  unfold blkd3_5_7
  exact List.forall_mem_cons.2 ⟨subd3_5_224, List.forall_mem_cons.2 ⟨subd3_5_225, List.forall_mem_cons.2 ⟨subd3_5_226, List.forall_mem_cons.2 ⟨subd3_5_227, List.forall_mem_cons.2 ⟨subd3_5_228, List.forall_mem_cons.2 ⟨subd3_5_229, List.forall_mem_cons.2 ⟨subd3_5_230, List.forall_mem_cons.2 ⟨subd3_5_231, List.forall_mem_cons.2 ⟨subd3_5_232, List.forall_mem_cons.2 ⟨subd3_5_233, List.forall_mem_cons.2 ⟨subd3_5_234, List.forall_mem_cons.2 ⟨subd3_5_235, List.forall_mem_cons.2 ⟨subd3_5_236, List.forall_mem_cons.2 ⟨subd3_5_237, List.forall_mem_cons.2 ⟨subd3_5_238, List.forall_mem_cons.2 ⟨subd3_5_239, List.forall_mem_cons.2 ⟨subd3_5_240, List.forall_mem_cons.2 ⟨subd3_5_241, List.forall_mem_cons.2 ⟨subd3_5_242, List.forall_mem_cons.2 ⟨subd3_5_243, List.forall_mem_cons.2 ⟨subd3_5_244, List.forall_mem_cons.2 ⟨subd3_5_245, List.forall_mem_cons.2 ⟨subd3_5_246, List.forall_mem_cons.2 ⟨subd3_5_247, List.forall_mem_cons.2 ⟨subd3_5_248, List.forall_mem_cons.2 ⟨subd3_5_249, List.forall_mem_cons.2 ⟨subd3_5_250, List.forall_mem_cons.2 ⟨subd3_5_251, List.forall_mem_cons.2 ⟨subd3_5_252, List.forall_mem_cons.2 ⟨subd3_5_253, List.forall_mem_cons.2 ⟨subd3_5_254, List.forall_mem_cons.2 ⟨subd3_5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_256 : subd3_5 [2, -1, 0] = true := by decide +kernel
theorem subd3_5_257 : subd3_5 [2, -1, 1] = true := by decide +kernel
theorem subd3_5_258 : subd3_5 [2, -1, 2] = true := by decide +kernel
theorem subd3_5_259 : subd3_5 [2, -1, 3] = true := by decide +kernel
theorem subd3_5_260 : subd3_5 [2, -1, 4] = true := by decide +kernel
theorem subd3_5_261 : subd3_5 [2, -1, 5] = true := by decide +kernel
theorem subd3_5_262 : subd3_5 [2, 0, -7] = true := by decide +kernel
theorem subd3_5_263 : subd3_5 [2, 0, -6] = true := by decide +kernel
theorem subd3_5_264 : subd3_5 [2, 0, -5] = true := by decide +kernel
theorem subd3_5_265 : subd3_5 [2, 0, -4] = true := by decide +kernel
theorem subd3_5_266 : subd3_5 [2, 0, -3] = true := by decide +kernel
theorem subd3_5_267 : subd3_5 [2, 0, -2] = true := by decide +kernel
theorem subd3_5_268 : subd3_5 [2, 0, -1] = true := by decide +kernel
theorem subd3_5_269 : subd3_5 [2, 0, 0] = true := by decide +kernel
theorem subd3_5_270 : subd3_5 [2, 0, 1] = true := by decide +kernel
theorem subd3_5_271 : subd3_5 [2, 0, 2] = true := by decide +kernel
theorem subd3_5_272 : subd3_5 [2, 0, 3] = true := by decide +kernel
theorem subd3_5_273 : subd3_5 [2, 0, 4] = true := by decide +kernel
theorem subd3_5_274 : subd3_5 [2, 0, 5] = true := by decide +kernel
theorem subd3_5_275 : subd3_5 [2, 0, 6] = true := by decide +kernel
theorem subd3_5_276 : subd3_5 [2, 1] = true := by decide +kernel
theorem subd3_5_277 : subd3_5 [2, 2] = true := by decide +kernel
theorem subd3_5_278 : subd3_5 [3, -3] = true := by decide +kernel
theorem subd3_5_279 : subd3_5 [3, -2] = true := by decide +kernel
theorem subd3_5_280 : subd3_5 [3, -1] = true := by decide +kernel
theorem subd3_5_281 : subd3_5 [3, 0] = true := by decide +kernel
theorem subd3_5_282 : subd3_5 [3, 1] = true := by decide +kernel
theorem sbd3_5_8 : ∀ q ∈ blkd3_5_8, subd3_5 q = true := by
  unfold blkd3_5_8
  exact List.forall_mem_cons.2 ⟨subd3_5_256, List.forall_mem_cons.2 ⟨subd3_5_257, List.forall_mem_cons.2 ⟨subd3_5_258, List.forall_mem_cons.2 ⟨subd3_5_259, List.forall_mem_cons.2 ⟨subd3_5_260, List.forall_mem_cons.2 ⟨subd3_5_261, List.forall_mem_cons.2 ⟨subd3_5_262, List.forall_mem_cons.2 ⟨subd3_5_263, List.forall_mem_cons.2 ⟨subd3_5_264, List.forall_mem_cons.2 ⟨subd3_5_265, List.forall_mem_cons.2 ⟨subd3_5_266, List.forall_mem_cons.2 ⟨subd3_5_267, List.forall_mem_cons.2 ⟨subd3_5_268, List.forall_mem_cons.2 ⟨subd3_5_269, List.forall_mem_cons.2 ⟨subd3_5_270, List.forall_mem_cons.2 ⟨subd3_5_271, List.forall_mem_cons.2 ⟨subd3_5_272, List.forall_mem_cons.2 ⟨subd3_5_273, List.forall_mem_cons.2 ⟨subd3_5_274, List.forall_mem_cons.2 ⟨subd3_5_275, List.forall_mem_cons.2 ⟨subd3_5_276, List.forall_mem_cons.2 ⟨subd3_5_277, List.forall_mem_cons.2 ⟨subd3_5_278, List.forall_mem_cons.2 ⟨subd3_5_279, List.forall_mem_cons.2 ⟨subd3_5_280, List.forall_mem_cons.2 ⟨subd3_5_281, List.forall_mem_cons.2 ⟨subd3_5_282, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_6 : ldCheck G d3_6.U d3_6.ms ldd3_6 = true := by decide +kernel
theorem pre_okd3_6 : subPre G cell3 d3_6 = true := by decide +kernel
theorem subd3_6_0 : subd3_6 [-3, -2] = true := by decide +kernel
theorem subd3_6_1 : subd3_6 [-3, -1] = true := by decide +kernel
theorem subd3_6_2 : subd3_6 [-3, 0] = true := by decide +kernel
theorem subd3_6_3 : subd3_6 [-3, 1] = true := by decide +kernel
theorem subd3_6_4 : subd3_6 [-3, 2] = true := by decide +kernel
theorem subd3_6_5 : subd3_6 [-2, -3] = true := by decide +kernel
theorem subd3_6_6 : subd3_6 [-2, -2] = true := by decide +kernel
theorem subd3_6_7 : subd3_6 [-2, -1, -8] = true := by decide +kernel
theorem subd3_6_8 : subd3_6 [-2, -1, -7] = true := by decide +kernel
theorem subd3_6_9 : subd3_6 [-2, -1, -6] = true := by decide +kernel
theorem subd3_6_10 : subd3_6 [-2, -1, -5] = true := by decide +kernel
theorem subd3_6_11 : subd3_6 [-2, -1, -4] = true := by decide +kernel
theorem subd3_6_12 : subd3_6 [-2, -1, -3] = true := by decide +kernel
theorem subd3_6_13 : subd3_6 [-2, -1, -2] = true := by decide +kernel
theorem subd3_6_14 : subd3_6 [-2, -1, -1] = true := by decide +kernel
theorem subd3_6_15 : subd3_6 [-2, -1, 0] = true := by decide +kernel
theorem subd3_6_16 : subd3_6 [-2, -1, 1] = true := by decide +kernel
theorem subd3_6_17 : subd3_6 [-2, -1, 2] = true := by decide +kernel
theorem subd3_6_18 : subd3_6 [-2, -1, 3] = true := by decide +kernel
theorem subd3_6_19 : subd3_6 [-2, -1, 4] = true := by decide +kernel
theorem subd3_6_20 : subd3_6 [-2, -1, 5] = true := by decide +kernel
theorem subd3_6_21 : subd3_6 [-2, -1, 6] = true := by decide +kernel
theorem subd3_6_22 : subd3_6 [-2, 0, -9] = true := by decide +kernel
theorem subd3_6_23 : subd3_6 [-2, 0, -8] = true := by decide +kernel
theorem subd3_6_24 : subd3_6 [-2, 0, -7] = true := by decide +kernel
theorem subd3_6_25 : subd3_6 [-2, 0, -6] = true := by decide +kernel
theorem subd3_6_26 : subd3_6 [-2, 0, -5] = true := by decide +kernel
theorem subd3_6_27 : subd3_6 [-2, 0, -4] = true := by decide +kernel
theorem subd3_6_28 : subd3_6 [-2, 0, -3] = true := by decide +kernel
theorem subd3_6_29 : subd3_6 [-2, 0, -2] = true := by decide +kernel
theorem subd3_6_30 : subd3_6 [-2, 0, -1] = true := by decide +kernel
theorem subd3_6_31 : subd3_6 [-2, 0, 0] = true := by decide +kernel
theorem sbd3_6_0 : ∀ q ∈ blkd3_6_0, subd3_6 q = true := by
  unfold blkd3_6_0
  exact List.forall_mem_cons.2 ⟨subd3_6_0, List.forall_mem_cons.2 ⟨subd3_6_1, List.forall_mem_cons.2 ⟨subd3_6_2, List.forall_mem_cons.2 ⟨subd3_6_3, List.forall_mem_cons.2 ⟨subd3_6_4, List.forall_mem_cons.2 ⟨subd3_6_5, List.forall_mem_cons.2 ⟨subd3_6_6, List.forall_mem_cons.2 ⟨subd3_6_7, List.forall_mem_cons.2 ⟨subd3_6_8, List.forall_mem_cons.2 ⟨subd3_6_9, List.forall_mem_cons.2 ⟨subd3_6_10, List.forall_mem_cons.2 ⟨subd3_6_11, List.forall_mem_cons.2 ⟨subd3_6_12, List.forall_mem_cons.2 ⟨subd3_6_13, List.forall_mem_cons.2 ⟨subd3_6_14, List.forall_mem_cons.2 ⟨subd3_6_15, List.forall_mem_cons.2 ⟨subd3_6_16, List.forall_mem_cons.2 ⟨subd3_6_17, List.forall_mem_cons.2 ⟨subd3_6_18, List.forall_mem_cons.2 ⟨subd3_6_19, List.forall_mem_cons.2 ⟨subd3_6_20, List.forall_mem_cons.2 ⟨subd3_6_21, List.forall_mem_cons.2 ⟨subd3_6_22, List.forall_mem_cons.2 ⟨subd3_6_23, List.forall_mem_cons.2 ⟨subd3_6_24, List.forall_mem_cons.2 ⟨subd3_6_25, List.forall_mem_cons.2 ⟨subd3_6_26, List.forall_mem_cons.2 ⟨subd3_6_27, List.forall_mem_cons.2 ⟨subd3_6_28, List.forall_mem_cons.2 ⟨subd3_6_29, List.forall_mem_cons.2 ⟨subd3_6_30, List.forall_mem_cons.2 ⟨subd3_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_32 : subd3_6 [-2, 0, 1] = true := by decide +kernel
theorem subd3_6_33 : subd3_6 [-2, 0, 2] = true := by decide +kernel
theorem subd3_6_34 : subd3_6 [-2, 0, 3] = true := by decide +kernel
theorem subd3_6_35 : subd3_6 [-2, 0, 4] = true := by decide +kernel
theorem subd3_6_36 : subd3_6 [-2, 0, 5] = true := by decide +kernel
theorem subd3_6_37 : subd3_6 [-2, 0, 6] = true := by decide +kernel
theorem subd3_6_38 : subd3_6 [-2, 0, 7] = true := by decide +kernel
theorem subd3_6_39 : subd3_6 [-2, 1, -8] = true := by decide +kernel
theorem subd3_6_40 : subd3_6 [-2, 1, -7] = true := by decide +kernel
theorem subd3_6_41 : subd3_6 [-2, 1, -6] = true := by decide +kernel
theorem subd3_6_42 : subd3_6 [-2, 1, -5] = true := by decide +kernel
theorem subd3_6_43 : subd3_6 [-2, 1, -4] = true := by decide +kernel
theorem subd3_6_44 : subd3_6 [-2, 1, -3] = true := by decide +kernel
theorem subd3_6_45 : subd3_6 [-2, 1, -2] = true := by decide +kernel
theorem subd3_6_46 : subd3_6 [-2, 1, -1] = true := by decide +kernel
theorem subd3_6_47 : subd3_6 [-2, 1, 0] = true := by decide +kernel
theorem subd3_6_48 : subd3_6 [-2, 1, 1] = true := by decide +kernel
theorem subd3_6_49 : subd3_6 [-2, 1, 2] = true := by decide +kernel
theorem subd3_6_50 : subd3_6 [-2, 1, 3] = true := by decide +kernel
theorem subd3_6_51 : subd3_6 [-2, 1, 4] = true := by decide +kernel
theorem subd3_6_52 : subd3_6 [-2, 1, 5] = true := by decide +kernel
theorem subd3_6_53 : subd3_6 [-2, 1, 6] = true := by decide +kernel
theorem subd3_6_54 : subd3_6 [-2, 1, 7] = true := by decide +kernel
theorem subd3_6_55 : subd3_6 [-2, 2] = true := by decide +kernel
theorem subd3_6_56 : subd3_6 [-2, 3] = true := by decide +kernel
theorem subd3_6_57 : subd3_6 [-1, -4] = true := by decide +kernel
theorem subd3_6_58 : subd3_6 [-1, -3] = true := by decide +kernel
theorem subd3_6_59 : subd3_6 [-1, -2, -9] = true := by decide +kernel
theorem subd3_6_60 : subd3_6 [-1, -2, -8] = true := by decide +kernel
theorem subd3_6_61 : subd3_6 [-1, -2, -7] = true := by decide +kernel
theorem subd3_6_62 : subd3_6 [-1, -2, -6] = true := by decide +kernel
theorem subd3_6_63 : subd3_6 [-1, -2, -5] = true := by decide +kernel
theorem sbd3_6_1 : ∀ q ∈ blkd3_6_1, subd3_6 q = true := by
  unfold blkd3_6_1
  exact List.forall_mem_cons.2 ⟨subd3_6_32, List.forall_mem_cons.2 ⟨subd3_6_33, List.forall_mem_cons.2 ⟨subd3_6_34, List.forall_mem_cons.2 ⟨subd3_6_35, List.forall_mem_cons.2 ⟨subd3_6_36, List.forall_mem_cons.2 ⟨subd3_6_37, List.forall_mem_cons.2 ⟨subd3_6_38, List.forall_mem_cons.2 ⟨subd3_6_39, List.forall_mem_cons.2 ⟨subd3_6_40, List.forall_mem_cons.2 ⟨subd3_6_41, List.forall_mem_cons.2 ⟨subd3_6_42, List.forall_mem_cons.2 ⟨subd3_6_43, List.forall_mem_cons.2 ⟨subd3_6_44, List.forall_mem_cons.2 ⟨subd3_6_45, List.forall_mem_cons.2 ⟨subd3_6_46, List.forall_mem_cons.2 ⟨subd3_6_47, List.forall_mem_cons.2 ⟨subd3_6_48, List.forall_mem_cons.2 ⟨subd3_6_49, List.forall_mem_cons.2 ⟨subd3_6_50, List.forall_mem_cons.2 ⟨subd3_6_51, List.forall_mem_cons.2 ⟨subd3_6_52, List.forall_mem_cons.2 ⟨subd3_6_53, List.forall_mem_cons.2 ⟨subd3_6_54, List.forall_mem_cons.2 ⟨subd3_6_55, List.forall_mem_cons.2 ⟨subd3_6_56, List.forall_mem_cons.2 ⟨subd3_6_57, List.forall_mem_cons.2 ⟨subd3_6_58, List.forall_mem_cons.2 ⟨subd3_6_59, List.forall_mem_cons.2 ⟨subd3_6_60, List.forall_mem_cons.2 ⟨subd3_6_61, List.forall_mem_cons.2 ⟨subd3_6_62, List.forall_mem_cons.2 ⟨subd3_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_64 : subd3_6 [-1, -2, -4] = true := by decide +kernel
theorem subd3_6_65 : subd3_6 [-1, -2, -3] = true := by decide +kernel
theorem subd3_6_66 : subd3_6 [-1, -2, -2] = true := by decide +kernel
theorem subd3_6_67 : subd3_6 [-1, -2, -1] = true := by decide +kernel
theorem subd3_6_68 : subd3_6 [-1, -2, 0] = true := by decide +kernel
theorem subd3_6_69 : subd3_6 [-1, -2, 1] = true := by decide +kernel
theorem subd3_6_70 : subd3_6 [-1, -2, 2] = true := by decide +kernel
theorem subd3_6_71 : subd3_6 [-1, -2, 3] = true := by decide +kernel
theorem subd3_6_72 : subd3_6 [-1, -2, 4] = true := by decide +kernel
theorem subd3_6_73 : subd3_6 [-1, -2, 5] = true := by decide +kernel
theorem subd3_6_74 : subd3_6 [-1, -2, 6] = true := by decide +kernel
theorem subd3_6_75 : subd3_6 [-1, -1, -10] = true := by decide +kernel
theorem subd3_6_76 : subd3_6 [-1, -1, -9] = true := by decide +kernel
theorem subd3_6_77 : subd3_6 [-1, -1, -8] = true := by decide +kernel
theorem subd3_6_78 : subd3_6 [-1, -1, -7] = true := by decide +kernel
theorem subd3_6_79 : subd3_6 [-1, -1, -6] = true := by decide +kernel
theorem subd3_6_80 : subd3_6 [-1, -1, -5] = true := by decide +kernel
theorem subd3_6_81 : subd3_6 [-1, -1, -4] = true := by decide +kernel
theorem subd3_6_82 : subd3_6 [-1, -1, -3] = true := by decide +kernel
theorem subd3_6_83 : subd3_6 [-1, -1, -2] = true := by decide +kernel
theorem subd3_6_84 : subd3_6 [-1, -1, -1] = true := by decide +kernel
theorem subd3_6_85 : subd3_6 [-1, -1, 0] = true := by decide +kernel
theorem subd3_6_86 : subd3_6 [-1, -1, 1] = true := by decide +kernel
theorem subd3_6_87 : subd3_6 [-1, -1, 2] = true := by decide +kernel
theorem subd3_6_88 : subd3_6 [-1, -1, 3] = true := by decide +kernel
theorem subd3_6_89 : subd3_6 [-1, -1, 4] = true := by decide +kernel
theorem subd3_6_90 : subd3_6 [-1, -1, 5] = true := by decide +kernel
theorem subd3_6_91 : subd3_6 [-1, -1, 6] = true := by decide +kernel
theorem subd3_6_92 : subd3_6 [-1, -1, 7] = true := by decide +kernel
theorem subd3_6_93 : subd3_6 [-1, -1, 8] = true := by decide +kernel
theorem subd3_6_94 : subd3_6 [-1, 0, -10] = true := by decide +kernel
theorem subd3_6_95 : subd3_6 [-1, 0, -9] = true := by decide +kernel
theorem sbd3_6_2 : ∀ q ∈ blkd3_6_2, subd3_6 q = true := by
  unfold blkd3_6_2
  exact List.forall_mem_cons.2 ⟨subd3_6_64, List.forall_mem_cons.2 ⟨subd3_6_65, List.forall_mem_cons.2 ⟨subd3_6_66, List.forall_mem_cons.2 ⟨subd3_6_67, List.forall_mem_cons.2 ⟨subd3_6_68, List.forall_mem_cons.2 ⟨subd3_6_69, List.forall_mem_cons.2 ⟨subd3_6_70, List.forall_mem_cons.2 ⟨subd3_6_71, List.forall_mem_cons.2 ⟨subd3_6_72, List.forall_mem_cons.2 ⟨subd3_6_73, List.forall_mem_cons.2 ⟨subd3_6_74, List.forall_mem_cons.2 ⟨subd3_6_75, List.forall_mem_cons.2 ⟨subd3_6_76, List.forall_mem_cons.2 ⟨subd3_6_77, List.forall_mem_cons.2 ⟨subd3_6_78, List.forall_mem_cons.2 ⟨subd3_6_79, List.forall_mem_cons.2 ⟨subd3_6_80, List.forall_mem_cons.2 ⟨subd3_6_81, List.forall_mem_cons.2 ⟨subd3_6_82, List.forall_mem_cons.2 ⟨subd3_6_83, List.forall_mem_cons.2 ⟨subd3_6_84, List.forall_mem_cons.2 ⟨subd3_6_85, List.forall_mem_cons.2 ⟨subd3_6_86, List.forall_mem_cons.2 ⟨subd3_6_87, List.forall_mem_cons.2 ⟨subd3_6_88, List.forall_mem_cons.2 ⟨subd3_6_89, List.forall_mem_cons.2 ⟨subd3_6_90, List.forall_mem_cons.2 ⟨subd3_6_91, List.forall_mem_cons.2 ⟨subd3_6_92, List.forall_mem_cons.2 ⟨subd3_6_93, List.forall_mem_cons.2 ⟨subd3_6_94, List.forall_mem_cons.2 ⟨subd3_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_96 : subd3_6 [-1, 0, -8] = true := by decide +kernel
theorem subd3_6_97 : subd3_6 [-1, 0, -7] = true := by decide +kernel
theorem subd3_6_98 : subd3_6 [-1, 0, -6] = true := by decide +kernel
theorem subd3_6_99 : subd3_6 [-1, 0, -5] = true := by decide +kernel
theorem subd3_6_100 : subd3_6 [-1, 0, -4] = true := by decide +kernel
theorem subd3_6_101 : subd3_6 [-1, 0, -3] = true := by decide +kernel
theorem subd3_6_102 : subd3_6 [-1, 0, -2] = true := by decide +kernel
theorem subd3_6_103 : subd3_6 [-1, 0, -1] = true := by decide +kernel
theorem subd3_6_104 : subd3_6 [-1, 0, 0] = true := by decide +kernel
theorem subd3_6_105 : subd3_6 [-1, 0, 1] = true := by decide +kernel
theorem subd3_6_106 : subd3_6 [-1, 0, 2] = true := by decide +kernel
theorem subd3_6_107 : subd3_6 [-1, 0, 3] = true := by decide +kernel
theorem subd3_6_108 : subd3_6 [-1, 0, 4] = true := by decide +kernel
theorem subd3_6_109 : subd3_6 [-1, 0, 5] = true := by decide +kernel
theorem subd3_6_110 : subd3_6 [-1, 0, 6] = true := by decide +kernel
theorem subd3_6_111 : subd3_6 [-1, 0, 7] = true := by decide +kernel
theorem subd3_6_112 : subd3_6 [-1, 0, 8] = true := by decide +kernel
theorem subd3_6_113 : subd3_6 [-1, 1, -9] = true := by decide +kernel
theorem subd3_6_114 : subd3_6 [-1, 1, -8] = true := by decide +kernel
theorem subd3_6_115 : subd3_6 [-1, 1, -7] = true := by decide +kernel
theorem subd3_6_116 : subd3_6 [-1, 1, -6] = true := by decide +kernel
theorem subd3_6_117 : subd3_6 [-1, 1, -5] = true := by decide +kernel
theorem subd3_6_118 : subd3_6 [-1, 1, -4] = true := by decide +kernel
theorem subd3_6_119 : subd3_6 [-1, 1, -3] = true := by decide +kernel
theorem subd3_6_120 : subd3_6 [-1, 1, -2] = true := by decide +kernel
theorem subd3_6_121 : subd3_6 [-1, 1, -1] = true := by decide +kernel
theorem subd3_6_122 : subd3_6 [-1, 1, 0] = true := by decide +kernel
theorem subd3_6_123 : subd3_6 [-1, 1, 1] = true := by decide +kernel
theorem subd3_6_124 : subd3_6 [-1, 1, 2] = true := by decide +kernel
theorem subd3_6_125 : subd3_6 [-1, 1, 3] = true := by decide +kernel
theorem subd3_6_126 : subd3_6 [-1, 1, 4] = true := by decide +kernel
theorem subd3_6_127 : subd3_6 [-1, 1, 5] = true := by decide +kernel
theorem sbd3_6_3 : ∀ q ∈ blkd3_6_3, subd3_6 q = true := by
  unfold blkd3_6_3
  exact List.forall_mem_cons.2 ⟨subd3_6_96, List.forall_mem_cons.2 ⟨subd3_6_97, List.forall_mem_cons.2 ⟨subd3_6_98, List.forall_mem_cons.2 ⟨subd3_6_99, List.forall_mem_cons.2 ⟨subd3_6_100, List.forall_mem_cons.2 ⟨subd3_6_101, List.forall_mem_cons.2 ⟨subd3_6_102, List.forall_mem_cons.2 ⟨subd3_6_103, List.forall_mem_cons.2 ⟨subd3_6_104, List.forall_mem_cons.2 ⟨subd3_6_105, List.forall_mem_cons.2 ⟨subd3_6_106, List.forall_mem_cons.2 ⟨subd3_6_107, List.forall_mem_cons.2 ⟨subd3_6_108, List.forall_mem_cons.2 ⟨subd3_6_109, List.forall_mem_cons.2 ⟨subd3_6_110, List.forall_mem_cons.2 ⟨subd3_6_111, List.forall_mem_cons.2 ⟨subd3_6_112, List.forall_mem_cons.2 ⟨subd3_6_113, List.forall_mem_cons.2 ⟨subd3_6_114, List.forall_mem_cons.2 ⟨subd3_6_115, List.forall_mem_cons.2 ⟨subd3_6_116, List.forall_mem_cons.2 ⟨subd3_6_117, List.forall_mem_cons.2 ⟨subd3_6_118, List.forall_mem_cons.2 ⟨subd3_6_119, List.forall_mem_cons.2 ⟨subd3_6_120, List.forall_mem_cons.2 ⟨subd3_6_121, List.forall_mem_cons.2 ⟨subd3_6_122, List.forall_mem_cons.2 ⟨subd3_6_123, List.forall_mem_cons.2 ⟨subd3_6_124, List.forall_mem_cons.2 ⟨subd3_6_125, List.forall_mem_cons.2 ⟨subd3_6_126, List.forall_mem_cons.2 ⟨subd3_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_128 : subd3_6 [-1, 1, 6] = true := by decide +kernel
theorem subd3_6_129 : subd3_6 [-1, 1, 7] = true := by decide +kernel
theorem subd3_6_130 : subd3_6 [-1, 1, 8] = true := by decide +kernel
theorem subd3_6_131 : subd3_6 [-1, 2, -8] = true := by decide +kernel
theorem subd3_6_132 : subd3_6 [-1, 2, -7] = true := by decide +kernel
theorem subd3_6_133 : subd3_6 [-1, 2, -6] = true := by decide +kernel
theorem subd3_6_134 : subd3_6 [-1, 2, -5] = true := by decide +kernel
theorem subd3_6_135 : subd3_6 [-1, 2, -4] = true := by decide +kernel
theorem subd3_6_136 : subd3_6 [-1, 2, -3] = true := by decide +kernel
theorem subd3_6_137 : subd3_6 [-1, 2, -2] = true := by decide +kernel
theorem subd3_6_138 : subd3_6 [-1, 2, -1] = true := by decide +kernel
theorem subd3_6_139 : subd3_6 [-1, 2, 0] = true := by decide +kernel
theorem subd3_6_140 : subd3_6 [-1, 2, 1] = true := by decide +kernel
theorem subd3_6_141 : subd3_6 [-1, 2, 2] = true := by decide +kernel
theorem subd3_6_142 : subd3_6 [-1, 2, 3] = true := by decide +kernel
theorem subd3_6_143 : subd3_6 [-1, 2, 4] = true := by decide +kernel
theorem subd3_6_144 : subd3_6 [-1, 2, 5] = true := by decide +kernel
theorem subd3_6_145 : subd3_6 [-1, 2, 6] = true := by decide +kernel
theorem subd3_6_146 : subd3_6 [-1, 2, 7] = true := by decide +kernel
theorem subd3_6_147 : subd3_6 [-1, 2, 8] = true := by decide +kernel
theorem subd3_6_148 : subd3_6 [-1, 3] = true := by decide +kernel
theorem subd3_6_149 : subd3_6 [0, -4] = true := by decide +kernel
theorem subd3_6_150 : subd3_6 [0, -3] = true := by decide +kernel
theorem subd3_6_151 : subd3_6 [0, -2, -9] = true := by decide +kernel
theorem subd3_6_152 : subd3_6 [0, -2, -8] = true := by decide +kernel
theorem subd3_6_153 : subd3_6 [0, -2, -7] = true := by decide +kernel
theorem subd3_6_154 : subd3_6 [0, -2, -6] = true := by decide +kernel
theorem subd3_6_155 : subd3_6 [0, -2, -5] = true := by decide +kernel
theorem subd3_6_156 : subd3_6 [0, -2, -4] = true := by decide +kernel
theorem subd3_6_157 : subd3_6 [0, -2, -3] = true := by decide +kernel
theorem subd3_6_158 : subd3_6 [0, -2, -2] = true := by decide +kernel
theorem subd3_6_159 : subd3_6 [0, -2, -1] = true := by decide +kernel
theorem sbd3_6_4 : ∀ q ∈ blkd3_6_4, subd3_6 q = true := by
  unfold blkd3_6_4
  exact List.forall_mem_cons.2 ⟨subd3_6_128, List.forall_mem_cons.2 ⟨subd3_6_129, List.forall_mem_cons.2 ⟨subd3_6_130, List.forall_mem_cons.2 ⟨subd3_6_131, List.forall_mem_cons.2 ⟨subd3_6_132, List.forall_mem_cons.2 ⟨subd3_6_133, List.forall_mem_cons.2 ⟨subd3_6_134, List.forall_mem_cons.2 ⟨subd3_6_135, List.forall_mem_cons.2 ⟨subd3_6_136, List.forall_mem_cons.2 ⟨subd3_6_137, List.forall_mem_cons.2 ⟨subd3_6_138, List.forall_mem_cons.2 ⟨subd3_6_139, List.forall_mem_cons.2 ⟨subd3_6_140, List.forall_mem_cons.2 ⟨subd3_6_141, List.forall_mem_cons.2 ⟨subd3_6_142, List.forall_mem_cons.2 ⟨subd3_6_143, List.forall_mem_cons.2 ⟨subd3_6_144, List.forall_mem_cons.2 ⟨subd3_6_145, List.forall_mem_cons.2 ⟨subd3_6_146, List.forall_mem_cons.2 ⟨subd3_6_147, List.forall_mem_cons.2 ⟨subd3_6_148, List.forall_mem_cons.2 ⟨subd3_6_149, List.forall_mem_cons.2 ⟨subd3_6_150, List.forall_mem_cons.2 ⟨subd3_6_151, List.forall_mem_cons.2 ⟨subd3_6_152, List.forall_mem_cons.2 ⟨subd3_6_153, List.forall_mem_cons.2 ⟨subd3_6_154, List.forall_mem_cons.2 ⟨subd3_6_155, List.forall_mem_cons.2 ⟨subd3_6_156, List.forall_mem_cons.2 ⟨subd3_6_157, List.forall_mem_cons.2 ⟨subd3_6_158, List.forall_mem_cons.2 ⟨subd3_6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
