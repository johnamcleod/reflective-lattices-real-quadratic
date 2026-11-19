import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_64 : subd9_1 [-3, -1, 5] = true := by decide +kernel
theorem subd9_1_65 : subd9_1 [-3, -1, 6] = true := by decide +kernel
theorem subd9_1_66 : subd9_1 [-3, 0, -7] = true := by decide +kernel
theorem subd9_1_67 : subd9_1 [-3, 0, -6] = true := by decide +kernel
theorem subd9_1_68 : subd9_1 [-3, 0, -5] = true := by decide +kernel
theorem subd9_1_69 : subd9_1 [-3, 0, -4] = true := by decide +kernel
theorem subd9_1_70 : subd9_1 [-3, 0, -3] = true := by decide +kernel
theorem subd9_1_71 : subd9_1 [-3, 0, -2] = true := by decide +kernel
theorem subd9_1_72 : subd9_1 [-3, 0, -1] = true := by decide +kernel
theorem subd9_1_73 : subd9_1 [-3, 0, 0] = true := by decide +kernel
theorem subd9_1_74 : subd9_1 [-3, 0, 1] = true := by decide +kernel
theorem subd9_1_75 : subd9_1 [-3, 0, 2] = true := by decide +kernel
theorem subd9_1_76 : subd9_1 [-3, 0, 3] = true := by decide +kernel
theorem subd9_1_77 : subd9_1 [-3, 0, 4] = true := by decide +kernel
theorem subd9_1_78 : subd9_1 [-3, 0, 5] = true := by decide +kernel
theorem subd9_1_79 : subd9_1 [-3, 0, 6] = true := by decide +kernel
theorem subd9_1_80 : subd9_1 [-3, 1, -7] = true := by decide +kernel
theorem subd9_1_81 : subd9_1 [-3, 1, -6] = true := by decide +kernel
theorem subd9_1_82 : subd9_1 [-3, 1, -5] = true := by decide +kernel
theorem subd9_1_83 : subd9_1 [-3, 1, -4] = true := by decide +kernel
theorem subd9_1_84 : subd9_1 [-3, 1, -3] = true := by decide +kernel
theorem subd9_1_85 : subd9_1 [-3, 1, -2] = true := by decide +kernel
theorem subd9_1_86 : subd9_1 [-3, 1, -1] = true := by decide +kernel
theorem subd9_1_87 : subd9_1 [-3, 1, 0] = true := by decide +kernel
theorem subd9_1_88 : subd9_1 [-3, 1, 1] = true := by decide +kernel
theorem subd9_1_89 : subd9_1 [-3, 1, 2] = true := by decide +kernel
theorem subd9_1_90 : subd9_1 [-3, 1, 3] = true := by decide +kernel
theorem subd9_1_91 : subd9_1 [-3, 1, 4] = true := by decide +kernel
theorem subd9_1_92 : subd9_1 [-3, 1, 5] = true := by decide +kernel
theorem subd9_1_93 : subd9_1 [-3, 1, 6] = true := by decide +kernel
theorem subd9_1_94 : subd9_1 [-3, 2] = true := by decide +kernel
theorem subd9_1_95 : subd9_1 [-3, 3] = true := by decide +kernel
theorem sbd9_1_2 : ∀ q ∈ blkd9_1_2, subd9_1 q = true := by
  unfold blkd9_1_2
  exact List.forall_mem_cons.2 ⟨subd9_1_64, List.forall_mem_cons.2 ⟨subd9_1_65, List.forall_mem_cons.2 ⟨subd9_1_66, List.forall_mem_cons.2 ⟨subd9_1_67, List.forall_mem_cons.2 ⟨subd9_1_68, List.forall_mem_cons.2 ⟨subd9_1_69, List.forall_mem_cons.2 ⟨subd9_1_70, List.forall_mem_cons.2 ⟨subd9_1_71, List.forall_mem_cons.2 ⟨subd9_1_72, List.forall_mem_cons.2 ⟨subd9_1_73, List.forall_mem_cons.2 ⟨subd9_1_74, List.forall_mem_cons.2 ⟨subd9_1_75, List.forall_mem_cons.2 ⟨subd9_1_76, List.forall_mem_cons.2 ⟨subd9_1_77, List.forall_mem_cons.2 ⟨subd9_1_78, List.forall_mem_cons.2 ⟨subd9_1_79, List.forall_mem_cons.2 ⟨subd9_1_80, List.forall_mem_cons.2 ⟨subd9_1_81, List.forall_mem_cons.2 ⟨subd9_1_82, List.forall_mem_cons.2 ⟨subd9_1_83, List.forall_mem_cons.2 ⟨subd9_1_84, List.forall_mem_cons.2 ⟨subd9_1_85, List.forall_mem_cons.2 ⟨subd9_1_86, List.forall_mem_cons.2 ⟨subd9_1_87, List.forall_mem_cons.2 ⟨subd9_1_88, List.forall_mem_cons.2 ⟨subd9_1_89, List.forall_mem_cons.2 ⟨subd9_1_90, List.forall_mem_cons.2 ⟨subd9_1_91, List.forall_mem_cons.2 ⟨subd9_1_92, List.forall_mem_cons.2 ⟨subd9_1_93, List.forall_mem_cons.2 ⟨subd9_1_94, List.forall_mem_cons.2 ⟨subd9_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_96 : subd9_1 [-3, 4] = true := by decide +kernel
theorem subd9_1_97 : subd9_1 [-3, 5] = true := by decide +kernel
theorem subd9_1_98 : subd9_1 [-3, 6] = true := by decide +kernel
theorem subd9_1_99 : subd9_1 [-2, -8] = true := by decide +kernel
theorem subd9_1_100 : subd9_1 [-2, -7] = true := by decide +kernel
theorem subd9_1_101 : subd9_1 [-2, -6] = true := by decide +kernel
theorem subd9_1_102 : subd9_1 [-2, -5] = true := by decide +kernel
theorem subd9_1_103 : subd9_1 [-2, -4] = true := by decide +kernel
theorem subd9_1_104 : subd9_1 [-2, -3, -6] = true := by decide +kernel
theorem subd9_1_105 : subd9_1 [-2, -3, -5] = true := by decide +kernel
theorem subd9_1_106 : subd9_1 [-2, -3, -4] = true := by decide +kernel
theorem subd9_1_107 : subd9_1 [-2, -3, -3] = true := by decide +kernel
theorem subd9_1_108 : subd9_1 [-2, -3, -2] = true := by decide +kernel
theorem subd9_1_109 : subd9_1 [-2, -3, -1] = true := by decide +kernel
theorem subd9_1_110 : subd9_1 [-2, -3, 0] = true := by decide +kernel
theorem subd9_1_111 : subd9_1 [-2, -3, 1] = true := by decide +kernel
theorem subd9_1_112 : subd9_1 [-2, -3, 2] = true := by decide +kernel
theorem subd9_1_113 : subd9_1 [-2, -3, 3] = true := by decide +kernel
theorem subd9_1_114 : subd9_1 [-2, -3, 4] = true := by decide +kernel
theorem subd9_1_115 : subd9_1 [-2, -3, 5] = true := by decide +kernel
theorem subd9_1_116 : subd9_1 [-2, -3, 6] = true := by decide +kernel
theorem subd9_1_117 : subd9_1 [-2, -3, 7] = true := by decide +kernel
theorem subd9_1_118 : subd9_1 [-2, -2, -6] = true := by decide +kernel
theorem subd9_1_119 : subd9_1 [-2, -2, -5] = true := by decide +kernel
theorem subd9_1_120 : subd9_1 [-2, -2, -4] = true := by decide +kernel
theorem subd9_1_121 : subd9_1 [-2, -2, -3] = true := by decide +kernel
theorem subd9_1_122 : subd9_1 [-2, -2, -2] = true := by decide +kernel
theorem subd9_1_123 : subd9_1 [-2, -2, -1] = true := by decide +kernel
theorem subd9_1_124 : subd9_1 [-2, -2, 0] = true := by decide +kernel
theorem subd9_1_125 : subd9_1 [-2, -2, 1] = true := by decide +kernel
theorem subd9_1_126 : subd9_1 [-2, -2, 2] = true := by decide +kernel
theorem subd9_1_127 : subd9_1 [-2, -2, 3] = true := by decide +kernel
theorem sbd9_1_3 : ∀ q ∈ blkd9_1_3, subd9_1 q = true := by
  unfold blkd9_1_3
  exact List.forall_mem_cons.2 ⟨subd9_1_96, List.forall_mem_cons.2 ⟨subd9_1_97, List.forall_mem_cons.2 ⟨subd9_1_98, List.forall_mem_cons.2 ⟨subd9_1_99, List.forall_mem_cons.2 ⟨subd9_1_100, List.forall_mem_cons.2 ⟨subd9_1_101, List.forall_mem_cons.2 ⟨subd9_1_102, List.forall_mem_cons.2 ⟨subd9_1_103, List.forall_mem_cons.2 ⟨subd9_1_104, List.forall_mem_cons.2 ⟨subd9_1_105, List.forall_mem_cons.2 ⟨subd9_1_106, List.forall_mem_cons.2 ⟨subd9_1_107, List.forall_mem_cons.2 ⟨subd9_1_108, List.forall_mem_cons.2 ⟨subd9_1_109, List.forall_mem_cons.2 ⟨subd9_1_110, List.forall_mem_cons.2 ⟨subd9_1_111, List.forall_mem_cons.2 ⟨subd9_1_112, List.forall_mem_cons.2 ⟨subd9_1_113, List.forall_mem_cons.2 ⟨subd9_1_114, List.forall_mem_cons.2 ⟨subd9_1_115, List.forall_mem_cons.2 ⟨subd9_1_116, List.forall_mem_cons.2 ⟨subd9_1_117, List.forall_mem_cons.2 ⟨subd9_1_118, List.forall_mem_cons.2 ⟨subd9_1_119, List.forall_mem_cons.2 ⟨subd9_1_120, List.forall_mem_cons.2 ⟨subd9_1_121, List.forall_mem_cons.2 ⟨subd9_1_122, List.forall_mem_cons.2 ⟨subd9_1_123, List.forall_mem_cons.2 ⟨subd9_1_124, List.forall_mem_cons.2 ⟨subd9_1_125, List.forall_mem_cons.2 ⟨subd9_1_126, List.forall_mem_cons.2 ⟨subd9_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_128 : subd9_1 [-2, -2, 4] = true := by decide +kernel
theorem subd9_1_129 : subd9_1 [-2, -2, 5] = true := by decide +kernel
theorem subd9_1_130 : subd9_1 [-2, -2, 6] = true := by decide +kernel
theorem subd9_1_131 : subd9_1 [-2, -2, 7] = true := by decide +kernel
theorem subd9_1_132 : subd9_1 [-2, -1, -7] = true := by decide +kernel
theorem subd9_1_133 : subd9_1 [-2, -1, -6] = true := by decide +kernel
theorem subd9_1_134 : subd9_1 [-2, -1, -5] = true := by decide +kernel
theorem subd9_1_135 : subd9_1 [-2, -1, -4] = true := by decide +kernel
theorem subd9_1_136 : subd9_1 [-2, -1, -3] = true := by decide +kernel
theorem subd9_1_137 : subd9_1 [-2, -1, -2] = true := by decide +kernel
theorem subd9_1_138 : subd9_1 [-2, -1, -1] = true := by decide +kernel
theorem subd9_1_139 : subd9_1 [-2, -1, 0] = true := by decide +kernel
theorem subd9_1_140 : subd9_1 [-2, -1, 1] = true := by decide +kernel
theorem subd9_1_141 : subd9_1 [-2, -1, 2] = true := by decide +kernel
theorem subd9_1_142 : subd9_1 [-2, -1, 3] = true := by decide +kernel
theorem subd9_1_143 : subd9_1 [-2, -1, 4] = true := by decide +kernel
theorem subd9_1_144 : subd9_1 [-2, -1, 5] = true := by decide +kernel
theorem subd9_1_145 : subd9_1 [-2, -1, 6] = true := by decide +kernel
theorem subd9_1_146 : subd9_1 [-2, -1, 7] = true := by decide +kernel
theorem subd9_1_147 : subd9_1 [-2, 0, -7] = true := by decide +kernel
theorem subd9_1_148 : subd9_1 [-2, 0, -6] = true := by decide +kernel
theorem subd9_1_149 : subd9_1 [-2, 0, -5] = true := by decide +kernel
theorem subd9_1_150 : subd9_1 [-2, 0, -4] = true := by decide +kernel
theorem subd9_1_151 : subd9_1 [-2, 0, -3] = true := by decide +kernel
theorem subd9_1_152 : subd9_1 [-2, 0, -2] = true := by decide +kernel
theorem subd9_1_153 : subd9_1 [-2, 0, -1] = true := by decide +kernel
theorem subd9_1_154 : subd9_1 [-2, 0, 0] = true := by decide +kernel
theorem subd9_1_155 : subd9_1 [-2, 0, 1] = true := by decide +kernel
theorem subd9_1_156 : subd9_1 [-2, 0, 2] = true := by decide +kernel
theorem subd9_1_157 : subd9_1 [-2, 0, 3] = true := by decide +kernel
theorem subd9_1_158 : subd9_1 [-2, 0, 4] = true := by decide +kernel
theorem subd9_1_159 : subd9_1 [-2, 0, 5] = true := by decide +kernel
theorem sbd9_1_4 : ∀ q ∈ blkd9_1_4, subd9_1 q = true := by
  unfold blkd9_1_4
  exact List.forall_mem_cons.2 ⟨subd9_1_128, List.forall_mem_cons.2 ⟨subd9_1_129, List.forall_mem_cons.2 ⟨subd9_1_130, List.forall_mem_cons.2 ⟨subd9_1_131, List.forall_mem_cons.2 ⟨subd9_1_132, List.forall_mem_cons.2 ⟨subd9_1_133, List.forall_mem_cons.2 ⟨subd9_1_134, List.forall_mem_cons.2 ⟨subd9_1_135, List.forall_mem_cons.2 ⟨subd9_1_136, List.forall_mem_cons.2 ⟨subd9_1_137, List.forall_mem_cons.2 ⟨subd9_1_138, List.forall_mem_cons.2 ⟨subd9_1_139, List.forall_mem_cons.2 ⟨subd9_1_140, List.forall_mem_cons.2 ⟨subd9_1_141, List.forall_mem_cons.2 ⟨subd9_1_142, List.forall_mem_cons.2 ⟨subd9_1_143, List.forall_mem_cons.2 ⟨subd9_1_144, List.forall_mem_cons.2 ⟨subd9_1_145, List.forall_mem_cons.2 ⟨subd9_1_146, List.forall_mem_cons.2 ⟨subd9_1_147, List.forall_mem_cons.2 ⟨subd9_1_148, List.forall_mem_cons.2 ⟨subd9_1_149, List.forall_mem_cons.2 ⟨subd9_1_150, List.forall_mem_cons.2 ⟨subd9_1_151, List.forall_mem_cons.2 ⟨subd9_1_152, List.forall_mem_cons.2 ⟨subd9_1_153, List.forall_mem_cons.2 ⟨subd9_1_154, List.forall_mem_cons.2 ⟨subd9_1_155, List.forall_mem_cons.2 ⟨subd9_1_156, List.forall_mem_cons.2 ⟨subd9_1_157, List.forall_mem_cons.2 ⟨subd9_1_158, List.forall_mem_cons.2 ⟨subd9_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_160 : subd9_1 [-2, 0, 6] = true := by decide +kernel
theorem subd9_1_161 : subd9_1 [-2, 0, 7] = true := by decide +kernel
theorem subd9_1_162 : subd9_1 [-2, 1, -8] = true := by decide +kernel
theorem subd9_1_163 : subd9_1 [-2, 1, -7] = true := by decide +kernel
theorem subd9_1_164 : subd9_1 [-2, 1, -6] = true := by decide +kernel
theorem subd9_1_165 : subd9_1 [-2, 1, -5] = true := by decide +kernel
theorem subd9_1_166 : subd9_1 [-2, 1, -4] = true := by decide +kernel
theorem subd9_1_167 : subd9_1 [-2, 1, -3] = true := by decide +kernel
theorem subd9_1_168 : subd9_1 [-2, 1, -2] = true := by decide +kernel
theorem subd9_1_169 : subd9_1 [-2, 1, -1] = true := by decide +kernel
theorem subd9_1_170 : subd9_1 [-2, 1, 0] = true := by decide +kernel
theorem subd9_1_171 : subd9_1 [-2, 1, 1] = true := by decide +kernel
theorem subd9_1_172 : subd9_1 [-2, 1, 2] = true := by decide +kernel
theorem subd9_1_173 : subd9_1 [-2, 1, 3] = true := by decide +kernel
theorem subd9_1_174 : subd9_1 [-2, 1, 4] = true := by decide +kernel
theorem subd9_1_175 : subd9_1 [-2, 1, 5] = true := by decide +kernel
theorem subd9_1_176 : subd9_1 [-2, 1, 6] = true := by decide +kernel
theorem subd9_1_177 : subd9_1 [-2, 2, -8] = true := by decide +kernel
theorem subd9_1_178 : subd9_1 [-2, 2, -7] = true := by decide +kernel
theorem subd9_1_179 : subd9_1 [-2, 2, -6] = true := by decide +kernel
theorem subd9_1_180 : subd9_1 [-2, 2, -5] = true := by decide +kernel
theorem subd9_1_181 : subd9_1 [-2, 2, -4] = true := by decide +kernel
theorem subd9_1_182 : subd9_1 [-2, 2, -3] = true := by decide +kernel
theorem subd9_1_183 : subd9_1 [-2, 2, -2] = true := by decide +kernel
theorem subd9_1_184 : subd9_1 [-2, 2, -1] = true := by decide +kernel
theorem subd9_1_185 : subd9_1 [-2, 2, 0] = true := by decide +kernel
theorem subd9_1_186 : subd9_1 [-2, 2, 1] = true := by decide +kernel
theorem subd9_1_187 : subd9_1 [-2, 2, 2] = true := by decide +kernel
theorem subd9_1_188 : subd9_1 [-2, 2, 3] = true := by decide +kernel
theorem subd9_1_189 : subd9_1 [-2, 2, 4] = true := by decide +kernel
theorem subd9_1_190 : subd9_1 [-2, 2, 5] = true := by decide +kernel
theorem subd9_1_191 : subd9_1 [-2, 2, 6] = true := by decide +kernel
theorem sbd9_1_5 : ∀ q ∈ blkd9_1_5, subd9_1 q = true := by
  unfold blkd9_1_5
  exact List.forall_mem_cons.2 ⟨subd9_1_160, List.forall_mem_cons.2 ⟨subd9_1_161, List.forall_mem_cons.2 ⟨subd9_1_162, List.forall_mem_cons.2 ⟨subd9_1_163, List.forall_mem_cons.2 ⟨subd9_1_164, List.forall_mem_cons.2 ⟨subd9_1_165, List.forall_mem_cons.2 ⟨subd9_1_166, List.forall_mem_cons.2 ⟨subd9_1_167, List.forall_mem_cons.2 ⟨subd9_1_168, List.forall_mem_cons.2 ⟨subd9_1_169, List.forall_mem_cons.2 ⟨subd9_1_170, List.forall_mem_cons.2 ⟨subd9_1_171, List.forall_mem_cons.2 ⟨subd9_1_172, List.forall_mem_cons.2 ⟨subd9_1_173, List.forall_mem_cons.2 ⟨subd9_1_174, List.forall_mem_cons.2 ⟨subd9_1_175, List.forall_mem_cons.2 ⟨subd9_1_176, List.forall_mem_cons.2 ⟨subd9_1_177, List.forall_mem_cons.2 ⟨subd9_1_178, List.forall_mem_cons.2 ⟨subd9_1_179, List.forall_mem_cons.2 ⟨subd9_1_180, List.forall_mem_cons.2 ⟨subd9_1_181, List.forall_mem_cons.2 ⟨subd9_1_182, List.forall_mem_cons.2 ⟨subd9_1_183, List.forall_mem_cons.2 ⟨subd9_1_184, List.forall_mem_cons.2 ⟨subd9_1_185, List.forall_mem_cons.2 ⟨subd9_1_186, List.forall_mem_cons.2 ⟨subd9_1_187, List.forall_mem_cons.2 ⟨subd9_1_188, List.forall_mem_cons.2 ⟨subd9_1_189, List.forall_mem_cons.2 ⟨subd9_1_190, List.forall_mem_cons.2 ⟨subd9_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_192 : subd9_1 [-2, 3] = true := by decide +kernel
theorem subd9_1_193 : subd9_1 [-2, 4] = true := by decide +kernel
theorem subd9_1_194 : subd9_1 [-2, 5] = true := by decide +kernel
theorem subd9_1_195 : subd9_1 [-2, 6] = true := by decide +kernel
theorem subd9_1_196 : subd9_1 [-1, -8] = true := by decide +kernel
theorem subd9_1_197 : subd9_1 [-1, -7] = true := by decide +kernel
theorem subd9_1_198 : subd9_1 [-1, -6] = true := by decide +kernel
theorem subd9_1_199 : subd9_1 [-1, -5] = true := by decide +kernel
theorem subd9_1_200 : subd9_1 [-1, -4] = true := by decide +kernel
theorem subd9_1_201 : subd9_1 [-1, -3, -6] = true := by decide +kernel
theorem subd9_1_202 : subd9_1 [-1, -3, -5] = true := by decide +kernel
theorem subd9_1_203 : subd9_1 [-1, -3, -4] = true := by decide +kernel
theorem subd9_1_204 : subd9_1 [-1, -3, -3] = true := by decide +kernel
theorem subd9_1_205 : subd9_1 [-1, -3, -2] = true := by decide +kernel
theorem subd9_1_206 : subd9_1 [-1, -3, -1] = true := by decide +kernel
theorem subd9_1_207 : subd9_1 [-1, -3, 0] = true := by decide +kernel
theorem subd9_1_208 : subd9_1 [-1, -3, 1] = true := by decide +kernel
theorem subd9_1_209 : subd9_1 [-1, -3, 2] = true := by decide +kernel
theorem subd9_1_210 : subd9_1 [-1, -3, 3] = true := by decide +kernel
theorem subd9_1_211 : subd9_1 [-1, -3, 4] = true := by decide +kernel
theorem subd9_1_212 : subd9_1 [-1, -3, 5] = true := by decide +kernel
theorem subd9_1_213 : subd9_1 [-1, -3, 6] = true := by decide +kernel
theorem subd9_1_214 : subd9_1 [-1, -3, 7] = true := by decide +kernel
theorem subd9_1_215 : subd9_1 [-1, -2, -7] = true := by decide +kernel
theorem subd9_1_216 : subd9_1 [-1, -2, -6] = true := by decide +kernel
theorem subd9_1_217 : subd9_1 [-1, -2, -5] = true := by decide +kernel
theorem subd9_1_218 : subd9_1 [-1, -2, -4] = true := by decide +kernel
theorem subd9_1_219 : subd9_1 [-1, -2, -3] = true := by decide +kernel
theorem subd9_1_220 : subd9_1 [-1, -2, -2] = true := by decide +kernel
theorem subd9_1_221 : subd9_1 [-1, -2, -1] = true := by decide +kernel
theorem subd9_1_222 : subd9_1 [-1, -2, 0] = true := by decide +kernel
theorem subd9_1_223 : subd9_1 [-1, -2, 1] = true := by decide +kernel
theorem sbd9_1_6 : ∀ q ∈ blkd9_1_6, subd9_1 q = true := by
  unfold blkd9_1_6
  exact List.forall_mem_cons.2 ⟨subd9_1_192, List.forall_mem_cons.2 ⟨subd9_1_193, List.forall_mem_cons.2 ⟨subd9_1_194, List.forall_mem_cons.2 ⟨subd9_1_195, List.forall_mem_cons.2 ⟨subd9_1_196, List.forall_mem_cons.2 ⟨subd9_1_197, List.forall_mem_cons.2 ⟨subd9_1_198, List.forall_mem_cons.2 ⟨subd9_1_199, List.forall_mem_cons.2 ⟨subd9_1_200, List.forall_mem_cons.2 ⟨subd9_1_201, List.forall_mem_cons.2 ⟨subd9_1_202, List.forall_mem_cons.2 ⟨subd9_1_203, List.forall_mem_cons.2 ⟨subd9_1_204, List.forall_mem_cons.2 ⟨subd9_1_205, List.forall_mem_cons.2 ⟨subd9_1_206, List.forall_mem_cons.2 ⟨subd9_1_207, List.forall_mem_cons.2 ⟨subd9_1_208, List.forall_mem_cons.2 ⟨subd9_1_209, List.forall_mem_cons.2 ⟨subd9_1_210, List.forall_mem_cons.2 ⟨subd9_1_211, List.forall_mem_cons.2 ⟨subd9_1_212, List.forall_mem_cons.2 ⟨subd9_1_213, List.forall_mem_cons.2 ⟨subd9_1_214, List.forall_mem_cons.2 ⟨subd9_1_215, List.forall_mem_cons.2 ⟨subd9_1_216, List.forall_mem_cons.2 ⟨subd9_1_217, List.forall_mem_cons.2 ⟨subd9_1_218, List.forall_mem_cons.2 ⟨subd9_1_219, List.forall_mem_cons.2 ⟨subd9_1_220, List.forall_mem_cons.2 ⟨subd9_1_221, List.forall_mem_cons.2 ⟨subd9_1_222, List.forall_mem_cons.2 ⟨subd9_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_224 : subd9_1 [-1, -2, 2] = true := by decide +kernel
theorem subd9_1_225 : subd9_1 [-1, -2, 3] = true := by decide +kernel
theorem subd9_1_226 : subd9_1 [-1, -2, 4] = true := by decide +kernel
theorem subd9_1_227 : subd9_1 [-1, -2, 5] = true := by decide +kernel
theorem subd9_1_228 : subd9_1 [-1, -2, 6] = true := by decide +kernel
theorem subd9_1_229 : subd9_1 [-1, -2, 7] = true := by decide +kernel
theorem subd9_1_230 : subd9_1 [-1, -1, -7] = true := by decide +kernel
theorem subd9_1_231 : subd9_1 [-1, -1, -6] = true := by decide +kernel
theorem subd9_1_232 : subd9_1 [-1, -1, -5] = true := by decide +kernel
theorem subd9_1_233 : subd9_1 [-1, -1, -4] = true := by decide +kernel
theorem subd9_1_234 : subd9_1 [-1, -1, -3] = true := by decide +kernel
theorem subd9_1_235 : subd9_1 [-1, -1, -2] = true := by decide +kernel
theorem subd9_1_236 : subd9_1 [-1, -1, -1] = true := by decide +kernel
theorem subd9_1_237 : subd9_1 [-1, -1, 0] = true := by decide +kernel
theorem subd9_1_238 : subd9_1 [-1, -1, 1] = true := by decide +kernel
theorem subd9_1_239 : subd9_1 [-1, -1, 2] = true := by decide +kernel
theorem subd9_1_240 : subd9_1 [-1, -1, 3] = true := by decide +kernel
theorem subd9_1_241 : subd9_1 [-1, -1, 4] = true := by decide +kernel
theorem subd9_1_242 : subd9_1 [-1, -1, 5] = true := by decide +kernel
theorem subd9_1_243 : subd9_1 [-1, -1, 6] = true := by decide +kernel
theorem subd9_1_244 : subd9_1 [-1, -1, 7] = true := by decide +kernel
theorem subd9_1_245 : subd9_1 [-1, 0, -8] = true := by decide +kernel
theorem subd9_1_246 : subd9_1 [-1, 0, -7] = true := by decide +kernel
theorem subd9_1_247 : subd9_1 [-1, 0, -6] = true := by decide +kernel
theorem subd9_1_248 : subd9_1 [-1, 0, -5] = true := by decide +kernel
theorem subd9_1_249 : subd9_1 [-1, 0, -4] = true := by decide +kernel
theorem subd9_1_250 : subd9_1 [-1, 0, -3] = true := by decide +kernel
theorem subd9_1_251 : subd9_1 [-1, 0, -2] = true := by decide +kernel
theorem subd9_1_252 : subd9_1 [-1, 0, -1] = true := by decide +kernel
theorem subd9_1_253 : subd9_1 [-1, 0, 0] = true := by decide +kernel
theorem subd9_1_254 : subd9_1 [-1, 0, 1] = true := by decide +kernel
theorem subd9_1_255 : subd9_1 [-1, 0, 2] = true := by decide +kernel
theorem sbd9_1_7 : ∀ q ∈ blkd9_1_7, subd9_1 q = true := by
  unfold blkd9_1_7
  exact List.forall_mem_cons.2 ⟨subd9_1_224, List.forall_mem_cons.2 ⟨subd9_1_225, List.forall_mem_cons.2 ⟨subd9_1_226, List.forall_mem_cons.2 ⟨subd9_1_227, List.forall_mem_cons.2 ⟨subd9_1_228, List.forall_mem_cons.2 ⟨subd9_1_229, List.forall_mem_cons.2 ⟨subd9_1_230, List.forall_mem_cons.2 ⟨subd9_1_231, List.forall_mem_cons.2 ⟨subd9_1_232, List.forall_mem_cons.2 ⟨subd9_1_233, List.forall_mem_cons.2 ⟨subd9_1_234, List.forall_mem_cons.2 ⟨subd9_1_235, List.forall_mem_cons.2 ⟨subd9_1_236, List.forall_mem_cons.2 ⟨subd9_1_237, List.forall_mem_cons.2 ⟨subd9_1_238, List.forall_mem_cons.2 ⟨subd9_1_239, List.forall_mem_cons.2 ⟨subd9_1_240, List.forall_mem_cons.2 ⟨subd9_1_241, List.forall_mem_cons.2 ⟨subd9_1_242, List.forall_mem_cons.2 ⟨subd9_1_243, List.forall_mem_cons.2 ⟨subd9_1_244, List.forall_mem_cons.2 ⟨subd9_1_245, List.forall_mem_cons.2 ⟨subd9_1_246, List.forall_mem_cons.2 ⟨subd9_1_247, List.forall_mem_cons.2 ⟨subd9_1_248, List.forall_mem_cons.2 ⟨subd9_1_249, List.forall_mem_cons.2 ⟨subd9_1_250, List.forall_mem_cons.2 ⟨subd9_1_251, List.forall_mem_cons.2 ⟨subd9_1_252, List.forall_mem_cons.2 ⟨subd9_1_253, List.forall_mem_cons.2 ⟨subd9_1_254, List.forall_mem_cons.2 ⟨subd9_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_256 : subd9_1 [-1, 0, 3] = true := by decide +kernel
theorem subd9_1_257 : subd9_1 [-1, 0, 4] = true := by decide +kernel
theorem subd9_1_258 : subd9_1 [-1, 0, 5] = true := by decide +kernel
theorem subd9_1_259 : subd9_1 [-1, 0, 6] = true := by decide +kernel
theorem subd9_1_260 : subd9_1 [-1, 0, 7] = true := by decide +kernel
theorem subd9_1_261 : subd9_1 [-1, 1, -8] = true := by decide +kernel
theorem subd9_1_262 : subd9_1 [-1, 1, -7] = true := by decide +kernel
theorem subd9_1_263 : subd9_1 [-1, 1, -6] = true := by decide +kernel
theorem subd9_1_264 : subd9_1 [-1, 1, -5] = true := by decide +kernel
theorem subd9_1_265 : subd9_1 [-1, 1, -4] = true := by decide +kernel
theorem subd9_1_266 : subd9_1 [-1, 1, -3] = true := by decide +kernel
theorem subd9_1_267 : subd9_1 [-1, 1, -2] = true := by decide +kernel
theorem subd9_1_268 : subd9_1 [-1, 1, -1] = true := by decide +kernel
theorem subd9_1_269 : subd9_1 [-1, 1, 0] = true := by decide +kernel
theorem subd9_1_270 : subd9_1 [-1, 1, 1] = true := by decide +kernel
theorem subd9_1_271 : subd9_1 [-1, 1, 2] = true := by decide +kernel
theorem subd9_1_272 : subd9_1 [-1, 1, 3] = true := by decide +kernel
theorem subd9_1_273 : subd9_1 [-1, 1, 4] = true := by decide +kernel
theorem subd9_1_274 : subd9_1 [-1, 1, 5] = true := by decide +kernel
theorem subd9_1_275 : subd9_1 [-1, 1, 6] = true := by decide +kernel
theorem subd9_1_276 : subd9_1 [-1, 2, -8] = true := by decide +kernel
theorem subd9_1_277 : subd9_1 [-1, 2, -7] = true := by decide +kernel
theorem subd9_1_278 : subd9_1 [-1, 2, -6] = true := by decide +kernel
theorem subd9_1_279 : subd9_1 [-1, 2, -5] = true := by decide +kernel
theorem subd9_1_280 : subd9_1 [-1, 2, -4] = true := by decide +kernel
theorem subd9_1_281 : subd9_1 [-1, 2, -3] = true := by decide +kernel
theorem subd9_1_282 : subd9_1 [-1, 2, -2] = true := by decide +kernel
theorem subd9_1_283 : subd9_1 [-1, 2, -1] = true := by decide +kernel
theorem subd9_1_284 : subd9_1 [-1, 2, 0] = true := by decide +kernel
theorem subd9_1_285 : subd9_1 [-1, 2, 1] = true := by decide +kernel
theorem subd9_1_286 : subd9_1 [-1, 2, 2] = true := by decide +kernel
theorem subd9_1_287 : subd9_1 [-1, 2, 3] = true := by decide +kernel
theorem sbd9_1_8 : ∀ q ∈ blkd9_1_8, subd9_1 q = true := by
  unfold blkd9_1_8
  exact List.forall_mem_cons.2 ⟨subd9_1_256, List.forall_mem_cons.2 ⟨subd9_1_257, List.forall_mem_cons.2 ⟨subd9_1_258, List.forall_mem_cons.2 ⟨subd9_1_259, List.forall_mem_cons.2 ⟨subd9_1_260, List.forall_mem_cons.2 ⟨subd9_1_261, List.forall_mem_cons.2 ⟨subd9_1_262, List.forall_mem_cons.2 ⟨subd9_1_263, List.forall_mem_cons.2 ⟨subd9_1_264, List.forall_mem_cons.2 ⟨subd9_1_265, List.forall_mem_cons.2 ⟨subd9_1_266, List.forall_mem_cons.2 ⟨subd9_1_267, List.forall_mem_cons.2 ⟨subd9_1_268, List.forall_mem_cons.2 ⟨subd9_1_269, List.forall_mem_cons.2 ⟨subd9_1_270, List.forall_mem_cons.2 ⟨subd9_1_271, List.forall_mem_cons.2 ⟨subd9_1_272, List.forall_mem_cons.2 ⟨subd9_1_273, List.forall_mem_cons.2 ⟨subd9_1_274, List.forall_mem_cons.2 ⟨subd9_1_275, List.forall_mem_cons.2 ⟨subd9_1_276, List.forall_mem_cons.2 ⟨subd9_1_277, List.forall_mem_cons.2 ⟨subd9_1_278, List.forall_mem_cons.2 ⟨subd9_1_279, List.forall_mem_cons.2 ⟨subd9_1_280, List.forall_mem_cons.2 ⟨subd9_1_281, List.forall_mem_cons.2 ⟨subd9_1_282, List.forall_mem_cons.2 ⟨subd9_1_283, List.forall_mem_cons.2 ⟨subd9_1_284, List.forall_mem_cons.2 ⟨subd9_1_285, List.forall_mem_cons.2 ⟨subd9_1_286, List.forall_mem_cons.2 ⟨subd9_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_288 : subd9_1 [-1, 2, 4] = true := by decide +kernel
theorem subd9_1_289 : subd9_1 [-1, 2, 5] = true := by decide +kernel
theorem subd9_1_290 : subd9_1 [-1, 2, 6] = true := by decide +kernel
theorem subd9_1_291 : subd9_1 [-1, 3, -8] = true := by decide +kernel
theorem subd9_1_292 : subd9_1 [-1, 3, -7] = true := by decide +kernel
theorem subd9_1_293 : subd9_1 [-1, 3, -6] = true := by decide +kernel
theorem subd9_1_294 : subd9_1 [-1, 3, -5] = true := by decide +kernel
theorem subd9_1_295 : subd9_1 [-1, 3, -4] = true := by decide +kernel
theorem subd9_1_296 : subd9_1 [-1, 3, -3] = true := by decide +kernel
theorem subd9_1_297 : subd9_1 [-1, 3, -2] = true := by decide +kernel
theorem subd9_1_298 : subd9_1 [-1, 3, -1] = true := by decide +kernel
theorem subd9_1_299 : subd9_1 [-1, 3, 0] = true := by decide +kernel
theorem subd9_1_300 : subd9_1 [-1, 3, 1] = true := by decide +kernel
theorem subd9_1_301 : subd9_1 [-1, 3, 2] = true := by decide +kernel
theorem subd9_1_302 : subd9_1 [-1, 3, 3] = true := by decide +kernel
theorem subd9_1_303 : subd9_1 [-1, 3, 4] = true := by decide +kernel
theorem subd9_1_304 : subd9_1 [-1, 3, 5] = true := by decide +kernel
theorem subd9_1_305 : subd9_1 [-1, 4] = true := by decide +kernel
theorem subd9_1_306 : subd9_1 [-1, 5] = true := by decide +kernel
theorem subd9_1_307 : subd9_1 [-1, 6] = true := by decide +kernel
theorem subd9_1_308 : subd9_1 [-1, 7] = true := by decide +kernel
theorem subd9_1_309 : subd9_1 [0, -8] = true := by decide +kernel
theorem subd9_1_310 : subd9_1 [0, -7] = true := by decide +kernel
theorem subd9_1_311 : subd9_1 [0, -6] = true := by decide +kernel
theorem subd9_1_312 : subd9_1 [0, -5] = true := by decide +kernel
theorem subd9_1_313 : subd9_1 [0, -4] = true := by decide +kernel
theorem subd9_1_314 : subd9_1 [0, -3, -6] = true := by decide +kernel
theorem subd9_1_315 : subd9_1 [0, -3, -5] = true := by decide +kernel
theorem subd9_1_316 : subd9_1 [0, -3, -4] = true := by decide +kernel
theorem subd9_1_317 : subd9_1 [0, -3, -3] = true := by decide +kernel
theorem subd9_1_318 : subd9_1 [0, -3, -2] = true := by decide +kernel
theorem subd9_1_319 : subd9_1 [0, -3, -1] = true := by decide +kernel
theorem sbd9_1_9 : ∀ q ∈ blkd9_1_9, subd9_1 q = true := by
  unfold blkd9_1_9
  exact List.forall_mem_cons.2 ⟨subd9_1_288, List.forall_mem_cons.2 ⟨subd9_1_289, List.forall_mem_cons.2 ⟨subd9_1_290, List.forall_mem_cons.2 ⟨subd9_1_291, List.forall_mem_cons.2 ⟨subd9_1_292, List.forall_mem_cons.2 ⟨subd9_1_293, List.forall_mem_cons.2 ⟨subd9_1_294, List.forall_mem_cons.2 ⟨subd9_1_295, List.forall_mem_cons.2 ⟨subd9_1_296, List.forall_mem_cons.2 ⟨subd9_1_297, List.forall_mem_cons.2 ⟨subd9_1_298, List.forall_mem_cons.2 ⟨subd9_1_299, List.forall_mem_cons.2 ⟨subd9_1_300, List.forall_mem_cons.2 ⟨subd9_1_301, List.forall_mem_cons.2 ⟨subd9_1_302, List.forall_mem_cons.2 ⟨subd9_1_303, List.forall_mem_cons.2 ⟨subd9_1_304, List.forall_mem_cons.2 ⟨subd9_1_305, List.forall_mem_cons.2 ⟨subd9_1_306, List.forall_mem_cons.2 ⟨subd9_1_307, List.forall_mem_cons.2 ⟨subd9_1_308, List.forall_mem_cons.2 ⟨subd9_1_309, List.forall_mem_cons.2 ⟨subd9_1_310, List.forall_mem_cons.2 ⟨subd9_1_311, List.forall_mem_cons.2 ⟨subd9_1_312, List.forall_mem_cons.2 ⟨subd9_1_313, List.forall_mem_cons.2 ⟨subd9_1_314, List.forall_mem_cons.2 ⟨subd9_1_315, List.forall_mem_cons.2 ⟨subd9_1_316, List.forall_mem_cons.2 ⟨subd9_1_317, List.forall_mem_cons.2 ⟨subd9_1_318, List.forall_mem_cons.2 ⟨subd9_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_320 : subd9_1 [0, -3, 0] = true := by decide +kernel
theorem subd9_1_321 : subd9_1 [0, -3, 1] = true := by decide +kernel
theorem subd9_1_322 : subd9_1 [0, -3, 2] = true := by decide +kernel
theorem subd9_1_323 : subd9_1 [0, -3, 3] = true := by decide +kernel
theorem subd9_1_324 : subd9_1 [0, -3, 4] = true := by decide +kernel
theorem subd9_1_325 : subd9_1 [0, -3, 5] = true := by decide +kernel
theorem subd9_1_326 : subd9_1 [0, -3, 6] = true := by decide +kernel
theorem subd9_1_327 : subd9_1 [0, -3, 7] = true := by decide +kernel
theorem subd9_1_328 : subd9_1 [0, -2, -7] = true := by decide +kernel
theorem subd9_1_329 : subd9_1 [0, -2, -6] = true := by decide +kernel
theorem subd9_1_330 : subd9_1 [0, -2, -5] = true := by decide +kernel
theorem subd9_1_331 : subd9_1 [0, -2, -4] = true := by decide +kernel
theorem subd9_1_332 : subd9_1 [0, -2, -3] = true := by decide +kernel
theorem subd9_1_333 : subd9_1 [0, -2, -2] = true := by decide +kernel
theorem subd9_1_334 : subd9_1 [0, -2, -1] = true := by decide +kernel
theorem subd9_1_335 : subd9_1 [0, -2, 0] = true := by decide +kernel
theorem subd9_1_336 : subd9_1 [0, -2, 1] = true := by decide +kernel
theorem subd9_1_337 : subd9_1 [0, -2, 2] = true := by decide +kernel
theorem subd9_1_338 : subd9_1 [0, -2, 3] = true := by decide +kernel
theorem subd9_1_339 : subd9_1 [0, -2, 4] = true := by decide +kernel
theorem subd9_1_340 : subd9_1 [0, -2, 5] = true := by decide +kernel
theorem subd9_1_341 : subd9_1 [0, -2, 6] = true := by decide +kernel
theorem subd9_1_342 : subd9_1 [0, -2, 7] = true := by decide +kernel
theorem subd9_1_343 : subd9_1 [0, -1, -7] = true := by decide +kernel
theorem subd9_1_344 : subd9_1 [0, -1, -6] = true := by decide +kernel
theorem subd9_1_345 : subd9_1 [0, -1, -5] = true := by decide +kernel
theorem subd9_1_346 : subd9_1 [0, -1, -4] = true := by decide +kernel
theorem subd9_1_347 : subd9_1 [0, -1, -3] = true := by decide +kernel
theorem subd9_1_348 : subd9_1 [0, -1, -2] = true := by decide +kernel
theorem subd9_1_349 : subd9_1 [0, -1, -1] = true := by decide +kernel
theorem subd9_1_350 : subd9_1 [0, -1, 0] = true := by decide +kernel
theorem subd9_1_351 : subd9_1 [0, -1, 1] = true := by decide +kernel
theorem sbd9_1_10 : ∀ q ∈ blkd9_1_10, subd9_1 q = true := by
  unfold blkd9_1_10
  exact List.forall_mem_cons.2 ⟨subd9_1_320, List.forall_mem_cons.2 ⟨subd9_1_321, List.forall_mem_cons.2 ⟨subd9_1_322, List.forall_mem_cons.2 ⟨subd9_1_323, List.forall_mem_cons.2 ⟨subd9_1_324, List.forall_mem_cons.2 ⟨subd9_1_325, List.forall_mem_cons.2 ⟨subd9_1_326, List.forall_mem_cons.2 ⟨subd9_1_327, List.forall_mem_cons.2 ⟨subd9_1_328, List.forall_mem_cons.2 ⟨subd9_1_329, List.forall_mem_cons.2 ⟨subd9_1_330, List.forall_mem_cons.2 ⟨subd9_1_331, List.forall_mem_cons.2 ⟨subd9_1_332, List.forall_mem_cons.2 ⟨subd9_1_333, List.forall_mem_cons.2 ⟨subd9_1_334, List.forall_mem_cons.2 ⟨subd9_1_335, List.forall_mem_cons.2 ⟨subd9_1_336, List.forall_mem_cons.2 ⟨subd9_1_337, List.forall_mem_cons.2 ⟨subd9_1_338, List.forall_mem_cons.2 ⟨subd9_1_339, List.forall_mem_cons.2 ⟨subd9_1_340, List.forall_mem_cons.2 ⟨subd9_1_341, List.forall_mem_cons.2 ⟨subd9_1_342, List.forall_mem_cons.2 ⟨subd9_1_343, List.forall_mem_cons.2 ⟨subd9_1_344, List.forall_mem_cons.2 ⟨subd9_1_345, List.forall_mem_cons.2 ⟨subd9_1_346, List.forall_mem_cons.2 ⟨subd9_1_347, List.forall_mem_cons.2 ⟨subd9_1_348, List.forall_mem_cons.2 ⟨subd9_1_349, List.forall_mem_cons.2 ⟨subd9_1_350, List.forall_mem_cons.2 ⟨subd9_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_352 : subd9_1 [0, -1, 2] = true := by decide +kernel
theorem subd9_1_353 : subd9_1 [0, -1, 3] = true := by decide +kernel
theorem subd9_1_354 : subd9_1 [0, -1, 4] = true := by decide +kernel
theorem subd9_1_355 : subd9_1 [0, -1, 5] = true := by decide +kernel
theorem subd9_1_356 : subd9_1 [0, -1, 6] = true := by decide +kernel
theorem subd9_1_357 : subd9_1 [0, -1, 7] = true := by decide +kernel
theorem subd9_1_358 : subd9_1 [0, 0, -8] = true := by decide +kernel
theorem subd9_1_359 : subd9_1 [0, 0, -7] = true := by decide +kernel
theorem subd9_1_360 : subd9_1 [0, 0, -6] = true := by decide +kernel
theorem subd9_1_361 : subd9_1 [0, 0, -5] = true := by decide +kernel
theorem subd9_1_362 : subd9_1 [0, 0, -4] = true := by decide +kernel
theorem subd9_1_363 : subd9_1 [0, 0, -3] = true := by decide +kernel
theorem subd9_1_364 : subd9_1 [0, 0, -2] = true := by decide +kernel
theorem subd9_1_365 : subd9_1 [0, 0, -1] = true := by decide +kernel
theorem subd9_1_366 : subd9_1 [0, 0, 0] = true := by decide +kernel
theorem subd9_1_367 : subd9_1 [0, 0, 1] = true := by decide +kernel
theorem subd9_1_368 : subd9_1 [0, 0, 2] = true := by decide +kernel
theorem subd9_1_369 : subd9_1 [0, 0, 3] = true := by decide +kernel
theorem subd9_1_370 : subd9_1 [0, 0, 4] = true := by decide +kernel
theorem subd9_1_371 : subd9_1 [0, 0, 5] = true := by decide +kernel
theorem subd9_1_372 : subd9_1 [0, 0, 6] = true := by decide +kernel
theorem subd9_1_373 : subd9_1 [0, 0, 7] = true := by decide +kernel
theorem subd9_1_374 : subd9_1 [0, 1, -8] = true := by decide +kernel
theorem subd9_1_375 : subd9_1 [0, 1, -7] = true := by decide +kernel
theorem subd9_1_376 : subd9_1 [0, 1, -6] = true := by decide +kernel
theorem subd9_1_377 : subd9_1 [0, 1, -5] = true := by decide +kernel
theorem subd9_1_378 : subd9_1 [0, 1, -4] = true := by decide +kernel
theorem subd9_1_379 : subd9_1 [0, 1, -3] = true := by decide +kernel
theorem subd9_1_380 : subd9_1 [0, 1, -2] = true := by decide +kernel
theorem subd9_1_381 : subd9_1 [0, 1, -1] = true := by decide +kernel
theorem subd9_1_382 : subd9_1 [0, 1, 0] = true := by decide +kernel
theorem subd9_1_383 : subd9_1 [0, 1, 1] = true := by decide +kernel
theorem sbd9_1_11 : ∀ q ∈ blkd9_1_11, subd9_1 q = true := by
  unfold blkd9_1_11
  exact List.forall_mem_cons.2 ⟨subd9_1_352, List.forall_mem_cons.2 ⟨subd9_1_353, List.forall_mem_cons.2 ⟨subd9_1_354, List.forall_mem_cons.2 ⟨subd9_1_355, List.forall_mem_cons.2 ⟨subd9_1_356, List.forall_mem_cons.2 ⟨subd9_1_357, List.forall_mem_cons.2 ⟨subd9_1_358, List.forall_mem_cons.2 ⟨subd9_1_359, List.forall_mem_cons.2 ⟨subd9_1_360, List.forall_mem_cons.2 ⟨subd9_1_361, List.forall_mem_cons.2 ⟨subd9_1_362, List.forall_mem_cons.2 ⟨subd9_1_363, List.forall_mem_cons.2 ⟨subd9_1_364, List.forall_mem_cons.2 ⟨subd9_1_365, List.forall_mem_cons.2 ⟨subd9_1_366, List.forall_mem_cons.2 ⟨subd9_1_367, List.forall_mem_cons.2 ⟨subd9_1_368, List.forall_mem_cons.2 ⟨subd9_1_369, List.forall_mem_cons.2 ⟨subd9_1_370, List.forall_mem_cons.2 ⟨subd9_1_371, List.forall_mem_cons.2 ⟨subd9_1_372, List.forall_mem_cons.2 ⟨subd9_1_373, List.forall_mem_cons.2 ⟨subd9_1_374, List.forall_mem_cons.2 ⟨subd9_1_375, List.forall_mem_cons.2 ⟨subd9_1_376, List.forall_mem_cons.2 ⟨subd9_1_377, List.forall_mem_cons.2 ⟨subd9_1_378, List.forall_mem_cons.2 ⟨subd9_1_379, List.forall_mem_cons.2 ⟨subd9_1_380, List.forall_mem_cons.2 ⟨subd9_1_381, List.forall_mem_cons.2 ⟨subd9_1_382, List.forall_mem_cons.2 ⟨subd9_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_384 : subd9_1 [0, 1, 2] = true := by decide +kernel
theorem subd9_1_385 : subd9_1 [0, 1, 3] = true := by decide +kernel
theorem subd9_1_386 : subd9_1 [0, 1, 4] = true := by decide +kernel
theorem subd9_1_387 : subd9_1 [0, 1, 5] = true := by decide +kernel
theorem subd9_1_388 : subd9_1 [0, 1, 6] = true := by decide +kernel
theorem subd9_1_389 : subd9_1 [0, 2, -8] = true := by decide +kernel
theorem subd9_1_390 : subd9_1 [0, 2, -7] = true := by decide +kernel
theorem subd9_1_391 : subd9_1 [0, 2, -6] = true := by decide +kernel
theorem subd9_1_392 : subd9_1 [0, 2, -5] = true := by decide +kernel
theorem subd9_1_393 : subd9_1 [0, 2, -4] = true := by decide +kernel
theorem subd9_1_394 : subd9_1 [0, 2, -3] = true := by decide +kernel
theorem subd9_1_395 : subd9_1 [0, 2, -2] = true := by decide +kernel
theorem subd9_1_396 : subd9_1 [0, 2, -1] = true := by decide +kernel
theorem subd9_1_397 : subd9_1 [0, 2, 0] = true := by decide +kernel
theorem subd9_1_398 : subd9_1 [0, 2, 1] = true := by decide +kernel
theorem subd9_1_399 : subd9_1 [0, 2, 2] = true := by decide +kernel
theorem subd9_1_400 : subd9_1 [0, 2, 3] = true := by decide +kernel
theorem subd9_1_401 : subd9_1 [0, 2, 4] = true := by decide +kernel
theorem subd9_1_402 : subd9_1 [0, 2, 5] = true := by decide +kernel
theorem subd9_1_403 : subd9_1 [0, 2, 6] = true := by decide +kernel
theorem subd9_1_404 : subd9_1 [0, 3, -8] = true := by decide +kernel
theorem subd9_1_405 : subd9_1 [0, 3, -7] = true := by decide +kernel
theorem subd9_1_406 : subd9_1 [0, 3, -6] = true := by decide +kernel
theorem subd9_1_407 : subd9_1 [0, 3, -5] = true := by decide +kernel
theorem subd9_1_408 : subd9_1 [0, 3, -4] = true := by decide +kernel
theorem subd9_1_409 : subd9_1 [0, 3, -3] = true := by decide +kernel
theorem subd9_1_410 : subd9_1 [0, 3, -2] = true := by decide +kernel
theorem subd9_1_411 : subd9_1 [0, 3, -1] = true := by decide +kernel
theorem subd9_1_412 : subd9_1 [0, 3, 0] = true := by decide +kernel
theorem subd9_1_413 : subd9_1 [0, 3, 1] = true := by decide +kernel
theorem subd9_1_414 : subd9_1 [0, 3, 2] = true := by decide +kernel
theorem subd9_1_415 : subd9_1 [0, 3, 3] = true := by decide +kernel
theorem sbd9_1_12 : ∀ q ∈ blkd9_1_12, subd9_1 q = true := by
  unfold blkd9_1_12
  exact List.forall_mem_cons.2 ⟨subd9_1_384, List.forall_mem_cons.2 ⟨subd9_1_385, List.forall_mem_cons.2 ⟨subd9_1_386, List.forall_mem_cons.2 ⟨subd9_1_387, List.forall_mem_cons.2 ⟨subd9_1_388, List.forall_mem_cons.2 ⟨subd9_1_389, List.forall_mem_cons.2 ⟨subd9_1_390, List.forall_mem_cons.2 ⟨subd9_1_391, List.forall_mem_cons.2 ⟨subd9_1_392, List.forall_mem_cons.2 ⟨subd9_1_393, List.forall_mem_cons.2 ⟨subd9_1_394, List.forall_mem_cons.2 ⟨subd9_1_395, List.forall_mem_cons.2 ⟨subd9_1_396, List.forall_mem_cons.2 ⟨subd9_1_397, List.forall_mem_cons.2 ⟨subd9_1_398, List.forall_mem_cons.2 ⟨subd9_1_399, List.forall_mem_cons.2 ⟨subd9_1_400, List.forall_mem_cons.2 ⟨subd9_1_401, List.forall_mem_cons.2 ⟨subd9_1_402, List.forall_mem_cons.2 ⟨subd9_1_403, List.forall_mem_cons.2 ⟨subd9_1_404, List.forall_mem_cons.2 ⟨subd9_1_405, List.forall_mem_cons.2 ⟨subd9_1_406, List.forall_mem_cons.2 ⟨subd9_1_407, List.forall_mem_cons.2 ⟨subd9_1_408, List.forall_mem_cons.2 ⟨subd9_1_409, List.forall_mem_cons.2 ⟨subd9_1_410, List.forall_mem_cons.2 ⟨subd9_1_411, List.forall_mem_cons.2 ⟨subd9_1_412, List.forall_mem_cons.2 ⟨subd9_1_413, List.forall_mem_cons.2 ⟨subd9_1_414, List.forall_mem_cons.2 ⟨subd9_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_416 : subd9_1 [0, 3, 4] = true := by decide +kernel
theorem subd9_1_417 : subd9_1 [0, 3, 5] = true := by decide +kernel
theorem subd9_1_418 : subd9_1 [0, 4] = true := by decide +kernel
theorem subd9_1_419 : subd9_1 [0, 5] = true := by decide +kernel
theorem subd9_1_420 : subd9_1 [0, 6] = true := by decide +kernel
theorem subd9_1_421 : subd9_1 [0, 7] = true := by decide +kernel
theorem subd9_1_422 : subd9_1 [1, -8] = true := by decide +kernel
theorem subd9_1_423 : subd9_1 [1, -7] = true := by decide +kernel
theorem subd9_1_424 : subd9_1 [1, -6] = true := by decide +kernel
theorem subd9_1_425 : subd9_1 [1, -5] = true := by decide +kernel
theorem subd9_1_426 : subd9_1 [1, -4] = true := by decide +kernel
theorem subd9_1_427 : subd9_1 [1, -3, -6] = true := by decide +kernel
theorem subd9_1_428 : subd9_1 [1, -3, -5] = true := by decide +kernel
theorem subd9_1_429 : subd9_1 [1, -3, -4] = true := by decide +kernel
theorem subd9_1_430 : subd9_1 [1, -3, -3] = true := by decide +kernel
theorem subd9_1_431 : subd9_1 [1, -3, -2] = true := by decide +kernel
theorem subd9_1_432 : subd9_1 [1, -3, -1] = true := by decide +kernel
theorem subd9_1_433 : subd9_1 [1, -3, 0] = true := by decide +kernel
theorem subd9_1_434 : subd9_1 [1, -3, 1] = true := by decide +kernel
theorem subd9_1_435 : subd9_1 [1, -3, 2] = true := by decide +kernel
theorem subd9_1_436 : subd9_1 [1, -3, 3] = true := by decide +kernel
theorem subd9_1_437 : subd9_1 [1, -3, 4] = true := by decide +kernel
theorem subd9_1_438 : subd9_1 [1, -3, 5] = true := by decide +kernel
theorem subd9_1_439 : subd9_1 [1, -3, 6] = true := by decide +kernel
theorem subd9_1_440 : subd9_1 [1, -3, 7] = true := by decide +kernel
theorem subd9_1_441 : subd9_1 [1, -2, -7] = true := by decide +kernel
theorem subd9_1_442 : subd9_1 [1, -2, -6] = true := by decide +kernel
theorem subd9_1_443 : subd9_1 [1, -2, -5] = true := by decide +kernel
theorem subd9_1_444 : subd9_1 [1, -2, -4] = true := by decide +kernel
theorem subd9_1_445 : subd9_1 [1, -2, -3] = true := by decide +kernel
theorem subd9_1_446 : subd9_1 [1, -2, -2] = true := by decide +kernel
theorem subd9_1_447 : subd9_1 [1, -2, -1] = true := by decide +kernel
theorem sbd9_1_13 : ∀ q ∈ blkd9_1_13, subd9_1 q = true := by
  unfold blkd9_1_13
  exact List.forall_mem_cons.2 ⟨subd9_1_416, List.forall_mem_cons.2 ⟨subd9_1_417, List.forall_mem_cons.2 ⟨subd9_1_418, List.forall_mem_cons.2 ⟨subd9_1_419, List.forall_mem_cons.2 ⟨subd9_1_420, List.forall_mem_cons.2 ⟨subd9_1_421, List.forall_mem_cons.2 ⟨subd9_1_422, List.forall_mem_cons.2 ⟨subd9_1_423, List.forall_mem_cons.2 ⟨subd9_1_424, List.forall_mem_cons.2 ⟨subd9_1_425, List.forall_mem_cons.2 ⟨subd9_1_426, List.forall_mem_cons.2 ⟨subd9_1_427, List.forall_mem_cons.2 ⟨subd9_1_428, List.forall_mem_cons.2 ⟨subd9_1_429, List.forall_mem_cons.2 ⟨subd9_1_430, List.forall_mem_cons.2 ⟨subd9_1_431, List.forall_mem_cons.2 ⟨subd9_1_432, List.forall_mem_cons.2 ⟨subd9_1_433, List.forall_mem_cons.2 ⟨subd9_1_434, List.forall_mem_cons.2 ⟨subd9_1_435, List.forall_mem_cons.2 ⟨subd9_1_436, List.forall_mem_cons.2 ⟨subd9_1_437, List.forall_mem_cons.2 ⟨subd9_1_438, List.forall_mem_cons.2 ⟨subd9_1_439, List.forall_mem_cons.2 ⟨subd9_1_440, List.forall_mem_cons.2 ⟨subd9_1_441, List.forall_mem_cons.2 ⟨subd9_1_442, List.forall_mem_cons.2 ⟨subd9_1_443, List.forall_mem_cons.2 ⟨subd9_1_444, List.forall_mem_cons.2 ⟨subd9_1_445, List.forall_mem_cons.2 ⟨subd9_1_446, List.forall_mem_cons.2 ⟨subd9_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_448 : subd9_1 [1, -2, 0] = true := by decide +kernel
theorem subd9_1_449 : subd9_1 [1, -2, 1] = true := by decide +kernel
theorem subd9_1_450 : subd9_1 [1, -2, 2] = true := by decide +kernel
theorem subd9_1_451 : subd9_1 [1, -2, 3] = true := by decide +kernel
theorem subd9_1_452 : subd9_1 [1, -2, 4] = true := by decide +kernel
theorem subd9_1_453 : subd9_1 [1, -2, 5] = true := by decide +kernel
theorem subd9_1_454 : subd9_1 [1, -2, 6] = true := by decide +kernel
theorem subd9_1_455 : subd9_1 [1, -2, 7] = true := by decide +kernel
theorem subd9_1_456 : subd9_1 [1, -1, -7] = true := by decide +kernel
theorem subd9_1_457 : subd9_1 [1, -1, -6] = true := by decide +kernel
theorem subd9_1_458 : subd9_1 [1, -1, -5] = true := by decide +kernel
theorem subd9_1_459 : subd9_1 [1, -1, -4] = true := by decide +kernel
theorem subd9_1_460 : subd9_1 [1, -1, -3] = true := by decide +kernel
theorem subd9_1_461 : subd9_1 [1, -1, -2] = true := by decide +kernel
theorem subd9_1_462 : subd9_1 [1, -1, -1] = true := by decide +kernel
theorem subd9_1_463 : subd9_1 [1, -1, 0] = true := by decide +kernel
theorem subd9_1_464 : subd9_1 [1, -1, 1] = true := by decide +kernel
theorem subd9_1_465 : subd9_1 [1, -1, 2] = true := by decide +kernel
theorem subd9_1_466 : subd9_1 [1, -1, 3] = true := by decide +kernel
theorem subd9_1_467 : subd9_1 [1, -1, 4] = true := by decide +kernel
theorem subd9_1_468 : subd9_1 [1, -1, 5] = true := by decide +kernel
theorem subd9_1_469 : subd9_1 [1, -1, 6] = true := by decide +kernel
theorem subd9_1_470 : subd9_1 [1, -1, 7] = true := by decide +kernel
theorem subd9_1_471 : subd9_1 [1, 0, -8] = true := by decide +kernel
theorem subd9_1_472 : subd9_1 [1, 0, -7] = true := by decide +kernel
theorem subd9_1_473 : subd9_1 [1, 0, -6] = true := by decide +kernel
theorem subd9_1_474 : subd9_1 [1, 0, -5] = true := by decide +kernel
theorem subd9_1_475 : subd9_1 [1, 0, -4] = true := by decide +kernel
theorem subd9_1_476 : subd9_1 [1, 0, -3] = true := by decide +kernel
theorem subd9_1_477 : subd9_1 [1, 0, -2] = true := by decide +kernel
theorem subd9_1_478 : subd9_1 [1, 0, -1] = true := by decide +kernel
theorem subd9_1_479 : subd9_1 [1, 0, 0] = true := by decide +kernel
theorem sbd9_1_14 : ∀ q ∈ blkd9_1_14, subd9_1 q = true := by
  unfold blkd9_1_14
  exact List.forall_mem_cons.2 ⟨subd9_1_448, List.forall_mem_cons.2 ⟨subd9_1_449, List.forall_mem_cons.2 ⟨subd9_1_450, List.forall_mem_cons.2 ⟨subd9_1_451, List.forall_mem_cons.2 ⟨subd9_1_452, List.forall_mem_cons.2 ⟨subd9_1_453, List.forall_mem_cons.2 ⟨subd9_1_454, List.forall_mem_cons.2 ⟨subd9_1_455, List.forall_mem_cons.2 ⟨subd9_1_456, List.forall_mem_cons.2 ⟨subd9_1_457, List.forall_mem_cons.2 ⟨subd9_1_458, List.forall_mem_cons.2 ⟨subd9_1_459, List.forall_mem_cons.2 ⟨subd9_1_460, List.forall_mem_cons.2 ⟨subd9_1_461, List.forall_mem_cons.2 ⟨subd9_1_462, List.forall_mem_cons.2 ⟨subd9_1_463, List.forall_mem_cons.2 ⟨subd9_1_464, List.forall_mem_cons.2 ⟨subd9_1_465, List.forall_mem_cons.2 ⟨subd9_1_466, List.forall_mem_cons.2 ⟨subd9_1_467, List.forall_mem_cons.2 ⟨subd9_1_468, List.forall_mem_cons.2 ⟨subd9_1_469, List.forall_mem_cons.2 ⟨subd9_1_470, List.forall_mem_cons.2 ⟨subd9_1_471, List.forall_mem_cons.2 ⟨subd9_1_472, List.forall_mem_cons.2 ⟨subd9_1_473, List.forall_mem_cons.2 ⟨subd9_1_474, List.forall_mem_cons.2 ⟨subd9_1_475, List.forall_mem_cons.2 ⟨subd9_1_476, List.forall_mem_cons.2 ⟨subd9_1_477, List.forall_mem_cons.2 ⟨subd9_1_478, List.forall_mem_cons.2 ⟨subd9_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_480 : subd9_1 [1, 0, 1] = true := by decide +kernel
theorem subd9_1_481 : subd9_1 [1, 0, 2] = true := by decide +kernel
theorem subd9_1_482 : subd9_1 [1, 0, 3] = true := by decide +kernel
theorem subd9_1_483 : subd9_1 [1, 0, 4] = true := by decide +kernel
theorem subd9_1_484 : subd9_1 [1, 0, 5] = true := by decide +kernel
theorem subd9_1_485 : subd9_1 [1, 0, 6] = true := by decide +kernel
theorem subd9_1_486 : subd9_1 [1, 0, 7] = true := by decide +kernel
theorem subd9_1_487 : subd9_1 [1, 1, -8] = true := by decide +kernel
theorem subd9_1_488 : subd9_1 [1, 1, -7] = true := by decide +kernel
theorem subd9_1_489 : subd9_1 [1, 1, -6] = true := by decide +kernel
theorem subd9_1_490 : subd9_1 [1, 1, -5] = true := by decide +kernel
theorem subd9_1_491 : subd9_1 [1, 1, -4] = true := by decide +kernel
theorem subd9_1_492 : subd9_1 [1, 1, -3] = true := by decide +kernel
theorem subd9_1_493 : subd9_1 [1, 1, -2] = true := by decide +kernel
theorem subd9_1_494 : subd9_1 [1, 1, -1] = true := by decide +kernel
theorem subd9_1_495 : subd9_1 [1, 1, 0] = true := by decide +kernel
theorem subd9_1_496 : subd9_1 [1, 1, 1] = true := by decide +kernel
theorem subd9_1_497 : subd9_1 [1, 1, 2] = true := by decide +kernel
theorem subd9_1_498 : subd9_1 [1, 1, 3] = true := by decide +kernel
theorem subd9_1_499 : subd9_1 [1, 1, 4] = true := by decide +kernel
theorem subd9_1_500 : subd9_1 [1, 1, 5] = true := by decide +kernel
theorem subd9_1_501 : subd9_1 [1, 1, 6] = true := by decide +kernel
theorem subd9_1_502 : subd9_1 [1, 2, -8] = true := by decide +kernel
theorem subd9_1_503 : subd9_1 [1, 2, -7] = true := by decide +kernel
theorem subd9_1_504 : subd9_1 [1, 2, -6] = true := by decide +kernel
theorem subd9_1_505 : subd9_1 [1, 2, -5] = true := by decide +kernel
theorem subd9_1_506 : subd9_1 [1, 2, -4] = true := by decide +kernel
theorem subd9_1_507 : subd9_1 [1, 2, -3] = true := by decide +kernel
theorem subd9_1_508 : subd9_1 [1, 2, -2] = true := by decide +kernel
theorem subd9_1_509 : subd9_1 [1, 2, -1] = true := by decide +kernel
theorem subd9_1_510 : subd9_1 [1, 2, 0] = true := by decide +kernel
theorem subd9_1_511 : subd9_1 [1, 2, 1] = true := by decide +kernel
theorem sbd9_1_15 : ∀ q ∈ blkd9_1_15, subd9_1 q = true := by
  unfold blkd9_1_15
  exact List.forall_mem_cons.2 ⟨subd9_1_480, List.forall_mem_cons.2 ⟨subd9_1_481, List.forall_mem_cons.2 ⟨subd9_1_482, List.forall_mem_cons.2 ⟨subd9_1_483, List.forall_mem_cons.2 ⟨subd9_1_484, List.forall_mem_cons.2 ⟨subd9_1_485, List.forall_mem_cons.2 ⟨subd9_1_486, List.forall_mem_cons.2 ⟨subd9_1_487, List.forall_mem_cons.2 ⟨subd9_1_488, List.forall_mem_cons.2 ⟨subd9_1_489, List.forall_mem_cons.2 ⟨subd9_1_490, List.forall_mem_cons.2 ⟨subd9_1_491, List.forall_mem_cons.2 ⟨subd9_1_492, List.forall_mem_cons.2 ⟨subd9_1_493, List.forall_mem_cons.2 ⟨subd9_1_494, List.forall_mem_cons.2 ⟨subd9_1_495, List.forall_mem_cons.2 ⟨subd9_1_496, List.forall_mem_cons.2 ⟨subd9_1_497, List.forall_mem_cons.2 ⟨subd9_1_498, List.forall_mem_cons.2 ⟨subd9_1_499, List.forall_mem_cons.2 ⟨subd9_1_500, List.forall_mem_cons.2 ⟨subd9_1_501, List.forall_mem_cons.2 ⟨subd9_1_502, List.forall_mem_cons.2 ⟨subd9_1_503, List.forall_mem_cons.2 ⟨subd9_1_504, List.forall_mem_cons.2 ⟨subd9_1_505, List.forall_mem_cons.2 ⟨subd9_1_506, List.forall_mem_cons.2 ⟨subd9_1_507, List.forall_mem_cons.2 ⟨subd9_1_508, List.forall_mem_cons.2 ⟨subd9_1_509, List.forall_mem_cons.2 ⟨subd9_1_510, List.forall_mem_cons.2 ⟨subd9_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
