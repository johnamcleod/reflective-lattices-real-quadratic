import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_0_64 : subd14_0 [-1, -1, -4] = true := by decide +kernel
theorem subd14_0_65 : subd14_0 [-1, -1, -3] = true := by decide +kernel
theorem subd14_0_66 : subd14_0 [-1, -1, -2] = true := by decide +kernel
theorem subd14_0_67 : subd14_0 [-1, -1, -1] = true := by decide +kernel
theorem subd14_0_68 : subd14_0 [-1, -1, 0] = true := by decide +kernel
theorem subd14_0_69 : subd14_0 [-1, -1, 1] = true := by decide +kernel
theorem subd14_0_70 : subd14_0 [-1, -1, 2] = true := by decide +kernel
theorem subd14_0_71 : subd14_0 [-1, -1, 3] = true := by decide +kernel
theorem subd14_0_72 : subd14_0 [-1, -1, 4] = true := by decide +kernel
theorem subd14_0_73 : subd14_0 [-1, -1, 5] = true := by decide +kernel
theorem subd14_0_74 : subd14_0 [-1, -1, 6] = true := by decide +kernel
theorem subd14_0_75 : subd14_0 [-1, 0, -7] = true := by decide +kernel
theorem subd14_0_76 : subd14_0 [-1, 0, -6] = true := by decide +kernel
theorem subd14_0_77 : subd14_0 [-1, 0, -5] = true := by decide +kernel
theorem subd14_0_78 : subd14_0 [-1, 0, -4] = true := by decide +kernel
theorem subd14_0_79 : subd14_0 [-1, 0, -3] = true := by decide +kernel
theorem subd14_0_80 : subd14_0 [-1, 0, -2] = true := by decide +kernel
theorem subd14_0_81 : subd14_0 [-1, 0, -1] = true := by decide +kernel
theorem subd14_0_82 : subd14_0 [-1, 0, 0] = true := by decide +kernel
theorem subd14_0_83 : subd14_0 [-1, 0, 1] = true := by decide +kernel
theorem subd14_0_84 : subd14_0 [-1, 0, 2] = true := by decide +kernel
theorem subd14_0_85 : subd14_0 [-1, 0, 3] = true := by decide +kernel
theorem subd14_0_86 : subd14_0 [-1, 0, 4] = true := by decide +kernel
theorem subd14_0_87 : subd14_0 [-1, 0, 5] = true := by decide +kernel
theorem subd14_0_88 : subd14_0 [-1, 0, 6] = true := by decide +kernel
theorem subd14_0_89 : subd14_0 [-1, 1, -7] = true := by decide +kernel
theorem subd14_0_90 : subd14_0 [-1, 1, -6] = true := by decide +kernel
theorem subd14_0_91 : subd14_0 [-1, 1, -5] = true := by decide +kernel
theorem subd14_0_92 : subd14_0 [-1, 1, -4] = true := by decide +kernel
theorem subd14_0_93 : subd14_0 [-1, 1, -3] = true := by decide +kernel
theorem subd14_0_94 : subd14_0 [-1, 1, -2] = true := by decide +kernel
theorem subd14_0_95 : subd14_0 [-1, 1, -1] = true := by decide +kernel
theorem sbd14_0_2 : ∀ q ∈ blkd14_0_2, subd14_0 q = true := by
  unfold blkd14_0_2
  exact List.forall_mem_cons.2 ⟨subd14_0_64, List.forall_mem_cons.2 ⟨subd14_0_65, List.forall_mem_cons.2 ⟨subd14_0_66, List.forall_mem_cons.2 ⟨subd14_0_67, List.forall_mem_cons.2 ⟨subd14_0_68, List.forall_mem_cons.2 ⟨subd14_0_69, List.forall_mem_cons.2 ⟨subd14_0_70, List.forall_mem_cons.2 ⟨subd14_0_71, List.forall_mem_cons.2 ⟨subd14_0_72, List.forall_mem_cons.2 ⟨subd14_0_73, List.forall_mem_cons.2 ⟨subd14_0_74, List.forall_mem_cons.2 ⟨subd14_0_75, List.forall_mem_cons.2 ⟨subd14_0_76, List.forall_mem_cons.2 ⟨subd14_0_77, List.forall_mem_cons.2 ⟨subd14_0_78, List.forall_mem_cons.2 ⟨subd14_0_79, List.forall_mem_cons.2 ⟨subd14_0_80, List.forall_mem_cons.2 ⟨subd14_0_81, List.forall_mem_cons.2 ⟨subd14_0_82, List.forall_mem_cons.2 ⟨subd14_0_83, List.forall_mem_cons.2 ⟨subd14_0_84, List.forall_mem_cons.2 ⟨subd14_0_85, List.forall_mem_cons.2 ⟨subd14_0_86, List.forall_mem_cons.2 ⟨subd14_0_87, List.forall_mem_cons.2 ⟨subd14_0_88, List.forall_mem_cons.2 ⟨subd14_0_89, List.forall_mem_cons.2 ⟨subd14_0_90, List.forall_mem_cons.2 ⟨subd14_0_91, List.forall_mem_cons.2 ⟨subd14_0_92, List.forall_mem_cons.2 ⟨subd14_0_93, List.forall_mem_cons.2 ⟨subd14_0_94, List.forall_mem_cons.2 ⟨subd14_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_96 : subd14_0 [-1, 1, 0] = true := by decide +kernel
theorem subd14_0_97 : subd14_0 [-1, 1, 1] = true := by decide +kernel
theorem subd14_0_98 : subd14_0 [-1, 1, 2] = true := by decide +kernel
theorem subd14_0_99 : subd14_0 [-1, 1, 3] = true := by decide +kernel
theorem subd14_0_100 : subd14_0 [-1, 1, 4] = true := by decide +kernel
theorem subd14_0_101 : subd14_0 [-1, 1, 5] = true := by decide +kernel
theorem subd14_0_102 : subd14_0 [-1, 1, 6] = true := by decide +kernel
theorem subd14_0_103 : subd14_0 [-1, 2, -6] = true := by decide +kernel
theorem subd14_0_104 : subd14_0 [-1, 2, -5] = true := by decide +kernel
theorem subd14_0_105 : subd14_0 [-1, 2, -4] = true := by decide +kernel
theorem subd14_0_106 : subd14_0 [-1, 2, -3] = true := by decide +kernel
theorem subd14_0_107 : subd14_0 [-1, 2, -2] = true := by decide +kernel
theorem subd14_0_108 : subd14_0 [-1, 2, -1] = true := by decide +kernel
theorem subd14_0_109 : subd14_0 [-1, 2, 0] = true := by decide +kernel
theorem subd14_0_110 : subd14_0 [-1, 2, 1] = true := by decide +kernel
theorem subd14_0_111 : subd14_0 [-1, 2, 2] = true := by decide +kernel
theorem subd14_0_112 : subd14_0 [-1, 2, 3] = true := by decide +kernel
theorem subd14_0_113 : subd14_0 [-1, 2, 4] = true := by decide +kernel
theorem subd14_0_114 : subd14_0 [-1, 2, 5] = true := by decide +kernel
theorem subd14_0_115 : subd14_0 [-1, 2, 6] = true := by decide +kernel
theorem subd14_0_116 : subd14_0 [-1, 3] = true := by decide +kernel
theorem subd14_0_117 : subd14_0 [-1, 4] = true := by decide +kernel
theorem subd14_0_118 : subd14_0 [-1, 5] = true := by decide +kernel
theorem subd14_0_119 : subd14_0 [0, -6] = true := by decide +kernel
theorem subd14_0_120 : subd14_0 [0, -5] = true := by decide +kernel
theorem subd14_0_121 : subd14_0 [0, -4] = true := by decide +kernel
theorem subd14_0_122 : subd14_0 [0, -3] = true := by decide +kernel
theorem subd14_0_123 : subd14_0 [0, -2, -7] = true := by decide +kernel
theorem subd14_0_124 : subd14_0 [0, -2, -6] = true := by decide +kernel
theorem subd14_0_125 : subd14_0 [0, -2, -5] = true := by decide +kernel
theorem subd14_0_126 : subd14_0 [0, -2, -4] = true := by decide +kernel
theorem subd14_0_127 : subd14_0 [0, -2, -3] = true := by decide +kernel
theorem sbd14_0_3 : ∀ q ∈ blkd14_0_3, subd14_0 q = true := by
  unfold blkd14_0_3
  exact List.forall_mem_cons.2 ⟨subd14_0_96, List.forall_mem_cons.2 ⟨subd14_0_97, List.forall_mem_cons.2 ⟨subd14_0_98, List.forall_mem_cons.2 ⟨subd14_0_99, List.forall_mem_cons.2 ⟨subd14_0_100, List.forall_mem_cons.2 ⟨subd14_0_101, List.forall_mem_cons.2 ⟨subd14_0_102, List.forall_mem_cons.2 ⟨subd14_0_103, List.forall_mem_cons.2 ⟨subd14_0_104, List.forall_mem_cons.2 ⟨subd14_0_105, List.forall_mem_cons.2 ⟨subd14_0_106, List.forall_mem_cons.2 ⟨subd14_0_107, List.forall_mem_cons.2 ⟨subd14_0_108, List.forall_mem_cons.2 ⟨subd14_0_109, List.forall_mem_cons.2 ⟨subd14_0_110, List.forall_mem_cons.2 ⟨subd14_0_111, List.forall_mem_cons.2 ⟨subd14_0_112, List.forall_mem_cons.2 ⟨subd14_0_113, List.forall_mem_cons.2 ⟨subd14_0_114, List.forall_mem_cons.2 ⟨subd14_0_115, List.forall_mem_cons.2 ⟨subd14_0_116, List.forall_mem_cons.2 ⟨subd14_0_117, List.forall_mem_cons.2 ⟨subd14_0_118, List.forall_mem_cons.2 ⟨subd14_0_119, List.forall_mem_cons.2 ⟨subd14_0_120, List.forall_mem_cons.2 ⟨subd14_0_121, List.forall_mem_cons.2 ⟨subd14_0_122, List.forall_mem_cons.2 ⟨subd14_0_123, List.forall_mem_cons.2 ⟨subd14_0_124, List.forall_mem_cons.2 ⟨subd14_0_125, List.forall_mem_cons.2 ⟨subd14_0_126, List.forall_mem_cons.2 ⟨subd14_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_128 : subd14_0 [0, -2, -2] = true := by decide +kernel
theorem subd14_0_129 : subd14_0 [0, -2, -1] = true := by decide +kernel
theorem subd14_0_130 : subd14_0 [0, -2, 0] = true := by decide +kernel
theorem subd14_0_131 : subd14_0 [0, -2, 1] = true := by decide +kernel
theorem subd14_0_132 : subd14_0 [0, -2, 2] = true := by decide +kernel
theorem subd14_0_133 : subd14_0 [0, -2, 3] = true := by decide +kernel
theorem subd14_0_134 : subd14_0 [0, -2, 4] = true := by decide +kernel
theorem subd14_0_135 : subd14_0 [0, -2, 5] = true := by decide +kernel
theorem subd14_0_136 : subd14_0 [0, -1, -7] = true := by decide +kernel
theorem subd14_0_137 : subd14_0 [0, -1, -6] = true := by decide +kernel
theorem subd14_0_138 : subd14_0 [0, -1, -5] = true := by decide +kernel
theorem subd14_0_139 : subd14_0 [0, -1, -4] = true := by decide +kernel
theorem subd14_0_140 : subd14_0 [0, -1, -3] = true := by decide +kernel
theorem subd14_0_141 : subd14_0 [0, -1, -2] = true := by decide +kernel
theorem subd14_0_142 : subd14_0 [0, -1, -1] = true := by decide +kernel
theorem subd14_0_143 : subd14_0 [0, -1, 0] = true := by decide +kernel
theorem subd14_0_144 : subd14_0 [0, -1, 1] = true := by decide +kernel
theorem subd14_0_145 : subd14_0 [0, -1, 2] = true := by decide +kernel
theorem subd14_0_146 : subd14_0 [0, -1, 3] = true := by decide +kernel
theorem subd14_0_147 : subd14_0 [0, -1, 4] = true := by decide +kernel
theorem subd14_0_148 : subd14_0 [0, -1, 5] = true := by decide +kernel
theorem subd14_0_149 : subd14_0 [0, -1, 6] = true := by decide +kernel
theorem subd14_0_150 : subd14_0 [0, 0, -7] = true := by decide +kernel
theorem subd14_0_151 : subd14_0 [0, 0, -6] = true := by decide +kernel
theorem subd14_0_152 : subd14_0 [0, 0, -5] = true := by decide +kernel
theorem subd14_0_153 : subd14_0 [0, 0, -4] = true := by decide +kernel
theorem subd14_0_154 : subd14_0 [0, 0, -3] = true := by decide +kernel
theorem subd14_0_155 : subd14_0 [0, 0, -2] = true := by decide +kernel
theorem subd14_0_156 : subd14_0 [0, 0, -1] = true := by decide +kernel
theorem subd14_0_157 : subd14_0 [0, 0, 0] = true := by decide +kernel
theorem subd14_0_158 : subd14_0 [0, 0, 1] = true := by decide +kernel
theorem subd14_0_159 : subd14_0 [0, 0, 2] = true := by decide +kernel
theorem sbd14_0_4 : ∀ q ∈ blkd14_0_4, subd14_0 q = true := by
  unfold blkd14_0_4
  exact List.forall_mem_cons.2 ⟨subd14_0_128, List.forall_mem_cons.2 ⟨subd14_0_129, List.forall_mem_cons.2 ⟨subd14_0_130, List.forall_mem_cons.2 ⟨subd14_0_131, List.forall_mem_cons.2 ⟨subd14_0_132, List.forall_mem_cons.2 ⟨subd14_0_133, List.forall_mem_cons.2 ⟨subd14_0_134, List.forall_mem_cons.2 ⟨subd14_0_135, List.forall_mem_cons.2 ⟨subd14_0_136, List.forall_mem_cons.2 ⟨subd14_0_137, List.forall_mem_cons.2 ⟨subd14_0_138, List.forall_mem_cons.2 ⟨subd14_0_139, List.forall_mem_cons.2 ⟨subd14_0_140, List.forall_mem_cons.2 ⟨subd14_0_141, List.forall_mem_cons.2 ⟨subd14_0_142, List.forall_mem_cons.2 ⟨subd14_0_143, List.forall_mem_cons.2 ⟨subd14_0_144, List.forall_mem_cons.2 ⟨subd14_0_145, List.forall_mem_cons.2 ⟨subd14_0_146, List.forall_mem_cons.2 ⟨subd14_0_147, List.forall_mem_cons.2 ⟨subd14_0_148, List.forall_mem_cons.2 ⟨subd14_0_149, List.forall_mem_cons.2 ⟨subd14_0_150, List.forall_mem_cons.2 ⟨subd14_0_151, List.forall_mem_cons.2 ⟨subd14_0_152, List.forall_mem_cons.2 ⟨subd14_0_153, List.forall_mem_cons.2 ⟨subd14_0_154, List.forall_mem_cons.2 ⟨subd14_0_155, List.forall_mem_cons.2 ⟨subd14_0_156, List.forall_mem_cons.2 ⟨subd14_0_157, List.forall_mem_cons.2 ⟨subd14_0_158, List.forall_mem_cons.2 ⟨subd14_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_160 : subd14_0 [0, 0, 3] = true := by decide +kernel
theorem subd14_0_161 : subd14_0 [0, 0, 4] = true := by decide +kernel
theorem subd14_0_162 : subd14_0 [0, 0, 5] = true := by decide +kernel
theorem subd14_0_163 : subd14_0 [0, 0, 6] = true := by decide +kernel
theorem subd14_0_164 : subd14_0 [0, 1, -7] = true := by decide +kernel
theorem subd14_0_165 : subd14_0 [0, 1, -6] = true := by decide +kernel
theorem subd14_0_166 : subd14_0 [0, 1, -5] = true := by decide +kernel
theorem subd14_0_167 : subd14_0 [0, 1, -4] = true := by decide +kernel
theorem subd14_0_168 : subd14_0 [0, 1, -3] = true := by decide +kernel
theorem subd14_0_169 : subd14_0 [0, 1, -2] = true := by decide +kernel
theorem subd14_0_170 : subd14_0 [0, 1, -1] = true := by decide +kernel
theorem subd14_0_171 : subd14_0 [0, 1, 0] = true := by decide +kernel
theorem subd14_0_172 : subd14_0 [0, 1, 1] = true := by decide +kernel
theorem subd14_0_173 : subd14_0 [0, 1, 2] = true := by decide +kernel
theorem subd14_0_174 : subd14_0 [0, 1, 3] = true := by decide +kernel
theorem subd14_0_175 : subd14_0 [0, 1, 4] = true := by decide +kernel
theorem subd14_0_176 : subd14_0 [0, 1, 5] = true := by decide +kernel
theorem subd14_0_177 : subd14_0 [0, 1, 6] = true := by decide +kernel
theorem subd14_0_178 : subd14_0 [0, 2, -6] = true := by decide +kernel
theorem subd14_0_179 : subd14_0 [0, 2, -5] = true := by decide +kernel
theorem subd14_0_180 : subd14_0 [0, 2, -4] = true := by decide +kernel
theorem subd14_0_181 : subd14_0 [0, 2, -3] = true := by decide +kernel
theorem subd14_0_182 : subd14_0 [0, 2, -2] = true := by decide +kernel
theorem subd14_0_183 : subd14_0 [0, 2, -1] = true := by decide +kernel
theorem subd14_0_184 : subd14_0 [0, 2, 0] = true := by decide +kernel
theorem subd14_0_185 : subd14_0 [0, 2, 1] = true := by decide +kernel
theorem subd14_0_186 : subd14_0 [0, 2, 2] = true := by decide +kernel
theorem subd14_0_187 : subd14_0 [0, 2, 3] = true := by decide +kernel
theorem subd14_0_188 : subd14_0 [0, 2, 4] = true := by decide +kernel
theorem subd14_0_189 : subd14_0 [0, 2, 5] = true := by decide +kernel
theorem subd14_0_190 : subd14_0 [0, 2, 6] = true := by decide +kernel
theorem subd14_0_191 : subd14_0 [0, 3] = true := by decide +kernel
theorem sbd14_0_5 : ∀ q ∈ blkd14_0_5, subd14_0 q = true := by
  unfold blkd14_0_5
  exact List.forall_mem_cons.2 ⟨subd14_0_160, List.forall_mem_cons.2 ⟨subd14_0_161, List.forall_mem_cons.2 ⟨subd14_0_162, List.forall_mem_cons.2 ⟨subd14_0_163, List.forall_mem_cons.2 ⟨subd14_0_164, List.forall_mem_cons.2 ⟨subd14_0_165, List.forall_mem_cons.2 ⟨subd14_0_166, List.forall_mem_cons.2 ⟨subd14_0_167, List.forall_mem_cons.2 ⟨subd14_0_168, List.forall_mem_cons.2 ⟨subd14_0_169, List.forall_mem_cons.2 ⟨subd14_0_170, List.forall_mem_cons.2 ⟨subd14_0_171, List.forall_mem_cons.2 ⟨subd14_0_172, List.forall_mem_cons.2 ⟨subd14_0_173, List.forall_mem_cons.2 ⟨subd14_0_174, List.forall_mem_cons.2 ⟨subd14_0_175, List.forall_mem_cons.2 ⟨subd14_0_176, List.forall_mem_cons.2 ⟨subd14_0_177, List.forall_mem_cons.2 ⟨subd14_0_178, List.forall_mem_cons.2 ⟨subd14_0_179, List.forall_mem_cons.2 ⟨subd14_0_180, List.forall_mem_cons.2 ⟨subd14_0_181, List.forall_mem_cons.2 ⟨subd14_0_182, List.forall_mem_cons.2 ⟨subd14_0_183, List.forall_mem_cons.2 ⟨subd14_0_184, List.forall_mem_cons.2 ⟨subd14_0_185, List.forall_mem_cons.2 ⟨subd14_0_186, List.forall_mem_cons.2 ⟨subd14_0_187, List.forall_mem_cons.2 ⟨subd14_0_188, List.forall_mem_cons.2 ⟨subd14_0_189, List.forall_mem_cons.2 ⟨subd14_0_190, List.forall_mem_cons.2 ⟨subd14_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_192 : subd14_0 [0, 4] = true := by decide +kernel
theorem subd14_0_193 : subd14_0 [0, 5] = true := by decide +kernel
theorem subd14_0_194 : subd14_0 [1, -6] = true := by decide +kernel
theorem subd14_0_195 : subd14_0 [1, -5] = true := by decide +kernel
theorem subd14_0_196 : subd14_0 [1, -4] = true := by decide +kernel
theorem subd14_0_197 : subd14_0 [1, -3] = true := by decide +kernel
theorem subd14_0_198 : subd14_0 [1, -2, -7] = true := by decide +kernel
theorem subd14_0_199 : subd14_0 [1, -2, -6] = true := by decide +kernel
theorem subd14_0_200 : subd14_0 [1, -2, -5] = true := by decide +kernel
theorem subd14_0_201 : subd14_0 [1, -2, -4] = true := by decide +kernel
theorem subd14_0_202 : subd14_0 [1, -2, -3] = true := by decide +kernel
theorem subd14_0_203 : subd14_0 [1, -2, -2] = true := by decide +kernel
theorem subd14_0_204 : subd14_0 [1, -2, -1] = true := by decide +kernel
theorem subd14_0_205 : subd14_0 [1, -2, 0] = true := by decide +kernel
theorem subd14_0_206 : subd14_0 [1, -2, 1] = true := by decide +kernel
theorem subd14_0_207 : subd14_0 [1, -2, 2] = true := by decide +kernel
theorem subd14_0_208 : subd14_0 [1, -2, 3] = true := by decide +kernel
theorem subd14_0_209 : subd14_0 [1, -2, 4] = true := by decide +kernel
theorem subd14_0_210 : subd14_0 [1, -2, 5] = true := by decide +kernel
theorem subd14_0_211 : subd14_0 [1, -1, -7] = true := by decide +kernel
theorem subd14_0_212 : subd14_0 [1, -1, -6] = true := by decide +kernel
theorem subd14_0_213 : subd14_0 [1, -1, -5] = true := by decide +kernel
theorem subd14_0_214 : subd14_0 [1, -1, -4] = true := by decide +kernel
theorem subd14_0_215 : subd14_0 [1, -1, -3] = true := by decide +kernel
theorem subd14_0_216 : subd14_0 [1, -1, -2] = true := by decide +kernel
theorem subd14_0_217 : subd14_0 [1, -1, -1] = true := by decide +kernel
theorem subd14_0_218 : subd14_0 [1, -1, 0] = true := by decide +kernel
theorem subd14_0_219 : subd14_0 [1, -1, 1] = true := by decide +kernel
theorem subd14_0_220 : subd14_0 [1, -1, 2] = true := by decide +kernel
theorem subd14_0_221 : subd14_0 [1, -1, 3] = true := by decide +kernel
theorem subd14_0_222 : subd14_0 [1, -1, 4] = true := by decide +kernel
theorem subd14_0_223 : subd14_0 [1, -1, 5] = true := by decide +kernel
theorem sbd14_0_6 : ∀ q ∈ blkd14_0_6, subd14_0 q = true := by
  unfold blkd14_0_6
  exact List.forall_mem_cons.2 ⟨subd14_0_192, List.forall_mem_cons.2 ⟨subd14_0_193, List.forall_mem_cons.2 ⟨subd14_0_194, List.forall_mem_cons.2 ⟨subd14_0_195, List.forall_mem_cons.2 ⟨subd14_0_196, List.forall_mem_cons.2 ⟨subd14_0_197, List.forall_mem_cons.2 ⟨subd14_0_198, List.forall_mem_cons.2 ⟨subd14_0_199, List.forall_mem_cons.2 ⟨subd14_0_200, List.forall_mem_cons.2 ⟨subd14_0_201, List.forall_mem_cons.2 ⟨subd14_0_202, List.forall_mem_cons.2 ⟨subd14_0_203, List.forall_mem_cons.2 ⟨subd14_0_204, List.forall_mem_cons.2 ⟨subd14_0_205, List.forall_mem_cons.2 ⟨subd14_0_206, List.forall_mem_cons.2 ⟨subd14_0_207, List.forall_mem_cons.2 ⟨subd14_0_208, List.forall_mem_cons.2 ⟨subd14_0_209, List.forall_mem_cons.2 ⟨subd14_0_210, List.forall_mem_cons.2 ⟨subd14_0_211, List.forall_mem_cons.2 ⟨subd14_0_212, List.forall_mem_cons.2 ⟨subd14_0_213, List.forall_mem_cons.2 ⟨subd14_0_214, List.forall_mem_cons.2 ⟨subd14_0_215, List.forall_mem_cons.2 ⟨subd14_0_216, List.forall_mem_cons.2 ⟨subd14_0_217, List.forall_mem_cons.2 ⟨subd14_0_218, List.forall_mem_cons.2 ⟨subd14_0_219, List.forall_mem_cons.2 ⟨subd14_0_220, List.forall_mem_cons.2 ⟨subd14_0_221, List.forall_mem_cons.2 ⟨subd14_0_222, List.forall_mem_cons.2 ⟨subd14_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_224 : subd14_0 [1, -1, 6] = true := by decide +kernel
theorem subd14_0_225 : subd14_0 [1, 0, -7] = true := by decide +kernel
theorem subd14_0_226 : subd14_0 [1, 0, -6] = true := by decide +kernel
theorem subd14_0_227 : subd14_0 [1, 0, -5] = true := by decide +kernel
theorem subd14_0_228 : subd14_0 [1, 0, -4] = true := by decide +kernel
theorem subd14_0_229 : subd14_0 [1, 0, -3] = true := by decide +kernel
theorem subd14_0_230 : subd14_0 [1, 0, -2] = true := by decide +kernel
theorem subd14_0_231 : subd14_0 [1, 0, -1] = true := by decide +kernel
theorem subd14_0_232 : subd14_0 [1, 0, 0] = true := by decide +kernel
theorem subd14_0_233 : subd14_0 [1, 0, 1] = true := by decide +kernel
theorem subd14_0_234 : subd14_0 [1, 0, 2] = true := by decide +kernel
theorem subd14_0_235 : subd14_0 [1, 0, 3] = true := by decide +kernel
theorem subd14_0_236 : subd14_0 [1, 0, 4] = true := by decide +kernel
theorem subd14_0_237 : subd14_0 [1, 0, 5] = true := by decide +kernel
theorem subd14_0_238 : subd14_0 [1, 0, 6] = true := by decide +kernel
theorem subd14_0_239 : subd14_0 [1, 1, -7] = true := by decide +kernel
theorem subd14_0_240 : subd14_0 [1, 1, -6] = true := by decide +kernel
theorem subd14_0_241 : subd14_0 [1, 1, -5] = true := by decide +kernel
theorem subd14_0_242 : subd14_0 [1, 1, -4] = true := by decide +kernel
theorem subd14_0_243 : subd14_0 [1, 1, -3] = true := by decide +kernel
theorem subd14_0_244 : subd14_0 [1, 1, -2] = true := by decide +kernel
theorem subd14_0_245 : subd14_0 [1, 1, -1] = true := by decide +kernel
theorem subd14_0_246 : subd14_0 [1, 1, 0] = true := by decide +kernel
theorem subd14_0_247 : subd14_0 [1, 1, 1] = true := by decide +kernel
theorem subd14_0_248 : subd14_0 [1, 1, 2] = true := by decide +kernel
theorem subd14_0_249 : subd14_0 [1, 1, 3] = true := by decide +kernel
theorem subd14_0_250 : subd14_0 [1, 1, 4] = true := by decide +kernel
theorem subd14_0_251 : subd14_0 [1, 1, 5] = true := by decide +kernel
theorem subd14_0_252 : subd14_0 [1, 1, 6] = true := by decide +kernel
theorem subd14_0_253 : subd14_0 [1, 2] = true := by decide +kernel
theorem subd14_0_254 : subd14_0 [1, 3] = true := by decide +kernel
theorem subd14_0_255 : subd14_0 [1, 4] = true := by decide +kernel
theorem sbd14_0_7 : ∀ q ∈ blkd14_0_7, subd14_0 q = true := by
  unfold blkd14_0_7
  exact List.forall_mem_cons.2 ⟨subd14_0_224, List.forall_mem_cons.2 ⟨subd14_0_225, List.forall_mem_cons.2 ⟨subd14_0_226, List.forall_mem_cons.2 ⟨subd14_0_227, List.forall_mem_cons.2 ⟨subd14_0_228, List.forall_mem_cons.2 ⟨subd14_0_229, List.forall_mem_cons.2 ⟨subd14_0_230, List.forall_mem_cons.2 ⟨subd14_0_231, List.forall_mem_cons.2 ⟨subd14_0_232, List.forall_mem_cons.2 ⟨subd14_0_233, List.forall_mem_cons.2 ⟨subd14_0_234, List.forall_mem_cons.2 ⟨subd14_0_235, List.forall_mem_cons.2 ⟨subd14_0_236, List.forall_mem_cons.2 ⟨subd14_0_237, List.forall_mem_cons.2 ⟨subd14_0_238, List.forall_mem_cons.2 ⟨subd14_0_239, List.forall_mem_cons.2 ⟨subd14_0_240, List.forall_mem_cons.2 ⟨subd14_0_241, List.forall_mem_cons.2 ⟨subd14_0_242, List.forall_mem_cons.2 ⟨subd14_0_243, List.forall_mem_cons.2 ⟨subd14_0_244, List.forall_mem_cons.2 ⟨subd14_0_245, List.forall_mem_cons.2 ⟨subd14_0_246, List.forall_mem_cons.2 ⟨subd14_0_247, List.forall_mem_cons.2 ⟨subd14_0_248, List.forall_mem_cons.2 ⟨subd14_0_249, List.forall_mem_cons.2 ⟨subd14_0_250, List.forall_mem_cons.2 ⟨subd14_0_251, List.forall_mem_cons.2 ⟨subd14_0_252, List.forall_mem_cons.2 ⟨subd14_0_253, List.forall_mem_cons.2 ⟨subd14_0_254, List.forall_mem_cons.2 ⟨subd14_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_256 : subd14_0 [1, 5] = true := by decide +kernel
theorem subd14_0_257 : subd14_0 [2, -6] = true := by decide +kernel
theorem subd14_0_258 : subd14_0 [2, -5] = true := by decide +kernel
theorem subd14_0_259 : subd14_0 [2, -4] = true := by decide +kernel
theorem subd14_0_260 : subd14_0 [2, -3] = true := by decide +kernel
theorem subd14_0_261 : subd14_0 [2, -2] = true := by decide +kernel
theorem subd14_0_262 : subd14_0 [2, -1, -7] = true := by decide +kernel
theorem subd14_0_263 : subd14_0 [2, -1, -6] = true := by decide +kernel
theorem subd14_0_264 : subd14_0 [2, -1, -5] = true := by decide +kernel
theorem subd14_0_265 : subd14_0 [2, -1, -4] = true := by decide +kernel
theorem subd14_0_266 : subd14_0 [2, -1, -3] = true := by decide +kernel
theorem subd14_0_267 : subd14_0 [2, -1, -2] = true := by decide +kernel
theorem subd14_0_268 : subd14_0 [2, -1, -1] = true := by decide +kernel
theorem subd14_0_269 : subd14_0 [2, -1, 0] = true := by decide +kernel
theorem subd14_0_270 : subd14_0 [2, -1, 1] = true := by decide +kernel
theorem subd14_0_271 : subd14_0 [2, -1, 2] = true := by decide +kernel
theorem subd14_0_272 : subd14_0 [2, -1, 3] = true := by decide +kernel
theorem subd14_0_273 : subd14_0 [2, -1, 4] = true := by decide +kernel
theorem subd14_0_274 : subd14_0 [2, -1, 5] = true := by decide +kernel
theorem subd14_0_275 : subd14_0 [2, -1, 6] = true := by decide +kernel
theorem subd14_0_276 : subd14_0 [2, 0, -7] = true := by decide +kernel
theorem subd14_0_277 : subd14_0 [2, 0, -6] = true := by decide +kernel
theorem subd14_0_278 : subd14_0 [2, 0, -5] = true := by decide +kernel
theorem subd14_0_279 : subd14_0 [2, 0, -4] = true := by decide +kernel
theorem subd14_0_280 : subd14_0 [2, 0, -3] = true := by decide +kernel
theorem subd14_0_281 : subd14_0 [2, 0, -2] = true := by decide +kernel
theorem subd14_0_282 : subd14_0 [2, 0, -1] = true := by decide +kernel
theorem subd14_0_283 : subd14_0 [2, 0, 0] = true := by decide +kernel
theorem subd14_0_284 : subd14_0 [2, 0, 1] = true := by decide +kernel
theorem subd14_0_285 : subd14_0 [2, 0, 2] = true := by decide +kernel
theorem subd14_0_286 : subd14_0 [2, 0, 3] = true := by decide +kernel
theorem subd14_0_287 : subd14_0 [2, 0, 4] = true := by decide +kernel
theorem sbd14_0_8 : ∀ q ∈ blkd14_0_8, subd14_0 q = true := by
  unfold blkd14_0_8
  exact List.forall_mem_cons.2 ⟨subd14_0_256, List.forall_mem_cons.2 ⟨subd14_0_257, List.forall_mem_cons.2 ⟨subd14_0_258, List.forall_mem_cons.2 ⟨subd14_0_259, List.forall_mem_cons.2 ⟨subd14_0_260, List.forall_mem_cons.2 ⟨subd14_0_261, List.forall_mem_cons.2 ⟨subd14_0_262, List.forall_mem_cons.2 ⟨subd14_0_263, List.forall_mem_cons.2 ⟨subd14_0_264, List.forall_mem_cons.2 ⟨subd14_0_265, List.forall_mem_cons.2 ⟨subd14_0_266, List.forall_mem_cons.2 ⟨subd14_0_267, List.forall_mem_cons.2 ⟨subd14_0_268, List.forall_mem_cons.2 ⟨subd14_0_269, List.forall_mem_cons.2 ⟨subd14_0_270, List.forall_mem_cons.2 ⟨subd14_0_271, List.forall_mem_cons.2 ⟨subd14_0_272, List.forall_mem_cons.2 ⟨subd14_0_273, List.forall_mem_cons.2 ⟨subd14_0_274, List.forall_mem_cons.2 ⟨subd14_0_275, List.forall_mem_cons.2 ⟨subd14_0_276, List.forall_mem_cons.2 ⟨subd14_0_277, List.forall_mem_cons.2 ⟨subd14_0_278, List.forall_mem_cons.2 ⟨subd14_0_279, List.forall_mem_cons.2 ⟨subd14_0_280, List.forall_mem_cons.2 ⟨subd14_0_281, List.forall_mem_cons.2 ⟨subd14_0_282, List.forall_mem_cons.2 ⟨subd14_0_283, List.forall_mem_cons.2 ⟨subd14_0_284, List.forall_mem_cons.2 ⟨subd14_0_285, List.forall_mem_cons.2 ⟨subd14_0_286, List.forall_mem_cons.2 ⟨subd14_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_288 : subd14_0 [2, 0, 5] = true := by decide +kernel
theorem subd14_0_289 : subd14_0 [2, 0, 6] = true := by decide +kernel
theorem subd14_0_290 : subd14_0 [2, 1] = true := by decide +kernel
theorem subd14_0_291 : subd14_0 [2, 2] = true := by decide +kernel
theorem subd14_0_292 : subd14_0 [2, 3] = true := by decide +kernel
theorem subd14_0_293 : subd14_0 [2, 4] = true := by decide +kernel
theorem subd14_0_294 : subd14_0 [3, -5] = true := by decide +kernel
theorem subd14_0_295 : subd14_0 [3, -4] = true := by decide +kernel
theorem subd14_0_296 : subd14_0 [3, -3] = true := by decide +kernel
theorem subd14_0_297 : subd14_0 [3, -2] = true := by decide +kernel
theorem subd14_0_298 : subd14_0 [3, -1] = true := by decide +kernel
theorem subd14_0_299 : subd14_0 [3, 0] = true := by decide +kernel
theorem subd14_0_300 : subd14_0 [3, 1] = true := by decide +kernel
theorem subd14_0_301 : subd14_0 [3, 2] = true := by decide +kernel
theorem subd14_0_302 : subd14_0 [3, 3] = true := by decide +kernel
theorem subd14_0_303 : subd14_0 [3, 4] = true := by decide +kernel
theorem subd14_0_304 : subd14_0 [4, -4] = true := by decide +kernel
theorem subd14_0_305 : subd14_0 [4, -3] = true := by decide +kernel
theorem subd14_0_306 : subd14_0 [4, -2] = true := by decide +kernel
theorem subd14_0_307 : subd14_0 [4, -1] = true := by decide +kernel
theorem subd14_0_308 : subd14_0 [4, 0] = true := by decide +kernel
theorem subd14_0_309 : subd14_0 [4, 1] = true := by decide +kernel
theorem subd14_0_310 : subd14_0 [4, 2] = true := by decide +kernel
theorem subd14_0_311 : subd14_0 [4, 3] = true := by decide +kernel
theorem subd14_0_312 : subd14_0 [5] = true := by decide +kernel
theorem sbd14_0_9 : ∀ q ∈ blkd14_0_9, subd14_0 q = true := by
  unfold blkd14_0_9
  exact List.forall_mem_cons.2 ⟨subd14_0_288, List.forall_mem_cons.2 ⟨subd14_0_289, List.forall_mem_cons.2 ⟨subd14_0_290, List.forall_mem_cons.2 ⟨subd14_0_291, List.forall_mem_cons.2 ⟨subd14_0_292, List.forall_mem_cons.2 ⟨subd14_0_293, List.forall_mem_cons.2 ⟨subd14_0_294, List.forall_mem_cons.2 ⟨subd14_0_295, List.forall_mem_cons.2 ⟨subd14_0_296, List.forall_mem_cons.2 ⟨subd14_0_297, List.forall_mem_cons.2 ⟨subd14_0_298, List.forall_mem_cons.2 ⟨subd14_0_299, List.forall_mem_cons.2 ⟨subd14_0_300, List.forall_mem_cons.2 ⟨subd14_0_301, List.forall_mem_cons.2 ⟨subd14_0_302, List.forall_mem_cons.2 ⟨subd14_0_303, List.forall_mem_cons.2 ⟨subd14_0_304, List.forall_mem_cons.2 ⟨subd14_0_305, List.forall_mem_cons.2 ⟨subd14_0_306, List.forall_mem_cons.2 ⟨subd14_0_307, List.forall_mem_cons.2 ⟨subd14_0_308, List.forall_mem_cons.2 ⟨subd14_0_309, List.forall_mem_cons.2 ⟨subd14_0_310, List.forall_mem_cons.2 ⟨subd14_0_311, List.forall_mem_cons.2 ⟨subd14_0_312, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [-1, -2] = true := by decide +kernel
theorem subd14_1_1 : subd14_1 [-1, -1, -14] = true := by decide +kernel
theorem subd14_1_2 : subd14_1 [-1, -1, -13] = true := by decide +kernel
theorem subd14_1_3 : subd14_1 [-1, -1, -12] = true := by decide +kernel
theorem subd14_1_4 : subd14_1 [-1, -1, -11] = true := by decide +kernel
theorem subd14_1_5 : subd14_1 [-1, -1, -10] = true := by decide +kernel
theorem subd14_1_6 : subd14_1 [-1, -1, -9] = true := by decide +kernel
theorem subd14_1_7 : subd14_1 [-1, -1, -8] = true := by decide +kernel
theorem subd14_1_8 : subd14_1 [-1, -1, -7] = true := by decide +kernel
theorem subd14_1_9 : subd14_1 [-1, -1, -6] = true := by decide +kernel
theorem subd14_1_10 : subd14_1 [-1, -1, -5] = true := by decide +kernel
theorem subd14_1_11 : subd14_1 [-1, -1, -4] = true := by decide +kernel
theorem subd14_1_12 : subd14_1 [-1, -1, -3] = true := by decide +kernel
theorem subd14_1_13 : subd14_1 [-1, -1, -2] = true := by decide +kernel
theorem subd14_1_14 : subd14_1 [-1, -1, -1] = true := by decide +kernel
theorem subd14_1_15 : subd14_1 [-1, -1, 0] = true := by decide +kernel
theorem subd14_1_16 : subd14_1 [-1, -1, 1] = true := by decide +kernel
theorem subd14_1_17 : subd14_1 [-1, -1, 2] = true := by decide +kernel
theorem subd14_1_18 : subd14_1 [-1, -1, 3] = true := by decide +kernel
theorem subd14_1_19 : subd14_1 [-1, -1, 4] = true := by decide +kernel
theorem subd14_1_20 : subd14_1 [-1, -1, 5] = true := by decide +kernel
theorem subd14_1_21 : subd14_1 [-1, -1, 6] = true := by decide +kernel
theorem subd14_1_22 : subd14_1 [-1, -1, 7] = true := by decide +kernel
theorem subd14_1_23 : subd14_1 [-1, -1, 8] = true := by decide +kernel
theorem subd14_1_24 : subd14_1 [-1, -1, 9] = true := by decide +kernel
theorem subd14_1_25 : subd14_1 [-1, -1, 10] = true := by decide +kernel
theorem subd14_1_26 : subd14_1 [-1, -1, 11] = true := by decide +kernel
theorem subd14_1_27 : subd14_1 [-1, -1, 12] = true := by decide +kernel
theorem subd14_1_28 : subd14_1 [-1, -1, 13] = true := by decide +kernel
theorem subd14_1_29 : subd14_1 [-1, 0, -20] = true := by decide +kernel
theorem subd14_1_30 : subd14_1 [-1, 0, -19] = true := by decide +kernel
theorem subd14_1_31 : subd14_1 [-1, 0, -18] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_cons.2 ⟨subd14_1_1, List.forall_mem_cons.2 ⟨subd14_1_2, List.forall_mem_cons.2 ⟨subd14_1_3, List.forall_mem_cons.2 ⟨subd14_1_4, List.forall_mem_cons.2 ⟨subd14_1_5, List.forall_mem_cons.2 ⟨subd14_1_6, List.forall_mem_cons.2 ⟨subd14_1_7, List.forall_mem_cons.2 ⟨subd14_1_8, List.forall_mem_cons.2 ⟨subd14_1_9, List.forall_mem_cons.2 ⟨subd14_1_10, List.forall_mem_cons.2 ⟨subd14_1_11, List.forall_mem_cons.2 ⟨subd14_1_12, List.forall_mem_cons.2 ⟨subd14_1_13, List.forall_mem_cons.2 ⟨subd14_1_14, List.forall_mem_cons.2 ⟨subd14_1_15, List.forall_mem_cons.2 ⟨subd14_1_16, List.forall_mem_cons.2 ⟨subd14_1_17, List.forall_mem_cons.2 ⟨subd14_1_18, List.forall_mem_cons.2 ⟨subd14_1_19, List.forall_mem_cons.2 ⟨subd14_1_20, List.forall_mem_cons.2 ⟨subd14_1_21, List.forall_mem_cons.2 ⟨subd14_1_22, List.forall_mem_cons.2 ⟨subd14_1_23, List.forall_mem_cons.2 ⟨subd14_1_24, List.forall_mem_cons.2 ⟨subd14_1_25, List.forall_mem_cons.2 ⟨subd14_1_26, List.forall_mem_cons.2 ⟨subd14_1_27, List.forall_mem_cons.2 ⟨subd14_1_28, List.forall_mem_cons.2 ⟨subd14_1_29, List.forall_mem_cons.2 ⟨subd14_1_30, List.forall_mem_cons.2 ⟨subd14_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
