import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_3_64 : subd9_3 [-4, 1, -2] = true := by decide +kernel
theorem subd9_3_65 : subd9_3 [-4, 1, -1] = true := by decide +kernel
theorem subd9_3_66 : subd9_3 [-4, 1, 0] = true := by decide +kernel
theorem subd9_3_67 : subd9_3 [-4, 1, 1] = true := by decide +kernel
theorem subd9_3_68 : subd9_3 [-4, 1, 2] = true := by decide +kernel
theorem subd9_3_69 : subd9_3 [-4, 1, 3] = true := by decide +kernel
theorem subd9_3_70 : subd9_3 [-4, 1, 4] = true := by decide +kernel
theorem subd9_3_71 : subd9_3 [-4, 1, 5] = true := by decide +kernel
theorem subd9_3_72 : subd9_3 [-4, 1, 6] = true := by decide +kernel
theorem subd9_3_73 : subd9_3 [-4, 2, -8] = true := by decide +kernel
theorem subd9_3_74 : subd9_3 [-4, 2, -7] = true := by decide +kernel
theorem subd9_3_75 : subd9_3 [-4, 2, -6] = true := by decide +kernel
theorem subd9_3_76 : subd9_3 [-4, 2, -5] = true := by decide +kernel
theorem subd9_3_77 : subd9_3 [-4, 2, -4] = true := by decide +kernel
theorem subd9_3_78 : subd9_3 [-4, 2, -3] = true := by decide +kernel
theorem subd9_3_79 : subd9_3 [-4, 2, -2] = true := by decide +kernel
theorem subd9_3_80 : subd9_3 [-4, 2, -1] = true := by decide +kernel
theorem subd9_3_81 : subd9_3 [-4, 2, 0] = true := by decide +kernel
theorem subd9_3_82 : subd9_3 [-4, 2, 1] = true := by decide +kernel
theorem subd9_3_83 : subd9_3 [-4, 2, 2] = true := by decide +kernel
theorem subd9_3_84 : subd9_3 [-4, 2, 3] = true := by decide +kernel
theorem subd9_3_85 : subd9_3 [-4, 2, 4] = true := by decide +kernel
theorem subd9_3_86 : subd9_3 [-4, 2, 5] = true := by decide +kernel
theorem subd9_3_87 : subd9_3 [-4, 2, 6] = true := by decide +kernel
theorem subd9_3_88 : subd9_3 [-4, 3] = true := by decide +kernel
theorem subd9_3_89 : subd9_3 [-4, 4] = true := by decide +kernel
theorem subd9_3_90 : subd9_3 [-3, -6] = true := by decide +kernel
theorem subd9_3_91 : subd9_3 [-3, -5] = true := by decide +kernel
theorem subd9_3_92 : subd9_3 [-3, -4] = true := by decide +kernel
theorem subd9_3_93 : subd9_3 [-3, -3, -8] = true := by decide +kernel
theorem subd9_3_94 : subd9_3 [-3, -3, -7] = true := by decide +kernel
theorem subd9_3_95 : subd9_3 [-3, -3, -6] = true := by decide +kernel
theorem sbd9_3_2 : ∀ q ∈ blkd9_3_2, subd9_3 q = true := by
  unfold blkd9_3_2
  exact List.forall_mem_cons.2 ⟨subd9_3_64, List.forall_mem_cons.2 ⟨subd9_3_65, List.forall_mem_cons.2 ⟨subd9_3_66, List.forall_mem_cons.2 ⟨subd9_3_67, List.forall_mem_cons.2 ⟨subd9_3_68, List.forall_mem_cons.2 ⟨subd9_3_69, List.forall_mem_cons.2 ⟨subd9_3_70, List.forall_mem_cons.2 ⟨subd9_3_71, List.forall_mem_cons.2 ⟨subd9_3_72, List.forall_mem_cons.2 ⟨subd9_3_73, List.forall_mem_cons.2 ⟨subd9_3_74, List.forall_mem_cons.2 ⟨subd9_3_75, List.forall_mem_cons.2 ⟨subd9_3_76, List.forall_mem_cons.2 ⟨subd9_3_77, List.forall_mem_cons.2 ⟨subd9_3_78, List.forall_mem_cons.2 ⟨subd9_3_79, List.forall_mem_cons.2 ⟨subd9_3_80, List.forall_mem_cons.2 ⟨subd9_3_81, List.forall_mem_cons.2 ⟨subd9_3_82, List.forall_mem_cons.2 ⟨subd9_3_83, List.forall_mem_cons.2 ⟨subd9_3_84, List.forall_mem_cons.2 ⟨subd9_3_85, List.forall_mem_cons.2 ⟨subd9_3_86, List.forall_mem_cons.2 ⟨subd9_3_87, List.forall_mem_cons.2 ⟨subd9_3_88, List.forall_mem_cons.2 ⟨subd9_3_89, List.forall_mem_cons.2 ⟨subd9_3_90, List.forall_mem_cons.2 ⟨subd9_3_91, List.forall_mem_cons.2 ⟨subd9_3_92, List.forall_mem_cons.2 ⟨subd9_3_93, List.forall_mem_cons.2 ⟨subd9_3_94, List.forall_mem_cons.2 ⟨subd9_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_96 : subd9_3 [-3, -3, -5] = true := by decide +kernel
theorem subd9_3_97 : subd9_3 [-3, -3, -4] = true := by decide +kernel
theorem subd9_3_98 : subd9_3 [-3, -3, -3] = true := by decide +kernel
theorem subd9_3_99 : subd9_3 [-3, -3, -2] = true := by decide +kernel
theorem subd9_3_100 : subd9_3 [-3, -3, -1] = true := by decide +kernel
theorem subd9_3_101 : subd9_3 [-3, -3, 0] = true := by decide +kernel
theorem subd9_3_102 : subd9_3 [-3, -3, 1] = true := by decide +kernel
theorem subd9_3_103 : subd9_3 [-3, -3, 2] = true := by decide +kernel
theorem subd9_3_104 : subd9_3 [-3, -3, 3] = true := by decide +kernel
theorem subd9_3_105 : subd9_3 [-3, -3, 4] = true := by decide +kernel
theorem subd9_3_106 : subd9_3 [-3, -3, 5] = true := by decide +kernel
theorem subd9_3_107 : subd9_3 [-3, -3, 6] = true := by decide +kernel
theorem subd9_3_108 : subd9_3 [-3, -2, -9] = true := by decide +kernel
theorem subd9_3_109 : subd9_3 [-3, -2, -8] = true := by decide +kernel
theorem subd9_3_110 : subd9_3 [-3, -2, -7] = true := by decide +kernel
theorem subd9_3_111 : subd9_3 [-3, -2, -6] = true := by decide +kernel
theorem subd9_3_112 : subd9_3 [-3, -2, -5] = true := by decide +kernel
theorem subd9_3_113 : subd9_3 [-3, -2, -4] = true := by decide +kernel
theorem subd9_3_114 : subd9_3 [-3, -2, -3] = true := by decide +kernel
theorem subd9_3_115 : subd9_3 [-3, -2, -2] = true := by decide +kernel
theorem subd9_3_116 : subd9_3 [-3, -2, -1] = true := by decide +kernel
theorem subd9_3_117 : subd9_3 [-3, -2, 0] = true := by decide +kernel
theorem subd9_3_118 : subd9_3 [-3, -2, 1] = true := by decide +kernel
theorem subd9_3_119 : subd9_3 [-3, -2, 2] = true := by decide +kernel
theorem subd9_3_120 : subd9_3 [-3, -2, 3] = true := by decide +kernel
theorem subd9_3_121 : subd9_3 [-3, -2, 4] = true := by decide +kernel
theorem subd9_3_122 : subd9_3 [-3, -2, 5] = true := by decide +kernel
theorem subd9_3_123 : subd9_3 [-3, -2, 6] = true := by decide +kernel
theorem subd9_3_124 : subd9_3 [-3, -2, 7] = true := by decide +kernel
theorem subd9_3_125 : subd9_3 [-3, -1, -9] = true := by decide +kernel
theorem subd9_3_126 : subd9_3 [-3, -1, -8] = true := by decide +kernel
theorem subd9_3_127 : subd9_3 [-3, -1, -7] = true := by decide +kernel
theorem sbd9_3_3 : ∀ q ∈ blkd9_3_3, subd9_3 q = true := by
  unfold blkd9_3_3
  exact List.forall_mem_cons.2 ⟨subd9_3_96, List.forall_mem_cons.2 ⟨subd9_3_97, List.forall_mem_cons.2 ⟨subd9_3_98, List.forall_mem_cons.2 ⟨subd9_3_99, List.forall_mem_cons.2 ⟨subd9_3_100, List.forall_mem_cons.2 ⟨subd9_3_101, List.forall_mem_cons.2 ⟨subd9_3_102, List.forall_mem_cons.2 ⟨subd9_3_103, List.forall_mem_cons.2 ⟨subd9_3_104, List.forall_mem_cons.2 ⟨subd9_3_105, List.forall_mem_cons.2 ⟨subd9_3_106, List.forall_mem_cons.2 ⟨subd9_3_107, List.forall_mem_cons.2 ⟨subd9_3_108, List.forall_mem_cons.2 ⟨subd9_3_109, List.forall_mem_cons.2 ⟨subd9_3_110, List.forall_mem_cons.2 ⟨subd9_3_111, List.forall_mem_cons.2 ⟨subd9_3_112, List.forall_mem_cons.2 ⟨subd9_3_113, List.forall_mem_cons.2 ⟨subd9_3_114, List.forall_mem_cons.2 ⟨subd9_3_115, List.forall_mem_cons.2 ⟨subd9_3_116, List.forall_mem_cons.2 ⟨subd9_3_117, List.forall_mem_cons.2 ⟨subd9_3_118, List.forall_mem_cons.2 ⟨subd9_3_119, List.forall_mem_cons.2 ⟨subd9_3_120, List.forall_mem_cons.2 ⟨subd9_3_121, List.forall_mem_cons.2 ⟨subd9_3_122, List.forall_mem_cons.2 ⟨subd9_3_123, List.forall_mem_cons.2 ⟨subd9_3_124, List.forall_mem_cons.2 ⟨subd9_3_125, List.forall_mem_cons.2 ⟨subd9_3_126, List.forall_mem_cons.2 ⟨subd9_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_128 : subd9_3 [-3, -1, -6] = true := by decide +kernel
theorem subd9_3_129 : subd9_3 [-3, -1, -5] = true := by decide +kernel
theorem subd9_3_130 : subd9_3 [-3, -1, -4] = true := by decide +kernel
theorem subd9_3_131 : subd9_3 [-3, -1, -3] = true := by decide +kernel
theorem subd9_3_132 : subd9_3 [-3, -1, -2] = true := by decide +kernel
theorem subd9_3_133 : subd9_3 [-3, -1, -1] = true := by decide +kernel
theorem subd9_3_134 : subd9_3 [-3, -1, 0] = true := by decide +kernel
theorem subd9_3_135 : subd9_3 [-3, -1, 1] = true := by decide +kernel
theorem subd9_3_136 : subd9_3 [-3, -1, 2] = true := by decide +kernel
theorem subd9_3_137 : subd9_3 [-3, -1, 3] = true := by decide +kernel
theorem subd9_3_138 : subd9_3 [-3, -1, 4] = true := by decide +kernel
theorem subd9_3_139 : subd9_3 [-3, -1, 5] = true := by decide +kernel
theorem subd9_3_140 : subd9_3 [-3, -1, 6] = true := by decide +kernel
theorem subd9_3_141 : subd9_3 [-3, -1, 7] = true := by decide +kernel
theorem subd9_3_142 : subd9_3 [-3, 0, -9] = true := by decide +kernel
theorem subd9_3_143 : subd9_3 [-3, 0, -8] = true := by decide +kernel
theorem subd9_3_144 : subd9_3 [-3, 0, -7] = true := by decide +kernel
theorem subd9_3_145 : subd9_3 [-3, 0, -6] = true := by decide +kernel
theorem subd9_3_146 : subd9_3 [-3, 0, -5] = true := by decide +kernel
theorem subd9_3_147 : subd9_3 [-3, 0, -4] = true := by decide +kernel
theorem subd9_3_148 : subd9_3 [-3, 0, -3] = true := by decide +kernel
theorem subd9_3_149 : subd9_3 [-3, 0, -2] = true := by decide +kernel
theorem subd9_3_150 : subd9_3 [-3, 0, -1] = true := by decide +kernel
theorem subd9_3_151 : subd9_3 [-3, 0, 0] = true := by decide +kernel
theorem subd9_3_152 : subd9_3 [-3, 0, 1] = true := by decide +kernel
theorem subd9_3_153 : subd9_3 [-3, 0, 2] = true := by decide +kernel
theorem subd9_3_154 : subd9_3 [-3, 0, 3] = true := by decide +kernel
theorem subd9_3_155 : subd9_3 [-3, 0, 4] = true := by decide +kernel
theorem subd9_3_156 : subd9_3 [-3, 0, 5] = true := by decide +kernel
theorem subd9_3_157 : subd9_3 [-3, 0, 6] = true := by decide +kernel
theorem subd9_3_158 : subd9_3 [-3, 0, 7] = true := by decide +kernel
theorem subd9_3_159 : subd9_3 [-3, 0, 8] = true := by decide +kernel
theorem sbd9_3_4 : ∀ q ∈ blkd9_3_4, subd9_3 q = true := by
  unfold blkd9_3_4
  exact List.forall_mem_cons.2 ⟨subd9_3_128, List.forall_mem_cons.2 ⟨subd9_3_129, List.forall_mem_cons.2 ⟨subd9_3_130, List.forall_mem_cons.2 ⟨subd9_3_131, List.forall_mem_cons.2 ⟨subd9_3_132, List.forall_mem_cons.2 ⟨subd9_3_133, List.forall_mem_cons.2 ⟨subd9_3_134, List.forall_mem_cons.2 ⟨subd9_3_135, List.forall_mem_cons.2 ⟨subd9_3_136, List.forall_mem_cons.2 ⟨subd9_3_137, List.forall_mem_cons.2 ⟨subd9_3_138, List.forall_mem_cons.2 ⟨subd9_3_139, List.forall_mem_cons.2 ⟨subd9_3_140, List.forall_mem_cons.2 ⟨subd9_3_141, List.forall_mem_cons.2 ⟨subd9_3_142, List.forall_mem_cons.2 ⟨subd9_3_143, List.forall_mem_cons.2 ⟨subd9_3_144, List.forall_mem_cons.2 ⟨subd9_3_145, List.forall_mem_cons.2 ⟨subd9_3_146, List.forall_mem_cons.2 ⟨subd9_3_147, List.forall_mem_cons.2 ⟨subd9_3_148, List.forall_mem_cons.2 ⟨subd9_3_149, List.forall_mem_cons.2 ⟨subd9_3_150, List.forall_mem_cons.2 ⟨subd9_3_151, List.forall_mem_cons.2 ⟨subd9_3_152, List.forall_mem_cons.2 ⟨subd9_3_153, List.forall_mem_cons.2 ⟨subd9_3_154, List.forall_mem_cons.2 ⟨subd9_3_155, List.forall_mem_cons.2 ⟨subd9_3_156, List.forall_mem_cons.2 ⟨subd9_3_157, List.forall_mem_cons.2 ⟨subd9_3_158, List.forall_mem_cons.2 ⟨subd9_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_160 : subd9_3 [-3, 1, -9] = true := by decide +kernel
theorem subd9_3_161 : subd9_3 [-3, 1, -8] = true := by decide +kernel
theorem subd9_3_162 : subd9_3 [-3, 1, -7] = true := by decide +kernel
theorem subd9_3_163 : subd9_3 [-3, 1, -6] = true := by decide +kernel
theorem subd9_3_164 : subd9_3 [-3, 1, -5] = true := by decide +kernel
theorem subd9_3_165 : subd9_3 [-3, 1, -4] = true := by decide +kernel
theorem subd9_3_166 : subd9_3 [-3, 1, -3] = true := by decide +kernel
theorem subd9_3_167 : subd9_3 [-3, 1, -2] = true := by decide +kernel
theorem subd9_3_168 : subd9_3 [-3, 1, -1] = true := by decide +kernel
theorem subd9_3_169 : subd9_3 [-3, 1, 0] = true := by decide +kernel
theorem subd9_3_170 : subd9_3 [-3, 1, 1] = true := by decide +kernel
theorem subd9_3_171 : subd9_3 [-3, 1, 2] = true := by decide +kernel
theorem subd9_3_172 : subd9_3 [-3, 1, 3] = true := by decide +kernel
theorem subd9_3_173 : subd9_3 [-3, 1, 4] = true := by decide +kernel
theorem subd9_3_174 : subd9_3 [-3, 1, 5] = true := by decide +kernel
theorem subd9_3_175 : subd9_3 [-3, 1, 6] = true := by decide +kernel
theorem subd9_3_176 : subd9_3 [-3, 1, 7] = true := by decide +kernel
theorem subd9_3_177 : subd9_3 [-3, 1, 8] = true := by decide +kernel
theorem subd9_3_178 : subd9_3 [-3, 2, -9] = true := by decide +kernel
theorem subd9_3_179 : subd9_3 [-3, 2, -8] = true := by decide +kernel
theorem subd9_3_180 : subd9_3 [-3, 2, -7] = true := by decide +kernel
theorem subd9_3_181 : subd9_3 [-3, 2, -6] = true := by decide +kernel
theorem subd9_3_182 : subd9_3 [-3, 2, -5] = true := by decide +kernel
theorem subd9_3_183 : subd9_3 [-3, 2, -4] = true := by decide +kernel
theorem subd9_3_184 : subd9_3 [-3, 2, -3] = true := by decide +kernel
theorem subd9_3_185 : subd9_3 [-3, 2, -2] = true := by decide +kernel
theorem subd9_3_186 : subd9_3 [-3, 2, -1] = true := by decide +kernel
theorem subd9_3_187 : subd9_3 [-3, 2, 0] = true := by decide +kernel
theorem subd9_3_188 : subd9_3 [-3, 2, 1] = true := by decide +kernel
theorem subd9_3_189 : subd9_3 [-3, 2, 2] = true := by decide +kernel
theorem subd9_3_190 : subd9_3 [-3, 2, 3] = true := by decide +kernel
theorem subd9_3_191 : subd9_3 [-3, 2, 4] = true := by decide +kernel
theorem sbd9_3_5 : ∀ q ∈ blkd9_3_5, subd9_3 q = true := by
  unfold blkd9_3_5
  exact List.forall_mem_cons.2 ⟨subd9_3_160, List.forall_mem_cons.2 ⟨subd9_3_161, List.forall_mem_cons.2 ⟨subd9_3_162, List.forall_mem_cons.2 ⟨subd9_3_163, List.forall_mem_cons.2 ⟨subd9_3_164, List.forall_mem_cons.2 ⟨subd9_3_165, List.forall_mem_cons.2 ⟨subd9_3_166, List.forall_mem_cons.2 ⟨subd9_3_167, List.forall_mem_cons.2 ⟨subd9_3_168, List.forall_mem_cons.2 ⟨subd9_3_169, List.forall_mem_cons.2 ⟨subd9_3_170, List.forall_mem_cons.2 ⟨subd9_3_171, List.forall_mem_cons.2 ⟨subd9_3_172, List.forall_mem_cons.2 ⟨subd9_3_173, List.forall_mem_cons.2 ⟨subd9_3_174, List.forall_mem_cons.2 ⟨subd9_3_175, List.forall_mem_cons.2 ⟨subd9_3_176, List.forall_mem_cons.2 ⟨subd9_3_177, List.forall_mem_cons.2 ⟨subd9_3_178, List.forall_mem_cons.2 ⟨subd9_3_179, List.forall_mem_cons.2 ⟨subd9_3_180, List.forall_mem_cons.2 ⟨subd9_3_181, List.forall_mem_cons.2 ⟨subd9_3_182, List.forall_mem_cons.2 ⟨subd9_3_183, List.forall_mem_cons.2 ⟨subd9_3_184, List.forall_mem_cons.2 ⟨subd9_3_185, List.forall_mem_cons.2 ⟨subd9_3_186, List.forall_mem_cons.2 ⟨subd9_3_187, List.forall_mem_cons.2 ⟨subd9_3_188, List.forall_mem_cons.2 ⟨subd9_3_189, List.forall_mem_cons.2 ⟨subd9_3_190, List.forall_mem_cons.2 ⟨subd9_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_192 : subd9_3 [-3, 2, 5] = true := by decide +kernel
theorem subd9_3_193 : subd9_3 [-3, 2, 6] = true := by decide +kernel
theorem subd9_3_194 : subd9_3 [-3, 2, 7] = true := by decide +kernel
theorem subd9_3_195 : subd9_3 [-3, 3, -8] = true := by decide +kernel
theorem subd9_3_196 : subd9_3 [-3, 3, -7] = true := by decide +kernel
theorem subd9_3_197 : subd9_3 [-3, 3, -6] = true := by decide +kernel
theorem subd9_3_198 : subd9_3 [-3, 3, -5] = true := by decide +kernel
theorem subd9_3_199 : subd9_3 [-3, 3, -4] = true := by decide +kernel
theorem subd9_3_200 : subd9_3 [-3, 3, -3] = true := by decide +kernel
theorem subd9_3_201 : subd9_3 [-3, 3, -2] = true := by decide +kernel
theorem subd9_3_202 : subd9_3 [-3, 3, -1] = true := by decide +kernel
theorem subd9_3_203 : subd9_3 [-3, 3, 0] = true := by decide +kernel
theorem subd9_3_204 : subd9_3 [-3, 3, 1] = true := by decide +kernel
theorem subd9_3_205 : subd9_3 [-3, 3, 2] = true := by decide +kernel
theorem subd9_3_206 : subd9_3 [-3, 3, 3] = true := by decide +kernel
theorem subd9_3_207 : subd9_3 [-3, 3, 4] = true := by decide +kernel
theorem subd9_3_208 : subd9_3 [-3, 3, 5] = true := by decide +kernel
theorem subd9_3_209 : subd9_3 [-3, 3, 6] = true := by decide +kernel
theorem subd9_3_210 : subd9_3 [-3, 4] = true := by decide +kernel
theorem subd9_3_211 : subd9_3 [-3, 5] = true := by decide +kernel
theorem subd9_3_212 : subd9_3 [-2, -6] = true := by decide +kernel
theorem subd9_3_213 : subd9_3 [-2, -5] = true := by decide +kernel
theorem subd9_3_214 : subd9_3 [-2, -4, -8] = true := by decide +kernel
theorem subd9_3_215 : subd9_3 [-2, -4, -7] = true := by decide +kernel
theorem subd9_3_216 : subd9_3 [-2, -4, -6] = true := by decide +kernel
theorem subd9_3_217 : subd9_3 [-2, -4, -5] = true := by decide +kernel
theorem subd9_3_218 : subd9_3 [-2, -4, -4] = true := by decide +kernel
theorem subd9_3_219 : subd9_3 [-2, -4, -3] = true := by decide +kernel
theorem subd9_3_220 : subd9_3 [-2, -4, -2] = true := by decide +kernel
theorem subd9_3_221 : subd9_3 [-2, -4, -1] = true := by decide +kernel
theorem subd9_3_222 : subd9_3 [-2, -4, 0] = true := by decide +kernel
theorem subd9_3_223 : subd9_3 [-2, -4, 1] = true := by decide +kernel
theorem sbd9_3_6 : ∀ q ∈ blkd9_3_6, subd9_3 q = true := by
  unfold blkd9_3_6
  exact List.forall_mem_cons.2 ⟨subd9_3_192, List.forall_mem_cons.2 ⟨subd9_3_193, List.forall_mem_cons.2 ⟨subd9_3_194, List.forall_mem_cons.2 ⟨subd9_3_195, List.forall_mem_cons.2 ⟨subd9_3_196, List.forall_mem_cons.2 ⟨subd9_3_197, List.forall_mem_cons.2 ⟨subd9_3_198, List.forall_mem_cons.2 ⟨subd9_3_199, List.forall_mem_cons.2 ⟨subd9_3_200, List.forall_mem_cons.2 ⟨subd9_3_201, List.forall_mem_cons.2 ⟨subd9_3_202, List.forall_mem_cons.2 ⟨subd9_3_203, List.forall_mem_cons.2 ⟨subd9_3_204, List.forall_mem_cons.2 ⟨subd9_3_205, List.forall_mem_cons.2 ⟨subd9_3_206, List.forall_mem_cons.2 ⟨subd9_3_207, List.forall_mem_cons.2 ⟨subd9_3_208, List.forall_mem_cons.2 ⟨subd9_3_209, List.forall_mem_cons.2 ⟨subd9_3_210, List.forall_mem_cons.2 ⟨subd9_3_211, List.forall_mem_cons.2 ⟨subd9_3_212, List.forall_mem_cons.2 ⟨subd9_3_213, List.forall_mem_cons.2 ⟨subd9_3_214, List.forall_mem_cons.2 ⟨subd9_3_215, List.forall_mem_cons.2 ⟨subd9_3_216, List.forall_mem_cons.2 ⟨subd9_3_217, List.forall_mem_cons.2 ⟨subd9_3_218, List.forall_mem_cons.2 ⟨subd9_3_219, List.forall_mem_cons.2 ⟨subd9_3_220, List.forall_mem_cons.2 ⟨subd9_3_221, List.forall_mem_cons.2 ⟨subd9_3_222, List.forall_mem_cons.2 ⟨subd9_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_224 : subd9_3 [-2, -4, 2] = true := by decide +kernel
theorem subd9_3_225 : subd9_3 [-2, -4, 3] = true := by decide +kernel
theorem subd9_3_226 : subd9_3 [-2, -4, 4] = true := by decide +kernel
theorem subd9_3_227 : subd9_3 [-2, -4, 5] = true := by decide +kernel
theorem subd9_3_228 : subd9_3 [-2, -4, 6] = true := by decide +kernel
theorem subd9_3_229 : subd9_3 [-2, -3, -9] = true := by decide +kernel
theorem subd9_3_230 : subd9_3 [-2, -3, -8] = true := by decide +kernel
theorem subd9_3_231 : subd9_3 [-2, -3, -7] = true := by decide +kernel
theorem subd9_3_232 : subd9_3 [-2, -3, -6] = true := by decide +kernel
theorem subd9_3_233 : subd9_3 [-2, -3, -5] = true := by decide +kernel
theorem subd9_3_234 : subd9_3 [-2, -3, -4] = true := by decide +kernel
theorem subd9_3_235 : subd9_3 [-2, -3, -3] = true := by decide +kernel
theorem subd9_3_236 : subd9_3 [-2, -3, -2] = true := by decide +kernel
theorem subd9_3_237 : subd9_3 [-2, -3, -1] = true := by decide +kernel
theorem subd9_3_238 : subd9_3 [-2, -3, 0] = true := by decide +kernel
theorem subd9_3_239 : subd9_3 [-2, -3, 1] = true := by decide +kernel
theorem subd9_3_240 : subd9_3 [-2, -3, 2] = true := by decide +kernel
theorem subd9_3_241 : subd9_3 [-2, -3, 3] = true := by decide +kernel
theorem subd9_3_242 : subd9_3 [-2, -3, 4] = true := by decide +kernel
theorem subd9_3_243 : subd9_3 [-2, -3, 5] = true := by decide +kernel
theorem subd9_3_244 : subd9_3 [-2, -3, 6] = true := by decide +kernel
theorem subd9_3_245 : subd9_3 [-2, -3, 7] = true := by decide +kernel
theorem subd9_3_246 : subd9_3 [-2, -2, -10] = true := by decide +kernel
theorem subd9_3_247 : subd9_3 [-2, -2, -9] = true := by decide +kernel
theorem subd9_3_248 : subd9_3 [-2, -2, -8] = true := by decide +kernel
theorem subd9_3_249 : subd9_3 [-2, -2, -7] = true := by decide +kernel
theorem subd9_3_250 : subd9_3 [-2, -2, -6] = true := by decide +kernel
theorem subd9_3_251 : subd9_3 [-2, -2, -5] = true := by decide +kernel
theorem subd9_3_252 : subd9_3 [-2, -2, -4] = true := by decide +kernel
theorem subd9_3_253 : subd9_3 [-2, -2, -3] = true := by decide +kernel
theorem subd9_3_254 : subd9_3 [-2, -2, -2] = true := by decide +kernel
theorem subd9_3_255 : subd9_3 [-2, -2, -1] = true := by decide +kernel
theorem sbd9_3_7 : ∀ q ∈ blkd9_3_7, subd9_3 q = true := by
  unfold blkd9_3_7
  exact List.forall_mem_cons.2 ⟨subd9_3_224, List.forall_mem_cons.2 ⟨subd9_3_225, List.forall_mem_cons.2 ⟨subd9_3_226, List.forall_mem_cons.2 ⟨subd9_3_227, List.forall_mem_cons.2 ⟨subd9_3_228, List.forall_mem_cons.2 ⟨subd9_3_229, List.forall_mem_cons.2 ⟨subd9_3_230, List.forall_mem_cons.2 ⟨subd9_3_231, List.forall_mem_cons.2 ⟨subd9_3_232, List.forall_mem_cons.2 ⟨subd9_3_233, List.forall_mem_cons.2 ⟨subd9_3_234, List.forall_mem_cons.2 ⟨subd9_3_235, List.forall_mem_cons.2 ⟨subd9_3_236, List.forall_mem_cons.2 ⟨subd9_3_237, List.forall_mem_cons.2 ⟨subd9_3_238, List.forall_mem_cons.2 ⟨subd9_3_239, List.forall_mem_cons.2 ⟨subd9_3_240, List.forall_mem_cons.2 ⟨subd9_3_241, List.forall_mem_cons.2 ⟨subd9_3_242, List.forall_mem_cons.2 ⟨subd9_3_243, List.forall_mem_cons.2 ⟨subd9_3_244, List.forall_mem_cons.2 ⟨subd9_3_245, List.forall_mem_cons.2 ⟨subd9_3_246, List.forall_mem_cons.2 ⟨subd9_3_247, List.forall_mem_cons.2 ⟨subd9_3_248, List.forall_mem_cons.2 ⟨subd9_3_249, List.forall_mem_cons.2 ⟨subd9_3_250, List.forall_mem_cons.2 ⟨subd9_3_251, List.forall_mem_cons.2 ⟨subd9_3_252, List.forall_mem_cons.2 ⟨subd9_3_253, List.forall_mem_cons.2 ⟨subd9_3_254, List.forall_mem_cons.2 ⟨subd9_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_256 : subd9_3 [-2, -2, 0] = true := by decide +kernel
theorem subd9_3_257 : subd9_3 [-2, -2, 1] = true := by decide +kernel
theorem subd9_3_258 : subd9_3 [-2, -2, 2] = true := by decide +kernel
theorem subd9_3_259 : subd9_3 [-2, -2, 3] = true := by decide +kernel
theorem subd9_3_260 : subd9_3 [-2, -2, 4] = true := by decide +kernel
theorem subd9_3_261 : subd9_3 [-2, -2, 5] = true := by decide +kernel
theorem subd9_3_262 : subd9_3 [-2, -2, 6] = true := by decide +kernel
theorem subd9_3_263 : subd9_3 [-2, -2, 7] = true := by decide +kernel
theorem subd9_3_264 : subd9_3 [-2, -2, 8] = true := by decide +kernel
theorem subd9_3_265 : subd9_3 [-2, -1, -10] = true := by decide +kernel
theorem subd9_3_266 : subd9_3 [-2, -1, -9] = true := by decide +kernel
theorem subd9_3_267 : subd9_3 [-2, -1, -8] = true := by decide +kernel
theorem subd9_3_268 : subd9_3 [-2, -1, -7] = true := by decide +kernel
theorem subd9_3_269 : subd9_3 [-2, -1, -6] = true := by decide +kernel
theorem subd9_3_270 : subd9_3 [-2, -1, -5] = true := by decide +kernel
theorem subd9_3_271 : subd9_3 [-2, -1, -4] = true := by decide +kernel
theorem subd9_3_272 : subd9_3 [-2, -1, -3] = true := by decide +kernel
theorem subd9_3_273 : subd9_3 [-2, -1, -2] = true := by decide +kernel
theorem subd9_3_274 : subd9_3 [-2, -1, -1] = true := by decide +kernel
theorem subd9_3_275 : subd9_3 [-2, -1, 0] = true := by decide +kernel
theorem subd9_3_276 : subd9_3 [-2, -1, 1] = true := by decide +kernel
theorem subd9_3_277 : subd9_3 [-2, -1, 2] = true := by decide +kernel
theorem subd9_3_278 : subd9_3 [-2, -1, 3] = true := by decide +kernel
theorem subd9_3_279 : subd9_3 [-2, -1, 4] = true := by decide +kernel
theorem subd9_3_280 : subd9_3 [-2, -1, 5] = true := by decide +kernel
theorem subd9_3_281 : subd9_3 [-2, -1, 6] = true := by decide +kernel
theorem subd9_3_282 : subd9_3 [-2, -1, 7] = true := by decide +kernel
theorem subd9_3_283 : subd9_3 [-2, -1, 8] = true := by decide +kernel
theorem subd9_3_284 : subd9_3 [-2, 0, -10] = true := by decide +kernel
theorem subd9_3_285 : subd9_3 [-2, 0, -9] = true := by decide +kernel
theorem subd9_3_286 : subd9_3 [-2, 0, -8] = true := by decide +kernel
theorem subd9_3_287 : subd9_3 [-2, 0, -7] = true := by decide +kernel
theorem sbd9_3_8 : ∀ q ∈ blkd9_3_8, subd9_3 q = true := by
  unfold blkd9_3_8
  exact List.forall_mem_cons.2 ⟨subd9_3_256, List.forall_mem_cons.2 ⟨subd9_3_257, List.forall_mem_cons.2 ⟨subd9_3_258, List.forall_mem_cons.2 ⟨subd9_3_259, List.forall_mem_cons.2 ⟨subd9_3_260, List.forall_mem_cons.2 ⟨subd9_3_261, List.forall_mem_cons.2 ⟨subd9_3_262, List.forall_mem_cons.2 ⟨subd9_3_263, List.forall_mem_cons.2 ⟨subd9_3_264, List.forall_mem_cons.2 ⟨subd9_3_265, List.forall_mem_cons.2 ⟨subd9_3_266, List.forall_mem_cons.2 ⟨subd9_3_267, List.forall_mem_cons.2 ⟨subd9_3_268, List.forall_mem_cons.2 ⟨subd9_3_269, List.forall_mem_cons.2 ⟨subd9_3_270, List.forall_mem_cons.2 ⟨subd9_3_271, List.forall_mem_cons.2 ⟨subd9_3_272, List.forall_mem_cons.2 ⟨subd9_3_273, List.forall_mem_cons.2 ⟨subd9_3_274, List.forall_mem_cons.2 ⟨subd9_3_275, List.forall_mem_cons.2 ⟨subd9_3_276, List.forall_mem_cons.2 ⟨subd9_3_277, List.forall_mem_cons.2 ⟨subd9_3_278, List.forall_mem_cons.2 ⟨subd9_3_279, List.forall_mem_cons.2 ⟨subd9_3_280, List.forall_mem_cons.2 ⟨subd9_3_281, List.forall_mem_cons.2 ⟨subd9_3_282, List.forall_mem_cons.2 ⟨subd9_3_283, List.forall_mem_cons.2 ⟨subd9_3_284, List.forall_mem_cons.2 ⟨subd9_3_285, List.forall_mem_cons.2 ⟨subd9_3_286, List.forall_mem_cons.2 ⟨subd9_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_288 : subd9_3 [-2, 0, -6] = true := by decide +kernel
theorem subd9_3_289 : subd9_3 [-2, 0, -5] = true := by decide +kernel
theorem subd9_3_290 : subd9_3 [-2, 0, -4] = true := by decide +kernel
theorem subd9_3_291 : subd9_3 [-2, 0, -3] = true := by decide +kernel
theorem subd9_3_292 : subd9_3 [-2, 0, -2] = true := by decide +kernel
theorem subd9_3_293 : subd9_3 [-2, 0, -1] = true := by decide +kernel
theorem subd9_3_294 : subd9_3 [-2, 0, 0] = true := by decide +kernel
theorem subd9_3_295 : subd9_3 [-2, 0, 1] = true := by decide +kernel
theorem subd9_3_296 : subd9_3 [-2, 0, 2] = true := by decide +kernel
theorem subd9_3_297 : subd9_3 [-2, 0, 3] = true := by decide +kernel
theorem subd9_3_298 : subd9_3 [-2, 0, 4] = true := by decide +kernel
theorem subd9_3_299 : subd9_3 [-2, 0, 5] = true := by decide +kernel
theorem subd9_3_300 : subd9_3 [-2, 0, 6] = true := by decide +kernel
theorem subd9_3_301 : subd9_3 [-2, 0, 7] = true := by decide +kernel
theorem subd9_3_302 : subd9_3 [-2, 0, 8] = true := by decide +kernel
theorem subd9_3_303 : subd9_3 [-2, 1, -10] = true := by decide +kernel
theorem subd9_3_304 : subd9_3 [-2, 1, -9] = true := by decide +kernel
theorem subd9_3_305 : subd9_3 [-2, 1, -8] = true := by decide +kernel
theorem subd9_3_306 : subd9_3 [-2, 1, -7] = true := by decide +kernel
theorem subd9_3_307 : subd9_3 [-2, 1, -6] = true := by decide +kernel
theorem subd9_3_308 : subd9_3 [-2, 1, -5] = true := by decide +kernel
theorem subd9_3_309 : subd9_3 [-2, 1, -4] = true := by decide +kernel
theorem subd9_3_310 : subd9_3 [-2, 1, -3] = true := by decide +kernel
theorem subd9_3_311 : subd9_3 [-2, 1, -2] = true := by decide +kernel
theorem subd9_3_312 : subd9_3 [-2, 1, -1] = true := by decide +kernel
theorem subd9_3_313 : subd9_3 [-2, 1, 0] = true := by decide +kernel
theorem subd9_3_314 : subd9_3 [-2, 1, 1] = true := by decide +kernel
theorem subd9_3_315 : subd9_3 [-2, 1, 2] = true := by decide +kernel
theorem subd9_3_316 : subd9_3 [-2, 1, 3] = true := by decide +kernel
theorem subd9_3_317 : subd9_3 [-2, 1, 4] = true := by decide +kernel
theorem subd9_3_318 : subd9_3 [-2, 1, 5] = true := by decide +kernel
theorem subd9_3_319 : subd9_3 [-2, 1, 6] = true := by decide +kernel
theorem sbd9_3_9 : ∀ q ∈ blkd9_3_9, subd9_3 q = true := by
  unfold blkd9_3_9
  exact List.forall_mem_cons.2 ⟨subd9_3_288, List.forall_mem_cons.2 ⟨subd9_3_289, List.forall_mem_cons.2 ⟨subd9_3_290, List.forall_mem_cons.2 ⟨subd9_3_291, List.forall_mem_cons.2 ⟨subd9_3_292, List.forall_mem_cons.2 ⟨subd9_3_293, List.forall_mem_cons.2 ⟨subd9_3_294, List.forall_mem_cons.2 ⟨subd9_3_295, List.forall_mem_cons.2 ⟨subd9_3_296, List.forall_mem_cons.2 ⟨subd9_3_297, List.forall_mem_cons.2 ⟨subd9_3_298, List.forall_mem_cons.2 ⟨subd9_3_299, List.forall_mem_cons.2 ⟨subd9_3_300, List.forall_mem_cons.2 ⟨subd9_3_301, List.forall_mem_cons.2 ⟨subd9_3_302, List.forall_mem_cons.2 ⟨subd9_3_303, List.forall_mem_cons.2 ⟨subd9_3_304, List.forall_mem_cons.2 ⟨subd9_3_305, List.forall_mem_cons.2 ⟨subd9_3_306, List.forall_mem_cons.2 ⟨subd9_3_307, List.forall_mem_cons.2 ⟨subd9_3_308, List.forall_mem_cons.2 ⟨subd9_3_309, List.forall_mem_cons.2 ⟨subd9_3_310, List.forall_mem_cons.2 ⟨subd9_3_311, List.forall_mem_cons.2 ⟨subd9_3_312, List.forall_mem_cons.2 ⟨subd9_3_313, List.forall_mem_cons.2 ⟨subd9_3_314, List.forall_mem_cons.2 ⟨subd9_3_315, List.forall_mem_cons.2 ⟨subd9_3_316, List.forall_mem_cons.2 ⟨subd9_3_317, List.forall_mem_cons.2 ⟨subd9_3_318, List.forall_mem_cons.2 ⟨subd9_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_320 : subd9_3 [-2, 1, 7] = true := by decide +kernel
theorem subd9_3_321 : subd9_3 [-2, 1, 8] = true := by decide +kernel
theorem subd9_3_322 : subd9_3 [-2, 2, -9] = true := by decide +kernel
theorem subd9_3_323 : subd9_3 [-2, 2, -8] = true := by decide +kernel
theorem subd9_3_324 : subd9_3 [-2, 2, -7] = true := by decide +kernel
theorem subd9_3_325 : subd9_3 [-2, 2, -6] = true := by decide +kernel
theorem subd9_3_326 : subd9_3 [-2, 2, -5] = true := by decide +kernel
theorem subd9_3_327 : subd9_3 [-2, 2, -4] = true := by decide +kernel
theorem subd9_3_328 : subd9_3 [-2, 2, -3] = true := by decide +kernel
theorem subd9_3_329 : subd9_3 [-2, 2, -2] = true := by decide +kernel
theorem subd9_3_330 : subd9_3 [-2, 2, -1] = true := by decide +kernel
theorem subd9_3_331 : subd9_3 [-2, 2, 0] = true := by decide +kernel
theorem subd9_3_332 : subd9_3 [-2, 2, 1] = true := by decide +kernel
theorem subd9_3_333 : subd9_3 [-2, 2, 2] = true := by decide +kernel
theorem subd9_3_334 : subd9_3 [-2, 2, 3] = true := by decide +kernel
theorem subd9_3_335 : subd9_3 [-2, 2, 4] = true := by decide +kernel
theorem subd9_3_336 : subd9_3 [-2, 2, 5] = true := by decide +kernel
theorem subd9_3_337 : subd9_3 [-2, 2, 6] = true := by decide +kernel
theorem subd9_3_338 : subd9_3 [-2, 2, 7] = true := by decide +kernel
theorem subd9_3_339 : subd9_3 [-2, 2, 8] = true := by decide +kernel
theorem subd9_3_340 : subd9_3 [-2, 3, -9] = true := by decide +kernel
theorem subd9_3_341 : subd9_3 [-2, 3, -8] = true := by decide +kernel
theorem subd9_3_342 : subd9_3 [-2, 3, -7] = true := by decide +kernel
theorem subd9_3_343 : subd9_3 [-2, 3, -6] = true := by decide +kernel
theorem subd9_3_344 : subd9_3 [-2, 3, -5] = true := by decide +kernel
theorem subd9_3_345 : subd9_3 [-2, 3, -4] = true := by decide +kernel
theorem subd9_3_346 : subd9_3 [-2, 3, -3] = true := by decide +kernel
theorem subd9_3_347 : subd9_3 [-2, 3, -2] = true := by decide +kernel
theorem subd9_3_348 : subd9_3 [-2, 3, -1] = true := by decide +kernel
theorem subd9_3_349 : subd9_3 [-2, 3, 0] = true := by decide +kernel
theorem subd9_3_350 : subd9_3 [-2, 3, 1] = true := by decide +kernel
theorem subd9_3_351 : subd9_3 [-2, 3, 2] = true := by decide +kernel
theorem sbd9_3_10 : ∀ q ∈ blkd9_3_10, subd9_3 q = true := by
  unfold blkd9_3_10
  exact List.forall_mem_cons.2 ⟨subd9_3_320, List.forall_mem_cons.2 ⟨subd9_3_321, List.forall_mem_cons.2 ⟨subd9_3_322, List.forall_mem_cons.2 ⟨subd9_3_323, List.forall_mem_cons.2 ⟨subd9_3_324, List.forall_mem_cons.2 ⟨subd9_3_325, List.forall_mem_cons.2 ⟨subd9_3_326, List.forall_mem_cons.2 ⟨subd9_3_327, List.forall_mem_cons.2 ⟨subd9_3_328, List.forall_mem_cons.2 ⟨subd9_3_329, List.forall_mem_cons.2 ⟨subd9_3_330, List.forall_mem_cons.2 ⟨subd9_3_331, List.forall_mem_cons.2 ⟨subd9_3_332, List.forall_mem_cons.2 ⟨subd9_3_333, List.forall_mem_cons.2 ⟨subd9_3_334, List.forall_mem_cons.2 ⟨subd9_3_335, List.forall_mem_cons.2 ⟨subd9_3_336, List.forall_mem_cons.2 ⟨subd9_3_337, List.forall_mem_cons.2 ⟨subd9_3_338, List.forall_mem_cons.2 ⟨subd9_3_339, List.forall_mem_cons.2 ⟨subd9_3_340, List.forall_mem_cons.2 ⟨subd9_3_341, List.forall_mem_cons.2 ⟨subd9_3_342, List.forall_mem_cons.2 ⟨subd9_3_343, List.forall_mem_cons.2 ⟨subd9_3_344, List.forall_mem_cons.2 ⟨subd9_3_345, List.forall_mem_cons.2 ⟨subd9_3_346, List.forall_mem_cons.2 ⟨subd9_3_347, List.forall_mem_cons.2 ⟨subd9_3_348, List.forall_mem_cons.2 ⟨subd9_3_349, List.forall_mem_cons.2 ⟨subd9_3_350, List.forall_mem_cons.2 ⟨subd9_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_352 : subd9_3 [-2, 3, 3] = true := by decide +kernel
theorem subd9_3_353 : subd9_3 [-2, 3, 4] = true := by decide +kernel
theorem subd9_3_354 : subd9_3 [-2, 3, 5] = true := by decide +kernel
theorem subd9_3_355 : subd9_3 [-2, 3, 6] = true := by decide +kernel
theorem subd9_3_356 : subd9_3 [-2, 3, 7] = true := by decide +kernel
theorem subd9_3_357 : subd9_3 [-2, 4, -7] = true := by decide +kernel
theorem subd9_3_358 : subd9_3 [-2, 4, -6] = true := by decide +kernel
theorem subd9_3_359 : subd9_3 [-2, 4, -5] = true := by decide +kernel
theorem subd9_3_360 : subd9_3 [-2, 4, -4] = true := by decide +kernel
theorem subd9_3_361 : subd9_3 [-2, 4, -3] = true := by decide +kernel
theorem subd9_3_362 : subd9_3 [-2, 4, -2] = true := by decide +kernel
theorem subd9_3_363 : subd9_3 [-2, 4, -1] = true := by decide +kernel
theorem subd9_3_364 : subd9_3 [-2, 4, 0] = true := by decide +kernel
theorem subd9_3_365 : subd9_3 [-2, 4, 1] = true := by decide +kernel
theorem subd9_3_366 : subd9_3 [-2, 4, 2] = true := by decide +kernel
theorem subd9_3_367 : subd9_3 [-2, 4, 3] = true := by decide +kernel
theorem subd9_3_368 : subd9_3 [-2, 4, 4] = true := by decide +kernel
theorem subd9_3_369 : subd9_3 [-2, 4, 5] = true := by decide +kernel
theorem subd9_3_370 : subd9_3 [-2, 4, 6] = true := by decide +kernel
theorem subd9_3_371 : subd9_3 [-2, 5] = true := by decide +kernel
theorem subd9_3_372 : subd9_3 [-1, -6] = true := by decide +kernel
theorem subd9_3_373 : subd9_3 [-1, -5] = true := by decide +kernel
theorem subd9_3_374 : subd9_3 [-1, -4, -8] = true := by decide +kernel
theorem subd9_3_375 : subd9_3 [-1, -4, -7] = true := by decide +kernel
theorem subd9_3_376 : subd9_3 [-1, -4, -6] = true := by decide +kernel
theorem subd9_3_377 : subd9_3 [-1, -4, -5] = true := by decide +kernel
theorem subd9_3_378 : subd9_3 [-1, -4, -4] = true := by decide +kernel
theorem subd9_3_379 : subd9_3 [-1, -4, -3] = true := by decide +kernel
theorem subd9_3_380 : subd9_3 [-1, -4, -2] = true := by decide +kernel
theorem subd9_3_381 : subd9_3 [-1, -4, -1] = true := by decide +kernel
theorem subd9_3_382 : subd9_3 [-1, -4, 0] = true := by decide +kernel
theorem subd9_3_383 : subd9_3 [-1, -4, 1] = true := by decide +kernel
theorem sbd9_3_11 : ∀ q ∈ blkd9_3_11, subd9_3 q = true := by
  unfold blkd9_3_11
  exact List.forall_mem_cons.2 ⟨subd9_3_352, List.forall_mem_cons.2 ⟨subd9_3_353, List.forall_mem_cons.2 ⟨subd9_3_354, List.forall_mem_cons.2 ⟨subd9_3_355, List.forall_mem_cons.2 ⟨subd9_3_356, List.forall_mem_cons.2 ⟨subd9_3_357, List.forall_mem_cons.2 ⟨subd9_3_358, List.forall_mem_cons.2 ⟨subd9_3_359, List.forall_mem_cons.2 ⟨subd9_3_360, List.forall_mem_cons.2 ⟨subd9_3_361, List.forall_mem_cons.2 ⟨subd9_3_362, List.forall_mem_cons.2 ⟨subd9_3_363, List.forall_mem_cons.2 ⟨subd9_3_364, List.forall_mem_cons.2 ⟨subd9_3_365, List.forall_mem_cons.2 ⟨subd9_3_366, List.forall_mem_cons.2 ⟨subd9_3_367, List.forall_mem_cons.2 ⟨subd9_3_368, List.forall_mem_cons.2 ⟨subd9_3_369, List.forall_mem_cons.2 ⟨subd9_3_370, List.forall_mem_cons.2 ⟨subd9_3_371, List.forall_mem_cons.2 ⟨subd9_3_372, List.forall_mem_cons.2 ⟨subd9_3_373, List.forall_mem_cons.2 ⟨subd9_3_374, List.forall_mem_cons.2 ⟨subd9_3_375, List.forall_mem_cons.2 ⟨subd9_3_376, List.forall_mem_cons.2 ⟨subd9_3_377, List.forall_mem_cons.2 ⟨subd9_3_378, List.forall_mem_cons.2 ⟨subd9_3_379, List.forall_mem_cons.2 ⟨subd9_3_380, List.forall_mem_cons.2 ⟨subd9_3_381, List.forall_mem_cons.2 ⟨subd9_3_382, List.forall_mem_cons.2 ⟨subd9_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_384 : subd9_3 [-1, -4, 2] = true := by decide +kernel
theorem subd9_3_385 : subd9_3 [-1, -4, 3] = true := by decide +kernel
theorem subd9_3_386 : subd9_3 [-1, -4, 4] = true := by decide +kernel
theorem subd9_3_387 : subd9_3 [-1, -4, 5] = true := by decide +kernel
theorem subd9_3_388 : subd9_3 [-1, -4, 6] = true := by decide +kernel
theorem subd9_3_389 : subd9_3 [-1, -3, -9] = true := by decide +kernel
theorem subd9_3_390 : subd9_3 [-1, -3, -8] = true := by decide +kernel
theorem subd9_3_391 : subd9_3 [-1, -3, -7] = true := by decide +kernel
theorem subd9_3_392 : subd9_3 [-1, -3, -6] = true := by decide +kernel
theorem subd9_3_393 : subd9_3 [-1, -3, -5] = true := by decide +kernel
theorem subd9_3_394 : subd9_3 [-1, -3, -4] = true := by decide +kernel
theorem subd9_3_395 : subd9_3 [-1, -3, -3] = true := by decide +kernel
theorem subd9_3_396 : subd9_3 [-1, -3, -2] = true := by decide +kernel
theorem subd9_3_397 : subd9_3 [-1, -3, -1] = true := by decide +kernel
theorem subd9_3_398 : subd9_3 [-1, -3, 0] = true := by decide +kernel
theorem subd9_3_399 : subd9_3 [-1, -3, 1] = true := by decide +kernel
theorem subd9_3_400 : subd9_3 [-1, -3, 2] = true := by decide +kernel
theorem subd9_3_401 : subd9_3 [-1, -3, 3] = true := by decide +kernel
theorem subd9_3_402 : subd9_3 [-1, -3, 4] = true := by decide +kernel
theorem subd9_3_403 : subd9_3 [-1, -3, 5] = true := by decide +kernel
theorem subd9_3_404 : subd9_3 [-1, -3, 6] = true := by decide +kernel
theorem subd9_3_405 : subd9_3 [-1, -3, 7] = true := by decide +kernel
theorem subd9_3_406 : subd9_3 [-1, -3, 8] = true := by decide +kernel
theorem subd9_3_407 : subd9_3 [-1, -2, -10] = true := by decide +kernel
theorem subd9_3_408 : subd9_3 [-1, -2, -9] = true := by decide +kernel
theorem subd9_3_409 : subd9_3 [-1, -2, -8] = true := by decide +kernel
theorem subd9_3_410 : subd9_3 [-1, -2, -7] = true := by decide +kernel
theorem subd9_3_411 : subd9_3 [-1, -2, -6] = true := by decide +kernel
theorem subd9_3_412 : subd9_3 [-1, -2, -5] = true := by decide +kernel
theorem subd9_3_413 : subd9_3 [-1, -2, -4] = true := by decide +kernel
theorem subd9_3_414 : subd9_3 [-1, -2, -3] = true := by decide +kernel
theorem subd9_3_415 : subd9_3 [-1, -2, -2] = true := by decide +kernel
theorem sbd9_3_12 : ∀ q ∈ blkd9_3_12, subd9_3 q = true := by
  unfold blkd9_3_12
  exact List.forall_mem_cons.2 ⟨subd9_3_384, List.forall_mem_cons.2 ⟨subd9_3_385, List.forall_mem_cons.2 ⟨subd9_3_386, List.forall_mem_cons.2 ⟨subd9_3_387, List.forall_mem_cons.2 ⟨subd9_3_388, List.forall_mem_cons.2 ⟨subd9_3_389, List.forall_mem_cons.2 ⟨subd9_3_390, List.forall_mem_cons.2 ⟨subd9_3_391, List.forall_mem_cons.2 ⟨subd9_3_392, List.forall_mem_cons.2 ⟨subd9_3_393, List.forall_mem_cons.2 ⟨subd9_3_394, List.forall_mem_cons.2 ⟨subd9_3_395, List.forall_mem_cons.2 ⟨subd9_3_396, List.forall_mem_cons.2 ⟨subd9_3_397, List.forall_mem_cons.2 ⟨subd9_3_398, List.forall_mem_cons.2 ⟨subd9_3_399, List.forall_mem_cons.2 ⟨subd9_3_400, List.forall_mem_cons.2 ⟨subd9_3_401, List.forall_mem_cons.2 ⟨subd9_3_402, List.forall_mem_cons.2 ⟨subd9_3_403, List.forall_mem_cons.2 ⟨subd9_3_404, List.forall_mem_cons.2 ⟨subd9_3_405, List.forall_mem_cons.2 ⟨subd9_3_406, List.forall_mem_cons.2 ⟨subd9_3_407, List.forall_mem_cons.2 ⟨subd9_3_408, List.forall_mem_cons.2 ⟨subd9_3_409, List.forall_mem_cons.2 ⟨subd9_3_410, List.forall_mem_cons.2 ⟨subd9_3_411, List.forall_mem_cons.2 ⟨subd9_3_412, List.forall_mem_cons.2 ⟨subd9_3_413, List.forall_mem_cons.2 ⟨subd9_3_414, List.forall_mem_cons.2 ⟨subd9_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_416 : subd9_3 [-1, -2, -1] = true := by decide +kernel
theorem subd9_3_417 : subd9_3 [-1, -2, 0] = true := by decide +kernel
theorem subd9_3_418 : subd9_3 [-1, -2, 1] = true := by decide +kernel
theorem subd9_3_419 : subd9_3 [-1, -2, 2] = true := by decide +kernel
theorem subd9_3_420 : subd9_3 [-1, -2, 3] = true := by decide +kernel
theorem subd9_3_421 : subd9_3 [-1, -2, 4] = true := by decide +kernel
theorem subd9_3_422 : subd9_3 [-1, -2, 5] = true := by decide +kernel
theorem subd9_3_423 : subd9_3 [-1, -2, 6] = true := by decide +kernel
theorem subd9_3_424 : subd9_3 [-1, -2, 7] = true := by decide +kernel
theorem subd9_3_425 : subd9_3 [-1, -2, 8] = true := by decide +kernel
theorem subd9_3_426 : subd9_3 [-1, -1, -10] = true := by decide +kernel
theorem subd9_3_427 : subd9_3 [-1, -1, -9] = true := by decide +kernel
theorem subd9_3_428 : subd9_3 [-1, -1, -8] = true := by decide +kernel
theorem subd9_3_429 : subd9_3 [-1, -1, -7] = true := by decide +kernel
theorem subd9_3_430 : subd9_3 [-1, -1, -6] = true := by decide +kernel
theorem subd9_3_431 : subd9_3 [-1, -1, -5] = true := by decide +kernel
theorem subd9_3_432 : subd9_3 [-1, -1, -4] = true := by decide +kernel
theorem subd9_3_433 : subd9_3 [-1, -1, -3] = true := by decide +kernel
theorem subd9_3_434 : subd9_3 [-1, -1, -2] = true := by decide +kernel
theorem subd9_3_435 : subd9_3 [-1, -1, -1] = true := by decide +kernel
theorem subd9_3_436 : subd9_3 [-1, -1, 0] = true := by decide +kernel
theorem subd9_3_437 : subd9_3 [-1, -1, 1] = true := by decide +kernel
theorem subd9_3_438 : subd9_3 [-1, -1, 2] = true := by decide +kernel
theorem subd9_3_439 : subd9_3 [-1, -1, 3] = true := by decide +kernel
theorem subd9_3_440 : subd9_3 [-1, -1, 4] = true := by decide +kernel
theorem subd9_3_441 : subd9_3 [-1, -1, 5] = true := by decide +kernel
theorem subd9_3_442 : subd9_3 [-1, -1, 6] = true := by decide +kernel
theorem subd9_3_443 : subd9_3 [-1, -1, 7] = true := by decide +kernel
theorem subd9_3_444 : subd9_3 [-1, -1, 8] = true := by decide +kernel
theorem subd9_3_445 : subd9_3 [-1, -1, 9] = true := by decide +kernel
theorem subd9_3_446 : subd9_3 [-1, 0, -10] = true := by decide +kernel
theorem subd9_3_447 : subd9_3 [-1, 0, -9] = true := by decide +kernel
theorem sbd9_3_13 : ∀ q ∈ blkd9_3_13, subd9_3 q = true := by
  unfold blkd9_3_13
  exact List.forall_mem_cons.2 ⟨subd9_3_416, List.forall_mem_cons.2 ⟨subd9_3_417, List.forall_mem_cons.2 ⟨subd9_3_418, List.forall_mem_cons.2 ⟨subd9_3_419, List.forall_mem_cons.2 ⟨subd9_3_420, List.forall_mem_cons.2 ⟨subd9_3_421, List.forall_mem_cons.2 ⟨subd9_3_422, List.forall_mem_cons.2 ⟨subd9_3_423, List.forall_mem_cons.2 ⟨subd9_3_424, List.forall_mem_cons.2 ⟨subd9_3_425, List.forall_mem_cons.2 ⟨subd9_3_426, List.forall_mem_cons.2 ⟨subd9_3_427, List.forall_mem_cons.2 ⟨subd9_3_428, List.forall_mem_cons.2 ⟨subd9_3_429, List.forall_mem_cons.2 ⟨subd9_3_430, List.forall_mem_cons.2 ⟨subd9_3_431, List.forall_mem_cons.2 ⟨subd9_3_432, List.forall_mem_cons.2 ⟨subd9_3_433, List.forall_mem_cons.2 ⟨subd9_3_434, List.forall_mem_cons.2 ⟨subd9_3_435, List.forall_mem_cons.2 ⟨subd9_3_436, List.forall_mem_cons.2 ⟨subd9_3_437, List.forall_mem_cons.2 ⟨subd9_3_438, List.forall_mem_cons.2 ⟨subd9_3_439, List.forall_mem_cons.2 ⟨subd9_3_440, List.forall_mem_cons.2 ⟨subd9_3_441, List.forall_mem_cons.2 ⟨subd9_3_442, List.forall_mem_cons.2 ⟨subd9_3_443, List.forall_mem_cons.2 ⟨subd9_3_444, List.forall_mem_cons.2 ⟨subd9_3_445, List.forall_mem_cons.2 ⟨subd9_3_446, List.forall_mem_cons.2 ⟨subd9_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_448 : subd9_3 [-1, 0, -8] = true := by decide +kernel
theorem subd9_3_449 : subd9_3 [-1, 0, -7] = true := by decide +kernel
theorem subd9_3_450 : subd9_3 [-1, 0, -6] = true := by decide +kernel
theorem subd9_3_451 : subd9_3 [-1, 0, -5] = true := by decide +kernel
theorem subd9_3_452 : subd9_3 [-1, 0, -4] = true := by decide +kernel
theorem subd9_3_453 : subd9_3 [-1, 0, -3] = true := by decide +kernel
theorem subd9_3_454 : subd9_3 [-1, 0, -2] = true := by decide +kernel
theorem subd9_3_455 : subd9_3 [-1, 0, -1] = true := by decide +kernel
theorem subd9_3_456 : subd9_3 [-1, 0, 0] = true := by decide +kernel
theorem subd9_3_457 : subd9_3 [-1, 0, 1] = true := by decide +kernel
theorem subd9_3_458 : subd9_3 [-1, 0, 2] = true := by decide +kernel
theorem subd9_3_459 : subd9_3 [-1, 0, 3] = true := by decide +kernel
theorem subd9_3_460 : subd9_3 [-1, 0, 4] = true := by decide +kernel
theorem subd9_3_461 : subd9_3 [-1, 0, 5] = true := by decide +kernel
theorem subd9_3_462 : subd9_3 [-1, 0, 6] = true := by decide +kernel
theorem subd9_3_463 : subd9_3 [-1, 0, 7] = true := by decide +kernel
theorem subd9_3_464 : subd9_3 [-1, 0, 8] = true := by decide +kernel
theorem subd9_3_465 : subd9_3 [-1, 0, 9] = true := by decide +kernel
theorem subd9_3_466 : subd9_3 [-1, 1, -10] = true := by decide +kernel
theorem subd9_3_467 : subd9_3 [-1, 1, -9] = true := by decide +kernel
theorem subd9_3_468 : subd9_3 [-1, 1, -8] = true := by decide +kernel
theorem subd9_3_469 : subd9_3 [-1, 1, -7] = true := by decide +kernel
theorem subd9_3_470 : subd9_3 [-1, 1, -6] = true := by decide +kernel
theorem subd9_3_471 : subd9_3 [-1, 1, -5] = true := by decide +kernel
theorem subd9_3_472 : subd9_3 [-1, 1, -4] = true := by decide +kernel
theorem subd9_3_473 : subd9_3 [-1, 1, -3] = true := by decide +kernel
theorem subd9_3_474 : subd9_3 [-1, 1, -2] = true := by decide +kernel
theorem subd9_3_475 : subd9_3 [-1, 1, -1] = true := by decide +kernel
theorem subd9_3_476 : subd9_3 [-1, 1, 0] = true := by decide +kernel
theorem subd9_3_477 : subd9_3 [-1, 1, 1] = true := by decide +kernel
theorem subd9_3_478 : subd9_3 [-1, 1, 2] = true := by decide +kernel
theorem subd9_3_479 : subd9_3 [-1, 1, 3] = true := by decide +kernel
theorem sbd9_3_14 : ∀ q ∈ blkd9_3_14, subd9_3 q = true := by
  unfold blkd9_3_14
  exact List.forall_mem_cons.2 ⟨subd9_3_448, List.forall_mem_cons.2 ⟨subd9_3_449, List.forall_mem_cons.2 ⟨subd9_3_450, List.forall_mem_cons.2 ⟨subd9_3_451, List.forall_mem_cons.2 ⟨subd9_3_452, List.forall_mem_cons.2 ⟨subd9_3_453, List.forall_mem_cons.2 ⟨subd9_3_454, List.forall_mem_cons.2 ⟨subd9_3_455, List.forall_mem_cons.2 ⟨subd9_3_456, List.forall_mem_cons.2 ⟨subd9_3_457, List.forall_mem_cons.2 ⟨subd9_3_458, List.forall_mem_cons.2 ⟨subd9_3_459, List.forall_mem_cons.2 ⟨subd9_3_460, List.forall_mem_cons.2 ⟨subd9_3_461, List.forall_mem_cons.2 ⟨subd9_3_462, List.forall_mem_cons.2 ⟨subd9_3_463, List.forall_mem_cons.2 ⟨subd9_3_464, List.forall_mem_cons.2 ⟨subd9_3_465, List.forall_mem_cons.2 ⟨subd9_3_466, List.forall_mem_cons.2 ⟨subd9_3_467, List.forall_mem_cons.2 ⟨subd9_3_468, List.forall_mem_cons.2 ⟨subd9_3_469, List.forall_mem_cons.2 ⟨subd9_3_470, List.forall_mem_cons.2 ⟨subd9_3_471, List.forall_mem_cons.2 ⟨subd9_3_472, List.forall_mem_cons.2 ⟨subd9_3_473, List.forall_mem_cons.2 ⟨subd9_3_474, List.forall_mem_cons.2 ⟨subd9_3_475, List.forall_mem_cons.2 ⟨subd9_3_476, List.forall_mem_cons.2 ⟨subd9_3_477, List.forall_mem_cons.2 ⟨subd9_3_478, List.forall_mem_cons.2 ⟨subd9_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_480 : subd9_3 [-1, 1, 4] = true := by decide +kernel
theorem subd9_3_481 : subd9_3 [-1, 1, 5] = true := by decide +kernel
theorem subd9_3_482 : subd9_3 [-1, 1, 6] = true := by decide +kernel
theorem subd9_3_483 : subd9_3 [-1, 1, 7] = true := by decide +kernel
theorem subd9_3_484 : subd9_3 [-1, 1, 8] = true := by decide +kernel
theorem subd9_3_485 : subd9_3 [-1, 1, 9] = true := by decide +kernel
theorem subd9_3_486 : subd9_3 [-1, 2, -10] = true := by decide +kernel
theorem subd9_3_487 : subd9_3 [-1, 2, -9] = true := by decide +kernel
theorem subd9_3_488 : subd9_3 [-1, 2, -8] = true := by decide +kernel
theorem subd9_3_489 : subd9_3 [-1, 2, -7] = true := by decide +kernel
theorem subd9_3_490 : subd9_3 [-1, 2, -6] = true := by decide +kernel
theorem subd9_3_491 : subd9_3 [-1, 2, -5] = true := by decide +kernel
theorem subd9_3_492 : subd9_3 [-1, 2, -4] = true := by decide +kernel
theorem subd9_3_493 : subd9_3 [-1, 2, -3] = true := by decide +kernel
theorem subd9_3_494 : subd9_3 [-1, 2, -2] = true := by decide +kernel
theorem subd9_3_495 : subd9_3 [-1, 2, -1] = true := by decide +kernel
theorem subd9_3_496 : subd9_3 [-1, 2, 0] = true := by decide +kernel
theorem subd9_3_497 : subd9_3 [-1, 2, 1] = true := by decide +kernel
theorem subd9_3_498 : subd9_3 [-1, 2, 2] = true := by decide +kernel
theorem subd9_3_499 : subd9_3 [-1, 2, 3] = true := by decide +kernel
theorem subd9_3_500 : subd9_3 [-1, 2, 4] = true := by decide +kernel
theorem subd9_3_501 : subd9_3 [-1, 2, 5] = true := by decide +kernel
theorem subd9_3_502 : subd9_3 [-1, 2, 6] = true := by decide +kernel
theorem subd9_3_503 : subd9_3 [-1, 2, 7] = true := by decide +kernel
theorem subd9_3_504 : subd9_3 [-1, 2, 8] = true := by decide +kernel
theorem subd9_3_505 : subd9_3 [-1, 2, 9] = true := by decide +kernel
theorem subd9_3_506 : subd9_3 [-1, 3, -9] = true := by decide +kernel
theorem subd9_3_507 : subd9_3 [-1, 3, -8] = true := by decide +kernel
theorem subd9_3_508 : subd9_3 [-1, 3, -7] = true := by decide +kernel
theorem subd9_3_509 : subd9_3 [-1, 3, -6] = true := by decide +kernel
theorem subd9_3_510 : subd9_3 [-1, 3, -5] = true := by decide +kernel
theorem subd9_3_511 : subd9_3 [-1, 3, -4] = true := by decide +kernel
theorem sbd9_3_15 : ∀ q ∈ blkd9_3_15, subd9_3 q = true := by
  unfold blkd9_3_15
  exact List.forall_mem_cons.2 ⟨subd9_3_480, List.forall_mem_cons.2 ⟨subd9_3_481, List.forall_mem_cons.2 ⟨subd9_3_482, List.forall_mem_cons.2 ⟨subd9_3_483, List.forall_mem_cons.2 ⟨subd9_3_484, List.forall_mem_cons.2 ⟨subd9_3_485, List.forall_mem_cons.2 ⟨subd9_3_486, List.forall_mem_cons.2 ⟨subd9_3_487, List.forall_mem_cons.2 ⟨subd9_3_488, List.forall_mem_cons.2 ⟨subd9_3_489, List.forall_mem_cons.2 ⟨subd9_3_490, List.forall_mem_cons.2 ⟨subd9_3_491, List.forall_mem_cons.2 ⟨subd9_3_492, List.forall_mem_cons.2 ⟨subd9_3_493, List.forall_mem_cons.2 ⟨subd9_3_494, List.forall_mem_cons.2 ⟨subd9_3_495, List.forall_mem_cons.2 ⟨subd9_3_496, List.forall_mem_cons.2 ⟨subd9_3_497, List.forall_mem_cons.2 ⟨subd9_3_498, List.forall_mem_cons.2 ⟨subd9_3_499, List.forall_mem_cons.2 ⟨subd9_3_500, List.forall_mem_cons.2 ⟨subd9_3_501, List.forall_mem_cons.2 ⟨subd9_3_502, List.forall_mem_cons.2 ⟨subd9_3_503, List.forall_mem_cons.2 ⟨subd9_3_504, List.forall_mem_cons.2 ⟨subd9_3_505, List.forall_mem_cons.2 ⟨subd9_3_506, List.forall_mem_cons.2 ⟨subd9_3_507, List.forall_mem_cons.2 ⟨subd9_3_508, List.forall_mem_cons.2 ⟨subd9_3_509, List.forall_mem_cons.2 ⟨subd9_3_510, List.forall_mem_cons.2 ⟨subd9_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
