import ReflectZphi.Data.Cert5.C091.Base

namespace ReflectZphi.Data.Cert5.C091

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_7_64 : subd5_7 [0, -1, -8] = true := by decide +kernel
theorem subd5_7_65 : subd5_7 [0, -1, -7] = true := by decide +kernel
theorem subd5_7_66 : subd5_7 [0, -1, -6] = true := by decide +kernel
theorem subd5_7_67 : subd5_7 [0, -1, -5] = true := by decide +kernel
theorem subd5_7_68 : subd5_7 [0, -1, -4] = true := by decide +kernel
theorem subd5_7_69 : subd5_7 [0, -1, -3] = true := by decide +kernel
theorem subd5_7_70 : subd5_7 [0, -1, -2] = true := by decide +kernel
theorem subd5_7_71 : subd5_7 [0, -1, -1] = true := by decide +kernel
theorem subd5_7_72 : subd5_7 [0, -1, 0] = true := by decide +kernel
theorem subd5_7_73 : subd5_7 [0, -1, 1] = true := by decide +kernel
theorem subd5_7_74 : subd5_7 [0, -1, 2] = true := by decide +kernel
theorem subd5_7_75 : subd5_7 [0, -1, 3] = true := by decide +kernel
theorem subd5_7_76 : subd5_7 [0, -1, 4] = true := by decide +kernel
theorem subd5_7_77 : subd5_7 [0, -1, 5] = true := by decide +kernel
theorem subd5_7_78 : subd5_7 [0, -1, 6] = true := by decide +kernel
theorem subd5_7_79 : subd5_7 [0, -1, 7] = true := by decide +kernel
theorem subd5_7_80 : subd5_7 [0, -1, 8] = true := by decide +kernel
theorem subd5_7_81 : subd5_7 [0, -1, 9] = true := by decide +kernel
theorem subd5_7_82 : subd5_7 [0, -1, 10] = true := by decide +kernel
theorem subd5_7_83 : subd5_7 [0, -1, 11] = true := by decide +kernel
theorem subd5_7_84 : subd5_7 [0, -1, 12] = true := by decide +kernel
theorem subd5_7_85 : subd5_7 [0, -1, 13] = true := by decide +kernel
theorem subd5_7_86 : subd5_7 [0, -1, 14] = true := by decide +kernel
theorem subd5_7_87 : subd5_7 [0, 0, -17] = true := by decide +kernel
theorem subd5_7_88 : subd5_7 [0, 0, -16] = true := by decide +kernel
theorem subd5_7_89 : subd5_7 [0, 0, -15] = true := by decide +kernel
theorem subd5_7_90 : subd5_7 [0, 0, -14] = true := by decide +kernel
theorem subd5_7_91 : subd5_7 [0, 0, -13] = true := by decide +kernel
theorem subd5_7_92 : subd5_7 [0, 0, -12] = true := by decide +kernel
theorem subd5_7_93 : subd5_7 [0, 0, -11] = true := by decide +kernel
theorem subd5_7_94 : subd5_7 [0, 0, -10] = true := by decide +kernel
theorem subd5_7_95 : subd5_7 [0, 0, -9] = true := by decide +kernel
theorem sbd5_7_2 : ∀ q ∈ blkd5_7_2, subd5_7 q = true := by
  unfold blkd5_7_2
  exact List.forall_mem_cons.2 ⟨subd5_7_64, List.forall_mem_cons.2 ⟨subd5_7_65, List.forall_mem_cons.2 ⟨subd5_7_66, List.forall_mem_cons.2 ⟨subd5_7_67, List.forall_mem_cons.2 ⟨subd5_7_68, List.forall_mem_cons.2 ⟨subd5_7_69, List.forall_mem_cons.2 ⟨subd5_7_70, List.forall_mem_cons.2 ⟨subd5_7_71, List.forall_mem_cons.2 ⟨subd5_7_72, List.forall_mem_cons.2 ⟨subd5_7_73, List.forall_mem_cons.2 ⟨subd5_7_74, List.forall_mem_cons.2 ⟨subd5_7_75, List.forall_mem_cons.2 ⟨subd5_7_76, List.forall_mem_cons.2 ⟨subd5_7_77, List.forall_mem_cons.2 ⟨subd5_7_78, List.forall_mem_cons.2 ⟨subd5_7_79, List.forall_mem_cons.2 ⟨subd5_7_80, List.forall_mem_cons.2 ⟨subd5_7_81, List.forall_mem_cons.2 ⟨subd5_7_82, List.forall_mem_cons.2 ⟨subd5_7_83, List.forall_mem_cons.2 ⟨subd5_7_84, List.forall_mem_cons.2 ⟨subd5_7_85, List.forall_mem_cons.2 ⟨subd5_7_86, List.forall_mem_cons.2 ⟨subd5_7_87, List.forall_mem_cons.2 ⟨subd5_7_88, List.forall_mem_cons.2 ⟨subd5_7_89, List.forall_mem_cons.2 ⟨subd5_7_90, List.forall_mem_cons.2 ⟨subd5_7_91, List.forall_mem_cons.2 ⟨subd5_7_92, List.forall_mem_cons.2 ⟨subd5_7_93, List.forall_mem_cons.2 ⟨subd5_7_94, List.forall_mem_cons.2 ⟨subd5_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_96 : subd5_7 [0, 0, -8] = true := by decide +kernel
theorem subd5_7_97 : subd5_7 [0, 0, -7] = true := by decide +kernel
theorem subd5_7_98 : subd5_7 [0, 0, -6] = true := by decide +kernel
theorem subd5_7_99 : subd5_7 [0, 0, -5] = true := by decide +kernel
theorem subd5_7_100 : subd5_7 [0, 0, -4] = true := by decide +kernel
theorem subd5_7_101 : subd5_7 [0, 0, -3] = true := by decide +kernel
theorem subd5_7_102 : subd5_7 [0, 0, -2] = true := by decide +kernel
theorem subd5_7_103 : subd5_7 [0, 0, -1] = true := by decide +kernel
theorem subd5_7_104 : subd5_7 [0, 0, 0] = true := by decide +kernel
theorem subd5_7_105 : subd5_7 [0, 0, 1] = true := by decide +kernel
theorem subd5_7_106 : subd5_7 [0, 0, 2] = true := by decide +kernel
theorem subd5_7_107 : subd5_7 [0, 0, 3] = true := by decide +kernel
theorem subd5_7_108 : subd5_7 [0, 0, 4] = true := by decide +kernel
theorem subd5_7_109 : subd5_7 [0, 0, 5] = true := by decide +kernel
theorem subd5_7_110 : subd5_7 [0, 0, 6] = true := by decide +kernel
theorem subd5_7_111 : subd5_7 [0, 0, 7] = true := by decide +kernel
theorem subd5_7_112 : subd5_7 [0, 0, 8] = true := by decide +kernel
theorem subd5_7_113 : subd5_7 [0, 0, 9] = true := by decide +kernel
theorem subd5_7_114 : subd5_7 [0, 0, 10] = true := by decide +kernel
theorem subd5_7_115 : subd5_7 [0, 0, 11] = true := by decide +kernel
theorem subd5_7_116 : subd5_7 [0, 0, 12] = true := by decide +kernel
theorem subd5_7_117 : subd5_7 [0, 0, 13] = true := by decide +kernel
theorem subd5_7_118 : subd5_7 [0, 0, 14] = true := by decide +kernel
theorem subd5_7_119 : subd5_7 [0, 0, 15] = true := by decide +kernel
theorem subd5_7_120 : subd5_7 [0, 0, 16] = true := by decide +kernel
theorem subd5_7_121 : subd5_7 [0, 1, -15] = true := by decide +kernel
theorem subd5_7_122 : subd5_7 [0, 1, -14] = true := by decide +kernel
theorem subd5_7_123 : subd5_7 [0, 1, -13] = true := by decide +kernel
theorem subd5_7_124 : subd5_7 [0, 1, -12] = true := by decide +kernel
theorem subd5_7_125 : subd5_7 [0, 1, -11] = true := by decide +kernel
theorem subd5_7_126 : subd5_7 [0, 1, -10] = true := by decide +kernel
theorem subd5_7_127 : subd5_7 [0, 1, -9] = true := by decide +kernel
theorem sbd5_7_3 : ∀ q ∈ blkd5_7_3, subd5_7 q = true := by
  unfold blkd5_7_3
  exact List.forall_mem_cons.2 ⟨subd5_7_96, List.forall_mem_cons.2 ⟨subd5_7_97, List.forall_mem_cons.2 ⟨subd5_7_98, List.forall_mem_cons.2 ⟨subd5_7_99, List.forall_mem_cons.2 ⟨subd5_7_100, List.forall_mem_cons.2 ⟨subd5_7_101, List.forall_mem_cons.2 ⟨subd5_7_102, List.forall_mem_cons.2 ⟨subd5_7_103, List.forall_mem_cons.2 ⟨subd5_7_104, List.forall_mem_cons.2 ⟨subd5_7_105, List.forall_mem_cons.2 ⟨subd5_7_106, List.forall_mem_cons.2 ⟨subd5_7_107, List.forall_mem_cons.2 ⟨subd5_7_108, List.forall_mem_cons.2 ⟨subd5_7_109, List.forall_mem_cons.2 ⟨subd5_7_110, List.forall_mem_cons.2 ⟨subd5_7_111, List.forall_mem_cons.2 ⟨subd5_7_112, List.forall_mem_cons.2 ⟨subd5_7_113, List.forall_mem_cons.2 ⟨subd5_7_114, List.forall_mem_cons.2 ⟨subd5_7_115, List.forall_mem_cons.2 ⟨subd5_7_116, List.forall_mem_cons.2 ⟨subd5_7_117, List.forall_mem_cons.2 ⟨subd5_7_118, List.forall_mem_cons.2 ⟨subd5_7_119, List.forall_mem_cons.2 ⟨subd5_7_120, List.forall_mem_cons.2 ⟨subd5_7_121, List.forall_mem_cons.2 ⟨subd5_7_122, List.forall_mem_cons.2 ⟨subd5_7_123, List.forall_mem_cons.2 ⟨subd5_7_124, List.forall_mem_cons.2 ⟨subd5_7_125, List.forall_mem_cons.2 ⟨subd5_7_126, List.forall_mem_cons.2 ⟨subd5_7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_128 : subd5_7 [0, 1, -8] = true := by decide +kernel
theorem subd5_7_129 : subd5_7 [0, 1, -7] = true := by decide +kernel
theorem subd5_7_130 : subd5_7 [0, 1, -6] = true := by decide +kernel
theorem subd5_7_131 : subd5_7 [0, 1, -5] = true := by decide +kernel
theorem subd5_7_132 : subd5_7 [0, 1, -4] = true := by decide +kernel
theorem subd5_7_133 : subd5_7 [0, 1, -3] = true := by decide +kernel
theorem subd5_7_134 : subd5_7 [0, 1, -2] = true := by decide +kernel
theorem subd5_7_135 : subd5_7 [0, 1, -1] = true := by decide +kernel
theorem subd5_7_136 : subd5_7 [0, 1, 0] = true := by decide +kernel
theorem subd5_7_137 : subd5_7 [0, 1, 1] = true := by decide +kernel
theorem subd5_7_138 : subd5_7 [0, 1, 2] = true := by decide +kernel
theorem subd5_7_139 : subd5_7 [0, 1, 3] = true := by decide +kernel
theorem subd5_7_140 : subd5_7 [0, 1, 4] = true := by decide +kernel
theorem subd5_7_141 : subd5_7 [0, 1, 5] = true := by decide +kernel
theorem subd5_7_142 : subd5_7 [0, 1, 6] = true := by decide +kernel
theorem subd5_7_143 : subd5_7 [0, 1, 7] = true := by decide +kernel
theorem subd5_7_144 : subd5_7 [0, 1, 8] = true := by decide +kernel
theorem subd5_7_145 : subd5_7 [0, 1, 9] = true := by decide +kernel
theorem subd5_7_146 : subd5_7 [0, 1, 10] = true := by decide +kernel
theorem subd5_7_147 : subd5_7 [0, 1, 11] = true := by decide +kernel
theorem subd5_7_148 : subd5_7 [0, 1, 12] = true := by decide +kernel
theorem subd5_7_149 : subd5_7 [0, 1, 13] = true := by decide +kernel
theorem subd5_7_150 : subd5_7 [0, 1, 14] = true := by decide +kernel
theorem subd5_7_151 : subd5_7 [1, -2] = true := by decide +kernel
theorem subd5_7_152 : subd5_7 [1, -1] = true := by decide +kernel
theorem subd5_7_153 : subd5_7 [1, 0, -14] = true := by decide +kernel
theorem subd5_7_154 : subd5_7 [1, 0, -13] = true := by decide +kernel
theorem subd5_7_155 : subd5_7 [1, 0, -12] = true := by decide +kernel
theorem subd5_7_156 : subd5_7 [1, 0, -11] = true := by decide +kernel
theorem subd5_7_157 : subd5_7 [1, 0, -10] = true := by decide +kernel
theorem subd5_7_158 : subd5_7 [1, 0, -9] = true := by decide +kernel
theorem subd5_7_159 : subd5_7 [1, 0, -8] = true := by decide +kernel
theorem sbd5_7_4 : ∀ q ∈ blkd5_7_4, subd5_7 q = true := by
  unfold blkd5_7_4
  exact List.forall_mem_cons.2 ⟨subd5_7_128, List.forall_mem_cons.2 ⟨subd5_7_129, List.forall_mem_cons.2 ⟨subd5_7_130, List.forall_mem_cons.2 ⟨subd5_7_131, List.forall_mem_cons.2 ⟨subd5_7_132, List.forall_mem_cons.2 ⟨subd5_7_133, List.forall_mem_cons.2 ⟨subd5_7_134, List.forall_mem_cons.2 ⟨subd5_7_135, List.forall_mem_cons.2 ⟨subd5_7_136, List.forall_mem_cons.2 ⟨subd5_7_137, List.forall_mem_cons.2 ⟨subd5_7_138, List.forall_mem_cons.2 ⟨subd5_7_139, List.forall_mem_cons.2 ⟨subd5_7_140, List.forall_mem_cons.2 ⟨subd5_7_141, List.forall_mem_cons.2 ⟨subd5_7_142, List.forall_mem_cons.2 ⟨subd5_7_143, List.forall_mem_cons.2 ⟨subd5_7_144, List.forall_mem_cons.2 ⟨subd5_7_145, List.forall_mem_cons.2 ⟨subd5_7_146, List.forall_mem_cons.2 ⟨subd5_7_147, List.forall_mem_cons.2 ⟨subd5_7_148, List.forall_mem_cons.2 ⟨subd5_7_149, List.forall_mem_cons.2 ⟨subd5_7_150, List.forall_mem_cons.2 ⟨subd5_7_151, List.forall_mem_cons.2 ⟨subd5_7_152, List.forall_mem_cons.2 ⟨subd5_7_153, List.forall_mem_cons.2 ⟨subd5_7_154, List.forall_mem_cons.2 ⟨subd5_7_155, List.forall_mem_cons.2 ⟨subd5_7_156, List.forall_mem_cons.2 ⟨subd5_7_157, List.forall_mem_cons.2 ⟨subd5_7_158, List.forall_mem_cons.2 ⟨subd5_7_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_160 : subd5_7 [1, 0, -7] = true := by decide +kernel
theorem subd5_7_161 : subd5_7 [1, 0, -6] = true := by decide +kernel
theorem subd5_7_162 : subd5_7 [1, 0, -5] = true := by decide +kernel
theorem subd5_7_163 : subd5_7 [1, 0, -4] = true := by decide +kernel
theorem subd5_7_164 : subd5_7 [1, 0, -3] = true := by decide +kernel
theorem subd5_7_165 : subd5_7 [1, 0, -2] = true := by decide +kernel
theorem subd5_7_166 : subd5_7 [1, 0, -1] = true := by decide +kernel
theorem subd5_7_167 : subd5_7 [1, 0, 0] = true := by decide +kernel
theorem subd5_7_168 : subd5_7 [1, 0, 1] = true := by decide +kernel
theorem subd5_7_169 : subd5_7 [1, 0, 2] = true := by decide +kernel
theorem subd5_7_170 : subd5_7 [1, 0, 3] = true := by decide +kernel
theorem subd5_7_171 : subd5_7 [1, 0, 4] = true := by decide +kernel
theorem subd5_7_172 : subd5_7 [1, 0, 5] = true := by decide +kernel
theorem subd5_7_173 : subd5_7 [1, 0, 6] = true := by decide +kernel
theorem subd5_7_174 : subd5_7 [1, 0, 7] = true := by decide +kernel
theorem subd5_7_175 : subd5_7 [1, 0, 8] = true := by decide +kernel
theorem subd5_7_176 : subd5_7 [1, 0, 9] = true := by decide +kernel
theorem subd5_7_177 : subd5_7 [1, 0, 10] = true := by decide +kernel
theorem subd5_7_178 : subd5_7 [1, 0, 11] = true := by decide +kernel
theorem subd5_7_179 : subd5_7 [1, 0, 12] = true := by decide +kernel
theorem subd5_7_180 : subd5_7 [1, 0, 13] = true := by decide +kernel
theorem subd5_7_181 : subd5_7 [1, 1, -13] = true := by decide +kernel
theorem subd5_7_182 : subd5_7 [1, 1, -12] = true := by decide +kernel
theorem subd5_7_183 : subd5_7 [1, 1, -11] = true := by decide +kernel
theorem subd5_7_184 : subd5_7 [1, 1, -10] = true := by decide +kernel
theorem subd5_7_185 : subd5_7 [1, 1, -9] = true := by decide +kernel
theorem subd5_7_186 : subd5_7 [1, 1, -8] = true := by decide +kernel
theorem subd5_7_187 : subd5_7 [1, 1, -7] = true := by decide +kernel
theorem subd5_7_188 : subd5_7 [1, 1, -6] = true := by decide +kernel
theorem subd5_7_189 : subd5_7 [1, 1, -5] = true := by decide +kernel
theorem subd5_7_190 : subd5_7 [1, 1, -4] = true := by decide +kernel
theorem subd5_7_191 : subd5_7 [1, 1, -3] = true := by decide +kernel
theorem sbd5_7_5 : ∀ q ∈ blkd5_7_5, subd5_7 q = true := by
  unfold blkd5_7_5
  exact List.forall_mem_cons.2 ⟨subd5_7_160, List.forall_mem_cons.2 ⟨subd5_7_161, List.forall_mem_cons.2 ⟨subd5_7_162, List.forall_mem_cons.2 ⟨subd5_7_163, List.forall_mem_cons.2 ⟨subd5_7_164, List.forall_mem_cons.2 ⟨subd5_7_165, List.forall_mem_cons.2 ⟨subd5_7_166, List.forall_mem_cons.2 ⟨subd5_7_167, List.forall_mem_cons.2 ⟨subd5_7_168, List.forall_mem_cons.2 ⟨subd5_7_169, List.forall_mem_cons.2 ⟨subd5_7_170, List.forall_mem_cons.2 ⟨subd5_7_171, List.forall_mem_cons.2 ⟨subd5_7_172, List.forall_mem_cons.2 ⟨subd5_7_173, List.forall_mem_cons.2 ⟨subd5_7_174, List.forall_mem_cons.2 ⟨subd5_7_175, List.forall_mem_cons.2 ⟨subd5_7_176, List.forall_mem_cons.2 ⟨subd5_7_177, List.forall_mem_cons.2 ⟨subd5_7_178, List.forall_mem_cons.2 ⟨subd5_7_179, List.forall_mem_cons.2 ⟨subd5_7_180, List.forall_mem_cons.2 ⟨subd5_7_181, List.forall_mem_cons.2 ⟨subd5_7_182, List.forall_mem_cons.2 ⟨subd5_7_183, List.forall_mem_cons.2 ⟨subd5_7_184, List.forall_mem_cons.2 ⟨subd5_7_185, List.forall_mem_cons.2 ⟨subd5_7_186, List.forall_mem_cons.2 ⟨subd5_7_187, List.forall_mem_cons.2 ⟨subd5_7_188, List.forall_mem_cons.2 ⟨subd5_7_189, List.forall_mem_cons.2 ⟨subd5_7_190, List.forall_mem_cons.2 ⟨subd5_7_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_192 : subd5_7 [1, 1, -2] = true := by decide +kernel
theorem subd5_7_193 : subd5_7 [1, 1, -1] = true := by decide +kernel
theorem subd5_7_194 : subd5_7 [1, 1, 0] = true := by decide +kernel
theorem subd5_7_195 : subd5_7 [1, 1, 1] = true := by decide +kernel
theorem subd5_7_196 : subd5_7 [1, 1, 2] = true := by decide +kernel
theorem subd5_7_197 : subd5_7 [1, 1, 3] = true := by decide +kernel
theorem subd5_7_198 : subd5_7 [1, 1, 4] = true := by decide +kernel
theorem subd5_7_199 : subd5_7 [1, 1, 5] = true := by decide +kernel
theorem subd5_7_200 : subd5_7 [1, 1, 6] = true := by decide +kernel
theorem subd5_7_201 : subd5_7 [1, 1, 7] = true := by decide +kernel
theorem subd5_7_202 : subd5_7 [1, 1, 8] = true := by decide +kernel
theorem subd5_7_203 : subd5_7 [1, 1, 9] = true := by decide +kernel
theorem subd5_7_204 : subd5_7 [1, 1, 10] = true := by decide +kernel
theorem subd5_7_205 : subd5_7 [1, 1, 11] = true := by decide +kernel
theorem subd5_7_206 : subd5_7 [1, 1, 12] = true := by decide +kernel
theorem sbd5_7_6 : ∀ q ∈ blkd5_7_6, subd5_7 q = true := by
  unfold blkd5_7_6
  exact List.forall_mem_cons.2 ⟨subd5_7_192, List.forall_mem_cons.2 ⟨subd5_7_193, List.forall_mem_cons.2 ⟨subd5_7_194, List.forall_mem_cons.2 ⟨subd5_7_195, List.forall_mem_cons.2 ⟨subd5_7_196, List.forall_mem_cons.2 ⟨subd5_7_197, List.forall_mem_cons.2 ⟨subd5_7_198, List.forall_mem_cons.2 ⟨subd5_7_199, List.forall_mem_cons.2 ⟨subd5_7_200, List.forall_mem_cons.2 ⟨subd5_7_201, List.forall_mem_cons.2 ⟨subd5_7_202, List.forall_mem_cons.2 ⟨subd5_7_203, List.forall_mem_cons.2 ⟨subd5_7_204, List.forall_mem_cons.2 ⟨subd5_7_205, List.forall_mem_cons.2 ⟨subd5_7_206, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_0 : subd6_0 [] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_nil _⟩
theorem subd6_1_0 : subd6_1 [] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_nil _⟩
theorem subd6_2_0 : subd6_2 [] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_nil _⟩
theorem subd6_3_0 : subd6_3 [] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_nil _⟩
theorem subd6_4_0 : subd6_4 [-2] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [-1] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [0] = true := by decide +kernel
theorem subd6_4_3 : subd6_4 [1] = true := by decide +kernel
theorem subd6_4_4 : subd6_4 [2] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_cons.2 ⟨subd6_4_3, List.forall_mem_cons.2 ⟨subd6_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd6_5_0 : subd6_5 [-3] = true := by decide +kernel
theorem subd6_5_1 : subd6_5 [-2] = true := by decide +kernel
theorem subd6_5_2 : subd6_5 [-1, -4] = true := by decide +kernel
theorem subd6_5_3 : subd6_5 [-1, -3] = true := by decide +kernel
theorem subd6_5_4 : subd6_5 [-1, -2] = true := by decide +kernel
theorem subd6_5_5 : subd6_5 [-1, -1] = true := by decide +kernel
theorem subd6_5_6 : subd6_5 [-1, 0] = true := by decide +kernel
theorem subd6_5_7 : subd6_5 [-1, 1] = true := by decide +kernel
theorem subd6_5_8 : subd6_5 [-1, 2] = true := by decide +kernel
theorem subd6_5_9 : subd6_5 [-1, 3] = true := by decide +kernel
theorem subd6_5_10 : subd6_5 [-1, 4] = true := by decide +kernel
theorem subd6_5_11 : subd6_5 [0, -5] = true := by decide +kernel
theorem subd6_5_12 : subd6_5 [0, -4] = true := by decide +kernel
theorem subd6_5_13 : subd6_5 [0, -3] = true := by decide +kernel
theorem subd6_5_14 : subd6_5 [0, -2] = true := by decide +kernel
theorem subd6_5_15 : subd6_5 [0, -1] = true := by decide +kernel
theorem subd6_5_16 : subd6_5 [0, 0] = true := by decide +kernel
theorem subd6_5_17 : subd6_5 [0, 1] = true := by decide +kernel
theorem subd6_5_18 : subd6_5 [0, 2] = true := by decide +kernel
theorem subd6_5_19 : subd6_5 [0, 3] = true := by decide +kernel
theorem subd6_5_20 : subd6_5 [0, 4] = true := by decide +kernel
theorem subd6_5_21 : subd6_5 [1, -5] = true := by decide +kernel
theorem subd6_5_22 : subd6_5 [1, -4] = true := by decide +kernel
theorem subd6_5_23 : subd6_5 [1, -3] = true := by decide +kernel
theorem subd6_5_24 : subd6_5 [1, -2] = true := by decide +kernel
theorem subd6_5_25 : subd6_5 [1, -1] = true := by decide +kernel
theorem subd6_5_26 : subd6_5 [1, 0] = true := by decide +kernel
theorem subd6_5_27 : subd6_5 [1, 1] = true := by decide +kernel
theorem subd6_5_28 : subd6_5 [1, 2] = true := by decide +kernel
theorem subd6_5_29 : subd6_5 [1, 3] = true := by decide +kernel
theorem subd6_5_30 : subd6_5 [2] = true := by decide +kernel
theorem subd6_5_31 : subd6_5 [3] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_cons.2 ⟨subd6_5_1, List.forall_mem_cons.2 ⟨subd6_5_2, List.forall_mem_cons.2 ⟨subd6_5_3, List.forall_mem_cons.2 ⟨subd6_5_4, List.forall_mem_cons.2 ⟨subd6_5_5, List.forall_mem_cons.2 ⟨subd6_5_6, List.forall_mem_cons.2 ⟨subd6_5_7, List.forall_mem_cons.2 ⟨subd6_5_8, List.forall_mem_cons.2 ⟨subd6_5_9, List.forall_mem_cons.2 ⟨subd6_5_10, List.forall_mem_cons.2 ⟨subd6_5_11, List.forall_mem_cons.2 ⟨subd6_5_12, List.forall_mem_cons.2 ⟨subd6_5_13, List.forall_mem_cons.2 ⟨subd6_5_14, List.forall_mem_cons.2 ⟨subd6_5_15, List.forall_mem_cons.2 ⟨subd6_5_16, List.forall_mem_cons.2 ⟨subd6_5_17, List.forall_mem_cons.2 ⟨subd6_5_18, List.forall_mem_cons.2 ⟨subd6_5_19, List.forall_mem_cons.2 ⟨subd6_5_20, List.forall_mem_cons.2 ⟨subd6_5_21, List.forall_mem_cons.2 ⟨subd6_5_22, List.forall_mem_cons.2 ⟨subd6_5_23, List.forall_mem_cons.2 ⟨subd6_5_24, List.forall_mem_cons.2 ⟨subd6_5_25, List.forall_mem_cons.2 ⟨subd6_5_26, List.forall_mem_cons.2 ⟨subd6_5_27, List.forall_mem_cons.2 ⟨subd6_5_28, List.forall_mem_cons.2 ⟨subd6_5_29, List.forall_mem_cons.2 ⟨subd6_5_30, List.forall_mem_cons.2 ⟨subd6_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_0 : subd6_6 [-2] = true := by decide +kernel
theorem subd6_6_1 : subd6_6 [-1, -3] = true := by decide +kernel
theorem subd6_6_2 : subd6_6 [-1, -2] = true := by decide +kernel
theorem subd6_6_3 : subd6_6 [-1, -1] = true := by decide +kernel
theorem subd6_6_4 : subd6_6 [-1, 0] = true := by decide +kernel
theorem subd6_6_5 : subd6_6 [-1, 1] = true := by decide +kernel
theorem subd6_6_6 : subd6_6 [-1, 2] = true := by decide +kernel
theorem subd6_6_7 : subd6_6 [0, -3] = true := by decide +kernel
theorem subd6_6_8 : subd6_6 [0, -2] = true := by decide +kernel
theorem subd6_6_9 : subd6_6 [0, -1] = true := by decide +kernel
theorem subd6_6_10 : subd6_6 [0, 0] = true := by decide +kernel
theorem subd6_6_11 : subd6_6 [0, 1] = true := by decide +kernel
theorem subd6_6_12 : subd6_6 [0, 2] = true := by decide +kernel
theorem subd6_6_13 : subd6_6 [1, -3] = true := by decide +kernel
theorem subd6_6_14 : subd6_6 [1, -2] = true := by decide +kernel
theorem subd6_6_15 : subd6_6 [1, -1] = true := by decide +kernel
theorem subd6_6_16 : subd6_6 [1, 0] = true := by decide +kernel
theorem subd6_6_17 : subd6_6 [1, 1] = true := by decide +kernel
theorem subd6_6_18 : subd6_6 [1, 2] = true := by decide +kernel
theorem subd6_6_19 : subd6_6 [2] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_cons.2 ⟨subd6_6_1, List.forall_mem_cons.2 ⟨subd6_6_2, List.forall_mem_cons.2 ⟨subd6_6_3, List.forall_mem_cons.2 ⟨subd6_6_4, List.forall_mem_cons.2 ⟨subd6_6_5, List.forall_mem_cons.2 ⟨subd6_6_6, List.forall_mem_cons.2 ⟨subd6_6_7, List.forall_mem_cons.2 ⟨subd6_6_8, List.forall_mem_cons.2 ⟨subd6_6_9, List.forall_mem_cons.2 ⟨subd6_6_10, List.forall_mem_cons.2 ⟨subd6_6_11, List.forall_mem_cons.2 ⟨subd6_6_12, List.forall_mem_cons.2 ⟨subd6_6_13, List.forall_mem_cons.2 ⟨subd6_6_14, List.forall_mem_cons.2 ⟨subd6_6_15, List.forall_mem_cons.2 ⟨subd6_6_16, List.forall_mem_cons.2 ⟨subd6_6_17, List.forall_mem_cons.2 ⟨subd6_6_18, List.forall_mem_cons.2 ⟨subd6_6_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_7_0 : subd6_7 [-1, -2] = true := by decide +kernel
theorem subd6_7_1 : subd6_7 [-1, -1, -8] = true := by decide +kernel
theorem subd6_7_2 : subd6_7 [-1, -1, -7] = true := by decide +kernel
theorem subd6_7_3 : subd6_7 [-1, -1, -6] = true := by decide +kernel
theorem subd6_7_4 : subd6_7 [-1, -1, -5] = true := by decide +kernel
theorem subd6_7_5 : subd6_7 [-1, -1, -4] = true := by decide +kernel
theorem subd6_7_6 : subd6_7 [-1, -1, -3] = true := by decide +kernel
theorem subd6_7_7 : subd6_7 [-1, -1, -2] = true := by decide +kernel
theorem subd6_7_8 : subd6_7 [-1, -1, -1] = true := by decide +kernel
theorem subd6_7_9 : subd6_7 [-1, -1, 0] = true := by decide +kernel
theorem subd6_7_10 : subd6_7 [-1, -1, 1] = true := by decide +kernel
theorem subd6_7_11 : subd6_7 [-1, -1, 2] = true := by decide +kernel
theorem subd6_7_12 : subd6_7 [-1, -1, 3] = true := by decide +kernel
theorem subd6_7_13 : subd6_7 [-1, -1, 4] = true := by decide +kernel
theorem subd6_7_14 : subd6_7 [-1, -1, 5] = true := by decide +kernel
theorem subd6_7_15 : subd6_7 [-1, -1, 6] = true := by decide +kernel
theorem subd6_7_16 : subd6_7 [-1, -1, 7] = true := by decide +kernel
theorem subd6_7_17 : subd6_7 [-1, 0, -9] = true := by decide +kernel
theorem subd6_7_18 : subd6_7 [-1, 0, -8] = true := by decide +kernel
theorem subd6_7_19 : subd6_7 [-1, 0, -7] = true := by decide +kernel
theorem subd6_7_20 : subd6_7 [-1, 0, -6] = true := by decide +kernel
theorem subd6_7_21 : subd6_7 [-1, 0, -5] = true := by decide +kernel
theorem subd6_7_22 : subd6_7 [-1, 0, -4] = true := by decide +kernel
theorem subd6_7_23 : subd6_7 [-1, 0, -3] = true := by decide +kernel
theorem subd6_7_24 : subd6_7 [-1, 0, -2] = true := by decide +kernel
theorem subd6_7_25 : subd6_7 [-1, 0, -1] = true := by decide +kernel
theorem subd6_7_26 : subd6_7 [-1, 0, 0] = true := by decide +kernel
theorem subd6_7_27 : subd6_7 [-1, 0, 1] = true := by decide +kernel
theorem subd6_7_28 : subd6_7 [-1, 0, 2] = true := by decide +kernel
theorem subd6_7_29 : subd6_7 [-1, 0, 3] = true := by decide +kernel
theorem subd6_7_30 : subd6_7 [-1, 0, 4] = true := by decide +kernel
theorem subd6_7_31 : subd6_7 [-1, 0, 5] = true := by decide +kernel
theorem sbd6_7_0 : ∀ q ∈ blkd6_7_0, subd6_7 q = true := by
  unfold blkd6_7_0
  exact List.forall_mem_cons.2 ⟨subd6_7_0, List.forall_mem_cons.2 ⟨subd6_7_1, List.forall_mem_cons.2 ⟨subd6_7_2, List.forall_mem_cons.2 ⟨subd6_7_3, List.forall_mem_cons.2 ⟨subd6_7_4, List.forall_mem_cons.2 ⟨subd6_7_5, List.forall_mem_cons.2 ⟨subd6_7_6, List.forall_mem_cons.2 ⟨subd6_7_7, List.forall_mem_cons.2 ⟨subd6_7_8, List.forall_mem_cons.2 ⟨subd6_7_9, List.forall_mem_cons.2 ⟨subd6_7_10, List.forall_mem_cons.2 ⟨subd6_7_11, List.forall_mem_cons.2 ⟨subd6_7_12, List.forall_mem_cons.2 ⟨subd6_7_13, List.forall_mem_cons.2 ⟨subd6_7_14, List.forall_mem_cons.2 ⟨subd6_7_15, List.forall_mem_cons.2 ⟨subd6_7_16, List.forall_mem_cons.2 ⟨subd6_7_17, List.forall_mem_cons.2 ⟨subd6_7_18, List.forall_mem_cons.2 ⟨subd6_7_19, List.forall_mem_cons.2 ⟨subd6_7_20, List.forall_mem_cons.2 ⟨subd6_7_21, List.forall_mem_cons.2 ⟨subd6_7_22, List.forall_mem_cons.2 ⟨subd6_7_23, List.forall_mem_cons.2 ⟨subd6_7_24, List.forall_mem_cons.2 ⟨subd6_7_25, List.forall_mem_cons.2 ⟨subd6_7_26, List.forall_mem_cons.2 ⟨subd6_7_27, List.forall_mem_cons.2 ⟨subd6_7_28, List.forall_mem_cons.2 ⟨subd6_7_29, List.forall_mem_cons.2 ⟨subd6_7_30, List.forall_mem_cons.2 ⟨subd6_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_7_32 : subd6_7 [-1, 0, 6] = true := by decide +kernel
theorem subd6_7_33 : subd6_7 [-1, 0, 7] = true := by decide +kernel
theorem subd6_7_34 : subd6_7 [-1, 0, 8] = true := by decide +kernel
theorem subd6_7_35 : subd6_7 [-1, 1] = true := by decide +kernel
theorem subd6_7_36 : subd6_7 [0, -2] = true := by decide +kernel
theorem subd6_7_37 : subd6_7 [0, -1, -9] = true := by decide +kernel
theorem subd6_7_38 : subd6_7 [0, -1, -8] = true := by decide +kernel
theorem subd6_7_39 : subd6_7 [0, -1, -7] = true := by decide +kernel
theorem subd6_7_40 : subd6_7 [0, -1, -6] = true := by decide +kernel
theorem subd6_7_41 : subd6_7 [0, -1, -5] = true := by decide +kernel
theorem subd6_7_42 : subd6_7 [0, -1, -4] = true := by decide +kernel
theorem subd6_7_43 : subd6_7 [0, -1, -3] = true := by decide +kernel
theorem subd6_7_44 : subd6_7 [0, -1, -2] = true := by decide +kernel
theorem subd6_7_45 : subd6_7 [0, -1, -1] = true := by decide +kernel
theorem subd6_7_46 : subd6_7 [0, -1, 0] = true := by decide +kernel
theorem subd6_7_47 : subd6_7 [0, -1, 1] = true := by decide +kernel
theorem subd6_7_48 : subd6_7 [0, -1, 2] = true := by decide +kernel
theorem subd6_7_49 : subd6_7 [0, -1, 3] = true := by decide +kernel
theorem subd6_7_50 : subd6_7 [0, -1, 4] = true := by decide +kernel
theorem subd6_7_51 : subd6_7 [0, -1, 5] = true := by decide +kernel
theorem subd6_7_52 : subd6_7 [0, -1, 6] = true := by decide +kernel
theorem subd6_7_53 : subd6_7 [0, -1, 7] = true := by decide +kernel
theorem subd6_7_54 : subd6_7 [0, -1, 8] = true := by decide +kernel
theorem subd6_7_55 : subd6_7 [0, 0, -11] = true := by decide +kernel
theorem subd6_7_56 : subd6_7 [0, 0, -10] = true := by decide +kernel
theorem subd6_7_57 : subd6_7 [0, 0, -9] = true := by decide +kernel
theorem subd6_7_58 : subd6_7 [0, 0, -8] = true := by decide +kernel
theorem subd6_7_59 : subd6_7 [0, 0, -7] = true := by decide +kernel
theorem subd6_7_60 : subd6_7 [0, 0, -6] = true := by decide +kernel
theorem subd6_7_61 : subd6_7 [0, 0, -5] = true := by decide +kernel
theorem subd6_7_62 : subd6_7 [0, 0, -4] = true := by decide +kernel
theorem subd6_7_63 : subd6_7 [0, 0, -3] = true := by decide +kernel
theorem sbd6_7_1 : ∀ q ∈ blkd6_7_1, subd6_7 q = true := by
  unfold blkd6_7_1
  exact List.forall_mem_cons.2 ⟨subd6_7_32, List.forall_mem_cons.2 ⟨subd6_7_33, List.forall_mem_cons.2 ⟨subd6_7_34, List.forall_mem_cons.2 ⟨subd6_7_35, List.forall_mem_cons.2 ⟨subd6_7_36, List.forall_mem_cons.2 ⟨subd6_7_37, List.forall_mem_cons.2 ⟨subd6_7_38, List.forall_mem_cons.2 ⟨subd6_7_39, List.forall_mem_cons.2 ⟨subd6_7_40, List.forall_mem_cons.2 ⟨subd6_7_41, List.forall_mem_cons.2 ⟨subd6_7_42, List.forall_mem_cons.2 ⟨subd6_7_43, List.forall_mem_cons.2 ⟨subd6_7_44, List.forall_mem_cons.2 ⟨subd6_7_45, List.forall_mem_cons.2 ⟨subd6_7_46, List.forall_mem_cons.2 ⟨subd6_7_47, List.forall_mem_cons.2 ⟨subd6_7_48, List.forall_mem_cons.2 ⟨subd6_7_49, List.forall_mem_cons.2 ⟨subd6_7_50, List.forall_mem_cons.2 ⟨subd6_7_51, List.forall_mem_cons.2 ⟨subd6_7_52, List.forall_mem_cons.2 ⟨subd6_7_53, List.forall_mem_cons.2 ⟨subd6_7_54, List.forall_mem_cons.2 ⟨subd6_7_55, List.forall_mem_cons.2 ⟨subd6_7_56, List.forall_mem_cons.2 ⟨subd6_7_57, List.forall_mem_cons.2 ⟨subd6_7_58, List.forall_mem_cons.2 ⟨subd6_7_59, List.forall_mem_cons.2 ⟨subd6_7_60, List.forall_mem_cons.2 ⟨subd6_7_61, List.forall_mem_cons.2 ⟨subd6_7_62, List.forall_mem_cons.2 ⟨subd6_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_7_64 : subd6_7 [0, 0, -2] = true := by decide +kernel
theorem subd6_7_65 : subd6_7 [0, 0, -1] = true := by decide +kernel
theorem subd6_7_66 : subd6_7 [0, 0, 0] = true := by decide +kernel
theorem subd6_7_67 : subd6_7 [0, 0, 1] = true := by decide +kernel
theorem subd6_7_68 : subd6_7 [0, 0, 2] = true := by decide +kernel
theorem subd6_7_69 : subd6_7 [0, 0, 3] = true := by decide +kernel
theorem subd6_7_70 : subd6_7 [0, 0, 4] = true := by decide +kernel
theorem subd6_7_71 : subd6_7 [0, 0, 5] = true := by decide +kernel
theorem subd6_7_72 : subd6_7 [0, 0, 6] = true := by decide +kernel
theorem subd6_7_73 : subd6_7 [0, 0, 7] = true := by decide +kernel
theorem subd6_7_74 : subd6_7 [0, 0, 8] = true := by decide +kernel
theorem subd6_7_75 : subd6_7 [0, 0, 9] = true := by decide +kernel
theorem subd6_7_76 : subd6_7 [0, 0, 10] = true := by decide +kernel
theorem subd6_7_77 : subd6_7 [0, 1, -9] = true := by decide +kernel
theorem subd6_7_78 : subd6_7 [0, 1, -8] = true := by decide +kernel
theorem subd6_7_79 : subd6_7 [0, 1, -7] = true := by decide +kernel
theorem subd6_7_80 : subd6_7 [0, 1, -6] = true := by decide +kernel
theorem subd6_7_81 : subd6_7 [0, 1, -5] = true := by decide +kernel
theorem subd6_7_82 : subd6_7 [0, 1, -4] = true := by decide +kernel
theorem subd6_7_83 : subd6_7 [0, 1, -3] = true := by decide +kernel
theorem subd6_7_84 : subd6_7 [0, 1, -2] = true := by decide +kernel
theorem subd6_7_85 : subd6_7 [0, 1, -1] = true := by decide +kernel
theorem subd6_7_86 : subd6_7 [0, 1, 0] = true := by decide +kernel
theorem subd6_7_87 : subd6_7 [0, 1, 1] = true := by decide +kernel
theorem subd6_7_88 : subd6_7 [0, 1, 2] = true := by decide +kernel
theorem subd6_7_89 : subd6_7 [0, 1, 3] = true := by decide +kernel
theorem subd6_7_90 : subd6_7 [0, 1, 4] = true := by decide +kernel
theorem subd6_7_91 : subd6_7 [0, 1, 5] = true := by decide +kernel
theorem subd6_7_92 : subd6_7 [0, 1, 6] = true := by decide +kernel
theorem subd6_7_93 : subd6_7 [0, 1, 7] = true := by decide +kernel
theorem subd6_7_94 : subd6_7 [0, 1, 8] = true := by decide +kernel
theorem subd6_7_95 : subd6_7 [1, -2] = true := by decide +kernel
theorem sbd6_7_2 : ∀ q ∈ blkd6_7_2, subd6_7 q = true := by
  unfold blkd6_7_2
  exact List.forall_mem_cons.2 ⟨subd6_7_64, List.forall_mem_cons.2 ⟨subd6_7_65, List.forall_mem_cons.2 ⟨subd6_7_66, List.forall_mem_cons.2 ⟨subd6_7_67, List.forall_mem_cons.2 ⟨subd6_7_68, List.forall_mem_cons.2 ⟨subd6_7_69, List.forall_mem_cons.2 ⟨subd6_7_70, List.forall_mem_cons.2 ⟨subd6_7_71, List.forall_mem_cons.2 ⟨subd6_7_72, List.forall_mem_cons.2 ⟨subd6_7_73, List.forall_mem_cons.2 ⟨subd6_7_74, List.forall_mem_cons.2 ⟨subd6_7_75, List.forall_mem_cons.2 ⟨subd6_7_76, List.forall_mem_cons.2 ⟨subd6_7_77, List.forall_mem_cons.2 ⟨subd6_7_78, List.forall_mem_cons.2 ⟨subd6_7_79, List.forall_mem_cons.2 ⟨subd6_7_80, List.forall_mem_cons.2 ⟨subd6_7_81, List.forall_mem_cons.2 ⟨subd6_7_82, List.forall_mem_cons.2 ⟨subd6_7_83, List.forall_mem_cons.2 ⟨subd6_7_84, List.forall_mem_cons.2 ⟨subd6_7_85, List.forall_mem_cons.2 ⟨subd6_7_86, List.forall_mem_cons.2 ⟨subd6_7_87, List.forall_mem_cons.2 ⟨subd6_7_88, List.forall_mem_cons.2 ⟨subd6_7_89, List.forall_mem_cons.2 ⟨subd6_7_90, List.forall_mem_cons.2 ⟨subd6_7_91, List.forall_mem_cons.2 ⟨subd6_7_92, List.forall_mem_cons.2 ⟨subd6_7_93, List.forall_mem_cons.2 ⟨subd6_7_94, List.forall_mem_cons.2 ⟨subd6_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C091
