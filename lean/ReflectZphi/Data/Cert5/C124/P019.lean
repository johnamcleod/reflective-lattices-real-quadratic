import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_8_96 : subd6_8 [0, -1, -29] = true := by decide +kernel
theorem subd6_8_97 : subd6_8 [0, -1, -28] = true := by decide +kernel
theorem subd6_8_98 : subd6_8 [0, -1, -27] = true := by decide +kernel
theorem subd6_8_99 : subd6_8 [0, -1, -26] = true := by decide +kernel
theorem subd6_8_100 : subd6_8 [0, -1, -25] = true := by decide +kernel
theorem subd6_8_101 : subd6_8 [0, -1, -24] = true := by decide +kernel
theorem subd6_8_102 : subd6_8 [0, -1, -23] = true := by decide +kernel
theorem subd6_8_103 : subd6_8 [0, -1, -22] = true := by decide +kernel
theorem subd6_8_104 : subd6_8 [0, -1, -21] = true := by decide +kernel
theorem subd6_8_105 : subd6_8 [0, -1, -20] = true := by decide +kernel
theorem subd6_8_106 : subd6_8 [0, -1, -19] = true := by decide +kernel
theorem subd6_8_107 : subd6_8 [0, -1, -18] = true := by decide +kernel
theorem subd6_8_108 : subd6_8 [0, -1, -17] = true := by decide +kernel
theorem subd6_8_109 : subd6_8 [0, -1, -16] = true := by decide +kernel
theorem subd6_8_110 : subd6_8 [0, -1, -15] = true := by decide +kernel
theorem subd6_8_111 : subd6_8 [0, -1, -14] = true := by decide +kernel
theorem subd6_8_112 : subd6_8 [0, -1, -13] = true := by decide +kernel
theorem subd6_8_113 : subd6_8 [0, -1, -12] = true := by decide +kernel
theorem subd6_8_114 : subd6_8 [0, -1, -11] = true := by decide +kernel
theorem subd6_8_115 : subd6_8 [0, -1, -10] = true := by decide +kernel
theorem subd6_8_116 : subd6_8 [0, -1, -9] = true := by decide +kernel
theorem subd6_8_117 : subd6_8 [0, -1, -8] = true := by decide +kernel
theorem subd6_8_118 : subd6_8 [0, -1, -7] = true := by decide +kernel
theorem subd6_8_119 : subd6_8 [0, -1, -6] = true := by decide +kernel
theorem subd6_8_120 : subd6_8 [0, -1, -5] = true := by decide +kernel
theorem subd6_8_121 : subd6_8 [0, -1, -4] = true := by decide +kernel
theorem subd6_8_122 : subd6_8 [0, -1, -3] = true := by decide +kernel
theorem subd6_8_123 : subd6_8 [0, -1, -2] = true := by decide +kernel
theorem subd6_8_124 : subd6_8 [0, -1, -1] = true := by decide +kernel
theorem subd6_8_125 : subd6_8 [0, -1, 0] = true := by decide +kernel
theorem subd6_8_126 : subd6_8 [0, -1, 1] = true := by decide +kernel
theorem subd6_8_127 : subd6_8 [0, -1, 2] = true := by decide +kernel
theorem sbd6_8_3 : ∀ q ∈ blkd6_8_3, subd6_8 q = true := by
  unfold blkd6_8_3
  exact List.forall_mem_cons.2 ⟨subd6_8_96, List.forall_mem_cons.2 ⟨subd6_8_97, List.forall_mem_cons.2 ⟨subd6_8_98, List.forall_mem_cons.2 ⟨subd6_8_99, List.forall_mem_cons.2 ⟨subd6_8_100, List.forall_mem_cons.2 ⟨subd6_8_101, List.forall_mem_cons.2 ⟨subd6_8_102, List.forall_mem_cons.2 ⟨subd6_8_103, List.forall_mem_cons.2 ⟨subd6_8_104, List.forall_mem_cons.2 ⟨subd6_8_105, List.forall_mem_cons.2 ⟨subd6_8_106, List.forall_mem_cons.2 ⟨subd6_8_107, List.forall_mem_cons.2 ⟨subd6_8_108, List.forall_mem_cons.2 ⟨subd6_8_109, List.forall_mem_cons.2 ⟨subd6_8_110, List.forall_mem_cons.2 ⟨subd6_8_111, List.forall_mem_cons.2 ⟨subd6_8_112, List.forall_mem_cons.2 ⟨subd6_8_113, List.forall_mem_cons.2 ⟨subd6_8_114, List.forall_mem_cons.2 ⟨subd6_8_115, List.forall_mem_cons.2 ⟨subd6_8_116, List.forall_mem_cons.2 ⟨subd6_8_117, List.forall_mem_cons.2 ⟨subd6_8_118, List.forall_mem_cons.2 ⟨subd6_8_119, List.forall_mem_cons.2 ⟨subd6_8_120, List.forall_mem_cons.2 ⟨subd6_8_121, List.forall_mem_cons.2 ⟨subd6_8_122, List.forall_mem_cons.2 ⟨subd6_8_123, List.forall_mem_cons.2 ⟨subd6_8_124, List.forall_mem_cons.2 ⟨subd6_8_125, List.forall_mem_cons.2 ⟨subd6_8_126, List.forall_mem_cons.2 ⟨subd6_8_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_8_128 : subd6_8 [0, -1, 3] = true := by decide +kernel
theorem subd6_8_129 : subd6_8 [0, -1, 4] = true := by decide +kernel
theorem subd6_8_130 : subd6_8 [0, -1, 5] = true := by decide +kernel
theorem subd6_8_131 : subd6_8 [0, -1, 6] = true := by decide +kernel
theorem subd6_8_132 : subd6_8 [0, -1, 7] = true := by decide +kernel
theorem subd6_8_133 : subd6_8 [0, -1, 8] = true := by decide +kernel
theorem subd6_8_134 : subd6_8 [0, -1, 9] = true := by decide +kernel
theorem subd6_8_135 : subd6_8 [0, -1, 10] = true := by decide +kernel
theorem subd6_8_136 : subd6_8 [0, -1, 11] = true := by decide +kernel
theorem subd6_8_137 : subd6_8 [0, -1, 12] = true := by decide +kernel
theorem subd6_8_138 : subd6_8 [0, -1, 13] = true := by decide +kernel
theorem subd6_8_139 : subd6_8 [0, -1, 14] = true := by decide +kernel
theorem subd6_8_140 : subd6_8 [0, -1, 15] = true := by decide +kernel
theorem subd6_8_141 : subd6_8 [0, -1, 16] = true := by decide +kernel
theorem subd6_8_142 : subd6_8 [0, -1, 17] = true := by decide +kernel
theorem subd6_8_143 : subd6_8 [0, -1, 18] = true := by decide +kernel
theorem subd6_8_144 : subd6_8 [0, -1, 19] = true := by decide +kernel
theorem subd6_8_145 : subd6_8 [0, -1, 20] = true := by decide +kernel
theorem subd6_8_146 : subd6_8 [0, -1, 21] = true := by decide +kernel
theorem subd6_8_147 : subd6_8 [0, -1, 22] = true := by decide +kernel
theorem subd6_8_148 : subd6_8 [0, -1, 23] = true := by decide +kernel
theorem subd6_8_149 : subd6_8 [0, -1, 24] = true := by decide +kernel
theorem subd6_8_150 : subd6_8 [0, -1, 25] = true := by decide +kernel
theorem subd6_8_151 : subd6_8 [0, -1, 26] = true := by decide +kernel
theorem subd6_8_152 : subd6_8 [0, -1, 27] = true := by decide +kernel
theorem subd6_8_153 : subd6_8 [0, -1, 28] = true := by decide +kernel
theorem subd6_8_154 : subd6_8 [0, -1, 29] = true := by decide +kernel
theorem subd6_8_155 : subd6_8 [0, -1, 30] = true := by decide +kernel
theorem subd6_8_156 : subd6_8 [0, 0, -43] = true := by decide +kernel
theorem subd6_8_157 : subd6_8 [0, 0, -42] = true := by decide +kernel
theorem subd6_8_158 : subd6_8 [0, 0, -41] = true := by decide +kernel
theorem subd6_8_159 : subd6_8 [0, 0, -40] = true := by decide +kernel
theorem sbd6_8_4 : ∀ q ∈ blkd6_8_4, subd6_8 q = true := by
  unfold blkd6_8_4
  exact List.forall_mem_cons.2 ⟨subd6_8_128, List.forall_mem_cons.2 ⟨subd6_8_129, List.forall_mem_cons.2 ⟨subd6_8_130, List.forall_mem_cons.2 ⟨subd6_8_131, List.forall_mem_cons.2 ⟨subd6_8_132, List.forall_mem_cons.2 ⟨subd6_8_133, List.forall_mem_cons.2 ⟨subd6_8_134, List.forall_mem_cons.2 ⟨subd6_8_135, List.forall_mem_cons.2 ⟨subd6_8_136, List.forall_mem_cons.2 ⟨subd6_8_137, List.forall_mem_cons.2 ⟨subd6_8_138, List.forall_mem_cons.2 ⟨subd6_8_139, List.forall_mem_cons.2 ⟨subd6_8_140, List.forall_mem_cons.2 ⟨subd6_8_141, List.forall_mem_cons.2 ⟨subd6_8_142, List.forall_mem_cons.2 ⟨subd6_8_143, List.forall_mem_cons.2 ⟨subd6_8_144, List.forall_mem_cons.2 ⟨subd6_8_145, List.forall_mem_cons.2 ⟨subd6_8_146, List.forall_mem_cons.2 ⟨subd6_8_147, List.forall_mem_cons.2 ⟨subd6_8_148, List.forall_mem_cons.2 ⟨subd6_8_149, List.forall_mem_cons.2 ⟨subd6_8_150, List.forall_mem_cons.2 ⟨subd6_8_151, List.forall_mem_cons.2 ⟨subd6_8_152, List.forall_mem_cons.2 ⟨subd6_8_153, List.forall_mem_cons.2 ⟨subd6_8_154, List.forall_mem_cons.2 ⟨subd6_8_155, List.forall_mem_cons.2 ⟨subd6_8_156, List.forall_mem_cons.2 ⟨subd6_8_157, List.forall_mem_cons.2 ⟨subd6_8_158, List.forall_mem_cons.2 ⟨subd6_8_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_8_160 : subd6_8 [0, 0, -39] = true := by decide +kernel
theorem subd6_8_161 : subd6_8 [0, 0, -38] = true := by decide +kernel
theorem subd6_8_162 : subd6_8 [0, 0, -37] = true := by decide +kernel
theorem subd6_8_163 : subd6_8 [0, 0, -36] = true := by decide +kernel
theorem subd6_8_164 : subd6_8 [0, 0, -35] = true := by decide +kernel
theorem subd6_8_165 : subd6_8 [0, 0, -34] = true := by decide +kernel
theorem subd6_8_166 : subd6_8 [0, 0, -33] = true := by decide +kernel
theorem subd6_8_167 : subd6_8 [0, 0, -32] = true := by decide +kernel
theorem subd6_8_168 : subd6_8 [0, 0, -31] = true := by decide +kernel
theorem subd6_8_169 : subd6_8 [0, 0, -30] = true := by decide +kernel
theorem subd6_8_170 : subd6_8 [0, 0, -29] = true := by decide +kernel
theorem subd6_8_171 : subd6_8 [0, 0, -28] = true := by decide +kernel
theorem subd6_8_172 : subd6_8 [0, 0, -27] = true := by decide +kernel
theorem subd6_8_173 : subd6_8 [0, 0, -26] = true := by decide +kernel
theorem subd6_8_174 : subd6_8 [0, 0, -25] = true := by decide +kernel
theorem subd6_8_175 : subd6_8 [0, 0, -24] = true := by decide +kernel
theorem subd6_8_176 : subd6_8 [0, 0, -23] = true := by decide +kernel
theorem subd6_8_177 : subd6_8 [0, 0, -22] = true := by decide +kernel
theorem subd6_8_178 : subd6_8 [0, 0, -21] = true := by decide +kernel
theorem subd6_8_179 : subd6_8 [0, 0, -20] = true := by decide +kernel
theorem subd6_8_180 : subd6_8 [0, 0, -19] = true := by decide +kernel
theorem subd6_8_181 : subd6_8 [0, 0, -18] = true := by decide +kernel
theorem subd6_8_182 : subd6_8 [0, 0, -17] = true := by decide +kernel
theorem subd6_8_183 : subd6_8 [0, 0, -16] = true := by decide +kernel
theorem subd6_8_184 : subd6_8 [0, 0, -15] = true := by decide +kernel
theorem subd6_8_185 : subd6_8 [0, 0, -14] = true := by decide +kernel
theorem subd6_8_186 : subd6_8 [0, 0, -13] = true := by decide +kernel
theorem subd6_8_187 : subd6_8 [0, 0, -12] = true := by decide +kernel
theorem subd6_8_188 : subd6_8 [0, 0, -11] = true := by decide +kernel
theorem subd6_8_189 : subd6_8 [0, 0, -10] = true := by decide +kernel
theorem subd6_8_190 : subd6_8 [0, 0, -9] = true := by decide +kernel
theorem subd6_8_191 : subd6_8 [0, 0, -8] = true := by decide +kernel
theorem sbd6_8_5 : ∀ q ∈ blkd6_8_5, subd6_8 q = true := by
  unfold blkd6_8_5
  exact List.forall_mem_cons.2 ⟨subd6_8_160, List.forall_mem_cons.2 ⟨subd6_8_161, List.forall_mem_cons.2 ⟨subd6_8_162, List.forall_mem_cons.2 ⟨subd6_8_163, List.forall_mem_cons.2 ⟨subd6_8_164, List.forall_mem_cons.2 ⟨subd6_8_165, List.forall_mem_cons.2 ⟨subd6_8_166, List.forall_mem_cons.2 ⟨subd6_8_167, List.forall_mem_cons.2 ⟨subd6_8_168, List.forall_mem_cons.2 ⟨subd6_8_169, List.forall_mem_cons.2 ⟨subd6_8_170, List.forall_mem_cons.2 ⟨subd6_8_171, List.forall_mem_cons.2 ⟨subd6_8_172, List.forall_mem_cons.2 ⟨subd6_8_173, List.forall_mem_cons.2 ⟨subd6_8_174, List.forall_mem_cons.2 ⟨subd6_8_175, List.forall_mem_cons.2 ⟨subd6_8_176, List.forall_mem_cons.2 ⟨subd6_8_177, List.forall_mem_cons.2 ⟨subd6_8_178, List.forall_mem_cons.2 ⟨subd6_8_179, List.forall_mem_cons.2 ⟨subd6_8_180, List.forall_mem_cons.2 ⟨subd6_8_181, List.forall_mem_cons.2 ⟨subd6_8_182, List.forall_mem_cons.2 ⟨subd6_8_183, List.forall_mem_cons.2 ⟨subd6_8_184, List.forall_mem_cons.2 ⟨subd6_8_185, List.forall_mem_cons.2 ⟨subd6_8_186, List.forall_mem_cons.2 ⟨subd6_8_187, List.forall_mem_cons.2 ⟨subd6_8_188, List.forall_mem_cons.2 ⟨subd6_8_189, List.forall_mem_cons.2 ⟨subd6_8_190, List.forall_mem_cons.2 ⟨subd6_8_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
