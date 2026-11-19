import ReflectZphi.Data.Cert5.C076.Base

namespace ReflectZphi.Data.Cert5.C076
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_96 : sub6 [-1, 0, 5] = true := by decide +kernel
theorem sub6_97 : sub6 [-1, 0, 6] = true := by decide +kernel
theorem sub6_98 : sub6 [-1, 1] = true := by decide +kernel
theorem sub6_99 : sub6 [-1, 2] = true := by decide +kernel
theorem sub6_100 : sub6 [-1, 3] = true := by decide +kernel
theorem sub6_101 : sub6 [-1, 4] = true := by decide +kernel
theorem sub6_102 : sub6 [-1, 5] = true := by decide +kernel
theorem sub6_103 : sub6 [-1, 6] = true := by decide +kernel
theorem sub6_104 : sub6 [0, -8] = true := by decide +kernel
theorem sub6_105 : sub6 [0, -7] = true := by decide +kernel
theorem sub6_106 : sub6 [0, -6] = true := by decide +kernel
theorem sub6_107 : sub6 [0, -5] = true := by decide +kernel
theorem sub6_108 : sub6 [0, -4] = true := by decide +kernel
theorem sub6_109 : sub6 [0, -3] = true := by decide +kernel
theorem sub6_110 : sub6 [0, -2] = true := by decide +kernel
theorem sub6_111 : sub6 [0, -1, -7] = true := by decide +kernel
theorem sub6_112 : sub6 [0, -1, -6] = true := by decide +kernel
theorem sub6_113 : sub6 [0, -1, -5] = true := by decide +kernel
theorem sub6_114 : sub6 [0, -1, -4] = true := by decide +kernel
theorem sub6_115 : sub6 [0, -1, -3] = true := by decide +kernel
theorem sub6_116 : sub6 [0, -1, -2] = true := by decide +kernel
theorem sub6_117 : sub6 [0, -1, -1] = true := by decide +kernel
theorem sub6_118 : sub6 [0, -1, 0] = true := by decide +kernel
theorem sub6_119 : sub6 [0, -1, 1] = true := by decide +kernel
theorem sub6_120 : sub6 [0, -1, 2] = true := by decide +kernel
theorem sub6_121 : sub6 [0, -1, 3] = true := by decide +kernel
theorem sub6_122 : sub6 [0, -1, 4] = true := by decide +kernel
theorem sub6_123 : sub6 [0, -1, 5] = true := by decide +kernel
theorem sub6_124 : sub6 [0, -1, 6] = true := by decide +kernel
theorem sub6_125 : sub6 [0, 0, -7] = true := by decide +kernel
theorem sub6_126 : sub6 [0, 0, -6] = true := by decide +kernel
theorem sub6_127 : sub6 [0, 0, -5] = true := by decide +kernel
theorem sb6_3 : ∀ q ∈ blk6_3, sub6 q = true := by
  unfold blk6_3
  exact List.forall_mem_cons.2 ⟨sub6_96, List.forall_mem_cons.2 ⟨sub6_97, List.forall_mem_cons.2 ⟨sub6_98, List.forall_mem_cons.2 ⟨sub6_99, List.forall_mem_cons.2 ⟨sub6_100, List.forall_mem_cons.2 ⟨sub6_101, List.forall_mem_cons.2 ⟨sub6_102, List.forall_mem_cons.2 ⟨sub6_103, List.forall_mem_cons.2 ⟨sub6_104, List.forall_mem_cons.2 ⟨sub6_105, List.forall_mem_cons.2 ⟨sub6_106, List.forall_mem_cons.2 ⟨sub6_107, List.forall_mem_cons.2 ⟨sub6_108, List.forall_mem_cons.2 ⟨sub6_109, List.forall_mem_cons.2 ⟨sub6_110, List.forall_mem_cons.2 ⟨sub6_111, List.forall_mem_cons.2 ⟨sub6_112, List.forall_mem_cons.2 ⟨sub6_113, List.forall_mem_cons.2 ⟨sub6_114, List.forall_mem_cons.2 ⟨sub6_115, List.forall_mem_cons.2 ⟨sub6_116, List.forall_mem_cons.2 ⟨sub6_117, List.forall_mem_cons.2 ⟨sub6_118, List.forall_mem_cons.2 ⟨sub6_119, List.forall_mem_cons.2 ⟨sub6_120, List.forall_mem_cons.2 ⟨sub6_121, List.forall_mem_cons.2 ⟨sub6_122, List.forall_mem_cons.2 ⟨sub6_123, List.forall_mem_cons.2 ⟨sub6_124, List.forall_mem_cons.2 ⟨sub6_125, List.forall_mem_cons.2 ⟨sub6_126, List.forall_mem_cons.2 ⟨sub6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_128 : sub6 [0, 0, -4] = true := by decide +kernel
theorem sub6_129 : sub6 [0, 0, -3] = true := by decide +kernel
theorem sub6_130 : sub6 [0, 0, -2] = true := by decide +kernel
theorem sub6_131 : sub6 [0, 0, -1] = true := by decide +kernel
theorem sub6_132 : sub6 [0, 0, 0] = true := by decide +kernel
theorem sub6_133 : sub6 [0, 0, 1] = true := by decide +kernel
theorem sub6_134 : sub6 [0, 0, 2] = true := by decide +kernel
theorem sub6_135 : sub6 [0, 0, 3] = true := by decide +kernel
theorem sub6_136 : sub6 [0, 0, 4] = true := by decide +kernel
theorem sub6_137 : sub6 [0, 0, 5] = true := by decide +kernel
theorem sub6_138 : sub6 [0, 0, 6] = true := by decide +kernel
theorem sub6_139 : sub6 [0, 1, -7] = true := by decide +kernel
theorem sub6_140 : sub6 [0, 1, -6] = true := by decide +kernel
theorem sub6_141 : sub6 [0, 1, -5] = true := by decide +kernel
theorem sub6_142 : sub6 [0, 1, -4] = true := by decide +kernel
theorem sub6_143 : sub6 [0, 1, -3] = true := by decide +kernel
theorem sub6_144 : sub6 [0, 1, -2] = true := by decide +kernel
theorem sub6_145 : sub6 [0, 1, -1] = true := by decide +kernel
theorem sub6_146 : sub6 [0, 1, 0] = true := by decide +kernel
theorem sub6_147 : sub6 [0, 1, 1] = true := by decide +kernel
theorem sub6_148 : sub6 [0, 1, 2] = true := by decide +kernel
theorem sub6_149 : sub6 [0, 1, 3] = true := by decide +kernel
theorem sub6_150 : sub6 [0, 1, 4] = true := by decide +kernel
theorem sub6_151 : sub6 [0, 1, 5] = true := by decide +kernel
theorem sub6_152 : sub6 [0, 1, 6] = true := by decide +kernel
theorem sub6_153 : sub6 [0, 2] = true := by decide +kernel
theorem sub6_154 : sub6 [0, 3] = true := by decide +kernel
theorem sub6_155 : sub6 [0, 4] = true := by decide +kernel
theorem sub6_156 : sub6 [0, 5] = true := by decide +kernel
theorem sub6_157 : sub6 [0, 6] = true := by decide +kernel
theorem sub6_158 : sub6 [0, 7] = true := by decide +kernel
theorem sub6_159 : sub6 [1, -7] = true := by decide +kernel
theorem sb6_4 : ∀ q ∈ blk6_4, sub6 q = true := by
  unfold blk6_4
  exact List.forall_mem_cons.2 ⟨sub6_128, List.forall_mem_cons.2 ⟨sub6_129, List.forall_mem_cons.2 ⟨sub6_130, List.forall_mem_cons.2 ⟨sub6_131, List.forall_mem_cons.2 ⟨sub6_132, List.forall_mem_cons.2 ⟨sub6_133, List.forall_mem_cons.2 ⟨sub6_134, List.forall_mem_cons.2 ⟨sub6_135, List.forall_mem_cons.2 ⟨sub6_136, List.forall_mem_cons.2 ⟨sub6_137, List.forall_mem_cons.2 ⟨sub6_138, List.forall_mem_cons.2 ⟨sub6_139, List.forall_mem_cons.2 ⟨sub6_140, List.forall_mem_cons.2 ⟨sub6_141, List.forall_mem_cons.2 ⟨sub6_142, List.forall_mem_cons.2 ⟨sub6_143, List.forall_mem_cons.2 ⟨sub6_144, List.forall_mem_cons.2 ⟨sub6_145, List.forall_mem_cons.2 ⟨sub6_146, List.forall_mem_cons.2 ⟨sub6_147, List.forall_mem_cons.2 ⟨sub6_148, List.forall_mem_cons.2 ⟨sub6_149, List.forall_mem_cons.2 ⟨sub6_150, List.forall_mem_cons.2 ⟨sub6_151, List.forall_mem_cons.2 ⟨sub6_152, List.forall_mem_cons.2 ⟨sub6_153, List.forall_mem_cons.2 ⟨sub6_154, List.forall_mem_cons.2 ⟨sub6_155, List.forall_mem_cons.2 ⟨sub6_156, List.forall_mem_cons.2 ⟨sub6_157, List.forall_mem_cons.2 ⟨sub6_158, List.forall_mem_cons.2 ⟨sub6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_160 : sub6 [1, -6] = true := by decide +kernel
theorem sub6_161 : sub6 [1, -5] = true := by decide +kernel
theorem sub6_162 : sub6 [1, -4] = true := by decide +kernel
theorem sub6_163 : sub6 [1, -3] = true := by decide +kernel
theorem sub6_164 : sub6 [1, -2] = true := by decide +kernel
theorem sub6_165 : sub6 [1, -1] = true := by decide +kernel
theorem sub6_166 : sub6 [1, 0, -7] = true := by decide +kernel
theorem sub6_167 : sub6 [1, 0, -6] = true := by decide +kernel
theorem sub6_168 : sub6 [1, 0, -5] = true := by decide +kernel
theorem sub6_169 : sub6 [1, 0, -4] = true := by decide +kernel
theorem sub6_170 : sub6 [1, 0, -3] = true := by decide +kernel
theorem sub6_171 : sub6 [1, 0, -2] = true := by decide +kernel
theorem sub6_172 : sub6 [1, 0, -1] = true := by decide +kernel
theorem sub6_173 : sub6 [1, 0, 0] = true := by decide +kernel
theorem sub6_174 : sub6 [1, 0, 1] = true := by decide +kernel
theorem sub6_175 : sub6 [1, 0, 2] = true := by decide +kernel
theorem sub6_176 : sub6 [1, 0, 3] = true := by decide +kernel
theorem sub6_177 : sub6 [1, 0, 4] = true := by decide +kernel
theorem sub6_178 : sub6 [1, 0, 5] = true := by decide +kernel
theorem sub6_179 : sub6 [1, 0, 6] = true := by decide +kernel
theorem sub6_180 : sub6 [1, 1, -7] = true := by decide +kernel
theorem sub6_181 : sub6 [1, 1, -6] = true := by decide +kernel
theorem sub6_182 : sub6 [1, 1, -5] = true := by decide +kernel
theorem sub6_183 : sub6 [1, 1, -4] = true := by decide +kernel
theorem sub6_184 : sub6 [1, 1, -3] = true := by decide +kernel
theorem sub6_185 : sub6 [1, 1, -2] = true := by decide +kernel
theorem sub6_186 : sub6 [1, 1, -1] = true := by decide +kernel
theorem sub6_187 : sub6 [1, 1, 0] = true := by decide +kernel
theorem sub6_188 : sub6 [1, 1, 1] = true := by decide +kernel
theorem sub6_189 : sub6 [1, 1, 2] = true := by decide +kernel
theorem sub6_190 : sub6 [1, 1, 3] = true := by decide +kernel
theorem sub6_191 : sub6 [1, 1, 4] = true := by decide +kernel
theorem sb6_5 : ∀ q ∈ blk6_5, sub6 q = true := by
  unfold blk6_5
  exact List.forall_mem_cons.2 ⟨sub6_160, List.forall_mem_cons.2 ⟨sub6_161, List.forall_mem_cons.2 ⟨sub6_162, List.forall_mem_cons.2 ⟨sub6_163, List.forall_mem_cons.2 ⟨sub6_164, List.forall_mem_cons.2 ⟨sub6_165, List.forall_mem_cons.2 ⟨sub6_166, List.forall_mem_cons.2 ⟨sub6_167, List.forall_mem_cons.2 ⟨sub6_168, List.forall_mem_cons.2 ⟨sub6_169, List.forall_mem_cons.2 ⟨sub6_170, List.forall_mem_cons.2 ⟨sub6_171, List.forall_mem_cons.2 ⟨sub6_172, List.forall_mem_cons.2 ⟨sub6_173, List.forall_mem_cons.2 ⟨sub6_174, List.forall_mem_cons.2 ⟨sub6_175, List.forall_mem_cons.2 ⟨sub6_176, List.forall_mem_cons.2 ⟨sub6_177, List.forall_mem_cons.2 ⟨sub6_178, List.forall_mem_cons.2 ⟨sub6_179, List.forall_mem_cons.2 ⟨sub6_180, List.forall_mem_cons.2 ⟨sub6_181, List.forall_mem_cons.2 ⟨sub6_182, List.forall_mem_cons.2 ⟨sub6_183, List.forall_mem_cons.2 ⟨sub6_184, List.forall_mem_cons.2 ⟨sub6_185, List.forall_mem_cons.2 ⟨sub6_186, List.forall_mem_cons.2 ⟨sub6_187, List.forall_mem_cons.2 ⟨sub6_188, List.forall_mem_cons.2 ⟨sub6_189, List.forall_mem_cons.2 ⟨sub6_190, List.forall_mem_cons.2 ⟨sub6_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_192 : sub6 [1, 1, 5] = true := by decide +kernel
theorem sub6_193 : sub6 [1, 1, 6] = true := by decide +kernel
theorem sub6_194 : sub6 [1, 2] = true := by decide +kernel
theorem sub6_195 : sub6 [1, 3] = true := by decide +kernel
theorem sub6_196 : sub6 [1, 4] = true := by decide +kernel
theorem sub6_197 : sub6 [1, 5] = true := by decide +kernel
theorem sub6_198 : sub6 [1, 6] = true := by decide +kernel
theorem sub6_199 : sub6 [1, 7] = true := by decide +kernel
theorem sub6_200 : sub6 [2, -7] = true := by decide +kernel
theorem sub6_201 : sub6 [2, -6] = true := by decide +kernel
theorem sub6_202 : sub6 [2, -5] = true := by decide +kernel
theorem sub6_203 : sub6 [2, -4] = true := by decide +kernel
theorem sub6_204 : sub6 [2, -3] = true := by decide +kernel
theorem sub6_205 : sub6 [2, -2] = true := by decide +kernel
theorem sub6_206 : sub6 [2, -1] = true := by decide +kernel
theorem sub6_207 : sub6 [2, 0] = true := by decide +kernel
theorem sub6_208 : sub6 [2, 1] = true := by decide +kernel
theorem sub6_209 : sub6 [2, 2] = true := by decide +kernel
theorem sub6_210 : sub6 [2, 3] = true := by decide +kernel
theorem sub6_211 : sub6 [2, 4] = true := by decide +kernel
theorem sub6_212 : sub6 [2, 5] = true := by decide +kernel
theorem sub6_213 : sub6 [2, 6] = true := by decide +kernel
theorem sub6_214 : sub6 [2, 7] = true := by decide +kernel
theorem sub6_215 : sub6 [2, 8] = true := by decide +kernel
theorem sub6_216 : sub6 [3, -6] = true := by decide +kernel
theorem sub6_217 : sub6 [3, -5] = true := by decide +kernel
theorem sub6_218 : sub6 [3, -4] = true := by decide +kernel
theorem sub6_219 : sub6 [3, -3] = true := by decide +kernel
theorem sub6_220 : sub6 [3, -2] = true := by decide +kernel
theorem sub6_221 : sub6 [3, -1] = true := by decide +kernel
theorem sub6_222 : sub6 [3, 0] = true := by decide +kernel
theorem sub6_223 : sub6 [3, 1] = true := by decide +kernel
theorem sb6_6 : ∀ q ∈ blk6_6, sub6 q = true := by
  unfold blk6_6
  exact List.forall_mem_cons.2 ⟨sub6_192, List.forall_mem_cons.2 ⟨sub6_193, List.forall_mem_cons.2 ⟨sub6_194, List.forall_mem_cons.2 ⟨sub6_195, List.forall_mem_cons.2 ⟨sub6_196, List.forall_mem_cons.2 ⟨sub6_197, List.forall_mem_cons.2 ⟨sub6_198, List.forall_mem_cons.2 ⟨sub6_199, List.forall_mem_cons.2 ⟨sub6_200, List.forall_mem_cons.2 ⟨sub6_201, List.forall_mem_cons.2 ⟨sub6_202, List.forall_mem_cons.2 ⟨sub6_203, List.forall_mem_cons.2 ⟨sub6_204, List.forall_mem_cons.2 ⟨sub6_205, List.forall_mem_cons.2 ⟨sub6_206, List.forall_mem_cons.2 ⟨sub6_207, List.forall_mem_cons.2 ⟨sub6_208, List.forall_mem_cons.2 ⟨sub6_209, List.forall_mem_cons.2 ⟨sub6_210, List.forall_mem_cons.2 ⟨sub6_211, List.forall_mem_cons.2 ⟨sub6_212, List.forall_mem_cons.2 ⟨sub6_213, List.forall_mem_cons.2 ⟨sub6_214, List.forall_mem_cons.2 ⟨sub6_215, List.forall_mem_cons.2 ⟨sub6_216, List.forall_mem_cons.2 ⟨sub6_217, List.forall_mem_cons.2 ⟨sub6_218, List.forall_mem_cons.2 ⟨sub6_219, List.forall_mem_cons.2 ⟨sub6_220, List.forall_mem_cons.2 ⟨sub6_221, List.forall_mem_cons.2 ⟨sub6_222, List.forall_mem_cons.2 ⟨sub6_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C076
