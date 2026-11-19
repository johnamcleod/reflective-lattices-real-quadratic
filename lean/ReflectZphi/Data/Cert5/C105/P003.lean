import ReflectZphi.Data.Cert5.C105.Base

namespace ReflectZphi.Data.Cert5.C105
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_96 : sub7 [-1, 6] = true := by decide +kernel
theorem sub7_97 : sub7 [0, -7] = true := by decide +kernel
theorem sub7_98 : sub7 [0, -6] = true := by decide +kernel
theorem sub7_99 : sub7 [0, -5] = true := by decide +kernel
theorem sub7_100 : sub7 [0, -4] = true := by decide +kernel
theorem sub7_101 : sub7 [0, -3] = true := by decide +kernel
theorem sub7_102 : sub7 [0, -2] = true := by decide +kernel
theorem sub7_103 : sub7 [0, -1, -7] = true := by decide +kernel
theorem sub7_104 : sub7 [0, -1, -6] = true := by decide +kernel
theorem sub7_105 : sub7 [0, -1, -5] = true := by decide +kernel
theorem sub7_106 : sub7 [0, -1, -4] = true := by decide +kernel
theorem sub7_107 : sub7 [0, -1, -3] = true := by decide +kernel
theorem sub7_108 : sub7 [0, -1, -2] = true := by decide +kernel
theorem sub7_109 : sub7 [0, -1, -1] = true := by decide +kernel
theorem sub7_110 : sub7 [0, -1, 0] = true := by decide +kernel
theorem sub7_111 : sub7 [0, -1, 1] = true := by decide +kernel
theorem sub7_112 : sub7 [0, -1, 2] = true := by decide +kernel
theorem sub7_113 : sub7 [0, -1, 3] = true := by decide +kernel
theorem sub7_114 : sub7 [0, -1, 4] = true := by decide +kernel
theorem sub7_115 : sub7 [0, -1, 5] = true := by decide +kernel
theorem sub7_116 : sub7 [0, -1, 6] = true := by decide +kernel
theorem sub7_117 : sub7 [0, 0, -7] = true := by decide +kernel
theorem sub7_118 : sub7 [0, 0, -6] = true := by decide +kernel
theorem sub7_119 : sub7 [0, 0, -5] = true := by decide +kernel
theorem sub7_120 : sub7 [0, 0, -4] = true := by decide +kernel
theorem sub7_121 : sub7 [0, 0, -3] = true := by decide +kernel
theorem sub7_122 : sub7 [0, 0, -2] = true := by decide +kernel
theorem sub7_123 : sub7 [0, 0, -1] = true := by decide +kernel
theorem sub7_124 : sub7 [0, 0, 0] = true := by decide +kernel
theorem sub7_125 : sub7 [0, 0, 1] = true := by decide +kernel
theorem sub7_126 : sub7 [0, 0, 2] = true := by decide +kernel
theorem sub7_127 : sub7 [0, 0, 3] = true := by decide +kernel
theorem sb7_3 : ∀ q ∈ blk7_3, sub7 q = true := by
  unfold blk7_3
  exact List.forall_mem_cons.2 ⟨sub7_96, List.forall_mem_cons.2 ⟨sub7_97, List.forall_mem_cons.2 ⟨sub7_98, List.forall_mem_cons.2 ⟨sub7_99, List.forall_mem_cons.2 ⟨sub7_100, List.forall_mem_cons.2 ⟨sub7_101, List.forall_mem_cons.2 ⟨sub7_102, List.forall_mem_cons.2 ⟨sub7_103, List.forall_mem_cons.2 ⟨sub7_104, List.forall_mem_cons.2 ⟨sub7_105, List.forall_mem_cons.2 ⟨sub7_106, List.forall_mem_cons.2 ⟨sub7_107, List.forall_mem_cons.2 ⟨sub7_108, List.forall_mem_cons.2 ⟨sub7_109, List.forall_mem_cons.2 ⟨sub7_110, List.forall_mem_cons.2 ⟨sub7_111, List.forall_mem_cons.2 ⟨sub7_112, List.forall_mem_cons.2 ⟨sub7_113, List.forall_mem_cons.2 ⟨sub7_114, List.forall_mem_cons.2 ⟨sub7_115, List.forall_mem_cons.2 ⟨sub7_116, List.forall_mem_cons.2 ⟨sub7_117, List.forall_mem_cons.2 ⟨sub7_118, List.forall_mem_cons.2 ⟨sub7_119, List.forall_mem_cons.2 ⟨sub7_120, List.forall_mem_cons.2 ⟨sub7_121, List.forall_mem_cons.2 ⟨sub7_122, List.forall_mem_cons.2 ⟨sub7_123, List.forall_mem_cons.2 ⟨sub7_124, List.forall_mem_cons.2 ⟨sub7_125, List.forall_mem_cons.2 ⟨sub7_126, List.forall_mem_cons.2 ⟨sub7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_128 : sub7 [0, 0, 4] = true := by decide +kernel
theorem sub7_129 : sub7 [0, 0, 5] = true := by decide +kernel
theorem sub7_130 : sub7 [0, 0, 6] = true := by decide +kernel
theorem sub7_131 : sub7 [0, 1, -7] = true := by decide +kernel
theorem sub7_132 : sub7 [0, 1, -6] = true := by decide +kernel
theorem sub7_133 : sub7 [0, 1, -5] = true := by decide +kernel
theorem sub7_134 : sub7 [0, 1, -4] = true := by decide +kernel
theorem sub7_135 : sub7 [0, 1, -3] = true := by decide +kernel
theorem sub7_136 : sub7 [0, 1, -2] = true := by decide +kernel
theorem sub7_137 : sub7 [0, 1, -1] = true := by decide +kernel
theorem sub7_138 : sub7 [0, 1, 0] = true := by decide +kernel
theorem sub7_139 : sub7 [0, 1, 1] = true := by decide +kernel
theorem sub7_140 : sub7 [0, 1, 2] = true := by decide +kernel
theorem sub7_141 : sub7 [0, 1, 3] = true := by decide +kernel
theorem sub7_142 : sub7 [0, 1, 4] = true := by decide +kernel
theorem sub7_143 : sub7 [0, 1, 5] = true := by decide +kernel
theorem sub7_144 : sub7 [0, 1, 6] = true := by decide +kernel
theorem sub7_145 : sub7 [0, 2] = true := by decide +kernel
theorem sub7_146 : sub7 [0, 3] = true := by decide +kernel
theorem sub7_147 : sub7 [0, 4] = true := by decide +kernel
theorem sub7_148 : sub7 [0, 5] = true := by decide +kernel
theorem sub7_149 : sub7 [0, 6] = true := by decide +kernel
theorem sub7_150 : sub7 [1, -7] = true := by decide +kernel
theorem sub7_151 : sub7 [1, -6] = true := by decide +kernel
theorem sub7_152 : sub7 [1, -5] = true := by decide +kernel
theorem sub7_153 : sub7 [1, -4] = true := by decide +kernel
theorem sub7_154 : sub7 [1, -3] = true := by decide +kernel
theorem sub7_155 : sub7 [1, -2] = true := by decide +kernel
theorem sub7_156 : sub7 [1, -1, -7] = true := by decide +kernel
theorem sub7_157 : sub7 [1, -1, -6] = true := by decide +kernel
theorem sub7_158 : sub7 [1, -1, -5] = true := by decide +kernel
theorem sub7_159 : sub7 [1, -1, -4] = true := by decide +kernel
theorem sb7_4 : ∀ q ∈ blk7_4, sub7 q = true := by
  unfold blk7_4
  exact List.forall_mem_cons.2 ⟨sub7_128, List.forall_mem_cons.2 ⟨sub7_129, List.forall_mem_cons.2 ⟨sub7_130, List.forall_mem_cons.2 ⟨sub7_131, List.forall_mem_cons.2 ⟨sub7_132, List.forall_mem_cons.2 ⟨sub7_133, List.forall_mem_cons.2 ⟨sub7_134, List.forall_mem_cons.2 ⟨sub7_135, List.forall_mem_cons.2 ⟨sub7_136, List.forall_mem_cons.2 ⟨sub7_137, List.forall_mem_cons.2 ⟨sub7_138, List.forall_mem_cons.2 ⟨sub7_139, List.forall_mem_cons.2 ⟨sub7_140, List.forall_mem_cons.2 ⟨sub7_141, List.forall_mem_cons.2 ⟨sub7_142, List.forall_mem_cons.2 ⟨sub7_143, List.forall_mem_cons.2 ⟨sub7_144, List.forall_mem_cons.2 ⟨sub7_145, List.forall_mem_cons.2 ⟨sub7_146, List.forall_mem_cons.2 ⟨sub7_147, List.forall_mem_cons.2 ⟨sub7_148, List.forall_mem_cons.2 ⟨sub7_149, List.forall_mem_cons.2 ⟨sub7_150, List.forall_mem_cons.2 ⟨sub7_151, List.forall_mem_cons.2 ⟨sub7_152, List.forall_mem_cons.2 ⟨sub7_153, List.forall_mem_cons.2 ⟨sub7_154, List.forall_mem_cons.2 ⟨sub7_155, List.forall_mem_cons.2 ⟨sub7_156, List.forall_mem_cons.2 ⟨sub7_157, List.forall_mem_cons.2 ⟨sub7_158, List.forall_mem_cons.2 ⟨sub7_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_160 : sub7 [1, -1, -3] = true := by decide +kernel
theorem sub7_161 : sub7 [1, -1, -2] = true := by decide +kernel
theorem sub7_162 : sub7 [1, -1, -1] = true := by decide +kernel
theorem sub7_163 : sub7 [1, -1, 0] = true := by decide +kernel
theorem sub7_164 : sub7 [1, -1, 1] = true := by decide +kernel
theorem sub7_165 : sub7 [1, -1, 2] = true := by decide +kernel
theorem sub7_166 : sub7 [1, -1, 3] = true := by decide +kernel
theorem sub7_167 : sub7 [1, -1, 4] = true := by decide +kernel
theorem sub7_168 : sub7 [1, -1, 5] = true := by decide +kernel
theorem sub7_169 : sub7 [1, 0, -7] = true := by decide +kernel
theorem sub7_170 : sub7 [1, 0, -6] = true := by decide +kernel
theorem sub7_171 : sub7 [1, 0, -5] = true := by decide +kernel
theorem sub7_172 : sub7 [1, 0, -4] = true := by decide +kernel
theorem sub7_173 : sub7 [1, 0, -3] = true := by decide +kernel
theorem sub7_174 : sub7 [1, 0, -2] = true := by decide +kernel
theorem sub7_175 : sub7 [1, 0, -1] = true := by decide +kernel
theorem sub7_176 : sub7 [1, 0, 0] = true := by decide +kernel
theorem sub7_177 : sub7 [1, 0, 1] = true := by decide +kernel
theorem sub7_178 : sub7 [1, 0, 2] = true := by decide +kernel
theorem sub7_179 : sub7 [1, 0, 3] = true := by decide +kernel
theorem sub7_180 : sub7 [1, 0, 4] = true := by decide +kernel
theorem sub7_181 : sub7 [1, 0, 5] = true := by decide +kernel
theorem sub7_182 : sub7 [1, 1, -7] = true := by decide +kernel
theorem sub7_183 : sub7 [1, 1, -6] = true := by decide +kernel
theorem sub7_184 : sub7 [1, 1, -5] = true := by decide +kernel
theorem sub7_185 : sub7 [1, 1, -4] = true := by decide +kernel
theorem sub7_186 : sub7 [1, 1, -3] = true := by decide +kernel
theorem sub7_187 : sub7 [1, 1, -2] = true := by decide +kernel
theorem sub7_188 : sub7 [1, 1, -1] = true := by decide +kernel
theorem sub7_189 : sub7 [1, 1, 0] = true := by decide +kernel
theorem sub7_190 : sub7 [1, 1, 1] = true := by decide +kernel
theorem sub7_191 : sub7 [1, 1, 2] = true := by decide +kernel
theorem sb7_5 : ∀ q ∈ blk7_5, sub7 q = true := by
  unfold blk7_5
  exact List.forall_mem_cons.2 ⟨sub7_160, List.forall_mem_cons.2 ⟨sub7_161, List.forall_mem_cons.2 ⟨sub7_162, List.forall_mem_cons.2 ⟨sub7_163, List.forall_mem_cons.2 ⟨sub7_164, List.forall_mem_cons.2 ⟨sub7_165, List.forall_mem_cons.2 ⟨sub7_166, List.forall_mem_cons.2 ⟨sub7_167, List.forall_mem_cons.2 ⟨sub7_168, List.forall_mem_cons.2 ⟨sub7_169, List.forall_mem_cons.2 ⟨sub7_170, List.forall_mem_cons.2 ⟨sub7_171, List.forall_mem_cons.2 ⟨sub7_172, List.forall_mem_cons.2 ⟨sub7_173, List.forall_mem_cons.2 ⟨sub7_174, List.forall_mem_cons.2 ⟨sub7_175, List.forall_mem_cons.2 ⟨sub7_176, List.forall_mem_cons.2 ⟨sub7_177, List.forall_mem_cons.2 ⟨sub7_178, List.forall_mem_cons.2 ⟨sub7_179, List.forall_mem_cons.2 ⟨sub7_180, List.forall_mem_cons.2 ⟨sub7_181, List.forall_mem_cons.2 ⟨sub7_182, List.forall_mem_cons.2 ⟨sub7_183, List.forall_mem_cons.2 ⟨sub7_184, List.forall_mem_cons.2 ⟨sub7_185, List.forall_mem_cons.2 ⟨sub7_186, List.forall_mem_cons.2 ⟨sub7_187, List.forall_mem_cons.2 ⟨sub7_188, List.forall_mem_cons.2 ⟨sub7_189, List.forall_mem_cons.2 ⟨sub7_190, List.forall_mem_cons.2 ⟨sub7_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_192 : sub7 [1, 1, 3] = true := by decide +kernel
theorem sub7_193 : sub7 [1, 1, 4] = true := by decide +kernel
theorem sub7_194 : sub7 [1, 1, 5] = true := by decide +kernel
theorem sub7_195 : sub7 [1, 1, 6] = true := by decide +kernel
theorem sub7_196 : sub7 [1, 2] = true := by decide +kernel
theorem sub7_197 : sub7 [1, 3] = true := by decide +kernel
theorem sub7_198 : sub7 [1, 4] = true := by decide +kernel
theorem sub7_199 : sub7 [1, 5] = true := by decide +kernel
theorem sub7_200 : sub7 [1, 6] = true := by decide +kernel
theorem sub7_201 : sub7 [2, -6] = true := by decide +kernel
theorem sub7_202 : sub7 [2, -5] = true := by decide +kernel
theorem sub7_203 : sub7 [2, -4] = true := by decide +kernel
theorem sub7_204 : sub7 [2, -3] = true := by decide +kernel
theorem sub7_205 : sub7 [2, -2] = true := by decide +kernel
theorem sub7_206 : sub7 [2, -1] = true := by decide +kernel
theorem sub7_207 : sub7 [2, 0] = true := by decide +kernel
theorem sub7_208 : sub7 [2, 1] = true := by decide +kernel
theorem sub7_209 : sub7 [2, 2] = true := by decide +kernel
theorem sub7_210 : sub7 [2, 3] = true := by decide +kernel
theorem sub7_211 : sub7 [2, 4] = true := by decide +kernel
theorem sub7_212 : sub7 [2, 5] = true := by decide +kernel
theorem sub7_213 : sub7 [2, 6] = true := by decide +kernel
theorem sub7_214 : sub7 [3, -6] = true := by decide +kernel
theorem sub7_215 : sub7 [3, -5] = true := by decide +kernel
theorem sub7_216 : sub7 [3, -4] = true := by decide +kernel
theorem sub7_217 : sub7 [3, -3] = true := by decide +kernel
theorem sub7_218 : sub7 [3, -2] = true := by decide +kernel
theorem sub7_219 : sub7 [3, -1] = true := by decide +kernel
theorem sub7_220 : sub7 [3, 0] = true := by decide +kernel
theorem sub7_221 : sub7 [3, 1] = true := by decide +kernel
theorem sub7_222 : sub7 [3, 2] = true := by decide +kernel
theorem sub7_223 : sub7 [3, 3] = true := by decide +kernel
theorem sb7_6 : ∀ q ∈ blk7_6, sub7 q = true := by
  unfold blk7_6
  exact List.forall_mem_cons.2 ⟨sub7_192, List.forall_mem_cons.2 ⟨sub7_193, List.forall_mem_cons.2 ⟨sub7_194, List.forall_mem_cons.2 ⟨sub7_195, List.forall_mem_cons.2 ⟨sub7_196, List.forall_mem_cons.2 ⟨sub7_197, List.forall_mem_cons.2 ⟨sub7_198, List.forall_mem_cons.2 ⟨sub7_199, List.forall_mem_cons.2 ⟨sub7_200, List.forall_mem_cons.2 ⟨sub7_201, List.forall_mem_cons.2 ⟨sub7_202, List.forall_mem_cons.2 ⟨sub7_203, List.forall_mem_cons.2 ⟨sub7_204, List.forall_mem_cons.2 ⟨sub7_205, List.forall_mem_cons.2 ⟨sub7_206, List.forall_mem_cons.2 ⟨sub7_207, List.forall_mem_cons.2 ⟨sub7_208, List.forall_mem_cons.2 ⟨sub7_209, List.forall_mem_cons.2 ⟨sub7_210, List.forall_mem_cons.2 ⟨sub7_211, List.forall_mem_cons.2 ⟨sub7_212, List.forall_mem_cons.2 ⟨sub7_213, List.forall_mem_cons.2 ⟨sub7_214, List.forall_mem_cons.2 ⟨sub7_215, List.forall_mem_cons.2 ⟨sub7_216, List.forall_mem_cons.2 ⟨sub7_217, List.forall_mem_cons.2 ⟨sub7_218, List.forall_mem_cons.2 ⟨sub7_219, List.forall_mem_cons.2 ⟨sub7_220, List.forall_mem_cons.2 ⟨sub7_221, List.forall_mem_cons.2 ⟨sub7_222, List.forall_mem_cons.2 ⟨sub7_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_224 : sub7 [3, 4] = true := by decide +kernel
theorem sub7_225 : sub7 [3, 5] = true := by decide +kernel
theorem sub7_226 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_227 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_228 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_229 : sub7 [4, -2] = true := by decide +kernel
theorem sub7_230 : sub7 [4, -1] = true := by decide +kernel
theorem sub7_231 : sub7 [4, 0] = true := by decide +kernel
theorem sub7_232 : sub7 [4, 1] = true := by decide +kernel
theorem sub7_233 : sub7 [4, 2] = true := by decide +kernel
theorem sub7_234 : sub7 [4, 3] = true := by decide +kernel
theorem sub7_235 : sub7 [4, 4] = true := by decide +kernel
theorem sub7_236 : sub7 [4, 5] = true := by decide +kernel
theorem sub7_237 : sub7 [5, -4] = true := by decide +kernel
theorem sub7_238 : sub7 [5, -3] = true := by decide +kernel
theorem sub7_239 : sub7 [5, -2] = true := by decide +kernel
theorem sub7_240 : sub7 [5, -1] = true := by decide +kernel
theorem sub7_241 : sub7 [5, 0] = true := by decide +kernel
theorem sub7_242 : sub7 [5, 1] = true := by decide +kernel
theorem sub7_243 : sub7 [5, 2] = true := by decide +kernel
theorem sub7_244 : sub7 [5, 3] = true := by decide +kernel
theorem sub7_245 : sub7 [5, 4] = true := by decide +kernel
theorem sub7_246 : sub7 [6] = true := by decide +kernel
theorem sb7_7 : ∀ q ∈ blk7_7, sub7 q = true := by
  unfold blk7_7
  exact List.forall_mem_cons.2 ⟨sub7_224, List.forall_mem_cons.2 ⟨sub7_225, List.forall_mem_cons.2 ⟨sub7_226, List.forall_mem_cons.2 ⟨sub7_227, List.forall_mem_cons.2 ⟨sub7_228, List.forall_mem_cons.2 ⟨sub7_229, List.forall_mem_cons.2 ⟨sub7_230, List.forall_mem_cons.2 ⟨sub7_231, List.forall_mem_cons.2 ⟨sub7_232, List.forall_mem_cons.2 ⟨sub7_233, List.forall_mem_cons.2 ⟨sub7_234, List.forall_mem_cons.2 ⟨sub7_235, List.forall_mem_cons.2 ⟨sub7_236, List.forall_mem_cons.2 ⟨sub7_237, List.forall_mem_cons.2 ⟨sub7_238, List.forall_mem_cons.2 ⟨sub7_239, List.forall_mem_cons.2 ⟨sub7_240, List.forall_mem_cons.2 ⟨sub7_241, List.forall_mem_cons.2 ⟨sub7_242, List.forall_mem_cons.2 ⟨sub7_243, List.forall_mem_cons.2 ⟨sub7_244, List.forall_mem_cons.2 ⟨sub7_245, List.forall_mem_cons.2 ⟨sub7_246, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C105
