import ReflectZphi.Data.Cert5.C125.Base

namespace ReflectZphi.Data.Cert5.C125
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_96 : sub7 [-3, -4] = true := by decide +kernel
theorem sub7_97 : sub7 [-3, -3, -8] = true := by decide +kernel
theorem sub7_98 : sub7 [-3, -3, -7] = true := by decide +kernel
theorem sub7_99 : sub7 [-3, -3, -6] = true := by decide +kernel
theorem sub7_100 : sub7 [-3, -3, -5] = true := by decide +kernel
theorem sub7_101 : sub7 [-3, -3, -4] = true := by decide +kernel
theorem sub7_102 : sub7 [-3, -3, -3] = true := by decide +kernel
theorem sub7_103 : sub7 [-3, -3, -2] = true := by decide +kernel
theorem sub7_104 : sub7 [-3, -3, -1] = true := by decide +kernel
theorem sub7_105 : sub7 [-3, -3, 0] = true := by decide +kernel
theorem sub7_106 : sub7 [-3, -3, 1] = true := by decide +kernel
theorem sub7_107 : sub7 [-3, -3, 2] = true := by decide +kernel
theorem sub7_108 : sub7 [-3, -3, 3] = true := by decide +kernel
theorem sub7_109 : sub7 [-3, -3, 4] = true := by decide +kernel
theorem sub7_110 : sub7 [-3, -3, 5] = true := by decide +kernel
theorem sub7_111 : sub7 [-3, -2, -8] = true := by decide +kernel
theorem sub7_112 : sub7 [-3, -2, -7] = true := by decide +kernel
theorem sub7_113 : sub7 [-3, -2, -6] = true := by decide +kernel
theorem sub7_114 : sub7 [-3, -2, -5] = true := by decide +kernel
theorem sub7_115 : sub7 [-3, -2, -4] = true := by decide +kernel
theorem sub7_116 : sub7 [-3, -2, -3] = true := by decide +kernel
theorem sub7_117 : sub7 [-3, -2, -2] = true := by decide +kernel
theorem sub7_118 : sub7 [-3, -2, -1] = true := by decide +kernel
theorem sub7_119 : sub7 [-3, -2, 0] = true := by decide +kernel
theorem sub7_120 : sub7 [-3, -2, 1] = true := by decide +kernel
theorem sub7_121 : sub7 [-3, -2, 2] = true := by decide +kernel
theorem sub7_122 : sub7 [-3, -2, 3] = true := by decide +kernel
theorem sub7_123 : sub7 [-3, -2, 4] = true := by decide +kernel
theorem sub7_124 : sub7 [-3, -2, 5] = true := by decide +kernel
theorem sub7_125 : sub7 [-3, -2, 6] = true := by decide +kernel
theorem sub7_126 : sub7 [-3, -1, -8] = true := by decide +kernel
theorem sub7_127 : sub7 [-3, -1, -7] = true := by decide +kernel
theorem sb7_3 : ∀ q ∈ blk7_3, sub7 q = true := by
  unfold blk7_3
  exact List.forall_mem_cons.2 ⟨sub7_96, List.forall_mem_cons.2 ⟨sub7_97, List.forall_mem_cons.2 ⟨sub7_98, List.forall_mem_cons.2 ⟨sub7_99, List.forall_mem_cons.2 ⟨sub7_100, List.forall_mem_cons.2 ⟨sub7_101, List.forall_mem_cons.2 ⟨sub7_102, List.forall_mem_cons.2 ⟨sub7_103, List.forall_mem_cons.2 ⟨sub7_104, List.forall_mem_cons.2 ⟨sub7_105, List.forall_mem_cons.2 ⟨sub7_106, List.forall_mem_cons.2 ⟨sub7_107, List.forall_mem_cons.2 ⟨sub7_108, List.forall_mem_cons.2 ⟨sub7_109, List.forall_mem_cons.2 ⟨sub7_110, List.forall_mem_cons.2 ⟨sub7_111, List.forall_mem_cons.2 ⟨sub7_112, List.forall_mem_cons.2 ⟨sub7_113, List.forall_mem_cons.2 ⟨sub7_114, List.forall_mem_cons.2 ⟨sub7_115, List.forall_mem_cons.2 ⟨sub7_116, List.forall_mem_cons.2 ⟨sub7_117, List.forall_mem_cons.2 ⟨sub7_118, List.forall_mem_cons.2 ⟨sub7_119, List.forall_mem_cons.2 ⟨sub7_120, List.forall_mem_cons.2 ⟨sub7_121, List.forall_mem_cons.2 ⟨sub7_122, List.forall_mem_cons.2 ⟨sub7_123, List.forall_mem_cons.2 ⟨sub7_124, List.forall_mem_cons.2 ⟨sub7_125, List.forall_mem_cons.2 ⟨sub7_126, List.forall_mem_cons.2 ⟨sub7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_128 : sub7 [-3, -1, -6] = true := by decide +kernel
theorem sub7_129 : sub7 [-3, -1, -5] = true := by decide +kernel
theorem sub7_130 : sub7 [-3, -1, -4] = true := by decide +kernel
theorem sub7_131 : sub7 [-3, -1, -3] = true := by decide +kernel
theorem sub7_132 : sub7 [-3, -1, -2] = true := by decide +kernel
theorem sub7_133 : sub7 [-3, -1, -1] = true := by decide +kernel
theorem sub7_134 : sub7 [-3, -1, 0] = true := by decide +kernel
theorem sub7_135 : sub7 [-3, -1, 1] = true := by decide +kernel
theorem sub7_136 : sub7 [-3, -1, 2] = true := by decide +kernel
theorem sub7_137 : sub7 [-3, -1, 3] = true := by decide +kernel
theorem sub7_138 : sub7 [-3, -1, 4] = true := by decide +kernel
theorem sub7_139 : sub7 [-3, -1, 5] = true := by decide +kernel
theorem sub7_140 : sub7 [-3, -1, 6] = true := by decide +kernel
theorem sub7_141 : sub7 [-3, -1, 7] = true := by decide +kernel
theorem sub7_142 : sub7 [-3, 0, -8] = true := by decide +kernel
theorem sub7_143 : sub7 [-3, 0, -7] = true := by decide +kernel
theorem sub7_144 : sub7 [-3, 0, -6] = true := by decide +kernel
theorem sub7_145 : sub7 [-3, 0, -5] = true := by decide +kernel
theorem sub7_146 : sub7 [-3, 0, -4] = true := by decide +kernel
theorem sub7_147 : sub7 [-3, 0, -3] = true := by decide +kernel
theorem sub7_148 : sub7 [-3, 0, -2] = true := by decide +kernel
theorem sub7_149 : sub7 [-3, 0, -1] = true := by decide +kernel
theorem sub7_150 : sub7 [-3, 0, 0] = true := by decide +kernel
theorem sub7_151 : sub7 [-3, 0, 1] = true := by decide +kernel
theorem sub7_152 : sub7 [-3, 0, 2] = true := by decide +kernel
theorem sub7_153 : sub7 [-3, 0, 3] = true := by decide +kernel
theorem sub7_154 : sub7 [-3, 0, 4] = true := by decide +kernel
theorem sub7_155 : sub7 [-3, 0, 5] = true := by decide +kernel
theorem sub7_156 : sub7 [-3, 0, 6] = true := by decide +kernel
theorem sub7_157 : sub7 [-3, 0, 7] = true := by decide +kernel
theorem sub7_158 : sub7 [-3, 0, 8] = true := by decide +kernel
theorem sub7_159 : sub7 [-3, 1, -8] = true := by decide +kernel
theorem sb7_4 : ∀ q ∈ blk7_4, sub7 q = true := by
  unfold blk7_4
  exact List.forall_mem_cons.2 ⟨sub7_128, List.forall_mem_cons.2 ⟨sub7_129, List.forall_mem_cons.2 ⟨sub7_130, List.forall_mem_cons.2 ⟨sub7_131, List.forall_mem_cons.2 ⟨sub7_132, List.forall_mem_cons.2 ⟨sub7_133, List.forall_mem_cons.2 ⟨sub7_134, List.forall_mem_cons.2 ⟨sub7_135, List.forall_mem_cons.2 ⟨sub7_136, List.forall_mem_cons.2 ⟨sub7_137, List.forall_mem_cons.2 ⟨sub7_138, List.forall_mem_cons.2 ⟨sub7_139, List.forall_mem_cons.2 ⟨sub7_140, List.forall_mem_cons.2 ⟨sub7_141, List.forall_mem_cons.2 ⟨sub7_142, List.forall_mem_cons.2 ⟨sub7_143, List.forall_mem_cons.2 ⟨sub7_144, List.forall_mem_cons.2 ⟨sub7_145, List.forall_mem_cons.2 ⟨sub7_146, List.forall_mem_cons.2 ⟨sub7_147, List.forall_mem_cons.2 ⟨sub7_148, List.forall_mem_cons.2 ⟨sub7_149, List.forall_mem_cons.2 ⟨sub7_150, List.forall_mem_cons.2 ⟨sub7_151, List.forall_mem_cons.2 ⟨sub7_152, List.forall_mem_cons.2 ⟨sub7_153, List.forall_mem_cons.2 ⟨sub7_154, List.forall_mem_cons.2 ⟨sub7_155, List.forall_mem_cons.2 ⟨sub7_156, List.forall_mem_cons.2 ⟨sub7_157, List.forall_mem_cons.2 ⟨sub7_158, List.forall_mem_cons.2 ⟨sub7_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_160 : sub7 [-3, 1, -7] = true := by decide +kernel
theorem sub7_161 : sub7 [-3, 1, -6] = true := by decide +kernel
theorem sub7_162 : sub7 [-3, 1, -5] = true := by decide +kernel
theorem sub7_163 : sub7 [-3, 1, -4] = true := by decide +kernel
theorem sub7_164 : sub7 [-3, 1, -3] = true := by decide +kernel
theorem sub7_165 : sub7 [-3, 1, -2] = true := by decide +kernel
theorem sub7_166 : sub7 [-3, 1, -1] = true := by decide +kernel
theorem sub7_167 : sub7 [-3, 1, 0] = true := by decide +kernel
theorem sub7_168 : sub7 [-3, 1, 1] = true := by decide +kernel
theorem sub7_169 : sub7 [-3, 1, 2] = true := by decide +kernel
theorem sub7_170 : sub7 [-3, 1, 3] = true := by decide +kernel
theorem sub7_171 : sub7 [-3, 1, 4] = true := by decide +kernel
theorem sub7_172 : sub7 [-3, 1, 5] = true := by decide +kernel
theorem sub7_173 : sub7 [-3, 1, 6] = true := by decide +kernel
theorem sub7_174 : sub7 [-3, 1, 7] = true := by decide +kernel
theorem sub7_175 : sub7 [-3, 1, 8] = true := by decide +kernel
theorem sub7_176 : sub7 [-3, 2, -7] = true := by decide +kernel
theorem sub7_177 : sub7 [-3, 2, -6] = true := by decide +kernel
theorem sub7_178 : sub7 [-3, 2, -5] = true := by decide +kernel
theorem sub7_179 : sub7 [-3, 2, -4] = true := by decide +kernel
theorem sub7_180 : sub7 [-3, 2, -3] = true := by decide +kernel
theorem sub7_181 : sub7 [-3, 2, -2] = true := by decide +kernel
theorem sub7_182 : sub7 [-3, 2, -1] = true := by decide +kernel
theorem sub7_183 : sub7 [-3, 2, 0] = true := by decide +kernel
theorem sub7_184 : sub7 [-3, 2, 1] = true := by decide +kernel
theorem sub7_185 : sub7 [-3, 2, 2] = true := by decide +kernel
theorem sub7_186 : sub7 [-3, 2, 3] = true := by decide +kernel
theorem sub7_187 : sub7 [-3, 2, 4] = true := by decide +kernel
theorem sub7_188 : sub7 [-3, 2, 5] = true := by decide +kernel
theorem sub7_189 : sub7 [-3, 2, 6] = true := by decide +kernel
theorem sub7_190 : sub7 [-3, 2, 7] = true := by decide +kernel
theorem sub7_191 : sub7 [-3, 2, 8] = true := by decide +kernel
theorem sb7_5 : ∀ q ∈ blk7_5, sub7 q = true := by
  unfold blk7_5
  exact List.forall_mem_cons.2 ⟨sub7_160, List.forall_mem_cons.2 ⟨sub7_161, List.forall_mem_cons.2 ⟨sub7_162, List.forall_mem_cons.2 ⟨sub7_163, List.forall_mem_cons.2 ⟨sub7_164, List.forall_mem_cons.2 ⟨sub7_165, List.forall_mem_cons.2 ⟨sub7_166, List.forall_mem_cons.2 ⟨sub7_167, List.forall_mem_cons.2 ⟨sub7_168, List.forall_mem_cons.2 ⟨sub7_169, List.forall_mem_cons.2 ⟨sub7_170, List.forall_mem_cons.2 ⟨sub7_171, List.forall_mem_cons.2 ⟨sub7_172, List.forall_mem_cons.2 ⟨sub7_173, List.forall_mem_cons.2 ⟨sub7_174, List.forall_mem_cons.2 ⟨sub7_175, List.forall_mem_cons.2 ⟨sub7_176, List.forall_mem_cons.2 ⟨sub7_177, List.forall_mem_cons.2 ⟨sub7_178, List.forall_mem_cons.2 ⟨sub7_179, List.forall_mem_cons.2 ⟨sub7_180, List.forall_mem_cons.2 ⟨sub7_181, List.forall_mem_cons.2 ⟨sub7_182, List.forall_mem_cons.2 ⟨sub7_183, List.forall_mem_cons.2 ⟨sub7_184, List.forall_mem_cons.2 ⟨sub7_185, List.forall_mem_cons.2 ⟨sub7_186, List.forall_mem_cons.2 ⟨sub7_187, List.forall_mem_cons.2 ⟨sub7_188, List.forall_mem_cons.2 ⟨sub7_189, List.forall_mem_cons.2 ⟨sub7_190, List.forall_mem_cons.2 ⟨sub7_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_192 : sub7 [-3, 3, -6] = true := by decide +kernel
theorem sub7_193 : sub7 [-3, 3, -5] = true := by decide +kernel
theorem sub7_194 : sub7 [-3, 3, -4] = true := by decide +kernel
theorem sub7_195 : sub7 [-3, 3, -3] = true := by decide +kernel
theorem sub7_196 : sub7 [-3, 3, -2] = true := by decide +kernel
theorem sub7_197 : sub7 [-3, 3, -1] = true := by decide +kernel
theorem sub7_198 : sub7 [-3, 3, 0] = true := by decide +kernel
theorem sub7_199 : sub7 [-3, 3, 1] = true := by decide +kernel
theorem sub7_200 : sub7 [-3, 3, 2] = true := by decide +kernel
theorem sub7_201 : sub7 [-3, 3, 3] = true := by decide +kernel
theorem sub7_202 : sub7 [-3, 3, 4] = true := by decide +kernel
theorem sub7_203 : sub7 [-3, 3, 5] = true := by decide +kernel
theorem sub7_204 : sub7 [-3, 3, 6] = true := by decide +kernel
theorem sub7_205 : sub7 [-3, 3, 7] = true := by decide +kernel
theorem sub7_206 : sub7 [-3, 3, 8] = true := by decide +kernel
theorem sub7_207 : sub7 [-3, 4] = true := by decide +kernel
theorem sub7_208 : sub7 [-3, 5] = true := by decide +kernel
theorem sub7_209 : sub7 [-2, -7] = true := by decide +kernel
theorem sub7_210 : sub7 [-2, -6] = true := by decide +kernel
theorem sub7_211 : sub7 [-2, -5] = true := by decide +kernel
theorem sub7_212 : sub7 [-2, -4, -8] = true := by decide +kernel
theorem sub7_213 : sub7 [-2, -4, -7] = true := by decide +kernel
theorem sub7_214 : sub7 [-2, -4, -6] = true := by decide +kernel
theorem sub7_215 : sub7 [-2, -4, -5] = true := by decide +kernel
theorem sub7_216 : sub7 [-2, -4, -4] = true := by decide +kernel
theorem sub7_217 : sub7 [-2, -4, -3] = true := by decide +kernel
theorem sub7_218 : sub7 [-2, -4, -2] = true := by decide +kernel
theorem sub7_219 : sub7 [-2, -4, -1] = true := by decide +kernel
theorem sub7_220 : sub7 [-2, -4, 0] = true := by decide +kernel
theorem sub7_221 : sub7 [-2, -4, 1] = true := by decide +kernel
theorem sub7_222 : sub7 [-2, -4, 2] = true := by decide +kernel
theorem sub7_223 : sub7 [-2, -4, 3] = true := by decide +kernel
theorem sb7_6 : ∀ q ∈ blk7_6, sub7 q = true := by
  unfold blk7_6
  exact List.forall_mem_cons.2 ⟨sub7_192, List.forall_mem_cons.2 ⟨sub7_193, List.forall_mem_cons.2 ⟨sub7_194, List.forall_mem_cons.2 ⟨sub7_195, List.forall_mem_cons.2 ⟨sub7_196, List.forall_mem_cons.2 ⟨sub7_197, List.forall_mem_cons.2 ⟨sub7_198, List.forall_mem_cons.2 ⟨sub7_199, List.forall_mem_cons.2 ⟨sub7_200, List.forall_mem_cons.2 ⟨sub7_201, List.forall_mem_cons.2 ⟨sub7_202, List.forall_mem_cons.2 ⟨sub7_203, List.forall_mem_cons.2 ⟨sub7_204, List.forall_mem_cons.2 ⟨sub7_205, List.forall_mem_cons.2 ⟨sub7_206, List.forall_mem_cons.2 ⟨sub7_207, List.forall_mem_cons.2 ⟨sub7_208, List.forall_mem_cons.2 ⟨sub7_209, List.forall_mem_cons.2 ⟨sub7_210, List.forall_mem_cons.2 ⟨sub7_211, List.forall_mem_cons.2 ⟨sub7_212, List.forall_mem_cons.2 ⟨sub7_213, List.forall_mem_cons.2 ⟨sub7_214, List.forall_mem_cons.2 ⟨sub7_215, List.forall_mem_cons.2 ⟨sub7_216, List.forall_mem_cons.2 ⟨sub7_217, List.forall_mem_cons.2 ⟨sub7_218, List.forall_mem_cons.2 ⟨sub7_219, List.forall_mem_cons.2 ⟨sub7_220, List.forall_mem_cons.2 ⟨sub7_221, List.forall_mem_cons.2 ⟨sub7_222, List.forall_mem_cons.2 ⟨sub7_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_224 : sub7 [-2, -4, 4] = true := by decide +kernel
theorem sub7_225 : sub7 [-2, -3, -9] = true := by decide +kernel
theorem sub7_226 : sub7 [-2, -3, -8] = true := by decide +kernel
theorem sub7_227 : sub7 [-2, -3, -7] = true := by decide +kernel
theorem sub7_228 : sub7 [-2, -3, -6] = true := by decide +kernel
theorem sub7_229 : sub7 [-2, -3, -5] = true := by decide +kernel
theorem sub7_230 : sub7 [-2, -3, -4] = true := by decide +kernel
theorem sub7_231 : sub7 [-2, -3, -3] = true := by decide +kernel
theorem sub7_232 : sub7 [-2, -3, -2] = true := by decide +kernel
theorem sub7_233 : sub7 [-2, -3, -1] = true := by decide +kernel
theorem sub7_234 : sub7 [-2, -3, 0] = true := by decide +kernel
theorem sub7_235 : sub7 [-2, -3, 1] = true := by decide +kernel
theorem sub7_236 : sub7 [-2, -3, 2] = true := by decide +kernel
theorem sub7_237 : sub7 [-2, -3, 3] = true := by decide +kernel
theorem sub7_238 : sub7 [-2, -3, 4] = true := by decide +kernel
theorem sub7_239 : sub7 [-2, -3, 5] = true := by decide +kernel
theorem sub7_240 : sub7 [-2, -3, 6] = true := by decide +kernel
theorem sub7_241 : sub7 [-2, -2, -9] = true := by decide +kernel
theorem sub7_242 : sub7 [-2, -2, -8] = true := by decide +kernel
theorem sub7_243 : sub7 [-2, -2, -7] = true := by decide +kernel
theorem sub7_244 : sub7 [-2, -2, -6] = true := by decide +kernel
theorem sub7_245 : sub7 [-2, -2, -5] = true := by decide +kernel
theorem sub7_246 : sub7 [-2, -2, -4] = true := by decide +kernel
theorem sub7_247 : sub7 [-2, -2, -3] = true := by decide +kernel
theorem sub7_248 : sub7 [-2, -2, -2] = true := by decide +kernel
theorem sub7_249 : sub7 [-2, -2, -1] = true := by decide +kernel
theorem sub7_250 : sub7 [-2, -2, 0] = true := by decide +kernel
theorem sub7_251 : sub7 [-2, -2, 1] = true := by decide +kernel
theorem sub7_252 : sub7 [-2, -2, 2] = true := by decide +kernel
theorem sub7_253 : sub7 [-2, -2, 3] = true := by decide +kernel
theorem sub7_254 : sub7 [-2, -2, 4] = true := by decide +kernel
theorem sub7_255 : sub7 [-2, -2, 5] = true := by decide +kernel
theorem sb7_7 : ∀ q ∈ blk7_7, sub7 q = true := by
  unfold blk7_7
  exact List.forall_mem_cons.2 ⟨sub7_224, List.forall_mem_cons.2 ⟨sub7_225, List.forall_mem_cons.2 ⟨sub7_226, List.forall_mem_cons.2 ⟨sub7_227, List.forall_mem_cons.2 ⟨sub7_228, List.forall_mem_cons.2 ⟨sub7_229, List.forall_mem_cons.2 ⟨sub7_230, List.forall_mem_cons.2 ⟨sub7_231, List.forall_mem_cons.2 ⟨sub7_232, List.forall_mem_cons.2 ⟨sub7_233, List.forall_mem_cons.2 ⟨sub7_234, List.forall_mem_cons.2 ⟨sub7_235, List.forall_mem_cons.2 ⟨sub7_236, List.forall_mem_cons.2 ⟨sub7_237, List.forall_mem_cons.2 ⟨sub7_238, List.forall_mem_cons.2 ⟨sub7_239, List.forall_mem_cons.2 ⟨sub7_240, List.forall_mem_cons.2 ⟨sub7_241, List.forall_mem_cons.2 ⟨sub7_242, List.forall_mem_cons.2 ⟨sub7_243, List.forall_mem_cons.2 ⟨sub7_244, List.forall_mem_cons.2 ⟨sub7_245, List.forall_mem_cons.2 ⟨sub7_246, List.forall_mem_cons.2 ⟨sub7_247, List.forall_mem_cons.2 ⟨sub7_248, List.forall_mem_cons.2 ⟨sub7_249, List.forall_mem_cons.2 ⟨sub7_250, List.forall_mem_cons.2 ⟨sub7_251, List.forall_mem_cons.2 ⟨sub7_252, List.forall_mem_cons.2 ⟨sub7_253, List.forall_mem_cons.2 ⟨sub7_254, List.forall_mem_cons.2 ⟨sub7_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_256 : sub7 [-2, -2, 6] = true := by decide +kernel
theorem sub7_257 : sub7 [-2, -2, 7] = true := by decide +kernel
theorem sub7_258 : sub7 [-2, -1, -9] = true := by decide +kernel
theorem sub7_259 : sub7 [-2, -1, -8] = true := by decide +kernel
theorem sub7_260 : sub7 [-2, -1, -7] = true := by decide +kernel
theorem sub7_261 : sub7 [-2, -1, -6] = true := by decide +kernel
theorem sub7_262 : sub7 [-2, -1, -5] = true := by decide +kernel
theorem sub7_263 : sub7 [-2, -1, -4] = true := by decide +kernel
theorem sub7_264 : sub7 [-2, -1, -3] = true := by decide +kernel
theorem sub7_265 : sub7 [-2, -1, -2] = true := by decide +kernel
theorem sub7_266 : sub7 [-2, -1, -1] = true := by decide +kernel
theorem sub7_267 : sub7 [-2, -1, 0] = true := by decide +kernel
theorem sub7_268 : sub7 [-2, -1, 1] = true := by decide +kernel
theorem sub7_269 : sub7 [-2, -1, 2] = true := by decide +kernel
theorem sub7_270 : sub7 [-2, -1, 3] = true := by decide +kernel
theorem sub7_271 : sub7 [-2, -1, 4] = true := by decide +kernel
theorem sub7_272 : sub7 [-2, -1, 5] = true := by decide +kernel
theorem sub7_273 : sub7 [-2, -1, 6] = true := by decide +kernel
theorem sub7_274 : sub7 [-2, -1, 7] = true := by decide +kernel
theorem sub7_275 : sub7 [-2, -1, 8] = true := by decide +kernel
theorem sub7_276 : sub7 [-2, 0, -9] = true := by decide +kernel
theorem sub7_277 : sub7 [-2, 0, -8] = true := by decide +kernel
theorem sub7_278 : sub7 [-2, 0, -7] = true := by decide +kernel
theorem sub7_279 : sub7 [-2, 0, -6] = true := by decide +kernel
theorem sub7_280 : sub7 [-2, 0, -5] = true := by decide +kernel
theorem sub7_281 : sub7 [-2, 0, -4] = true := by decide +kernel
theorem sub7_282 : sub7 [-2, 0, -3] = true := by decide +kernel
theorem sub7_283 : sub7 [-2, 0, -2] = true := by decide +kernel
theorem sub7_284 : sub7 [-2, 0, -1] = true := by decide +kernel
theorem sub7_285 : sub7 [-2, 0, 0] = true := by decide +kernel
theorem sub7_286 : sub7 [-2, 0, 1] = true := by decide +kernel
theorem sub7_287 : sub7 [-2, 0, 2] = true := by decide +kernel
theorem sb7_8 : ∀ q ∈ blk7_8, sub7 q = true := by
  unfold blk7_8
  exact List.forall_mem_cons.2 ⟨sub7_256, List.forall_mem_cons.2 ⟨sub7_257, List.forall_mem_cons.2 ⟨sub7_258, List.forall_mem_cons.2 ⟨sub7_259, List.forall_mem_cons.2 ⟨sub7_260, List.forall_mem_cons.2 ⟨sub7_261, List.forall_mem_cons.2 ⟨sub7_262, List.forall_mem_cons.2 ⟨sub7_263, List.forall_mem_cons.2 ⟨sub7_264, List.forall_mem_cons.2 ⟨sub7_265, List.forall_mem_cons.2 ⟨sub7_266, List.forall_mem_cons.2 ⟨sub7_267, List.forall_mem_cons.2 ⟨sub7_268, List.forall_mem_cons.2 ⟨sub7_269, List.forall_mem_cons.2 ⟨sub7_270, List.forall_mem_cons.2 ⟨sub7_271, List.forall_mem_cons.2 ⟨sub7_272, List.forall_mem_cons.2 ⟨sub7_273, List.forall_mem_cons.2 ⟨sub7_274, List.forall_mem_cons.2 ⟨sub7_275, List.forall_mem_cons.2 ⟨sub7_276, List.forall_mem_cons.2 ⟨sub7_277, List.forall_mem_cons.2 ⟨sub7_278, List.forall_mem_cons.2 ⟨sub7_279, List.forall_mem_cons.2 ⟨sub7_280, List.forall_mem_cons.2 ⟨sub7_281, List.forall_mem_cons.2 ⟨sub7_282, List.forall_mem_cons.2 ⟨sub7_283, List.forall_mem_cons.2 ⟨sub7_284, List.forall_mem_cons.2 ⟨sub7_285, List.forall_mem_cons.2 ⟨sub7_286, List.forall_mem_cons.2 ⟨sub7_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_288 : sub7 [-2, 0, 3] = true := by decide +kernel
theorem sub7_289 : sub7 [-2, 0, 4] = true := by decide +kernel
theorem sub7_290 : sub7 [-2, 0, 5] = true := by decide +kernel
theorem sub7_291 : sub7 [-2, 0, 6] = true := by decide +kernel
theorem sub7_292 : sub7 [-2, 0, 7] = true := by decide +kernel
theorem sub7_293 : sub7 [-2, 0, 8] = true := by decide +kernel
theorem sub7_294 : sub7 [-2, 1, -8] = true := by decide +kernel
theorem sub7_295 : sub7 [-2, 1, -7] = true := by decide +kernel
theorem sub7_296 : sub7 [-2, 1, -6] = true := by decide +kernel
theorem sub7_297 : sub7 [-2, 1, -5] = true := by decide +kernel
theorem sub7_298 : sub7 [-2, 1, -4] = true := by decide +kernel
theorem sub7_299 : sub7 [-2, 1, -3] = true := by decide +kernel
theorem sub7_300 : sub7 [-2, 1, -2] = true := by decide +kernel
theorem sub7_301 : sub7 [-2, 1, -1] = true := by decide +kernel
theorem sub7_302 : sub7 [-2, 1, 0] = true := by decide +kernel
theorem sub7_303 : sub7 [-2, 1, 1] = true := by decide +kernel
theorem sub7_304 : sub7 [-2, 1, 2] = true := by decide +kernel
theorem sub7_305 : sub7 [-2, 1, 3] = true := by decide +kernel
theorem sub7_306 : sub7 [-2, 1, 4] = true := by decide +kernel
theorem sub7_307 : sub7 [-2, 1, 5] = true := by decide +kernel
theorem sub7_308 : sub7 [-2, 1, 6] = true := by decide +kernel
theorem sub7_309 : sub7 [-2, 1, 7] = true := by decide +kernel
theorem sub7_310 : sub7 [-2, 1, 8] = true := by decide +kernel
theorem sub7_311 : sub7 [-2, 2, -8] = true := by decide +kernel
theorem sub7_312 : sub7 [-2, 2, -7] = true := by decide +kernel
theorem sub7_313 : sub7 [-2, 2, -6] = true := by decide +kernel
theorem sub7_314 : sub7 [-2, 2, -5] = true := by decide +kernel
theorem sub7_315 : sub7 [-2, 2, -4] = true := by decide +kernel
theorem sub7_316 : sub7 [-2, 2, -3] = true := by decide +kernel
theorem sub7_317 : sub7 [-2, 2, -2] = true := by decide +kernel
theorem sub7_318 : sub7 [-2, 2, -1] = true := by decide +kernel
theorem sub7_319 : sub7 [-2, 2, 0] = true := by decide +kernel
theorem sb7_9 : ∀ q ∈ blk7_9, sub7 q = true := by
  unfold blk7_9
  exact List.forall_mem_cons.2 ⟨sub7_288, List.forall_mem_cons.2 ⟨sub7_289, List.forall_mem_cons.2 ⟨sub7_290, List.forall_mem_cons.2 ⟨sub7_291, List.forall_mem_cons.2 ⟨sub7_292, List.forall_mem_cons.2 ⟨sub7_293, List.forall_mem_cons.2 ⟨sub7_294, List.forall_mem_cons.2 ⟨sub7_295, List.forall_mem_cons.2 ⟨sub7_296, List.forall_mem_cons.2 ⟨sub7_297, List.forall_mem_cons.2 ⟨sub7_298, List.forall_mem_cons.2 ⟨sub7_299, List.forall_mem_cons.2 ⟨sub7_300, List.forall_mem_cons.2 ⟨sub7_301, List.forall_mem_cons.2 ⟨sub7_302, List.forall_mem_cons.2 ⟨sub7_303, List.forall_mem_cons.2 ⟨sub7_304, List.forall_mem_cons.2 ⟨sub7_305, List.forall_mem_cons.2 ⟨sub7_306, List.forall_mem_cons.2 ⟨sub7_307, List.forall_mem_cons.2 ⟨sub7_308, List.forall_mem_cons.2 ⟨sub7_309, List.forall_mem_cons.2 ⟨sub7_310, List.forall_mem_cons.2 ⟨sub7_311, List.forall_mem_cons.2 ⟨sub7_312, List.forall_mem_cons.2 ⟨sub7_313, List.forall_mem_cons.2 ⟨sub7_314, List.forall_mem_cons.2 ⟨sub7_315, List.forall_mem_cons.2 ⟨sub7_316, List.forall_mem_cons.2 ⟨sub7_317, List.forall_mem_cons.2 ⟨sub7_318, List.forall_mem_cons.2 ⟨sub7_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_320 : sub7 [-2, 2, 1] = true := by decide +kernel
theorem sub7_321 : sub7 [-2, 2, 2] = true := by decide +kernel
theorem sub7_322 : sub7 [-2, 2, 3] = true := by decide +kernel
theorem sub7_323 : sub7 [-2, 2, 4] = true := by decide +kernel
theorem sub7_324 : sub7 [-2, 2, 5] = true := by decide +kernel
theorem sub7_325 : sub7 [-2, 2, 6] = true := by decide +kernel
theorem sub7_326 : sub7 [-2, 2, 7] = true := by decide +kernel
theorem sub7_327 : sub7 [-2, 2, 8] = true := by decide +kernel
theorem sub7_328 : sub7 [-2, 3, -7] = true := by decide +kernel
theorem sub7_329 : sub7 [-2, 3, -6] = true := by decide +kernel
theorem sub7_330 : sub7 [-2, 3, -5] = true := by decide +kernel
theorem sub7_331 : sub7 [-2, 3, -4] = true := by decide +kernel
theorem sub7_332 : sub7 [-2, 3, -3] = true := by decide +kernel
theorem sub7_333 : sub7 [-2, 3, -2] = true := by decide +kernel
theorem sub7_334 : sub7 [-2, 3, -1] = true := by decide +kernel
theorem sub7_335 : sub7 [-2, 3, 0] = true := by decide +kernel
theorem sub7_336 : sub7 [-2, 3, 1] = true := by decide +kernel
theorem sub7_337 : sub7 [-2, 3, 2] = true := by decide +kernel
theorem sub7_338 : sub7 [-2, 3, 3] = true := by decide +kernel
theorem sub7_339 : sub7 [-2, 3, 4] = true := by decide +kernel
theorem sub7_340 : sub7 [-2, 3, 5] = true := by decide +kernel
theorem sub7_341 : sub7 [-2, 3, 6] = true := by decide +kernel
theorem sub7_342 : sub7 [-2, 3, 7] = true := by decide +kernel
theorem sub7_343 : sub7 [-2, 3, 8] = true := by decide +kernel
theorem sub7_344 : sub7 [-2, 4, -5] = true := by decide +kernel
theorem sub7_345 : sub7 [-2, 4, -4] = true := by decide +kernel
theorem sub7_346 : sub7 [-2, 4, -3] = true := by decide +kernel
theorem sub7_347 : sub7 [-2, 4, -2] = true := by decide +kernel
theorem sub7_348 : sub7 [-2, 4, -1] = true := by decide +kernel
theorem sub7_349 : sub7 [-2, 4, 0] = true := by decide +kernel
theorem sub7_350 : sub7 [-2, 4, 1] = true := by decide +kernel
theorem sub7_351 : sub7 [-2, 4, 2] = true := by decide +kernel
theorem sb7_10 : ∀ q ∈ blk7_10, sub7 q = true := by
  unfold blk7_10
  exact List.forall_mem_cons.2 ⟨sub7_320, List.forall_mem_cons.2 ⟨sub7_321, List.forall_mem_cons.2 ⟨sub7_322, List.forall_mem_cons.2 ⟨sub7_323, List.forall_mem_cons.2 ⟨sub7_324, List.forall_mem_cons.2 ⟨sub7_325, List.forall_mem_cons.2 ⟨sub7_326, List.forall_mem_cons.2 ⟨sub7_327, List.forall_mem_cons.2 ⟨sub7_328, List.forall_mem_cons.2 ⟨sub7_329, List.forall_mem_cons.2 ⟨sub7_330, List.forall_mem_cons.2 ⟨sub7_331, List.forall_mem_cons.2 ⟨sub7_332, List.forall_mem_cons.2 ⟨sub7_333, List.forall_mem_cons.2 ⟨sub7_334, List.forall_mem_cons.2 ⟨sub7_335, List.forall_mem_cons.2 ⟨sub7_336, List.forall_mem_cons.2 ⟨sub7_337, List.forall_mem_cons.2 ⟨sub7_338, List.forall_mem_cons.2 ⟨sub7_339, List.forall_mem_cons.2 ⟨sub7_340, List.forall_mem_cons.2 ⟨sub7_341, List.forall_mem_cons.2 ⟨sub7_342, List.forall_mem_cons.2 ⟨sub7_343, List.forall_mem_cons.2 ⟨sub7_344, List.forall_mem_cons.2 ⟨sub7_345, List.forall_mem_cons.2 ⟨sub7_346, List.forall_mem_cons.2 ⟨sub7_347, List.forall_mem_cons.2 ⟨sub7_348, List.forall_mem_cons.2 ⟨sub7_349, List.forall_mem_cons.2 ⟨sub7_350, List.forall_mem_cons.2 ⟨sub7_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_352 : sub7 [-2, 4, 3] = true := by decide +kernel
theorem sub7_353 : sub7 [-2, 4, 4] = true := by decide +kernel
theorem sub7_354 : sub7 [-2, 4, 5] = true := by decide +kernel
theorem sub7_355 : sub7 [-2, 4, 6] = true := by decide +kernel
theorem sub7_356 : sub7 [-2, 4, 7] = true := by decide +kernel
theorem sub7_357 : sub7 [-2, 4, 8] = true := by decide +kernel
theorem sub7_358 : sub7 [-2, 5] = true := by decide +kernel
theorem sub7_359 : sub7 [-2, 6] = true := by decide +kernel
theorem sub7_360 : sub7 [-1, -7] = true := by decide +kernel
theorem sub7_361 : sub7 [-1, -6] = true := by decide +kernel
theorem sub7_362 : sub7 [-1, -5] = true := by decide +kernel
theorem sub7_363 : sub7 [-1, -4, -9] = true := by decide +kernel
theorem sub7_364 : sub7 [-1, -4, -8] = true := by decide +kernel
theorem sub7_365 : sub7 [-1, -4, -7] = true := by decide +kernel
theorem sub7_366 : sub7 [-1, -4, -6] = true := by decide +kernel
theorem sub7_367 : sub7 [-1, -4, -5] = true := by decide +kernel
theorem sub7_368 : sub7 [-1, -4, -4] = true := by decide +kernel
theorem sub7_369 : sub7 [-1, -4, -3] = true := by decide +kernel
theorem sub7_370 : sub7 [-1, -4, -2] = true := by decide +kernel
theorem sub7_371 : sub7 [-1, -4, -1] = true := by decide +kernel
theorem sub7_372 : sub7 [-1, -4, 0] = true := by decide +kernel
theorem sub7_373 : sub7 [-1, -4, 1] = true := by decide +kernel
theorem sub7_374 : sub7 [-1, -4, 2] = true := by decide +kernel
theorem sub7_375 : sub7 [-1, -4, 3] = true := by decide +kernel
theorem sub7_376 : sub7 [-1, -4, 4] = true := by decide +kernel
theorem sub7_377 : sub7 [-1, -4, 5] = true := by decide +kernel
theorem sub7_378 : sub7 [-1, -3, -9] = true := by decide +kernel
theorem sub7_379 : sub7 [-1, -3, -8] = true := by decide +kernel
theorem sub7_380 : sub7 [-1, -3, -7] = true := by decide +kernel
theorem sub7_381 : sub7 [-1, -3, -6] = true := by decide +kernel
theorem sub7_382 : sub7 [-1, -3, -5] = true := by decide +kernel
theorem sub7_383 : sub7 [-1, -3, -4] = true := by decide +kernel
theorem sb7_11 : ∀ q ∈ blk7_11, sub7 q = true := by
  unfold blk7_11
  exact List.forall_mem_cons.2 ⟨sub7_352, List.forall_mem_cons.2 ⟨sub7_353, List.forall_mem_cons.2 ⟨sub7_354, List.forall_mem_cons.2 ⟨sub7_355, List.forall_mem_cons.2 ⟨sub7_356, List.forall_mem_cons.2 ⟨sub7_357, List.forall_mem_cons.2 ⟨sub7_358, List.forall_mem_cons.2 ⟨sub7_359, List.forall_mem_cons.2 ⟨sub7_360, List.forall_mem_cons.2 ⟨sub7_361, List.forall_mem_cons.2 ⟨sub7_362, List.forall_mem_cons.2 ⟨sub7_363, List.forall_mem_cons.2 ⟨sub7_364, List.forall_mem_cons.2 ⟨sub7_365, List.forall_mem_cons.2 ⟨sub7_366, List.forall_mem_cons.2 ⟨sub7_367, List.forall_mem_cons.2 ⟨sub7_368, List.forall_mem_cons.2 ⟨sub7_369, List.forall_mem_cons.2 ⟨sub7_370, List.forall_mem_cons.2 ⟨sub7_371, List.forall_mem_cons.2 ⟨sub7_372, List.forall_mem_cons.2 ⟨sub7_373, List.forall_mem_cons.2 ⟨sub7_374, List.forall_mem_cons.2 ⟨sub7_375, List.forall_mem_cons.2 ⟨sub7_376, List.forall_mem_cons.2 ⟨sub7_377, List.forall_mem_cons.2 ⟨sub7_378, List.forall_mem_cons.2 ⟨sub7_379, List.forall_mem_cons.2 ⟨sub7_380, List.forall_mem_cons.2 ⟨sub7_381, List.forall_mem_cons.2 ⟨sub7_382, List.forall_mem_cons.2 ⟨sub7_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_384 : sub7 [-1, -3, -3] = true := by decide +kernel
theorem sub7_385 : sub7 [-1, -3, -2] = true := by decide +kernel
theorem sub7_386 : sub7 [-1, -3, -1] = true := by decide +kernel
theorem sub7_387 : sub7 [-1, -3, 0] = true := by decide +kernel
theorem sub7_388 : sub7 [-1, -3, 1] = true := by decide +kernel
theorem sub7_389 : sub7 [-1, -3, 2] = true := by decide +kernel
theorem sub7_390 : sub7 [-1, -3, 3] = true := by decide +kernel
theorem sub7_391 : sub7 [-1, -3, 4] = true := by decide +kernel
theorem sub7_392 : sub7 [-1, -3, 5] = true := by decide +kernel
theorem sub7_393 : sub7 [-1, -3, 6] = true := by decide +kernel
theorem sub7_394 : sub7 [-1, -2, -10] = true := by decide +kernel
theorem sub7_395 : sub7 [-1, -2, -9] = true := by decide +kernel
theorem sub7_396 : sub7 [-1, -2, -8] = true := by decide +kernel
theorem sub7_397 : sub7 [-1, -2, -7] = true := by decide +kernel
theorem sub7_398 : sub7 [-1, -2, -6] = true := by decide +kernel
theorem sub7_399 : sub7 [-1, -2, -5] = true := by decide +kernel
theorem sub7_400 : sub7 [-1, -2, -4] = true := by decide +kernel
theorem sub7_401 : sub7 [-1, -2, -3] = true := by decide +kernel
theorem sub7_402 : sub7 [-1, -2, -2] = true := by decide +kernel
theorem sub7_403 : sub7 [-1, -2, -1] = true := by decide +kernel
theorem sub7_404 : sub7 [-1, -2, 0] = true := by decide +kernel
theorem sub7_405 : sub7 [-1, -2, 1] = true := by decide +kernel
theorem sub7_406 : sub7 [-1, -2, 2] = true := by decide +kernel
theorem sub7_407 : sub7 [-1, -2, 3] = true := by decide +kernel
theorem sub7_408 : sub7 [-1, -2, 4] = true := by decide +kernel
theorem sub7_409 : sub7 [-1, -2, 5] = true := by decide +kernel
theorem sub7_410 : sub7 [-1, -2, 6] = true := by decide +kernel
theorem sub7_411 : sub7 [-1, -2, 7] = true := by decide +kernel
theorem sub7_412 : sub7 [-1, -1, -9] = true := by decide +kernel
theorem sub7_413 : sub7 [-1, -1, -8] = true := by decide +kernel
theorem sub7_414 : sub7 [-1, -1, -7] = true := by decide +kernel
theorem sub7_415 : sub7 [-1, -1, -6] = true := by decide +kernel
theorem sb7_12 : ∀ q ∈ blk7_12, sub7 q = true := by
  unfold blk7_12
  exact List.forall_mem_cons.2 ⟨sub7_384, List.forall_mem_cons.2 ⟨sub7_385, List.forall_mem_cons.2 ⟨sub7_386, List.forall_mem_cons.2 ⟨sub7_387, List.forall_mem_cons.2 ⟨sub7_388, List.forall_mem_cons.2 ⟨sub7_389, List.forall_mem_cons.2 ⟨sub7_390, List.forall_mem_cons.2 ⟨sub7_391, List.forall_mem_cons.2 ⟨sub7_392, List.forall_mem_cons.2 ⟨sub7_393, List.forall_mem_cons.2 ⟨sub7_394, List.forall_mem_cons.2 ⟨sub7_395, List.forall_mem_cons.2 ⟨sub7_396, List.forall_mem_cons.2 ⟨sub7_397, List.forall_mem_cons.2 ⟨sub7_398, List.forall_mem_cons.2 ⟨sub7_399, List.forall_mem_cons.2 ⟨sub7_400, List.forall_mem_cons.2 ⟨sub7_401, List.forall_mem_cons.2 ⟨sub7_402, List.forall_mem_cons.2 ⟨sub7_403, List.forall_mem_cons.2 ⟨sub7_404, List.forall_mem_cons.2 ⟨sub7_405, List.forall_mem_cons.2 ⟨sub7_406, List.forall_mem_cons.2 ⟨sub7_407, List.forall_mem_cons.2 ⟨sub7_408, List.forall_mem_cons.2 ⟨sub7_409, List.forall_mem_cons.2 ⟨sub7_410, List.forall_mem_cons.2 ⟨sub7_411, List.forall_mem_cons.2 ⟨sub7_412, List.forall_mem_cons.2 ⟨sub7_413, List.forall_mem_cons.2 ⟨sub7_414, List.forall_mem_cons.2 ⟨sub7_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_416 : sub7 [-1, -1, -5] = true := by decide +kernel
theorem sub7_417 : sub7 [-1, -1, -4] = true := by decide +kernel
theorem sub7_418 : sub7 [-1, -1, -3] = true := by decide +kernel
theorem sub7_419 : sub7 [-1, -1, -2] = true := by decide +kernel
theorem sub7_420 : sub7 [-1, -1, -1] = true := by decide +kernel
theorem sub7_421 : sub7 [-1, -1, 0] = true := by decide +kernel
theorem sub7_422 : sub7 [-1, -1, 1] = true := by decide +kernel
theorem sub7_423 : sub7 [-1, -1, 2] = true := by decide +kernel
theorem sub7_424 : sub7 [-1, -1, 3] = true := by decide +kernel
theorem sub7_425 : sub7 [-1, -1, 4] = true := by decide +kernel
theorem sub7_426 : sub7 [-1, -1, 5] = true := by decide +kernel
theorem sub7_427 : sub7 [-1, -1, 6] = true := by decide +kernel
theorem sub7_428 : sub7 [-1, -1, 7] = true := by decide +kernel
theorem sub7_429 : sub7 [-1, -1, 8] = true := by decide +kernel
theorem sub7_430 : sub7 [-1, 0, -9] = true := by decide +kernel
theorem sub7_431 : sub7 [-1, 0, -8] = true := by decide +kernel
theorem sub7_432 : sub7 [-1, 0, -7] = true := by decide +kernel
theorem sub7_433 : sub7 [-1, 0, -6] = true := by decide +kernel
theorem sub7_434 : sub7 [-1, 0, -5] = true := by decide +kernel
theorem sub7_435 : sub7 [-1, 0, -4] = true := by decide +kernel
theorem sub7_436 : sub7 [-1, 0, -3] = true := by decide +kernel
theorem sub7_437 : sub7 [-1, 0, -2] = true := by decide +kernel
theorem sub7_438 : sub7 [-1, 0, -1] = true := by decide +kernel
theorem sub7_439 : sub7 [-1, 0, 0] = true := by decide +kernel
theorem sub7_440 : sub7 [-1, 0, 1] = true := by decide +kernel
theorem sub7_441 : sub7 [-1, 0, 2] = true := by decide +kernel
theorem sub7_442 : sub7 [-1, 0, 3] = true := by decide +kernel
theorem sub7_443 : sub7 [-1, 0, 4] = true := by decide +kernel
theorem sub7_444 : sub7 [-1, 0, 5] = true := by decide +kernel
theorem sub7_445 : sub7 [-1, 0, 6] = true := by decide +kernel
theorem sub7_446 : sub7 [-1, 0, 7] = true := by decide +kernel
theorem sub7_447 : sub7 [-1, 0, 8] = true := by decide +kernel
theorem sb7_13 : ∀ q ∈ blk7_13, sub7 q = true := by
  unfold blk7_13
  exact List.forall_mem_cons.2 ⟨sub7_416, List.forall_mem_cons.2 ⟨sub7_417, List.forall_mem_cons.2 ⟨sub7_418, List.forall_mem_cons.2 ⟨sub7_419, List.forall_mem_cons.2 ⟨sub7_420, List.forall_mem_cons.2 ⟨sub7_421, List.forall_mem_cons.2 ⟨sub7_422, List.forall_mem_cons.2 ⟨sub7_423, List.forall_mem_cons.2 ⟨sub7_424, List.forall_mem_cons.2 ⟨sub7_425, List.forall_mem_cons.2 ⟨sub7_426, List.forall_mem_cons.2 ⟨sub7_427, List.forall_mem_cons.2 ⟨sub7_428, List.forall_mem_cons.2 ⟨sub7_429, List.forall_mem_cons.2 ⟨sub7_430, List.forall_mem_cons.2 ⟨sub7_431, List.forall_mem_cons.2 ⟨sub7_432, List.forall_mem_cons.2 ⟨sub7_433, List.forall_mem_cons.2 ⟨sub7_434, List.forall_mem_cons.2 ⟨sub7_435, List.forall_mem_cons.2 ⟨sub7_436, List.forall_mem_cons.2 ⟨sub7_437, List.forall_mem_cons.2 ⟨sub7_438, List.forall_mem_cons.2 ⟨sub7_439, List.forall_mem_cons.2 ⟨sub7_440, List.forall_mem_cons.2 ⟨sub7_441, List.forall_mem_cons.2 ⟨sub7_442, List.forall_mem_cons.2 ⟨sub7_443, List.forall_mem_cons.2 ⟨sub7_444, List.forall_mem_cons.2 ⟨sub7_445, List.forall_mem_cons.2 ⟨sub7_446, List.forall_mem_cons.2 ⟨sub7_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_448 : sub7 [-1, 1, -9] = true := by decide +kernel
theorem sub7_449 : sub7 [-1, 1, -8] = true := by decide +kernel
theorem sub7_450 : sub7 [-1, 1, -7] = true := by decide +kernel
theorem sub7_451 : sub7 [-1, 1, -6] = true := by decide +kernel
theorem sub7_452 : sub7 [-1, 1, -5] = true := by decide +kernel
theorem sub7_453 : sub7 [-1, 1, -4] = true := by decide +kernel
theorem sub7_454 : sub7 [-1, 1, -3] = true := by decide +kernel
theorem sub7_455 : sub7 [-1, 1, -2] = true := by decide +kernel
theorem sub7_456 : sub7 [-1, 1, -1] = true := by decide +kernel
theorem sub7_457 : sub7 [-1, 1, 0] = true := by decide +kernel
theorem sub7_458 : sub7 [-1, 1, 1] = true := by decide +kernel
theorem sub7_459 : sub7 [-1, 1, 2] = true := by decide +kernel
theorem sub7_460 : sub7 [-1, 1, 3] = true := by decide +kernel
theorem sub7_461 : sub7 [-1, 1, 4] = true := by decide +kernel
theorem sub7_462 : sub7 [-1, 1, 5] = true := by decide +kernel
theorem sub7_463 : sub7 [-1, 1, 6] = true := by decide +kernel
theorem sub7_464 : sub7 [-1, 1, 7] = true := by decide +kernel
theorem sub7_465 : sub7 [-1, 1, 8] = true := by decide +kernel
theorem sub7_466 : sub7 [-1, 1, 9] = true := by decide +kernel
theorem sub7_467 : sub7 [-1, 2, -8] = true := by decide +kernel
theorem sub7_468 : sub7 [-1, 2, -7] = true := by decide +kernel
theorem sub7_469 : sub7 [-1, 2, -6] = true := by decide +kernel
theorem sub7_470 : sub7 [-1, 2, -5] = true := by decide +kernel
theorem sub7_471 : sub7 [-1, 2, -4] = true := by decide +kernel
theorem sub7_472 : sub7 [-1, 2, -3] = true := by decide +kernel
theorem sub7_473 : sub7 [-1, 2, -2] = true := by decide +kernel
theorem sub7_474 : sub7 [-1, 2, -1] = true := by decide +kernel
theorem sub7_475 : sub7 [-1, 2, 0] = true := by decide +kernel
theorem sub7_476 : sub7 [-1, 2, 1] = true := by decide +kernel
theorem sub7_477 : sub7 [-1, 2, 2] = true := by decide +kernel
theorem sub7_478 : sub7 [-1, 2, 3] = true := by decide +kernel
theorem sub7_479 : sub7 [-1, 2, 4] = true := by decide +kernel
theorem sb7_14 : ∀ q ∈ blk7_14, sub7 q = true := by
  unfold blk7_14
  exact List.forall_mem_cons.2 ⟨sub7_448, List.forall_mem_cons.2 ⟨sub7_449, List.forall_mem_cons.2 ⟨sub7_450, List.forall_mem_cons.2 ⟨sub7_451, List.forall_mem_cons.2 ⟨sub7_452, List.forall_mem_cons.2 ⟨sub7_453, List.forall_mem_cons.2 ⟨sub7_454, List.forall_mem_cons.2 ⟨sub7_455, List.forall_mem_cons.2 ⟨sub7_456, List.forall_mem_cons.2 ⟨sub7_457, List.forall_mem_cons.2 ⟨sub7_458, List.forall_mem_cons.2 ⟨sub7_459, List.forall_mem_cons.2 ⟨sub7_460, List.forall_mem_cons.2 ⟨sub7_461, List.forall_mem_cons.2 ⟨sub7_462, List.forall_mem_cons.2 ⟨sub7_463, List.forall_mem_cons.2 ⟨sub7_464, List.forall_mem_cons.2 ⟨sub7_465, List.forall_mem_cons.2 ⟨sub7_466, List.forall_mem_cons.2 ⟨sub7_467, List.forall_mem_cons.2 ⟨sub7_468, List.forall_mem_cons.2 ⟨sub7_469, List.forall_mem_cons.2 ⟨sub7_470, List.forall_mem_cons.2 ⟨sub7_471, List.forall_mem_cons.2 ⟨sub7_472, List.forall_mem_cons.2 ⟨sub7_473, List.forall_mem_cons.2 ⟨sub7_474, List.forall_mem_cons.2 ⟨sub7_475, List.forall_mem_cons.2 ⟨sub7_476, List.forall_mem_cons.2 ⟨sub7_477, List.forall_mem_cons.2 ⟨sub7_478, List.forall_mem_cons.2 ⟨sub7_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_480 : sub7 [-1, 2, 5] = true := by decide +kernel
theorem sub7_481 : sub7 [-1, 2, 6] = true := by decide +kernel
theorem sub7_482 : sub7 [-1, 2, 7] = true := by decide +kernel
theorem sub7_483 : sub7 [-1, 2, 8] = true := by decide +kernel
theorem sub7_484 : sub7 [-1, 2, 9] = true := by decide +kernel
theorem sub7_485 : sub7 [-1, 3, -7] = true := by decide +kernel
theorem sub7_486 : sub7 [-1, 3, -6] = true := by decide +kernel
theorem sub7_487 : sub7 [-1, 3, -5] = true := by decide +kernel
theorem sub7_488 : sub7 [-1, 3, -4] = true := by decide +kernel
theorem sub7_489 : sub7 [-1, 3, -3] = true := by decide +kernel
theorem sub7_490 : sub7 [-1, 3, -2] = true := by decide +kernel
theorem sub7_491 : sub7 [-1, 3, -1] = true := by decide +kernel
theorem sub7_492 : sub7 [-1, 3, 0] = true := by decide +kernel
theorem sub7_493 : sub7 [-1, 3, 1] = true := by decide +kernel
theorem sub7_494 : sub7 [-1, 3, 2] = true := by decide +kernel
theorem sub7_495 : sub7 [-1, 3, 3] = true := by decide +kernel
theorem sub7_496 : sub7 [-1, 3, 4] = true := by decide +kernel
theorem sub7_497 : sub7 [-1, 3, 5] = true := by decide +kernel
theorem sub7_498 : sub7 [-1, 3, 6] = true := by decide +kernel
theorem sub7_499 : sub7 [-1, 3, 7] = true := by decide +kernel
theorem sub7_500 : sub7 [-1, 3, 8] = true := by decide +kernel
theorem sub7_501 : sub7 [-1, 3, 9] = true := by decide +kernel
theorem sub7_502 : sub7 [-1, 4, -6] = true := by decide +kernel
theorem sub7_503 : sub7 [-1, 4, -5] = true := by decide +kernel
theorem sub7_504 : sub7 [-1, 4, -4] = true := by decide +kernel
theorem sub7_505 : sub7 [-1, 4, -3] = true := by decide +kernel
theorem sub7_506 : sub7 [-1, 4, -2] = true := by decide +kernel
theorem sub7_507 : sub7 [-1, 4, -1] = true := by decide +kernel
theorem sub7_508 : sub7 [-1, 4, 0] = true := by decide +kernel
theorem sub7_509 : sub7 [-1, 4, 1] = true := by decide +kernel
theorem sub7_510 : sub7 [-1, 4, 2] = true := by decide +kernel
theorem sub7_511 : sub7 [-1, 4, 3] = true := by decide +kernel
theorem sb7_15 : ∀ q ∈ blk7_15, sub7 q = true := by
  unfold blk7_15
  exact List.forall_mem_cons.2 ⟨sub7_480, List.forall_mem_cons.2 ⟨sub7_481, List.forall_mem_cons.2 ⟨sub7_482, List.forall_mem_cons.2 ⟨sub7_483, List.forall_mem_cons.2 ⟨sub7_484, List.forall_mem_cons.2 ⟨sub7_485, List.forall_mem_cons.2 ⟨sub7_486, List.forall_mem_cons.2 ⟨sub7_487, List.forall_mem_cons.2 ⟨sub7_488, List.forall_mem_cons.2 ⟨sub7_489, List.forall_mem_cons.2 ⟨sub7_490, List.forall_mem_cons.2 ⟨sub7_491, List.forall_mem_cons.2 ⟨sub7_492, List.forall_mem_cons.2 ⟨sub7_493, List.forall_mem_cons.2 ⟨sub7_494, List.forall_mem_cons.2 ⟨sub7_495, List.forall_mem_cons.2 ⟨sub7_496, List.forall_mem_cons.2 ⟨sub7_497, List.forall_mem_cons.2 ⟨sub7_498, List.forall_mem_cons.2 ⟨sub7_499, List.forall_mem_cons.2 ⟨sub7_500, List.forall_mem_cons.2 ⟨sub7_501, List.forall_mem_cons.2 ⟨sub7_502, List.forall_mem_cons.2 ⟨sub7_503, List.forall_mem_cons.2 ⟨sub7_504, List.forall_mem_cons.2 ⟨sub7_505, List.forall_mem_cons.2 ⟨sub7_506, List.forall_mem_cons.2 ⟨sub7_507, List.forall_mem_cons.2 ⟨sub7_508, List.forall_mem_cons.2 ⟨sub7_509, List.forall_mem_cons.2 ⟨sub7_510, List.forall_mem_cons.2 ⟨sub7_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_512 : sub7 [-1, 4, 4] = true := by decide +kernel
theorem sub7_513 : sub7 [-1, 4, 5] = true := by decide +kernel
theorem sub7_514 : sub7 [-1, 4, 6] = true := by decide +kernel
theorem sub7_515 : sub7 [-1, 4, 7] = true := by decide +kernel
theorem sub7_516 : sub7 [-1, 4, 8] = true := by decide +kernel
theorem sub7_517 : sub7 [-1, 5] = true := by decide +kernel
theorem sub7_518 : sub7 [-1, 6] = true := by decide +kernel
theorem sub7_519 : sub7 [0, -7] = true := by decide +kernel
theorem sub7_520 : sub7 [0, -6] = true := by decide +kernel
theorem sub7_521 : sub7 [0, -5] = true := by decide +kernel
theorem sub7_522 : sub7 [0, -4, -9] = true := by decide +kernel
theorem sub7_523 : sub7 [0, -4, -8] = true := by decide +kernel
theorem sub7_524 : sub7 [0, -4, -7] = true := by decide +kernel
theorem sub7_525 : sub7 [0, -4, -6] = true := by decide +kernel
theorem sub7_526 : sub7 [0, -4, -5] = true := by decide +kernel
theorem sub7_527 : sub7 [0, -4, -4] = true := by decide +kernel
theorem sub7_528 : sub7 [0, -4, -3] = true := by decide +kernel
theorem sub7_529 : sub7 [0, -4, -2] = true := by decide +kernel
theorem sub7_530 : sub7 [0, -4, -1] = true := by decide +kernel
theorem sub7_531 : sub7 [0, -4, 0] = true := by decide +kernel
theorem sub7_532 : sub7 [0, -4, 1] = true := by decide +kernel
theorem sub7_533 : sub7 [0, -4, 2] = true := by decide +kernel
theorem sub7_534 : sub7 [0, -4, 3] = true := by decide +kernel
theorem sub7_535 : sub7 [0, -4, 4] = true := by decide +kernel
theorem sub7_536 : sub7 [0, -4, 5] = true := by decide +kernel
theorem sub7_537 : sub7 [0, -3, -10] = true := by decide +kernel
theorem sub7_538 : sub7 [0, -3, -9] = true := by decide +kernel
theorem sub7_539 : sub7 [0, -3, -8] = true := by decide +kernel
theorem sub7_540 : sub7 [0, -3, -7] = true := by decide +kernel
theorem sub7_541 : sub7 [0, -3, -6] = true := by decide +kernel
theorem sub7_542 : sub7 [0, -3, -5] = true := by decide +kernel
theorem sub7_543 : sub7 [0, -3, -4] = true := by decide +kernel
theorem sb7_16 : ∀ q ∈ blk7_16, sub7 q = true := by
  unfold blk7_16
  exact List.forall_mem_cons.2 ⟨sub7_512, List.forall_mem_cons.2 ⟨sub7_513, List.forall_mem_cons.2 ⟨sub7_514, List.forall_mem_cons.2 ⟨sub7_515, List.forall_mem_cons.2 ⟨sub7_516, List.forall_mem_cons.2 ⟨sub7_517, List.forall_mem_cons.2 ⟨sub7_518, List.forall_mem_cons.2 ⟨sub7_519, List.forall_mem_cons.2 ⟨sub7_520, List.forall_mem_cons.2 ⟨sub7_521, List.forall_mem_cons.2 ⟨sub7_522, List.forall_mem_cons.2 ⟨sub7_523, List.forall_mem_cons.2 ⟨sub7_524, List.forall_mem_cons.2 ⟨sub7_525, List.forall_mem_cons.2 ⟨sub7_526, List.forall_mem_cons.2 ⟨sub7_527, List.forall_mem_cons.2 ⟨sub7_528, List.forall_mem_cons.2 ⟨sub7_529, List.forall_mem_cons.2 ⟨sub7_530, List.forall_mem_cons.2 ⟨sub7_531, List.forall_mem_cons.2 ⟨sub7_532, List.forall_mem_cons.2 ⟨sub7_533, List.forall_mem_cons.2 ⟨sub7_534, List.forall_mem_cons.2 ⟨sub7_535, List.forall_mem_cons.2 ⟨sub7_536, List.forall_mem_cons.2 ⟨sub7_537, List.forall_mem_cons.2 ⟨sub7_538, List.forall_mem_cons.2 ⟨sub7_539, List.forall_mem_cons.2 ⟨sub7_540, List.forall_mem_cons.2 ⟨sub7_541, List.forall_mem_cons.2 ⟨sub7_542, List.forall_mem_cons.2 ⟨sub7_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_544 : sub7 [0, -3, -3] = true := by decide +kernel
theorem sub7_545 : sub7 [0, -3, -2] = true := by decide +kernel
theorem sub7_546 : sub7 [0, -3, -1] = true := by decide +kernel
theorem sub7_547 : sub7 [0, -3, 0] = true := by decide +kernel
theorem sub7_548 : sub7 [0, -3, 1] = true := by decide +kernel
theorem sub7_549 : sub7 [0, -3, 2] = true := by decide +kernel
theorem sub7_550 : sub7 [0, -3, 3] = true := by decide +kernel
theorem sub7_551 : sub7 [0, -3, 4] = true := by decide +kernel
theorem sub7_552 : sub7 [0, -3, 5] = true := by decide +kernel
theorem sub7_553 : sub7 [0, -3, 6] = true := by decide +kernel
theorem sub7_554 : sub7 [0, -2, -10] = true := by decide +kernel
theorem sub7_555 : sub7 [0, -2, -9] = true := by decide +kernel
theorem sub7_556 : sub7 [0, -2, -8] = true := by decide +kernel
theorem sub7_557 : sub7 [0, -2, -7] = true := by decide +kernel
theorem sub7_558 : sub7 [0, -2, -6] = true := by decide +kernel
theorem sub7_559 : sub7 [0, -2, -5] = true := by decide +kernel
theorem sub7_560 : sub7 [0, -2, -4] = true := by decide +kernel
theorem sub7_561 : sub7 [0, -2, -3] = true := by decide +kernel
theorem sub7_562 : sub7 [0, -2, -2] = true := by decide +kernel
theorem sub7_563 : sub7 [0, -2, -1] = true := by decide +kernel
theorem sub7_564 : sub7 [0, -2, 0] = true := by decide +kernel
theorem sub7_565 : sub7 [0, -2, 1] = true := by decide +kernel
theorem sub7_566 : sub7 [0, -2, 2] = true := by decide +kernel
theorem sub7_567 : sub7 [0, -2, 3] = true := by decide +kernel
theorem sub7_568 : sub7 [0, -2, 4] = true := by decide +kernel
theorem sub7_569 : sub7 [0, -2, 5] = true := by decide +kernel
theorem sub7_570 : sub7 [0, -2, 6] = true := by decide +kernel
theorem sub7_571 : sub7 [0, -2, 7] = true := by decide +kernel
theorem sub7_572 : sub7 [0, -1, -10] = true := by decide +kernel
theorem sub7_573 : sub7 [0, -1, -9] = true := by decide +kernel
theorem sub7_574 : sub7 [0, -1, -8] = true := by decide +kernel
theorem sub7_575 : sub7 [0, -1, -7] = true := by decide +kernel
theorem sb7_17 : ∀ q ∈ blk7_17, sub7 q = true := by
  unfold blk7_17
  exact List.forall_mem_cons.2 ⟨sub7_544, List.forall_mem_cons.2 ⟨sub7_545, List.forall_mem_cons.2 ⟨sub7_546, List.forall_mem_cons.2 ⟨sub7_547, List.forall_mem_cons.2 ⟨sub7_548, List.forall_mem_cons.2 ⟨sub7_549, List.forall_mem_cons.2 ⟨sub7_550, List.forall_mem_cons.2 ⟨sub7_551, List.forall_mem_cons.2 ⟨sub7_552, List.forall_mem_cons.2 ⟨sub7_553, List.forall_mem_cons.2 ⟨sub7_554, List.forall_mem_cons.2 ⟨sub7_555, List.forall_mem_cons.2 ⟨sub7_556, List.forall_mem_cons.2 ⟨sub7_557, List.forall_mem_cons.2 ⟨sub7_558, List.forall_mem_cons.2 ⟨sub7_559, List.forall_mem_cons.2 ⟨sub7_560, List.forall_mem_cons.2 ⟨sub7_561, List.forall_mem_cons.2 ⟨sub7_562, List.forall_mem_cons.2 ⟨sub7_563, List.forall_mem_cons.2 ⟨sub7_564, List.forall_mem_cons.2 ⟨sub7_565, List.forall_mem_cons.2 ⟨sub7_566, List.forall_mem_cons.2 ⟨sub7_567, List.forall_mem_cons.2 ⟨sub7_568, List.forall_mem_cons.2 ⟨sub7_569, List.forall_mem_cons.2 ⟨sub7_570, List.forall_mem_cons.2 ⟨sub7_571, List.forall_mem_cons.2 ⟨sub7_572, List.forall_mem_cons.2 ⟨sub7_573, List.forall_mem_cons.2 ⟨sub7_574, List.forall_mem_cons.2 ⟨sub7_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C125
