import ReflectZphi.Data.Cert5.C043.Base

namespace ReflectZphi.Data.Cert5.C043
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub1_96 : sub1 [-3, -2, -1] = true := by decide +kernel
theorem sub1_97 : sub1 [-3, -2, 0] = true := by decide +kernel
theorem sub1_98 : sub1 [-3, -2, 1] = true := by decide +kernel
theorem sub1_99 : sub1 [-3, -2, 2] = true := by decide +kernel
theorem sub1_100 : sub1 [-3, -2, 3] = true := by decide +kernel
theorem sub1_101 : sub1 [-3, -2, 4] = true := by decide +kernel
theorem sub1_102 : sub1 [-3, -2, 5] = true := by decide +kernel
theorem sub1_103 : sub1 [-3, -2, 6] = true := by decide +kernel
theorem sub1_104 : sub1 [-3, -1, -8] = true := by decide +kernel
theorem sub1_105 : sub1 [-3, -1, -7] = true := by decide +kernel
theorem sub1_106 : sub1 [-3, -1, -6] = true := by decide +kernel
theorem sub1_107 : sub1 [-3, -1, -5] = true := by decide +kernel
theorem sub1_108 : sub1 [-3, -1, -4] = true := by decide +kernel
theorem sub1_109 : sub1 [-3, -1, -3] = true := by decide +kernel
theorem sub1_110 : sub1 [-3, -1, -2] = true := by decide +kernel
theorem sub1_111 : sub1 [-3, -1, -1] = true := by decide +kernel
theorem sub1_112 : sub1 [-3, -1, 0] = true := by decide +kernel
theorem sub1_113 : sub1 [-3, -1, 1] = true := by decide +kernel
theorem sub1_114 : sub1 [-3, -1, 2] = true := by decide +kernel
theorem sub1_115 : sub1 [-3, -1, 3] = true := by decide +kernel
theorem sub1_116 : sub1 [-3, -1, 4] = true := by decide +kernel
theorem sub1_117 : sub1 [-3, -1, 5] = true := by decide +kernel
theorem sub1_118 : sub1 [-3, -1, 6] = true := by decide +kernel
theorem sub1_119 : sub1 [-3, 0, -8] = true := by decide +kernel
theorem sub1_120 : sub1 [-3, 0, -7] = true := by decide +kernel
theorem sub1_121 : sub1 [-3, 0, -6] = true := by decide +kernel
theorem sub1_122 : sub1 [-3, 0, -5] = true := by decide +kernel
theorem sub1_123 : sub1 [-3, 0, -4] = true := by decide +kernel
theorem sub1_124 : sub1 [-3, 0, -3] = true := by decide +kernel
theorem sub1_125 : sub1 [-3, 0, -2] = true := by decide +kernel
theorem sub1_126 : sub1 [-3, 0, -1] = true := by decide +kernel
theorem sub1_127 : sub1 [-3, 0, 0] = true := by decide +kernel
theorem sb1_3 : ∀ q ∈ blk1_3, sub1 q = true := by
  unfold blk1_3
  exact List.forall_mem_cons.2 ⟨sub1_96, List.forall_mem_cons.2 ⟨sub1_97, List.forall_mem_cons.2 ⟨sub1_98, List.forall_mem_cons.2 ⟨sub1_99, List.forall_mem_cons.2 ⟨sub1_100, List.forall_mem_cons.2 ⟨sub1_101, List.forall_mem_cons.2 ⟨sub1_102, List.forall_mem_cons.2 ⟨sub1_103, List.forall_mem_cons.2 ⟨sub1_104, List.forall_mem_cons.2 ⟨sub1_105, List.forall_mem_cons.2 ⟨sub1_106, List.forall_mem_cons.2 ⟨sub1_107, List.forall_mem_cons.2 ⟨sub1_108, List.forall_mem_cons.2 ⟨sub1_109, List.forall_mem_cons.2 ⟨sub1_110, List.forall_mem_cons.2 ⟨sub1_111, List.forall_mem_cons.2 ⟨sub1_112, List.forall_mem_cons.2 ⟨sub1_113, List.forall_mem_cons.2 ⟨sub1_114, List.forall_mem_cons.2 ⟨sub1_115, List.forall_mem_cons.2 ⟨sub1_116, List.forall_mem_cons.2 ⟨sub1_117, List.forall_mem_cons.2 ⟨sub1_118, List.forall_mem_cons.2 ⟨sub1_119, List.forall_mem_cons.2 ⟨sub1_120, List.forall_mem_cons.2 ⟨sub1_121, List.forall_mem_cons.2 ⟨sub1_122, List.forall_mem_cons.2 ⟨sub1_123, List.forall_mem_cons.2 ⟨sub1_124, List.forall_mem_cons.2 ⟨sub1_125, List.forall_mem_cons.2 ⟨sub1_126, List.forall_mem_cons.2 ⟨sub1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_128 : sub1 [-3, 0, 1] = true := by decide +kernel
theorem sub1_129 : sub1 [-3, 0, 2] = true := by decide +kernel
theorem sub1_130 : sub1 [-3, 0, 3] = true := by decide +kernel
theorem sub1_131 : sub1 [-3, 0, 4] = true := by decide +kernel
theorem sub1_132 : sub1 [-3, 0, 5] = true := by decide +kernel
theorem sub1_133 : sub1 [-3, 0, 6] = true := by decide +kernel
theorem sub1_134 : sub1 [-3, 0, 7] = true := by decide +kernel
theorem sub1_135 : sub1 [-3, 1, -8] = true := by decide +kernel
theorem sub1_136 : sub1 [-3, 1, -7] = true := by decide +kernel
theorem sub1_137 : sub1 [-3, 1, -6] = true := by decide +kernel
theorem sub1_138 : sub1 [-3, 1, -5] = true := by decide +kernel
theorem sub1_139 : sub1 [-3, 1, -4] = true := by decide +kernel
theorem sub1_140 : sub1 [-3, 1, -3] = true := by decide +kernel
theorem sub1_141 : sub1 [-3, 1, -2] = true := by decide +kernel
theorem sub1_142 : sub1 [-3, 1, -1] = true := by decide +kernel
theorem sub1_143 : sub1 [-3, 1, 0] = true := by decide +kernel
theorem sub1_144 : sub1 [-3, 1, 1] = true := by decide +kernel
theorem sub1_145 : sub1 [-3, 1, 2] = true := by decide +kernel
theorem sub1_146 : sub1 [-3, 1, 3] = true := by decide +kernel
theorem sub1_147 : sub1 [-3, 1, 4] = true := by decide +kernel
theorem sub1_148 : sub1 [-3, 1, 5] = true := by decide +kernel
theorem sub1_149 : sub1 [-3, 1, 6] = true := by decide +kernel
theorem sub1_150 : sub1 [-3, 2, -8] = true := by decide +kernel
theorem sub1_151 : sub1 [-3, 2, -7] = true := by decide +kernel
theorem sub1_152 : sub1 [-3, 2, -6] = true := by decide +kernel
theorem sub1_153 : sub1 [-3, 2, -5] = true := by decide +kernel
theorem sub1_154 : sub1 [-3, 2, -4] = true := by decide +kernel
theorem sub1_155 : sub1 [-3, 2, -3] = true := by decide +kernel
theorem sub1_156 : sub1 [-3, 2, -2] = true := by decide +kernel
theorem sub1_157 : sub1 [-3, 2, -1] = true := by decide +kernel
theorem sub1_158 : sub1 [-3, 2, 0] = true := by decide +kernel
theorem sub1_159 : sub1 [-3, 2, 1] = true := by decide +kernel
theorem sb1_4 : ∀ q ∈ blk1_4, sub1 q = true := by
  unfold blk1_4
  exact List.forall_mem_cons.2 ⟨sub1_128, List.forall_mem_cons.2 ⟨sub1_129, List.forall_mem_cons.2 ⟨sub1_130, List.forall_mem_cons.2 ⟨sub1_131, List.forall_mem_cons.2 ⟨sub1_132, List.forall_mem_cons.2 ⟨sub1_133, List.forall_mem_cons.2 ⟨sub1_134, List.forall_mem_cons.2 ⟨sub1_135, List.forall_mem_cons.2 ⟨sub1_136, List.forall_mem_cons.2 ⟨sub1_137, List.forall_mem_cons.2 ⟨sub1_138, List.forall_mem_cons.2 ⟨sub1_139, List.forall_mem_cons.2 ⟨sub1_140, List.forall_mem_cons.2 ⟨sub1_141, List.forall_mem_cons.2 ⟨sub1_142, List.forall_mem_cons.2 ⟨sub1_143, List.forall_mem_cons.2 ⟨sub1_144, List.forall_mem_cons.2 ⟨sub1_145, List.forall_mem_cons.2 ⟨sub1_146, List.forall_mem_cons.2 ⟨sub1_147, List.forall_mem_cons.2 ⟨sub1_148, List.forall_mem_cons.2 ⟨sub1_149, List.forall_mem_cons.2 ⟨sub1_150, List.forall_mem_cons.2 ⟨sub1_151, List.forall_mem_cons.2 ⟨sub1_152, List.forall_mem_cons.2 ⟨sub1_153, List.forall_mem_cons.2 ⟨sub1_154, List.forall_mem_cons.2 ⟨sub1_155, List.forall_mem_cons.2 ⟨sub1_156, List.forall_mem_cons.2 ⟨sub1_157, List.forall_mem_cons.2 ⟨sub1_158, List.forall_mem_cons.2 ⟨sub1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_160 : sub1 [-3, 2, 2] = true := by decide +kernel
theorem sub1_161 : sub1 [-3, 2, 3] = true := by decide +kernel
theorem sub1_162 : sub1 [-3, 2, 4] = true := by decide +kernel
theorem sub1_163 : sub1 [-3, 2, 5] = true := by decide +kernel
theorem sub1_164 : sub1 [-3, 2, 6] = true := by decide +kernel
theorem sub1_165 : sub1 [-3, 3, -8] = true := by decide +kernel
theorem sub1_166 : sub1 [-3, 3, -7] = true := by decide +kernel
theorem sub1_167 : sub1 [-3, 3, -6] = true := by decide +kernel
theorem sub1_168 : sub1 [-3, 3, -5] = true := by decide +kernel
theorem sub1_169 : sub1 [-3, 3, -4] = true := by decide +kernel
theorem sub1_170 : sub1 [-3, 3, -3] = true := by decide +kernel
theorem sub1_171 : sub1 [-3, 3, -2] = true := by decide +kernel
theorem sub1_172 : sub1 [-3, 3, -1] = true := by decide +kernel
theorem sub1_173 : sub1 [-3, 3, 0] = true := by decide +kernel
theorem sub1_174 : sub1 [-3, 3, 1] = true := by decide +kernel
theorem sub1_175 : sub1 [-3, 3, 2] = true := by decide +kernel
theorem sub1_176 : sub1 [-3, 3, 3] = true := by decide +kernel
theorem sub1_177 : sub1 [-3, 3, 4] = true := by decide +kernel
theorem sub1_178 : sub1 [-3, 3, 5] = true := by decide +kernel
theorem sub1_179 : sub1 [-3, 4] = true := by decide +kernel
theorem sub1_180 : sub1 [-3, 5] = true := by decide +kernel
theorem sub1_181 : sub1 [-3, 6] = true := by decide +kernel
theorem sub1_182 : sub1 [-2, -7] = true := by decide +kernel
theorem sub1_183 : sub1 [-2, -6] = true := by decide +kernel
theorem sub1_184 : sub1 [-2, -5] = true := by decide +kernel
theorem sub1_185 : sub1 [-2, -4] = true := by decide +kernel
theorem sub1_186 : sub1 [-2, -3, -7] = true := by decide +kernel
theorem sub1_187 : sub1 [-2, -3, -6] = true := by decide +kernel
theorem sub1_188 : sub1 [-2, -3, -5] = true := by decide +kernel
theorem sub1_189 : sub1 [-2, -3, -4] = true := by decide +kernel
theorem sub1_190 : sub1 [-2, -3, -3] = true := by decide +kernel
theorem sub1_191 : sub1 [-2, -3, -2] = true := by decide +kernel
theorem sb1_5 : ∀ q ∈ blk1_5, sub1 q = true := by
  unfold blk1_5
  exact List.forall_mem_cons.2 ⟨sub1_160, List.forall_mem_cons.2 ⟨sub1_161, List.forall_mem_cons.2 ⟨sub1_162, List.forall_mem_cons.2 ⟨sub1_163, List.forall_mem_cons.2 ⟨sub1_164, List.forall_mem_cons.2 ⟨sub1_165, List.forall_mem_cons.2 ⟨sub1_166, List.forall_mem_cons.2 ⟨sub1_167, List.forall_mem_cons.2 ⟨sub1_168, List.forall_mem_cons.2 ⟨sub1_169, List.forall_mem_cons.2 ⟨sub1_170, List.forall_mem_cons.2 ⟨sub1_171, List.forall_mem_cons.2 ⟨sub1_172, List.forall_mem_cons.2 ⟨sub1_173, List.forall_mem_cons.2 ⟨sub1_174, List.forall_mem_cons.2 ⟨sub1_175, List.forall_mem_cons.2 ⟨sub1_176, List.forall_mem_cons.2 ⟨sub1_177, List.forall_mem_cons.2 ⟨sub1_178, List.forall_mem_cons.2 ⟨sub1_179, List.forall_mem_cons.2 ⟨sub1_180, List.forall_mem_cons.2 ⟨sub1_181, List.forall_mem_cons.2 ⟨sub1_182, List.forall_mem_cons.2 ⟨sub1_183, List.forall_mem_cons.2 ⟨sub1_184, List.forall_mem_cons.2 ⟨sub1_185, List.forall_mem_cons.2 ⟨sub1_186, List.forall_mem_cons.2 ⟨sub1_187, List.forall_mem_cons.2 ⟨sub1_188, List.forall_mem_cons.2 ⟨sub1_189, List.forall_mem_cons.2 ⟨sub1_190, List.forall_mem_cons.2 ⟨sub1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_192 : sub1 [-2, -3, -1] = true := by decide +kernel
theorem sub1_193 : sub1 [-2, -3, 0] = true := by decide +kernel
theorem sub1_194 : sub1 [-2, -3, 1] = true := by decide +kernel
theorem sub1_195 : sub1 [-2, -3, 2] = true := by decide +kernel
theorem sub1_196 : sub1 [-2, -3, 3] = true := by decide +kernel
theorem sub1_197 : sub1 [-2, -3, 4] = true := by decide +kernel
theorem sub1_198 : sub1 [-2, -3, 5] = true := by decide +kernel
theorem sub1_199 : sub1 [-2, -3, 6] = true := by decide +kernel
theorem sub1_200 : sub1 [-2, -2, -8] = true := by decide +kernel
theorem sub1_201 : sub1 [-2, -2, -7] = true := by decide +kernel
theorem sub1_202 : sub1 [-2, -2, -6] = true := by decide +kernel
theorem sub1_203 : sub1 [-2, -2, -5] = true := by decide +kernel
theorem sub1_204 : sub1 [-2, -2, -4] = true := by decide +kernel
theorem sub1_205 : sub1 [-2, -2, -3] = true := by decide +kernel
theorem sub1_206 : sub1 [-2, -2, -2] = true := by decide +kernel
theorem sub1_207 : sub1 [-2, -2, -1] = true := by decide +kernel
theorem sub1_208 : sub1 [-2, -2, 0] = true := by decide +kernel
theorem sub1_209 : sub1 [-2, -2, 1] = true := by decide +kernel
theorem sub1_210 : sub1 [-2, -2, 2] = true := by decide +kernel
theorem sub1_211 : sub1 [-2, -2, 3] = true := by decide +kernel
theorem sub1_212 : sub1 [-2, -2, 4] = true := by decide +kernel
theorem sub1_213 : sub1 [-2, -2, 5] = true := by decide +kernel
theorem sub1_214 : sub1 [-2, -2, 6] = true := by decide +kernel
theorem sub1_215 : sub1 [-2, -2, 7] = true := by decide +kernel
theorem sub1_216 : sub1 [-2, -1, -8] = true := by decide +kernel
theorem sub1_217 : sub1 [-2, -1, -7] = true := by decide +kernel
theorem sub1_218 : sub1 [-2, -1, -6] = true := by decide +kernel
theorem sub1_219 : sub1 [-2, -1, -5] = true := by decide +kernel
theorem sub1_220 : sub1 [-2, -1, -4] = true := by decide +kernel
theorem sub1_221 : sub1 [-2, -1, -3] = true := by decide +kernel
theorem sub1_222 : sub1 [-2, -1, -2] = true := by decide +kernel
theorem sub1_223 : sub1 [-2, -1, -1] = true := by decide +kernel
theorem sb1_6 : ∀ q ∈ blk1_6, sub1 q = true := by
  unfold blk1_6
  exact List.forall_mem_cons.2 ⟨sub1_192, List.forall_mem_cons.2 ⟨sub1_193, List.forall_mem_cons.2 ⟨sub1_194, List.forall_mem_cons.2 ⟨sub1_195, List.forall_mem_cons.2 ⟨sub1_196, List.forall_mem_cons.2 ⟨sub1_197, List.forall_mem_cons.2 ⟨sub1_198, List.forall_mem_cons.2 ⟨sub1_199, List.forall_mem_cons.2 ⟨sub1_200, List.forall_mem_cons.2 ⟨sub1_201, List.forall_mem_cons.2 ⟨sub1_202, List.forall_mem_cons.2 ⟨sub1_203, List.forall_mem_cons.2 ⟨sub1_204, List.forall_mem_cons.2 ⟨sub1_205, List.forall_mem_cons.2 ⟨sub1_206, List.forall_mem_cons.2 ⟨sub1_207, List.forall_mem_cons.2 ⟨sub1_208, List.forall_mem_cons.2 ⟨sub1_209, List.forall_mem_cons.2 ⟨sub1_210, List.forall_mem_cons.2 ⟨sub1_211, List.forall_mem_cons.2 ⟨sub1_212, List.forall_mem_cons.2 ⟨sub1_213, List.forall_mem_cons.2 ⟨sub1_214, List.forall_mem_cons.2 ⟨sub1_215, List.forall_mem_cons.2 ⟨sub1_216, List.forall_mem_cons.2 ⟨sub1_217, List.forall_mem_cons.2 ⟨sub1_218, List.forall_mem_cons.2 ⟨sub1_219, List.forall_mem_cons.2 ⟨sub1_220, List.forall_mem_cons.2 ⟨sub1_221, List.forall_mem_cons.2 ⟨sub1_222, List.forall_mem_cons.2 ⟨sub1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_224 : sub1 [-2, -1, 0] = true := by decide +kernel
theorem sub1_225 : sub1 [-2, -1, 1] = true := by decide +kernel
theorem sub1_226 : sub1 [-2, -1, 2] = true := by decide +kernel
theorem sub1_227 : sub1 [-2, -1, 3] = true := by decide +kernel
theorem sub1_228 : sub1 [-2, -1, 4] = true := by decide +kernel
theorem sub1_229 : sub1 [-2, -1, 5] = true := by decide +kernel
theorem sub1_230 : sub1 [-2, -1, 6] = true := by decide +kernel
theorem sub1_231 : sub1 [-2, -1, 7] = true := by decide +kernel
theorem sub1_232 : sub1 [-2, 0, -8] = true := by decide +kernel
theorem sub1_233 : sub1 [-2, 0, -7] = true := by decide +kernel
theorem sub1_234 : sub1 [-2, 0, -6] = true := by decide +kernel
theorem sub1_235 : sub1 [-2, 0, -5] = true := by decide +kernel
theorem sub1_236 : sub1 [-2, 0, -4] = true := by decide +kernel
theorem sub1_237 : sub1 [-2, 0, -3] = true := by decide +kernel
theorem sub1_238 : sub1 [-2, 0, -2] = true := by decide +kernel
theorem sub1_239 : sub1 [-2, 0, -1] = true := by decide +kernel
theorem sub1_240 : sub1 [-2, 0, 0] = true := by decide +kernel
theorem sub1_241 : sub1 [-2, 0, 1] = true := by decide +kernel
theorem sub1_242 : sub1 [-2, 0, 2] = true := by decide +kernel
theorem sub1_243 : sub1 [-2, 0, 3] = true := by decide +kernel
theorem sub1_244 : sub1 [-2, 0, 4] = true := by decide +kernel
theorem sub1_245 : sub1 [-2, 0, 5] = true := by decide +kernel
theorem sub1_246 : sub1 [-2, 0, 6] = true := by decide +kernel
theorem sub1_247 : sub1 [-2, 0, 7] = true := by decide +kernel
theorem sub1_248 : sub1 [-2, 1, -8] = true := by decide +kernel
theorem sub1_249 : sub1 [-2, 1, -7] = true := by decide +kernel
theorem sub1_250 : sub1 [-2, 1, -6] = true := by decide +kernel
theorem sub1_251 : sub1 [-2, 1, -5] = true := by decide +kernel
theorem sub1_252 : sub1 [-2, 1, -4] = true := by decide +kernel
theorem sub1_253 : sub1 [-2, 1, -3] = true := by decide +kernel
theorem sub1_254 : sub1 [-2, 1, -2] = true := by decide +kernel
theorem sub1_255 : sub1 [-2, 1, -1] = true := by decide +kernel
theorem sb1_7 : ∀ q ∈ blk1_7, sub1 q = true := by
  unfold blk1_7
  exact List.forall_mem_cons.2 ⟨sub1_224, List.forall_mem_cons.2 ⟨sub1_225, List.forall_mem_cons.2 ⟨sub1_226, List.forall_mem_cons.2 ⟨sub1_227, List.forall_mem_cons.2 ⟨sub1_228, List.forall_mem_cons.2 ⟨sub1_229, List.forall_mem_cons.2 ⟨sub1_230, List.forall_mem_cons.2 ⟨sub1_231, List.forall_mem_cons.2 ⟨sub1_232, List.forall_mem_cons.2 ⟨sub1_233, List.forall_mem_cons.2 ⟨sub1_234, List.forall_mem_cons.2 ⟨sub1_235, List.forall_mem_cons.2 ⟨sub1_236, List.forall_mem_cons.2 ⟨sub1_237, List.forall_mem_cons.2 ⟨sub1_238, List.forall_mem_cons.2 ⟨sub1_239, List.forall_mem_cons.2 ⟨sub1_240, List.forall_mem_cons.2 ⟨sub1_241, List.forall_mem_cons.2 ⟨sub1_242, List.forall_mem_cons.2 ⟨sub1_243, List.forall_mem_cons.2 ⟨sub1_244, List.forall_mem_cons.2 ⟨sub1_245, List.forall_mem_cons.2 ⟨sub1_246, List.forall_mem_cons.2 ⟨sub1_247, List.forall_mem_cons.2 ⟨sub1_248, List.forall_mem_cons.2 ⟨sub1_249, List.forall_mem_cons.2 ⟨sub1_250, List.forall_mem_cons.2 ⟨sub1_251, List.forall_mem_cons.2 ⟨sub1_252, List.forall_mem_cons.2 ⟨sub1_253, List.forall_mem_cons.2 ⟨sub1_254, List.forall_mem_cons.2 ⟨sub1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_256 : sub1 [-2, 1, 0] = true := by decide +kernel
theorem sub1_257 : sub1 [-2, 1, 1] = true := by decide +kernel
theorem sub1_258 : sub1 [-2, 1, 2] = true := by decide +kernel
theorem sub1_259 : sub1 [-2, 1, 3] = true := by decide +kernel
theorem sub1_260 : sub1 [-2, 1, 4] = true := by decide +kernel
theorem sub1_261 : sub1 [-2, 1, 5] = true := by decide +kernel
theorem sub1_262 : sub1 [-2, 1, 6] = true := by decide +kernel
theorem sub1_263 : sub1 [-2, 1, 7] = true := by decide +kernel
theorem sub1_264 : sub1 [-2, 2, -8] = true := by decide +kernel
theorem sub1_265 : sub1 [-2, 2, -7] = true := by decide +kernel
theorem sub1_266 : sub1 [-2, 2, -6] = true := by decide +kernel
theorem sub1_267 : sub1 [-2, 2, -5] = true := by decide +kernel
theorem sub1_268 : sub1 [-2, 2, -4] = true := by decide +kernel
theorem sub1_269 : sub1 [-2, 2, -3] = true := by decide +kernel
theorem sub1_270 : sub1 [-2, 2, -2] = true := by decide +kernel
theorem sub1_271 : sub1 [-2, 2, -1] = true := by decide +kernel
theorem sub1_272 : sub1 [-2, 2, 0] = true := by decide +kernel
theorem sub1_273 : sub1 [-2, 2, 1] = true := by decide +kernel
theorem sub1_274 : sub1 [-2, 2, 2] = true := by decide +kernel
theorem sub1_275 : sub1 [-2, 2, 3] = true := by decide +kernel
theorem sub1_276 : sub1 [-2, 2, 4] = true := by decide +kernel
theorem sub1_277 : sub1 [-2, 2, 5] = true := by decide +kernel
theorem sub1_278 : sub1 [-2, 2, 6] = true := by decide +kernel
theorem sub1_279 : sub1 [-2, 3, -8] = true := by decide +kernel
theorem sub1_280 : sub1 [-2, 3, -7] = true := by decide +kernel
theorem sub1_281 : sub1 [-2, 3, -6] = true := by decide +kernel
theorem sub1_282 : sub1 [-2, 3, -5] = true := by decide +kernel
theorem sub1_283 : sub1 [-2, 3, -4] = true := by decide +kernel
theorem sub1_284 : sub1 [-2, 3, -3] = true := by decide +kernel
theorem sub1_285 : sub1 [-2, 3, -2] = true := by decide +kernel
theorem sub1_286 : sub1 [-2, 3, -1] = true := by decide +kernel
theorem sub1_287 : sub1 [-2, 3, 0] = true := by decide +kernel
theorem sb1_8 : ∀ q ∈ blk1_8, sub1 q = true := by
  unfold blk1_8
  exact List.forall_mem_cons.2 ⟨sub1_256, List.forall_mem_cons.2 ⟨sub1_257, List.forall_mem_cons.2 ⟨sub1_258, List.forall_mem_cons.2 ⟨sub1_259, List.forall_mem_cons.2 ⟨sub1_260, List.forall_mem_cons.2 ⟨sub1_261, List.forall_mem_cons.2 ⟨sub1_262, List.forall_mem_cons.2 ⟨sub1_263, List.forall_mem_cons.2 ⟨sub1_264, List.forall_mem_cons.2 ⟨sub1_265, List.forall_mem_cons.2 ⟨sub1_266, List.forall_mem_cons.2 ⟨sub1_267, List.forall_mem_cons.2 ⟨sub1_268, List.forall_mem_cons.2 ⟨sub1_269, List.forall_mem_cons.2 ⟨sub1_270, List.forall_mem_cons.2 ⟨sub1_271, List.forall_mem_cons.2 ⟨sub1_272, List.forall_mem_cons.2 ⟨sub1_273, List.forall_mem_cons.2 ⟨sub1_274, List.forall_mem_cons.2 ⟨sub1_275, List.forall_mem_cons.2 ⟨sub1_276, List.forall_mem_cons.2 ⟨sub1_277, List.forall_mem_cons.2 ⟨sub1_278, List.forall_mem_cons.2 ⟨sub1_279, List.forall_mem_cons.2 ⟨sub1_280, List.forall_mem_cons.2 ⟨sub1_281, List.forall_mem_cons.2 ⟨sub1_282, List.forall_mem_cons.2 ⟨sub1_283, List.forall_mem_cons.2 ⟨sub1_284, List.forall_mem_cons.2 ⟨sub1_285, List.forall_mem_cons.2 ⟨sub1_286, List.forall_mem_cons.2 ⟨sub1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_288 : sub1 [-2, 3, 1] = true := by decide +kernel
theorem sub1_289 : sub1 [-2, 3, 2] = true := by decide +kernel
theorem sub1_290 : sub1 [-2, 3, 3] = true := by decide +kernel
theorem sub1_291 : sub1 [-2, 3, 4] = true := by decide +kernel
theorem sub1_292 : sub1 [-2, 3, 5] = true := by decide +kernel
theorem sub1_293 : sub1 [-2, 3, 6] = true := by decide +kernel
theorem sub1_294 : sub1 [-2, 4, -7] = true := by decide +kernel
theorem sub1_295 : sub1 [-2, 4, -6] = true := by decide +kernel
theorem sub1_296 : sub1 [-2, 4, -5] = true := by decide +kernel
theorem sub1_297 : sub1 [-2, 4, -4] = true := by decide +kernel
theorem sub1_298 : sub1 [-2, 4, -3] = true := by decide +kernel
theorem sub1_299 : sub1 [-2, 4, -2] = true := by decide +kernel
theorem sub1_300 : sub1 [-2, 4, -1] = true := by decide +kernel
theorem sub1_301 : sub1 [-2, 4, 0] = true := by decide +kernel
theorem sub1_302 : sub1 [-2, 4, 1] = true := by decide +kernel
theorem sub1_303 : sub1 [-2, 4, 2] = true := by decide +kernel
theorem sub1_304 : sub1 [-2, 4, 3] = true := by decide +kernel
theorem sub1_305 : sub1 [-2, 4, 4] = true := by decide +kernel
theorem sub1_306 : sub1 [-2, 4, 5] = true := by decide +kernel
theorem sub1_307 : sub1 [-2, 5] = true := by decide +kernel
theorem sub1_308 : sub1 [-2, 6] = true := by decide +kernel
theorem sub1_309 : sub1 [-1, -7] = true := by decide +kernel
theorem sub1_310 : sub1 [-1, -6] = true := by decide +kernel
theorem sub1_311 : sub1 [-1, -5] = true := by decide +kernel
theorem sub1_312 : sub1 [-1, -4] = true := by decide +kernel
theorem sub1_313 : sub1 [-1, -3, -7] = true := by decide +kernel
theorem sub1_314 : sub1 [-1, -3, -6] = true := by decide +kernel
theorem sub1_315 : sub1 [-1, -3, -5] = true := by decide +kernel
theorem sub1_316 : sub1 [-1, -3, -4] = true := by decide +kernel
theorem sub1_317 : sub1 [-1, -3, -3] = true := by decide +kernel
theorem sub1_318 : sub1 [-1, -3, -2] = true := by decide +kernel
theorem sub1_319 : sub1 [-1, -3, -1] = true := by decide +kernel
theorem sb1_9 : ∀ q ∈ blk1_9, sub1 q = true := by
  unfold blk1_9
  exact List.forall_mem_cons.2 ⟨sub1_288, List.forall_mem_cons.2 ⟨sub1_289, List.forall_mem_cons.2 ⟨sub1_290, List.forall_mem_cons.2 ⟨sub1_291, List.forall_mem_cons.2 ⟨sub1_292, List.forall_mem_cons.2 ⟨sub1_293, List.forall_mem_cons.2 ⟨sub1_294, List.forall_mem_cons.2 ⟨sub1_295, List.forall_mem_cons.2 ⟨sub1_296, List.forall_mem_cons.2 ⟨sub1_297, List.forall_mem_cons.2 ⟨sub1_298, List.forall_mem_cons.2 ⟨sub1_299, List.forall_mem_cons.2 ⟨sub1_300, List.forall_mem_cons.2 ⟨sub1_301, List.forall_mem_cons.2 ⟨sub1_302, List.forall_mem_cons.2 ⟨sub1_303, List.forall_mem_cons.2 ⟨sub1_304, List.forall_mem_cons.2 ⟨sub1_305, List.forall_mem_cons.2 ⟨sub1_306, List.forall_mem_cons.2 ⟨sub1_307, List.forall_mem_cons.2 ⟨sub1_308, List.forall_mem_cons.2 ⟨sub1_309, List.forall_mem_cons.2 ⟨sub1_310, List.forall_mem_cons.2 ⟨sub1_311, List.forall_mem_cons.2 ⟨sub1_312, List.forall_mem_cons.2 ⟨sub1_313, List.forall_mem_cons.2 ⟨sub1_314, List.forall_mem_cons.2 ⟨sub1_315, List.forall_mem_cons.2 ⟨sub1_316, List.forall_mem_cons.2 ⟨sub1_317, List.forall_mem_cons.2 ⟨sub1_318, List.forall_mem_cons.2 ⟨sub1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_320 : sub1 [-1, -3, 0] = true := by decide +kernel
theorem sub1_321 : sub1 [-1, -3, 1] = true := by decide +kernel
theorem sub1_322 : sub1 [-1, -3, 2] = true := by decide +kernel
theorem sub1_323 : sub1 [-1, -3, 3] = true := by decide +kernel
theorem sub1_324 : sub1 [-1, -3, 4] = true := by decide +kernel
theorem sub1_325 : sub1 [-1, -3, 5] = true := by decide +kernel
theorem sub1_326 : sub1 [-1, -3, 6] = true := by decide +kernel
theorem sub1_327 : sub1 [-1, -3, 7] = true := by decide +kernel
theorem sub1_328 : sub1 [-1, -2, -8] = true := by decide +kernel
theorem sub1_329 : sub1 [-1, -2, -7] = true := by decide +kernel
theorem sub1_330 : sub1 [-1, -2, -6] = true := by decide +kernel
theorem sub1_331 : sub1 [-1, -2, -5] = true := by decide +kernel
theorem sub1_332 : sub1 [-1, -2, -4] = true := by decide +kernel
theorem sub1_333 : sub1 [-1, -2, -3] = true := by decide +kernel
theorem sub1_334 : sub1 [-1, -2, -2] = true := by decide +kernel
theorem sub1_335 : sub1 [-1, -2, -1] = true := by decide +kernel
theorem sub1_336 : sub1 [-1, -2, 0] = true := by decide +kernel
theorem sub1_337 : sub1 [-1, -2, 1] = true := by decide +kernel
theorem sub1_338 : sub1 [-1, -2, 2] = true := by decide +kernel
theorem sub1_339 : sub1 [-1, -2, 3] = true := by decide +kernel
theorem sub1_340 : sub1 [-1, -2, 4] = true := by decide +kernel
theorem sub1_341 : sub1 [-1, -2, 5] = true := by decide +kernel
theorem sub1_342 : sub1 [-1, -2, 6] = true := by decide +kernel
theorem sub1_343 : sub1 [-1, -2, 7] = true := by decide +kernel
theorem sub1_344 : sub1 [-1, -1, -8] = true := by decide +kernel
theorem sub1_345 : sub1 [-1, -1, -7] = true := by decide +kernel
theorem sub1_346 : sub1 [-1, -1, -6] = true := by decide +kernel
theorem sub1_347 : sub1 [-1, -1, -5] = true := by decide +kernel
theorem sub1_348 : sub1 [-1, -1, -4] = true := by decide +kernel
theorem sub1_349 : sub1 [-1, -1, -3] = true := by decide +kernel
theorem sub1_350 : sub1 [-1, -1, -2] = true := by decide +kernel
theorem sub1_351 : sub1 [-1, -1, -1] = true := by decide +kernel
theorem sb1_10 : ∀ q ∈ blk1_10, sub1 q = true := by
  unfold blk1_10
  exact List.forall_mem_cons.2 ⟨sub1_320, List.forall_mem_cons.2 ⟨sub1_321, List.forall_mem_cons.2 ⟨sub1_322, List.forall_mem_cons.2 ⟨sub1_323, List.forall_mem_cons.2 ⟨sub1_324, List.forall_mem_cons.2 ⟨sub1_325, List.forall_mem_cons.2 ⟨sub1_326, List.forall_mem_cons.2 ⟨sub1_327, List.forall_mem_cons.2 ⟨sub1_328, List.forall_mem_cons.2 ⟨sub1_329, List.forall_mem_cons.2 ⟨sub1_330, List.forall_mem_cons.2 ⟨sub1_331, List.forall_mem_cons.2 ⟨sub1_332, List.forall_mem_cons.2 ⟨sub1_333, List.forall_mem_cons.2 ⟨sub1_334, List.forall_mem_cons.2 ⟨sub1_335, List.forall_mem_cons.2 ⟨sub1_336, List.forall_mem_cons.2 ⟨sub1_337, List.forall_mem_cons.2 ⟨sub1_338, List.forall_mem_cons.2 ⟨sub1_339, List.forall_mem_cons.2 ⟨sub1_340, List.forall_mem_cons.2 ⟨sub1_341, List.forall_mem_cons.2 ⟨sub1_342, List.forall_mem_cons.2 ⟨sub1_343, List.forall_mem_cons.2 ⟨sub1_344, List.forall_mem_cons.2 ⟨sub1_345, List.forall_mem_cons.2 ⟨sub1_346, List.forall_mem_cons.2 ⟨sub1_347, List.forall_mem_cons.2 ⟨sub1_348, List.forall_mem_cons.2 ⟨sub1_349, List.forall_mem_cons.2 ⟨sub1_350, List.forall_mem_cons.2 ⟨sub1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_352 : sub1 [-1, -1, 0] = true := by decide +kernel
theorem sub1_353 : sub1 [-1, -1, 1] = true := by decide +kernel
theorem sub1_354 : sub1 [-1, -1, 2] = true := by decide +kernel
theorem sub1_355 : sub1 [-1, -1, 3] = true := by decide +kernel
theorem sub1_356 : sub1 [-1, -1, 4] = true := by decide +kernel
theorem sub1_357 : sub1 [-1, -1, 5] = true := by decide +kernel
theorem sub1_358 : sub1 [-1, -1, 6] = true := by decide +kernel
theorem sub1_359 : sub1 [-1, -1, 7] = true := by decide +kernel
theorem sub1_360 : sub1 [-1, 0, -8] = true := by decide +kernel
theorem sub1_361 : sub1 [-1, 0, -7] = true := by decide +kernel
theorem sub1_362 : sub1 [-1, 0, -6] = true := by decide +kernel
theorem sub1_363 : sub1 [-1, 0, -5] = true := by decide +kernel
theorem sub1_364 : sub1 [-1, 0, -4] = true := by decide +kernel
theorem sub1_365 : sub1 [-1, 0, -3] = true := by decide +kernel
theorem sub1_366 : sub1 [-1, 0, -2] = true := by decide +kernel
theorem sub1_367 : sub1 [-1, 0, -1] = true := by decide +kernel
theorem sub1_368 : sub1 [-1, 0, 0] = true := by decide +kernel
theorem sub1_369 : sub1 [-1, 0, 1] = true := by decide +kernel
theorem sub1_370 : sub1 [-1, 0, 2] = true := by decide +kernel
theorem sub1_371 : sub1 [-1, 0, 3] = true := by decide +kernel
theorem sub1_372 : sub1 [-1, 0, 4] = true := by decide +kernel
theorem sub1_373 : sub1 [-1, 0, 5] = true := by decide +kernel
theorem sub1_374 : sub1 [-1, 0, 6] = true := by decide +kernel
theorem sub1_375 : sub1 [-1, 0, 7] = true := by decide +kernel
theorem sub1_376 : sub1 [-1, 1, -8] = true := by decide +kernel
theorem sub1_377 : sub1 [-1, 1, -7] = true := by decide +kernel
theorem sub1_378 : sub1 [-1, 1, -6] = true := by decide +kernel
theorem sub1_379 : sub1 [-1, 1, -5] = true := by decide +kernel
theorem sub1_380 : sub1 [-1, 1, -4] = true := by decide +kernel
theorem sub1_381 : sub1 [-1, 1, -3] = true := by decide +kernel
theorem sub1_382 : sub1 [-1, 1, -2] = true := by decide +kernel
theorem sub1_383 : sub1 [-1, 1, -1] = true := by decide +kernel
theorem sb1_11 : ∀ q ∈ blk1_11, sub1 q = true := by
  unfold blk1_11
  exact List.forall_mem_cons.2 ⟨sub1_352, List.forall_mem_cons.2 ⟨sub1_353, List.forall_mem_cons.2 ⟨sub1_354, List.forall_mem_cons.2 ⟨sub1_355, List.forall_mem_cons.2 ⟨sub1_356, List.forall_mem_cons.2 ⟨sub1_357, List.forall_mem_cons.2 ⟨sub1_358, List.forall_mem_cons.2 ⟨sub1_359, List.forall_mem_cons.2 ⟨sub1_360, List.forall_mem_cons.2 ⟨sub1_361, List.forall_mem_cons.2 ⟨sub1_362, List.forall_mem_cons.2 ⟨sub1_363, List.forall_mem_cons.2 ⟨sub1_364, List.forall_mem_cons.2 ⟨sub1_365, List.forall_mem_cons.2 ⟨sub1_366, List.forall_mem_cons.2 ⟨sub1_367, List.forall_mem_cons.2 ⟨sub1_368, List.forall_mem_cons.2 ⟨sub1_369, List.forall_mem_cons.2 ⟨sub1_370, List.forall_mem_cons.2 ⟨sub1_371, List.forall_mem_cons.2 ⟨sub1_372, List.forall_mem_cons.2 ⟨sub1_373, List.forall_mem_cons.2 ⟨sub1_374, List.forall_mem_cons.2 ⟨sub1_375, List.forall_mem_cons.2 ⟨sub1_376, List.forall_mem_cons.2 ⟨sub1_377, List.forall_mem_cons.2 ⟨sub1_378, List.forall_mem_cons.2 ⟨sub1_379, List.forall_mem_cons.2 ⟨sub1_380, List.forall_mem_cons.2 ⟨sub1_381, List.forall_mem_cons.2 ⟨sub1_382, List.forall_mem_cons.2 ⟨sub1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_384 : sub1 [-1, 1, 0] = true := by decide +kernel
theorem sub1_385 : sub1 [-1, 1, 1] = true := by decide +kernel
theorem sub1_386 : sub1 [-1, 1, 2] = true := by decide +kernel
theorem sub1_387 : sub1 [-1, 1, 3] = true := by decide +kernel
theorem sub1_388 : sub1 [-1, 1, 4] = true := by decide +kernel
theorem sub1_389 : sub1 [-1, 1, 5] = true := by decide +kernel
theorem sub1_390 : sub1 [-1, 1, 6] = true := by decide +kernel
theorem sub1_391 : sub1 [-1, 1, 7] = true := by decide +kernel
theorem sub1_392 : sub1 [-1, 2, -8] = true := by decide +kernel
theorem sub1_393 : sub1 [-1, 2, -7] = true := by decide +kernel
theorem sub1_394 : sub1 [-1, 2, -6] = true := by decide +kernel
theorem sub1_395 : sub1 [-1, 2, -5] = true := by decide +kernel
theorem sub1_396 : sub1 [-1, 2, -4] = true := by decide +kernel
theorem sub1_397 : sub1 [-1, 2, -3] = true := by decide +kernel
theorem sub1_398 : sub1 [-1, 2, -2] = true := by decide +kernel
theorem sub1_399 : sub1 [-1, 2, -1] = true := by decide +kernel
theorem sub1_400 : sub1 [-1, 2, 0] = true := by decide +kernel
theorem sub1_401 : sub1 [-1, 2, 1] = true := by decide +kernel
theorem sub1_402 : sub1 [-1, 2, 2] = true := by decide +kernel
theorem sub1_403 : sub1 [-1, 2, 3] = true := by decide +kernel
theorem sub1_404 : sub1 [-1, 2, 4] = true := by decide +kernel
theorem sub1_405 : sub1 [-1, 2, 5] = true := by decide +kernel
theorem sub1_406 : sub1 [-1, 2, 6] = true := by decide +kernel
theorem sub1_407 : sub1 [-1, 2, 7] = true := by decide +kernel
theorem sub1_408 : sub1 [-1, 3, -8] = true := by decide +kernel
theorem sub1_409 : sub1 [-1, 3, -7] = true := by decide +kernel
theorem sub1_410 : sub1 [-1, 3, -6] = true := by decide +kernel
theorem sub1_411 : sub1 [-1, 3, -5] = true := by decide +kernel
theorem sub1_412 : sub1 [-1, 3, -4] = true := by decide +kernel
theorem sub1_413 : sub1 [-1, 3, -3] = true := by decide +kernel
theorem sub1_414 : sub1 [-1, 3, -2] = true := by decide +kernel
theorem sub1_415 : sub1 [-1, 3, -1] = true := by decide +kernel
theorem sb1_12 : ∀ q ∈ blk1_12, sub1 q = true := by
  unfold blk1_12
  exact List.forall_mem_cons.2 ⟨sub1_384, List.forall_mem_cons.2 ⟨sub1_385, List.forall_mem_cons.2 ⟨sub1_386, List.forall_mem_cons.2 ⟨sub1_387, List.forall_mem_cons.2 ⟨sub1_388, List.forall_mem_cons.2 ⟨sub1_389, List.forall_mem_cons.2 ⟨sub1_390, List.forall_mem_cons.2 ⟨sub1_391, List.forall_mem_cons.2 ⟨sub1_392, List.forall_mem_cons.2 ⟨sub1_393, List.forall_mem_cons.2 ⟨sub1_394, List.forall_mem_cons.2 ⟨sub1_395, List.forall_mem_cons.2 ⟨sub1_396, List.forall_mem_cons.2 ⟨sub1_397, List.forall_mem_cons.2 ⟨sub1_398, List.forall_mem_cons.2 ⟨sub1_399, List.forall_mem_cons.2 ⟨sub1_400, List.forall_mem_cons.2 ⟨sub1_401, List.forall_mem_cons.2 ⟨sub1_402, List.forall_mem_cons.2 ⟨sub1_403, List.forall_mem_cons.2 ⟨sub1_404, List.forall_mem_cons.2 ⟨sub1_405, List.forall_mem_cons.2 ⟨sub1_406, List.forall_mem_cons.2 ⟨sub1_407, List.forall_mem_cons.2 ⟨sub1_408, List.forall_mem_cons.2 ⟨sub1_409, List.forall_mem_cons.2 ⟨sub1_410, List.forall_mem_cons.2 ⟨sub1_411, List.forall_mem_cons.2 ⟨sub1_412, List.forall_mem_cons.2 ⟨sub1_413, List.forall_mem_cons.2 ⟨sub1_414, List.forall_mem_cons.2 ⟨sub1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_416 : sub1 [-1, 3, 0] = true := by decide +kernel
theorem sub1_417 : sub1 [-1, 3, 1] = true := by decide +kernel
theorem sub1_418 : sub1 [-1, 3, 2] = true := by decide +kernel
theorem sub1_419 : sub1 [-1, 3, 3] = true := by decide +kernel
theorem sub1_420 : sub1 [-1, 3, 4] = true := by decide +kernel
theorem sub1_421 : sub1 [-1, 3, 5] = true := by decide +kernel
theorem sub1_422 : sub1 [-1, 3, 6] = true := by decide +kernel
theorem sub1_423 : sub1 [-1, 4, -8] = true := by decide +kernel
theorem sub1_424 : sub1 [-1, 4, -7] = true := by decide +kernel
theorem sub1_425 : sub1 [-1, 4, -6] = true := by decide +kernel
theorem sub1_426 : sub1 [-1, 4, -5] = true := by decide +kernel
theorem sub1_427 : sub1 [-1, 4, -4] = true := by decide +kernel
theorem sub1_428 : sub1 [-1, 4, -3] = true := by decide +kernel
theorem sub1_429 : sub1 [-1, 4, -2] = true := by decide +kernel
theorem sub1_430 : sub1 [-1, 4, -1] = true := by decide +kernel
theorem sub1_431 : sub1 [-1, 4, 0] = true := by decide +kernel
theorem sub1_432 : sub1 [-1, 4, 1] = true := by decide +kernel
theorem sub1_433 : sub1 [-1, 4, 2] = true := by decide +kernel
theorem sub1_434 : sub1 [-1, 4, 3] = true := by decide +kernel
theorem sub1_435 : sub1 [-1, 4, 4] = true := by decide +kernel
theorem sub1_436 : sub1 [-1, 4, 5] = true := by decide +kernel
theorem sub1_437 : sub1 [-1, 5] = true := by decide +kernel
theorem sub1_438 : sub1 [-1, 6] = true := by decide +kernel
theorem sub1_439 : sub1 [0, -7] = true := by decide +kernel
theorem sub1_440 : sub1 [0, -6] = true := by decide +kernel
theorem sub1_441 : sub1 [0, -5] = true := by decide +kernel
theorem sub1_442 : sub1 [0, -4, -6] = true := by decide +kernel
theorem sub1_443 : sub1 [0, -4, -5] = true := by decide +kernel
theorem sub1_444 : sub1 [0, -4, -4] = true := by decide +kernel
theorem sub1_445 : sub1 [0, -4, -3] = true := by decide +kernel
theorem sub1_446 : sub1 [0, -4, -2] = true := by decide +kernel
theorem sub1_447 : sub1 [0, -4, -1] = true := by decide +kernel
theorem sb1_13 : ∀ q ∈ blk1_13, sub1 q = true := by
  unfold blk1_13
  exact List.forall_mem_cons.2 ⟨sub1_416, List.forall_mem_cons.2 ⟨sub1_417, List.forall_mem_cons.2 ⟨sub1_418, List.forall_mem_cons.2 ⟨sub1_419, List.forall_mem_cons.2 ⟨sub1_420, List.forall_mem_cons.2 ⟨sub1_421, List.forall_mem_cons.2 ⟨sub1_422, List.forall_mem_cons.2 ⟨sub1_423, List.forall_mem_cons.2 ⟨sub1_424, List.forall_mem_cons.2 ⟨sub1_425, List.forall_mem_cons.2 ⟨sub1_426, List.forall_mem_cons.2 ⟨sub1_427, List.forall_mem_cons.2 ⟨sub1_428, List.forall_mem_cons.2 ⟨sub1_429, List.forall_mem_cons.2 ⟨sub1_430, List.forall_mem_cons.2 ⟨sub1_431, List.forall_mem_cons.2 ⟨sub1_432, List.forall_mem_cons.2 ⟨sub1_433, List.forall_mem_cons.2 ⟨sub1_434, List.forall_mem_cons.2 ⟨sub1_435, List.forall_mem_cons.2 ⟨sub1_436, List.forall_mem_cons.2 ⟨sub1_437, List.forall_mem_cons.2 ⟨sub1_438, List.forall_mem_cons.2 ⟨sub1_439, List.forall_mem_cons.2 ⟨sub1_440, List.forall_mem_cons.2 ⟨sub1_441, List.forall_mem_cons.2 ⟨sub1_442, List.forall_mem_cons.2 ⟨sub1_443, List.forall_mem_cons.2 ⟨sub1_444, List.forall_mem_cons.2 ⟨sub1_445, List.forall_mem_cons.2 ⟨sub1_446, List.forall_mem_cons.2 ⟨sub1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_448 : sub1 [0, -4, 0] = true := by decide +kernel
theorem sub1_449 : sub1 [0, -4, 1] = true := by decide +kernel
theorem sub1_450 : sub1 [0, -4, 2] = true := by decide +kernel
theorem sub1_451 : sub1 [0, -4, 3] = true := by decide +kernel
theorem sub1_452 : sub1 [0, -4, 4] = true := by decide +kernel
theorem sub1_453 : sub1 [0, -4, 5] = true := by decide +kernel
theorem sub1_454 : sub1 [0, -4, 6] = true := by decide +kernel
theorem sub1_455 : sub1 [0, -3, -7] = true := by decide +kernel
theorem sub1_456 : sub1 [0, -3, -6] = true := by decide +kernel
theorem sub1_457 : sub1 [0, -3, -5] = true := by decide +kernel
theorem sub1_458 : sub1 [0, -3, -4] = true := by decide +kernel
theorem sub1_459 : sub1 [0, -3, -3] = true := by decide +kernel
theorem sub1_460 : sub1 [0, -3, -2] = true := by decide +kernel
theorem sub1_461 : sub1 [0, -3, -1] = true := by decide +kernel
theorem sub1_462 : sub1 [0, -3, 0] = true := by decide +kernel
theorem sub1_463 : sub1 [0, -3, 1] = true := by decide +kernel
theorem sub1_464 : sub1 [0, -3, 2] = true := by decide +kernel
theorem sub1_465 : sub1 [0, -3, 3] = true := by decide +kernel
theorem sub1_466 : sub1 [0, -3, 4] = true := by decide +kernel
theorem sub1_467 : sub1 [0, -3, 5] = true := by decide +kernel
theorem sub1_468 : sub1 [0, -3, 6] = true := by decide +kernel
theorem sub1_469 : sub1 [0, -3, 7] = true := by decide +kernel
theorem sub1_470 : sub1 [0, -2, -8] = true := by decide +kernel
theorem sub1_471 : sub1 [0, -2, -7] = true := by decide +kernel
theorem sub1_472 : sub1 [0, -2, -6] = true := by decide +kernel
theorem sub1_473 : sub1 [0, -2, -5] = true := by decide +kernel
theorem sub1_474 : sub1 [0, -2, -4] = true := by decide +kernel
theorem sub1_475 : sub1 [0, -2, -3] = true := by decide +kernel
theorem sub1_476 : sub1 [0, -2, -2] = true := by decide +kernel
theorem sub1_477 : sub1 [0, -2, -1] = true := by decide +kernel
theorem sub1_478 : sub1 [0, -2, 0] = true := by decide +kernel
theorem sub1_479 : sub1 [0, -2, 1] = true := by decide +kernel
theorem sb1_14 : ∀ q ∈ blk1_14, sub1 q = true := by
  unfold blk1_14
  exact List.forall_mem_cons.2 ⟨sub1_448, List.forall_mem_cons.2 ⟨sub1_449, List.forall_mem_cons.2 ⟨sub1_450, List.forall_mem_cons.2 ⟨sub1_451, List.forall_mem_cons.2 ⟨sub1_452, List.forall_mem_cons.2 ⟨sub1_453, List.forall_mem_cons.2 ⟨sub1_454, List.forall_mem_cons.2 ⟨sub1_455, List.forall_mem_cons.2 ⟨sub1_456, List.forall_mem_cons.2 ⟨sub1_457, List.forall_mem_cons.2 ⟨sub1_458, List.forall_mem_cons.2 ⟨sub1_459, List.forall_mem_cons.2 ⟨sub1_460, List.forall_mem_cons.2 ⟨sub1_461, List.forall_mem_cons.2 ⟨sub1_462, List.forall_mem_cons.2 ⟨sub1_463, List.forall_mem_cons.2 ⟨sub1_464, List.forall_mem_cons.2 ⟨sub1_465, List.forall_mem_cons.2 ⟨sub1_466, List.forall_mem_cons.2 ⟨sub1_467, List.forall_mem_cons.2 ⟨sub1_468, List.forall_mem_cons.2 ⟨sub1_469, List.forall_mem_cons.2 ⟨sub1_470, List.forall_mem_cons.2 ⟨sub1_471, List.forall_mem_cons.2 ⟨sub1_472, List.forall_mem_cons.2 ⟨sub1_473, List.forall_mem_cons.2 ⟨sub1_474, List.forall_mem_cons.2 ⟨sub1_475, List.forall_mem_cons.2 ⟨sub1_476, List.forall_mem_cons.2 ⟨sub1_477, List.forall_mem_cons.2 ⟨sub1_478, List.forall_mem_cons.2 ⟨sub1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_480 : sub1 [0, -2, 2] = true := by decide +kernel
theorem sub1_481 : sub1 [0, -2, 3] = true := by decide +kernel
theorem sub1_482 : sub1 [0, -2, 4] = true := by decide +kernel
theorem sub1_483 : sub1 [0, -2, 5] = true := by decide +kernel
theorem sub1_484 : sub1 [0, -2, 6] = true := by decide +kernel
theorem sub1_485 : sub1 [0, -2, 7] = true := by decide +kernel
theorem sub1_486 : sub1 [0, -1, -8] = true := by decide +kernel
theorem sub1_487 : sub1 [0, -1, -7] = true := by decide +kernel
theorem sub1_488 : sub1 [0, -1, -6] = true := by decide +kernel
theorem sub1_489 : sub1 [0, -1, -5] = true := by decide +kernel
theorem sub1_490 : sub1 [0, -1, -4] = true := by decide +kernel
theorem sub1_491 : sub1 [0, -1, -3] = true := by decide +kernel
theorem sub1_492 : sub1 [0, -1, -2] = true := by decide +kernel
theorem sub1_493 : sub1 [0, -1, -1] = true := by decide +kernel
theorem sub1_494 : sub1 [0, -1, 0] = true := by decide +kernel
theorem sub1_495 : sub1 [0, -1, 1] = true := by decide +kernel
theorem sub1_496 : sub1 [0, -1, 2] = true := by decide +kernel
theorem sub1_497 : sub1 [0, -1, 3] = true := by decide +kernel
theorem sub1_498 : sub1 [0, -1, 4] = true := by decide +kernel
theorem sub1_499 : sub1 [0, -1, 5] = true := by decide +kernel
theorem sub1_500 : sub1 [0, -1, 6] = true := by decide +kernel
theorem sub1_501 : sub1 [0, -1, 7] = true := by decide +kernel
theorem sub1_502 : sub1 [0, 0, -8] = true := by decide +kernel
theorem sub1_503 : sub1 [0, 0, -7] = true := by decide +kernel
theorem sub1_504 : sub1 [0, 0, -6] = true := by decide +kernel
theorem sub1_505 : sub1 [0, 0, -5] = true := by decide +kernel
theorem sub1_506 : sub1 [0, 0, -4] = true := by decide +kernel
theorem sub1_507 : sub1 [0, 0, -3] = true := by decide +kernel
theorem sub1_508 : sub1 [0, 0, -2] = true := by decide +kernel
theorem sub1_509 : sub1 [0, 0, -1] = true := by decide +kernel
theorem sub1_510 : sub1 [0, 0, 0] = true := by decide +kernel
theorem sub1_511 : sub1 [0, 0, 1] = true := by decide +kernel
theorem sb1_15 : ∀ q ∈ blk1_15, sub1 q = true := by
  unfold blk1_15
  exact List.forall_mem_cons.2 ⟨sub1_480, List.forall_mem_cons.2 ⟨sub1_481, List.forall_mem_cons.2 ⟨sub1_482, List.forall_mem_cons.2 ⟨sub1_483, List.forall_mem_cons.2 ⟨sub1_484, List.forall_mem_cons.2 ⟨sub1_485, List.forall_mem_cons.2 ⟨sub1_486, List.forall_mem_cons.2 ⟨sub1_487, List.forall_mem_cons.2 ⟨sub1_488, List.forall_mem_cons.2 ⟨sub1_489, List.forall_mem_cons.2 ⟨sub1_490, List.forall_mem_cons.2 ⟨sub1_491, List.forall_mem_cons.2 ⟨sub1_492, List.forall_mem_cons.2 ⟨sub1_493, List.forall_mem_cons.2 ⟨sub1_494, List.forall_mem_cons.2 ⟨sub1_495, List.forall_mem_cons.2 ⟨sub1_496, List.forall_mem_cons.2 ⟨sub1_497, List.forall_mem_cons.2 ⟨sub1_498, List.forall_mem_cons.2 ⟨sub1_499, List.forall_mem_cons.2 ⟨sub1_500, List.forall_mem_cons.2 ⟨sub1_501, List.forall_mem_cons.2 ⟨sub1_502, List.forall_mem_cons.2 ⟨sub1_503, List.forall_mem_cons.2 ⟨sub1_504, List.forall_mem_cons.2 ⟨sub1_505, List.forall_mem_cons.2 ⟨sub1_506, List.forall_mem_cons.2 ⟨sub1_507, List.forall_mem_cons.2 ⟨sub1_508, List.forall_mem_cons.2 ⟨sub1_509, List.forall_mem_cons.2 ⟨sub1_510, List.forall_mem_cons.2 ⟨sub1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_512 : sub1 [0, 0, 2] = true := by decide +kernel
theorem sub1_513 : sub1 [0, 0, 3] = true := by decide +kernel
theorem sub1_514 : sub1 [0, 0, 4] = true := by decide +kernel
theorem sub1_515 : sub1 [0, 0, 5] = true := by decide +kernel
theorem sub1_516 : sub1 [0, 0, 6] = true := by decide +kernel
theorem sub1_517 : sub1 [0, 0, 7] = true := by decide +kernel
theorem sub1_518 : sub1 [0, 1, -8] = true := by decide +kernel
theorem sub1_519 : sub1 [0, 1, -7] = true := by decide +kernel
theorem sub1_520 : sub1 [0, 1, -6] = true := by decide +kernel
theorem sub1_521 : sub1 [0, 1, -5] = true := by decide +kernel
theorem sub1_522 : sub1 [0, 1, -4] = true := by decide +kernel
theorem sub1_523 : sub1 [0, 1, -3] = true := by decide +kernel
theorem sub1_524 : sub1 [0, 1, -2] = true := by decide +kernel
theorem sub1_525 : sub1 [0, 1, -1] = true := by decide +kernel
theorem sub1_526 : sub1 [0, 1, 0] = true := by decide +kernel
theorem sub1_527 : sub1 [0, 1, 1] = true := by decide +kernel
theorem sub1_528 : sub1 [0, 1, 2] = true := by decide +kernel
theorem sub1_529 : sub1 [0, 1, 3] = true := by decide +kernel
theorem sub1_530 : sub1 [0, 1, 4] = true := by decide +kernel
theorem sub1_531 : sub1 [0, 1, 5] = true := by decide +kernel
theorem sub1_532 : sub1 [0, 1, 6] = true := by decide +kernel
theorem sub1_533 : sub1 [0, 1, 7] = true := by decide +kernel
theorem sub1_534 : sub1 [0, 2, -8] = true := by decide +kernel
theorem sub1_535 : sub1 [0, 2, -7] = true := by decide +kernel
theorem sub1_536 : sub1 [0, 2, -6] = true := by decide +kernel
theorem sub1_537 : sub1 [0, 2, -5] = true := by decide +kernel
theorem sub1_538 : sub1 [0, 2, -4] = true := by decide +kernel
theorem sub1_539 : sub1 [0, 2, -3] = true := by decide +kernel
theorem sub1_540 : sub1 [0, 2, -2] = true := by decide +kernel
theorem sub1_541 : sub1 [0, 2, -1] = true := by decide +kernel
theorem sub1_542 : sub1 [0, 2, 0] = true := by decide +kernel
theorem sub1_543 : sub1 [0, 2, 1] = true := by decide +kernel
theorem sb1_16 : ∀ q ∈ blk1_16, sub1 q = true := by
  unfold blk1_16
  exact List.forall_mem_cons.2 ⟨sub1_512, List.forall_mem_cons.2 ⟨sub1_513, List.forall_mem_cons.2 ⟨sub1_514, List.forall_mem_cons.2 ⟨sub1_515, List.forall_mem_cons.2 ⟨sub1_516, List.forall_mem_cons.2 ⟨sub1_517, List.forall_mem_cons.2 ⟨sub1_518, List.forall_mem_cons.2 ⟨sub1_519, List.forall_mem_cons.2 ⟨sub1_520, List.forall_mem_cons.2 ⟨sub1_521, List.forall_mem_cons.2 ⟨sub1_522, List.forall_mem_cons.2 ⟨sub1_523, List.forall_mem_cons.2 ⟨sub1_524, List.forall_mem_cons.2 ⟨sub1_525, List.forall_mem_cons.2 ⟨sub1_526, List.forall_mem_cons.2 ⟨sub1_527, List.forall_mem_cons.2 ⟨sub1_528, List.forall_mem_cons.2 ⟨sub1_529, List.forall_mem_cons.2 ⟨sub1_530, List.forall_mem_cons.2 ⟨sub1_531, List.forall_mem_cons.2 ⟨sub1_532, List.forall_mem_cons.2 ⟨sub1_533, List.forall_mem_cons.2 ⟨sub1_534, List.forall_mem_cons.2 ⟨sub1_535, List.forall_mem_cons.2 ⟨sub1_536, List.forall_mem_cons.2 ⟨sub1_537, List.forall_mem_cons.2 ⟨sub1_538, List.forall_mem_cons.2 ⟨sub1_539, List.forall_mem_cons.2 ⟨sub1_540, List.forall_mem_cons.2 ⟨sub1_541, List.forall_mem_cons.2 ⟨sub1_542, List.forall_mem_cons.2 ⟨sub1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_544 : sub1 [0, 2, 2] = true := by decide +kernel
theorem sub1_545 : sub1 [0, 2, 3] = true := by decide +kernel
theorem sub1_546 : sub1 [0, 2, 4] = true := by decide +kernel
theorem sub1_547 : sub1 [0, 2, 5] = true := by decide +kernel
theorem sub1_548 : sub1 [0, 2, 6] = true := by decide +kernel
theorem sub1_549 : sub1 [0, 2, 7] = true := by decide +kernel
theorem sub1_550 : sub1 [0, 3, -8] = true := by decide +kernel
theorem sub1_551 : sub1 [0, 3, -7] = true := by decide +kernel
theorem sub1_552 : sub1 [0, 3, -6] = true := by decide +kernel
theorem sub1_553 : sub1 [0, 3, -5] = true := by decide +kernel
theorem sub1_554 : sub1 [0, 3, -4] = true := by decide +kernel
theorem sub1_555 : sub1 [0, 3, -3] = true := by decide +kernel
theorem sub1_556 : sub1 [0, 3, -2] = true := by decide +kernel
theorem sub1_557 : sub1 [0, 3, -1] = true := by decide +kernel
theorem sub1_558 : sub1 [0, 3, 0] = true := by decide +kernel
theorem sub1_559 : sub1 [0, 3, 1] = true := by decide +kernel
theorem sub1_560 : sub1 [0, 3, 2] = true := by decide +kernel
theorem sub1_561 : sub1 [0, 3, 3] = true := by decide +kernel
theorem sub1_562 : sub1 [0, 3, 4] = true := by decide +kernel
theorem sub1_563 : sub1 [0, 3, 5] = true := by decide +kernel
theorem sub1_564 : sub1 [0, 3, 6] = true := by decide +kernel
theorem sub1_565 : sub1 [0, 4, -7] = true := by decide +kernel
theorem sub1_566 : sub1 [0, 4, -6] = true := by decide +kernel
theorem sub1_567 : sub1 [0, 4, -5] = true := by decide +kernel
theorem sub1_568 : sub1 [0, 4, -4] = true := by decide +kernel
theorem sub1_569 : sub1 [0, 4, -3] = true := by decide +kernel
theorem sub1_570 : sub1 [0, 4, -2] = true := by decide +kernel
theorem sub1_571 : sub1 [0, 4, -1] = true := by decide +kernel
theorem sub1_572 : sub1 [0, 4, 0] = true := by decide +kernel
theorem sub1_573 : sub1 [0, 4, 1] = true := by decide +kernel
theorem sub1_574 : sub1 [0, 4, 2] = true := by decide +kernel
theorem sub1_575 : sub1 [0, 4, 3] = true := by decide +kernel
theorem sb1_17 : ∀ q ∈ blk1_17, sub1 q = true := by
  unfold blk1_17
  exact List.forall_mem_cons.2 ⟨sub1_544, List.forall_mem_cons.2 ⟨sub1_545, List.forall_mem_cons.2 ⟨sub1_546, List.forall_mem_cons.2 ⟨sub1_547, List.forall_mem_cons.2 ⟨sub1_548, List.forall_mem_cons.2 ⟨sub1_549, List.forall_mem_cons.2 ⟨sub1_550, List.forall_mem_cons.2 ⟨sub1_551, List.forall_mem_cons.2 ⟨sub1_552, List.forall_mem_cons.2 ⟨sub1_553, List.forall_mem_cons.2 ⟨sub1_554, List.forall_mem_cons.2 ⟨sub1_555, List.forall_mem_cons.2 ⟨sub1_556, List.forall_mem_cons.2 ⟨sub1_557, List.forall_mem_cons.2 ⟨sub1_558, List.forall_mem_cons.2 ⟨sub1_559, List.forall_mem_cons.2 ⟨sub1_560, List.forall_mem_cons.2 ⟨sub1_561, List.forall_mem_cons.2 ⟨sub1_562, List.forall_mem_cons.2 ⟨sub1_563, List.forall_mem_cons.2 ⟨sub1_564, List.forall_mem_cons.2 ⟨sub1_565, List.forall_mem_cons.2 ⟨sub1_566, List.forall_mem_cons.2 ⟨sub1_567, List.forall_mem_cons.2 ⟨sub1_568, List.forall_mem_cons.2 ⟨sub1_569, List.forall_mem_cons.2 ⟨sub1_570, List.forall_mem_cons.2 ⟨sub1_571, List.forall_mem_cons.2 ⟨sub1_572, List.forall_mem_cons.2 ⟨sub1_573, List.forall_mem_cons.2 ⟨sub1_574, List.forall_mem_cons.2 ⟨sub1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C043
