import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_9_96 : subd7_9 [-1, -1, 4] = true := by decide +kernel
theorem subd7_9_97 : subd7_9 [-1, -1, 5] = true := by decide +kernel
theorem subd7_9_98 : subd7_9 [-1, -1, 6] = true := by decide +kernel
theorem subd7_9_99 : subd7_9 [-1, 0, -7] = true := by decide +kernel
theorem subd7_9_100 : subd7_9 [-1, 0, -6] = true := by decide +kernel
theorem subd7_9_101 : subd7_9 [-1, 0, -5] = true := by decide +kernel
theorem subd7_9_102 : subd7_9 [-1, 0, -4] = true := by decide +kernel
theorem subd7_9_103 : subd7_9 [-1, 0, -3] = true := by decide +kernel
theorem subd7_9_104 : subd7_9 [-1, 0, -2] = true := by decide +kernel
theorem subd7_9_105 : subd7_9 [-1, 0, -1] = true := by decide +kernel
theorem subd7_9_106 : subd7_9 [-1, 0, 0] = true := by decide +kernel
theorem subd7_9_107 : subd7_9 [-1, 0, 1] = true := by decide +kernel
theorem subd7_9_108 : subd7_9 [-1, 0, 2] = true := by decide +kernel
theorem subd7_9_109 : subd7_9 [-1, 0, 3] = true := by decide +kernel
theorem subd7_9_110 : subd7_9 [-1, 0, 4] = true := by decide +kernel
theorem subd7_9_111 : subd7_9 [-1, 0, 5] = true := by decide +kernel
theorem subd7_9_112 : subd7_9 [-1, 0, 6] = true := by decide +kernel
theorem subd7_9_113 : subd7_9 [-1, 1, -7] = true := by decide +kernel
theorem subd7_9_114 : subd7_9 [-1, 1, -6] = true := by decide +kernel
theorem subd7_9_115 : subd7_9 [-1, 1, -5] = true := by decide +kernel
theorem subd7_9_116 : subd7_9 [-1, 1, -4] = true := by decide +kernel
theorem subd7_9_117 : subd7_9 [-1, 1, -3] = true := by decide +kernel
theorem subd7_9_118 : subd7_9 [-1, 1, -2] = true := by decide +kernel
theorem subd7_9_119 : subd7_9 [-1, 1, -1] = true := by decide +kernel
theorem subd7_9_120 : subd7_9 [-1, 1, 0] = true := by decide +kernel
theorem subd7_9_121 : subd7_9 [-1, 1, 1] = true := by decide +kernel
theorem subd7_9_122 : subd7_9 [-1, 1, 2] = true := by decide +kernel
theorem subd7_9_123 : subd7_9 [-1, 1, 3] = true := by decide +kernel
theorem subd7_9_124 : subd7_9 [-1, 1, 4] = true := by decide +kernel
theorem subd7_9_125 : subd7_9 [-1, 1, 5] = true := by decide +kernel
theorem subd7_9_126 : subd7_9 [-1, 2] = true := by decide +kernel
theorem subd7_9_127 : subd7_9 [-1, 3] = true := by decide +kernel
theorem sbd7_9_3 : ∀ q ∈ blkd7_9_3, subd7_9 q = true := by
  unfold blkd7_9_3
  exact List.forall_mem_cons.2 ⟨subd7_9_96, List.forall_mem_cons.2 ⟨subd7_9_97, List.forall_mem_cons.2 ⟨subd7_9_98, List.forall_mem_cons.2 ⟨subd7_9_99, List.forall_mem_cons.2 ⟨subd7_9_100, List.forall_mem_cons.2 ⟨subd7_9_101, List.forall_mem_cons.2 ⟨subd7_9_102, List.forall_mem_cons.2 ⟨subd7_9_103, List.forall_mem_cons.2 ⟨subd7_9_104, List.forall_mem_cons.2 ⟨subd7_9_105, List.forall_mem_cons.2 ⟨subd7_9_106, List.forall_mem_cons.2 ⟨subd7_9_107, List.forall_mem_cons.2 ⟨subd7_9_108, List.forall_mem_cons.2 ⟨subd7_9_109, List.forall_mem_cons.2 ⟨subd7_9_110, List.forall_mem_cons.2 ⟨subd7_9_111, List.forall_mem_cons.2 ⟨subd7_9_112, List.forall_mem_cons.2 ⟨subd7_9_113, List.forall_mem_cons.2 ⟨subd7_9_114, List.forall_mem_cons.2 ⟨subd7_9_115, List.forall_mem_cons.2 ⟨subd7_9_116, List.forall_mem_cons.2 ⟨subd7_9_117, List.forall_mem_cons.2 ⟨subd7_9_118, List.forall_mem_cons.2 ⟨subd7_9_119, List.forall_mem_cons.2 ⟨subd7_9_120, List.forall_mem_cons.2 ⟨subd7_9_121, List.forall_mem_cons.2 ⟨subd7_9_122, List.forall_mem_cons.2 ⟨subd7_9_123, List.forall_mem_cons.2 ⟨subd7_9_124, List.forall_mem_cons.2 ⟨subd7_9_125, List.forall_mem_cons.2 ⟨subd7_9_126, List.forall_mem_cons.2 ⟨subd7_9_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_9_128 : subd7_9 [-1, 4] = true := by decide +kernel
theorem subd7_9_129 : subd7_9 [-1, 5] = true := by decide +kernel
theorem subd7_9_130 : subd7_9 [-1, 6] = true := by decide +kernel
theorem subd7_9_131 : subd7_9 [0, -7] = true := by decide +kernel
theorem subd7_9_132 : subd7_9 [0, -6] = true := by decide +kernel
theorem subd7_9_133 : subd7_9 [0, -5] = true := by decide +kernel
theorem subd7_9_134 : subd7_9 [0, -4] = true := by decide +kernel
theorem subd7_9_135 : subd7_9 [0, -3] = true := by decide +kernel
theorem subd7_9_136 : subd7_9 [0, -2, -6] = true := by decide +kernel
theorem subd7_9_137 : subd7_9 [0, -2, -5] = true := by decide +kernel
theorem subd7_9_138 : subd7_9 [0, -2, -4] = true := by decide +kernel
theorem subd7_9_139 : subd7_9 [0, -2, -3] = true := by decide +kernel
theorem subd7_9_140 : subd7_9 [0, -2, -2] = true := by decide +kernel
theorem subd7_9_141 : subd7_9 [0, -2, -1] = true := by decide +kernel
theorem subd7_9_142 : subd7_9 [0, -2, 0] = true := by decide +kernel
theorem subd7_9_143 : subd7_9 [0, -2, 1] = true := by decide +kernel
theorem subd7_9_144 : subd7_9 [0, -2, 2] = true := by decide +kernel
theorem subd7_9_145 : subd7_9 [0, -2, 3] = true := by decide +kernel
theorem subd7_9_146 : subd7_9 [0, -2, 4] = true := by decide +kernel
theorem subd7_9_147 : subd7_9 [0, -2, 5] = true := by decide +kernel
theorem subd7_9_148 : subd7_9 [0, -2, 6] = true := by decide +kernel
theorem subd7_9_149 : subd7_9 [0, -1, -7] = true := by decide +kernel
theorem subd7_9_150 : subd7_9 [0, -1, -6] = true := by decide +kernel
theorem subd7_9_151 : subd7_9 [0, -1, -5] = true := by decide +kernel
theorem subd7_9_152 : subd7_9 [0, -1, -4] = true := by decide +kernel
theorem subd7_9_153 : subd7_9 [0, -1, -3] = true := by decide +kernel
theorem subd7_9_154 : subd7_9 [0, -1, -2] = true := by decide +kernel
theorem subd7_9_155 : subd7_9 [0, -1, -1] = true := by decide +kernel
theorem subd7_9_156 : subd7_9 [0, -1, 0] = true := by decide +kernel
theorem subd7_9_157 : subd7_9 [0, -1, 1] = true := by decide +kernel
theorem subd7_9_158 : subd7_9 [0, -1, 2] = true := by decide +kernel
theorem subd7_9_159 : subd7_9 [0, -1, 3] = true := by decide +kernel
theorem sbd7_9_4 : ∀ q ∈ blkd7_9_4, subd7_9 q = true := by
  unfold blkd7_9_4
  exact List.forall_mem_cons.2 ⟨subd7_9_128, List.forall_mem_cons.2 ⟨subd7_9_129, List.forall_mem_cons.2 ⟨subd7_9_130, List.forall_mem_cons.2 ⟨subd7_9_131, List.forall_mem_cons.2 ⟨subd7_9_132, List.forall_mem_cons.2 ⟨subd7_9_133, List.forall_mem_cons.2 ⟨subd7_9_134, List.forall_mem_cons.2 ⟨subd7_9_135, List.forall_mem_cons.2 ⟨subd7_9_136, List.forall_mem_cons.2 ⟨subd7_9_137, List.forall_mem_cons.2 ⟨subd7_9_138, List.forall_mem_cons.2 ⟨subd7_9_139, List.forall_mem_cons.2 ⟨subd7_9_140, List.forall_mem_cons.2 ⟨subd7_9_141, List.forall_mem_cons.2 ⟨subd7_9_142, List.forall_mem_cons.2 ⟨subd7_9_143, List.forall_mem_cons.2 ⟨subd7_9_144, List.forall_mem_cons.2 ⟨subd7_9_145, List.forall_mem_cons.2 ⟨subd7_9_146, List.forall_mem_cons.2 ⟨subd7_9_147, List.forall_mem_cons.2 ⟨subd7_9_148, List.forall_mem_cons.2 ⟨subd7_9_149, List.forall_mem_cons.2 ⟨subd7_9_150, List.forall_mem_cons.2 ⟨subd7_9_151, List.forall_mem_cons.2 ⟨subd7_9_152, List.forall_mem_cons.2 ⟨subd7_9_153, List.forall_mem_cons.2 ⟨subd7_9_154, List.forall_mem_cons.2 ⟨subd7_9_155, List.forall_mem_cons.2 ⟨subd7_9_156, List.forall_mem_cons.2 ⟨subd7_9_157, List.forall_mem_cons.2 ⟨subd7_9_158, List.forall_mem_cons.2 ⟨subd7_9_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_9_160 : subd7_9 [0, -1, 4] = true := by decide +kernel
theorem subd7_9_161 : subd7_9 [0, -1, 5] = true := by decide +kernel
theorem subd7_9_162 : subd7_9 [0, -1, 6] = true := by decide +kernel
theorem subd7_9_163 : subd7_9 [0, 0, -7] = true := by decide +kernel
theorem subd7_9_164 : subd7_9 [0, 0, -6] = true := by decide +kernel
theorem subd7_9_165 : subd7_9 [0, 0, -5] = true := by decide +kernel
theorem subd7_9_166 : subd7_9 [0, 0, -4] = true := by decide +kernel
theorem subd7_9_167 : subd7_9 [0, 0, -3] = true := by decide +kernel
theorem subd7_9_168 : subd7_9 [0, 0, -2] = true := by decide +kernel
theorem subd7_9_169 : subd7_9 [0, 0, -1] = true := by decide +kernel
theorem subd7_9_170 : subd7_9 [0, 0, 0] = true := by decide +kernel
theorem subd7_9_171 : subd7_9 [0, 0, 1] = true := by decide +kernel
theorem subd7_9_172 : subd7_9 [0, 0, 2] = true := by decide +kernel
theorem subd7_9_173 : subd7_9 [0, 0, 3] = true := by decide +kernel
theorem subd7_9_174 : subd7_9 [0, 0, 4] = true := by decide +kernel
theorem subd7_9_175 : subd7_9 [0, 0, 5] = true := by decide +kernel
theorem subd7_9_176 : subd7_9 [0, 0, 6] = true := by decide +kernel
theorem subd7_9_177 : subd7_9 [0, 1, -7] = true := by decide +kernel
theorem subd7_9_178 : subd7_9 [0, 1, -6] = true := by decide +kernel
theorem subd7_9_179 : subd7_9 [0, 1, -5] = true := by decide +kernel
theorem subd7_9_180 : subd7_9 [0, 1, -4] = true := by decide +kernel
theorem subd7_9_181 : subd7_9 [0, 1, -3] = true := by decide +kernel
theorem subd7_9_182 : subd7_9 [0, 1, -2] = true := by decide +kernel
theorem subd7_9_183 : subd7_9 [0, 1, -1] = true := by decide +kernel
theorem subd7_9_184 : subd7_9 [0, 1, 0] = true := by decide +kernel
theorem subd7_9_185 : subd7_9 [0, 1, 1] = true := by decide +kernel
theorem subd7_9_186 : subd7_9 [0, 1, 2] = true := by decide +kernel
theorem subd7_9_187 : subd7_9 [0, 1, 3] = true := by decide +kernel
theorem subd7_9_188 : subd7_9 [0, 1, 4] = true := by decide +kernel
theorem subd7_9_189 : subd7_9 [0, 1, 5] = true := by decide +kernel
theorem subd7_9_190 : subd7_9 [0, 1, 6] = true := by decide +kernel
theorem subd7_9_191 : subd7_9 [0, 2, -7] = true := by decide +kernel
theorem sbd7_9_5 : ∀ q ∈ blkd7_9_5, subd7_9 q = true := by
  unfold blkd7_9_5
  exact List.forall_mem_cons.2 ⟨subd7_9_160, List.forall_mem_cons.2 ⟨subd7_9_161, List.forall_mem_cons.2 ⟨subd7_9_162, List.forall_mem_cons.2 ⟨subd7_9_163, List.forall_mem_cons.2 ⟨subd7_9_164, List.forall_mem_cons.2 ⟨subd7_9_165, List.forall_mem_cons.2 ⟨subd7_9_166, List.forall_mem_cons.2 ⟨subd7_9_167, List.forall_mem_cons.2 ⟨subd7_9_168, List.forall_mem_cons.2 ⟨subd7_9_169, List.forall_mem_cons.2 ⟨subd7_9_170, List.forall_mem_cons.2 ⟨subd7_9_171, List.forall_mem_cons.2 ⟨subd7_9_172, List.forall_mem_cons.2 ⟨subd7_9_173, List.forall_mem_cons.2 ⟨subd7_9_174, List.forall_mem_cons.2 ⟨subd7_9_175, List.forall_mem_cons.2 ⟨subd7_9_176, List.forall_mem_cons.2 ⟨subd7_9_177, List.forall_mem_cons.2 ⟨subd7_9_178, List.forall_mem_cons.2 ⟨subd7_9_179, List.forall_mem_cons.2 ⟨subd7_9_180, List.forall_mem_cons.2 ⟨subd7_9_181, List.forall_mem_cons.2 ⟨subd7_9_182, List.forall_mem_cons.2 ⟨subd7_9_183, List.forall_mem_cons.2 ⟨subd7_9_184, List.forall_mem_cons.2 ⟨subd7_9_185, List.forall_mem_cons.2 ⟨subd7_9_186, List.forall_mem_cons.2 ⟨subd7_9_187, List.forall_mem_cons.2 ⟨subd7_9_188, List.forall_mem_cons.2 ⟨subd7_9_189, List.forall_mem_cons.2 ⟨subd7_9_190, List.forall_mem_cons.2 ⟨subd7_9_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_9_192 : subd7_9 [0, 2, -6] = true := by decide +kernel
theorem subd7_9_193 : subd7_9 [0, 2, -5] = true := by decide +kernel
theorem subd7_9_194 : subd7_9 [0, 2, -4] = true := by decide +kernel
theorem subd7_9_195 : subd7_9 [0, 2, -3] = true := by decide +kernel
theorem subd7_9_196 : subd7_9 [0, 2, -2] = true := by decide +kernel
theorem subd7_9_197 : subd7_9 [0, 2, -1] = true := by decide +kernel
theorem subd7_9_198 : subd7_9 [0, 2, 0] = true := by decide +kernel
theorem subd7_9_199 : subd7_9 [0, 2, 1] = true := by decide +kernel
theorem subd7_9_200 : subd7_9 [0, 2, 2] = true := by decide +kernel
theorem subd7_9_201 : subd7_9 [0, 2, 3] = true := by decide +kernel
theorem subd7_9_202 : subd7_9 [0, 2, 4] = true := by decide +kernel
theorem subd7_9_203 : subd7_9 [0, 2, 5] = true := by decide +kernel
theorem subd7_9_204 : subd7_9 [0, 3] = true := by decide +kernel
theorem subd7_9_205 : subd7_9 [0, 4] = true := by decide +kernel
theorem subd7_9_206 : subd7_9 [0, 5] = true := by decide +kernel
theorem subd7_9_207 : subd7_9 [0, 6] = true := by decide +kernel
theorem subd7_9_208 : subd7_9 [1, -7] = true := by decide +kernel
theorem subd7_9_209 : subd7_9 [1, -6] = true := by decide +kernel
theorem subd7_9_210 : subd7_9 [1, -5] = true := by decide +kernel
theorem subd7_9_211 : subd7_9 [1, -4] = true := by decide +kernel
theorem subd7_9_212 : subd7_9 [1, -3] = true := by decide +kernel
theorem subd7_9_213 : subd7_9 [1, -2] = true := by decide +kernel
theorem subd7_9_214 : subd7_9 [1, -1, -6] = true := by decide +kernel
theorem subd7_9_215 : subd7_9 [1, -1, -5] = true := by decide +kernel
theorem subd7_9_216 : subd7_9 [1, -1, -4] = true := by decide +kernel
theorem subd7_9_217 : subd7_9 [1, -1, -3] = true := by decide +kernel
theorem subd7_9_218 : subd7_9 [1, -1, -2] = true := by decide +kernel
theorem subd7_9_219 : subd7_9 [1, -1, -1] = true := by decide +kernel
theorem subd7_9_220 : subd7_9 [1, -1, 0] = true := by decide +kernel
theorem subd7_9_221 : subd7_9 [1, -1, 1] = true := by decide +kernel
theorem subd7_9_222 : subd7_9 [1, -1, 2] = true := by decide +kernel
theorem subd7_9_223 : subd7_9 [1, -1, 3] = true := by decide +kernel
theorem sbd7_9_6 : ∀ q ∈ blkd7_9_6, subd7_9 q = true := by
  unfold blkd7_9_6
  exact List.forall_mem_cons.2 ⟨subd7_9_192, List.forall_mem_cons.2 ⟨subd7_9_193, List.forall_mem_cons.2 ⟨subd7_9_194, List.forall_mem_cons.2 ⟨subd7_9_195, List.forall_mem_cons.2 ⟨subd7_9_196, List.forall_mem_cons.2 ⟨subd7_9_197, List.forall_mem_cons.2 ⟨subd7_9_198, List.forall_mem_cons.2 ⟨subd7_9_199, List.forall_mem_cons.2 ⟨subd7_9_200, List.forall_mem_cons.2 ⟨subd7_9_201, List.forall_mem_cons.2 ⟨subd7_9_202, List.forall_mem_cons.2 ⟨subd7_9_203, List.forall_mem_cons.2 ⟨subd7_9_204, List.forall_mem_cons.2 ⟨subd7_9_205, List.forall_mem_cons.2 ⟨subd7_9_206, List.forall_mem_cons.2 ⟨subd7_9_207, List.forall_mem_cons.2 ⟨subd7_9_208, List.forall_mem_cons.2 ⟨subd7_9_209, List.forall_mem_cons.2 ⟨subd7_9_210, List.forall_mem_cons.2 ⟨subd7_9_211, List.forall_mem_cons.2 ⟨subd7_9_212, List.forall_mem_cons.2 ⟨subd7_9_213, List.forall_mem_cons.2 ⟨subd7_9_214, List.forall_mem_cons.2 ⟨subd7_9_215, List.forall_mem_cons.2 ⟨subd7_9_216, List.forall_mem_cons.2 ⟨subd7_9_217, List.forall_mem_cons.2 ⟨subd7_9_218, List.forall_mem_cons.2 ⟨subd7_9_219, List.forall_mem_cons.2 ⟨subd7_9_220, List.forall_mem_cons.2 ⟨subd7_9_221, List.forall_mem_cons.2 ⟨subd7_9_222, List.forall_mem_cons.2 ⟨subd7_9_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_9_224 : subd7_9 [1, -1, 4] = true := by decide +kernel
theorem subd7_9_225 : subd7_9 [1, -1, 5] = true := by decide +kernel
theorem subd7_9_226 : subd7_9 [1, -1, 6] = true := by decide +kernel
theorem subd7_9_227 : subd7_9 [1, 0, -7] = true := by decide +kernel
theorem subd7_9_228 : subd7_9 [1, 0, -6] = true := by decide +kernel
theorem subd7_9_229 : subd7_9 [1, 0, -5] = true := by decide +kernel
theorem subd7_9_230 : subd7_9 [1, 0, -4] = true := by decide +kernel
theorem subd7_9_231 : subd7_9 [1, 0, -3] = true := by decide +kernel
theorem subd7_9_232 : subd7_9 [1, 0, -2] = true := by decide +kernel
theorem subd7_9_233 : subd7_9 [1, 0, -1] = true := by decide +kernel
theorem subd7_9_234 : subd7_9 [1, 0, 0] = true := by decide +kernel
theorem subd7_9_235 : subd7_9 [1, 0, 1] = true := by decide +kernel
theorem subd7_9_236 : subd7_9 [1, 0, 2] = true := by decide +kernel
theorem subd7_9_237 : subd7_9 [1, 0, 3] = true := by decide +kernel
theorem subd7_9_238 : subd7_9 [1, 0, 4] = true := by decide +kernel
theorem subd7_9_239 : subd7_9 [1, 0, 5] = true := by decide +kernel
theorem subd7_9_240 : subd7_9 [1, 0, 6] = true := by decide +kernel
theorem subd7_9_241 : subd7_9 [1, 1, -7] = true := by decide +kernel
theorem subd7_9_242 : subd7_9 [1, 1, -6] = true := by decide +kernel
theorem subd7_9_243 : subd7_9 [1, 1, -5] = true := by decide +kernel
theorem subd7_9_244 : subd7_9 [1, 1, -4] = true := by decide +kernel
theorem subd7_9_245 : subd7_9 [1, 1, -3] = true := by decide +kernel
theorem subd7_9_246 : subd7_9 [1, 1, -2] = true := by decide +kernel
theorem subd7_9_247 : subd7_9 [1, 1, -1] = true := by decide +kernel
theorem subd7_9_248 : subd7_9 [1, 1, 0] = true := by decide +kernel
theorem subd7_9_249 : subd7_9 [1, 1, 1] = true := by decide +kernel
theorem subd7_9_250 : subd7_9 [1, 1, 2] = true := by decide +kernel
theorem subd7_9_251 : subd7_9 [1, 1, 3] = true := by decide +kernel
theorem subd7_9_252 : subd7_9 [1, 1, 4] = true := by decide +kernel
theorem subd7_9_253 : subd7_9 [1, 1, 5] = true := by decide +kernel
theorem subd7_9_254 : subd7_9 [1, 1, 6] = true := by decide +kernel
theorem subd7_9_255 : subd7_9 [1, 2, -7] = true := by decide +kernel
theorem sbd7_9_7 : ∀ q ∈ blkd7_9_7, subd7_9 q = true := by
  unfold blkd7_9_7
  exact List.forall_mem_cons.2 ⟨subd7_9_224, List.forall_mem_cons.2 ⟨subd7_9_225, List.forall_mem_cons.2 ⟨subd7_9_226, List.forall_mem_cons.2 ⟨subd7_9_227, List.forall_mem_cons.2 ⟨subd7_9_228, List.forall_mem_cons.2 ⟨subd7_9_229, List.forall_mem_cons.2 ⟨subd7_9_230, List.forall_mem_cons.2 ⟨subd7_9_231, List.forall_mem_cons.2 ⟨subd7_9_232, List.forall_mem_cons.2 ⟨subd7_9_233, List.forall_mem_cons.2 ⟨subd7_9_234, List.forall_mem_cons.2 ⟨subd7_9_235, List.forall_mem_cons.2 ⟨subd7_9_236, List.forall_mem_cons.2 ⟨subd7_9_237, List.forall_mem_cons.2 ⟨subd7_9_238, List.forall_mem_cons.2 ⟨subd7_9_239, List.forall_mem_cons.2 ⟨subd7_9_240, List.forall_mem_cons.2 ⟨subd7_9_241, List.forall_mem_cons.2 ⟨subd7_9_242, List.forall_mem_cons.2 ⟨subd7_9_243, List.forall_mem_cons.2 ⟨subd7_9_244, List.forall_mem_cons.2 ⟨subd7_9_245, List.forall_mem_cons.2 ⟨subd7_9_246, List.forall_mem_cons.2 ⟨subd7_9_247, List.forall_mem_cons.2 ⟨subd7_9_248, List.forall_mem_cons.2 ⟨subd7_9_249, List.forall_mem_cons.2 ⟨subd7_9_250, List.forall_mem_cons.2 ⟨subd7_9_251, List.forall_mem_cons.2 ⟨subd7_9_252, List.forall_mem_cons.2 ⟨subd7_9_253, List.forall_mem_cons.2 ⟨subd7_9_254, List.forall_mem_cons.2 ⟨subd7_9_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_9_256 : subd7_9 [1, 2, -6] = true := by decide +kernel
theorem subd7_9_257 : subd7_9 [1, 2, -5] = true := by decide +kernel
theorem subd7_9_258 : subd7_9 [1, 2, -4] = true := by decide +kernel
theorem subd7_9_259 : subd7_9 [1, 2, -3] = true := by decide +kernel
theorem subd7_9_260 : subd7_9 [1, 2, -2] = true := by decide +kernel
theorem subd7_9_261 : subd7_9 [1, 2, -1] = true := by decide +kernel
theorem subd7_9_262 : subd7_9 [1, 2, 0] = true := by decide +kernel
theorem subd7_9_263 : subd7_9 [1, 2, 1] = true := by decide +kernel
theorem subd7_9_264 : subd7_9 [1, 2, 2] = true := by decide +kernel
theorem subd7_9_265 : subd7_9 [1, 2, 3] = true := by decide +kernel
theorem subd7_9_266 : subd7_9 [1, 2, 4] = true := by decide +kernel
theorem subd7_9_267 : subd7_9 [1, 2, 5] = true := by decide +kernel
theorem subd7_9_268 : subd7_9 [1, 2, 6] = true := by decide +kernel
theorem subd7_9_269 : subd7_9 [1, 3] = true := by decide +kernel
theorem subd7_9_270 : subd7_9 [1, 4] = true := by decide +kernel
theorem subd7_9_271 : subd7_9 [1, 5] = true := by decide +kernel
theorem subd7_9_272 : subd7_9 [2, -6] = true := by decide +kernel
theorem subd7_9_273 : subd7_9 [2, -5] = true := by decide +kernel
theorem subd7_9_274 : subd7_9 [2, -4] = true := by decide +kernel
theorem subd7_9_275 : subd7_9 [2, -3] = true := by decide +kernel
theorem subd7_9_276 : subd7_9 [2, -2] = true := by decide +kernel
theorem subd7_9_277 : subd7_9 [2, -1] = true := by decide +kernel
theorem subd7_9_278 : subd7_9 [2, 0, -6] = true := by decide +kernel
theorem subd7_9_279 : subd7_9 [2, 0, -5] = true := by decide +kernel
theorem subd7_9_280 : subd7_9 [2, 0, -4] = true := by decide +kernel
theorem subd7_9_281 : subd7_9 [2, 0, -3] = true := by decide +kernel
theorem subd7_9_282 : subd7_9 [2, 0, -2] = true := by decide +kernel
theorem subd7_9_283 : subd7_9 [2, 0, -1] = true := by decide +kernel
theorem subd7_9_284 : subd7_9 [2, 0, 0] = true := by decide +kernel
theorem subd7_9_285 : subd7_9 [2, 0, 1] = true := by decide +kernel
theorem subd7_9_286 : subd7_9 [2, 0, 2] = true := by decide +kernel
theorem subd7_9_287 : subd7_9 [2, 0, 3] = true := by decide +kernel
theorem sbd7_9_8 : ∀ q ∈ blkd7_9_8, subd7_9 q = true := by
  unfold blkd7_9_8
  exact List.forall_mem_cons.2 ⟨subd7_9_256, List.forall_mem_cons.2 ⟨subd7_9_257, List.forall_mem_cons.2 ⟨subd7_9_258, List.forall_mem_cons.2 ⟨subd7_9_259, List.forall_mem_cons.2 ⟨subd7_9_260, List.forall_mem_cons.2 ⟨subd7_9_261, List.forall_mem_cons.2 ⟨subd7_9_262, List.forall_mem_cons.2 ⟨subd7_9_263, List.forall_mem_cons.2 ⟨subd7_9_264, List.forall_mem_cons.2 ⟨subd7_9_265, List.forall_mem_cons.2 ⟨subd7_9_266, List.forall_mem_cons.2 ⟨subd7_9_267, List.forall_mem_cons.2 ⟨subd7_9_268, List.forall_mem_cons.2 ⟨subd7_9_269, List.forall_mem_cons.2 ⟨subd7_9_270, List.forall_mem_cons.2 ⟨subd7_9_271, List.forall_mem_cons.2 ⟨subd7_9_272, List.forall_mem_cons.2 ⟨subd7_9_273, List.forall_mem_cons.2 ⟨subd7_9_274, List.forall_mem_cons.2 ⟨subd7_9_275, List.forall_mem_cons.2 ⟨subd7_9_276, List.forall_mem_cons.2 ⟨subd7_9_277, List.forall_mem_cons.2 ⟨subd7_9_278, List.forall_mem_cons.2 ⟨subd7_9_279, List.forall_mem_cons.2 ⟨subd7_9_280, List.forall_mem_cons.2 ⟨subd7_9_281, List.forall_mem_cons.2 ⟨subd7_9_282, List.forall_mem_cons.2 ⟨subd7_9_283, List.forall_mem_cons.2 ⟨subd7_9_284, List.forall_mem_cons.2 ⟨subd7_9_285, List.forall_mem_cons.2 ⟨subd7_9_286, List.forall_mem_cons.2 ⟨subd7_9_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_9_288 : subd7_9 [2, 0, 4] = true := by decide +kernel
theorem subd7_9_289 : subd7_9 [2, 0, 5] = true := by decide +kernel
theorem subd7_9_290 : subd7_9 [2, 0, 6] = true := by decide +kernel
theorem subd7_9_291 : subd7_9 [2, 1, -6] = true := by decide +kernel
theorem subd7_9_292 : subd7_9 [2, 1, -5] = true := by decide +kernel
theorem subd7_9_293 : subd7_9 [2, 1, -4] = true := by decide +kernel
theorem subd7_9_294 : subd7_9 [2, 1, -3] = true := by decide +kernel
theorem subd7_9_295 : subd7_9 [2, 1, -2] = true := by decide +kernel
theorem subd7_9_296 : subd7_9 [2, 1, -1] = true := by decide +kernel
theorem subd7_9_297 : subd7_9 [2, 1, 0] = true := by decide +kernel
theorem subd7_9_298 : subd7_9 [2, 1, 1] = true := by decide +kernel
theorem subd7_9_299 : subd7_9 [2, 1, 2] = true := by decide +kernel
theorem subd7_9_300 : subd7_9 [2, 1, 3] = true := by decide +kernel
theorem subd7_9_301 : subd7_9 [2, 1, 4] = true := by decide +kernel
theorem subd7_9_302 : subd7_9 [2, 1, 5] = true := by decide +kernel
theorem subd7_9_303 : subd7_9 [2, 1, 6] = true := by decide +kernel
theorem subd7_9_304 : subd7_9 [2, 2] = true := by decide +kernel
theorem subd7_9_305 : subd7_9 [2, 3] = true := by decide +kernel
theorem subd7_9_306 : subd7_9 [2, 4] = true := by decide +kernel
theorem subd7_9_307 : subd7_9 [2, 5] = true := by decide +kernel
theorem subd7_9_308 : subd7_9 [3, -6] = true := by decide +kernel
theorem subd7_9_309 : subd7_9 [3, -5] = true := by decide +kernel
theorem subd7_9_310 : subd7_9 [3, -4] = true := by decide +kernel
theorem subd7_9_311 : subd7_9 [3, -3] = true := by decide +kernel
theorem subd7_9_312 : subd7_9 [3, -2] = true := by decide +kernel
theorem subd7_9_313 : subd7_9 [3, -1] = true := by decide +kernel
theorem subd7_9_314 : subd7_9 [3, 0] = true := by decide +kernel
theorem subd7_9_315 : subd7_9 [3, 1] = true := by decide +kernel
theorem subd7_9_316 : subd7_9 [3, 2] = true := by decide +kernel
theorem subd7_9_317 : subd7_9 [3, 3] = true := by decide +kernel
theorem subd7_9_318 : subd7_9 [3, 4] = true := by decide +kernel
theorem subd7_9_319 : subd7_9 [3, 5] = true := by decide +kernel
theorem sbd7_9_9 : ∀ q ∈ blkd7_9_9, subd7_9 q = true := by
  unfold blkd7_9_9
  exact List.forall_mem_cons.2 ⟨subd7_9_288, List.forall_mem_cons.2 ⟨subd7_9_289, List.forall_mem_cons.2 ⟨subd7_9_290, List.forall_mem_cons.2 ⟨subd7_9_291, List.forall_mem_cons.2 ⟨subd7_9_292, List.forall_mem_cons.2 ⟨subd7_9_293, List.forall_mem_cons.2 ⟨subd7_9_294, List.forall_mem_cons.2 ⟨subd7_9_295, List.forall_mem_cons.2 ⟨subd7_9_296, List.forall_mem_cons.2 ⟨subd7_9_297, List.forall_mem_cons.2 ⟨subd7_9_298, List.forall_mem_cons.2 ⟨subd7_9_299, List.forall_mem_cons.2 ⟨subd7_9_300, List.forall_mem_cons.2 ⟨subd7_9_301, List.forall_mem_cons.2 ⟨subd7_9_302, List.forall_mem_cons.2 ⟨subd7_9_303, List.forall_mem_cons.2 ⟨subd7_9_304, List.forall_mem_cons.2 ⟨subd7_9_305, List.forall_mem_cons.2 ⟨subd7_9_306, List.forall_mem_cons.2 ⟨subd7_9_307, List.forall_mem_cons.2 ⟨subd7_9_308, List.forall_mem_cons.2 ⟨subd7_9_309, List.forall_mem_cons.2 ⟨subd7_9_310, List.forall_mem_cons.2 ⟨subd7_9_311, List.forall_mem_cons.2 ⟨subd7_9_312, List.forall_mem_cons.2 ⟨subd7_9_313, List.forall_mem_cons.2 ⟨subd7_9_314, List.forall_mem_cons.2 ⟨subd7_9_315, List.forall_mem_cons.2 ⟨subd7_9_316, List.forall_mem_cons.2 ⟨subd7_9_317, List.forall_mem_cons.2 ⟨subd7_9_318, List.forall_mem_cons.2 ⟨subd7_9_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_9_320 : subd7_9 [4, -5] = true := by decide +kernel
theorem subd7_9_321 : subd7_9 [4, -4] = true := by decide +kernel
theorem subd7_9_322 : subd7_9 [4, -3] = true := by decide +kernel
theorem subd7_9_323 : subd7_9 [4, -2] = true := by decide +kernel
theorem subd7_9_324 : subd7_9 [4, -1] = true := by decide +kernel
theorem subd7_9_325 : subd7_9 [4, 0] = true := by decide +kernel
theorem subd7_9_326 : subd7_9 [4, 1] = true := by decide +kernel
theorem subd7_9_327 : subd7_9 [4, 2] = true := by decide +kernel
theorem subd7_9_328 : subd7_9 [4, 3] = true := by decide +kernel
theorem subd7_9_329 : subd7_9 [4, 4] = true := by decide +kernel
theorem subd7_9_330 : subd7_9 [5, -4] = true := by decide +kernel
theorem subd7_9_331 : subd7_9 [5, -3] = true := by decide +kernel
theorem subd7_9_332 : subd7_9 [5, -2] = true := by decide +kernel
theorem subd7_9_333 : subd7_9 [5, -1] = true := by decide +kernel
theorem subd7_9_334 : subd7_9 [5, 0] = true := by decide +kernel
theorem subd7_9_335 : subd7_9 [5, 1] = true := by decide +kernel
theorem subd7_9_336 : subd7_9 [5, 2] = true := by decide +kernel
theorem subd7_9_337 : subd7_9 [5, 3] = true := by decide +kernel
theorem subd7_9_338 : subd7_9 [6] = true := by decide +kernel
theorem sbd7_9_10 : ∀ q ∈ blkd7_9_10, subd7_9 q = true := by
  unfold blkd7_9_10
  exact List.forall_mem_cons.2 ⟨subd7_9_320, List.forall_mem_cons.2 ⟨subd7_9_321, List.forall_mem_cons.2 ⟨subd7_9_322, List.forall_mem_cons.2 ⟨subd7_9_323, List.forall_mem_cons.2 ⟨subd7_9_324, List.forall_mem_cons.2 ⟨subd7_9_325, List.forall_mem_cons.2 ⟨subd7_9_326, List.forall_mem_cons.2 ⟨subd7_9_327, List.forall_mem_cons.2 ⟨subd7_9_328, List.forall_mem_cons.2 ⟨subd7_9_329, List.forall_mem_cons.2 ⟨subd7_9_330, List.forall_mem_cons.2 ⟨subd7_9_331, List.forall_mem_cons.2 ⟨subd7_9_332, List.forall_mem_cons.2 ⟨subd7_9_333, List.forall_mem_cons.2 ⟨subd7_9_334, List.forall_mem_cons.2 ⟨subd7_9_335, List.forall_mem_cons.2 ⟨subd7_9_336, List.forall_mem_cons.2 ⟨subd7_9_337, List.forall_mem_cons.2 ⟨subd7_9_338, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_10 : ldCheck G d7_10.U d7_10.ms ldd7_10 = true := by decide +kernel
theorem pre_okd7_10 : subPre G cell7 d7_10 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
