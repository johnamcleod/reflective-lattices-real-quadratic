import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_3_96 : subd8_3 [0, -1, -6] = true := by decide +kernel
theorem subd8_3_97 : subd8_3 [0, -1, -5] = true := by decide +kernel
theorem subd8_3_98 : subd8_3 [0, -1, -4] = true := by decide +kernel
theorem subd8_3_99 : subd8_3 [0, -1, -3] = true := by decide +kernel
theorem subd8_3_100 : subd8_3 [0, -1, -2] = true := by decide +kernel
theorem subd8_3_101 : subd8_3 [0, -1, -1] = true := by decide +kernel
theorem subd8_3_102 : subd8_3 [0, -1, 0] = true := by decide +kernel
theorem subd8_3_103 : subd8_3 [0, -1, 1] = true := by decide +kernel
theorem subd8_3_104 : subd8_3 [0, -1, 2] = true := by decide +kernel
theorem subd8_3_105 : subd8_3 [0, -1, 3] = true := by decide +kernel
theorem subd8_3_106 : subd8_3 [0, -1, 4] = true := by decide +kernel
theorem subd8_3_107 : subd8_3 [0, -1, 5] = true := by decide +kernel
theorem subd8_3_108 : subd8_3 [0, -1, 6] = true := by decide +kernel
theorem subd8_3_109 : subd8_3 [0, 0, -8] = true := by decide +kernel
theorem subd8_3_110 : subd8_3 [0, 0, -7] = true := by decide +kernel
theorem subd8_3_111 : subd8_3 [0, 0, -6] = true := by decide +kernel
theorem subd8_3_112 : subd8_3 [0, 0, -5] = true := by decide +kernel
theorem subd8_3_113 : subd8_3 [0, 0, -4] = true := by decide +kernel
theorem subd8_3_114 : subd8_3 [0, 0, -3] = true := by decide +kernel
theorem subd8_3_115 : subd8_3 [0, 0, -2] = true := by decide +kernel
theorem subd8_3_116 : subd8_3 [0, 0, -1] = true := by decide +kernel
theorem subd8_3_117 : subd8_3 [0, 0, 0] = true := by decide +kernel
theorem subd8_3_118 : subd8_3 [0, 0, 1] = true := by decide +kernel
theorem subd8_3_119 : subd8_3 [0, 0, 2] = true := by decide +kernel
theorem subd8_3_120 : subd8_3 [0, 0, 3] = true := by decide +kernel
theorem subd8_3_121 : subd8_3 [0, 0, 4] = true := by decide +kernel
theorem subd8_3_122 : subd8_3 [0, 0, 5] = true := by decide +kernel
theorem subd8_3_123 : subd8_3 [0, 0, 6] = true := by decide +kernel
theorem subd8_3_124 : subd8_3 [0, 0, 7] = true := by decide +kernel
theorem subd8_3_125 : subd8_3 [0, 1, -7] = true := by decide +kernel
theorem subd8_3_126 : subd8_3 [0, 1, -6] = true := by decide +kernel
theorem subd8_3_127 : subd8_3 [0, 1, -5] = true := by decide +kernel
theorem sbd8_3_3 : ∀ q ∈ blkd8_3_3, subd8_3 q = true := by
  unfold blkd8_3_3
  exact List.forall_mem_cons.2 ⟨subd8_3_96, List.forall_mem_cons.2 ⟨subd8_3_97, List.forall_mem_cons.2 ⟨subd8_3_98, List.forall_mem_cons.2 ⟨subd8_3_99, List.forall_mem_cons.2 ⟨subd8_3_100, List.forall_mem_cons.2 ⟨subd8_3_101, List.forall_mem_cons.2 ⟨subd8_3_102, List.forall_mem_cons.2 ⟨subd8_3_103, List.forall_mem_cons.2 ⟨subd8_3_104, List.forall_mem_cons.2 ⟨subd8_3_105, List.forall_mem_cons.2 ⟨subd8_3_106, List.forall_mem_cons.2 ⟨subd8_3_107, List.forall_mem_cons.2 ⟨subd8_3_108, List.forall_mem_cons.2 ⟨subd8_3_109, List.forall_mem_cons.2 ⟨subd8_3_110, List.forall_mem_cons.2 ⟨subd8_3_111, List.forall_mem_cons.2 ⟨subd8_3_112, List.forall_mem_cons.2 ⟨subd8_3_113, List.forall_mem_cons.2 ⟨subd8_3_114, List.forall_mem_cons.2 ⟨subd8_3_115, List.forall_mem_cons.2 ⟨subd8_3_116, List.forall_mem_cons.2 ⟨subd8_3_117, List.forall_mem_cons.2 ⟨subd8_3_118, List.forall_mem_cons.2 ⟨subd8_3_119, List.forall_mem_cons.2 ⟨subd8_3_120, List.forall_mem_cons.2 ⟨subd8_3_121, List.forall_mem_cons.2 ⟨subd8_3_122, List.forall_mem_cons.2 ⟨subd8_3_123, List.forall_mem_cons.2 ⟨subd8_3_124, List.forall_mem_cons.2 ⟨subd8_3_125, List.forall_mem_cons.2 ⟨subd8_3_126, List.forall_mem_cons.2 ⟨subd8_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_128 : subd8_3 [0, 1, -4] = true := by decide +kernel
theorem subd8_3_129 : subd8_3 [0, 1, -3] = true := by decide +kernel
theorem subd8_3_130 : subd8_3 [0, 1, -2] = true := by decide +kernel
theorem subd8_3_131 : subd8_3 [0, 1, -1] = true := by decide +kernel
theorem subd8_3_132 : subd8_3 [0, 1, 0] = true := by decide +kernel
theorem subd8_3_133 : subd8_3 [0, 1, 1] = true := by decide +kernel
theorem subd8_3_134 : subd8_3 [0, 1, 2] = true := by decide +kernel
theorem subd8_3_135 : subd8_3 [0, 1, 3] = true := by decide +kernel
theorem subd8_3_136 : subd8_3 [0, 1, 4] = true := by decide +kernel
theorem subd8_3_137 : subd8_3 [0, 1, 5] = true := by decide +kernel
theorem subd8_3_138 : subd8_3 [0, 1, 6] = true := by decide +kernel
theorem subd8_3_139 : subd8_3 [0, 1, 7] = true := by decide +kernel
theorem subd8_3_140 : subd8_3 [0, 2, -6] = true := by decide +kernel
theorem subd8_3_141 : subd8_3 [0, 2, -5] = true := by decide +kernel
theorem subd8_3_142 : subd8_3 [0, 2, -4] = true := by decide +kernel
theorem subd8_3_143 : subd8_3 [0, 2, -3] = true := by decide +kernel
theorem subd8_3_144 : subd8_3 [0, 2, -2] = true := by decide +kernel
theorem subd8_3_145 : subd8_3 [0, 2, -1] = true := by decide +kernel
theorem subd8_3_146 : subd8_3 [0, 2, 0] = true := by decide +kernel
theorem subd8_3_147 : subd8_3 [0, 2, 1] = true := by decide +kernel
theorem subd8_3_148 : subd8_3 [0, 2, 2] = true := by decide +kernel
theorem subd8_3_149 : subd8_3 [0, 2, 3] = true := by decide +kernel
theorem subd8_3_150 : subd8_3 [0, 2, 4] = true := by decide +kernel
theorem subd8_3_151 : subd8_3 [0, 2, 5] = true := by decide +kernel
theorem subd8_3_152 : subd8_3 [0, 2, 6] = true := by decide +kernel
theorem subd8_3_153 : subd8_3 [0, 2, 7] = true := by decide +kernel
theorem subd8_3_154 : subd8_3 [0, 3] = true := by decide +kernel
theorem subd8_3_155 : subd8_3 [1, -4] = true := by decide +kernel
theorem subd8_3_156 : subd8_3 [1, -3] = true := by decide +kernel
theorem subd8_3_157 : subd8_3 [1, -2] = true := by decide +kernel
theorem subd8_3_158 : subd8_3 [1, -1, -8] = true := by decide +kernel
theorem subd8_3_159 : subd8_3 [1, -1, -7] = true := by decide +kernel
theorem sbd8_3_4 : ∀ q ∈ blkd8_3_4, subd8_3 q = true := by
  unfold blkd8_3_4
  exact List.forall_mem_cons.2 ⟨subd8_3_128, List.forall_mem_cons.2 ⟨subd8_3_129, List.forall_mem_cons.2 ⟨subd8_3_130, List.forall_mem_cons.2 ⟨subd8_3_131, List.forall_mem_cons.2 ⟨subd8_3_132, List.forall_mem_cons.2 ⟨subd8_3_133, List.forall_mem_cons.2 ⟨subd8_3_134, List.forall_mem_cons.2 ⟨subd8_3_135, List.forall_mem_cons.2 ⟨subd8_3_136, List.forall_mem_cons.2 ⟨subd8_3_137, List.forall_mem_cons.2 ⟨subd8_3_138, List.forall_mem_cons.2 ⟨subd8_3_139, List.forall_mem_cons.2 ⟨subd8_3_140, List.forall_mem_cons.2 ⟨subd8_3_141, List.forall_mem_cons.2 ⟨subd8_3_142, List.forall_mem_cons.2 ⟨subd8_3_143, List.forall_mem_cons.2 ⟨subd8_3_144, List.forall_mem_cons.2 ⟨subd8_3_145, List.forall_mem_cons.2 ⟨subd8_3_146, List.forall_mem_cons.2 ⟨subd8_3_147, List.forall_mem_cons.2 ⟨subd8_3_148, List.forall_mem_cons.2 ⟨subd8_3_149, List.forall_mem_cons.2 ⟨subd8_3_150, List.forall_mem_cons.2 ⟨subd8_3_151, List.forall_mem_cons.2 ⟨subd8_3_152, List.forall_mem_cons.2 ⟨subd8_3_153, List.forall_mem_cons.2 ⟨subd8_3_154, List.forall_mem_cons.2 ⟨subd8_3_155, List.forall_mem_cons.2 ⟨subd8_3_156, List.forall_mem_cons.2 ⟨subd8_3_157, List.forall_mem_cons.2 ⟨subd8_3_158, List.forall_mem_cons.2 ⟨subd8_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_160 : subd8_3 [1, -1, -6] = true := by decide +kernel
theorem subd8_3_161 : subd8_3 [1, -1, -5] = true := by decide +kernel
theorem subd8_3_162 : subd8_3 [1, -1, -4] = true := by decide +kernel
theorem subd8_3_163 : subd8_3 [1, -1, -3] = true := by decide +kernel
theorem subd8_3_164 : subd8_3 [1, -1, -2] = true := by decide +kernel
theorem subd8_3_165 : subd8_3 [1, -1, -1] = true := by decide +kernel
theorem subd8_3_166 : subd8_3 [1, -1, 0] = true := by decide +kernel
theorem subd8_3_167 : subd8_3 [1, -1, 1] = true := by decide +kernel
theorem subd8_3_168 : subd8_3 [1, -1, 2] = true := by decide +kernel
theorem subd8_3_169 : subd8_3 [1, -1, 3] = true := by decide +kernel
theorem subd8_3_170 : subd8_3 [1, -1, 4] = true := by decide +kernel
theorem subd8_3_171 : subd8_3 [1, -1, 5] = true := by decide +kernel
theorem subd8_3_172 : subd8_3 [1, -1, 6] = true := by decide +kernel
theorem subd8_3_173 : subd8_3 [1, 0, -8] = true := by decide +kernel
theorem subd8_3_174 : subd8_3 [1, 0, -7] = true := by decide +kernel
theorem subd8_3_175 : subd8_3 [1, 0, -6] = true := by decide +kernel
theorem subd8_3_176 : subd8_3 [1, 0, -5] = true := by decide +kernel
theorem subd8_3_177 : subd8_3 [1, 0, -4] = true := by decide +kernel
theorem subd8_3_178 : subd8_3 [1, 0, -3] = true := by decide +kernel
theorem subd8_3_179 : subd8_3 [1, 0, -2] = true := by decide +kernel
theorem subd8_3_180 : subd8_3 [1, 0, -1] = true := by decide +kernel
theorem subd8_3_181 : subd8_3 [1, 0, 0] = true := by decide +kernel
theorem subd8_3_182 : subd8_3 [1, 0, 1] = true := by decide +kernel
theorem subd8_3_183 : subd8_3 [1, 0, 2] = true := by decide +kernel
theorem subd8_3_184 : subd8_3 [1, 0, 3] = true := by decide +kernel
theorem subd8_3_185 : subd8_3 [1, 0, 4] = true := by decide +kernel
theorem subd8_3_186 : subd8_3 [1, 0, 5] = true := by decide +kernel
theorem subd8_3_187 : subd8_3 [1, 0, 6] = true := by decide +kernel
theorem subd8_3_188 : subd8_3 [1, 0, 7] = true := by decide +kernel
theorem subd8_3_189 : subd8_3 [1, 1, -7] = true := by decide +kernel
theorem subd8_3_190 : subd8_3 [1, 1, -6] = true := by decide +kernel
theorem subd8_3_191 : subd8_3 [1, 1, -5] = true := by decide +kernel
theorem sbd8_3_5 : ∀ q ∈ blkd8_3_5, subd8_3 q = true := by
  unfold blkd8_3_5
  exact List.forall_mem_cons.2 ⟨subd8_3_160, List.forall_mem_cons.2 ⟨subd8_3_161, List.forall_mem_cons.2 ⟨subd8_3_162, List.forall_mem_cons.2 ⟨subd8_3_163, List.forall_mem_cons.2 ⟨subd8_3_164, List.forall_mem_cons.2 ⟨subd8_3_165, List.forall_mem_cons.2 ⟨subd8_3_166, List.forall_mem_cons.2 ⟨subd8_3_167, List.forall_mem_cons.2 ⟨subd8_3_168, List.forall_mem_cons.2 ⟨subd8_3_169, List.forall_mem_cons.2 ⟨subd8_3_170, List.forall_mem_cons.2 ⟨subd8_3_171, List.forall_mem_cons.2 ⟨subd8_3_172, List.forall_mem_cons.2 ⟨subd8_3_173, List.forall_mem_cons.2 ⟨subd8_3_174, List.forall_mem_cons.2 ⟨subd8_3_175, List.forall_mem_cons.2 ⟨subd8_3_176, List.forall_mem_cons.2 ⟨subd8_3_177, List.forall_mem_cons.2 ⟨subd8_3_178, List.forall_mem_cons.2 ⟨subd8_3_179, List.forall_mem_cons.2 ⟨subd8_3_180, List.forall_mem_cons.2 ⟨subd8_3_181, List.forall_mem_cons.2 ⟨subd8_3_182, List.forall_mem_cons.2 ⟨subd8_3_183, List.forall_mem_cons.2 ⟨subd8_3_184, List.forall_mem_cons.2 ⟨subd8_3_185, List.forall_mem_cons.2 ⟨subd8_3_186, List.forall_mem_cons.2 ⟨subd8_3_187, List.forall_mem_cons.2 ⟨subd8_3_188, List.forall_mem_cons.2 ⟨subd8_3_189, List.forall_mem_cons.2 ⟨subd8_3_190, List.forall_mem_cons.2 ⟨subd8_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_192 : subd8_3 [1, 1, -4] = true := by decide +kernel
theorem subd8_3_193 : subd8_3 [1, 1, -3] = true := by decide +kernel
theorem subd8_3_194 : subd8_3 [1, 1, -2] = true := by decide +kernel
theorem subd8_3_195 : subd8_3 [1, 1, -1] = true := by decide +kernel
theorem subd8_3_196 : subd8_3 [1, 1, 0] = true := by decide +kernel
theorem subd8_3_197 : subd8_3 [1, 1, 1] = true := by decide +kernel
theorem subd8_3_198 : subd8_3 [1, 1, 2] = true := by decide +kernel
theorem subd8_3_199 : subd8_3 [1, 1, 3] = true := by decide +kernel
theorem subd8_3_200 : subd8_3 [1, 1, 4] = true := by decide +kernel
theorem subd8_3_201 : subd8_3 [1, 1, 5] = true := by decide +kernel
theorem subd8_3_202 : subd8_3 [1, 1, 6] = true := by decide +kernel
theorem subd8_3_203 : subd8_3 [1, 1, 7] = true := by decide +kernel
theorem subd8_3_204 : subd8_3 [1, 2] = true := by decide +kernel
theorem subd8_3_205 : subd8_3 [1, 3] = true := by decide +kernel
theorem subd8_3_206 : subd8_3 [2, -4] = true := by decide +kernel
theorem subd8_3_207 : subd8_3 [2, -3] = true := by decide +kernel
theorem subd8_3_208 : subd8_3 [2, -2] = true := by decide +kernel
theorem subd8_3_209 : subd8_3 [2, -1] = true := by decide +kernel
theorem subd8_3_210 : subd8_3 [2, 0, -7] = true := by decide +kernel
theorem subd8_3_211 : subd8_3 [2, 0, -6] = true := by decide +kernel
theorem subd8_3_212 : subd8_3 [2, 0, -5] = true := by decide +kernel
theorem subd8_3_213 : subd8_3 [2, 0, -4] = true := by decide +kernel
theorem subd8_3_214 : subd8_3 [2, 0, -3] = true := by decide +kernel
theorem subd8_3_215 : subd8_3 [2, 0, -2] = true := by decide +kernel
theorem subd8_3_216 : subd8_3 [2, 0, -1] = true := by decide +kernel
theorem subd8_3_217 : subd8_3 [2, 0, 0] = true := by decide +kernel
theorem subd8_3_218 : subd8_3 [2, 0, 1] = true := by decide +kernel
theorem subd8_3_219 : subd8_3 [2, 0, 2] = true := by decide +kernel
theorem subd8_3_220 : subd8_3 [2, 0, 3] = true := by decide +kernel
theorem subd8_3_221 : subd8_3 [2, 0, 4] = true := by decide +kernel
theorem subd8_3_222 : subd8_3 [2, 0, 5] = true := by decide +kernel
theorem subd8_3_223 : subd8_3 [2, 0, 6] = true := by decide +kernel
theorem sbd8_3_6 : ∀ q ∈ blkd8_3_6, subd8_3 q = true := by
  unfold blkd8_3_6
  exact List.forall_mem_cons.2 ⟨subd8_3_192, List.forall_mem_cons.2 ⟨subd8_3_193, List.forall_mem_cons.2 ⟨subd8_3_194, List.forall_mem_cons.2 ⟨subd8_3_195, List.forall_mem_cons.2 ⟨subd8_3_196, List.forall_mem_cons.2 ⟨subd8_3_197, List.forall_mem_cons.2 ⟨subd8_3_198, List.forall_mem_cons.2 ⟨subd8_3_199, List.forall_mem_cons.2 ⟨subd8_3_200, List.forall_mem_cons.2 ⟨subd8_3_201, List.forall_mem_cons.2 ⟨subd8_3_202, List.forall_mem_cons.2 ⟨subd8_3_203, List.forall_mem_cons.2 ⟨subd8_3_204, List.forall_mem_cons.2 ⟨subd8_3_205, List.forall_mem_cons.2 ⟨subd8_3_206, List.forall_mem_cons.2 ⟨subd8_3_207, List.forall_mem_cons.2 ⟨subd8_3_208, List.forall_mem_cons.2 ⟨subd8_3_209, List.forall_mem_cons.2 ⟨subd8_3_210, List.forall_mem_cons.2 ⟨subd8_3_211, List.forall_mem_cons.2 ⟨subd8_3_212, List.forall_mem_cons.2 ⟨subd8_3_213, List.forall_mem_cons.2 ⟨subd8_3_214, List.forall_mem_cons.2 ⟨subd8_3_215, List.forall_mem_cons.2 ⟨subd8_3_216, List.forall_mem_cons.2 ⟨subd8_3_217, List.forall_mem_cons.2 ⟨subd8_3_218, List.forall_mem_cons.2 ⟨subd8_3_219, List.forall_mem_cons.2 ⟨subd8_3_220, List.forall_mem_cons.2 ⟨subd8_3_221, List.forall_mem_cons.2 ⟨subd8_3_222, List.forall_mem_cons.2 ⟨subd8_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_224 : subd8_3 [2, 1] = true := by decide +kernel
theorem subd8_3_225 : subd8_3 [2, 2] = true := by decide +kernel
theorem subd8_3_226 : subd8_3 [2, 3] = true := by decide +kernel
theorem subd8_3_227 : subd8_3 [3, -3] = true := by decide +kernel
theorem subd8_3_228 : subd8_3 [3, -2] = true := by decide +kernel
theorem subd8_3_229 : subd8_3 [3, -1] = true := by decide +kernel
theorem subd8_3_230 : subd8_3 [3, 0] = true := by decide +kernel
theorem subd8_3_231 : subd8_3 [3, 1] = true := by decide +kernel
theorem subd8_3_232 : subd8_3 [3, 2] = true := by decide +kernel
theorem sbd8_3_7 : ∀ q ∈ blkd8_3_7, subd8_3 q = true := by
  unfold blkd8_3_7
  exact List.forall_mem_cons.2 ⟨subd8_3_224, List.forall_mem_cons.2 ⟨subd8_3_225, List.forall_mem_cons.2 ⟨subd8_3_226, List.forall_mem_cons.2 ⟨subd8_3_227, List.forall_mem_cons.2 ⟨subd8_3_228, List.forall_mem_cons.2 ⟨subd8_3_229, List.forall_mem_cons.2 ⟨subd8_3_230, List.forall_mem_cons.2 ⟨subd8_3_231, List.forall_mem_cons.2 ⟨subd8_3_232, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_4 : ldCheck G d8_4.U d8_4.ms ldd8_4 = true := by decide +kernel
theorem pre_okd8_4 : subPre G cell8 d8_4 = true := by decide +kernel
theorem subd8_4_0 : subd8_4 [-2] = true := by decide +kernel
theorem subd8_4_1 : subd8_4 [-1, -3] = true := by decide +kernel
theorem subd8_4_2 : subd8_4 [-1, -2] = true := by decide +kernel
theorem subd8_4_3 : subd8_4 [-1, -1, -7] = true := by decide +kernel
theorem subd8_4_4 : subd8_4 [-1, -1, -6] = true := by decide +kernel
theorem subd8_4_5 : subd8_4 [-1, -1, -5] = true := by decide +kernel
theorem subd8_4_6 : subd8_4 [-1, -1, -4] = true := by decide +kernel
theorem subd8_4_7 : subd8_4 [-1, -1, -3] = true := by decide +kernel
theorem subd8_4_8 : subd8_4 [-1, -1, -2] = true := by decide +kernel
theorem subd8_4_9 : subd8_4 [-1, -1, -1] = true := by decide +kernel
theorem subd8_4_10 : subd8_4 [-1, -1, 0] = true := by decide +kernel
theorem subd8_4_11 : subd8_4 [-1, -1, 1] = true := by decide +kernel
theorem subd8_4_12 : subd8_4 [-1, -1, 2] = true := by decide +kernel
theorem subd8_4_13 : subd8_4 [-1, -1, 3] = true := by decide +kernel
theorem subd8_4_14 : subd8_4 [-1, -1, 4] = true := by decide +kernel
theorem subd8_4_15 : subd8_4 [-1, -1, 5] = true := by decide +kernel
theorem subd8_4_16 : subd8_4 [-1, -1, 6] = true := by decide +kernel
theorem subd8_4_17 : subd8_4 [-1, 0, -8] = true := by decide +kernel
theorem subd8_4_18 : subd8_4 [-1, 0, -7] = true := by decide +kernel
theorem subd8_4_19 : subd8_4 [-1, 0, -6] = true := by decide +kernel
theorem subd8_4_20 : subd8_4 [-1, 0, -5] = true := by decide +kernel
theorem subd8_4_21 : subd8_4 [-1, 0, -4] = true := by decide +kernel
theorem subd8_4_22 : subd8_4 [-1, 0, -3] = true := by decide +kernel
theorem subd8_4_23 : subd8_4 [-1, 0, -2] = true := by decide +kernel
theorem subd8_4_24 : subd8_4 [-1, 0, -1] = true := by decide +kernel
theorem subd8_4_25 : subd8_4 [-1, 0, 0] = true := by decide +kernel
theorem subd8_4_26 : subd8_4 [-1, 0, 1] = true := by decide +kernel
theorem subd8_4_27 : subd8_4 [-1, 0, 2] = true := by decide +kernel
theorem subd8_4_28 : subd8_4 [-1, 0, 3] = true := by decide +kernel
theorem subd8_4_29 : subd8_4 [-1, 0, 4] = true := by decide +kernel
theorem subd8_4_30 : subd8_4 [-1, 0, 5] = true := by decide +kernel
theorem subd8_4_31 : subd8_4 [-1, 0, 6] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_cons.2 ⟨subd8_4_1, List.forall_mem_cons.2 ⟨subd8_4_2, List.forall_mem_cons.2 ⟨subd8_4_3, List.forall_mem_cons.2 ⟨subd8_4_4, List.forall_mem_cons.2 ⟨subd8_4_5, List.forall_mem_cons.2 ⟨subd8_4_6, List.forall_mem_cons.2 ⟨subd8_4_7, List.forall_mem_cons.2 ⟨subd8_4_8, List.forall_mem_cons.2 ⟨subd8_4_9, List.forall_mem_cons.2 ⟨subd8_4_10, List.forall_mem_cons.2 ⟨subd8_4_11, List.forall_mem_cons.2 ⟨subd8_4_12, List.forall_mem_cons.2 ⟨subd8_4_13, List.forall_mem_cons.2 ⟨subd8_4_14, List.forall_mem_cons.2 ⟨subd8_4_15, List.forall_mem_cons.2 ⟨subd8_4_16, List.forall_mem_cons.2 ⟨subd8_4_17, List.forall_mem_cons.2 ⟨subd8_4_18, List.forall_mem_cons.2 ⟨subd8_4_19, List.forall_mem_cons.2 ⟨subd8_4_20, List.forall_mem_cons.2 ⟨subd8_4_21, List.forall_mem_cons.2 ⟨subd8_4_22, List.forall_mem_cons.2 ⟨subd8_4_23, List.forall_mem_cons.2 ⟨subd8_4_24, List.forall_mem_cons.2 ⟨subd8_4_25, List.forall_mem_cons.2 ⟨subd8_4_26, List.forall_mem_cons.2 ⟨subd8_4_27, List.forall_mem_cons.2 ⟨subd8_4_28, List.forall_mem_cons.2 ⟨subd8_4_29, List.forall_mem_cons.2 ⟨subd8_4_30, List.forall_mem_cons.2 ⟨subd8_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_32 : subd8_4 [-1, 1] = true := by decide +kernel
theorem subd8_4_33 : subd8_4 [-1, 2] = true := by decide +kernel
theorem subd8_4_34 : subd8_4 [0, -3] = true := by decide +kernel
theorem subd8_4_35 : subd8_4 [0, -2] = true := by decide +kernel
theorem subd8_4_36 : subd8_4 [0, -1, -7] = true := by decide +kernel
theorem subd8_4_37 : subd8_4 [0, -1, -6] = true := by decide +kernel
theorem subd8_4_38 : subd8_4 [0, -1, -5] = true := by decide +kernel
theorem subd8_4_39 : subd8_4 [0, -1, -4] = true := by decide +kernel
theorem subd8_4_40 : subd8_4 [0, -1, -3] = true := by decide +kernel
theorem subd8_4_41 : subd8_4 [0, -1, -2] = true := by decide +kernel
theorem subd8_4_42 : subd8_4 [0, -1, -1] = true := by decide +kernel
theorem subd8_4_43 : subd8_4 [0, -1, 0] = true := by decide +kernel
theorem subd8_4_44 : subd8_4 [0, -1, 1] = true := by decide +kernel
theorem subd8_4_45 : subd8_4 [0, -1, 2] = true := by decide +kernel
theorem subd8_4_46 : subd8_4 [0, -1, 3] = true := by decide +kernel
theorem subd8_4_47 : subd8_4 [0, -1, 4] = true := by decide +kernel
theorem subd8_4_48 : subd8_4 [0, -1, 5] = true := by decide +kernel
theorem subd8_4_49 : subd8_4 [0, -1, 6] = true := by decide +kernel
theorem subd8_4_50 : subd8_4 [0, -1, 7] = true := by decide +kernel
theorem subd8_4_51 : subd8_4 [0, 0, -8] = true := by decide +kernel
theorem subd8_4_52 : subd8_4 [0, 0, -7] = true := by decide +kernel
theorem subd8_4_53 : subd8_4 [0, 0, -6] = true := by decide +kernel
theorem subd8_4_54 : subd8_4 [0, 0, -5] = true := by decide +kernel
theorem subd8_4_55 : subd8_4 [0, 0, -4] = true := by decide +kernel
theorem subd8_4_56 : subd8_4 [0, 0, -3] = true := by decide +kernel
theorem subd8_4_57 : subd8_4 [0, 0, -2] = true := by decide +kernel
theorem subd8_4_58 : subd8_4 [0, 0, -1] = true := by decide +kernel
theorem subd8_4_59 : subd8_4 [0, 0, 0] = true := by decide +kernel
theorem subd8_4_60 : subd8_4 [0, 0, 1] = true := by decide +kernel
theorem subd8_4_61 : subd8_4 [0, 0, 2] = true := by decide +kernel
theorem subd8_4_62 : subd8_4 [0, 0, 3] = true := by decide +kernel
theorem subd8_4_63 : subd8_4 [0, 0, 4] = true := by decide +kernel
theorem sbd8_4_1 : ∀ q ∈ blkd8_4_1, subd8_4 q = true := by
  unfold blkd8_4_1
  exact List.forall_mem_cons.2 ⟨subd8_4_32, List.forall_mem_cons.2 ⟨subd8_4_33, List.forall_mem_cons.2 ⟨subd8_4_34, List.forall_mem_cons.2 ⟨subd8_4_35, List.forall_mem_cons.2 ⟨subd8_4_36, List.forall_mem_cons.2 ⟨subd8_4_37, List.forall_mem_cons.2 ⟨subd8_4_38, List.forall_mem_cons.2 ⟨subd8_4_39, List.forall_mem_cons.2 ⟨subd8_4_40, List.forall_mem_cons.2 ⟨subd8_4_41, List.forall_mem_cons.2 ⟨subd8_4_42, List.forall_mem_cons.2 ⟨subd8_4_43, List.forall_mem_cons.2 ⟨subd8_4_44, List.forall_mem_cons.2 ⟨subd8_4_45, List.forall_mem_cons.2 ⟨subd8_4_46, List.forall_mem_cons.2 ⟨subd8_4_47, List.forall_mem_cons.2 ⟨subd8_4_48, List.forall_mem_cons.2 ⟨subd8_4_49, List.forall_mem_cons.2 ⟨subd8_4_50, List.forall_mem_cons.2 ⟨subd8_4_51, List.forall_mem_cons.2 ⟨subd8_4_52, List.forall_mem_cons.2 ⟨subd8_4_53, List.forall_mem_cons.2 ⟨subd8_4_54, List.forall_mem_cons.2 ⟨subd8_4_55, List.forall_mem_cons.2 ⟨subd8_4_56, List.forall_mem_cons.2 ⟨subd8_4_57, List.forall_mem_cons.2 ⟨subd8_4_58, List.forall_mem_cons.2 ⟨subd8_4_59, List.forall_mem_cons.2 ⟨subd8_4_60, List.forall_mem_cons.2 ⟨subd8_4_61, List.forall_mem_cons.2 ⟨subd8_4_62, List.forall_mem_cons.2 ⟨subd8_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_64 : subd8_4 [0, 0, 5] = true := by decide +kernel
theorem subd8_4_65 : subd8_4 [0, 0, 6] = true := by decide +kernel
theorem subd8_4_66 : subd8_4 [0, 0, 7] = true := by decide +kernel
theorem subd8_4_67 : subd8_4 [0, 1, -8] = true := by decide +kernel
theorem subd8_4_68 : subd8_4 [0, 1, -7] = true := by decide +kernel
theorem subd8_4_69 : subd8_4 [0, 1, -6] = true := by decide +kernel
theorem subd8_4_70 : subd8_4 [0, 1, -5] = true := by decide +kernel
theorem subd8_4_71 : subd8_4 [0, 1, -4] = true := by decide +kernel
theorem subd8_4_72 : subd8_4 [0, 1, -3] = true := by decide +kernel
theorem subd8_4_73 : subd8_4 [0, 1, -2] = true := by decide +kernel
theorem subd8_4_74 : subd8_4 [0, 1, -1] = true := by decide +kernel
theorem subd8_4_75 : subd8_4 [0, 1, 0] = true := by decide +kernel
theorem subd8_4_76 : subd8_4 [0, 1, 1] = true := by decide +kernel
theorem subd8_4_77 : subd8_4 [0, 1, 2] = true := by decide +kernel
theorem subd8_4_78 : subd8_4 [0, 1, 3] = true := by decide +kernel
theorem subd8_4_79 : subd8_4 [0, 1, 4] = true := by decide +kernel
theorem subd8_4_80 : subd8_4 [0, 1, 5] = true := by decide +kernel
theorem subd8_4_81 : subd8_4 [0, 1, 6] = true := by decide +kernel
theorem subd8_4_82 : subd8_4 [0, 2] = true := by decide +kernel
theorem subd8_4_83 : subd8_4 [1, -3] = true := by decide +kernel
theorem subd8_4_84 : subd8_4 [1, -2] = true := by decide +kernel
theorem subd8_4_85 : subd8_4 [1, -1] = true := by decide +kernel
theorem subd8_4_86 : subd8_4 [1, 0, -7] = true := by decide +kernel
theorem subd8_4_87 : subd8_4 [1, 0, -6] = true := by decide +kernel
theorem subd8_4_88 : subd8_4 [1, 0, -5] = true := by decide +kernel
theorem subd8_4_89 : subd8_4 [1, 0, -4] = true := by decide +kernel
theorem subd8_4_90 : subd8_4 [1, 0, -3] = true := by decide +kernel
theorem subd8_4_91 : subd8_4 [1, 0, -2] = true := by decide +kernel
theorem subd8_4_92 : subd8_4 [1, 0, -1] = true := by decide +kernel
theorem subd8_4_93 : subd8_4 [1, 0, 0] = true := by decide +kernel
theorem subd8_4_94 : subd8_4 [1, 0, 1] = true := by decide +kernel
theorem subd8_4_95 : subd8_4 [1, 0, 2] = true := by decide +kernel
theorem sbd8_4_2 : ∀ q ∈ blkd8_4_2, subd8_4 q = true := by
  unfold blkd8_4_2
  exact List.forall_mem_cons.2 ⟨subd8_4_64, List.forall_mem_cons.2 ⟨subd8_4_65, List.forall_mem_cons.2 ⟨subd8_4_66, List.forall_mem_cons.2 ⟨subd8_4_67, List.forall_mem_cons.2 ⟨subd8_4_68, List.forall_mem_cons.2 ⟨subd8_4_69, List.forall_mem_cons.2 ⟨subd8_4_70, List.forall_mem_cons.2 ⟨subd8_4_71, List.forall_mem_cons.2 ⟨subd8_4_72, List.forall_mem_cons.2 ⟨subd8_4_73, List.forall_mem_cons.2 ⟨subd8_4_74, List.forall_mem_cons.2 ⟨subd8_4_75, List.forall_mem_cons.2 ⟨subd8_4_76, List.forall_mem_cons.2 ⟨subd8_4_77, List.forall_mem_cons.2 ⟨subd8_4_78, List.forall_mem_cons.2 ⟨subd8_4_79, List.forall_mem_cons.2 ⟨subd8_4_80, List.forall_mem_cons.2 ⟨subd8_4_81, List.forall_mem_cons.2 ⟨subd8_4_82, List.forall_mem_cons.2 ⟨subd8_4_83, List.forall_mem_cons.2 ⟨subd8_4_84, List.forall_mem_cons.2 ⟨subd8_4_85, List.forall_mem_cons.2 ⟨subd8_4_86, List.forall_mem_cons.2 ⟨subd8_4_87, List.forall_mem_cons.2 ⟨subd8_4_88, List.forall_mem_cons.2 ⟨subd8_4_89, List.forall_mem_cons.2 ⟨subd8_4_90, List.forall_mem_cons.2 ⟨subd8_4_91, List.forall_mem_cons.2 ⟨subd8_4_92, List.forall_mem_cons.2 ⟨subd8_4_93, List.forall_mem_cons.2 ⟨subd8_4_94, List.forall_mem_cons.2 ⟨subd8_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_96 : subd8_4 [1, 0, 3] = true := by decide +kernel
theorem subd8_4_97 : subd8_4 [1, 0, 4] = true := by decide +kernel
theorem subd8_4_98 : subd8_4 [1, 0, 5] = true := by decide +kernel
theorem subd8_4_99 : subd8_4 [1, 0, 6] = true := by decide +kernel
theorem subd8_4_100 : subd8_4 [1, 0, 7] = true := by decide +kernel
theorem subd8_4_101 : subd8_4 [1, 1, -7] = true := by decide +kernel
theorem subd8_4_102 : subd8_4 [1, 1, -6] = true := by decide +kernel
theorem subd8_4_103 : subd8_4 [1, 1, -5] = true := by decide +kernel
theorem subd8_4_104 : subd8_4 [1, 1, -4] = true := by decide +kernel
theorem subd8_4_105 : subd8_4 [1, 1, -3] = true := by decide +kernel
theorem subd8_4_106 : subd8_4 [1, 1, -2] = true := by decide +kernel
theorem subd8_4_107 : subd8_4 [1, 1, -1] = true := by decide +kernel
theorem subd8_4_108 : subd8_4 [1, 1, 0] = true := by decide +kernel
theorem subd8_4_109 : subd8_4 [1, 1, 1] = true := by decide +kernel
theorem subd8_4_110 : subd8_4 [1, 1, 2] = true := by decide +kernel
theorem subd8_4_111 : subd8_4 [1, 1, 3] = true := by decide +kernel
theorem subd8_4_112 : subd8_4 [1, 1, 4] = true := by decide +kernel
theorem subd8_4_113 : subd8_4 [1, 1, 5] = true := by decide +kernel
theorem subd8_4_114 : subd8_4 [1, 1, 6] = true := by decide +kernel
theorem subd8_4_115 : subd8_4 [1, 2] = true := by decide +kernel
theorem subd8_4_116 : subd8_4 [2] = true := by decide +kernel
theorem sbd8_4_3 : ∀ q ∈ blkd8_4_3, subd8_4 q = true := by
  unfold blkd8_4_3
  exact List.forall_mem_cons.2 ⟨subd8_4_96, List.forall_mem_cons.2 ⟨subd8_4_97, List.forall_mem_cons.2 ⟨subd8_4_98, List.forall_mem_cons.2 ⟨subd8_4_99, List.forall_mem_cons.2 ⟨subd8_4_100, List.forall_mem_cons.2 ⟨subd8_4_101, List.forall_mem_cons.2 ⟨subd8_4_102, List.forall_mem_cons.2 ⟨subd8_4_103, List.forall_mem_cons.2 ⟨subd8_4_104, List.forall_mem_cons.2 ⟨subd8_4_105, List.forall_mem_cons.2 ⟨subd8_4_106, List.forall_mem_cons.2 ⟨subd8_4_107, List.forall_mem_cons.2 ⟨subd8_4_108, List.forall_mem_cons.2 ⟨subd8_4_109, List.forall_mem_cons.2 ⟨subd8_4_110, List.forall_mem_cons.2 ⟨subd8_4_111, List.forall_mem_cons.2 ⟨subd8_4_112, List.forall_mem_cons.2 ⟨subd8_4_113, List.forall_mem_cons.2 ⟨subd8_4_114, List.forall_mem_cons.2 ⟨subd8_4_115, List.forall_mem_cons.2 ⟨subd8_4_116, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_5 : ldCheck G d8_5.U d8_5.ms ldd8_5 = true := by decide +kernel
theorem pre_okd8_5 : subPre G cell8 d8_5 = true := by decide +kernel
theorem subd8_5_0 : subd8_5 [-2] = true := by decide +kernel
theorem subd8_5_1 : subd8_5 [-1] = true := by decide +kernel
theorem subd8_5_2 : subd8_5 [0, -3] = true := by decide +kernel
theorem subd8_5_3 : subd8_5 [0, -2] = true := by decide +kernel
theorem subd8_5_4 : subd8_5 [0, -1] = true := by decide +kernel
theorem subd8_5_5 : subd8_5 [0, 0] = true := by decide +kernel
theorem subd8_5_6 : subd8_5 [0, 1] = true := by decide +kernel
theorem subd8_5_7 : subd8_5 [0, 2] = true := by decide +kernel
theorem subd8_5_8 : subd8_5 [1] = true := by decide +kernel
theorem subd8_5_9 : subd8_5 [2] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_cons.2 ⟨subd8_5_1, List.forall_mem_cons.2 ⟨subd8_5_2, List.forall_mem_cons.2 ⟨subd8_5_3, List.forall_mem_cons.2 ⟨subd8_5_4, List.forall_mem_cons.2 ⟨subd8_5_5, List.forall_mem_cons.2 ⟨subd8_5_6, List.forall_mem_cons.2 ⟨subd8_5_7, List.forall_mem_cons.2 ⟨subd8_5_8, List.forall_mem_cons.2 ⟨subd8_5_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C140
