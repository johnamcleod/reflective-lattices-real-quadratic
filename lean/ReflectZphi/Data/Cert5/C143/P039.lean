import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd16_1_96 : subd16_1 [-2, 2, 0] = true := by decide +kernel
theorem subd16_1_97 : subd16_1 [-2, 2, 1] = true := by decide +kernel
theorem subd16_1_98 : subd16_1 [-2, 2, 2] = true := by decide +kernel
theorem subd16_1_99 : subd16_1 [-2, 2, 3] = true := by decide +kernel
theorem subd16_1_100 : subd16_1 [-2, 2, 4] = true := by decide +kernel
theorem subd16_1_101 : subd16_1 [-2, 2, 5] = true := by decide +kernel
theorem subd16_1_102 : subd16_1 [-2, 2, 6] = true := by decide +kernel
theorem subd16_1_103 : subd16_1 [-2, 3] = true := by decide +kernel
theorem subd16_1_104 : subd16_1 [-2, 4] = true := by decide +kernel
theorem subd16_1_105 : subd16_1 [-2, 5] = true := by decide +kernel
theorem subd16_1_106 : subd16_1 [-2, 6] = true := by decide +kernel
theorem subd16_1_107 : subd16_1 [-1, -6] = true := by decide +kernel
theorem subd16_1_108 : subd16_1 [-1, -5] = true := by decide +kernel
theorem subd16_1_109 : subd16_1 [-1, -4] = true := by decide +kernel
theorem subd16_1_110 : subd16_1 [-1, -3] = true := by decide +kernel
theorem subd16_1_111 : subd16_1 [-1, -2] = true := by decide +kernel
theorem subd16_1_112 : subd16_1 [-1, -1, -7] = true := by decide +kernel
theorem subd16_1_113 : subd16_1 [-1, -1, -6] = true := by decide +kernel
theorem subd16_1_114 : subd16_1 [-1, -1, -5] = true := by decide +kernel
theorem subd16_1_115 : subd16_1 [-1, -1, -4] = true := by decide +kernel
theorem subd16_1_116 : subd16_1 [-1, -1, -3] = true := by decide +kernel
theorem subd16_1_117 : subd16_1 [-1, -1, -2] = true := by decide +kernel
theorem subd16_1_118 : subd16_1 [-1, -1, -1] = true := by decide +kernel
theorem subd16_1_119 : subd16_1 [-1, -1, 0] = true := by decide +kernel
theorem subd16_1_120 : subd16_1 [-1, -1, 1] = true := by decide +kernel
theorem subd16_1_121 : subd16_1 [-1, -1, 2] = true := by decide +kernel
theorem subd16_1_122 : subd16_1 [-1, -1, 3] = true := by decide +kernel
theorem subd16_1_123 : subd16_1 [-1, -1, 4] = true := by decide +kernel
theorem subd16_1_124 : subd16_1 [-1, -1, 5] = true := by decide +kernel
theorem subd16_1_125 : subd16_1 [-1, -1, 6] = true := by decide +kernel
theorem subd16_1_126 : subd16_1 [-1, 0, -7] = true := by decide +kernel
theorem subd16_1_127 : subd16_1 [-1, 0, -6] = true := by decide +kernel
theorem sbd16_1_3 : ∀ q ∈ blkd16_1_3, subd16_1 q = true := by
  unfold blkd16_1_3
  exact List.forall_mem_cons.2 ⟨subd16_1_96, List.forall_mem_cons.2 ⟨subd16_1_97, List.forall_mem_cons.2 ⟨subd16_1_98, List.forall_mem_cons.2 ⟨subd16_1_99, List.forall_mem_cons.2 ⟨subd16_1_100, List.forall_mem_cons.2 ⟨subd16_1_101, List.forall_mem_cons.2 ⟨subd16_1_102, List.forall_mem_cons.2 ⟨subd16_1_103, List.forall_mem_cons.2 ⟨subd16_1_104, List.forall_mem_cons.2 ⟨subd16_1_105, List.forall_mem_cons.2 ⟨subd16_1_106, List.forall_mem_cons.2 ⟨subd16_1_107, List.forall_mem_cons.2 ⟨subd16_1_108, List.forall_mem_cons.2 ⟨subd16_1_109, List.forall_mem_cons.2 ⟨subd16_1_110, List.forall_mem_cons.2 ⟨subd16_1_111, List.forall_mem_cons.2 ⟨subd16_1_112, List.forall_mem_cons.2 ⟨subd16_1_113, List.forall_mem_cons.2 ⟨subd16_1_114, List.forall_mem_cons.2 ⟨subd16_1_115, List.forall_mem_cons.2 ⟨subd16_1_116, List.forall_mem_cons.2 ⟨subd16_1_117, List.forall_mem_cons.2 ⟨subd16_1_118, List.forall_mem_cons.2 ⟨subd16_1_119, List.forall_mem_cons.2 ⟨subd16_1_120, List.forall_mem_cons.2 ⟨subd16_1_121, List.forall_mem_cons.2 ⟨subd16_1_122, List.forall_mem_cons.2 ⟨subd16_1_123, List.forall_mem_cons.2 ⟨subd16_1_124, List.forall_mem_cons.2 ⟨subd16_1_125, List.forall_mem_cons.2 ⟨subd16_1_126, List.forall_mem_cons.2 ⟨subd16_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_128 : subd16_1 [-1, 0, -5] = true := by decide +kernel
theorem subd16_1_129 : subd16_1 [-1, 0, -4] = true := by decide +kernel
theorem subd16_1_130 : subd16_1 [-1, 0, -3] = true := by decide +kernel
theorem subd16_1_131 : subd16_1 [-1, 0, -2] = true := by decide +kernel
theorem subd16_1_132 : subd16_1 [-1, 0, -1] = true := by decide +kernel
theorem subd16_1_133 : subd16_1 [-1, 0, 0] = true := by decide +kernel
theorem subd16_1_134 : subd16_1 [-1, 0, 1] = true := by decide +kernel
theorem subd16_1_135 : subd16_1 [-1, 0, 2] = true := by decide +kernel
theorem subd16_1_136 : subd16_1 [-1, 0, 3] = true := by decide +kernel
theorem subd16_1_137 : subd16_1 [-1, 0, 4] = true := by decide +kernel
theorem subd16_1_138 : subd16_1 [-1, 0, 5] = true := by decide +kernel
theorem subd16_1_139 : subd16_1 [-1, 0, 6] = true := by decide +kernel
theorem subd16_1_140 : subd16_1 [-1, 1, -7] = true := by decide +kernel
theorem subd16_1_141 : subd16_1 [-1, 1, -6] = true := by decide +kernel
theorem subd16_1_142 : subd16_1 [-1, 1, -5] = true := by decide +kernel
theorem subd16_1_143 : subd16_1 [-1, 1, -4] = true := by decide +kernel
theorem subd16_1_144 : subd16_1 [-1, 1, -3] = true := by decide +kernel
theorem subd16_1_145 : subd16_1 [-1, 1, -2] = true := by decide +kernel
theorem subd16_1_146 : subd16_1 [-1, 1, -1] = true := by decide +kernel
theorem subd16_1_147 : subd16_1 [-1, 1, 0] = true := by decide +kernel
theorem subd16_1_148 : subd16_1 [-1, 1, 1] = true := by decide +kernel
theorem subd16_1_149 : subd16_1 [-1, 1, 2] = true := by decide +kernel
theorem subd16_1_150 : subd16_1 [-1, 1, 3] = true := by decide +kernel
theorem subd16_1_151 : subd16_1 [-1, 1, 4] = true := by decide +kernel
theorem subd16_1_152 : subd16_1 [-1, 1, 5] = true := by decide +kernel
theorem subd16_1_153 : subd16_1 [-1, 1, 6] = true := by decide +kernel
theorem subd16_1_154 : subd16_1 [-1, 2, -7] = true := by decide +kernel
theorem subd16_1_155 : subd16_1 [-1, 2, -6] = true := by decide +kernel
theorem subd16_1_156 : subd16_1 [-1, 2, -5] = true := by decide +kernel
theorem subd16_1_157 : subd16_1 [-1, 2, -4] = true := by decide +kernel
theorem subd16_1_158 : subd16_1 [-1, 2, -3] = true := by decide +kernel
theorem subd16_1_159 : subd16_1 [-1, 2, -2] = true := by decide +kernel
theorem sbd16_1_4 : ∀ q ∈ blkd16_1_4, subd16_1 q = true := by
  unfold blkd16_1_4
  exact List.forall_mem_cons.2 ⟨subd16_1_128, List.forall_mem_cons.2 ⟨subd16_1_129, List.forall_mem_cons.2 ⟨subd16_1_130, List.forall_mem_cons.2 ⟨subd16_1_131, List.forall_mem_cons.2 ⟨subd16_1_132, List.forall_mem_cons.2 ⟨subd16_1_133, List.forall_mem_cons.2 ⟨subd16_1_134, List.forall_mem_cons.2 ⟨subd16_1_135, List.forall_mem_cons.2 ⟨subd16_1_136, List.forall_mem_cons.2 ⟨subd16_1_137, List.forall_mem_cons.2 ⟨subd16_1_138, List.forall_mem_cons.2 ⟨subd16_1_139, List.forall_mem_cons.2 ⟨subd16_1_140, List.forall_mem_cons.2 ⟨subd16_1_141, List.forall_mem_cons.2 ⟨subd16_1_142, List.forall_mem_cons.2 ⟨subd16_1_143, List.forall_mem_cons.2 ⟨subd16_1_144, List.forall_mem_cons.2 ⟨subd16_1_145, List.forall_mem_cons.2 ⟨subd16_1_146, List.forall_mem_cons.2 ⟨subd16_1_147, List.forall_mem_cons.2 ⟨subd16_1_148, List.forall_mem_cons.2 ⟨subd16_1_149, List.forall_mem_cons.2 ⟨subd16_1_150, List.forall_mem_cons.2 ⟨subd16_1_151, List.forall_mem_cons.2 ⟨subd16_1_152, List.forall_mem_cons.2 ⟨subd16_1_153, List.forall_mem_cons.2 ⟨subd16_1_154, List.forall_mem_cons.2 ⟨subd16_1_155, List.forall_mem_cons.2 ⟨subd16_1_156, List.forall_mem_cons.2 ⟨subd16_1_157, List.forall_mem_cons.2 ⟨subd16_1_158, List.forall_mem_cons.2 ⟨subd16_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_160 : subd16_1 [-1, 2, -1] = true := by decide +kernel
theorem subd16_1_161 : subd16_1 [-1, 2, 0] = true := by decide +kernel
theorem subd16_1_162 : subd16_1 [-1, 2, 1] = true := by decide +kernel
theorem subd16_1_163 : subd16_1 [-1, 2, 2] = true := by decide +kernel
theorem subd16_1_164 : subd16_1 [-1, 2, 3] = true := by decide +kernel
theorem subd16_1_165 : subd16_1 [-1, 2, 4] = true := by decide +kernel
theorem subd16_1_166 : subd16_1 [-1, 2, 5] = true := by decide +kernel
theorem subd16_1_167 : subd16_1 [-1, 2, 6] = true := by decide +kernel
theorem subd16_1_168 : subd16_1 [-1, 3] = true := by decide +kernel
theorem subd16_1_169 : subd16_1 [-1, 4] = true := by decide +kernel
theorem subd16_1_170 : subd16_1 [-1, 5] = true := by decide +kernel
theorem subd16_1_171 : subd16_1 [-1, 6] = true := by decide +kernel
theorem subd16_1_172 : subd16_1 [0, -7] = true := by decide +kernel
theorem subd16_1_173 : subd16_1 [0, -6] = true := by decide +kernel
theorem subd16_1_174 : subd16_1 [0, -5] = true := by decide +kernel
theorem subd16_1_175 : subd16_1 [0, -4] = true := by decide +kernel
theorem subd16_1_176 : subd16_1 [0, -3] = true := by decide +kernel
theorem subd16_1_177 : subd16_1 [0, -2, -7] = true := by decide +kernel
theorem subd16_1_178 : subd16_1 [0, -2, -6] = true := by decide +kernel
theorem subd16_1_179 : subd16_1 [0, -2, -5] = true := by decide +kernel
theorem subd16_1_180 : subd16_1 [0, -2, -4] = true := by decide +kernel
theorem subd16_1_181 : subd16_1 [0, -2, -3] = true := by decide +kernel
theorem subd16_1_182 : subd16_1 [0, -2, -2] = true := by decide +kernel
theorem subd16_1_183 : subd16_1 [0, -2, -1] = true := by decide +kernel
theorem subd16_1_184 : subd16_1 [0, -2, 0] = true := by decide +kernel
theorem subd16_1_185 : subd16_1 [0, -2, 1] = true := by decide +kernel
theorem subd16_1_186 : subd16_1 [0, -2, 2] = true := by decide +kernel
theorem subd16_1_187 : subd16_1 [0, -2, 3] = true := by decide +kernel
theorem subd16_1_188 : subd16_1 [0, -2, 4] = true := by decide +kernel
theorem subd16_1_189 : subd16_1 [0, -2, 5] = true := by decide +kernel
theorem subd16_1_190 : subd16_1 [0, -2, 6] = true := by decide +kernel
theorem subd16_1_191 : subd16_1 [0, -1, -7] = true := by decide +kernel
theorem sbd16_1_5 : ∀ q ∈ blkd16_1_5, subd16_1 q = true := by
  unfold blkd16_1_5
  exact List.forall_mem_cons.2 ⟨subd16_1_160, List.forall_mem_cons.2 ⟨subd16_1_161, List.forall_mem_cons.2 ⟨subd16_1_162, List.forall_mem_cons.2 ⟨subd16_1_163, List.forall_mem_cons.2 ⟨subd16_1_164, List.forall_mem_cons.2 ⟨subd16_1_165, List.forall_mem_cons.2 ⟨subd16_1_166, List.forall_mem_cons.2 ⟨subd16_1_167, List.forall_mem_cons.2 ⟨subd16_1_168, List.forall_mem_cons.2 ⟨subd16_1_169, List.forall_mem_cons.2 ⟨subd16_1_170, List.forall_mem_cons.2 ⟨subd16_1_171, List.forall_mem_cons.2 ⟨subd16_1_172, List.forall_mem_cons.2 ⟨subd16_1_173, List.forall_mem_cons.2 ⟨subd16_1_174, List.forall_mem_cons.2 ⟨subd16_1_175, List.forall_mem_cons.2 ⟨subd16_1_176, List.forall_mem_cons.2 ⟨subd16_1_177, List.forall_mem_cons.2 ⟨subd16_1_178, List.forall_mem_cons.2 ⟨subd16_1_179, List.forall_mem_cons.2 ⟨subd16_1_180, List.forall_mem_cons.2 ⟨subd16_1_181, List.forall_mem_cons.2 ⟨subd16_1_182, List.forall_mem_cons.2 ⟨subd16_1_183, List.forall_mem_cons.2 ⟨subd16_1_184, List.forall_mem_cons.2 ⟨subd16_1_185, List.forall_mem_cons.2 ⟨subd16_1_186, List.forall_mem_cons.2 ⟨subd16_1_187, List.forall_mem_cons.2 ⟨subd16_1_188, List.forall_mem_cons.2 ⟨subd16_1_189, List.forall_mem_cons.2 ⟨subd16_1_190, List.forall_mem_cons.2 ⟨subd16_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_192 : subd16_1 [0, -1, -6] = true := by decide +kernel
theorem subd16_1_193 : subd16_1 [0, -1, -5] = true := by decide +kernel
theorem subd16_1_194 : subd16_1 [0, -1, -4] = true := by decide +kernel
theorem subd16_1_195 : subd16_1 [0, -1, -3] = true := by decide +kernel
theorem subd16_1_196 : subd16_1 [0, -1, -2] = true := by decide +kernel
theorem subd16_1_197 : subd16_1 [0, -1, -1] = true := by decide +kernel
theorem subd16_1_198 : subd16_1 [0, -1, 0] = true := by decide +kernel
theorem subd16_1_199 : subd16_1 [0, -1, 1] = true := by decide +kernel
theorem subd16_1_200 : subd16_1 [0, -1, 2] = true := by decide +kernel
theorem subd16_1_201 : subd16_1 [0, -1, 3] = true := by decide +kernel
theorem subd16_1_202 : subd16_1 [0, -1, 4] = true := by decide +kernel
theorem subd16_1_203 : subd16_1 [0, -1, 5] = true := by decide +kernel
theorem subd16_1_204 : subd16_1 [0, -1, 6] = true := by decide +kernel
theorem subd16_1_205 : subd16_1 [0, 0, -7] = true := by decide +kernel
theorem subd16_1_206 : subd16_1 [0, 0, -6] = true := by decide +kernel
theorem subd16_1_207 : subd16_1 [0, 0, -5] = true := by decide +kernel
theorem subd16_1_208 : subd16_1 [0, 0, -4] = true := by decide +kernel
theorem subd16_1_209 : subd16_1 [0, 0, -3] = true := by decide +kernel
theorem subd16_1_210 : subd16_1 [0, 0, -2] = true := by decide +kernel
theorem subd16_1_211 : subd16_1 [0, 0, -1] = true := by decide +kernel
theorem subd16_1_212 : subd16_1 [0, 0, 0] = true := by decide +kernel
theorem subd16_1_213 : subd16_1 [0, 0, 1] = true := by decide +kernel
theorem subd16_1_214 : subd16_1 [0, 0, 2] = true := by decide +kernel
theorem subd16_1_215 : subd16_1 [0, 0, 3] = true := by decide +kernel
theorem subd16_1_216 : subd16_1 [0, 0, 4] = true := by decide +kernel
theorem subd16_1_217 : subd16_1 [0, 0, 5] = true := by decide +kernel
theorem subd16_1_218 : subd16_1 [0, 0, 6] = true := by decide +kernel
theorem subd16_1_219 : subd16_1 [0, 1, -7] = true := by decide +kernel
theorem subd16_1_220 : subd16_1 [0, 1, -6] = true := by decide +kernel
theorem subd16_1_221 : subd16_1 [0, 1, -5] = true := by decide +kernel
theorem subd16_1_222 : subd16_1 [0, 1, -4] = true := by decide +kernel
theorem subd16_1_223 : subd16_1 [0, 1, -3] = true := by decide +kernel
theorem sbd16_1_6 : ∀ q ∈ blkd16_1_6, subd16_1 q = true := by
  unfold blkd16_1_6
  exact List.forall_mem_cons.2 ⟨subd16_1_192, List.forall_mem_cons.2 ⟨subd16_1_193, List.forall_mem_cons.2 ⟨subd16_1_194, List.forall_mem_cons.2 ⟨subd16_1_195, List.forall_mem_cons.2 ⟨subd16_1_196, List.forall_mem_cons.2 ⟨subd16_1_197, List.forall_mem_cons.2 ⟨subd16_1_198, List.forall_mem_cons.2 ⟨subd16_1_199, List.forall_mem_cons.2 ⟨subd16_1_200, List.forall_mem_cons.2 ⟨subd16_1_201, List.forall_mem_cons.2 ⟨subd16_1_202, List.forall_mem_cons.2 ⟨subd16_1_203, List.forall_mem_cons.2 ⟨subd16_1_204, List.forall_mem_cons.2 ⟨subd16_1_205, List.forall_mem_cons.2 ⟨subd16_1_206, List.forall_mem_cons.2 ⟨subd16_1_207, List.forall_mem_cons.2 ⟨subd16_1_208, List.forall_mem_cons.2 ⟨subd16_1_209, List.forall_mem_cons.2 ⟨subd16_1_210, List.forall_mem_cons.2 ⟨subd16_1_211, List.forall_mem_cons.2 ⟨subd16_1_212, List.forall_mem_cons.2 ⟨subd16_1_213, List.forall_mem_cons.2 ⟨subd16_1_214, List.forall_mem_cons.2 ⟨subd16_1_215, List.forall_mem_cons.2 ⟨subd16_1_216, List.forall_mem_cons.2 ⟨subd16_1_217, List.forall_mem_cons.2 ⟨subd16_1_218, List.forall_mem_cons.2 ⟨subd16_1_219, List.forall_mem_cons.2 ⟨subd16_1_220, List.forall_mem_cons.2 ⟨subd16_1_221, List.forall_mem_cons.2 ⟨subd16_1_222, List.forall_mem_cons.2 ⟨subd16_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_224 : subd16_1 [0, 1, -2] = true := by decide +kernel
theorem subd16_1_225 : subd16_1 [0, 1, -1] = true := by decide +kernel
theorem subd16_1_226 : subd16_1 [0, 1, 0] = true := by decide +kernel
theorem subd16_1_227 : subd16_1 [0, 1, 1] = true := by decide +kernel
theorem subd16_1_228 : subd16_1 [0, 1, 2] = true := by decide +kernel
theorem subd16_1_229 : subd16_1 [0, 1, 3] = true := by decide +kernel
theorem subd16_1_230 : subd16_1 [0, 1, 4] = true := by decide +kernel
theorem subd16_1_231 : subd16_1 [0, 1, 5] = true := by decide +kernel
theorem subd16_1_232 : subd16_1 [0, 1, 6] = true := by decide +kernel
theorem subd16_1_233 : subd16_1 [0, 2, -7] = true := by decide +kernel
theorem subd16_1_234 : subd16_1 [0, 2, -6] = true := by decide +kernel
theorem subd16_1_235 : subd16_1 [0, 2, -5] = true := by decide +kernel
theorem subd16_1_236 : subd16_1 [0, 2, -4] = true := by decide +kernel
theorem subd16_1_237 : subd16_1 [0, 2, -3] = true := by decide +kernel
theorem subd16_1_238 : subd16_1 [0, 2, -2] = true := by decide +kernel
theorem subd16_1_239 : subd16_1 [0, 2, -1] = true := by decide +kernel
theorem subd16_1_240 : subd16_1 [0, 2, 0] = true := by decide +kernel
theorem subd16_1_241 : subd16_1 [0, 2, 1] = true := by decide +kernel
theorem subd16_1_242 : subd16_1 [0, 2, 2] = true := by decide +kernel
theorem subd16_1_243 : subd16_1 [0, 2, 3] = true := by decide +kernel
theorem subd16_1_244 : subd16_1 [0, 2, 4] = true := by decide +kernel
theorem subd16_1_245 : subd16_1 [0, 2, 5] = true := by decide +kernel
theorem subd16_1_246 : subd16_1 [0, 2, 6] = true := by decide +kernel
theorem subd16_1_247 : subd16_1 [0, 3] = true := by decide +kernel
theorem subd16_1_248 : subd16_1 [0, 4] = true := by decide +kernel
theorem subd16_1_249 : subd16_1 [0, 5] = true := by decide +kernel
theorem subd16_1_250 : subd16_1 [0, 6] = true := by decide +kernel
theorem subd16_1_251 : subd16_1 [1, -7] = true := by decide +kernel
theorem subd16_1_252 : subd16_1 [1, -6] = true := by decide +kernel
theorem subd16_1_253 : subd16_1 [1, -5] = true := by decide +kernel
theorem subd16_1_254 : subd16_1 [1, -4] = true := by decide +kernel
theorem subd16_1_255 : subd16_1 [1, -3] = true := by decide +kernel
theorem sbd16_1_7 : ∀ q ∈ blkd16_1_7, subd16_1 q = true := by
  unfold blkd16_1_7
  exact List.forall_mem_cons.2 ⟨subd16_1_224, List.forall_mem_cons.2 ⟨subd16_1_225, List.forall_mem_cons.2 ⟨subd16_1_226, List.forall_mem_cons.2 ⟨subd16_1_227, List.forall_mem_cons.2 ⟨subd16_1_228, List.forall_mem_cons.2 ⟨subd16_1_229, List.forall_mem_cons.2 ⟨subd16_1_230, List.forall_mem_cons.2 ⟨subd16_1_231, List.forall_mem_cons.2 ⟨subd16_1_232, List.forall_mem_cons.2 ⟨subd16_1_233, List.forall_mem_cons.2 ⟨subd16_1_234, List.forall_mem_cons.2 ⟨subd16_1_235, List.forall_mem_cons.2 ⟨subd16_1_236, List.forall_mem_cons.2 ⟨subd16_1_237, List.forall_mem_cons.2 ⟨subd16_1_238, List.forall_mem_cons.2 ⟨subd16_1_239, List.forall_mem_cons.2 ⟨subd16_1_240, List.forall_mem_cons.2 ⟨subd16_1_241, List.forall_mem_cons.2 ⟨subd16_1_242, List.forall_mem_cons.2 ⟨subd16_1_243, List.forall_mem_cons.2 ⟨subd16_1_244, List.forall_mem_cons.2 ⟨subd16_1_245, List.forall_mem_cons.2 ⟨subd16_1_246, List.forall_mem_cons.2 ⟨subd16_1_247, List.forall_mem_cons.2 ⟨subd16_1_248, List.forall_mem_cons.2 ⟨subd16_1_249, List.forall_mem_cons.2 ⟨subd16_1_250, List.forall_mem_cons.2 ⟨subd16_1_251, List.forall_mem_cons.2 ⟨subd16_1_252, List.forall_mem_cons.2 ⟨subd16_1_253, List.forall_mem_cons.2 ⟨subd16_1_254, List.forall_mem_cons.2 ⟨subd16_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_256 : subd16_1 [1, -2, -7] = true := by decide +kernel
theorem subd16_1_257 : subd16_1 [1, -2, -6] = true := by decide +kernel
theorem subd16_1_258 : subd16_1 [1, -2, -5] = true := by decide +kernel
theorem subd16_1_259 : subd16_1 [1, -2, -4] = true := by decide +kernel
theorem subd16_1_260 : subd16_1 [1, -2, -3] = true := by decide +kernel
theorem subd16_1_261 : subd16_1 [1, -2, -2] = true := by decide +kernel
theorem subd16_1_262 : subd16_1 [1, -2, -1] = true := by decide +kernel
theorem subd16_1_263 : subd16_1 [1, -2, 0] = true := by decide +kernel
theorem subd16_1_264 : subd16_1 [1, -2, 1] = true := by decide +kernel
theorem subd16_1_265 : subd16_1 [1, -2, 2] = true := by decide +kernel
theorem subd16_1_266 : subd16_1 [1, -2, 3] = true := by decide +kernel
theorem subd16_1_267 : subd16_1 [1, -2, 4] = true := by decide +kernel
theorem subd16_1_268 : subd16_1 [1, -2, 5] = true := by decide +kernel
theorem subd16_1_269 : subd16_1 [1, -2, 6] = true := by decide +kernel
theorem subd16_1_270 : subd16_1 [1, -1, -7] = true := by decide +kernel
theorem subd16_1_271 : subd16_1 [1, -1, -6] = true := by decide +kernel
theorem subd16_1_272 : subd16_1 [1, -1, -5] = true := by decide +kernel
theorem subd16_1_273 : subd16_1 [1, -1, -4] = true := by decide +kernel
theorem subd16_1_274 : subd16_1 [1, -1, -3] = true := by decide +kernel
theorem subd16_1_275 : subd16_1 [1, -1, -2] = true := by decide +kernel
theorem subd16_1_276 : subd16_1 [1, -1, -1] = true := by decide +kernel
theorem subd16_1_277 : subd16_1 [1, -1, 0] = true := by decide +kernel
theorem subd16_1_278 : subd16_1 [1, -1, 1] = true := by decide +kernel
theorem subd16_1_279 : subd16_1 [1, -1, 2] = true := by decide +kernel
theorem subd16_1_280 : subd16_1 [1, -1, 3] = true := by decide +kernel
theorem subd16_1_281 : subd16_1 [1, -1, 4] = true := by decide +kernel
theorem subd16_1_282 : subd16_1 [1, -1, 5] = true := by decide +kernel
theorem subd16_1_283 : subd16_1 [1, -1, 6] = true := by decide +kernel
theorem subd16_1_284 : subd16_1 [1, 0, -7] = true := by decide +kernel
theorem subd16_1_285 : subd16_1 [1, 0, -6] = true := by decide +kernel
theorem subd16_1_286 : subd16_1 [1, 0, -5] = true := by decide +kernel
theorem subd16_1_287 : subd16_1 [1, 0, -4] = true := by decide +kernel
theorem sbd16_1_8 : ∀ q ∈ blkd16_1_8, subd16_1 q = true := by
  unfold blkd16_1_8
  exact List.forall_mem_cons.2 ⟨subd16_1_256, List.forall_mem_cons.2 ⟨subd16_1_257, List.forall_mem_cons.2 ⟨subd16_1_258, List.forall_mem_cons.2 ⟨subd16_1_259, List.forall_mem_cons.2 ⟨subd16_1_260, List.forall_mem_cons.2 ⟨subd16_1_261, List.forall_mem_cons.2 ⟨subd16_1_262, List.forall_mem_cons.2 ⟨subd16_1_263, List.forall_mem_cons.2 ⟨subd16_1_264, List.forall_mem_cons.2 ⟨subd16_1_265, List.forall_mem_cons.2 ⟨subd16_1_266, List.forall_mem_cons.2 ⟨subd16_1_267, List.forall_mem_cons.2 ⟨subd16_1_268, List.forall_mem_cons.2 ⟨subd16_1_269, List.forall_mem_cons.2 ⟨subd16_1_270, List.forall_mem_cons.2 ⟨subd16_1_271, List.forall_mem_cons.2 ⟨subd16_1_272, List.forall_mem_cons.2 ⟨subd16_1_273, List.forall_mem_cons.2 ⟨subd16_1_274, List.forall_mem_cons.2 ⟨subd16_1_275, List.forall_mem_cons.2 ⟨subd16_1_276, List.forall_mem_cons.2 ⟨subd16_1_277, List.forall_mem_cons.2 ⟨subd16_1_278, List.forall_mem_cons.2 ⟨subd16_1_279, List.forall_mem_cons.2 ⟨subd16_1_280, List.forall_mem_cons.2 ⟨subd16_1_281, List.forall_mem_cons.2 ⟨subd16_1_282, List.forall_mem_cons.2 ⟨subd16_1_283, List.forall_mem_cons.2 ⟨subd16_1_284, List.forall_mem_cons.2 ⟨subd16_1_285, List.forall_mem_cons.2 ⟨subd16_1_286, List.forall_mem_cons.2 ⟨subd16_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_288 : subd16_1 [1, 0, -3] = true := by decide +kernel
theorem subd16_1_289 : subd16_1 [1, 0, -2] = true := by decide +kernel
theorem subd16_1_290 : subd16_1 [1, 0, -1] = true := by decide +kernel
theorem subd16_1_291 : subd16_1 [1, 0, 0] = true := by decide +kernel
theorem subd16_1_292 : subd16_1 [1, 0, 1] = true := by decide +kernel
theorem subd16_1_293 : subd16_1 [1, 0, 2] = true := by decide +kernel
theorem subd16_1_294 : subd16_1 [1, 0, 3] = true := by decide +kernel
theorem subd16_1_295 : subd16_1 [1, 0, 4] = true := by decide +kernel
theorem subd16_1_296 : subd16_1 [1, 0, 5] = true := by decide +kernel
theorem subd16_1_297 : subd16_1 [1, 0, 6] = true := by decide +kernel
theorem subd16_1_298 : subd16_1 [1, 1, -7] = true := by decide +kernel
theorem subd16_1_299 : subd16_1 [1, 1, -6] = true := by decide +kernel
theorem subd16_1_300 : subd16_1 [1, 1, -5] = true := by decide +kernel
theorem subd16_1_301 : subd16_1 [1, 1, -4] = true := by decide +kernel
theorem subd16_1_302 : subd16_1 [1, 1, -3] = true := by decide +kernel
theorem subd16_1_303 : subd16_1 [1, 1, -2] = true := by decide +kernel
theorem subd16_1_304 : subd16_1 [1, 1, -1] = true := by decide +kernel
theorem subd16_1_305 : subd16_1 [1, 1, 0] = true := by decide +kernel
theorem subd16_1_306 : subd16_1 [1, 1, 1] = true := by decide +kernel
theorem subd16_1_307 : subd16_1 [1, 1, 2] = true := by decide +kernel
theorem subd16_1_308 : subd16_1 [1, 1, 3] = true := by decide +kernel
theorem subd16_1_309 : subd16_1 [1, 1, 4] = true := by decide +kernel
theorem subd16_1_310 : subd16_1 [1, 1, 5] = true := by decide +kernel
theorem subd16_1_311 : subd16_1 [1, 1, 6] = true := by decide +kernel
theorem subd16_1_312 : subd16_1 [1, 2] = true := by decide +kernel
theorem subd16_1_313 : subd16_1 [1, 3] = true := by decide +kernel
theorem subd16_1_314 : subd16_1 [1, 4] = true := by decide +kernel
theorem subd16_1_315 : subd16_1 [1, 5] = true := by decide +kernel
theorem subd16_1_316 : subd16_1 [2, -7] = true := by decide +kernel
theorem subd16_1_317 : subd16_1 [2, -6] = true := by decide +kernel
theorem subd16_1_318 : subd16_1 [2, -5] = true := by decide +kernel
theorem subd16_1_319 : subd16_1 [2, -4] = true := by decide +kernel
theorem sbd16_1_9 : ∀ q ∈ blkd16_1_9, subd16_1 q = true := by
  unfold blkd16_1_9
  exact List.forall_mem_cons.2 ⟨subd16_1_288, List.forall_mem_cons.2 ⟨subd16_1_289, List.forall_mem_cons.2 ⟨subd16_1_290, List.forall_mem_cons.2 ⟨subd16_1_291, List.forall_mem_cons.2 ⟨subd16_1_292, List.forall_mem_cons.2 ⟨subd16_1_293, List.forall_mem_cons.2 ⟨subd16_1_294, List.forall_mem_cons.2 ⟨subd16_1_295, List.forall_mem_cons.2 ⟨subd16_1_296, List.forall_mem_cons.2 ⟨subd16_1_297, List.forall_mem_cons.2 ⟨subd16_1_298, List.forall_mem_cons.2 ⟨subd16_1_299, List.forall_mem_cons.2 ⟨subd16_1_300, List.forall_mem_cons.2 ⟨subd16_1_301, List.forall_mem_cons.2 ⟨subd16_1_302, List.forall_mem_cons.2 ⟨subd16_1_303, List.forall_mem_cons.2 ⟨subd16_1_304, List.forall_mem_cons.2 ⟨subd16_1_305, List.forall_mem_cons.2 ⟨subd16_1_306, List.forall_mem_cons.2 ⟨subd16_1_307, List.forall_mem_cons.2 ⟨subd16_1_308, List.forall_mem_cons.2 ⟨subd16_1_309, List.forall_mem_cons.2 ⟨subd16_1_310, List.forall_mem_cons.2 ⟨subd16_1_311, List.forall_mem_cons.2 ⟨subd16_1_312, List.forall_mem_cons.2 ⟨subd16_1_313, List.forall_mem_cons.2 ⟨subd16_1_314, List.forall_mem_cons.2 ⟨subd16_1_315, List.forall_mem_cons.2 ⟨subd16_1_316, List.forall_mem_cons.2 ⟨subd16_1_317, List.forall_mem_cons.2 ⟨subd16_1_318, List.forall_mem_cons.2 ⟨subd16_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_320 : subd16_1 [2, -3] = true := by decide +kernel
theorem subd16_1_321 : subd16_1 [2, -2, -7] = true := by decide +kernel
theorem subd16_1_322 : subd16_1 [2, -2, -6] = true := by decide +kernel
theorem subd16_1_323 : subd16_1 [2, -2, -5] = true := by decide +kernel
theorem subd16_1_324 : subd16_1 [2, -2, -4] = true := by decide +kernel
theorem subd16_1_325 : subd16_1 [2, -2, -3] = true := by decide +kernel
theorem subd16_1_326 : subd16_1 [2, -2, -2] = true := by decide +kernel
theorem subd16_1_327 : subd16_1 [2, -2, -1] = true := by decide +kernel
theorem subd16_1_328 : subd16_1 [2, -2, 0] = true := by decide +kernel
theorem subd16_1_329 : subd16_1 [2, -2, 1] = true := by decide +kernel
theorem subd16_1_330 : subd16_1 [2, -2, 2] = true := by decide +kernel
theorem subd16_1_331 : subd16_1 [2, -2, 3] = true := by decide +kernel
theorem subd16_1_332 : subd16_1 [2, -2, 4] = true := by decide +kernel
theorem subd16_1_333 : subd16_1 [2, -2, 5] = true := by decide +kernel
theorem subd16_1_334 : subd16_1 [2, -2, 6] = true := by decide +kernel
theorem subd16_1_335 : subd16_1 [2, -1, -7] = true := by decide +kernel
theorem subd16_1_336 : subd16_1 [2, -1, -6] = true := by decide +kernel
theorem subd16_1_337 : subd16_1 [2, -1, -5] = true := by decide +kernel
theorem subd16_1_338 : subd16_1 [2, -1, -4] = true := by decide +kernel
theorem subd16_1_339 : subd16_1 [2, -1, -3] = true := by decide +kernel
theorem subd16_1_340 : subd16_1 [2, -1, -2] = true := by decide +kernel
theorem subd16_1_341 : subd16_1 [2, -1, -1] = true := by decide +kernel
theorem subd16_1_342 : subd16_1 [2, -1, 0] = true := by decide +kernel
theorem subd16_1_343 : subd16_1 [2, -1, 1] = true := by decide +kernel
theorem subd16_1_344 : subd16_1 [2, -1, 2] = true := by decide +kernel
theorem subd16_1_345 : subd16_1 [2, -1, 3] = true := by decide +kernel
theorem subd16_1_346 : subd16_1 [2, -1, 4] = true := by decide +kernel
theorem subd16_1_347 : subd16_1 [2, -1, 5] = true := by decide +kernel
theorem subd16_1_348 : subd16_1 [2, -1, 6] = true := by decide +kernel
theorem subd16_1_349 : subd16_1 [2, 0, -7] = true := by decide +kernel
theorem subd16_1_350 : subd16_1 [2, 0, -6] = true := by decide +kernel
theorem subd16_1_351 : subd16_1 [2, 0, -5] = true := by decide +kernel
theorem sbd16_1_10 : ∀ q ∈ blkd16_1_10, subd16_1 q = true := by
  unfold blkd16_1_10
  exact List.forall_mem_cons.2 ⟨subd16_1_320, List.forall_mem_cons.2 ⟨subd16_1_321, List.forall_mem_cons.2 ⟨subd16_1_322, List.forall_mem_cons.2 ⟨subd16_1_323, List.forall_mem_cons.2 ⟨subd16_1_324, List.forall_mem_cons.2 ⟨subd16_1_325, List.forall_mem_cons.2 ⟨subd16_1_326, List.forall_mem_cons.2 ⟨subd16_1_327, List.forall_mem_cons.2 ⟨subd16_1_328, List.forall_mem_cons.2 ⟨subd16_1_329, List.forall_mem_cons.2 ⟨subd16_1_330, List.forall_mem_cons.2 ⟨subd16_1_331, List.forall_mem_cons.2 ⟨subd16_1_332, List.forall_mem_cons.2 ⟨subd16_1_333, List.forall_mem_cons.2 ⟨subd16_1_334, List.forall_mem_cons.2 ⟨subd16_1_335, List.forall_mem_cons.2 ⟨subd16_1_336, List.forall_mem_cons.2 ⟨subd16_1_337, List.forall_mem_cons.2 ⟨subd16_1_338, List.forall_mem_cons.2 ⟨subd16_1_339, List.forall_mem_cons.2 ⟨subd16_1_340, List.forall_mem_cons.2 ⟨subd16_1_341, List.forall_mem_cons.2 ⟨subd16_1_342, List.forall_mem_cons.2 ⟨subd16_1_343, List.forall_mem_cons.2 ⟨subd16_1_344, List.forall_mem_cons.2 ⟨subd16_1_345, List.forall_mem_cons.2 ⟨subd16_1_346, List.forall_mem_cons.2 ⟨subd16_1_347, List.forall_mem_cons.2 ⟨subd16_1_348, List.forall_mem_cons.2 ⟨subd16_1_349, List.forall_mem_cons.2 ⟨subd16_1_350, List.forall_mem_cons.2 ⟨subd16_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_352 : subd16_1 [2, 0, -4] = true := by decide +kernel
theorem subd16_1_353 : subd16_1 [2, 0, -3] = true := by decide +kernel
theorem subd16_1_354 : subd16_1 [2, 0, -2] = true := by decide +kernel
theorem subd16_1_355 : subd16_1 [2, 0, -1] = true := by decide +kernel
theorem subd16_1_356 : subd16_1 [2, 0, 0] = true := by decide +kernel
theorem subd16_1_357 : subd16_1 [2, 0, 1] = true := by decide +kernel
theorem subd16_1_358 : subd16_1 [2, 0, 2] = true := by decide +kernel
theorem subd16_1_359 : subd16_1 [2, 0, 3] = true := by decide +kernel
theorem subd16_1_360 : subd16_1 [2, 0, 4] = true := by decide +kernel
theorem subd16_1_361 : subd16_1 [2, 0, 5] = true := by decide +kernel
theorem subd16_1_362 : subd16_1 [2, 0, 6] = true := by decide +kernel
theorem subd16_1_363 : subd16_1 [2, 1, -6] = true := by decide +kernel
theorem subd16_1_364 : subd16_1 [2, 1, -5] = true := by decide +kernel
theorem subd16_1_365 : subd16_1 [2, 1, -4] = true := by decide +kernel
theorem subd16_1_366 : subd16_1 [2, 1, -3] = true := by decide +kernel
theorem subd16_1_367 : subd16_1 [2, 1, -2] = true := by decide +kernel
theorem subd16_1_368 : subd16_1 [2, 1, -1] = true := by decide +kernel
theorem subd16_1_369 : subd16_1 [2, 1, 0] = true := by decide +kernel
theorem subd16_1_370 : subd16_1 [2, 1, 1] = true := by decide +kernel
theorem subd16_1_371 : subd16_1 [2, 1, 2] = true := by decide +kernel
theorem subd16_1_372 : subd16_1 [2, 1, 3] = true := by decide +kernel
theorem subd16_1_373 : subd16_1 [2, 1, 4] = true := by decide +kernel
theorem subd16_1_374 : subd16_1 [2, 1, 5] = true := by decide +kernel
theorem subd16_1_375 : subd16_1 [2, 1, 6] = true := by decide +kernel
theorem subd16_1_376 : subd16_1 [2, 2] = true := by decide +kernel
theorem subd16_1_377 : subd16_1 [2, 3] = true := by decide +kernel
theorem subd16_1_378 : subd16_1 [2, 4] = true := by decide +kernel
theorem subd16_1_379 : subd16_1 [2, 5] = true := by decide +kernel
theorem subd16_1_380 : subd16_1 [3, -7] = true := by decide +kernel
theorem subd16_1_381 : subd16_1 [3, -6] = true := by decide +kernel
theorem subd16_1_382 : subd16_1 [3, -5] = true := by decide +kernel
theorem subd16_1_383 : subd16_1 [3, -4] = true := by decide +kernel
theorem sbd16_1_11 : ∀ q ∈ blkd16_1_11, subd16_1 q = true := by
  unfold blkd16_1_11
  exact List.forall_mem_cons.2 ⟨subd16_1_352, List.forall_mem_cons.2 ⟨subd16_1_353, List.forall_mem_cons.2 ⟨subd16_1_354, List.forall_mem_cons.2 ⟨subd16_1_355, List.forall_mem_cons.2 ⟨subd16_1_356, List.forall_mem_cons.2 ⟨subd16_1_357, List.forall_mem_cons.2 ⟨subd16_1_358, List.forall_mem_cons.2 ⟨subd16_1_359, List.forall_mem_cons.2 ⟨subd16_1_360, List.forall_mem_cons.2 ⟨subd16_1_361, List.forall_mem_cons.2 ⟨subd16_1_362, List.forall_mem_cons.2 ⟨subd16_1_363, List.forall_mem_cons.2 ⟨subd16_1_364, List.forall_mem_cons.2 ⟨subd16_1_365, List.forall_mem_cons.2 ⟨subd16_1_366, List.forall_mem_cons.2 ⟨subd16_1_367, List.forall_mem_cons.2 ⟨subd16_1_368, List.forall_mem_cons.2 ⟨subd16_1_369, List.forall_mem_cons.2 ⟨subd16_1_370, List.forall_mem_cons.2 ⟨subd16_1_371, List.forall_mem_cons.2 ⟨subd16_1_372, List.forall_mem_cons.2 ⟨subd16_1_373, List.forall_mem_cons.2 ⟨subd16_1_374, List.forall_mem_cons.2 ⟨subd16_1_375, List.forall_mem_cons.2 ⟨subd16_1_376, List.forall_mem_cons.2 ⟨subd16_1_377, List.forall_mem_cons.2 ⟨subd16_1_378, List.forall_mem_cons.2 ⟨subd16_1_379, List.forall_mem_cons.2 ⟨subd16_1_380, List.forall_mem_cons.2 ⟨subd16_1_381, List.forall_mem_cons.2 ⟨subd16_1_382, List.forall_mem_cons.2 ⟨subd16_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
