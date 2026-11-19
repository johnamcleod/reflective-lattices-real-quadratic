import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd18_1_96 : subd18_1 [-3, 1, 0] = true := by decide +kernel
theorem subd18_1_97 : subd18_1 [-3, 1, 1] = true := by decide +kernel
theorem subd18_1_98 : subd18_1 [-3, 1, 2] = true := by decide +kernel
theorem subd18_1_99 : subd18_1 [-3, 1, 3] = true := by decide +kernel
theorem subd18_1_100 : subd18_1 [-3, 1, 4] = true := by decide +kernel
theorem subd18_1_101 : subd18_1 [-3, 2] = true := by decide +kernel
theorem subd18_1_102 : subd18_1 [-3, 3] = true := by decide +kernel
theorem subd18_1_103 : subd18_1 [-3, 4] = true := by decide +kernel
theorem subd18_1_104 : subd18_1 [-3, 5] = true := by decide +kernel
theorem subd18_1_105 : subd18_1 [-2, -8] = true := by decide +kernel
theorem subd18_1_106 : subd18_1 [-2, -7] = true := by decide +kernel
theorem subd18_1_107 : subd18_1 [-2, -6] = true := by decide +kernel
theorem subd18_1_108 : subd18_1 [-2, -5] = true := by decide +kernel
theorem subd18_1_109 : subd18_1 [-2, -4, -6] = true := by decide +kernel
theorem subd18_1_110 : subd18_1 [-2, -4, -5] = true := by decide +kernel
theorem subd18_1_111 : subd18_1 [-2, -4, -4] = true := by decide +kernel
theorem subd18_1_112 : subd18_1 [-2, -4, -3] = true := by decide +kernel
theorem subd18_1_113 : subd18_1 [-2, -4, -2] = true := by decide +kernel
theorem subd18_1_114 : subd18_1 [-2, -4, -1] = true := by decide +kernel
theorem subd18_1_115 : subd18_1 [-2, -4, 0] = true := by decide +kernel
theorem subd18_1_116 : subd18_1 [-2, -4, 1] = true := by decide +kernel
theorem subd18_1_117 : subd18_1 [-2, -4, 2] = true := by decide +kernel
theorem subd18_1_118 : subd18_1 [-2, -4, 3] = true := by decide +kernel
theorem subd18_1_119 : subd18_1 [-2, -4, 4] = true := by decide +kernel
theorem subd18_1_120 : subd18_1 [-2, -4, 5] = true := by decide +kernel
theorem subd18_1_121 : subd18_1 [-2, -4, 6] = true := by decide +kernel
theorem subd18_1_122 : subd18_1 [-2, -4, 7] = true := by decide +kernel
theorem subd18_1_123 : subd18_1 [-2, -3, -7] = true := by decide +kernel
theorem subd18_1_124 : subd18_1 [-2, -3, -6] = true := by decide +kernel
theorem subd18_1_125 : subd18_1 [-2, -3, -5] = true := by decide +kernel
theorem subd18_1_126 : subd18_1 [-2, -3, -4] = true := by decide +kernel
theorem subd18_1_127 : subd18_1 [-2, -3, -3] = true := by decide +kernel
theorem sbd18_1_3 : ∀ q ∈ blkd18_1_3, subd18_1 q = true := by
  unfold blkd18_1_3
  exact List.forall_mem_cons.2 ⟨subd18_1_96, List.forall_mem_cons.2 ⟨subd18_1_97, List.forall_mem_cons.2 ⟨subd18_1_98, List.forall_mem_cons.2 ⟨subd18_1_99, List.forall_mem_cons.2 ⟨subd18_1_100, List.forall_mem_cons.2 ⟨subd18_1_101, List.forall_mem_cons.2 ⟨subd18_1_102, List.forall_mem_cons.2 ⟨subd18_1_103, List.forall_mem_cons.2 ⟨subd18_1_104, List.forall_mem_cons.2 ⟨subd18_1_105, List.forall_mem_cons.2 ⟨subd18_1_106, List.forall_mem_cons.2 ⟨subd18_1_107, List.forall_mem_cons.2 ⟨subd18_1_108, List.forall_mem_cons.2 ⟨subd18_1_109, List.forall_mem_cons.2 ⟨subd18_1_110, List.forall_mem_cons.2 ⟨subd18_1_111, List.forall_mem_cons.2 ⟨subd18_1_112, List.forall_mem_cons.2 ⟨subd18_1_113, List.forall_mem_cons.2 ⟨subd18_1_114, List.forall_mem_cons.2 ⟨subd18_1_115, List.forall_mem_cons.2 ⟨subd18_1_116, List.forall_mem_cons.2 ⟨subd18_1_117, List.forall_mem_cons.2 ⟨subd18_1_118, List.forall_mem_cons.2 ⟨subd18_1_119, List.forall_mem_cons.2 ⟨subd18_1_120, List.forall_mem_cons.2 ⟨subd18_1_121, List.forall_mem_cons.2 ⟨subd18_1_122, List.forall_mem_cons.2 ⟨subd18_1_123, List.forall_mem_cons.2 ⟨subd18_1_124, List.forall_mem_cons.2 ⟨subd18_1_125, List.forall_mem_cons.2 ⟨subd18_1_126, List.forall_mem_cons.2 ⟨subd18_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_128 : subd18_1 [-2, -3, -2] = true := by decide +kernel
theorem subd18_1_129 : subd18_1 [-2, -3, -1] = true := by decide +kernel
theorem subd18_1_130 : subd18_1 [-2, -3, 0] = true := by decide +kernel
theorem subd18_1_131 : subd18_1 [-2, -3, 1] = true := by decide +kernel
theorem subd18_1_132 : subd18_1 [-2, -3, 2] = true := by decide +kernel
theorem subd18_1_133 : subd18_1 [-2, -3, 3] = true := by decide +kernel
theorem subd18_1_134 : subd18_1 [-2, -3, 4] = true := by decide +kernel
theorem subd18_1_135 : subd18_1 [-2, -3, 5] = true := by decide +kernel
theorem subd18_1_136 : subd18_1 [-2, -3, 6] = true := by decide +kernel
theorem subd18_1_137 : subd18_1 [-2, -3, 7] = true := by decide +kernel
theorem subd18_1_138 : subd18_1 [-2, -2, -8] = true := by decide +kernel
theorem subd18_1_139 : subd18_1 [-2, -2, -7] = true := by decide +kernel
theorem subd18_1_140 : subd18_1 [-2, -2, -6] = true := by decide +kernel
theorem subd18_1_141 : subd18_1 [-2, -2, -5] = true := by decide +kernel
theorem subd18_1_142 : subd18_1 [-2, -2, -4] = true := by decide +kernel
theorem subd18_1_143 : subd18_1 [-2, -2, -3] = true := by decide +kernel
theorem subd18_1_144 : subd18_1 [-2, -2, -2] = true := by decide +kernel
theorem subd18_1_145 : subd18_1 [-2, -2, -1] = true := by decide +kernel
theorem subd18_1_146 : subd18_1 [-2, -2, 0] = true := by decide +kernel
theorem subd18_1_147 : subd18_1 [-2, -2, 1] = true := by decide +kernel
theorem subd18_1_148 : subd18_1 [-2, -2, 2] = true := by decide +kernel
theorem subd18_1_149 : subd18_1 [-2, -2, 3] = true := by decide +kernel
theorem subd18_1_150 : subd18_1 [-2, -2, 4] = true := by decide +kernel
theorem subd18_1_151 : subd18_1 [-2, -2, 5] = true := by decide +kernel
theorem subd18_1_152 : subd18_1 [-2, -2, 6] = true := by decide +kernel
theorem subd18_1_153 : subd18_1 [-2, -2, 7] = true := by decide +kernel
theorem subd18_1_154 : subd18_1 [-2, -1, -8] = true := by decide +kernel
theorem subd18_1_155 : subd18_1 [-2, -1, -7] = true := by decide +kernel
theorem subd18_1_156 : subd18_1 [-2, -1, -6] = true := by decide +kernel
theorem subd18_1_157 : subd18_1 [-2, -1, -5] = true := by decide +kernel
theorem subd18_1_158 : subd18_1 [-2, -1, -4] = true := by decide +kernel
theorem subd18_1_159 : subd18_1 [-2, -1, -3] = true := by decide +kernel
theorem sbd18_1_4 : ∀ q ∈ blkd18_1_4, subd18_1 q = true := by
  unfold blkd18_1_4
  exact List.forall_mem_cons.2 ⟨subd18_1_128, List.forall_mem_cons.2 ⟨subd18_1_129, List.forall_mem_cons.2 ⟨subd18_1_130, List.forall_mem_cons.2 ⟨subd18_1_131, List.forall_mem_cons.2 ⟨subd18_1_132, List.forall_mem_cons.2 ⟨subd18_1_133, List.forall_mem_cons.2 ⟨subd18_1_134, List.forall_mem_cons.2 ⟨subd18_1_135, List.forall_mem_cons.2 ⟨subd18_1_136, List.forall_mem_cons.2 ⟨subd18_1_137, List.forall_mem_cons.2 ⟨subd18_1_138, List.forall_mem_cons.2 ⟨subd18_1_139, List.forall_mem_cons.2 ⟨subd18_1_140, List.forall_mem_cons.2 ⟨subd18_1_141, List.forall_mem_cons.2 ⟨subd18_1_142, List.forall_mem_cons.2 ⟨subd18_1_143, List.forall_mem_cons.2 ⟨subd18_1_144, List.forall_mem_cons.2 ⟨subd18_1_145, List.forall_mem_cons.2 ⟨subd18_1_146, List.forall_mem_cons.2 ⟨subd18_1_147, List.forall_mem_cons.2 ⟨subd18_1_148, List.forall_mem_cons.2 ⟨subd18_1_149, List.forall_mem_cons.2 ⟨subd18_1_150, List.forall_mem_cons.2 ⟨subd18_1_151, List.forall_mem_cons.2 ⟨subd18_1_152, List.forall_mem_cons.2 ⟨subd18_1_153, List.forall_mem_cons.2 ⟨subd18_1_154, List.forall_mem_cons.2 ⟨subd18_1_155, List.forall_mem_cons.2 ⟨subd18_1_156, List.forall_mem_cons.2 ⟨subd18_1_157, List.forall_mem_cons.2 ⟨subd18_1_158, List.forall_mem_cons.2 ⟨subd18_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_160 : subd18_1 [-2, -1, -2] = true := by decide +kernel
theorem subd18_1_161 : subd18_1 [-2, -1, -1] = true := by decide +kernel
theorem subd18_1_162 : subd18_1 [-2, -1, 0] = true := by decide +kernel
theorem subd18_1_163 : subd18_1 [-2, -1, 1] = true := by decide +kernel
theorem subd18_1_164 : subd18_1 [-2, -1, 2] = true := by decide +kernel
theorem subd18_1_165 : subd18_1 [-2, -1, 3] = true := by decide +kernel
theorem subd18_1_166 : subd18_1 [-2, -1, 4] = true := by decide +kernel
theorem subd18_1_167 : subd18_1 [-2, -1, 5] = true := by decide +kernel
theorem subd18_1_168 : subd18_1 [-2, -1, 6] = true := by decide +kernel
theorem subd18_1_169 : subd18_1 [-2, -1, 7] = true := by decide +kernel
theorem subd18_1_170 : subd18_1 [-2, 0, -9] = true := by decide +kernel
theorem subd18_1_171 : subd18_1 [-2, 0, -8] = true := by decide +kernel
theorem subd18_1_172 : subd18_1 [-2, 0, -7] = true := by decide +kernel
theorem subd18_1_173 : subd18_1 [-2, 0, -6] = true := by decide +kernel
theorem subd18_1_174 : subd18_1 [-2, 0, -5] = true := by decide +kernel
theorem subd18_1_175 : subd18_1 [-2, 0, -4] = true := by decide +kernel
theorem subd18_1_176 : subd18_1 [-2, 0, -3] = true := by decide +kernel
theorem subd18_1_177 : subd18_1 [-2, 0, -2] = true := by decide +kernel
theorem subd18_1_178 : subd18_1 [-2, 0, -1] = true := by decide +kernel
theorem subd18_1_179 : subd18_1 [-2, 0, 0] = true := by decide +kernel
theorem subd18_1_180 : subd18_1 [-2, 0, 1] = true := by decide +kernel
theorem subd18_1_181 : subd18_1 [-2, 0, 2] = true := by decide +kernel
theorem subd18_1_182 : subd18_1 [-2, 0, 3] = true := by decide +kernel
theorem subd18_1_183 : subd18_1 [-2, 0, 4] = true := by decide +kernel
theorem subd18_1_184 : subd18_1 [-2, 0, 5] = true := by decide +kernel
theorem subd18_1_185 : subd18_1 [-2, 0, 6] = true := by decide +kernel
theorem subd18_1_186 : subd18_1 [-2, 1, -9] = true := by decide +kernel
theorem subd18_1_187 : subd18_1 [-2, 1, -8] = true := by decide +kernel
theorem subd18_1_188 : subd18_1 [-2, 1, -7] = true := by decide +kernel
theorem subd18_1_189 : subd18_1 [-2, 1, -6] = true := by decide +kernel
theorem subd18_1_190 : subd18_1 [-2, 1, -5] = true := by decide +kernel
theorem subd18_1_191 : subd18_1 [-2, 1, -4] = true := by decide +kernel
theorem sbd18_1_5 : ∀ q ∈ blkd18_1_5, subd18_1 q = true := by
  unfold blkd18_1_5
  exact List.forall_mem_cons.2 ⟨subd18_1_160, List.forall_mem_cons.2 ⟨subd18_1_161, List.forall_mem_cons.2 ⟨subd18_1_162, List.forall_mem_cons.2 ⟨subd18_1_163, List.forall_mem_cons.2 ⟨subd18_1_164, List.forall_mem_cons.2 ⟨subd18_1_165, List.forall_mem_cons.2 ⟨subd18_1_166, List.forall_mem_cons.2 ⟨subd18_1_167, List.forall_mem_cons.2 ⟨subd18_1_168, List.forall_mem_cons.2 ⟨subd18_1_169, List.forall_mem_cons.2 ⟨subd18_1_170, List.forall_mem_cons.2 ⟨subd18_1_171, List.forall_mem_cons.2 ⟨subd18_1_172, List.forall_mem_cons.2 ⟨subd18_1_173, List.forall_mem_cons.2 ⟨subd18_1_174, List.forall_mem_cons.2 ⟨subd18_1_175, List.forall_mem_cons.2 ⟨subd18_1_176, List.forall_mem_cons.2 ⟨subd18_1_177, List.forall_mem_cons.2 ⟨subd18_1_178, List.forall_mem_cons.2 ⟨subd18_1_179, List.forall_mem_cons.2 ⟨subd18_1_180, List.forall_mem_cons.2 ⟨subd18_1_181, List.forall_mem_cons.2 ⟨subd18_1_182, List.forall_mem_cons.2 ⟨subd18_1_183, List.forall_mem_cons.2 ⟨subd18_1_184, List.forall_mem_cons.2 ⟨subd18_1_185, List.forall_mem_cons.2 ⟨subd18_1_186, List.forall_mem_cons.2 ⟨subd18_1_187, List.forall_mem_cons.2 ⟨subd18_1_188, List.forall_mem_cons.2 ⟨subd18_1_189, List.forall_mem_cons.2 ⟨subd18_1_190, List.forall_mem_cons.2 ⟨subd18_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_192 : subd18_1 [-2, 1, -3] = true := by decide +kernel
theorem subd18_1_193 : subd18_1 [-2, 1, -2] = true := by decide +kernel
theorem subd18_1_194 : subd18_1 [-2, 1, -1] = true := by decide +kernel
theorem subd18_1_195 : subd18_1 [-2, 1, 0] = true := by decide +kernel
theorem subd18_1_196 : subd18_1 [-2, 1, 1] = true := by decide +kernel
theorem subd18_1_197 : subd18_1 [-2, 1, 2] = true := by decide +kernel
theorem subd18_1_198 : subd18_1 [-2, 1, 3] = true := by decide +kernel
theorem subd18_1_199 : subd18_1 [-2, 1, 4] = true := by decide +kernel
theorem subd18_1_200 : subd18_1 [-2, 1, 5] = true := by decide +kernel
theorem subd18_1_201 : subd18_1 [-2, 2, -9] = true := by decide +kernel
theorem subd18_1_202 : subd18_1 [-2, 2, -8] = true := by decide +kernel
theorem subd18_1_203 : subd18_1 [-2, 2, -7] = true := by decide +kernel
theorem subd18_1_204 : subd18_1 [-2, 2, -6] = true := by decide +kernel
theorem subd18_1_205 : subd18_1 [-2, 2, -5] = true := by decide +kernel
theorem subd18_1_206 : subd18_1 [-2, 2, -4] = true := by decide +kernel
theorem subd18_1_207 : subd18_1 [-2, 2, -3] = true := by decide +kernel
theorem subd18_1_208 : subd18_1 [-2, 2, -2] = true := by decide +kernel
theorem subd18_1_209 : subd18_1 [-2, 2, -1] = true := by decide +kernel
theorem subd18_1_210 : subd18_1 [-2, 2, 0] = true := by decide +kernel
theorem subd18_1_211 : subd18_1 [-2, 2, 1] = true := by decide +kernel
theorem subd18_1_212 : subd18_1 [-2, 2, 2] = true := by decide +kernel
theorem subd18_1_213 : subd18_1 [-2, 2, 3] = true := by decide +kernel
theorem subd18_1_214 : subd18_1 [-2, 2, 4] = true := by decide +kernel
theorem subd18_1_215 : subd18_1 [-2, 2, 5] = true := by decide +kernel
theorem subd18_1_216 : subd18_1 [-2, 3] = true := by decide +kernel
theorem subd18_1_217 : subd18_1 [-2, 4] = true := by decide +kernel
theorem subd18_1_218 : subd18_1 [-2, 5] = true := by decide +kernel
theorem subd18_1_219 : subd18_1 [-2, 6] = true := by decide +kernel
theorem subd18_1_220 : subd18_1 [-1, -8] = true := by decide +kernel
theorem subd18_1_221 : subd18_1 [-1, -7] = true := by decide +kernel
theorem subd18_1_222 : subd18_1 [-1, -6] = true := by decide +kernel
theorem subd18_1_223 : subd18_1 [-1, -5] = true := by decide +kernel
theorem sbd18_1_6 : ∀ q ∈ blkd18_1_6, subd18_1 q = true := by
  unfold blkd18_1_6
  exact List.forall_mem_cons.2 ⟨subd18_1_192, List.forall_mem_cons.2 ⟨subd18_1_193, List.forall_mem_cons.2 ⟨subd18_1_194, List.forall_mem_cons.2 ⟨subd18_1_195, List.forall_mem_cons.2 ⟨subd18_1_196, List.forall_mem_cons.2 ⟨subd18_1_197, List.forall_mem_cons.2 ⟨subd18_1_198, List.forall_mem_cons.2 ⟨subd18_1_199, List.forall_mem_cons.2 ⟨subd18_1_200, List.forall_mem_cons.2 ⟨subd18_1_201, List.forall_mem_cons.2 ⟨subd18_1_202, List.forall_mem_cons.2 ⟨subd18_1_203, List.forall_mem_cons.2 ⟨subd18_1_204, List.forall_mem_cons.2 ⟨subd18_1_205, List.forall_mem_cons.2 ⟨subd18_1_206, List.forall_mem_cons.2 ⟨subd18_1_207, List.forall_mem_cons.2 ⟨subd18_1_208, List.forall_mem_cons.2 ⟨subd18_1_209, List.forall_mem_cons.2 ⟨subd18_1_210, List.forall_mem_cons.2 ⟨subd18_1_211, List.forall_mem_cons.2 ⟨subd18_1_212, List.forall_mem_cons.2 ⟨subd18_1_213, List.forall_mem_cons.2 ⟨subd18_1_214, List.forall_mem_cons.2 ⟨subd18_1_215, List.forall_mem_cons.2 ⟨subd18_1_216, List.forall_mem_cons.2 ⟨subd18_1_217, List.forall_mem_cons.2 ⟨subd18_1_218, List.forall_mem_cons.2 ⟨subd18_1_219, List.forall_mem_cons.2 ⟨subd18_1_220, List.forall_mem_cons.2 ⟨subd18_1_221, List.forall_mem_cons.2 ⟨subd18_1_222, List.forall_mem_cons.2 ⟨subd18_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_224 : subd18_1 [-1, -4, -6] = true := by decide +kernel
theorem subd18_1_225 : subd18_1 [-1, -4, -5] = true := by decide +kernel
theorem subd18_1_226 : subd18_1 [-1, -4, -4] = true := by decide +kernel
theorem subd18_1_227 : subd18_1 [-1, -4, -3] = true := by decide +kernel
theorem subd18_1_228 : subd18_1 [-1, -4, -2] = true := by decide +kernel
theorem subd18_1_229 : subd18_1 [-1, -4, -1] = true := by decide +kernel
theorem subd18_1_230 : subd18_1 [-1, -4, 0] = true := by decide +kernel
theorem subd18_1_231 : subd18_1 [-1, -4, 1] = true := by decide +kernel
theorem subd18_1_232 : subd18_1 [-1, -4, 2] = true := by decide +kernel
theorem subd18_1_233 : subd18_1 [-1, -4, 3] = true := by decide +kernel
theorem subd18_1_234 : subd18_1 [-1, -4, 4] = true := by decide +kernel
theorem subd18_1_235 : subd18_1 [-1, -4, 5] = true := by decide +kernel
theorem subd18_1_236 : subd18_1 [-1, -4, 6] = true := by decide +kernel
theorem subd18_1_237 : subd18_1 [-1, -4, 7] = true := by decide +kernel
theorem subd18_1_238 : subd18_1 [-1, -4, 8] = true := by decide +kernel
theorem subd18_1_239 : subd18_1 [-1, -3, -7] = true := by decide +kernel
theorem subd18_1_240 : subd18_1 [-1, -3, -6] = true := by decide +kernel
theorem subd18_1_241 : subd18_1 [-1, -3, -5] = true := by decide +kernel
theorem subd18_1_242 : subd18_1 [-1, -3, -4] = true := by decide +kernel
theorem subd18_1_243 : subd18_1 [-1, -3, -3] = true := by decide +kernel
theorem subd18_1_244 : subd18_1 [-1, -3, -2] = true := by decide +kernel
theorem subd18_1_245 : subd18_1 [-1, -3, -1] = true := by decide +kernel
theorem subd18_1_246 : subd18_1 [-1, -3, 0] = true := by decide +kernel
theorem subd18_1_247 : subd18_1 [-1, -3, 1] = true := by decide +kernel
theorem subd18_1_248 : subd18_1 [-1, -3, 2] = true := by decide +kernel
theorem subd18_1_249 : subd18_1 [-1, -3, 3] = true := by decide +kernel
theorem subd18_1_250 : subd18_1 [-1, -3, 4] = true := by decide +kernel
theorem subd18_1_251 : subd18_1 [-1, -3, 5] = true := by decide +kernel
theorem subd18_1_252 : subd18_1 [-1, -3, 6] = true := by decide +kernel
theorem subd18_1_253 : subd18_1 [-1, -3, 7] = true := by decide +kernel
theorem subd18_1_254 : subd18_1 [-1, -3, 8] = true := by decide +kernel
theorem subd18_1_255 : subd18_1 [-1, -2, -8] = true := by decide +kernel
theorem sbd18_1_7 : ∀ q ∈ blkd18_1_7, subd18_1 q = true := by
  unfold blkd18_1_7
  exact List.forall_mem_cons.2 ⟨subd18_1_224, List.forall_mem_cons.2 ⟨subd18_1_225, List.forall_mem_cons.2 ⟨subd18_1_226, List.forall_mem_cons.2 ⟨subd18_1_227, List.forall_mem_cons.2 ⟨subd18_1_228, List.forall_mem_cons.2 ⟨subd18_1_229, List.forall_mem_cons.2 ⟨subd18_1_230, List.forall_mem_cons.2 ⟨subd18_1_231, List.forall_mem_cons.2 ⟨subd18_1_232, List.forall_mem_cons.2 ⟨subd18_1_233, List.forall_mem_cons.2 ⟨subd18_1_234, List.forall_mem_cons.2 ⟨subd18_1_235, List.forall_mem_cons.2 ⟨subd18_1_236, List.forall_mem_cons.2 ⟨subd18_1_237, List.forall_mem_cons.2 ⟨subd18_1_238, List.forall_mem_cons.2 ⟨subd18_1_239, List.forall_mem_cons.2 ⟨subd18_1_240, List.forall_mem_cons.2 ⟨subd18_1_241, List.forall_mem_cons.2 ⟨subd18_1_242, List.forall_mem_cons.2 ⟨subd18_1_243, List.forall_mem_cons.2 ⟨subd18_1_244, List.forall_mem_cons.2 ⟨subd18_1_245, List.forall_mem_cons.2 ⟨subd18_1_246, List.forall_mem_cons.2 ⟨subd18_1_247, List.forall_mem_cons.2 ⟨subd18_1_248, List.forall_mem_cons.2 ⟨subd18_1_249, List.forall_mem_cons.2 ⟨subd18_1_250, List.forall_mem_cons.2 ⟨subd18_1_251, List.forall_mem_cons.2 ⟨subd18_1_252, List.forall_mem_cons.2 ⟨subd18_1_253, List.forall_mem_cons.2 ⟨subd18_1_254, List.forall_mem_cons.2 ⟨subd18_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_256 : subd18_1 [-1, -2, -7] = true := by decide +kernel
theorem subd18_1_257 : subd18_1 [-1, -2, -6] = true := by decide +kernel
theorem subd18_1_258 : subd18_1 [-1, -2, -5] = true := by decide +kernel
theorem subd18_1_259 : subd18_1 [-1, -2, -4] = true := by decide +kernel
theorem subd18_1_260 : subd18_1 [-1, -2, -3] = true := by decide +kernel
theorem subd18_1_261 : subd18_1 [-1, -2, -2] = true := by decide +kernel
theorem subd18_1_262 : subd18_1 [-1, -2, -1] = true := by decide +kernel
theorem subd18_1_263 : subd18_1 [-1, -2, 0] = true := by decide +kernel
theorem subd18_1_264 : subd18_1 [-1, -2, 1] = true := by decide +kernel
theorem subd18_1_265 : subd18_1 [-1, -2, 2] = true := by decide +kernel
theorem subd18_1_266 : subd18_1 [-1, -2, 3] = true := by decide +kernel
theorem subd18_1_267 : subd18_1 [-1, -2, 4] = true := by decide +kernel
theorem subd18_1_268 : subd18_1 [-1, -2, 5] = true := by decide +kernel
theorem subd18_1_269 : subd18_1 [-1, -2, 6] = true := by decide +kernel
theorem subd18_1_270 : subd18_1 [-1, -2, 7] = true := by decide +kernel
theorem subd18_1_271 : subd18_1 [-1, -2, 8] = true := by decide +kernel
theorem subd18_1_272 : subd18_1 [-1, -1, -8] = true := by decide +kernel
theorem subd18_1_273 : subd18_1 [-1, -1, -7] = true := by decide +kernel
theorem subd18_1_274 : subd18_1 [-1, -1, -6] = true := by decide +kernel
theorem subd18_1_275 : subd18_1 [-1, -1, -5] = true := by decide +kernel
theorem subd18_1_276 : subd18_1 [-1, -1, -4] = true := by decide +kernel
theorem subd18_1_277 : subd18_1 [-1, -1, -3] = true := by decide +kernel
theorem subd18_1_278 : subd18_1 [-1, -1, -2] = true := by decide +kernel
theorem subd18_1_279 : subd18_1 [-1, -1, -1] = true := by decide +kernel
theorem subd18_1_280 : subd18_1 [-1, -1, 0] = true := by decide +kernel
theorem subd18_1_281 : subd18_1 [-1, -1, 1] = true := by decide +kernel
theorem subd18_1_282 : subd18_1 [-1, -1, 2] = true := by decide +kernel
theorem subd18_1_283 : subd18_1 [-1, -1, 3] = true := by decide +kernel
theorem subd18_1_284 : subd18_1 [-1, -1, 4] = true := by decide +kernel
theorem subd18_1_285 : subd18_1 [-1, -1, 5] = true := by decide +kernel
theorem subd18_1_286 : subd18_1 [-1, -1, 6] = true := by decide +kernel
theorem subd18_1_287 : subd18_1 [-1, -1, 7] = true := by decide +kernel
theorem sbd18_1_8 : ∀ q ∈ blkd18_1_8, subd18_1 q = true := by
  unfold blkd18_1_8
  exact List.forall_mem_cons.2 ⟨subd18_1_256, List.forall_mem_cons.2 ⟨subd18_1_257, List.forall_mem_cons.2 ⟨subd18_1_258, List.forall_mem_cons.2 ⟨subd18_1_259, List.forall_mem_cons.2 ⟨subd18_1_260, List.forall_mem_cons.2 ⟨subd18_1_261, List.forall_mem_cons.2 ⟨subd18_1_262, List.forall_mem_cons.2 ⟨subd18_1_263, List.forall_mem_cons.2 ⟨subd18_1_264, List.forall_mem_cons.2 ⟨subd18_1_265, List.forall_mem_cons.2 ⟨subd18_1_266, List.forall_mem_cons.2 ⟨subd18_1_267, List.forall_mem_cons.2 ⟨subd18_1_268, List.forall_mem_cons.2 ⟨subd18_1_269, List.forall_mem_cons.2 ⟨subd18_1_270, List.forall_mem_cons.2 ⟨subd18_1_271, List.forall_mem_cons.2 ⟨subd18_1_272, List.forall_mem_cons.2 ⟨subd18_1_273, List.forall_mem_cons.2 ⟨subd18_1_274, List.forall_mem_cons.2 ⟨subd18_1_275, List.forall_mem_cons.2 ⟨subd18_1_276, List.forall_mem_cons.2 ⟨subd18_1_277, List.forall_mem_cons.2 ⟨subd18_1_278, List.forall_mem_cons.2 ⟨subd18_1_279, List.forall_mem_cons.2 ⟨subd18_1_280, List.forall_mem_cons.2 ⟨subd18_1_281, List.forall_mem_cons.2 ⟨subd18_1_282, List.forall_mem_cons.2 ⟨subd18_1_283, List.forall_mem_cons.2 ⟨subd18_1_284, List.forall_mem_cons.2 ⟨subd18_1_285, List.forall_mem_cons.2 ⟨subd18_1_286, List.forall_mem_cons.2 ⟨subd18_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_288 : subd18_1 [-1, 0, -9] = true := by decide +kernel
theorem subd18_1_289 : subd18_1 [-1, 0, -8] = true := by decide +kernel
theorem subd18_1_290 : subd18_1 [-1, 0, -7] = true := by decide +kernel
theorem subd18_1_291 : subd18_1 [-1, 0, -6] = true := by decide +kernel
theorem subd18_1_292 : subd18_1 [-1, 0, -5] = true := by decide +kernel
theorem subd18_1_293 : subd18_1 [-1, 0, -4] = true := by decide +kernel
theorem subd18_1_294 : subd18_1 [-1, 0, -3] = true := by decide +kernel
theorem subd18_1_295 : subd18_1 [-1, 0, -2] = true := by decide +kernel
theorem subd18_1_296 : subd18_1 [-1, 0, -1] = true := by decide +kernel
theorem subd18_1_297 : subd18_1 [-1, 0, 0] = true := by decide +kernel
theorem subd18_1_298 : subd18_1 [-1, 0, 1] = true := by decide +kernel
theorem subd18_1_299 : subd18_1 [-1, 0, 2] = true := by decide +kernel
theorem subd18_1_300 : subd18_1 [-1, 0, 3] = true := by decide +kernel
theorem subd18_1_301 : subd18_1 [-1, 0, 4] = true := by decide +kernel
theorem subd18_1_302 : subd18_1 [-1, 0, 5] = true := by decide +kernel
theorem subd18_1_303 : subd18_1 [-1, 0, 6] = true := by decide +kernel
theorem subd18_1_304 : subd18_1 [-1, 0, 7] = true := by decide +kernel
theorem subd18_1_305 : subd18_1 [-1, 1, -9] = true := by decide +kernel
theorem subd18_1_306 : subd18_1 [-1, 1, -8] = true := by decide +kernel
theorem subd18_1_307 : subd18_1 [-1, 1, -7] = true := by decide +kernel
theorem subd18_1_308 : subd18_1 [-1, 1, -6] = true := by decide +kernel
theorem subd18_1_309 : subd18_1 [-1, 1, -5] = true := by decide +kernel
theorem subd18_1_310 : subd18_1 [-1, 1, -4] = true := by decide +kernel
theorem subd18_1_311 : subd18_1 [-1, 1, -3] = true := by decide +kernel
theorem subd18_1_312 : subd18_1 [-1, 1, -2] = true := by decide +kernel
theorem subd18_1_313 : subd18_1 [-1, 1, -1] = true := by decide +kernel
theorem subd18_1_314 : subd18_1 [-1, 1, 0] = true := by decide +kernel
theorem subd18_1_315 : subd18_1 [-1, 1, 1] = true := by decide +kernel
theorem subd18_1_316 : subd18_1 [-1, 1, 2] = true := by decide +kernel
theorem subd18_1_317 : subd18_1 [-1, 1, 3] = true := by decide +kernel
theorem subd18_1_318 : subd18_1 [-1, 1, 4] = true := by decide +kernel
theorem subd18_1_319 : subd18_1 [-1, 1, 5] = true := by decide +kernel
theorem sbd18_1_9 : ∀ q ∈ blkd18_1_9, subd18_1 q = true := by
  unfold blkd18_1_9
  exact List.forall_mem_cons.2 ⟨subd18_1_288, List.forall_mem_cons.2 ⟨subd18_1_289, List.forall_mem_cons.2 ⟨subd18_1_290, List.forall_mem_cons.2 ⟨subd18_1_291, List.forall_mem_cons.2 ⟨subd18_1_292, List.forall_mem_cons.2 ⟨subd18_1_293, List.forall_mem_cons.2 ⟨subd18_1_294, List.forall_mem_cons.2 ⟨subd18_1_295, List.forall_mem_cons.2 ⟨subd18_1_296, List.forall_mem_cons.2 ⟨subd18_1_297, List.forall_mem_cons.2 ⟨subd18_1_298, List.forall_mem_cons.2 ⟨subd18_1_299, List.forall_mem_cons.2 ⟨subd18_1_300, List.forall_mem_cons.2 ⟨subd18_1_301, List.forall_mem_cons.2 ⟨subd18_1_302, List.forall_mem_cons.2 ⟨subd18_1_303, List.forall_mem_cons.2 ⟨subd18_1_304, List.forall_mem_cons.2 ⟨subd18_1_305, List.forall_mem_cons.2 ⟨subd18_1_306, List.forall_mem_cons.2 ⟨subd18_1_307, List.forall_mem_cons.2 ⟨subd18_1_308, List.forall_mem_cons.2 ⟨subd18_1_309, List.forall_mem_cons.2 ⟨subd18_1_310, List.forall_mem_cons.2 ⟨subd18_1_311, List.forall_mem_cons.2 ⟨subd18_1_312, List.forall_mem_cons.2 ⟨subd18_1_313, List.forall_mem_cons.2 ⟨subd18_1_314, List.forall_mem_cons.2 ⟨subd18_1_315, List.forall_mem_cons.2 ⟨subd18_1_316, List.forall_mem_cons.2 ⟨subd18_1_317, List.forall_mem_cons.2 ⟨subd18_1_318, List.forall_mem_cons.2 ⟨subd18_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_320 : subd18_1 [-1, 1, 6] = true := by decide +kernel
theorem subd18_1_321 : subd18_1 [-1, 2, -9] = true := by decide +kernel
theorem subd18_1_322 : subd18_1 [-1, 2, -8] = true := by decide +kernel
theorem subd18_1_323 : subd18_1 [-1, 2, -7] = true := by decide +kernel
theorem subd18_1_324 : subd18_1 [-1, 2, -6] = true := by decide +kernel
theorem subd18_1_325 : subd18_1 [-1, 2, -5] = true := by decide +kernel
theorem subd18_1_326 : subd18_1 [-1, 2, -4] = true := by decide +kernel
theorem subd18_1_327 : subd18_1 [-1, 2, -3] = true := by decide +kernel
theorem subd18_1_328 : subd18_1 [-1, 2, -2] = true := by decide +kernel
theorem subd18_1_329 : subd18_1 [-1, 2, -1] = true := by decide +kernel
theorem subd18_1_330 : subd18_1 [-1, 2, 0] = true := by decide +kernel
theorem subd18_1_331 : subd18_1 [-1, 2, 1] = true := by decide +kernel
theorem subd18_1_332 : subd18_1 [-1, 2, 2] = true := by decide +kernel
theorem subd18_1_333 : subd18_1 [-1, 2, 3] = true := by decide +kernel
theorem subd18_1_334 : subd18_1 [-1, 2, 4] = true := by decide +kernel
theorem subd18_1_335 : subd18_1 [-1, 2, 5] = true := by decide +kernel
theorem subd18_1_336 : subd18_1 [-1, 3, -9] = true := by decide +kernel
theorem subd18_1_337 : subd18_1 [-1, 3, -8] = true := by decide +kernel
theorem subd18_1_338 : subd18_1 [-1, 3, -7] = true := by decide +kernel
theorem subd18_1_339 : subd18_1 [-1, 3, -6] = true := by decide +kernel
theorem subd18_1_340 : subd18_1 [-1, 3, -5] = true := by decide +kernel
theorem subd18_1_341 : subd18_1 [-1, 3, -4] = true := by decide +kernel
theorem subd18_1_342 : subd18_1 [-1, 3, -3] = true := by decide +kernel
theorem subd18_1_343 : subd18_1 [-1, 3, -2] = true := by decide +kernel
theorem subd18_1_344 : subd18_1 [-1, 3, -1] = true := by decide +kernel
theorem subd18_1_345 : subd18_1 [-1, 3, 0] = true := by decide +kernel
theorem subd18_1_346 : subd18_1 [-1, 3, 1] = true := by decide +kernel
theorem subd18_1_347 : subd18_1 [-1, 3, 2] = true := by decide +kernel
theorem subd18_1_348 : subd18_1 [-1, 3, 3] = true := by decide +kernel
theorem subd18_1_349 : subd18_1 [-1, 3, 4] = true := by decide +kernel
theorem subd18_1_350 : subd18_1 [-1, 3, 5] = true := by decide +kernel
theorem subd18_1_351 : subd18_1 [-1, 4] = true := by decide +kernel
theorem sbd18_1_10 : ∀ q ∈ blkd18_1_10, subd18_1 q = true := by
  unfold blkd18_1_10
  exact List.forall_mem_cons.2 ⟨subd18_1_320, List.forall_mem_cons.2 ⟨subd18_1_321, List.forall_mem_cons.2 ⟨subd18_1_322, List.forall_mem_cons.2 ⟨subd18_1_323, List.forall_mem_cons.2 ⟨subd18_1_324, List.forall_mem_cons.2 ⟨subd18_1_325, List.forall_mem_cons.2 ⟨subd18_1_326, List.forall_mem_cons.2 ⟨subd18_1_327, List.forall_mem_cons.2 ⟨subd18_1_328, List.forall_mem_cons.2 ⟨subd18_1_329, List.forall_mem_cons.2 ⟨subd18_1_330, List.forall_mem_cons.2 ⟨subd18_1_331, List.forall_mem_cons.2 ⟨subd18_1_332, List.forall_mem_cons.2 ⟨subd18_1_333, List.forall_mem_cons.2 ⟨subd18_1_334, List.forall_mem_cons.2 ⟨subd18_1_335, List.forall_mem_cons.2 ⟨subd18_1_336, List.forall_mem_cons.2 ⟨subd18_1_337, List.forall_mem_cons.2 ⟨subd18_1_338, List.forall_mem_cons.2 ⟨subd18_1_339, List.forall_mem_cons.2 ⟨subd18_1_340, List.forall_mem_cons.2 ⟨subd18_1_341, List.forall_mem_cons.2 ⟨subd18_1_342, List.forall_mem_cons.2 ⟨subd18_1_343, List.forall_mem_cons.2 ⟨subd18_1_344, List.forall_mem_cons.2 ⟨subd18_1_345, List.forall_mem_cons.2 ⟨subd18_1_346, List.forall_mem_cons.2 ⟨subd18_1_347, List.forall_mem_cons.2 ⟨subd18_1_348, List.forall_mem_cons.2 ⟨subd18_1_349, List.forall_mem_cons.2 ⟨subd18_1_350, List.forall_mem_cons.2 ⟨subd18_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_352 : subd18_1 [-1, 5] = true := by decide +kernel
theorem subd18_1_353 : subd18_1 [-1, 6] = true := by decide +kernel
theorem subd18_1_354 : subd18_1 [0, -8] = true := by decide +kernel
theorem subd18_1_355 : subd18_1 [0, -7] = true := by decide +kernel
theorem subd18_1_356 : subd18_1 [0, -6] = true := by decide +kernel
theorem subd18_1_357 : subd18_1 [0, -5] = true := by decide +kernel
theorem subd18_1_358 : subd18_1 [0, -4, -5] = true := by decide +kernel
theorem subd18_1_359 : subd18_1 [0, -4, -4] = true := by decide +kernel
theorem subd18_1_360 : subd18_1 [0, -4, -3] = true := by decide +kernel
theorem subd18_1_361 : subd18_1 [0, -4, -2] = true := by decide +kernel
theorem subd18_1_362 : subd18_1 [0, -4, -1] = true := by decide +kernel
theorem subd18_1_363 : subd18_1 [0, -4, 0] = true := by decide +kernel
theorem subd18_1_364 : subd18_1 [0, -4, 1] = true := by decide +kernel
theorem subd18_1_365 : subd18_1 [0, -4, 2] = true := by decide +kernel
theorem subd18_1_366 : subd18_1 [0, -4, 3] = true := by decide +kernel
theorem subd18_1_367 : subd18_1 [0, -4, 4] = true := by decide +kernel
theorem subd18_1_368 : subd18_1 [0, -4, 5] = true := by decide +kernel
theorem subd18_1_369 : subd18_1 [0, -4, 6] = true := by decide +kernel
theorem subd18_1_370 : subd18_1 [0, -4, 7] = true := by decide +kernel
theorem subd18_1_371 : subd18_1 [0, -4, 8] = true := by decide +kernel
theorem subd18_1_372 : subd18_1 [0, -3, -6] = true := by decide +kernel
theorem subd18_1_373 : subd18_1 [0, -3, -5] = true := by decide +kernel
theorem subd18_1_374 : subd18_1 [0, -3, -4] = true := by decide +kernel
theorem subd18_1_375 : subd18_1 [0, -3, -3] = true := by decide +kernel
theorem subd18_1_376 : subd18_1 [0, -3, -2] = true := by decide +kernel
theorem subd18_1_377 : subd18_1 [0, -3, -1] = true := by decide +kernel
theorem subd18_1_378 : subd18_1 [0, -3, 0] = true := by decide +kernel
theorem subd18_1_379 : subd18_1 [0, -3, 1] = true := by decide +kernel
theorem subd18_1_380 : subd18_1 [0, -3, 2] = true := by decide +kernel
theorem subd18_1_381 : subd18_1 [0, -3, 3] = true := by decide +kernel
theorem subd18_1_382 : subd18_1 [0, -3, 4] = true := by decide +kernel
theorem subd18_1_383 : subd18_1 [0, -3, 5] = true := by decide +kernel
theorem sbd18_1_11 : ∀ q ∈ blkd18_1_11, subd18_1 q = true := by
  unfold blkd18_1_11
  exact List.forall_mem_cons.2 ⟨subd18_1_352, List.forall_mem_cons.2 ⟨subd18_1_353, List.forall_mem_cons.2 ⟨subd18_1_354, List.forall_mem_cons.2 ⟨subd18_1_355, List.forall_mem_cons.2 ⟨subd18_1_356, List.forall_mem_cons.2 ⟨subd18_1_357, List.forall_mem_cons.2 ⟨subd18_1_358, List.forall_mem_cons.2 ⟨subd18_1_359, List.forall_mem_cons.2 ⟨subd18_1_360, List.forall_mem_cons.2 ⟨subd18_1_361, List.forall_mem_cons.2 ⟨subd18_1_362, List.forall_mem_cons.2 ⟨subd18_1_363, List.forall_mem_cons.2 ⟨subd18_1_364, List.forall_mem_cons.2 ⟨subd18_1_365, List.forall_mem_cons.2 ⟨subd18_1_366, List.forall_mem_cons.2 ⟨subd18_1_367, List.forall_mem_cons.2 ⟨subd18_1_368, List.forall_mem_cons.2 ⟨subd18_1_369, List.forall_mem_cons.2 ⟨subd18_1_370, List.forall_mem_cons.2 ⟨subd18_1_371, List.forall_mem_cons.2 ⟨subd18_1_372, List.forall_mem_cons.2 ⟨subd18_1_373, List.forall_mem_cons.2 ⟨subd18_1_374, List.forall_mem_cons.2 ⟨subd18_1_375, List.forall_mem_cons.2 ⟨subd18_1_376, List.forall_mem_cons.2 ⟨subd18_1_377, List.forall_mem_cons.2 ⟨subd18_1_378, List.forall_mem_cons.2 ⟨subd18_1_379, List.forall_mem_cons.2 ⟨subd18_1_380, List.forall_mem_cons.2 ⟨subd18_1_381, List.forall_mem_cons.2 ⟨subd18_1_382, List.forall_mem_cons.2 ⟨subd18_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_384 : subd18_1 [0, -3, 6] = true := by decide +kernel
theorem subd18_1_385 : subd18_1 [0, -3, 7] = true := by decide +kernel
theorem subd18_1_386 : subd18_1 [0, -3, 8] = true := by decide +kernel
theorem subd18_1_387 : subd18_1 [0, -2, -7] = true := by decide +kernel
theorem subd18_1_388 : subd18_1 [0, -2, -6] = true := by decide +kernel
theorem subd18_1_389 : subd18_1 [0, -2, -5] = true := by decide +kernel
theorem subd18_1_390 : subd18_1 [0, -2, -4] = true := by decide +kernel
theorem subd18_1_391 : subd18_1 [0, -2, -3] = true := by decide +kernel
theorem subd18_1_392 : subd18_1 [0, -2, -2] = true := by decide +kernel
theorem subd18_1_393 : subd18_1 [0, -2, -1] = true := by decide +kernel
theorem subd18_1_394 : subd18_1 [0, -2, 0] = true := by decide +kernel
theorem subd18_1_395 : subd18_1 [0, -2, 1] = true := by decide +kernel
theorem subd18_1_396 : subd18_1 [0, -2, 2] = true := by decide +kernel
theorem subd18_1_397 : subd18_1 [0, -2, 3] = true := by decide +kernel
theorem subd18_1_398 : subd18_1 [0, -2, 4] = true := by decide +kernel
theorem subd18_1_399 : subd18_1 [0, -2, 5] = true := by decide +kernel
theorem subd18_1_400 : subd18_1 [0, -2, 6] = true := by decide +kernel
theorem subd18_1_401 : subd18_1 [0, -2, 7] = true := by decide +kernel
theorem subd18_1_402 : subd18_1 [0, -2, 8] = true := by decide +kernel
theorem subd18_1_403 : subd18_1 [0, -1, -8] = true := by decide +kernel
theorem subd18_1_404 : subd18_1 [0, -1, -7] = true := by decide +kernel
theorem subd18_1_405 : subd18_1 [0, -1, -6] = true := by decide +kernel
theorem subd18_1_406 : subd18_1 [0, -1, -5] = true := by decide +kernel
theorem subd18_1_407 : subd18_1 [0, -1, -4] = true := by decide +kernel
theorem subd18_1_408 : subd18_1 [0, -1, -3] = true := by decide +kernel
theorem subd18_1_409 : subd18_1 [0, -1, -2] = true := by decide +kernel
theorem subd18_1_410 : subd18_1 [0, -1, -1] = true := by decide +kernel
theorem subd18_1_411 : subd18_1 [0, -1, 0] = true := by decide +kernel
theorem subd18_1_412 : subd18_1 [0, -1, 1] = true := by decide +kernel
theorem subd18_1_413 : subd18_1 [0, -1, 2] = true := by decide +kernel
theorem subd18_1_414 : subd18_1 [0, -1, 3] = true := by decide +kernel
theorem subd18_1_415 : subd18_1 [0, -1, 4] = true := by decide +kernel
theorem sbd18_1_12 : ∀ q ∈ blkd18_1_12, subd18_1 q = true := by
  unfold blkd18_1_12
  exact List.forall_mem_cons.2 ⟨subd18_1_384, List.forall_mem_cons.2 ⟨subd18_1_385, List.forall_mem_cons.2 ⟨subd18_1_386, List.forall_mem_cons.2 ⟨subd18_1_387, List.forall_mem_cons.2 ⟨subd18_1_388, List.forall_mem_cons.2 ⟨subd18_1_389, List.forall_mem_cons.2 ⟨subd18_1_390, List.forall_mem_cons.2 ⟨subd18_1_391, List.forall_mem_cons.2 ⟨subd18_1_392, List.forall_mem_cons.2 ⟨subd18_1_393, List.forall_mem_cons.2 ⟨subd18_1_394, List.forall_mem_cons.2 ⟨subd18_1_395, List.forall_mem_cons.2 ⟨subd18_1_396, List.forall_mem_cons.2 ⟨subd18_1_397, List.forall_mem_cons.2 ⟨subd18_1_398, List.forall_mem_cons.2 ⟨subd18_1_399, List.forall_mem_cons.2 ⟨subd18_1_400, List.forall_mem_cons.2 ⟨subd18_1_401, List.forall_mem_cons.2 ⟨subd18_1_402, List.forall_mem_cons.2 ⟨subd18_1_403, List.forall_mem_cons.2 ⟨subd18_1_404, List.forall_mem_cons.2 ⟨subd18_1_405, List.forall_mem_cons.2 ⟨subd18_1_406, List.forall_mem_cons.2 ⟨subd18_1_407, List.forall_mem_cons.2 ⟨subd18_1_408, List.forall_mem_cons.2 ⟨subd18_1_409, List.forall_mem_cons.2 ⟨subd18_1_410, List.forall_mem_cons.2 ⟨subd18_1_411, List.forall_mem_cons.2 ⟨subd18_1_412, List.forall_mem_cons.2 ⟨subd18_1_413, List.forall_mem_cons.2 ⟨subd18_1_414, List.forall_mem_cons.2 ⟨subd18_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_416 : subd18_1 [0, -1, 5] = true := by decide +kernel
theorem subd18_1_417 : subd18_1 [0, -1, 6] = true := by decide +kernel
theorem subd18_1_418 : subd18_1 [0, -1, 7] = true := by decide +kernel
theorem subd18_1_419 : subd18_1 [0, -1, 8] = true := by decide +kernel
theorem subd18_1_420 : subd18_1 [0, 0, -8] = true := by decide +kernel
theorem subd18_1_421 : subd18_1 [0, 0, -7] = true := by decide +kernel
theorem subd18_1_422 : subd18_1 [0, 0, -6] = true := by decide +kernel
theorem subd18_1_423 : subd18_1 [0, 0, -5] = true := by decide +kernel
theorem subd18_1_424 : subd18_1 [0, 0, -4] = true := by decide +kernel
theorem subd18_1_425 : subd18_1 [0, 0, -3] = true := by decide +kernel
theorem subd18_1_426 : subd18_1 [0, 0, -2] = true := by decide +kernel
theorem subd18_1_427 : subd18_1 [0, 0, -1] = true := by decide +kernel
theorem subd18_1_428 : subd18_1 [0, 0, 0] = true := by decide +kernel
theorem subd18_1_429 : subd18_1 [0, 0, 1] = true := by decide +kernel
theorem subd18_1_430 : subd18_1 [0, 0, 2] = true := by decide +kernel
theorem subd18_1_431 : subd18_1 [0, 0, 3] = true := by decide +kernel
theorem subd18_1_432 : subd18_1 [0, 0, 4] = true := by decide +kernel
theorem subd18_1_433 : subd18_1 [0, 0, 5] = true := by decide +kernel
theorem subd18_1_434 : subd18_1 [0, 0, 6] = true := by decide +kernel
theorem subd18_1_435 : subd18_1 [0, 0, 7] = true := by decide +kernel
theorem subd18_1_436 : subd18_1 [0, 1, -9] = true := by decide +kernel
theorem subd18_1_437 : subd18_1 [0, 1, -8] = true := by decide +kernel
theorem subd18_1_438 : subd18_1 [0, 1, -7] = true := by decide +kernel
theorem subd18_1_439 : subd18_1 [0, 1, -6] = true := by decide +kernel
theorem subd18_1_440 : subd18_1 [0, 1, -5] = true := by decide +kernel
theorem subd18_1_441 : subd18_1 [0, 1, -4] = true := by decide +kernel
theorem subd18_1_442 : subd18_1 [0, 1, -3] = true := by decide +kernel
theorem subd18_1_443 : subd18_1 [0, 1, -2] = true := by decide +kernel
theorem subd18_1_444 : subd18_1 [0, 1, -1] = true := by decide +kernel
theorem subd18_1_445 : subd18_1 [0, 1, 0] = true := by decide +kernel
theorem subd18_1_446 : subd18_1 [0, 1, 1] = true := by decide +kernel
theorem subd18_1_447 : subd18_1 [0, 1, 2] = true := by decide +kernel
theorem sbd18_1_13 : ∀ q ∈ blkd18_1_13, subd18_1 q = true := by
  unfold blkd18_1_13
  exact List.forall_mem_cons.2 ⟨subd18_1_416, List.forall_mem_cons.2 ⟨subd18_1_417, List.forall_mem_cons.2 ⟨subd18_1_418, List.forall_mem_cons.2 ⟨subd18_1_419, List.forall_mem_cons.2 ⟨subd18_1_420, List.forall_mem_cons.2 ⟨subd18_1_421, List.forall_mem_cons.2 ⟨subd18_1_422, List.forall_mem_cons.2 ⟨subd18_1_423, List.forall_mem_cons.2 ⟨subd18_1_424, List.forall_mem_cons.2 ⟨subd18_1_425, List.forall_mem_cons.2 ⟨subd18_1_426, List.forall_mem_cons.2 ⟨subd18_1_427, List.forall_mem_cons.2 ⟨subd18_1_428, List.forall_mem_cons.2 ⟨subd18_1_429, List.forall_mem_cons.2 ⟨subd18_1_430, List.forall_mem_cons.2 ⟨subd18_1_431, List.forall_mem_cons.2 ⟨subd18_1_432, List.forall_mem_cons.2 ⟨subd18_1_433, List.forall_mem_cons.2 ⟨subd18_1_434, List.forall_mem_cons.2 ⟨subd18_1_435, List.forall_mem_cons.2 ⟨subd18_1_436, List.forall_mem_cons.2 ⟨subd18_1_437, List.forall_mem_cons.2 ⟨subd18_1_438, List.forall_mem_cons.2 ⟨subd18_1_439, List.forall_mem_cons.2 ⟨subd18_1_440, List.forall_mem_cons.2 ⟨subd18_1_441, List.forall_mem_cons.2 ⟨subd18_1_442, List.forall_mem_cons.2 ⟨subd18_1_443, List.forall_mem_cons.2 ⟨subd18_1_444, List.forall_mem_cons.2 ⟨subd18_1_445, List.forall_mem_cons.2 ⟨subd18_1_446, List.forall_mem_cons.2 ⟨subd18_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_448 : subd18_1 [0, 1, 3] = true := by decide +kernel
theorem subd18_1_449 : subd18_1 [0, 1, 4] = true := by decide +kernel
theorem subd18_1_450 : subd18_1 [0, 1, 5] = true := by decide +kernel
theorem subd18_1_451 : subd18_1 [0, 1, 6] = true := by decide +kernel
theorem subd18_1_452 : subd18_1 [0, 1, 7] = true := by decide +kernel
theorem subd18_1_453 : subd18_1 [0, 2, -9] = true := by decide +kernel
theorem subd18_1_454 : subd18_1 [0, 2, -8] = true := by decide +kernel
theorem subd18_1_455 : subd18_1 [0, 2, -7] = true := by decide +kernel
theorem subd18_1_456 : subd18_1 [0, 2, -6] = true := by decide +kernel
theorem subd18_1_457 : subd18_1 [0, 2, -5] = true := by decide +kernel
theorem subd18_1_458 : subd18_1 [0, 2, -4] = true := by decide +kernel
theorem subd18_1_459 : subd18_1 [0, 2, -3] = true := by decide +kernel
theorem subd18_1_460 : subd18_1 [0, 2, -2] = true := by decide +kernel
theorem subd18_1_461 : subd18_1 [0, 2, -1] = true := by decide +kernel
theorem subd18_1_462 : subd18_1 [0, 2, 0] = true := by decide +kernel
theorem subd18_1_463 : subd18_1 [0, 2, 1] = true := by decide +kernel
theorem subd18_1_464 : subd18_1 [0, 2, 2] = true := by decide +kernel
theorem subd18_1_465 : subd18_1 [0, 2, 3] = true := by decide +kernel
theorem subd18_1_466 : subd18_1 [0, 2, 4] = true := by decide +kernel
theorem subd18_1_467 : subd18_1 [0, 2, 5] = true := by decide +kernel
theorem subd18_1_468 : subd18_1 [0, 2, 6] = true := by decide +kernel
theorem subd18_1_469 : subd18_1 [0, 3, -9] = true := by decide +kernel
theorem subd18_1_470 : subd18_1 [0, 3, -8] = true := by decide +kernel
theorem subd18_1_471 : subd18_1 [0, 3, -7] = true := by decide +kernel
theorem subd18_1_472 : subd18_1 [0, 3, -6] = true := by decide +kernel
theorem subd18_1_473 : subd18_1 [0, 3, -5] = true := by decide +kernel
theorem subd18_1_474 : subd18_1 [0, 3, -4] = true := by decide +kernel
theorem subd18_1_475 : subd18_1 [0, 3, -3] = true := by decide +kernel
theorem subd18_1_476 : subd18_1 [0, 3, -2] = true := by decide +kernel
theorem subd18_1_477 : subd18_1 [0, 3, -1] = true := by decide +kernel
theorem subd18_1_478 : subd18_1 [0, 3, 0] = true := by decide +kernel
theorem subd18_1_479 : subd18_1 [0, 3, 1] = true := by decide +kernel
theorem sbd18_1_14 : ∀ q ∈ blkd18_1_14, subd18_1 q = true := by
  unfold blkd18_1_14
  exact List.forall_mem_cons.2 ⟨subd18_1_448, List.forall_mem_cons.2 ⟨subd18_1_449, List.forall_mem_cons.2 ⟨subd18_1_450, List.forall_mem_cons.2 ⟨subd18_1_451, List.forall_mem_cons.2 ⟨subd18_1_452, List.forall_mem_cons.2 ⟨subd18_1_453, List.forall_mem_cons.2 ⟨subd18_1_454, List.forall_mem_cons.2 ⟨subd18_1_455, List.forall_mem_cons.2 ⟨subd18_1_456, List.forall_mem_cons.2 ⟨subd18_1_457, List.forall_mem_cons.2 ⟨subd18_1_458, List.forall_mem_cons.2 ⟨subd18_1_459, List.forall_mem_cons.2 ⟨subd18_1_460, List.forall_mem_cons.2 ⟨subd18_1_461, List.forall_mem_cons.2 ⟨subd18_1_462, List.forall_mem_cons.2 ⟨subd18_1_463, List.forall_mem_cons.2 ⟨subd18_1_464, List.forall_mem_cons.2 ⟨subd18_1_465, List.forall_mem_cons.2 ⟨subd18_1_466, List.forall_mem_cons.2 ⟨subd18_1_467, List.forall_mem_cons.2 ⟨subd18_1_468, List.forall_mem_cons.2 ⟨subd18_1_469, List.forall_mem_cons.2 ⟨subd18_1_470, List.forall_mem_cons.2 ⟨subd18_1_471, List.forall_mem_cons.2 ⟨subd18_1_472, List.forall_mem_cons.2 ⟨subd18_1_473, List.forall_mem_cons.2 ⟨subd18_1_474, List.forall_mem_cons.2 ⟨subd18_1_475, List.forall_mem_cons.2 ⟨subd18_1_476, List.forall_mem_cons.2 ⟨subd18_1_477, List.forall_mem_cons.2 ⟨subd18_1_478, List.forall_mem_cons.2 ⟨subd18_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_480 : subd18_1 [0, 3, 2] = true := by decide +kernel
theorem subd18_1_481 : subd18_1 [0, 3, 3] = true := by decide +kernel
theorem subd18_1_482 : subd18_1 [0, 3, 4] = true := by decide +kernel
theorem subd18_1_483 : subd18_1 [0, 3, 5] = true := by decide +kernel
theorem subd18_1_484 : subd18_1 [0, 4, -9] = true := by decide +kernel
theorem subd18_1_485 : subd18_1 [0, 4, -8] = true := by decide +kernel
theorem subd18_1_486 : subd18_1 [0, 4, -7] = true := by decide +kernel
theorem subd18_1_487 : subd18_1 [0, 4, -6] = true := by decide +kernel
theorem subd18_1_488 : subd18_1 [0, 4, -5] = true := by decide +kernel
theorem subd18_1_489 : subd18_1 [0, 4, -4] = true := by decide +kernel
theorem subd18_1_490 : subd18_1 [0, 4, -3] = true := by decide +kernel
theorem subd18_1_491 : subd18_1 [0, 4, -2] = true := by decide +kernel
theorem subd18_1_492 : subd18_1 [0, 4, -1] = true := by decide +kernel
theorem subd18_1_493 : subd18_1 [0, 4, 0] = true := by decide +kernel
theorem subd18_1_494 : subd18_1 [0, 4, 1] = true := by decide +kernel
theorem subd18_1_495 : subd18_1 [0, 4, 2] = true := by decide +kernel
theorem subd18_1_496 : subd18_1 [0, 4, 3] = true := by decide +kernel
theorem subd18_1_497 : subd18_1 [0, 4, 4] = true := by decide +kernel
theorem subd18_1_498 : subd18_1 [0, 5] = true := by decide +kernel
theorem subd18_1_499 : subd18_1 [0, 6] = true := by decide +kernel
theorem subd18_1_500 : subd18_1 [0, 7] = true := by decide +kernel
theorem subd18_1_501 : subd18_1 [1, -7] = true := by decide +kernel
theorem subd18_1_502 : subd18_1 [1, -6] = true := by decide +kernel
theorem subd18_1_503 : subd18_1 [1, -5] = true := by decide +kernel
theorem subd18_1_504 : subd18_1 [1, -4] = true := by decide +kernel
theorem subd18_1_505 : subd18_1 [1, -3, -6] = true := by decide +kernel
theorem subd18_1_506 : subd18_1 [1, -3, -5] = true := by decide +kernel
theorem subd18_1_507 : subd18_1 [1, -3, -4] = true := by decide +kernel
theorem subd18_1_508 : subd18_1 [1, -3, -3] = true := by decide +kernel
theorem subd18_1_509 : subd18_1 [1, -3, -2] = true := by decide +kernel
theorem subd18_1_510 : subd18_1 [1, -3, -1] = true := by decide +kernel
theorem subd18_1_511 : subd18_1 [1, -3, 0] = true := by decide +kernel
theorem sbd18_1_15 : ∀ q ∈ blkd18_1_15, subd18_1 q = true := by
  unfold blkd18_1_15
  exact List.forall_mem_cons.2 ⟨subd18_1_480, List.forall_mem_cons.2 ⟨subd18_1_481, List.forall_mem_cons.2 ⟨subd18_1_482, List.forall_mem_cons.2 ⟨subd18_1_483, List.forall_mem_cons.2 ⟨subd18_1_484, List.forall_mem_cons.2 ⟨subd18_1_485, List.forall_mem_cons.2 ⟨subd18_1_486, List.forall_mem_cons.2 ⟨subd18_1_487, List.forall_mem_cons.2 ⟨subd18_1_488, List.forall_mem_cons.2 ⟨subd18_1_489, List.forall_mem_cons.2 ⟨subd18_1_490, List.forall_mem_cons.2 ⟨subd18_1_491, List.forall_mem_cons.2 ⟨subd18_1_492, List.forall_mem_cons.2 ⟨subd18_1_493, List.forall_mem_cons.2 ⟨subd18_1_494, List.forall_mem_cons.2 ⟨subd18_1_495, List.forall_mem_cons.2 ⟨subd18_1_496, List.forall_mem_cons.2 ⟨subd18_1_497, List.forall_mem_cons.2 ⟨subd18_1_498, List.forall_mem_cons.2 ⟨subd18_1_499, List.forall_mem_cons.2 ⟨subd18_1_500, List.forall_mem_cons.2 ⟨subd18_1_501, List.forall_mem_cons.2 ⟨subd18_1_502, List.forall_mem_cons.2 ⟨subd18_1_503, List.forall_mem_cons.2 ⟨subd18_1_504, List.forall_mem_cons.2 ⟨subd18_1_505, List.forall_mem_cons.2 ⟨subd18_1_506, List.forall_mem_cons.2 ⟨subd18_1_507, List.forall_mem_cons.2 ⟨subd18_1_508, List.forall_mem_cons.2 ⟨subd18_1_509, List.forall_mem_cons.2 ⟨subd18_1_510, List.forall_mem_cons.2 ⟨subd18_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_512 : subd18_1 [1, -3, 1] = true := by decide +kernel
theorem subd18_1_513 : subd18_1 [1, -3, 2] = true := by decide +kernel
theorem subd18_1_514 : subd18_1 [1, -3, 3] = true := by decide +kernel
theorem subd18_1_515 : subd18_1 [1, -3, 4] = true := by decide +kernel
theorem subd18_1_516 : subd18_1 [1, -3, 5] = true := by decide +kernel
theorem subd18_1_517 : subd18_1 [1, -3, 6] = true := by decide +kernel
theorem subd18_1_518 : subd18_1 [1, -3, 7] = true := by decide +kernel
theorem subd18_1_519 : subd18_1 [1, -3, 8] = true := by decide +kernel
theorem subd18_1_520 : subd18_1 [1, -2, -6] = true := by decide +kernel
theorem subd18_1_521 : subd18_1 [1, -2, -5] = true := by decide +kernel
theorem subd18_1_522 : subd18_1 [1, -2, -4] = true := by decide +kernel
theorem subd18_1_523 : subd18_1 [1, -2, -3] = true := by decide +kernel
theorem subd18_1_524 : subd18_1 [1, -2, -2] = true := by decide +kernel
theorem subd18_1_525 : subd18_1 [1, -2, -1] = true := by decide +kernel
theorem subd18_1_526 : subd18_1 [1, -2, 0] = true := by decide +kernel
theorem subd18_1_527 : subd18_1 [1, -2, 1] = true := by decide +kernel
theorem subd18_1_528 : subd18_1 [1, -2, 2] = true := by decide +kernel
theorem subd18_1_529 : subd18_1 [1, -2, 3] = true := by decide +kernel
theorem subd18_1_530 : subd18_1 [1, -2, 4] = true := by decide +kernel
theorem subd18_1_531 : subd18_1 [1, -2, 5] = true := by decide +kernel
theorem subd18_1_532 : subd18_1 [1, -2, 6] = true := by decide +kernel
theorem subd18_1_533 : subd18_1 [1, -2, 7] = true := by decide +kernel
theorem subd18_1_534 : subd18_1 [1, -2, 8] = true := by decide +kernel
theorem subd18_1_535 : subd18_1 [1, -1, -7] = true := by decide +kernel
theorem subd18_1_536 : subd18_1 [1, -1, -6] = true := by decide +kernel
theorem subd18_1_537 : subd18_1 [1, -1, -5] = true := by decide +kernel
theorem subd18_1_538 : subd18_1 [1, -1, -4] = true := by decide +kernel
theorem subd18_1_539 : subd18_1 [1, -1, -3] = true := by decide +kernel
theorem subd18_1_540 : subd18_1 [1, -1, -2] = true := by decide +kernel
theorem subd18_1_541 : subd18_1 [1, -1, -1] = true := by decide +kernel
theorem subd18_1_542 : subd18_1 [1, -1, 0] = true := by decide +kernel
theorem subd18_1_543 : subd18_1 [1, -1, 1] = true := by decide +kernel
theorem sbd18_1_16 : ∀ q ∈ blkd18_1_16, subd18_1 q = true := by
  unfold blkd18_1_16
  exact List.forall_mem_cons.2 ⟨subd18_1_512, List.forall_mem_cons.2 ⟨subd18_1_513, List.forall_mem_cons.2 ⟨subd18_1_514, List.forall_mem_cons.2 ⟨subd18_1_515, List.forall_mem_cons.2 ⟨subd18_1_516, List.forall_mem_cons.2 ⟨subd18_1_517, List.forall_mem_cons.2 ⟨subd18_1_518, List.forall_mem_cons.2 ⟨subd18_1_519, List.forall_mem_cons.2 ⟨subd18_1_520, List.forall_mem_cons.2 ⟨subd18_1_521, List.forall_mem_cons.2 ⟨subd18_1_522, List.forall_mem_cons.2 ⟨subd18_1_523, List.forall_mem_cons.2 ⟨subd18_1_524, List.forall_mem_cons.2 ⟨subd18_1_525, List.forall_mem_cons.2 ⟨subd18_1_526, List.forall_mem_cons.2 ⟨subd18_1_527, List.forall_mem_cons.2 ⟨subd18_1_528, List.forall_mem_cons.2 ⟨subd18_1_529, List.forall_mem_cons.2 ⟨subd18_1_530, List.forall_mem_cons.2 ⟨subd18_1_531, List.forall_mem_cons.2 ⟨subd18_1_532, List.forall_mem_cons.2 ⟨subd18_1_533, List.forall_mem_cons.2 ⟨subd18_1_534, List.forall_mem_cons.2 ⟨subd18_1_535, List.forall_mem_cons.2 ⟨subd18_1_536, List.forall_mem_cons.2 ⟨subd18_1_537, List.forall_mem_cons.2 ⟨subd18_1_538, List.forall_mem_cons.2 ⟨subd18_1_539, List.forall_mem_cons.2 ⟨subd18_1_540, List.forall_mem_cons.2 ⟨subd18_1_541, List.forall_mem_cons.2 ⟨subd18_1_542, List.forall_mem_cons.2 ⟨subd18_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_544 : subd18_1 [1, -1, 2] = true := by decide +kernel
theorem subd18_1_545 : subd18_1 [1, -1, 3] = true := by decide +kernel
theorem subd18_1_546 : subd18_1 [1, -1, 4] = true := by decide +kernel
theorem subd18_1_547 : subd18_1 [1, -1, 5] = true := by decide +kernel
theorem subd18_1_548 : subd18_1 [1, -1, 6] = true := by decide +kernel
theorem subd18_1_549 : subd18_1 [1, -1, 7] = true := by decide +kernel
theorem subd18_1_550 : subd18_1 [1, -1, 8] = true := by decide +kernel
theorem subd18_1_551 : subd18_1 [1, 0, -8] = true := by decide +kernel
theorem subd18_1_552 : subd18_1 [1, 0, -7] = true := by decide +kernel
theorem subd18_1_553 : subd18_1 [1, 0, -6] = true := by decide +kernel
theorem subd18_1_554 : subd18_1 [1, 0, -5] = true := by decide +kernel
theorem subd18_1_555 : subd18_1 [1, 0, -4] = true := by decide +kernel
theorem subd18_1_556 : subd18_1 [1, 0, -3] = true := by decide +kernel
theorem subd18_1_557 : subd18_1 [1, 0, -2] = true := by decide +kernel
theorem subd18_1_558 : subd18_1 [1, 0, -1] = true := by decide +kernel
theorem subd18_1_559 : subd18_1 [1, 0, 0] = true := by decide +kernel
theorem subd18_1_560 : subd18_1 [1, 0, 1] = true := by decide +kernel
theorem subd18_1_561 : subd18_1 [1, 0, 2] = true := by decide +kernel
theorem subd18_1_562 : subd18_1 [1, 0, 3] = true := by decide +kernel
theorem subd18_1_563 : subd18_1 [1, 0, 4] = true := by decide +kernel
theorem subd18_1_564 : subd18_1 [1, 0, 5] = true := by decide +kernel
theorem subd18_1_565 : subd18_1 [1, 0, 6] = true := by decide +kernel
theorem subd18_1_566 : subd18_1 [1, 0, 7] = true := by decide +kernel
theorem subd18_1_567 : subd18_1 [1, 0, 8] = true := by decide +kernel
theorem subd18_1_568 : subd18_1 [1, 1, -8] = true := by decide +kernel
theorem subd18_1_569 : subd18_1 [1, 1, -7] = true := by decide +kernel
theorem subd18_1_570 : subd18_1 [1, 1, -6] = true := by decide +kernel
theorem subd18_1_571 : subd18_1 [1, 1, -5] = true := by decide +kernel
theorem subd18_1_572 : subd18_1 [1, 1, -4] = true := by decide +kernel
theorem subd18_1_573 : subd18_1 [1, 1, -3] = true := by decide +kernel
theorem subd18_1_574 : subd18_1 [1, 1, -2] = true := by decide +kernel
theorem subd18_1_575 : subd18_1 [1, 1, -1] = true := by decide +kernel
theorem sbd18_1_17 : ∀ q ∈ blkd18_1_17, subd18_1 q = true := by
  unfold blkd18_1_17
  exact List.forall_mem_cons.2 ⟨subd18_1_544, List.forall_mem_cons.2 ⟨subd18_1_545, List.forall_mem_cons.2 ⟨subd18_1_546, List.forall_mem_cons.2 ⟨subd18_1_547, List.forall_mem_cons.2 ⟨subd18_1_548, List.forall_mem_cons.2 ⟨subd18_1_549, List.forall_mem_cons.2 ⟨subd18_1_550, List.forall_mem_cons.2 ⟨subd18_1_551, List.forall_mem_cons.2 ⟨subd18_1_552, List.forall_mem_cons.2 ⟨subd18_1_553, List.forall_mem_cons.2 ⟨subd18_1_554, List.forall_mem_cons.2 ⟨subd18_1_555, List.forall_mem_cons.2 ⟨subd18_1_556, List.forall_mem_cons.2 ⟨subd18_1_557, List.forall_mem_cons.2 ⟨subd18_1_558, List.forall_mem_cons.2 ⟨subd18_1_559, List.forall_mem_cons.2 ⟨subd18_1_560, List.forall_mem_cons.2 ⟨subd18_1_561, List.forall_mem_cons.2 ⟨subd18_1_562, List.forall_mem_cons.2 ⟨subd18_1_563, List.forall_mem_cons.2 ⟨subd18_1_564, List.forall_mem_cons.2 ⟨subd18_1_565, List.forall_mem_cons.2 ⟨subd18_1_566, List.forall_mem_cons.2 ⟨subd18_1_567, List.forall_mem_cons.2 ⟨subd18_1_568, List.forall_mem_cons.2 ⟨subd18_1_569, List.forall_mem_cons.2 ⟨subd18_1_570, List.forall_mem_cons.2 ⟨subd18_1_571, List.forall_mem_cons.2 ⟨subd18_1_572, List.forall_mem_cons.2 ⟨subd18_1_573, List.forall_mem_cons.2 ⟨subd18_1_574, List.forall_mem_cons.2 ⟨subd18_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
