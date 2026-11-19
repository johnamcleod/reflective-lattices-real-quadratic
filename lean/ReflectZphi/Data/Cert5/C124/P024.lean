import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_10_96 : subd6_10 [-1, 0, -6] = true := by decide +kernel
theorem subd6_10_97 : subd6_10 [-1, 0, -5] = true := by decide +kernel
theorem subd6_10_98 : subd6_10 [-1, 0, -4] = true := by decide +kernel
theorem subd6_10_99 : subd6_10 [-1, 0, -3] = true := by decide +kernel
theorem subd6_10_100 : subd6_10 [-1, 0, -2] = true := by decide +kernel
theorem subd6_10_101 : subd6_10 [-1, 0, -1] = true := by decide +kernel
theorem subd6_10_102 : subd6_10 [-1, 0, 0] = true := by decide +kernel
theorem subd6_10_103 : subd6_10 [-1, 0, 1] = true := by decide +kernel
theorem subd6_10_104 : subd6_10 [-1, 0, 2] = true := by decide +kernel
theorem subd6_10_105 : subd6_10 [-1, 0, 3] = true := by decide +kernel
theorem subd6_10_106 : subd6_10 [-1, 0, 4] = true := by decide +kernel
theorem subd6_10_107 : subd6_10 [-1, 0, 5] = true := by decide +kernel
theorem subd6_10_108 : subd6_10 [-1, 0, 6] = true := by decide +kernel
theorem subd6_10_109 : subd6_10 [-1, 0, 7] = true := by decide +kernel
theorem subd6_10_110 : subd6_10 [-1, 0, 8] = true := by decide +kernel
theorem subd6_10_111 : subd6_10 [-1, 0, 9] = true := by decide +kernel
theorem subd6_10_112 : subd6_10 [-1, 0, 10] = true := by decide +kernel
theorem subd6_10_113 : subd6_10 [-1, 1, -10] = true := by decide +kernel
theorem subd6_10_114 : subd6_10 [-1, 1, -9] = true := by decide +kernel
theorem subd6_10_115 : subd6_10 [-1, 1, -8] = true := by decide +kernel
theorem subd6_10_116 : subd6_10 [-1, 1, -7] = true := by decide +kernel
theorem subd6_10_117 : subd6_10 [-1, 1, -6] = true := by decide +kernel
theorem subd6_10_118 : subd6_10 [-1, 1, -5] = true := by decide +kernel
theorem subd6_10_119 : subd6_10 [-1, 1, -4] = true := by decide +kernel
theorem subd6_10_120 : subd6_10 [-1, 1, -3] = true := by decide +kernel
theorem subd6_10_121 : subd6_10 [-1, 1, -2] = true := by decide +kernel
theorem subd6_10_122 : subd6_10 [-1, 1, -1] = true := by decide +kernel
theorem subd6_10_123 : subd6_10 [-1, 1, 0] = true := by decide +kernel
theorem subd6_10_124 : subd6_10 [-1, 1, 1] = true := by decide +kernel
theorem subd6_10_125 : subd6_10 [-1, 1, 2] = true := by decide +kernel
theorem subd6_10_126 : subd6_10 [-1, 1, 3] = true := by decide +kernel
theorem subd6_10_127 : subd6_10 [-1, 1, 4] = true := by decide +kernel
theorem sbd6_10_3 : ∀ q ∈ blkd6_10_3, subd6_10 q = true := by
  unfold blkd6_10_3
  exact List.forall_mem_cons.2 ⟨subd6_10_96, List.forall_mem_cons.2 ⟨subd6_10_97, List.forall_mem_cons.2 ⟨subd6_10_98, List.forall_mem_cons.2 ⟨subd6_10_99, List.forall_mem_cons.2 ⟨subd6_10_100, List.forall_mem_cons.2 ⟨subd6_10_101, List.forall_mem_cons.2 ⟨subd6_10_102, List.forall_mem_cons.2 ⟨subd6_10_103, List.forall_mem_cons.2 ⟨subd6_10_104, List.forall_mem_cons.2 ⟨subd6_10_105, List.forall_mem_cons.2 ⟨subd6_10_106, List.forall_mem_cons.2 ⟨subd6_10_107, List.forall_mem_cons.2 ⟨subd6_10_108, List.forall_mem_cons.2 ⟨subd6_10_109, List.forall_mem_cons.2 ⟨subd6_10_110, List.forall_mem_cons.2 ⟨subd6_10_111, List.forall_mem_cons.2 ⟨subd6_10_112, List.forall_mem_cons.2 ⟨subd6_10_113, List.forall_mem_cons.2 ⟨subd6_10_114, List.forall_mem_cons.2 ⟨subd6_10_115, List.forall_mem_cons.2 ⟨subd6_10_116, List.forall_mem_cons.2 ⟨subd6_10_117, List.forall_mem_cons.2 ⟨subd6_10_118, List.forall_mem_cons.2 ⟨subd6_10_119, List.forall_mem_cons.2 ⟨subd6_10_120, List.forall_mem_cons.2 ⟨subd6_10_121, List.forall_mem_cons.2 ⟨subd6_10_122, List.forall_mem_cons.2 ⟨subd6_10_123, List.forall_mem_cons.2 ⟨subd6_10_124, List.forall_mem_cons.2 ⟨subd6_10_125, List.forall_mem_cons.2 ⟨subd6_10_126, List.forall_mem_cons.2 ⟨subd6_10_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_10_128 : subd6_10 [-1, 1, 5] = true := by decide +kernel
theorem subd6_10_129 : subd6_10 [-1, 1, 6] = true := by decide +kernel
theorem subd6_10_130 : subd6_10 [-1, 1, 7] = true := by decide +kernel
theorem subd6_10_131 : subd6_10 [-1, 1, 8] = true := by decide +kernel
theorem subd6_10_132 : subd6_10 [-1, 1, 9] = true := by decide +kernel
theorem subd6_10_133 : subd6_10 [-1, 2, -8] = true := by decide +kernel
theorem subd6_10_134 : subd6_10 [-1, 2, -7] = true := by decide +kernel
theorem subd6_10_135 : subd6_10 [-1, 2, -6] = true := by decide +kernel
theorem subd6_10_136 : subd6_10 [-1, 2, -5] = true := by decide +kernel
theorem subd6_10_137 : subd6_10 [-1, 2, -4] = true := by decide +kernel
theorem subd6_10_138 : subd6_10 [-1, 2, -3] = true := by decide +kernel
theorem subd6_10_139 : subd6_10 [-1, 2, -2] = true := by decide +kernel
theorem subd6_10_140 : subd6_10 [-1, 2, -1] = true := by decide +kernel
theorem subd6_10_141 : subd6_10 [-1, 2, 0] = true := by decide +kernel
theorem subd6_10_142 : subd6_10 [-1, 2, 1] = true := by decide +kernel
theorem subd6_10_143 : subd6_10 [-1, 2, 2] = true := by decide +kernel
theorem subd6_10_144 : subd6_10 [-1, 2, 3] = true := by decide +kernel
theorem subd6_10_145 : subd6_10 [-1, 2, 4] = true := by decide +kernel
theorem subd6_10_146 : subd6_10 [-1, 2, 5] = true := by decide +kernel
theorem subd6_10_147 : subd6_10 [-1, 2, 6] = true := by decide +kernel
theorem subd6_10_148 : subd6_10 [-1, 2, 7] = true := by decide +kernel
theorem subd6_10_149 : subd6_10 [0, -3] = true := by decide +kernel
theorem subd6_10_150 : subd6_10 [0, -2, -8] = true := by decide +kernel
theorem subd6_10_151 : subd6_10 [0, -2, -7] = true := by decide +kernel
theorem subd6_10_152 : subd6_10 [0, -2, -6] = true := by decide +kernel
theorem subd6_10_153 : subd6_10 [0, -2, -5] = true := by decide +kernel
theorem subd6_10_154 : subd6_10 [0, -2, -4] = true := by decide +kernel
theorem subd6_10_155 : subd6_10 [0, -2, -3] = true := by decide +kernel
theorem subd6_10_156 : subd6_10 [0, -2, -2] = true := by decide +kernel
theorem subd6_10_157 : subd6_10 [0, -2, -1] = true := by decide +kernel
theorem subd6_10_158 : subd6_10 [0, -2, 0] = true := by decide +kernel
theorem subd6_10_159 : subd6_10 [0, -2, 1] = true := by decide +kernel
theorem sbd6_10_4 : ∀ q ∈ blkd6_10_4, subd6_10 q = true := by
  unfold blkd6_10_4
  exact List.forall_mem_cons.2 ⟨subd6_10_128, List.forall_mem_cons.2 ⟨subd6_10_129, List.forall_mem_cons.2 ⟨subd6_10_130, List.forall_mem_cons.2 ⟨subd6_10_131, List.forall_mem_cons.2 ⟨subd6_10_132, List.forall_mem_cons.2 ⟨subd6_10_133, List.forall_mem_cons.2 ⟨subd6_10_134, List.forall_mem_cons.2 ⟨subd6_10_135, List.forall_mem_cons.2 ⟨subd6_10_136, List.forall_mem_cons.2 ⟨subd6_10_137, List.forall_mem_cons.2 ⟨subd6_10_138, List.forall_mem_cons.2 ⟨subd6_10_139, List.forall_mem_cons.2 ⟨subd6_10_140, List.forall_mem_cons.2 ⟨subd6_10_141, List.forall_mem_cons.2 ⟨subd6_10_142, List.forall_mem_cons.2 ⟨subd6_10_143, List.forall_mem_cons.2 ⟨subd6_10_144, List.forall_mem_cons.2 ⟨subd6_10_145, List.forall_mem_cons.2 ⟨subd6_10_146, List.forall_mem_cons.2 ⟨subd6_10_147, List.forall_mem_cons.2 ⟨subd6_10_148, List.forall_mem_cons.2 ⟨subd6_10_149, List.forall_mem_cons.2 ⟨subd6_10_150, List.forall_mem_cons.2 ⟨subd6_10_151, List.forall_mem_cons.2 ⟨subd6_10_152, List.forall_mem_cons.2 ⟨subd6_10_153, List.forall_mem_cons.2 ⟨subd6_10_154, List.forall_mem_cons.2 ⟨subd6_10_155, List.forall_mem_cons.2 ⟨subd6_10_156, List.forall_mem_cons.2 ⟨subd6_10_157, List.forall_mem_cons.2 ⟨subd6_10_158, List.forall_mem_cons.2 ⟨subd6_10_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_10_160 : subd6_10 [0, -2, 2] = true := by decide +kernel
theorem subd6_10_161 : subd6_10 [0, -2, 3] = true := by decide +kernel
theorem subd6_10_162 : subd6_10 [0, -2, 4] = true := by decide +kernel
theorem subd6_10_163 : subd6_10 [0, -2, 5] = true := by decide +kernel
theorem subd6_10_164 : subd6_10 [0, -2, 6] = true := by decide +kernel
theorem subd6_10_165 : subd6_10 [0, -2, 7] = true := by decide +kernel
theorem subd6_10_166 : subd6_10 [0, -1, -11] = true := by decide +kernel
theorem subd6_10_167 : subd6_10 [0, -1, -10] = true := by decide +kernel
theorem subd6_10_168 : subd6_10 [0, -1, -9] = true := by decide +kernel
theorem subd6_10_169 : subd6_10 [0, -1, -8] = true := by decide +kernel
theorem subd6_10_170 : subd6_10 [0, -1, -7] = true := by decide +kernel
theorem subd6_10_171 : subd6_10 [0, -1, -6] = true := by decide +kernel
theorem subd6_10_172 : subd6_10 [0, -1, -5] = true := by decide +kernel
theorem subd6_10_173 : subd6_10 [0, -1, -4] = true := by decide +kernel
theorem subd6_10_174 : subd6_10 [0, -1, -3] = true := by decide +kernel
theorem subd6_10_175 : subd6_10 [0, -1, -2] = true := by decide +kernel
theorem subd6_10_176 : subd6_10 [0, -1, -1] = true := by decide +kernel
theorem subd6_10_177 : subd6_10 [0, -1, 0] = true := by decide +kernel
theorem subd6_10_178 : subd6_10 [0, -1, 1] = true := by decide +kernel
theorem subd6_10_179 : subd6_10 [0, -1, 2] = true := by decide +kernel
theorem subd6_10_180 : subd6_10 [0, -1, 3] = true := by decide +kernel
theorem subd6_10_181 : subd6_10 [0, -1, 4] = true := by decide +kernel
theorem subd6_10_182 : subd6_10 [0, -1, 5] = true := by decide +kernel
theorem subd6_10_183 : subd6_10 [0, -1, 6] = true := by decide +kernel
theorem subd6_10_184 : subd6_10 [0, -1, 7] = true := by decide +kernel
theorem subd6_10_185 : subd6_10 [0, -1, 8] = true := by decide +kernel
theorem subd6_10_186 : subd6_10 [0, -1, 9] = true := by decide +kernel
theorem subd6_10_187 : subd6_10 [0, -1, 10] = true := by decide +kernel
theorem subd6_10_188 : subd6_10 [0, 0, -11] = true := by decide +kernel
theorem subd6_10_189 : subd6_10 [0, 0, -10] = true := by decide +kernel
theorem subd6_10_190 : subd6_10 [0, 0, -9] = true := by decide +kernel
theorem subd6_10_191 : subd6_10 [0, 0, -8] = true := by decide +kernel
theorem sbd6_10_5 : ∀ q ∈ blkd6_10_5, subd6_10 q = true := by
  unfold blkd6_10_5
  exact List.forall_mem_cons.2 ⟨subd6_10_160, List.forall_mem_cons.2 ⟨subd6_10_161, List.forall_mem_cons.2 ⟨subd6_10_162, List.forall_mem_cons.2 ⟨subd6_10_163, List.forall_mem_cons.2 ⟨subd6_10_164, List.forall_mem_cons.2 ⟨subd6_10_165, List.forall_mem_cons.2 ⟨subd6_10_166, List.forall_mem_cons.2 ⟨subd6_10_167, List.forall_mem_cons.2 ⟨subd6_10_168, List.forall_mem_cons.2 ⟨subd6_10_169, List.forall_mem_cons.2 ⟨subd6_10_170, List.forall_mem_cons.2 ⟨subd6_10_171, List.forall_mem_cons.2 ⟨subd6_10_172, List.forall_mem_cons.2 ⟨subd6_10_173, List.forall_mem_cons.2 ⟨subd6_10_174, List.forall_mem_cons.2 ⟨subd6_10_175, List.forall_mem_cons.2 ⟨subd6_10_176, List.forall_mem_cons.2 ⟨subd6_10_177, List.forall_mem_cons.2 ⟨subd6_10_178, List.forall_mem_cons.2 ⟨subd6_10_179, List.forall_mem_cons.2 ⟨subd6_10_180, List.forall_mem_cons.2 ⟨subd6_10_181, List.forall_mem_cons.2 ⟨subd6_10_182, List.forall_mem_cons.2 ⟨subd6_10_183, List.forall_mem_cons.2 ⟨subd6_10_184, List.forall_mem_cons.2 ⟨subd6_10_185, List.forall_mem_cons.2 ⟨subd6_10_186, List.forall_mem_cons.2 ⟨subd6_10_187, List.forall_mem_cons.2 ⟨subd6_10_188, List.forall_mem_cons.2 ⟨subd6_10_189, List.forall_mem_cons.2 ⟨subd6_10_190, List.forall_mem_cons.2 ⟨subd6_10_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_10_192 : subd6_10 [0, 0, -7] = true := by decide +kernel
theorem subd6_10_193 : subd6_10 [0, 0, -6] = true := by decide +kernel
theorem subd6_10_194 : subd6_10 [0, 0, -5] = true := by decide +kernel
theorem subd6_10_195 : subd6_10 [0, 0, -4] = true := by decide +kernel
theorem subd6_10_196 : subd6_10 [0, 0, -3] = true := by decide +kernel
theorem subd6_10_197 : subd6_10 [0, 0, -2] = true := by decide +kernel
theorem subd6_10_198 : subd6_10 [0, 0, -1] = true := by decide +kernel
theorem subd6_10_199 : subd6_10 [0, 0, 0] = true := by decide +kernel
theorem subd6_10_200 : subd6_10 [0, 0, 1] = true := by decide +kernel
theorem subd6_10_201 : subd6_10 [0, 0, 2] = true := by decide +kernel
theorem subd6_10_202 : subd6_10 [0, 0, 3] = true := by decide +kernel
theorem subd6_10_203 : subd6_10 [0, 0, 4] = true := by decide +kernel
theorem subd6_10_204 : subd6_10 [0, 0, 5] = true := by decide +kernel
theorem subd6_10_205 : subd6_10 [0, 0, 6] = true := by decide +kernel
theorem subd6_10_206 : subd6_10 [0, 0, 7] = true := by decide +kernel
theorem subd6_10_207 : subd6_10 [0, 0, 8] = true := by decide +kernel
theorem subd6_10_208 : subd6_10 [0, 0, 9] = true := by decide +kernel
theorem subd6_10_209 : subd6_10 [0, 0, 10] = true := by decide +kernel
theorem subd6_10_210 : subd6_10 [0, 1, -11] = true := by decide +kernel
theorem subd6_10_211 : subd6_10 [0, 1, -10] = true := by decide +kernel
theorem subd6_10_212 : subd6_10 [0, 1, -9] = true := by decide +kernel
theorem subd6_10_213 : subd6_10 [0, 1, -8] = true := by decide +kernel
theorem subd6_10_214 : subd6_10 [0, 1, -7] = true := by decide +kernel
theorem subd6_10_215 : subd6_10 [0, 1, -6] = true := by decide +kernel
theorem subd6_10_216 : subd6_10 [0, 1, -5] = true := by decide +kernel
theorem subd6_10_217 : subd6_10 [0, 1, -4] = true := by decide +kernel
theorem subd6_10_218 : subd6_10 [0, 1, -3] = true := by decide +kernel
theorem subd6_10_219 : subd6_10 [0, 1, -2] = true := by decide +kernel
theorem subd6_10_220 : subd6_10 [0, 1, -1] = true := by decide +kernel
theorem subd6_10_221 : subd6_10 [0, 1, 0] = true := by decide +kernel
theorem subd6_10_222 : subd6_10 [0, 1, 1] = true := by decide +kernel
theorem subd6_10_223 : subd6_10 [0, 1, 2] = true := by decide +kernel
theorem sbd6_10_6 : ∀ q ∈ blkd6_10_6, subd6_10 q = true := by
  unfold blkd6_10_6
  exact List.forall_mem_cons.2 ⟨subd6_10_192, List.forall_mem_cons.2 ⟨subd6_10_193, List.forall_mem_cons.2 ⟨subd6_10_194, List.forall_mem_cons.2 ⟨subd6_10_195, List.forall_mem_cons.2 ⟨subd6_10_196, List.forall_mem_cons.2 ⟨subd6_10_197, List.forall_mem_cons.2 ⟨subd6_10_198, List.forall_mem_cons.2 ⟨subd6_10_199, List.forall_mem_cons.2 ⟨subd6_10_200, List.forall_mem_cons.2 ⟨subd6_10_201, List.forall_mem_cons.2 ⟨subd6_10_202, List.forall_mem_cons.2 ⟨subd6_10_203, List.forall_mem_cons.2 ⟨subd6_10_204, List.forall_mem_cons.2 ⟨subd6_10_205, List.forall_mem_cons.2 ⟨subd6_10_206, List.forall_mem_cons.2 ⟨subd6_10_207, List.forall_mem_cons.2 ⟨subd6_10_208, List.forall_mem_cons.2 ⟨subd6_10_209, List.forall_mem_cons.2 ⟨subd6_10_210, List.forall_mem_cons.2 ⟨subd6_10_211, List.forall_mem_cons.2 ⟨subd6_10_212, List.forall_mem_cons.2 ⟨subd6_10_213, List.forall_mem_cons.2 ⟨subd6_10_214, List.forall_mem_cons.2 ⟨subd6_10_215, List.forall_mem_cons.2 ⟨subd6_10_216, List.forall_mem_cons.2 ⟨subd6_10_217, List.forall_mem_cons.2 ⟨subd6_10_218, List.forall_mem_cons.2 ⟨subd6_10_219, List.forall_mem_cons.2 ⟨subd6_10_220, List.forall_mem_cons.2 ⟨subd6_10_221, List.forall_mem_cons.2 ⟨subd6_10_222, List.forall_mem_cons.2 ⟨subd6_10_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_10_224 : subd6_10 [0, 1, 3] = true := by decide +kernel
theorem subd6_10_225 : subd6_10 [0, 1, 4] = true := by decide +kernel
theorem subd6_10_226 : subd6_10 [0, 1, 5] = true := by decide +kernel
theorem subd6_10_227 : subd6_10 [0, 1, 6] = true := by decide +kernel
theorem subd6_10_228 : subd6_10 [0, 1, 7] = true := by decide +kernel
theorem subd6_10_229 : subd6_10 [0, 1, 8] = true := by decide +kernel
theorem subd6_10_230 : subd6_10 [0, 1, 9] = true := by decide +kernel
theorem subd6_10_231 : subd6_10 [0, 1, 10] = true := by decide +kernel
theorem subd6_10_232 : subd6_10 [0, 2, -8] = true := by decide +kernel
theorem subd6_10_233 : subd6_10 [0, 2, -7] = true := by decide +kernel
theorem subd6_10_234 : subd6_10 [0, 2, -6] = true := by decide +kernel
theorem subd6_10_235 : subd6_10 [0, 2, -5] = true := by decide +kernel
theorem subd6_10_236 : subd6_10 [0, 2, -4] = true := by decide +kernel
theorem subd6_10_237 : subd6_10 [0, 2, -3] = true := by decide +kernel
theorem subd6_10_238 : subd6_10 [0, 2, -2] = true := by decide +kernel
theorem subd6_10_239 : subd6_10 [0, 2, -1] = true := by decide +kernel
theorem subd6_10_240 : subd6_10 [0, 2, 0] = true := by decide +kernel
theorem subd6_10_241 : subd6_10 [0, 2, 1] = true := by decide +kernel
theorem subd6_10_242 : subd6_10 [0, 2, 2] = true := by decide +kernel
theorem subd6_10_243 : subd6_10 [0, 2, 3] = true := by decide +kernel
theorem subd6_10_244 : subd6_10 [0, 2, 4] = true := by decide +kernel
theorem subd6_10_245 : subd6_10 [0, 2, 5] = true := by decide +kernel
theorem subd6_10_246 : subd6_10 [0, 2, 6] = true := by decide +kernel
theorem subd6_10_247 : subd6_10 [0, 2, 7] = true := by decide +kernel
theorem subd6_10_248 : subd6_10 [1, -3] = true := by decide +kernel
theorem subd6_10_249 : subd6_10 [1, -2, -8] = true := by decide +kernel
theorem subd6_10_250 : subd6_10 [1, -2, -7] = true := by decide +kernel
theorem subd6_10_251 : subd6_10 [1, -2, -6] = true := by decide +kernel
theorem subd6_10_252 : subd6_10 [1, -2, -5] = true := by decide +kernel
theorem subd6_10_253 : subd6_10 [1, -2, -4] = true := by decide +kernel
theorem subd6_10_254 : subd6_10 [1, -2, -3] = true := by decide +kernel
theorem subd6_10_255 : subd6_10 [1, -2, -2] = true := by decide +kernel
theorem sbd6_10_7 : ∀ q ∈ blkd6_10_7, subd6_10 q = true := by
  unfold blkd6_10_7
  exact List.forall_mem_cons.2 ⟨subd6_10_224, List.forall_mem_cons.2 ⟨subd6_10_225, List.forall_mem_cons.2 ⟨subd6_10_226, List.forall_mem_cons.2 ⟨subd6_10_227, List.forall_mem_cons.2 ⟨subd6_10_228, List.forall_mem_cons.2 ⟨subd6_10_229, List.forall_mem_cons.2 ⟨subd6_10_230, List.forall_mem_cons.2 ⟨subd6_10_231, List.forall_mem_cons.2 ⟨subd6_10_232, List.forall_mem_cons.2 ⟨subd6_10_233, List.forall_mem_cons.2 ⟨subd6_10_234, List.forall_mem_cons.2 ⟨subd6_10_235, List.forall_mem_cons.2 ⟨subd6_10_236, List.forall_mem_cons.2 ⟨subd6_10_237, List.forall_mem_cons.2 ⟨subd6_10_238, List.forall_mem_cons.2 ⟨subd6_10_239, List.forall_mem_cons.2 ⟨subd6_10_240, List.forall_mem_cons.2 ⟨subd6_10_241, List.forall_mem_cons.2 ⟨subd6_10_242, List.forall_mem_cons.2 ⟨subd6_10_243, List.forall_mem_cons.2 ⟨subd6_10_244, List.forall_mem_cons.2 ⟨subd6_10_245, List.forall_mem_cons.2 ⟨subd6_10_246, List.forall_mem_cons.2 ⟨subd6_10_247, List.forall_mem_cons.2 ⟨subd6_10_248, List.forall_mem_cons.2 ⟨subd6_10_249, List.forall_mem_cons.2 ⟨subd6_10_250, List.forall_mem_cons.2 ⟨subd6_10_251, List.forall_mem_cons.2 ⟨subd6_10_252, List.forall_mem_cons.2 ⟨subd6_10_253, List.forall_mem_cons.2 ⟨subd6_10_254, List.forall_mem_cons.2 ⟨subd6_10_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_10_256 : subd6_10 [1, -2, -1] = true := by decide +kernel
theorem subd6_10_257 : subd6_10 [1, -2, 0] = true := by decide +kernel
theorem subd6_10_258 : subd6_10 [1, -2, 1] = true := by decide +kernel
theorem subd6_10_259 : subd6_10 [1, -2, 2] = true := by decide +kernel
theorem subd6_10_260 : subd6_10 [1, -2, 3] = true := by decide +kernel
theorem subd6_10_261 : subd6_10 [1, -2, 4] = true := by decide +kernel
theorem subd6_10_262 : subd6_10 [1, -2, 5] = true := by decide +kernel
theorem subd6_10_263 : subd6_10 [1, -2, 6] = true := by decide +kernel
theorem subd6_10_264 : subd6_10 [1, -2, 7] = true := by decide +kernel
theorem subd6_10_265 : subd6_10 [1, -1, -10] = true := by decide +kernel
theorem subd6_10_266 : subd6_10 [1, -1, -9] = true := by decide +kernel
theorem subd6_10_267 : subd6_10 [1, -1, -8] = true := by decide +kernel
theorem subd6_10_268 : subd6_10 [1, -1, -7] = true := by decide +kernel
theorem subd6_10_269 : subd6_10 [1, -1, -6] = true := by decide +kernel
theorem subd6_10_270 : subd6_10 [1, -1, -5] = true := by decide +kernel
theorem subd6_10_271 : subd6_10 [1, -1, -4] = true := by decide +kernel
theorem subd6_10_272 : subd6_10 [1, -1, -3] = true := by decide +kernel
theorem subd6_10_273 : subd6_10 [1, -1, -2] = true := by decide +kernel
theorem subd6_10_274 : subd6_10 [1, -1, -1] = true := by decide +kernel
theorem subd6_10_275 : subd6_10 [1, -1, 0] = true := by decide +kernel
theorem subd6_10_276 : subd6_10 [1, -1, 1] = true := by decide +kernel
theorem subd6_10_277 : subd6_10 [1, -1, 2] = true := by decide +kernel
theorem subd6_10_278 : subd6_10 [1, -1, 3] = true := by decide +kernel
theorem subd6_10_279 : subd6_10 [1, -1, 4] = true := by decide +kernel
theorem subd6_10_280 : subd6_10 [1, -1, 5] = true := by decide +kernel
theorem subd6_10_281 : subd6_10 [1, -1, 6] = true := by decide +kernel
theorem subd6_10_282 : subd6_10 [1, -1, 7] = true := by decide +kernel
theorem subd6_10_283 : subd6_10 [1, -1, 8] = true := by decide +kernel
theorem subd6_10_284 : subd6_10 [1, -1, 9] = true := by decide +kernel
theorem subd6_10_285 : subd6_10 [1, 0, -11] = true := by decide +kernel
theorem subd6_10_286 : subd6_10 [1, 0, -10] = true := by decide +kernel
theorem subd6_10_287 : subd6_10 [1, 0, -9] = true := by decide +kernel
theorem sbd6_10_8 : ∀ q ∈ blkd6_10_8, subd6_10 q = true := by
  unfold blkd6_10_8
  exact List.forall_mem_cons.2 ⟨subd6_10_256, List.forall_mem_cons.2 ⟨subd6_10_257, List.forall_mem_cons.2 ⟨subd6_10_258, List.forall_mem_cons.2 ⟨subd6_10_259, List.forall_mem_cons.2 ⟨subd6_10_260, List.forall_mem_cons.2 ⟨subd6_10_261, List.forall_mem_cons.2 ⟨subd6_10_262, List.forall_mem_cons.2 ⟨subd6_10_263, List.forall_mem_cons.2 ⟨subd6_10_264, List.forall_mem_cons.2 ⟨subd6_10_265, List.forall_mem_cons.2 ⟨subd6_10_266, List.forall_mem_cons.2 ⟨subd6_10_267, List.forall_mem_cons.2 ⟨subd6_10_268, List.forall_mem_cons.2 ⟨subd6_10_269, List.forall_mem_cons.2 ⟨subd6_10_270, List.forall_mem_cons.2 ⟨subd6_10_271, List.forall_mem_cons.2 ⟨subd6_10_272, List.forall_mem_cons.2 ⟨subd6_10_273, List.forall_mem_cons.2 ⟨subd6_10_274, List.forall_mem_cons.2 ⟨subd6_10_275, List.forall_mem_cons.2 ⟨subd6_10_276, List.forall_mem_cons.2 ⟨subd6_10_277, List.forall_mem_cons.2 ⟨subd6_10_278, List.forall_mem_cons.2 ⟨subd6_10_279, List.forall_mem_cons.2 ⟨subd6_10_280, List.forall_mem_cons.2 ⟨subd6_10_281, List.forall_mem_cons.2 ⟨subd6_10_282, List.forall_mem_cons.2 ⟨subd6_10_283, List.forall_mem_cons.2 ⟨subd6_10_284, List.forall_mem_cons.2 ⟨subd6_10_285, List.forall_mem_cons.2 ⟨subd6_10_286, List.forall_mem_cons.2 ⟨subd6_10_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_10_288 : subd6_10 [1, 0, -8] = true := by decide +kernel
theorem subd6_10_289 : subd6_10 [1, 0, -7] = true := by decide +kernel
theorem subd6_10_290 : subd6_10 [1, 0, -6] = true := by decide +kernel
theorem subd6_10_291 : subd6_10 [1, 0, -5] = true := by decide +kernel
theorem subd6_10_292 : subd6_10 [1, 0, -4] = true := by decide +kernel
theorem subd6_10_293 : subd6_10 [1, 0, -3] = true := by decide +kernel
theorem subd6_10_294 : subd6_10 [1, 0, -2] = true := by decide +kernel
theorem subd6_10_295 : subd6_10 [1, 0, -1] = true := by decide +kernel
theorem subd6_10_296 : subd6_10 [1, 0, 0] = true := by decide +kernel
theorem subd6_10_297 : subd6_10 [1, 0, 1] = true := by decide +kernel
theorem subd6_10_298 : subd6_10 [1, 0, 2] = true := by decide +kernel
theorem subd6_10_299 : subd6_10 [1, 0, 3] = true := by decide +kernel
theorem subd6_10_300 : subd6_10 [1, 0, 4] = true := by decide +kernel
theorem subd6_10_301 : subd6_10 [1, 0, 5] = true := by decide +kernel
theorem subd6_10_302 : subd6_10 [1, 0, 6] = true := by decide +kernel
theorem subd6_10_303 : subd6_10 [1, 0, 7] = true := by decide +kernel
theorem subd6_10_304 : subd6_10 [1, 0, 8] = true := by decide +kernel
theorem subd6_10_305 : subd6_10 [1, 0, 9] = true := by decide +kernel
theorem subd6_10_306 : subd6_10 [1, 0, 10] = true := by decide +kernel
theorem subd6_10_307 : subd6_10 [1, 1, -10] = true := by decide +kernel
theorem subd6_10_308 : subd6_10 [1, 1, -9] = true := by decide +kernel
theorem subd6_10_309 : subd6_10 [1, 1, -8] = true := by decide +kernel
theorem subd6_10_310 : subd6_10 [1, 1, -7] = true := by decide +kernel
theorem subd6_10_311 : subd6_10 [1, 1, -6] = true := by decide +kernel
theorem subd6_10_312 : subd6_10 [1, 1, -5] = true := by decide +kernel
theorem subd6_10_313 : subd6_10 [1, 1, -4] = true := by decide +kernel
theorem subd6_10_314 : subd6_10 [1, 1, -3] = true := by decide +kernel
theorem subd6_10_315 : subd6_10 [1, 1, -2] = true := by decide +kernel
theorem subd6_10_316 : subd6_10 [1, 1, -1] = true := by decide +kernel
theorem subd6_10_317 : subd6_10 [1, 1, 0] = true := by decide +kernel
theorem subd6_10_318 : subd6_10 [1, 1, 1] = true := by decide +kernel
theorem subd6_10_319 : subd6_10 [1, 1, 2] = true := by decide +kernel
theorem sbd6_10_9 : ∀ q ∈ blkd6_10_9, subd6_10 q = true := by
  unfold blkd6_10_9
  exact List.forall_mem_cons.2 ⟨subd6_10_288, List.forall_mem_cons.2 ⟨subd6_10_289, List.forall_mem_cons.2 ⟨subd6_10_290, List.forall_mem_cons.2 ⟨subd6_10_291, List.forall_mem_cons.2 ⟨subd6_10_292, List.forall_mem_cons.2 ⟨subd6_10_293, List.forall_mem_cons.2 ⟨subd6_10_294, List.forall_mem_cons.2 ⟨subd6_10_295, List.forall_mem_cons.2 ⟨subd6_10_296, List.forall_mem_cons.2 ⟨subd6_10_297, List.forall_mem_cons.2 ⟨subd6_10_298, List.forall_mem_cons.2 ⟨subd6_10_299, List.forall_mem_cons.2 ⟨subd6_10_300, List.forall_mem_cons.2 ⟨subd6_10_301, List.forall_mem_cons.2 ⟨subd6_10_302, List.forall_mem_cons.2 ⟨subd6_10_303, List.forall_mem_cons.2 ⟨subd6_10_304, List.forall_mem_cons.2 ⟨subd6_10_305, List.forall_mem_cons.2 ⟨subd6_10_306, List.forall_mem_cons.2 ⟨subd6_10_307, List.forall_mem_cons.2 ⟨subd6_10_308, List.forall_mem_cons.2 ⟨subd6_10_309, List.forall_mem_cons.2 ⟨subd6_10_310, List.forall_mem_cons.2 ⟨subd6_10_311, List.forall_mem_cons.2 ⟨subd6_10_312, List.forall_mem_cons.2 ⟨subd6_10_313, List.forall_mem_cons.2 ⟨subd6_10_314, List.forall_mem_cons.2 ⟨subd6_10_315, List.forall_mem_cons.2 ⟨subd6_10_316, List.forall_mem_cons.2 ⟨subd6_10_317, List.forall_mem_cons.2 ⟨subd6_10_318, List.forall_mem_cons.2 ⟨subd6_10_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_10_320 : subd6_10 [1, 1, 3] = true := by decide +kernel
theorem subd6_10_321 : subd6_10 [1, 1, 4] = true := by decide +kernel
theorem subd6_10_322 : subd6_10 [1, 1, 5] = true := by decide +kernel
theorem subd6_10_323 : subd6_10 [1, 1, 6] = true := by decide +kernel
theorem subd6_10_324 : subd6_10 [1, 1, 7] = true := by decide +kernel
theorem subd6_10_325 : subd6_10 [1, 1, 8] = true := by decide +kernel
theorem subd6_10_326 : subd6_10 [1, 1, 9] = true := by decide +kernel
theorem subd6_10_327 : subd6_10 [1, 2] = true := by decide +kernel
theorem subd6_10_328 : subd6_10 [2, -3] = true := by decide +kernel
theorem subd6_10_329 : subd6_10 [2, -2, -7] = true := by decide +kernel
theorem subd6_10_330 : subd6_10 [2, -2, -6] = true := by decide +kernel
theorem subd6_10_331 : subd6_10 [2, -2, -5] = true := by decide +kernel
theorem subd6_10_332 : subd6_10 [2, -2, -4] = true := by decide +kernel
theorem subd6_10_333 : subd6_10 [2, -2, -3] = true := by decide +kernel
theorem subd6_10_334 : subd6_10 [2, -2, -2] = true := by decide +kernel
theorem subd6_10_335 : subd6_10 [2, -2, -1] = true := by decide +kernel
theorem subd6_10_336 : subd6_10 [2, -2, 0] = true := by decide +kernel
theorem subd6_10_337 : subd6_10 [2, -2, 1] = true := by decide +kernel
theorem subd6_10_338 : subd6_10 [2, -2, 2] = true := by decide +kernel
theorem subd6_10_339 : subd6_10 [2, -2, 3] = true := by decide +kernel
theorem subd6_10_340 : subd6_10 [2, -2, 4] = true := by decide +kernel
theorem subd6_10_341 : subd6_10 [2, -2, 5] = true := by decide +kernel
theorem subd6_10_342 : subd6_10 [2, -2, 6] = true := by decide +kernel
theorem subd6_10_343 : subd6_10 [2, -1, -9] = true := by decide +kernel
theorem subd6_10_344 : subd6_10 [2, -1, -8] = true := by decide +kernel
theorem subd6_10_345 : subd6_10 [2, -1, -7] = true := by decide +kernel
theorem subd6_10_346 : subd6_10 [2, -1, -6] = true := by decide +kernel
theorem subd6_10_347 : subd6_10 [2, -1, -5] = true := by decide +kernel
theorem subd6_10_348 : subd6_10 [2, -1, -4] = true := by decide +kernel
theorem subd6_10_349 : subd6_10 [2, -1, -3] = true := by decide +kernel
theorem subd6_10_350 : subd6_10 [2, -1, -2] = true := by decide +kernel
theorem subd6_10_351 : subd6_10 [2, -1, -1] = true := by decide +kernel
theorem sbd6_10_10 : ∀ q ∈ blkd6_10_10, subd6_10 q = true := by
  unfold blkd6_10_10
  exact List.forall_mem_cons.2 ⟨subd6_10_320, List.forall_mem_cons.2 ⟨subd6_10_321, List.forall_mem_cons.2 ⟨subd6_10_322, List.forall_mem_cons.2 ⟨subd6_10_323, List.forall_mem_cons.2 ⟨subd6_10_324, List.forall_mem_cons.2 ⟨subd6_10_325, List.forall_mem_cons.2 ⟨subd6_10_326, List.forall_mem_cons.2 ⟨subd6_10_327, List.forall_mem_cons.2 ⟨subd6_10_328, List.forall_mem_cons.2 ⟨subd6_10_329, List.forall_mem_cons.2 ⟨subd6_10_330, List.forall_mem_cons.2 ⟨subd6_10_331, List.forall_mem_cons.2 ⟨subd6_10_332, List.forall_mem_cons.2 ⟨subd6_10_333, List.forall_mem_cons.2 ⟨subd6_10_334, List.forall_mem_cons.2 ⟨subd6_10_335, List.forall_mem_cons.2 ⟨subd6_10_336, List.forall_mem_cons.2 ⟨subd6_10_337, List.forall_mem_cons.2 ⟨subd6_10_338, List.forall_mem_cons.2 ⟨subd6_10_339, List.forall_mem_cons.2 ⟨subd6_10_340, List.forall_mem_cons.2 ⟨subd6_10_341, List.forall_mem_cons.2 ⟨subd6_10_342, List.forall_mem_cons.2 ⟨subd6_10_343, List.forall_mem_cons.2 ⟨subd6_10_344, List.forall_mem_cons.2 ⟨subd6_10_345, List.forall_mem_cons.2 ⟨subd6_10_346, List.forall_mem_cons.2 ⟨subd6_10_347, List.forall_mem_cons.2 ⟨subd6_10_348, List.forall_mem_cons.2 ⟨subd6_10_349, List.forall_mem_cons.2 ⟨subd6_10_350, List.forall_mem_cons.2 ⟨subd6_10_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_10_352 : subd6_10 [2, -1, 0] = true := by decide +kernel
theorem subd6_10_353 : subd6_10 [2, -1, 1] = true := by decide +kernel
theorem subd6_10_354 : subd6_10 [2, -1, 2] = true := by decide +kernel
theorem subd6_10_355 : subd6_10 [2, -1, 3] = true := by decide +kernel
theorem subd6_10_356 : subd6_10 [2, -1, 4] = true := by decide +kernel
theorem subd6_10_357 : subd6_10 [2, -1, 5] = true := by decide +kernel
theorem subd6_10_358 : subd6_10 [2, -1, 6] = true := by decide +kernel
theorem subd6_10_359 : subd6_10 [2, -1, 7] = true := by decide +kernel
theorem subd6_10_360 : subd6_10 [2, -1, 8] = true := by decide +kernel
theorem subd6_10_361 : subd6_10 [2, 0, -9] = true := by decide +kernel
theorem subd6_10_362 : subd6_10 [2, 0, -8] = true := by decide +kernel
theorem subd6_10_363 : subd6_10 [2, 0, -7] = true := by decide +kernel
theorem subd6_10_364 : subd6_10 [2, 0, -6] = true := by decide +kernel
theorem subd6_10_365 : subd6_10 [2, 0, -5] = true := by decide +kernel
theorem subd6_10_366 : subd6_10 [2, 0, -4] = true := by decide +kernel
theorem subd6_10_367 : subd6_10 [2, 0, -3] = true := by decide +kernel
theorem subd6_10_368 : subd6_10 [2, 0, -2] = true := by decide +kernel
theorem subd6_10_369 : subd6_10 [2, 0, -1] = true := by decide +kernel
theorem subd6_10_370 : subd6_10 [2, 0, 0] = true := by decide +kernel
theorem subd6_10_371 : subd6_10 [2, 0, 1] = true := by decide +kernel
theorem subd6_10_372 : subd6_10 [2, 0, 2] = true := by decide +kernel
theorem subd6_10_373 : subd6_10 [2, 0, 3] = true := by decide +kernel
theorem subd6_10_374 : subd6_10 [2, 0, 4] = true := by decide +kernel
theorem subd6_10_375 : subd6_10 [2, 0, 5] = true := by decide +kernel
theorem subd6_10_376 : subd6_10 [2, 0, 6] = true := by decide +kernel
theorem subd6_10_377 : subd6_10 [2, 0, 7] = true := by decide +kernel
theorem subd6_10_378 : subd6_10 [2, 0, 8] = true := by decide +kernel
theorem subd6_10_379 : subd6_10 [2, 1, -7] = true := by decide +kernel
theorem subd6_10_380 : subd6_10 [2, 1, -6] = true := by decide +kernel
theorem subd6_10_381 : subd6_10 [2, 1, -5] = true := by decide +kernel
theorem subd6_10_382 : subd6_10 [2, 1, -4] = true := by decide +kernel
theorem subd6_10_383 : subd6_10 [2, 1, -3] = true := by decide +kernel
theorem sbd6_10_11 : ∀ q ∈ blkd6_10_11, subd6_10 q = true := by
  unfold blkd6_10_11
  exact List.forall_mem_cons.2 ⟨subd6_10_352, List.forall_mem_cons.2 ⟨subd6_10_353, List.forall_mem_cons.2 ⟨subd6_10_354, List.forall_mem_cons.2 ⟨subd6_10_355, List.forall_mem_cons.2 ⟨subd6_10_356, List.forall_mem_cons.2 ⟨subd6_10_357, List.forall_mem_cons.2 ⟨subd6_10_358, List.forall_mem_cons.2 ⟨subd6_10_359, List.forall_mem_cons.2 ⟨subd6_10_360, List.forall_mem_cons.2 ⟨subd6_10_361, List.forall_mem_cons.2 ⟨subd6_10_362, List.forall_mem_cons.2 ⟨subd6_10_363, List.forall_mem_cons.2 ⟨subd6_10_364, List.forall_mem_cons.2 ⟨subd6_10_365, List.forall_mem_cons.2 ⟨subd6_10_366, List.forall_mem_cons.2 ⟨subd6_10_367, List.forall_mem_cons.2 ⟨subd6_10_368, List.forall_mem_cons.2 ⟨subd6_10_369, List.forall_mem_cons.2 ⟨subd6_10_370, List.forall_mem_cons.2 ⟨subd6_10_371, List.forall_mem_cons.2 ⟨subd6_10_372, List.forall_mem_cons.2 ⟨subd6_10_373, List.forall_mem_cons.2 ⟨subd6_10_374, List.forall_mem_cons.2 ⟨subd6_10_375, List.forall_mem_cons.2 ⟨subd6_10_376, List.forall_mem_cons.2 ⟨subd6_10_377, List.forall_mem_cons.2 ⟨subd6_10_378, List.forall_mem_cons.2 ⟨subd6_10_379, List.forall_mem_cons.2 ⟨subd6_10_380, List.forall_mem_cons.2 ⟨subd6_10_381, List.forall_mem_cons.2 ⟨subd6_10_382, List.forall_mem_cons.2 ⟨subd6_10_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_10_384 : subd6_10 [2, 1, -2] = true := by decide +kernel
theorem subd6_10_385 : subd6_10 [2, 1, -1] = true := by decide +kernel
theorem subd6_10_386 : subd6_10 [2, 1, 0] = true := by decide +kernel
theorem subd6_10_387 : subd6_10 [2, 1, 1] = true := by decide +kernel
theorem subd6_10_388 : subd6_10 [2, 1, 2] = true := by decide +kernel
theorem subd6_10_389 : subd6_10 [2, 1, 3] = true := by decide +kernel
theorem subd6_10_390 : subd6_10 [2, 1, 4] = true := by decide +kernel
theorem subd6_10_391 : subd6_10 [2, 1, 5] = true := by decide +kernel
theorem subd6_10_392 : subd6_10 [2, 1, 6] = true := by decide +kernel
theorem subd6_10_393 : subd6_10 [3, -3] = true := by decide +kernel
theorem subd6_10_394 : subd6_10 [3, -2] = true := by decide +kernel
theorem subd6_10_395 : subd6_10 [3, -1] = true := by decide +kernel
theorem subd6_10_396 : subd6_10 [3, 0] = true := by decide +kernel
theorem sbd6_10_12 : ∀ q ∈ blkd6_10_12, subd6_10 q = true := by
  unfold blkd6_10_12
  exact List.forall_mem_cons.2 ⟨subd6_10_384, List.forall_mem_cons.2 ⟨subd6_10_385, List.forall_mem_cons.2 ⟨subd6_10_386, List.forall_mem_cons.2 ⟨subd6_10_387, List.forall_mem_cons.2 ⟨subd6_10_388, List.forall_mem_cons.2 ⟨subd6_10_389, List.forall_mem_cons.2 ⟨subd6_10_390, List.forall_mem_cons.2 ⟨subd6_10_391, List.forall_mem_cons.2 ⟨subd6_10_392, List.forall_mem_cons.2 ⟨subd6_10_393, List.forall_mem_cons.2 ⟨subd6_10_394, List.forall_mem_cons.2 ⟨subd6_10_395, List.forall_mem_cons.2 ⟨subd6_10_396, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_11 : ldCheck G d6_11.U d6_11.ms ldd6_11 = true := by decide +kernel
theorem pre_okd6_11 : subPre G cell6 d6_11 = true := by decide +kernel
theorem subd6_11_0 : subd6_11 [-6] = true := by decide +kernel
theorem subd6_11_1 : subd6_11 [-5, -4] = true := by decide +kernel
theorem subd6_11_2 : subd6_11 [-5, -3] = true := by decide +kernel
theorem subd6_11_3 : subd6_11 [-5, -2] = true := by decide +kernel
theorem subd6_11_4 : subd6_11 [-5, -1] = true := by decide +kernel
theorem subd6_11_5 : subd6_11 [-5, 0] = true := by decide +kernel
theorem subd6_11_6 : subd6_11 [-5, 1] = true := by decide +kernel
theorem subd6_11_7 : subd6_11 [-5, 2] = true := by decide +kernel
theorem subd6_11_8 : subd6_11 [-5, 3] = true := by decide +kernel
theorem subd6_11_9 : subd6_11 [-5, 4] = true := by decide +kernel
theorem subd6_11_10 : subd6_11 [-5, 5] = true := by decide +kernel
theorem subd6_11_11 : subd6_11 [-4, -5] = true := by decide +kernel
theorem subd6_11_12 : subd6_11 [-4, -4] = true := by decide +kernel
theorem subd6_11_13 : subd6_11 [-4, -3] = true := by decide +kernel
theorem subd6_11_14 : subd6_11 [-4, -2] = true := by decide +kernel
theorem subd6_11_15 : subd6_11 [-4, -1] = true := by decide +kernel
theorem subd6_11_16 : subd6_11 [-4, 0] = true := by decide +kernel
theorem subd6_11_17 : subd6_11 [-4, 1] = true := by decide +kernel
theorem subd6_11_18 : subd6_11 [-4, 2] = true := by decide +kernel
theorem subd6_11_19 : subd6_11 [-4, 3] = true := by decide +kernel
theorem subd6_11_20 : subd6_11 [-4, 4] = true := by decide +kernel
theorem subd6_11_21 : subd6_11 [-4, 5] = true := by decide +kernel
theorem subd6_11_22 : subd6_11 [-4, 6] = true := by decide +kernel
theorem subd6_11_23 : subd6_11 [-3, -6] = true := by decide +kernel
theorem subd6_11_24 : subd6_11 [-3, -5] = true := by decide +kernel
theorem subd6_11_25 : subd6_11 [-3, -4] = true := by decide +kernel
theorem subd6_11_26 : subd6_11 [-3, -3] = true := by decide +kernel
theorem subd6_11_27 : subd6_11 [-3, -2] = true := by decide +kernel
theorem subd6_11_28 : subd6_11 [-3, -1] = true := by decide +kernel
theorem subd6_11_29 : subd6_11 [-3, 0] = true := by decide +kernel
theorem subd6_11_30 : subd6_11 [-3, 1] = true := by decide +kernel
theorem subd6_11_31 : subd6_11 [-3, 2] = true := by decide +kernel
theorem sbd6_11_0 : ∀ q ∈ blkd6_11_0, subd6_11 q = true := by
  unfold blkd6_11_0
  exact List.forall_mem_cons.2 ⟨subd6_11_0, List.forall_mem_cons.2 ⟨subd6_11_1, List.forall_mem_cons.2 ⟨subd6_11_2, List.forall_mem_cons.2 ⟨subd6_11_3, List.forall_mem_cons.2 ⟨subd6_11_4, List.forall_mem_cons.2 ⟨subd6_11_5, List.forall_mem_cons.2 ⟨subd6_11_6, List.forall_mem_cons.2 ⟨subd6_11_7, List.forall_mem_cons.2 ⟨subd6_11_8, List.forall_mem_cons.2 ⟨subd6_11_9, List.forall_mem_cons.2 ⟨subd6_11_10, List.forall_mem_cons.2 ⟨subd6_11_11, List.forall_mem_cons.2 ⟨subd6_11_12, List.forall_mem_cons.2 ⟨subd6_11_13, List.forall_mem_cons.2 ⟨subd6_11_14, List.forall_mem_cons.2 ⟨subd6_11_15, List.forall_mem_cons.2 ⟨subd6_11_16, List.forall_mem_cons.2 ⟨subd6_11_17, List.forall_mem_cons.2 ⟨subd6_11_18, List.forall_mem_cons.2 ⟨subd6_11_19, List.forall_mem_cons.2 ⟨subd6_11_20, List.forall_mem_cons.2 ⟨subd6_11_21, List.forall_mem_cons.2 ⟨subd6_11_22, List.forall_mem_cons.2 ⟨subd6_11_23, List.forall_mem_cons.2 ⟨subd6_11_24, List.forall_mem_cons.2 ⟨subd6_11_25, List.forall_mem_cons.2 ⟨subd6_11_26, List.forall_mem_cons.2 ⟨subd6_11_27, List.forall_mem_cons.2 ⟨subd6_11_28, List.forall_mem_cons.2 ⟨subd6_11_29, List.forall_mem_cons.2 ⟨subd6_11_30, List.forall_mem_cons.2 ⟨subd6_11_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
