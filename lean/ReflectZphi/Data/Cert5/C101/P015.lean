import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_1_96 : subd11_1 [-1, 0, 7] = true := by decide +kernel
theorem subd11_1_97 : subd11_1 [-1, 0, 8] = true := by decide +kernel
theorem subd11_1_98 : subd11_1 [-1, 0, 9] = true := by decide +kernel
theorem subd11_1_99 : subd11_1 [-1, 0, 10] = true := by decide +kernel
theorem subd11_1_100 : subd11_1 [-1, 0, 11] = true := by decide +kernel
theorem subd11_1_101 : subd11_1 [-1, 0, 12] = true := by decide +kernel
theorem subd11_1_102 : subd11_1 [-1, 0, 13] = true := by decide +kernel
theorem subd11_1_103 : subd11_1 [-1, 0, 14] = true := by decide +kernel
theorem subd11_1_104 : subd11_1 [-1, 0, 15] = true := by decide +kernel
theorem subd11_1_105 : subd11_1 [-1, 0, 16] = true := by decide +kernel
theorem subd11_1_106 : subd11_1 [-1, 0, 17] = true := by decide +kernel
theorem subd11_1_107 : subd11_1 [-1, 0, 18] = true := by decide +kernel
theorem subd11_1_108 : subd11_1 [-1, 0, 19] = true := by decide +kernel
theorem subd11_1_109 : subd11_1 [-1, 1, -15] = true := by decide +kernel
theorem subd11_1_110 : subd11_1 [-1, 1, -14] = true := by decide +kernel
theorem subd11_1_111 : subd11_1 [-1, 1, -13] = true := by decide +kernel
theorem subd11_1_112 : subd11_1 [-1, 1, -12] = true := by decide +kernel
theorem subd11_1_113 : subd11_1 [-1, 1, -11] = true := by decide +kernel
theorem subd11_1_114 : subd11_1 [-1, 1, -10] = true := by decide +kernel
theorem subd11_1_115 : subd11_1 [-1, 1, -9] = true := by decide +kernel
theorem subd11_1_116 : subd11_1 [-1, 1, -8] = true := by decide +kernel
theorem subd11_1_117 : subd11_1 [-1, 1, -7] = true := by decide +kernel
theorem subd11_1_118 : subd11_1 [-1, 1, -6] = true := by decide +kernel
theorem subd11_1_119 : subd11_1 [-1, 1, -5] = true := by decide +kernel
theorem subd11_1_120 : subd11_1 [-1, 1, -4] = true := by decide +kernel
theorem subd11_1_121 : subd11_1 [-1, 1, -3] = true := by decide +kernel
theorem subd11_1_122 : subd11_1 [-1, 1, -2] = true := by decide +kernel
theorem subd11_1_123 : subd11_1 [-1, 1, -1] = true := by decide +kernel
theorem subd11_1_124 : subd11_1 [-1, 1, 0] = true := by decide +kernel
theorem subd11_1_125 : subd11_1 [-1, 1, 1] = true := by decide +kernel
theorem subd11_1_126 : subd11_1 [-1, 1, 2] = true := by decide +kernel
theorem subd11_1_127 : subd11_1 [-1, 1, 3] = true := by decide +kernel
theorem sbd11_1_3 : ∀ q ∈ blkd11_1_3, subd11_1 q = true := by
  unfold blkd11_1_3
  exact List.forall_mem_cons.2 ⟨subd11_1_96, List.forall_mem_cons.2 ⟨subd11_1_97, List.forall_mem_cons.2 ⟨subd11_1_98, List.forall_mem_cons.2 ⟨subd11_1_99, List.forall_mem_cons.2 ⟨subd11_1_100, List.forall_mem_cons.2 ⟨subd11_1_101, List.forall_mem_cons.2 ⟨subd11_1_102, List.forall_mem_cons.2 ⟨subd11_1_103, List.forall_mem_cons.2 ⟨subd11_1_104, List.forall_mem_cons.2 ⟨subd11_1_105, List.forall_mem_cons.2 ⟨subd11_1_106, List.forall_mem_cons.2 ⟨subd11_1_107, List.forall_mem_cons.2 ⟨subd11_1_108, List.forall_mem_cons.2 ⟨subd11_1_109, List.forall_mem_cons.2 ⟨subd11_1_110, List.forall_mem_cons.2 ⟨subd11_1_111, List.forall_mem_cons.2 ⟨subd11_1_112, List.forall_mem_cons.2 ⟨subd11_1_113, List.forall_mem_cons.2 ⟨subd11_1_114, List.forall_mem_cons.2 ⟨subd11_1_115, List.forall_mem_cons.2 ⟨subd11_1_116, List.forall_mem_cons.2 ⟨subd11_1_117, List.forall_mem_cons.2 ⟨subd11_1_118, List.forall_mem_cons.2 ⟨subd11_1_119, List.forall_mem_cons.2 ⟨subd11_1_120, List.forall_mem_cons.2 ⟨subd11_1_121, List.forall_mem_cons.2 ⟨subd11_1_122, List.forall_mem_cons.2 ⟨subd11_1_123, List.forall_mem_cons.2 ⟨subd11_1_124, List.forall_mem_cons.2 ⟨subd11_1_125, List.forall_mem_cons.2 ⟨subd11_1_126, List.forall_mem_cons.2 ⟨subd11_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_128 : subd11_1 [-1, 1, 4] = true := by decide +kernel
theorem subd11_1_129 : subd11_1 [-1, 1, 5] = true := by decide +kernel
theorem subd11_1_130 : subd11_1 [-1, 1, 6] = true := by decide +kernel
theorem subd11_1_131 : subd11_1 [-1, 1, 7] = true := by decide +kernel
theorem subd11_1_132 : subd11_1 [-1, 1, 8] = true := by decide +kernel
theorem subd11_1_133 : subd11_1 [-1, 1, 9] = true := by decide +kernel
theorem subd11_1_134 : subd11_1 [-1, 1, 10] = true := by decide +kernel
theorem subd11_1_135 : subd11_1 [-1, 1, 11] = true := by decide +kernel
theorem subd11_1_136 : subd11_1 [-1, 1, 12] = true := by decide +kernel
theorem subd11_1_137 : subd11_1 [-1, 1, 13] = true := by decide +kernel
theorem subd11_1_138 : subd11_1 [-1, 1, 14] = true := by decide +kernel
theorem subd11_1_139 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_140 : subd11_1 [0, -2, -12] = true := by decide +kernel
theorem subd11_1_141 : subd11_1 [0, -2, -11] = true := by decide +kernel
theorem subd11_1_142 : subd11_1 [0, -2, -10] = true := by decide +kernel
theorem subd11_1_143 : subd11_1 [0, -2, -9] = true := by decide +kernel
theorem subd11_1_144 : subd11_1 [0, -2, -8] = true := by decide +kernel
theorem subd11_1_145 : subd11_1 [0, -2, -7] = true := by decide +kernel
theorem subd11_1_146 : subd11_1 [0, -2, -6] = true := by decide +kernel
theorem subd11_1_147 : subd11_1 [0, -2, -5] = true := by decide +kernel
theorem subd11_1_148 : subd11_1 [0, -2, -4] = true := by decide +kernel
theorem subd11_1_149 : subd11_1 [0, -2, -3] = true := by decide +kernel
theorem subd11_1_150 : subd11_1 [0, -2, -2] = true := by decide +kernel
theorem subd11_1_151 : subd11_1 [0, -2, -1] = true := by decide +kernel
theorem subd11_1_152 : subd11_1 [0, -2, 0] = true := by decide +kernel
theorem subd11_1_153 : subd11_1 [0, -2, 1] = true := by decide +kernel
theorem subd11_1_154 : subd11_1 [0, -2, 2] = true := by decide +kernel
theorem subd11_1_155 : subd11_1 [0, -2, 3] = true := by decide +kernel
theorem subd11_1_156 : subd11_1 [0, -2, 4] = true := by decide +kernel
theorem subd11_1_157 : subd11_1 [0, -2, 5] = true := by decide +kernel
theorem subd11_1_158 : subd11_1 [0, -2, 6] = true := by decide +kernel
theorem subd11_1_159 : subd11_1 [0, -2, 7] = true := by decide +kernel
theorem sbd11_1_4 : ∀ q ∈ blkd11_1_4, subd11_1 q = true := by
  unfold blkd11_1_4
  exact List.forall_mem_cons.2 ⟨subd11_1_128, List.forall_mem_cons.2 ⟨subd11_1_129, List.forall_mem_cons.2 ⟨subd11_1_130, List.forall_mem_cons.2 ⟨subd11_1_131, List.forall_mem_cons.2 ⟨subd11_1_132, List.forall_mem_cons.2 ⟨subd11_1_133, List.forall_mem_cons.2 ⟨subd11_1_134, List.forall_mem_cons.2 ⟨subd11_1_135, List.forall_mem_cons.2 ⟨subd11_1_136, List.forall_mem_cons.2 ⟨subd11_1_137, List.forall_mem_cons.2 ⟨subd11_1_138, List.forall_mem_cons.2 ⟨subd11_1_139, List.forall_mem_cons.2 ⟨subd11_1_140, List.forall_mem_cons.2 ⟨subd11_1_141, List.forall_mem_cons.2 ⟨subd11_1_142, List.forall_mem_cons.2 ⟨subd11_1_143, List.forall_mem_cons.2 ⟨subd11_1_144, List.forall_mem_cons.2 ⟨subd11_1_145, List.forall_mem_cons.2 ⟨subd11_1_146, List.forall_mem_cons.2 ⟨subd11_1_147, List.forall_mem_cons.2 ⟨subd11_1_148, List.forall_mem_cons.2 ⟨subd11_1_149, List.forall_mem_cons.2 ⟨subd11_1_150, List.forall_mem_cons.2 ⟨subd11_1_151, List.forall_mem_cons.2 ⟨subd11_1_152, List.forall_mem_cons.2 ⟨subd11_1_153, List.forall_mem_cons.2 ⟨subd11_1_154, List.forall_mem_cons.2 ⟨subd11_1_155, List.forall_mem_cons.2 ⟨subd11_1_156, List.forall_mem_cons.2 ⟨subd11_1_157, List.forall_mem_cons.2 ⟨subd11_1_158, List.forall_mem_cons.2 ⟨subd11_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_160 : subd11_1 [0, -2, 8] = true := by decide +kernel
theorem subd11_1_161 : subd11_1 [0, -2, 9] = true := by decide +kernel
theorem subd11_1_162 : subd11_1 [0, -2, 10] = true := by decide +kernel
theorem subd11_1_163 : subd11_1 [0, -2, 11] = true := by decide +kernel
theorem subd11_1_164 : subd11_1 [0, -1, -21] = true := by decide +kernel
theorem subd11_1_165 : subd11_1 [0, -1, -20] = true := by decide +kernel
theorem subd11_1_166 : subd11_1 [0, -1, -19] = true := by decide +kernel
theorem subd11_1_167 : subd11_1 [0, -1, -18] = true := by decide +kernel
theorem subd11_1_168 : subd11_1 [0, -1, -17] = true := by decide +kernel
theorem subd11_1_169 : subd11_1 [0, -1, -16] = true := by decide +kernel
theorem subd11_1_170 : subd11_1 [0, -1, -15] = true := by decide +kernel
theorem subd11_1_171 : subd11_1 [0, -1, -14] = true := by decide +kernel
theorem subd11_1_172 : subd11_1 [0, -1, -13] = true := by decide +kernel
theorem subd11_1_173 : subd11_1 [0, -1, -12] = true := by decide +kernel
theorem subd11_1_174 : subd11_1 [0, -1, -11] = true := by decide +kernel
theorem subd11_1_175 : subd11_1 [0, -1, -10] = true := by decide +kernel
theorem subd11_1_176 : subd11_1 [0, -1, -9] = true := by decide +kernel
theorem subd11_1_177 : subd11_1 [0, -1, -8] = true := by decide +kernel
theorem subd11_1_178 : subd11_1 [0, -1, -7] = true := by decide +kernel
theorem subd11_1_179 : subd11_1 [0, -1, -6] = true := by decide +kernel
theorem subd11_1_180 : subd11_1 [0, -1, -5] = true := by decide +kernel
theorem subd11_1_181 : subd11_1 [0, -1, -4] = true := by decide +kernel
theorem subd11_1_182 : subd11_1 [0, -1, -3] = true := by decide +kernel
theorem subd11_1_183 : subd11_1 [0, -1, -2] = true := by decide +kernel
theorem subd11_1_184 : subd11_1 [0, -1, -1] = true := by decide +kernel
theorem subd11_1_185 : subd11_1 [0, -1, 0] = true := by decide +kernel
theorem subd11_1_186 : subd11_1 [0, -1, 1] = true := by decide +kernel
theorem subd11_1_187 : subd11_1 [0, -1, 2] = true := by decide +kernel
theorem subd11_1_188 : subd11_1 [0, -1, 3] = true := by decide +kernel
theorem subd11_1_189 : subd11_1 [0, -1, 4] = true := by decide +kernel
theorem subd11_1_190 : subd11_1 [0, -1, 5] = true := by decide +kernel
theorem subd11_1_191 : subd11_1 [0, -1, 6] = true := by decide +kernel
theorem sbd11_1_5 : ∀ q ∈ blkd11_1_5, subd11_1 q = true := by
  unfold blkd11_1_5
  exact List.forall_mem_cons.2 ⟨subd11_1_160, List.forall_mem_cons.2 ⟨subd11_1_161, List.forall_mem_cons.2 ⟨subd11_1_162, List.forall_mem_cons.2 ⟨subd11_1_163, List.forall_mem_cons.2 ⟨subd11_1_164, List.forall_mem_cons.2 ⟨subd11_1_165, List.forall_mem_cons.2 ⟨subd11_1_166, List.forall_mem_cons.2 ⟨subd11_1_167, List.forall_mem_cons.2 ⟨subd11_1_168, List.forall_mem_cons.2 ⟨subd11_1_169, List.forall_mem_cons.2 ⟨subd11_1_170, List.forall_mem_cons.2 ⟨subd11_1_171, List.forall_mem_cons.2 ⟨subd11_1_172, List.forall_mem_cons.2 ⟨subd11_1_173, List.forall_mem_cons.2 ⟨subd11_1_174, List.forall_mem_cons.2 ⟨subd11_1_175, List.forall_mem_cons.2 ⟨subd11_1_176, List.forall_mem_cons.2 ⟨subd11_1_177, List.forall_mem_cons.2 ⟨subd11_1_178, List.forall_mem_cons.2 ⟨subd11_1_179, List.forall_mem_cons.2 ⟨subd11_1_180, List.forall_mem_cons.2 ⟨subd11_1_181, List.forall_mem_cons.2 ⟨subd11_1_182, List.forall_mem_cons.2 ⟨subd11_1_183, List.forall_mem_cons.2 ⟨subd11_1_184, List.forall_mem_cons.2 ⟨subd11_1_185, List.forall_mem_cons.2 ⟨subd11_1_186, List.forall_mem_cons.2 ⟨subd11_1_187, List.forall_mem_cons.2 ⟨subd11_1_188, List.forall_mem_cons.2 ⟨subd11_1_189, List.forall_mem_cons.2 ⟨subd11_1_190, List.forall_mem_cons.2 ⟨subd11_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_192 : subd11_1 [0, -1, 7] = true := by decide +kernel
theorem subd11_1_193 : subd11_1 [0, -1, 8] = true := by decide +kernel
theorem subd11_1_194 : subd11_1 [0, -1, 9] = true := by decide +kernel
theorem subd11_1_195 : subd11_1 [0, -1, 10] = true := by decide +kernel
theorem subd11_1_196 : subd11_1 [0, -1, 11] = true := by decide +kernel
theorem subd11_1_197 : subd11_1 [0, -1, 12] = true := by decide +kernel
theorem subd11_1_198 : subd11_1 [0, -1, 13] = true := by decide +kernel
theorem subd11_1_199 : subd11_1 [0, -1, 14] = true := by decide +kernel
theorem subd11_1_200 : subd11_1 [0, -1, 15] = true := by decide +kernel
theorem subd11_1_201 : subd11_1 [0, -1, 16] = true := by decide +kernel
theorem subd11_1_202 : subd11_1 [0, -1, 17] = true := by decide +kernel
theorem subd11_1_203 : subd11_1 [0, -1, 18] = true := by decide +kernel
theorem subd11_1_204 : subd11_1 [0, -1, 19] = true := by decide +kernel
theorem subd11_1_205 : subd11_1 [0, -1, 20] = true := by decide +kernel
theorem subd11_1_206 : subd11_1 [0, -1, 21] = true := by decide +kernel
theorem subd11_1_207 : subd11_1 [0, 0, -24] = true := by decide +kernel
theorem subd11_1_208 : subd11_1 [0, 0, -23] = true := by decide +kernel
theorem subd11_1_209 : subd11_1 [0, 0, -22] = true := by decide +kernel
theorem subd11_1_210 : subd11_1 [0, 0, -21] = true := by decide +kernel
theorem subd11_1_211 : subd11_1 [0, 0, -20] = true := by decide +kernel
theorem subd11_1_212 : subd11_1 [0, 0, -19] = true := by decide +kernel
theorem subd11_1_213 : subd11_1 [0, 0, -18] = true := by decide +kernel
theorem subd11_1_214 : subd11_1 [0, 0, -17] = true := by decide +kernel
theorem subd11_1_215 : subd11_1 [0, 0, -16] = true := by decide +kernel
theorem subd11_1_216 : subd11_1 [0, 0, -15] = true := by decide +kernel
theorem subd11_1_217 : subd11_1 [0, 0, -14] = true := by decide +kernel
theorem subd11_1_218 : subd11_1 [0, 0, -13] = true := by decide +kernel
theorem subd11_1_219 : subd11_1 [0, 0, -12] = true := by decide +kernel
theorem subd11_1_220 : subd11_1 [0, 0, -11] = true := by decide +kernel
theorem subd11_1_221 : subd11_1 [0, 0, -10] = true := by decide +kernel
theorem subd11_1_222 : subd11_1 [0, 0, -9] = true := by decide +kernel
theorem subd11_1_223 : subd11_1 [0, 0, -8] = true := by decide +kernel
theorem sbd11_1_6 : ∀ q ∈ blkd11_1_6, subd11_1 q = true := by
  unfold blkd11_1_6
  exact List.forall_mem_cons.2 ⟨subd11_1_192, List.forall_mem_cons.2 ⟨subd11_1_193, List.forall_mem_cons.2 ⟨subd11_1_194, List.forall_mem_cons.2 ⟨subd11_1_195, List.forall_mem_cons.2 ⟨subd11_1_196, List.forall_mem_cons.2 ⟨subd11_1_197, List.forall_mem_cons.2 ⟨subd11_1_198, List.forall_mem_cons.2 ⟨subd11_1_199, List.forall_mem_cons.2 ⟨subd11_1_200, List.forall_mem_cons.2 ⟨subd11_1_201, List.forall_mem_cons.2 ⟨subd11_1_202, List.forall_mem_cons.2 ⟨subd11_1_203, List.forall_mem_cons.2 ⟨subd11_1_204, List.forall_mem_cons.2 ⟨subd11_1_205, List.forall_mem_cons.2 ⟨subd11_1_206, List.forall_mem_cons.2 ⟨subd11_1_207, List.forall_mem_cons.2 ⟨subd11_1_208, List.forall_mem_cons.2 ⟨subd11_1_209, List.forall_mem_cons.2 ⟨subd11_1_210, List.forall_mem_cons.2 ⟨subd11_1_211, List.forall_mem_cons.2 ⟨subd11_1_212, List.forall_mem_cons.2 ⟨subd11_1_213, List.forall_mem_cons.2 ⟨subd11_1_214, List.forall_mem_cons.2 ⟨subd11_1_215, List.forall_mem_cons.2 ⟨subd11_1_216, List.forall_mem_cons.2 ⟨subd11_1_217, List.forall_mem_cons.2 ⟨subd11_1_218, List.forall_mem_cons.2 ⟨subd11_1_219, List.forall_mem_cons.2 ⟨subd11_1_220, List.forall_mem_cons.2 ⟨subd11_1_221, List.forall_mem_cons.2 ⟨subd11_1_222, List.forall_mem_cons.2 ⟨subd11_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_224 : subd11_1 [0, 0, -7] = true := by decide +kernel
theorem subd11_1_225 : subd11_1 [0, 0, -6] = true := by decide +kernel
theorem subd11_1_226 : subd11_1 [0, 0, -5] = true := by decide +kernel
theorem subd11_1_227 : subd11_1 [0, 0, -4] = true := by decide +kernel
theorem subd11_1_228 : subd11_1 [0, 0, -3] = true := by decide +kernel
theorem subd11_1_229 : subd11_1 [0, 0, -2] = true := by decide +kernel
theorem subd11_1_230 : subd11_1 [0, 0, -1] = true := by decide +kernel
theorem subd11_1_231 : subd11_1 [0, 0, 0] = true := by decide +kernel
theorem subd11_1_232 : subd11_1 [0, 0, 1] = true := by decide +kernel
theorem subd11_1_233 : subd11_1 [0, 0, 2] = true := by decide +kernel
theorem subd11_1_234 : subd11_1 [0, 0, 3] = true := by decide +kernel
theorem subd11_1_235 : subd11_1 [0, 0, 4] = true := by decide +kernel
theorem subd11_1_236 : subd11_1 [0, 0, 5] = true := by decide +kernel
theorem subd11_1_237 : subd11_1 [0, 0, 6] = true := by decide +kernel
theorem subd11_1_238 : subd11_1 [0, 0, 7] = true := by decide +kernel
theorem subd11_1_239 : subd11_1 [0, 0, 8] = true := by decide +kernel
theorem subd11_1_240 : subd11_1 [0, 0, 9] = true := by decide +kernel
theorem subd11_1_241 : subd11_1 [0, 0, 10] = true := by decide +kernel
theorem subd11_1_242 : subd11_1 [0, 0, 11] = true := by decide +kernel
theorem subd11_1_243 : subd11_1 [0, 0, 12] = true := by decide +kernel
theorem subd11_1_244 : subd11_1 [0, 0, 13] = true := by decide +kernel
theorem subd11_1_245 : subd11_1 [0, 0, 14] = true := by decide +kernel
theorem subd11_1_246 : subd11_1 [0, 0, 15] = true := by decide +kernel
theorem subd11_1_247 : subd11_1 [0, 0, 16] = true := by decide +kernel
theorem subd11_1_248 : subd11_1 [0, 0, 17] = true := by decide +kernel
theorem subd11_1_249 : subd11_1 [0, 0, 18] = true := by decide +kernel
theorem subd11_1_250 : subd11_1 [0, 0, 19] = true := by decide +kernel
theorem subd11_1_251 : subd11_1 [0, 0, 20] = true := by decide +kernel
theorem subd11_1_252 : subd11_1 [0, 0, 21] = true := by decide +kernel
theorem subd11_1_253 : subd11_1 [0, 0, 22] = true := by decide +kernel
theorem subd11_1_254 : subd11_1 [0, 0, 23] = true := by decide +kernel
theorem subd11_1_255 : subd11_1 [0, 1, -22] = true := by decide +kernel
theorem sbd11_1_7 : ∀ q ∈ blkd11_1_7, subd11_1 q = true := by
  unfold blkd11_1_7
  exact List.forall_mem_cons.2 ⟨subd11_1_224, List.forall_mem_cons.2 ⟨subd11_1_225, List.forall_mem_cons.2 ⟨subd11_1_226, List.forall_mem_cons.2 ⟨subd11_1_227, List.forall_mem_cons.2 ⟨subd11_1_228, List.forall_mem_cons.2 ⟨subd11_1_229, List.forall_mem_cons.2 ⟨subd11_1_230, List.forall_mem_cons.2 ⟨subd11_1_231, List.forall_mem_cons.2 ⟨subd11_1_232, List.forall_mem_cons.2 ⟨subd11_1_233, List.forall_mem_cons.2 ⟨subd11_1_234, List.forall_mem_cons.2 ⟨subd11_1_235, List.forall_mem_cons.2 ⟨subd11_1_236, List.forall_mem_cons.2 ⟨subd11_1_237, List.forall_mem_cons.2 ⟨subd11_1_238, List.forall_mem_cons.2 ⟨subd11_1_239, List.forall_mem_cons.2 ⟨subd11_1_240, List.forall_mem_cons.2 ⟨subd11_1_241, List.forall_mem_cons.2 ⟨subd11_1_242, List.forall_mem_cons.2 ⟨subd11_1_243, List.forall_mem_cons.2 ⟨subd11_1_244, List.forall_mem_cons.2 ⟨subd11_1_245, List.forall_mem_cons.2 ⟨subd11_1_246, List.forall_mem_cons.2 ⟨subd11_1_247, List.forall_mem_cons.2 ⟨subd11_1_248, List.forall_mem_cons.2 ⟨subd11_1_249, List.forall_mem_cons.2 ⟨subd11_1_250, List.forall_mem_cons.2 ⟨subd11_1_251, List.forall_mem_cons.2 ⟨subd11_1_252, List.forall_mem_cons.2 ⟨subd11_1_253, List.forall_mem_cons.2 ⟨subd11_1_254, List.forall_mem_cons.2 ⟨subd11_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_256 : subd11_1 [0, 1, -21] = true := by decide +kernel
theorem subd11_1_257 : subd11_1 [0, 1, -20] = true := by decide +kernel
theorem subd11_1_258 : subd11_1 [0, 1, -19] = true := by decide +kernel
theorem subd11_1_259 : subd11_1 [0, 1, -18] = true := by decide +kernel
theorem subd11_1_260 : subd11_1 [0, 1, -17] = true := by decide +kernel
theorem subd11_1_261 : subd11_1 [0, 1, -16] = true := by decide +kernel
theorem subd11_1_262 : subd11_1 [0, 1, -15] = true := by decide +kernel
theorem subd11_1_263 : subd11_1 [0, 1, -14] = true := by decide +kernel
theorem subd11_1_264 : subd11_1 [0, 1, -13] = true := by decide +kernel
theorem subd11_1_265 : subd11_1 [0, 1, -12] = true := by decide +kernel
theorem subd11_1_266 : subd11_1 [0, 1, -11] = true := by decide +kernel
theorem subd11_1_267 : subd11_1 [0, 1, -10] = true := by decide +kernel
theorem subd11_1_268 : subd11_1 [0, 1, -9] = true := by decide +kernel
theorem subd11_1_269 : subd11_1 [0, 1, -8] = true := by decide +kernel
theorem subd11_1_270 : subd11_1 [0, 1, -7] = true := by decide +kernel
theorem subd11_1_271 : subd11_1 [0, 1, -6] = true := by decide +kernel
theorem subd11_1_272 : subd11_1 [0, 1, -5] = true := by decide +kernel
theorem subd11_1_273 : subd11_1 [0, 1, -4] = true := by decide +kernel
theorem subd11_1_274 : subd11_1 [0, 1, -3] = true := by decide +kernel
theorem subd11_1_275 : subd11_1 [0, 1, -2] = true := by decide +kernel
theorem subd11_1_276 : subd11_1 [0, 1, -1] = true := by decide +kernel
theorem subd11_1_277 : subd11_1 [0, 1, 0] = true := by decide +kernel
theorem subd11_1_278 : subd11_1 [0, 1, 1] = true := by decide +kernel
theorem subd11_1_279 : subd11_1 [0, 1, 2] = true := by decide +kernel
theorem subd11_1_280 : subd11_1 [0, 1, 3] = true := by decide +kernel
theorem subd11_1_281 : subd11_1 [0, 1, 4] = true := by decide +kernel
theorem subd11_1_282 : subd11_1 [0, 1, 5] = true := by decide +kernel
theorem subd11_1_283 : subd11_1 [0, 1, 6] = true := by decide +kernel
theorem subd11_1_284 : subd11_1 [0, 1, 7] = true := by decide +kernel
theorem subd11_1_285 : subd11_1 [0, 1, 8] = true := by decide +kernel
theorem subd11_1_286 : subd11_1 [0, 1, 9] = true := by decide +kernel
theorem subd11_1_287 : subd11_1 [0, 1, 10] = true := by decide +kernel
theorem sbd11_1_8 : ∀ q ∈ blkd11_1_8, subd11_1 q = true := by
  unfold blkd11_1_8
  exact List.forall_mem_cons.2 ⟨subd11_1_256, List.forall_mem_cons.2 ⟨subd11_1_257, List.forall_mem_cons.2 ⟨subd11_1_258, List.forall_mem_cons.2 ⟨subd11_1_259, List.forall_mem_cons.2 ⟨subd11_1_260, List.forall_mem_cons.2 ⟨subd11_1_261, List.forall_mem_cons.2 ⟨subd11_1_262, List.forall_mem_cons.2 ⟨subd11_1_263, List.forall_mem_cons.2 ⟨subd11_1_264, List.forall_mem_cons.2 ⟨subd11_1_265, List.forall_mem_cons.2 ⟨subd11_1_266, List.forall_mem_cons.2 ⟨subd11_1_267, List.forall_mem_cons.2 ⟨subd11_1_268, List.forall_mem_cons.2 ⟨subd11_1_269, List.forall_mem_cons.2 ⟨subd11_1_270, List.forall_mem_cons.2 ⟨subd11_1_271, List.forall_mem_cons.2 ⟨subd11_1_272, List.forall_mem_cons.2 ⟨subd11_1_273, List.forall_mem_cons.2 ⟨subd11_1_274, List.forall_mem_cons.2 ⟨subd11_1_275, List.forall_mem_cons.2 ⟨subd11_1_276, List.forall_mem_cons.2 ⟨subd11_1_277, List.forall_mem_cons.2 ⟨subd11_1_278, List.forall_mem_cons.2 ⟨subd11_1_279, List.forall_mem_cons.2 ⟨subd11_1_280, List.forall_mem_cons.2 ⟨subd11_1_281, List.forall_mem_cons.2 ⟨subd11_1_282, List.forall_mem_cons.2 ⟨subd11_1_283, List.forall_mem_cons.2 ⟨subd11_1_284, List.forall_mem_cons.2 ⟨subd11_1_285, List.forall_mem_cons.2 ⟨subd11_1_286, List.forall_mem_cons.2 ⟨subd11_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_288 : subd11_1 [0, 1, 11] = true := by decide +kernel
theorem subd11_1_289 : subd11_1 [0, 1, 12] = true := by decide +kernel
theorem subd11_1_290 : subd11_1 [0, 1, 13] = true := by decide +kernel
theorem subd11_1_291 : subd11_1 [0, 1, 14] = true := by decide +kernel
theorem subd11_1_292 : subd11_1 [0, 1, 15] = true := by decide +kernel
theorem subd11_1_293 : subd11_1 [0, 1, 16] = true := by decide +kernel
theorem subd11_1_294 : subd11_1 [0, 1, 17] = true := by decide +kernel
theorem subd11_1_295 : subd11_1 [0, 1, 18] = true := by decide +kernel
theorem subd11_1_296 : subd11_1 [0, 1, 19] = true := by decide +kernel
theorem subd11_1_297 : subd11_1 [0, 1, 20] = true := by decide +kernel
theorem subd11_1_298 : subd11_1 [0, 2, -12] = true := by decide +kernel
theorem subd11_1_299 : subd11_1 [0, 2, -11] = true := by decide +kernel
theorem subd11_1_300 : subd11_1 [0, 2, -10] = true := by decide +kernel
theorem subd11_1_301 : subd11_1 [0, 2, -9] = true := by decide +kernel
theorem subd11_1_302 : subd11_1 [0, 2, -8] = true := by decide +kernel
theorem subd11_1_303 : subd11_1 [0, 2, -7] = true := by decide +kernel
theorem subd11_1_304 : subd11_1 [0, 2, -6] = true := by decide +kernel
theorem subd11_1_305 : subd11_1 [0, 2, -5] = true := by decide +kernel
theorem subd11_1_306 : subd11_1 [0, 2, -4] = true := by decide +kernel
theorem subd11_1_307 : subd11_1 [0, 2, -3] = true := by decide +kernel
theorem subd11_1_308 : subd11_1 [0, 2, -2] = true := by decide +kernel
theorem subd11_1_309 : subd11_1 [0, 2, -1] = true := by decide +kernel
theorem subd11_1_310 : subd11_1 [0, 2, 0] = true := by decide +kernel
theorem subd11_1_311 : subd11_1 [0, 2, 1] = true := by decide +kernel
theorem subd11_1_312 : subd11_1 [0, 2, 2] = true := by decide +kernel
theorem subd11_1_313 : subd11_1 [0, 2, 3] = true := by decide +kernel
theorem subd11_1_314 : subd11_1 [0, 2, 4] = true := by decide +kernel
theorem subd11_1_315 : subd11_1 [0, 2, 5] = true := by decide +kernel
theorem subd11_1_316 : subd11_1 [0, 2, 6] = true := by decide +kernel
theorem subd11_1_317 : subd11_1 [0, 2, 7] = true := by decide +kernel
theorem subd11_1_318 : subd11_1 [0, 2, 8] = true := by decide +kernel
theorem subd11_1_319 : subd11_1 [0, 2, 9] = true := by decide +kernel
theorem sbd11_1_9 : ∀ q ∈ blkd11_1_9, subd11_1 q = true := by
  unfold blkd11_1_9
  exact List.forall_mem_cons.2 ⟨subd11_1_288, List.forall_mem_cons.2 ⟨subd11_1_289, List.forall_mem_cons.2 ⟨subd11_1_290, List.forall_mem_cons.2 ⟨subd11_1_291, List.forall_mem_cons.2 ⟨subd11_1_292, List.forall_mem_cons.2 ⟨subd11_1_293, List.forall_mem_cons.2 ⟨subd11_1_294, List.forall_mem_cons.2 ⟨subd11_1_295, List.forall_mem_cons.2 ⟨subd11_1_296, List.forall_mem_cons.2 ⟨subd11_1_297, List.forall_mem_cons.2 ⟨subd11_1_298, List.forall_mem_cons.2 ⟨subd11_1_299, List.forall_mem_cons.2 ⟨subd11_1_300, List.forall_mem_cons.2 ⟨subd11_1_301, List.forall_mem_cons.2 ⟨subd11_1_302, List.forall_mem_cons.2 ⟨subd11_1_303, List.forall_mem_cons.2 ⟨subd11_1_304, List.forall_mem_cons.2 ⟨subd11_1_305, List.forall_mem_cons.2 ⟨subd11_1_306, List.forall_mem_cons.2 ⟨subd11_1_307, List.forall_mem_cons.2 ⟨subd11_1_308, List.forall_mem_cons.2 ⟨subd11_1_309, List.forall_mem_cons.2 ⟨subd11_1_310, List.forall_mem_cons.2 ⟨subd11_1_311, List.forall_mem_cons.2 ⟨subd11_1_312, List.forall_mem_cons.2 ⟨subd11_1_313, List.forall_mem_cons.2 ⟨subd11_1_314, List.forall_mem_cons.2 ⟨subd11_1_315, List.forall_mem_cons.2 ⟨subd11_1_316, List.forall_mem_cons.2 ⟨subd11_1_317, List.forall_mem_cons.2 ⟨subd11_1_318, List.forall_mem_cons.2 ⟨subd11_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
