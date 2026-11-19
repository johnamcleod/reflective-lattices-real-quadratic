import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_3_96 : subd12_3 [-1, -1, 8] = true := by decide +kernel
theorem subd12_3_97 : subd12_3 [-1, -1, 9] = true := by decide +kernel
theorem subd12_3_98 : subd12_3 [-1, -1, 10] = true := by decide +kernel
theorem subd12_3_99 : subd12_3 [-1, 0, -12] = true := by decide +kernel
theorem subd12_3_100 : subd12_3 [-1, 0, -11] = true := by decide +kernel
theorem subd12_3_101 : subd12_3 [-1, 0, -10] = true := by decide +kernel
theorem subd12_3_102 : subd12_3 [-1, 0, -9] = true := by decide +kernel
theorem subd12_3_103 : subd12_3 [-1, 0, -8] = true := by decide +kernel
theorem subd12_3_104 : subd12_3 [-1, 0, -7] = true := by decide +kernel
theorem subd12_3_105 : subd12_3 [-1, 0, -6] = true := by decide +kernel
theorem subd12_3_106 : subd12_3 [-1, 0, -5] = true := by decide +kernel
theorem subd12_3_107 : subd12_3 [-1, 0, -4] = true := by decide +kernel
theorem subd12_3_108 : subd12_3 [-1, 0, -3] = true := by decide +kernel
theorem subd12_3_109 : subd12_3 [-1, 0, -2] = true := by decide +kernel
theorem subd12_3_110 : subd12_3 [-1, 0, -1] = true := by decide +kernel
theorem subd12_3_111 : subd12_3 [-1, 0, 0] = true := by decide +kernel
theorem subd12_3_112 : subd12_3 [-1, 0, 1] = true := by decide +kernel
theorem subd12_3_113 : subd12_3 [-1, 0, 2] = true := by decide +kernel
theorem subd12_3_114 : subd12_3 [-1, 0, 3] = true := by decide +kernel
theorem subd12_3_115 : subd12_3 [-1, 0, 4] = true := by decide +kernel
theorem subd12_3_116 : subd12_3 [-1, 0, 5] = true := by decide +kernel
theorem subd12_3_117 : subd12_3 [-1, 0, 6] = true := by decide +kernel
theorem subd12_3_118 : subd12_3 [-1, 0, 7] = true := by decide +kernel
theorem subd12_3_119 : subd12_3 [-1, 0, 8] = true := by decide +kernel
theorem subd12_3_120 : subd12_3 [-1, 0, 9] = true := by decide +kernel
theorem subd12_3_121 : subd12_3 [-1, 0, 10] = true := by decide +kernel
theorem subd12_3_122 : subd12_3 [-1, 0, 11] = true := by decide +kernel
theorem subd12_3_123 : subd12_3 [-1, 1, -11] = true := by decide +kernel
theorem subd12_3_124 : subd12_3 [-1, 1, -10] = true := by decide +kernel
theorem subd12_3_125 : subd12_3 [-1, 1, -9] = true := by decide +kernel
theorem subd12_3_126 : subd12_3 [-1, 1, -8] = true := by decide +kernel
theorem subd12_3_127 : subd12_3 [-1, 1, -7] = true := by decide +kernel
theorem sbd12_3_3 : ∀ q ∈ blkd12_3_3, subd12_3 q = true := by
  unfold blkd12_3_3
  exact List.forall_mem_cons.2 ⟨subd12_3_96, List.forall_mem_cons.2 ⟨subd12_3_97, List.forall_mem_cons.2 ⟨subd12_3_98, List.forall_mem_cons.2 ⟨subd12_3_99, List.forall_mem_cons.2 ⟨subd12_3_100, List.forall_mem_cons.2 ⟨subd12_3_101, List.forall_mem_cons.2 ⟨subd12_3_102, List.forall_mem_cons.2 ⟨subd12_3_103, List.forall_mem_cons.2 ⟨subd12_3_104, List.forall_mem_cons.2 ⟨subd12_3_105, List.forall_mem_cons.2 ⟨subd12_3_106, List.forall_mem_cons.2 ⟨subd12_3_107, List.forall_mem_cons.2 ⟨subd12_3_108, List.forall_mem_cons.2 ⟨subd12_3_109, List.forall_mem_cons.2 ⟨subd12_3_110, List.forall_mem_cons.2 ⟨subd12_3_111, List.forall_mem_cons.2 ⟨subd12_3_112, List.forall_mem_cons.2 ⟨subd12_3_113, List.forall_mem_cons.2 ⟨subd12_3_114, List.forall_mem_cons.2 ⟨subd12_3_115, List.forall_mem_cons.2 ⟨subd12_3_116, List.forall_mem_cons.2 ⟨subd12_3_117, List.forall_mem_cons.2 ⟨subd12_3_118, List.forall_mem_cons.2 ⟨subd12_3_119, List.forall_mem_cons.2 ⟨subd12_3_120, List.forall_mem_cons.2 ⟨subd12_3_121, List.forall_mem_cons.2 ⟨subd12_3_122, List.forall_mem_cons.2 ⟨subd12_3_123, List.forall_mem_cons.2 ⟨subd12_3_124, List.forall_mem_cons.2 ⟨subd12_3_125, List.forall_mem_cons.2 ⟨subd12_3_126, List.forall_mem_cons.2 ⟨subd12_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_128 : subd12_3 [-1, 1, -6] = true := by decide +kernel
theorem subd12_3_129 : subd12_3 [-1, 1, -5] = true := by decide +kernel
theorem subd12_3_130 : subd12_3 [-1, 1, -4] = true := by decide +kernel
theorem subd12_3_131 : subd12_3 [-1, 1, -3] = true := by decide +kernel
theorem subd12_3_132 : subd12_3 [-1, 1, -2] = true := by decide +kernel
theorem subd12_3_133 : subd12_3 [-1, 1, -1] = true := by decide +kernel
theorem subd12_3_134 : subd12_3 [-1, 1, 0] = true := by decide +kernel
theorem subd12_3_135 : subd12_3 [-1, 1, 1] = true := by decide +kernel
theorem subd12_3_136 : subd12_3 [-1, 1, 2] = true := by decide +kernel
theorem subd12_3_137 : subd12_3 [-1, 1, 3] = true := by decide +kernel
theorem subd12_3_138 : subd12_3 [-1, 1, 4] = true := by decide +kernel
theorem subd12_3_139 : subd12_3 [-1, 1, 5] = true := by decide +kernel
theorem subd12_3_140 : subd12_3 [-1, 1, 6] = true := by decide +kernel
theorem subd12_3_141 : subd12_3 [-1, 1, 7] = true := by decide +kernel
theorem subd12_3_142 : subd12_3 [-1, 1, 8] = true := by decide +kernel
theorem subd12_3_143 : subd12_3 [-1, 1, 9] = true := by decide +kernel
theorem subd12_3_144 : subd12_3 [-1, 1, 10] = true := by decide +kernel
theorem subd12_3_145 : subd12_3 [-1, 2, -9] = true := by decide +kernel
theorem subd12_3_146 : subd12_3 [-1, 2, -8] = true := by decide +kernel
theorem subd12_3_147 : subd12_3 [-1, 2, -7] = true := by decide +kernel
theorem subd12_3_148 : subd12_3 [-1, 2, -6] = true := by decide +kernel
theorem subd12_3_149 : subd12_3 [-1, 2, -5] = true := by decide +kernel
theorem subd12_3_150 : subd12_3 [-1, 2, -4] = true := by decide +kernel
theorem subd12_3_151 : subd12_3 [-1, 2, -3] = true := by decide +kernel
theorem subd12_3_152 : subd12_3 [-1, 2, -2] = true := by decide +kernel
theorem subd12_3_153 : subd12_3 [-1, 2, -1] = true := by decide +kernel
theorem subd12_3_154 : subd12_3 [-1, 2, 0] = true := by decide +kernel
theorem subd12_3_155 : subd12_3 [-1, 2, 1] = true := by decide +kernel
theorem subd12_3_156 : subd12_3 [-1, 2, 2] = true := by decide +kernel
theorem subd12_3_157 : subd12_3 [-1, 2, 3] = true := by decide +kernel
theorem subd12_3_158 : subd12_3 [-1, 2, 4] = true := by decide +kernel
theorem subd12_3_159 : subd12_3 [-1, 2, 5] = true := by decide +kernel
theorem sbd12_3_4 : ∀ q ∈ blkd12_3_4, subd12_3 q = true := by
  unfold blkd12_3_4
  exact List.forall_mem_cons.2 ⟨subd12_3_128, List.forall_mem_cons.2 ⟨subd12_3_129, List.forall_mem_cons.2 ⟨subd12_3_130, List.forall_mem_cons.2 ⟨subd12_3_131, List.forall_mem_cons.2 ⟨subd12_3_132, List.forall_mem_cons.2 ⟨subd12_3_133, List.forall_mem_cons.2 ⟨subd12_3_134, List.forall_mem_cons.2 ⟨subd12_3_135, List.forall_mem_cons.2 ⟨subd12_3_136, List.forall_mem_cons.2 ⟨subd12_3_137, List.forall_mem_cons.2 ⟨subd12_3_138, List.forall_mem_cons.2 ⟨subd12_3_139, List.forall_mem_cons.2 ⟨subd12_3_140, List.forall_mem_cons.2 ⟨subd12_3_141, List.forall_mem_cons.2 ⟨subd12_3_142, List.forall_mem_cons.2 ⟨subd12_3_143, List.forall_mem_cons.2 ⟨subd12_3_144, List.forall_mem_cons.2 ⟨subd12_3_145, List.forall_mem_cons.2 ⟨subd12_3_146, List.forall_mem_cons.2 ⟨subd12_3_147, List.forall_mem_cons.2 ⟨subd12_3_148, List.forall_mem_cons.2 ⟨subd12_3_149, List.forall_mem_cons.2 ⟨subd12_3_150, List.forall_mem_cons.2 ⟨subd12_3_151, List.forall_mem_cons.2 ⟨subd12_3_152, List.forall_mem_cons.2 ⟨subd12_3_153, List.forall_mem_cons.2 ⟨subd12_3_154, List.forall_mem_cons.2 ⟨subd12_3_155, List.forall_mem_cons.2 ⟨subd12_3_156, List.forall_mem_cons.2 ⟨subd12_3_157, List.forall_mem_cons.2 ⟨subd12_3_158, List.forall_mem_cons.2 ⟨subd12_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_160 : subd12_3 [-1, 2, 6] = true := by decide +kernel
theorem subd12_3_161 : subd12_3 [-1, 2, 7] = true := by decide +kernel
theorem subd12_3_162 : subd12_3 [-1, 2, 8] = true := by decide +kernel
theorem subd12_3_163 : subd12_3 [0, -4] = true := by decide +kernel
theorem subd12_3_164 : subd12_3 [0, -3] = true := by decide +kernel
theorem subd12_3_165 : subd12_3 [0, -2, -9] = true := by decide +kernel
theorem subd12_3_166 : subd12_3 [0, -2, -8] = true := by decide +kernel
theorem subd12_3_167 : subd12_3 [0, -2, -7] = true := by decide +kernel
theorem subd12_3_168 : subd12_3 [0, -2, -6] = true := by decide +kernel
theorem subd12_3_169 : subd12_3 [0, -2, -5] = true := by decide +kernel
theorem subd12_3_170 : subd12_3 [0, -2, -4] = true := by decide +kernel
theorem subd12_3_171 : subd12_3 [0, -2, -3] = true := by decide +kernel
theorem subd12_3_172 : subd12_3 [0, -2, -2] = true := by decide +kernel
theorem subd12_3_173 : subd12_3 [0, -2, -1] = true := by decide +kernel
theorem subd12_3_174 : subd12_3 [0, -2, 0] = true := by decide +kernel
theorem subd12_3_175 : subd12_3 [0, -2, 1] = true := by decide +kernel
theorem subd12_3_176 : subd12_3 [0, -2, 2] = true := by decide +kernel
theorem subd12_3_177 : subd12_3 [0, -2, 3] = true := by decide +kernel
theorem subd12_3_178 : subd12_3 [0, -2, 4] = true := by decide +kernel
theorem subd12_3_179 : subd12_3 [0, -2, 5] = true := by decide +kernel
theorem subd12_3_180 : subd12_3 [0, -2, 6] = true := by decide +kernel
theorem subd12_3_181 : subd12_3 [0, -2, 7] = true := by decide +kernel
theorem subd12_3_182 : subd12_3 [0, -2, 8] = true := by decide +kernel
theorem subd12_3_183 : subd12_3 [0, -2, 9] = true := by decide +kernel
theorem subd12_3_184 : subd12_3 [0, -1, -12] = true := by decide +kernel
theorem subd12_3_185 : subd12_3 [0, -1, -11] = true := by decide +kernel
theorem subd12_3_186 : subd12_3 [0, -1, -10] = true := by decide +kernel
theorem subd12_3_187 : subd12_3 [0, -1, -9] = true := by decide +kernel
theorem subd12_3_188 : subd12_3 [0, -1, -8] = true := by decide +kernel
theorem subd12_3_189 : subd12_3 [0, -1, -7] = true := by decide +kernel
theorem subd12_3_190 : subd12_3 [0, -1, -6] = true := by decide +kernel
theorem subd12_3_191 : subd12_3 [0, -1, -5] = true := by decide +kernel
theorem sbd12_3_5 : ∀ q ∈ blkd12_3_5, subd12_3 q = true := by
  unfold blkd12_3_5
  exact List.forall_mem_cons.2 ⟨subd12_3_160, List.forall_mem_cons.2 ⟨subd12_3_161, List.forall_mem_cons.2 ⟨subd12_3_162, List.forall_mem_cons.2 ⟨subd12_3_163, List.forall_mem_cons.2 ⟨subd12_3_164, List.forall_mem_cons.2 ⟨subd12_3_165, List.forall_mem_cons.2 ⟨subd12_3_166, List.forall_mem_cons.2 ⟨subd12_3_167, List.forall_mem_cons.2 ⟨subd12_3_168, List.forall_mem_cons.2 ⟨subd12_3_169, List.forall_mem_cons.2 ⟨subd12_3_170, List.forall_mem_cons.2 ⟨subd12_3_171, List.forall_mem_cons.2 ⟨subd12_3_172, List.forall_mem_cons.2 ⟨subd12_3_173, List.forall_mem_cons.2 ⟨subd12_3_174, List.forall_mem_cons.2 ⟨subd12_3_175, List.forall_mem_cons.2 ⟨subd12_3_176, List.forall_mem_cons.2 ⟨subd12_3_177, List.forall_mem_cons.2 ⟨subd12_3_178, List.forall_mem_cons.2 ⟨subd12_3_179, List.forall_mem_cons.2 ⟨subd12_3_180, List.forall_mem_cons.2 ⟨subd12_3_181, List.forall_mem_cons.2 ⟨subd12_3_182, List.forall_mem_cons.2 ⟨subd12_3_183, List.forall_mem_cons.2 ⟨subd12_3_184, List.forall_mem_cons.2 ⟨subd12_3_185, List.forall_mem_cons.2 ⟨subd12_3_186, List.forall_mem_cons.2 ⟨subd12_3_187, List.forall_mem_cons.2 ⟨subd12_3_188, List.forall_mem_cons.2 ⟨subd12_3_189, List.forall_mem_cons.2 ⟨subd12_3_190, List.forall_mem_cons.2 ⟨subd12_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_192 : subd12_3 [0, -1, -4] = true := by decide +kernel
theorem subd12_3_193 : subd12_3 [0, -1, -3] = true := by decide +kernel
theorem subd12_3_194 : subd12_3 [0, -1, -2] = true := by decide +kernel
theorem subd12_3_195 : subd12_3 [0, -1, -1] = true := by decide +kernel
theorem subd12_3_196 : subd12_3 [0, -1, 0] = true := by decide +kernel
theorem subd12_3_197 : subd12_3 [0, -1, 1] = true := by decide +kernel
theorem subd12_3_198 : subd12_3 [0, -1, 2] = true := by decide +kernel
theorem subd12_3_199 : subd12_3 [0, -1, 3] = true := by decide +kernel
theorem subd12_3_200 : subd12_3 [0, -1, 4] = true := by decide +kernel
theorem subd12_3_201 : subd12_3 [0, -1, 5] = true := by decide +kernel
theorem subd12_3_202 : subd12_3 [0, -1, 6] = true := by decide +kernel
theorem subd12_3_203 : subd12_3 [0, -1, 7] = true := by decide +kernel
theorem subd12_3_204 : subd12_3 [0, -1, 8] = true := by decide +kernel
theorem subd12_3_205 : subd12_3 [0, -1, 9] = true := by decide +kernel
theorem subd12_3_206 : subd12_3 [0, -1, 10] = true := by decide +kernel
theorem subd12_3_207 : subd12_3 [0, -1, 11] = true := by decide +kernel
theorem subd12_3_208 : subd12_3 [0, 0, -13] = true := by decide +kernel
theorem subd12_3_209 : subd12_3 [0, 0, -12] = true := by decide +kernel
theorem subd12_3_210 : subd12_3 [0, 0, -11] = true := by decide +kernel
theorem subd12_3_211 : subd12_3 [0, 0, -10] = true := by decide +kernel
theorem subd12_3_212 : subd12_3 [0, 0, -9] = true := by decide +kernel
theorem subd12_3_213 : subd12_3 [0, 0, -8] = true := by decide +kernel
theorem subd12_3_214 : subd12_3 [0, 0, -7] = true := by decide +kernel
theorem subd12_3_215 : subd12_3 [0, 0, -6] = true := by decide +kernel
theorem subd12_3_216 : subd12_3 [0, 0, -5] = true := by decide +kernel
theorem subd12_3_217 : subd12_3 [0, 0, -4] = true := by decide +kernel
theorem subd12_3_218 : subd12_3 [0, 0, -3] = true := by decide +kernel
theorem subd12_3_219 : subd12_3 [0, 0, -2] = true := by decide +kernel
theorem subd12_3_220 : subd12_3 [0, 0, -1] = true := by decide +kernel
theorem subd12_3_221 : subd12_3 [0, 0, 0] = true := by decide +kernel
theorem subd12_3_222 : subd12_3 [0, 0, 1] = true := by decide +kernel
theorem subd12_3_223 : subd12_3 [0, 0, 2] = true := by decide +kernel
theorem sbd12_3_6 : ∀ q ∈ blkd12_3_6, subd12_3 q = true := by
  unfold blkd12_3_6
  exact List.forall_mem_cons.2 ⟨subd12_3_192, List.forall_mem_cons.2 ⟨subd12_3_193, List.forall_mem_cons.2 ⟨subd12_3_194, List.forall_mem_cons.2 ⟨subd12_3_195, List.forall_mem_cons.2 ⟨subd12_3_196, List.forall_mem_cons.2 ⟨subd12_3_197, List.forall_mem_cons.2 ⟨subd12_3_198, List.forall_mem_cons.2 ⟨subd12_3_199, List.forall_mem_cons.2 ⟨subd12_3_200, List.forall_mem_cons.2 ⟨subd12_3_201, List.forall_mem_cons.2 ⟨subd12_3_202, List.forall_mem_cons.2 ⟨subd12_3_203, List.forall_mem_cons.2 ⟨subd12_3_204, List.forall_mem_cons.2 ⟨subd12_3_205, List.forall_mem_cons.2 ⟨subd12_3_206, List.forall_mem_cons.2 ⟨subd12_3_207, List.forall_mem_cons.2 ⟨subd12_3_208, List.forall_mem_cons.2 ⟨subd12_3_209, List.forall_mem_cons.2 ⟨subd12_3_210, List.forall_mem_cons.2 ⟨subd12_3_211, List.forall_mem_cons.2 ⟨subd12_3_212, List.forall_mem_cons.2 ⟨subd12_3_213, List.forall_mem_cons.2 ⟨subd12_3_214, List.forall_mem_cons.2 ⟨subd12_3_215, List.forall_mem_cons.2 ⟨subd12_3_216, List.forall_mem_cons.2 ⟨subd12_3_217, List.forall_mem_cons.2 ⟨subd12_3_218, List.forall_mem_cons.2 ⟨subd12_3_219, List.forall_mem_cons.2 ⟨subd12_3_220, List.forall_mem_cons.2 ⟨subd12_3_221, List.forall_mem_cons.2 ⟨subd12_3_222, List.forall_mem_cons.2 ⟨subd12_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_224 : subd12_3 [0, 0, 3] = true := by decide +kernel
theorem subd12_3_225 : subd12_3 [0, 0, 4] = true := by decide +kernel
theorem subd12_3_226 : subd12_3 [0, 0, 5] = true := by decide +kernel
theorem subd12_3_227 : subd12_3 [0, 0, 6] = true := by decide +kernel
theorem subd12_3_228 : subd12_3 [0, 0, 7] = true := by decide +kernel
theorem subd12_3_229 : subd12_3 [0, 0, 8] = true := by decide +kernel
theorem subd12_3_230 : subd12_3 [0, 0, 9] = true := by decide +kernel
theorem subd12_3_231 : subd12_3 [0, 0, 10] = true := by decide +kernel
theorem subd12_3_232 : subd12_3 [0, 0, 11] = true := by decide +kernel
theorem subd12_3_233 : subd12_3 [0, 0, 12] = true := by decide +kernel
theorem subd12_3_234 : subd12_3 [0, 1, -12] = true := by decide +kernel
theorem subd12_3_235 : subd12_3 [0, 1, -11] = true := by decide +kernel
theorem subd12_3_236 : subd12_3 [0, 1, -10] = true := by decide +kernel
theorem subd12_3_237 : subd12_3 [0, 1, -9] = true := by decide +kernel
theorem subd12_3_238 : subd12_3 [0, 1, -8] = true := by decide +kernel
theorem subd12_3_239 : subd12_3 [0, 1, -7] = true := by decide +kernel
theorem subd12_3_240 : subd12_3 [0, 1, -6] = true := by decide +kernel
theorem subd12_3_241 : subd12_3 [0, 1, -5] = true := by decide +kernel
theorem subd12_3_242 : subd12_3 [0, 1, -4] = true := by decide +kernel
theorem subd12_3_243 : subd12_3 [0, 1, -3] = true := by decide +kernel
theorem subd12_3_244 : subd12_3 [0, 1, -2] = true := by decide +kernel
theorem subd12_3_245 : subd12_3 [0, 1, -1] = true := by decide +kernel
theorem subd12_3_246 : subd12_3 [0, 1, 0] = true := by decide +kernel
theorem subd12_3_247 : subd12_3 [0, 1, 1] = true := by decide +kernel
theorem subd12_3_248 : subd12_3 [0, 1, 2] = true := by decide +kernel
theorem subd12_3_249 : subd12_3 [0, 1, 3] = true := by decide +kernel
theorem subd12_3_250 : subd12_3 [0, 1, 4] = true := by decide +kernel
theorem subd12_3_251 : subd12_3 [0, 1, 5] = true := by decide +kernel
theorem subd12_3_252 : subd12_3 [0, 1, 6] = true := by decide +kernel
theorem subd12_3_253 : subd12_3 [0, 1, 7] = true := by decide +kernel
theorem subd12_3_254 : subd12_3 [0, 1, 8] = true := by decide +kernel
theorem subd12_3_255 : subd12_3 [0, 1, 9] = true := by decide +kernel
theorem sbd12_3_7 : ∀ q ∈ blkd12_3_7, subd12_3 q = true := by
  unfold blkd12_3_7
  exact List.forall_mem_cons.2 ⟨subd12_3_224, List.forall_mem_cons.2 ⟨subd12_3_225, List.forall_mem_cons.2 ⟨subd12_3_226, List.forall_mem_cons.2 ⟨subd12_3_227, List.forall_mem_cons.2 ⟨subd12_3_228, List.forall_mem_cons.2 ⟨subd12_3_229, List.forall_mem_cons.2 ⟨subd12_3_230, List.forall_mem_cons.2 ⟨subd12_3_231, List.forall_mem_cons.2 ⟨subd12_3_232, List.forall_mem_cons.2 ⟨subd12_3_233, List.forall_mem_cons.2 ⟨subd12_3_234, List.forall_mem_cons.2 ⟨subd12_3_235, List.forall_mem_cons.2 ⟨subd12_3_236, List.forall_mem_cons.2 ⟨subd12_3_237, List.forall_mem_cons.2 ⟨subd12_3_238, List.forall_mem_cons.2 ⟨subd12_3_239, List.forall_mem_cons.2 ⟨subd12_3_240, List.forall_mem_cons.2 ⟨subd12_3_241, List.forall_mem_cons.2 ⟨subd12_3_242, List.forall_mem_cons.2 ⟨subd12_3_243, List.forall_mem_cons.2 ⟨subd12_3_244, List.forall_mem_cons.2 ⟨subd12_3_245, List.forall_mem_cons.2 ⟨subd12_3_246, List.forall_mem_cons.2 ⟨subd12_3_247, List.forall_mem_cons.2 ⟨subd12_3_248, List.forall_mem_cons.2 ⟨subd12_3_249, List.forall_mem_cons.2 ⟨subd12_3_250, List.forall_mem_cons.2 ⟨subd12_3_251, List.forall_mem_cons.2 ⟨subd12_3_252, List.forall_mem_cons.2 ⟨subd12_3_253, List.forall_mem_cons.2 ⟨subd12_3_254, List.forall_mem_cons.2 ⟨subd12_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_256 : subd12_3 [0, 1, 10] = true := by decide +kernel
theorem subd12_3_257 : subd12_3 [0, 1, 11] = true := by decide +kernel
theorem subd12_3_258 : subd12_3 [0, 2, -10] = true := by decide +kernel
theorem subd12_3_259 : subd12_3 [0, 2, -9] = true := by decide +kernel
theorem subd12_3_260 : subd12_3 [0, 2, -8] = true := by decide +kernel
theorem subd12_3_261 : subd12_3 [0, 2, -7] = true := by decide +kernel
theorem subd12_3_262 : subd12_3 [0, 2, -6] = true := by decide +kernel
theorem subd12_3_263 : subd12_3 [0, 2, -5] = true := by decide +kernel
theorem subd12_3_264 : subd12_3 [0, 2, -4] = true := by decide +kernel
theorem subd12_3_265 : subd12_3 [0, 2, -3] = true := by decide +kernel
theorem subd12_3_266 : subd12_3 [0, 2, -2] = true := by decide +kernel
theorem subd12_3_267 : subd12_3 [0, 2, -1] = true := by decide +kernel
theorem subd12_3_268 : subd12_3 [0, 2, 0] = true := by decide +kernel
theorem subd12_3_269 : subd12_3 [0, 2, 1] = true := by decide +kernel
theorem subd12_3_270 : subd12_3 [0, 2, 2] = true := by decide +kernel
theorem subd12_3_271 : subd12_3 [0, 2, 3] = true := by decide +kernel
theorem subd12_3_272 : subd12_3 [0, 2, 4] = true := by decide +kernel
theorem subd12_3_273 : subd12_3 [0, 2, 5] = true := by decide +kernel
theorem subd12_3_274 : subd12_3 [0, 2, 6] = true := by decide +kernel
theorem subd12_3_275 : subd12_3 [0, 2, 7] = true := by decide +kernel
theorem subd12_3_276 : subd12_3 [0, 2, 8] = true := by decide +kernel
theorem subd12_3_277 : subd12_3 [0, 3] = true := by decide +kernel
theorem subd12_3_278 : subd12_3 [1, -3] = true := by decide +kernel
theorem subd12_3_279 : subd12_3 [1, -2, -9] = true := by decide +kernel
theorem subd12_3_280 : subd12_3 [1, -2, -8] = true := by decide +kernel
theorem subd12_3_281 : subd12_3 [1, -2, -7] = true := by decide +kernel
theorem subd12_3_282 : subd12_3 [1, -2, -6] = true := by decide +kernel
theorem subd12_3_283 : subd12_3 [1, -2, -5] = true := by decide +kernel
theorem subd12_3_284 : subd12_3 [1, -2, -4] = true := by decide +kernel
theorem subd12_3_285 : subd12_3 [1, -2, -3] = true := by decide +kernel
theorem subd12_3_286 : subd12_3 [1, -2, -2] = true := by decide +kernel
theorem subd12_3_287 : subd12_3 [1, -2, -1] = true := by decide +kernel
theorem sbd12_3_8 : ∀ q ∈ blkd12_3_8, subd12_3 q = true := by
  unfold blkd12_3_8
  exact List.forall_mem_cons.2 ⟨subd12_3_256, List.forall_mem_cons.2 ⟨subd12_3_257, List.forall_mem_cons.2 ⟨subd12_3_258, List.forall_mem_cons.2 ⟨subd12_3_259, List.forall_mem_cons.2 ⟨subd12_3_260, List.forall_mem_cons.2 ⟨subd12_3_261, List.forall_mem_cons.2 ⟨subd12_3_262, List.forall_mem_cons.2 ⟨subd12_3_263, List.forall_mem_cons.2 ⟨subd12_3_264, List.forall_mem_cons.2 ⟨subd12_3_265, List.forall_mem_cons.2 ⟨subd12_3_266, List.forall_mem_cons.2 ⟨subd12_3_267, List.forall_mem_cons.2 ⟨subd12_3_268, List.forall_mem_cons.2 ⟨subd12_3_269, List.forall_mem_cons.2 ⟨subd12_3_270, List.forall_mem_cons.2 ⟨subd12_3_271, List.forall_mem_cons.2 ⟨subd12_3_272, List.forall_mem_cons.2 ⟨subd12_3_273, List.forall_mem_cons.2 ⟨subd12_3_274, List.forall_mem_cons.2 ⟨subd12_3_275, List.forall_mem_cons.2 ⟨subd12_3_276, List.forall_mem_cons.2 ⟨subd12_3_277, List.forall_mem_cons.2 ⟨subd12_3_278, List.forall_mem_cons.2 ⟨subd12_3_279, List.forall_mem_cons.2 ⟨subd12_3_280, List.forall_mem_cons.2 ⟨subd12_3_281, List.forall_mem_cons.2 ⟨subd12_3_282, List.forall_mem_cons.2 ⟨subd12_3_283, List.forall_mem_cons.2 ⟨subd12_3_284, List.forall_mem_cons.2 ⟨subd12_3_285, List.forall_mem_cons.2 ⟨subd12_3_286, List.forall_mem_cons.2 ⟨subd12_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_288 : subd12_3 [1, -2, 0] = true := by decide +kernel
theorem subd12_3_289 : subd12_3 [1, -2, 1] = true := by decide +kernel
theorem subd12_3_290 : subd12_3 [1, -2, 2] = true := by decide +kernel
theorem subd12_3_291 : subd12_3 [1, -2, 3] = true := by decide +kernel
theorem subd12_3_292 : subd12_3 [1, -2, 4] = true := by decide +kernel
theorem subd12_3_293 : subd12_3 [1, -2, 5] = true := by decide +kernel
theorem subd12_3_294 : subd12_3 [1, -2, 6] = true := by decide +kernel
theorem subd12_3_295 : subd12_3 [1, -2, 7] = true := by decide +kernel
theorem subd12_3_296 : subd12_3 [1, -2, 8] = true := by decide +kernel
theorem subd12_3_297 : subd12_3 [1, -1, -11] = true := by decide +kernel
theorem subd12_3_298 : subd12_3 [1, -1, -10] = true := by decide +kernel
theorem subd12_3_299 : subd12_3 [1, -1, -9] = true := by decide +kernel
theorem subd12_3_300 : subd12_3 [1, -1, -8] = true := by decide +kernel
theorem subd12_3_301 : subd12_3 [1, -1, -7] = true := by decide +kernel
theorem subd12_3_302 : subd12_3 [1, -1, -6] = true := by decide +kernel
theorem subd12_3_303 : subd12_3 [1, -1, -5] = true := by decide +kernel
theorem subd12_3_304 : subd12_3 [1, -1, -4] = true := by decide +kernel
theorem subd12_3_305 : subd12_3 [1, -1, -3] = true := by decide +kernel
theorem subd12_3_306 : subd12_3 [1, -1, -2] = true := by decide +kernel
theorem subd12_3_307 : subd12_3 [1, -1, -1] = true := by decide +kernel
theorem subd12_3_308 : subd12_3 [1, -1, 0] = true := by decide +kernel
theorem subd12_3_309 : subd12_3 [1, -1, 1] = true := by decide +kernel
theorem subd12_3_310 : subd12_3 [1, -1, 2] = true := by decide +kernel
theorem subd12_3_311 : subd12_3 [1, -1, 3] = true := by decide +kernel
theorem subd12_3_312 : subd12_3 [1, -1, 4] = true := by decide +kernel
theorem subd12_3_313 : subd12_3 [1, -1, 5] = true := by decide +kernel
theorem subd12_3_314 : subd12_3 [1, -1, 6] = true := by decide +kernel
theorem subd12_3_315 : subd12_3 [1, -1, 7] = true := by decide +kernel
theorem subd12_3_316 : subd12_3 [1, -1, 8] = true := by decide +kernel
theorem subd12_3_317 : subd12_3 [1, -1, 9] = true := by decide +kernel
theorem subd12_3_318 : subd12_3 [1, -1, 10] = true := by decide +kernel
theorem subd12_3_319 : subd12_3 [1, 0, -12] = true := by decide +kernel
theorem sbd12_3_9 : ∀ q ∈ blkd12_3_9, subd12_3 q = true := by
  unfold blkd12_3_9
  exact List.forall_mem_cons.2 ⟨subd12_3_288, List.forall_mem_cons.2 ⟨subd12_3_289, List.forall_mem_cons.2 ⟨subd12_3_290, List.forall_mem_cons.2 ⟨subd12_3_291, List.forall_mem_cons.2 ⟨subd12_3_292, List.forall_mem_cons.2 ⟨subd12_3_293, List.forall_mem_cons.2 ⟨subd12_3_294, List.forall_mem_cons.2 ⟨subd12_3_295, List.forall_mem_cons.2 ⟨subd12_3_296, List.forall_mem_cons.2 ⟨subd12_3_297, List.forall_mem_cons.2 ⟨subd12_3_298, List.forall_mem_cons.2 ⟨subd12_3_299, List.forall_mem_cons.2 ⟨subd12_3_300, List.forall_mem_cons.2 ⟨subd12_3_301, List.forall_mem_cons.2 ⟨subd12_3_302, List.forall_mem_cons.2 ⟨subd12_3_303, List.forall_mem_cons.2 ⟨subd12_3_304, List.forall_mem_cons.2 ⟨subd12_3_305, List.forall_mem_cons.2 ⟨subd12_3_306, List.forall_mem_cons.2 ⟨subd12_3_307, List.forall_mem_cons.2 ⟨subd12_3_308, List.forall_mem_cons.2 ⟨subd12_3_309, List.forall_mem_cons.2 ⟨subd12_3_310, List.forall_mem_cons.2 ⟨subd12_3_311, List.forall_mem_cons.2 ⟨subd12_3_312, List.forall_mem_cons.2 ⟨subd12_3_313, List.forall_mem_cons.2 ⟨subd12_3_314, List.forall_mem_cons.2 ⟨subd12_3_315, List.forall_mem_cons.2 ⟨subd12_3_316, List.forall_mem_cons.2 ⟨subd12_3_317, List.forall_mem_cons.2 ⟨subd12_3_318, List.forall_mem_cons.2 ⟨subd12_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_320 : subd12_3 [1, 0, -11] = true := by decide +kernel
theorem subd12_3_321 : subd12_3 [1, 0, -10] = true := by decide +kernel
theorem subd12_3_322 : subd12_3 [1, 0, -9] = true := by decide +kernel
theorem subd12_3_323 : subd12_3 [1, 0, -8] = true := by decide +kernel
theorem subd12_3_324 : subd12_3 [1, 0, -7] = true := by decide +kernel
theorem subd12_3_325 : subd12_3 [1, 0, -6] = true := by decide +kernel
theorem subd12_3_326 : subd12_3 [1, 0, -5] = true := by decide +kernel
theorem subd12_3_327 : subd12_3 [1, 0, -4] = true := by decide +kernel
theorem subd12_3_328 : subd12_3 [1, 0, -3] = true := by decide +kernel
theorem subd12_3_329 : subd12_3 [1, 0, -2] = true := by decide +kernel
theorem subd12_3_330 : subd12_3 [1, 0, -1] = true := by decide +kernel
theorem subd12_3_331 : subd12_3 [1, 0, 0] = true := by decide +kernel
theorem subd12_3_332 : subd12_3 [1, 0, 1] = true := by decide +kernel
theorem subd12_3_333 : subd12_3 [1, 0, 2] = true := by decide +kernel
theorem subd12_3_334 : subd12_3 [1, 0, 3] = true := by decide +kernel
theorem subd12_3_335 : subd12_3 [1, 0, 4] = true := by decide +kernel
theorem subd12_3_336 : subd12_3 [1, 0, 5] = true := by decide +kernel
theorem subd12_3_337 : subd12_3 [1, 0, 6] = true := by decide +kernel
theorem subd12_3_338 : subd12_3 [1, 0, 7] = true := by decide +kernel
theorem subd12_3_339 : subd12_3 [1, 0, 8] = true := by decide +kernel
theorem subd12_3_340 : subd12_3 [1, 0, 9] = true := by decide +kernel
theorem subd12_3_341 : subd12_3 [1, 0, 10] = true := by decide +kernel
theorem subd12_3_342 : subd12_3 [1, 0, 11] = true := by decide +kernel
theorem subd12_3_343 : subd12_3 [1, 1, -11] = true := by decide +kernel
theorem subd12_3_344 : subd12_3 [1, 1, -10] = true := by decide +kernel
theorem subd12_3_345 : subd12_3 [1, 1, -9] = true := by decide +kernel
theorem subd12_3_346 : subd12_3 [1, 1, -8] = true := by decide +kernel
theorem subd12_3_347 : subd12_3 [1, 1, -7] = true := by decide +kernel
theorem subd12_3_348 : subd12_3 [1, 1, -6] = true := by decide +kernel
theorem subd12_3_349 : subd12_3 [1, 1, -5] = true := by decide +kernel
theorem subd12_3_350 : subd12_3 [1, 1, -4] = true := by decide +kernel
theorem subd12_3_351 : subd12_3 [1, 1, -3] = true := by decide +kernel
theorem sbd12_3_10 : ∀ q ∈ blkd12_3_10, subd12_3 q = true := by
  unfold blkd12_3_10
  exact List.forall_mem_cons.2 ⟨subd12_3_320, List.forall_mem_cons.2 ⟨subd12_3_321, List.forall_mem_cons.2 ⟨subd12_3_322, List.forall_mem_cons.2 ⟨subd12_3_323, List.forall_mem_cons.2 ⟨subd12_3_324, List.forall_mem_cons.2 ⟨subd12_3_325, List.forall_mem_cons.2 ⟨subd12_3_326, List.forall_mem_cons.2 ⟨subd12_3_327, List.forall_mem_cons.2 ⟨subd12_3_328, List.forall_mem_cons.2 ⟨subd12_3_329, List.forall_mem_cons.2 ⟨subd12_3_330, List.forall_mem_cons.2 ⟨subd12_3_331, List.forall_mem_cons.2 ⟨subd12_3_332, List.forall_mem_cons.2 ⟨subd12_3_333, List.forall_mem_cons.2 ⟨subd12_3_334, List.forall_mem_cons.2 ⟨subd12_3_335, List.forall_mem_cons.2 ⟨subd12_3_336, List.forall_mem_cons.2 ⟨subd12_3_337, List.forall_mem_cons.2 ⟨subd12_3_338, List.forall_mem_cons.2 ⟨subd12_3_339, List.forall_mem_cons.2 ⟨subd12_3_340, List.forall_mem_cons.2 ⟨subd12_3_341, List.forall_mem_cons.2 ⟨subd12_3_342, List.forall_mem_cons.2 ⟨subd12_3_343, List.forall_mem_cons.2 ⟨subd12_3_344, List.forall_mem_cons.2 ⟨subd12_3_345, List.forall_mem_cons.2 ⟨subd12_3_346, List.forall_mem_cons.2 ⟨subd12_3_347, List.forall_mem_cons.2 ⟨subd12_3_348, List.forall_mem_cons.2 ⟨subd12_3_349, List.forall_mem_cons.2 ⟨subd12_3_350, List.forall_mem_cons.2 ⟨subd12_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_352 : subd12_3 [1, 1, -2] = true := by decide +kernel
theorem subd12_3_353 : subd12_3 [1, 1, -1] = true := by decide +kernel
theorem subd12_3_354 : subd12_3 [1, 1, 0] = true := by decide +kernel
theorem subd12_3_355 : subd12_3 [1, 1, 1] = true := by decide +kernel
theorem subd12_3_356 : subd12_3 [1, 1, 2] = true := by decide +kernel
theorem subd12_3_357 : subd12_3 [1, 1, 3] = true := by decide +kernel
theorem subd12_3_358 : subd12_3 [1, 1, 4] = true := by decide +kernel
theorem subd12_3_359 : subd12_3 [1, 1, 5] = true := by decide +kernel
theorem subd12_3_360 : subd12_3 [1, 1, 6] = true := by decide +kernel
theorem subd12_3_361 : subd12_3 [1, 1, 7] = true := by decide +kernel
theorem subd12_3_362 : subd12_3 [1, 1, 8] = true := by decide +kernel
theorem subd12_3_363 : subd12_3 [1, 1, 9] = true := by decide +kernel
theorem subd12_3_364 : subd12_3 [1, 1, 10] = true := by decide +kernel
theorem subd12_3_365 : subd12_3 [1, 2, -9] = true := by decide +kernel
theorem subd12_3_366 : subd12_3 [1, 2, -8] = true := by decide +kernel
theorem subd12_3_367 : subd12_3 [1, 2, -7] = true := by decide +kernel
theorem subd12_3_368 : subd12_3 [1, 2, -6] = true := by decide +kernel
theorem subd12_3_369 : subd12_3 [1, 2, -5] = true := by decide +kernel
theorem subd12_3_370 : subd12_3 [1, 2, -4] = true := by decide +kernel
theorem subd12_3_371 : subd12_3 [1, 2, -3] = true := by decide +kernel
theorem subd12_3_372 : subd12_3 [1, 2, -2] = true := by decide +kernel
theorem subd12_3_373 : subd12_3 [1, 2, -1] = true := by decide +kernel
theorem subd12_3_374 : subd12_3 [1, 2, 0] = true := by decide +kernel
theorem subd12_3_375 : subd12_3 [1, 2, 1] = true := by decide +kernel
theorem subd12_3_376 : subd12_3 [1, 2, 2] = true := by decide +kernel
theorem subd12_3_377 : subd12_3 [1, 2, 3] = true := by decide +kernel
theorem subd12_3_378 : subd12_3 [1, 2, 4] = true := by decide +kernel
theorem subd12_3_379 : subd12_3 [1, 2, 5] = true := by decide +kernel
theorem subd12_3_380 : subd12_3 [1, 2, 6] = true := by decide +kernel
theorem subd12_3_381 : subd12_3 [1, 2, 7] = true := by decide +kernel
theorem subd12_3_382 : subd12_3 [2, -3] = true := by decide +kernel
theorem subd12_3_383 : subd12_3 [2, -2] = true := by decide +kernel
theorem sbd12_3_11 : ∀ q ∈ blkd12_3_11, subd12_3 q = true := by
  unfold blkd12_3_11
  exact List.forall_mem_cons.2 ⟨subd12_3_352, List.forall_mem_cons.2 ⟨subd12_3_353, List.forall_mem_cons.2 ⟨subd12_3_354, List.forall_mem_cons.2 ⟨subd12_3_355, List.forall_mem_cons.2 ⟨subd12_3_356, List.forall_mem_cons.2 ⟨subd12_3_357, List.forall_mem_cons.2 ⟨subd12_3_358, List.forall_mem_cons.2 ⟨subd12_3_359, List.forall_mem_cons.2 ⟨subd12_3_360, List.forall_mem_cons.2 ⟨subd12_3_361, List.forall_mem_cons.2 ⟨subd12_3_362, List.forall_mem_cons.2 ⟨subd12_3_363, List.forall_mem_cons.2 ⟨subd12_3_364, List.forall_mem_cons.2 ⟨subd12_3_365, List.forall_mem_cons.2 ⟨subd12_3_366, List.forall_mem_cons.2 ⟨subd12_3_367, List.forall_mem_cons.2 ⟨subd12_3_368, List.forall_mem_cons.2 ⟨subd12_3_369, List.forall_mem_cons.2 ⟨subd12_3_370, List.forall_mem_cons.2 ⟨subd12_3_371, List.forall_mem_cons.2 ⟨subd12_3_372, List.forall_mem_cons.2 ⟨subd12_3_373, List.forall_mem_cons.2 ⟨subd12_3_374, List.forall_mem_cons.2 ⟨subd12_3_375, List.forall_mem_cons.2 ⟨subd12_3_376, List.forall_mem_cons.2 ⟨subd12_3_377, List.forall_mem_cons.2 ⟨subd12_3_378, List.forall_mem_cons.2 ⟨subd12_3_379, List.forall_mem_cons.2 ⟨subd12_3_380, List.forall_mem_cons.2 ⟨subd12_3_381, List.forall_mem_cons.2 ⟨subd12_3_382, List.forall_mem_cons.2 ⟨subd12_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_384 : subd12_3 [2, -1, -9] = true := by decide +kernel
theorem subd12_3_385 : subd12_3 [2, -1, -8] = true := by decide +kernel
theorem subd12_3_386 : subd12_3 [2, -1, -7] = true := by decide +kernel
theorem subd12_3_387 : subd12_3 [2, -1, -6] = true := by decide +kernel
theorem subd12_3_388 : subd12_3 [2, -1, -5] = true := by decide +kernel
theorem subd12_3_389 : subd12_3 [2, -1, -4] = true := by decide +kernel
theorem subd12_3_390 : subd12_3 [2, -1, -3] = true := by decide +kernel
theorem subd12_3_391 : subd12_3 [2, -1, -2] = true := by decide +kernel
theorem subd12_3_392 : subd12_3 [2, -1, -1] = true := by decide +kernel
theorem subd12_3_393 : subd12_3 [2, -1, 0] = true := by decide +kernel
theorem subd12_3_394 : subd12_3 [2, -1, 1] = true := by decide +kernel
theorem subd12_3_395 : subd12_3 [2, -1, 2] = true := by decide +kernel
theorem subd12_3_396 : subd12_3 [2, -1, 3] = true := by decide +kernel
theorem subd12_3_397 : subd12_3 [2, -1, 4] = true := by decide +kernel
theorem subd12_3_398 : subd12_3 [2, -1, 5] = true := by decide +kernel
theorem subd12_3_399 : subd12_3 [2, -1, 6] = true := by decide +kernel
theorem subd12_3_400 : subd12_3 [2, -1, 7] = true := by decide +kernel
theorem subd12_3_401 : subd12_3 [2, -1, 8] = true := by decide +kernel
theorem subd12_3_402 : subd12_3 [2, 0, -10] = true := by decide +kernel
theorem subd12_3_403 : subd12_3 [2, 0, -9] = true := by decide +kernel
theorem subd12_3_404 : subd12_3 [2, 0, -8] = true := by decide +kernel
theorem subd12_3_405 : subd12_3 [2, 0, -7] = true := by decide +kernel
theorem subd12_3_406 : subd12_3 [2, 0, -6] = true := by decide +kernel
theorem subd12_3_407 : subd12_3 [2, 0, -5] = true := by decide +kernel
theorem subd12_3_408 : subd12_3 [2, 0, -4] = true := by decide +kernel
theorem subd12_3_409 : subd12_3 [2, 0, -3] = true := by decide +kernel
theorem subd12_3_410 : subd12_3 [2, 0, -2] = true := by decide +kernel
theorem subd12_3_411 : subd12_3 [2, 0, -1] = true := by decide +kernel
theorem subd12_3_412 : subd12_3 [2, 0, 0] = true := by decide +kernel
theorem subd12_3_413 : subd12_3 [2, 0, 1] = true := by decide +kernel
theorem subd12_3_414 : subd12_3 [2, 0, 2] = true := by decide +kernel
theorem subd12_3_415 : subd12_3 [2, 0, 3] = true := by decide +kernel
theorem sbd12_3_12 : ∀ q ∈ blkd12_3_12, subd12_3 q = true := by
  unfold blkd12_3_12
  exact List.forall_mem_cons.2 ⟨subd12_3_384, List.forall_mem_cons.2 ⟨subd12_3_385, List.forall_mem_cons.2 ⟨subd12_3_386, List.forall_mem_cons.2 ⟨subd12_3_387, List.forall_mem_cons.2 ⟨subd12_3_388, List.forall_mem_cons.2 ⟨subd12_3_389, List.forall_mem_cons.2 ⟨subd12_3_390, List.forall_mem_cons.2 ⟨subd12_3_391, List.forall_mem_cons.2 ⟨subd12_3_392, List.forall_mem_cons.2 ⟨subd12_3_393, List.forall_mem_cons.2 ⟨subd12_3_394, List.forall_mem_cons.2 ⟨subd12_3_395, List.forall_mem_cons.2 ⟨subd12_3_396, List.forall_mem_cons.2 ⟨subd12_3_397, List.forall_mem_cons.2 ⟨subd12_3_398, List.forall_mem_cons.2 ⟨subd12_3_399, List.forall_mem_cons.2 ⟨subd12_3_400, List.forall_mem_cons.2 ⟨subd12_3_401, List.forall_mem_cons.2 ⟨subd12_3_402, List.forall_mem_cons.2 ⟨subd12_3_403, List.forall_mem_cons.2 ⟨subd12_3_404, List.forall_mem_cons.2 ⟨subd12_3_405, List.forall_mem_cons.2 ⟨subd12_3_406, List.forall_mem_cons.2 ⟨subd12_3_407, List.forall_mem_cons.2 ⟨subd12_3_408, List.forall_mem_cons.2 ⟨subd12_3_409, List.forall_mem_cons.2 ⟨subd12_3_410, List.forall_mem_cons.2 ⟨subd12_3_411, List.forall_mem_cons.2 ⟨subd12_3_412, List.forall_mem_cons.2 ⟨subd12_3_413, List.forall_mem_cons.2 ⟨subd12_3_414, List.forall_mem_cons.2 ⟨subd12_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_416 : subd12_3 [2, 0, 4] = true := by decide +kernel
theorem subd12_3_417 : subd12_3 [2, 0, 5] = true := by decide +kernel
theorem subd12_3_418 : subd12_3 [2, 0, 6] = true := by decide +kernel
theorem subd12_3_419 : subd12_3 [2, 0, 7] = true := by decide +kernel
theorem subd12_3_420 : subd12_3 [2, 0, 8] = true := by decide +kernel
theorem subd12_3_421 : subd12_3 [2, 0, 9] = true := by decide +kernel
theorem subd12_3_422 : subd12_3 [2, 1, -9] = true := by decide +kernel
theorem subd12_3_423 : subd12_3 [2, 1, -8] = true := by decide +kernel
theorem subd12_3_424 : subd12_3 [2, 1, -7] = true := by decide +kernel
theorem subd12_3_425 : subd12_3 [2, 1, -6] = true := by decide +kernel
theorem subd12_3_426 : subd12_3 [2, 1, -5] = true := by decide +kernel
theorem subd12_3_427 : subd12_3 [2, 1, -4] = true := by decide +kernel
theorem subd12_3_428 : subd12_3 [2, 1, -3] = true := by decide +kernel
theorem subd12_3_429 : subd12_3 [2, 1, -2] = true := by decide +kernel
theorem subd12_3_430 : subd12_3 [2, 1, -1] = true := by decide +kernel
theorem subd12_3_431 : subd12_3 [2, 1, 0] = true := by decide +kernel
theorem subd12_3_432 : subd12_3 [2, 1, 1] = true := by decide +kernel
theorem subd12_3_433 : subd12_3 [2, 1, 2] = true := by decide +kernel
theorem subd12_3_434 : subd12_3 [2, 1, 3] = true := by decide +kernel
theorem subd12_3_435 : subd12_3 [2, 1, 4] = true := by decide +kernel
theorem subd12_3_436 : subd12_3 [2, 1, 5] = true := by decide +kernel
theorem subd12_3_437 : subd12_3 [2, 1, 6] = true := by decide +kernel
theorem subd12_3_438 : subd12_3 [2, 1, 7] = true := by decide +kernel
theorem subd12_3_439 : subd12_3 [2, 2] = true := by decide +kernel
theorem subd12_3_440 : subd12_3 [3] = true := by decide +kernel
theorem sbd12_3_13 : ∀ q ∈ blkd12_3_13, subd12_3 q = true := by
  unfold blkd12_3_13
  exact List.forall_mem_cons.2 ⟨subd12_3_416, List.forall_mem_cons.2 ⟨subd12_3_417, List.forall_mem_cons.2 ⟨subd12_3_418, List.forall_mem_cons.2 ⟨subd12_3_419, List.forall_mem_cons.2 ⟨subd12_3_420, List.forall_mem_cons.2 ⟨subd12_3_421, List.forall_mem_cons.2 ⟨subd12_3_422, List.forall_mem_cons.2 ⟨subd12_3_423, List.forall_mem_cons.2 ⟨subd12_3_424, List.forall_mem_cons.2 ⟨subd12_3_425, List.forall_mem_cons.2 ⟨subd12_3_426, List.forall_mem_cons.2 ⟨subd12_3_427, List.forall_mem_cons.2 ⟨subd12_3_428, List.forall_mem_cons.2 ⟨subd12_3_429, List.forall_mem_cons.2 ⟨subd12_3_430, List.forall_mem_cons.2 ⟨subd12_3_431, List.forall_mem_cons.2 ⟨subd12_3_432, List.forall_mem_cons.2 ⟨subd12_3_433, List.forall_mem_cons.2 ⟨subd12_3_434, List.forall_mem_cons.2 ⟨subd12_3_435, List.forall_mem_cons.2 ⟨subd12_3_436, List.forall_mem_cons.2 ⟨subd12_3_437, List.forall_mem_cons.2 ⟨subd12_3_438, List.forall_mem_cons.2 ⟨subd12_3_439, List.forall_mem_cons.2 ⟨subd12_3_440, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [-6] = true := by decide +kernel
theorem subd13_0_1 : subd13_0 [-5, -2] = true := by decide +kernel
theorem subd13_0_2 : subd13_0 [-5, -1] = true := by decide +kernel
theorem subd13_0_3 : subd13_0 [-5, 0] = true := by decide +kernel
theorem subd13_0_4 : subd13_0 [-5, 1] = true := by decide +kernel
theorem subd13_0_5 : subd13_0 [-5, 2] = true := by decide +kernel
theorem subd13_0_6 : subd13_0 [-5, 3] = true := by decide +kernel
theorem subd13_0_7 : subd13_0 [-5, 4] = true := by decide +kernel
theorem subd13_0_8 : subd13_0 [-5, 5] = true := by decide +kernel
theorem subd13_0_9 : subd13_0 [-4, -4] = true := by decide +kernel
theorem subd13_0_10 : subd13_0 [-4, -3] = true := by decide +kernel
theorem subd13_0_11 : subd13_0 [-4, -2] = true := by decide +kernel
theorem subd13_0_12 : subd13_0 [-4, -1] = true := by decide +kernel
theorem subd13_0_13 : subd13_0 [-4, 0] = true := by decide +kernel
theorem subd13_0_14 : subd13_0 [-4, 1] = true := by decide +kernel
theorem subd13_0_15 : subd13_0 [-4, 2] = true := by decide +kernel
theorem subd13_0_16 : subd13_0 [-4, 3] = true := by decide +kernel
theorem subd13_0_17 : subd13_0 [-4, 4] = true := by decide +kernel
theorem subd13_0_18 : subd13_0 [-4, 5] = true := by decide +kernel
theorem subd13_0_19 : subd13_0 [-3, -5] = true := by decide +kernel
theorem subd13_0_20 : subd13_0 [-3, -4] = true := by decide +kernel
theorem subd13_0_21 : subd13_0 [-3, -3] = true := by decide +kernel
theorem subd13_0_22 : subd13_0 [-3, -2] = true := by decide +kernel
theorem subd13_0_23 : subd13_0 [-3, -1] = true := by decide +kernel
theorem subd13_0_24 : subd13_0 [-3, 0] = true := by decide +kernel
theorem subd13_0_25 : subd13_0 [-3, 1] = true := by decide +kernel
theorem subd13_0_26 : subd13_0 [-3, 2] = true := by decide +kernel
theorem subd13_0_27 : subd13_0 [-3, 3] = true := by decide +kernel
theorem subd13_0_28 : subd13_0 [-3, 4] = true := by decide +kernel
theorem subd13_0_29 : subd13_0 [-3, 5] = true := by decide +kernel
theorem subd13_0_30 : subd13_0 [-3, 6] = true := by decide +kernel
theorem subd13_0_31 : subd13_0 [-2, -5] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_cons.2 ⟨subd13_0_1, List.forall_mem_cons.2 ⟨subd13_0_2, List.forall_mem_cons.2 ⟨subd13_0_3, List.forall_mem_cons.2 ⟨subd13_0_4, List.forall_mem_cons.2 ⟨subd13_0_5, List.forall_mem_cons.2 ⟨subd13_0_6, List.forall_mem_cons.2 ⟨subd13_0_7, List.forall_mem_cons.2 ⟨subd13_0_8, List.forall_mem_cons.2 ⟨subd13_0_9, List.forall_mem_cons.2 ⟨subd13_0_10, List.forall_mem_cons.2 ⟨subd13_0_11, List.forall_mem_cons.2 ⟨subd13_0_12, List.forall_mem_cons.2 ⟨subd13_0_13, List.forall_mem_cons.2 ⟨subd13_0_14, List.forall_mem_cons.2 ⟨subd13_0_15, List.forall_mem_cons.2 ⟨subd13_0_16, List.forall_mem_cons.2 ⟨subd13_0_17, List.forall_mem_cons.2 ⟨subd13_0_18, List.forall_mem_cons.2 ⟨subd13_0_19, List.forall_mem_cons.2 ⟨subd13_0_20, List.forall_mem_cons.2 ⟨subd13_0_21, List.forall_mem_cons.2 ⟨subd13_0_22, List.forall_mem_cons.2 ⟨subd13_0_23, List.forall_mem_cons.2 ⟨subd13_0_24, List.forall_mem_cons.2 ⟨subd13_0_25, List.forall_mem_cons.2 ⟨subd13_0_26, List.forall_mem_cons.2 ⟨subd13_0_27, List.forall_mem_cons.2 ⟨subd13_0_28, List.forall_mem_cons.2 ⟨subd13_0_29, List.forall_mem_cons.2 ⟨subd13_0_30, List.forall_mem_cons.2 ⟨subd13_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
