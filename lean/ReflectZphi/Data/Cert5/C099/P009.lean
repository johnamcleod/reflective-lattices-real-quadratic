import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_6_96 : subd5_6 [-2, 1, 6] = true := by decide +kernel
theorem subd5_6_97 : subd5_6 [-2, 1, 7] = true := by decide +kernel
theorem subd5_6_98 : subd5_6 [-2, 2] = true := by decide +kernel
theorem subd5_6_99 : subd5_6 [-2, 3] = true := by decide +kernel
theorem subd5_6_100 : subd5_6 [-2, 4] = true := by decide +kernel
theorem subd5_6_101 : subd5_6 [-2, 5] = true := by decide +kernel
theorem subd5_6_102 : subd5_6 [-1, -7] = true := by decide +kernel
theorem subd5_6_103 : subd5_6 [-1, -6] = true := by decide +kernel
theorem subd5_6_104 : subd5_6 [-1, -5] = true := by decide +kernel
theorem subd5_6_105 : subd5_6 [-1, -4] = true := by decide +kernel
theorem subd5_6_106 : subd5_6 [-1, -3, -7] = true := by decide +kernel
theorem subd5_6_107 : subd5_6 [-1, -3, -6] = true := by decide +kernel
theorem subd5_6_108 : subd5_6 [-1, -3, -5] = true := by decide +kernel
theorem subd5_6_109 : subd5_6 [-1, -3, -4] = true := by decide +kernel
theorem subd5_6_110 : subd5_6 [-1, -3, -3] = true := by decide +kernel
theorem subd5_6_111 : subd5_6 [-1, -3, -2] = true := by decide +kernel
theorem subd5_6_112 : subd5_6 [-1, -3, -1] = true := by decide +kernel
theorem subd5_6_113 : subd5_6 [-1, -3, 0] = true := by decide +kernel
theorem subd5_6_114 : subd5_6 [-1, -3, 1] = true := by decide +kernel
theorem subd5_6_115 : subd5_6 [-1, -3, 2] = true := by decide +kernel
theorem subd5_6_116 : subd5_6 [-1, -3, 3] = true := by decide +kernel
theorem subd5_6_117 : subd5_6 [-1, -3, 4] = true := by decide +kernel
theorem subd5_6_118 : subd5_6 [-1, -3, 5] = true := by decide +kernel
theorem subd5_6_119 : subd5_6 [-1, -3, 6] = true := by decide +kernel
theorem subd5_6_120 : subd5_6 [-1, -3, 7] = true := by decide +kernel
theorem subd5_6_121 : subd5_6 [-1, -2, -7] = true := by decide +kernel
theorem subd5_6_122 : subd5_6 [-1, -2, -6] = true := by decide +kernel
theorem subd5_6_123 : subd5_6 [-1, -2, -5] = true := by decide +kernel
theorem subd5_6_124 : subd5_6 [-1, -2, -4] = true := by decide +kernel
theorem subd5_6_125 : subd5_6 [-1, -2, -3] = true := by decide +kernel
theorem subd5_6_126 : subd5_6 [-1, -2, -2] = true := by decide +kernel
theorem subd5_6_127 : subd5_6 [-1, -2, -1] = true := by decide +kernel
theorem sbd5_6_3 : ∀ q ∈ blkd5_6_3, subd5_6 q = true := by
  unfold blkd5_6_3
  exact List.forall_mem_cons.2 ⟨subd5_6_96, List.forall_mem_cons.2 ⟨subd5_6_97, List.forall_mem_cons.2 ⟨subd5_6_98, List.forall_mem_cons.2 ⟨subd5_6_99, List.forall_mem_cons.2 ⟨subd5_6_100, List.forall_mem_cons.2 ⟨subd5_6_101, List.forall_mem_cons.2 ⟨subd5_6_102, List.forall_mem_cons.2 ⟨subd5_6_103, List.forall_mem_cons.2 ⟨subd5_6_104, List.forall_mem_cons.2 ⟨subd5_6_105, List.forall_mem_cons.2 ⟨subd5_6_106, List.forall_mem_cons.2 ⟨subd5_6_107, List.forall_mem_cons.2 ⟨subd5_6_108, List.forall_mem_cons.2 ⟨subd5_6_109, List.forall_mem_cons.2 ⟨subd5_6_110, List.forall_mem_cons.2 ⟨subd5_6_111, List.forall_mem_cons.2 ⟨subd5_6_112, List.forall_mem_cons.2 ⟨subd5_6_113, List.forall_mem_cons.2 ⟨subd5_6_114, List.forall_mem_cons.2 ⟨subd5_6_115, List.forall_mem_cons.2 ⟨subd5_6_116, List.forall_mem_cons.2 ⟨subd5_6_117, List.forall_mem_cons.2 ⟨subd5_6_118, List.forall_mem_cons.2 ⟨subd5_6_119, List.forall_mem_cons.2 ⟨subd5_6_120, List.forall_mem_cons.2 ⟨subd5_6_121, List.forall_mem_cons.2 ⟨subd5_6_122, List.forall_mem_cons.2 ⟨subd5_6_123, List.forall_mem_cons.2 ⟨subd5_6_124, List.forall_mem_cons.2 ⟨subd5_6_125, List.forall_mem_cons.2 ⟨subd5_6_126, List.forall_mem_cons.2 ⟨subd5_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_128 : subd5_6 [-1, -2, 0] = true := by decide +kernel
theorem subd5_6_129 : subd5_6 [-1, -2, 1] = true := by decide +kernel
theorem subd5_6_130 : subd5_6 [-1, -2, 2] = true := by decide +kernel
theorem subd5_6_131 : subd5_6 [-1, -2, 3] = true := by decide +kernel
theorem subd5_6_132 : subd5_6 [-1, -2, 4] = true := by decide +kernel
theorem subd5_6_133 : subd5_6 [-1, -2, 5] = true := by decide +kernel
theorem subd5_6_134 : subd5_6 [-1, -2, 6] = true := by decide +kernel
theorem subd5_6_135 : subd5_6 [-1, -2, 7] = true := by decide +kernel
theorem subd5_6_136 : subd5_6 [-1, -1, -8] = true := by decide +kernel
theorem subd5_6_137 : subd5_6 [-1, -1, -7] = true := by decide +kernel
theorem subd5_6_138 : subd5_6 [-1, -1, -6] = true := by decide +kernel
theorem subd5_6_139 : subd5_6 [-1, -1, -5] = true := by decide +kernel
theorem subd5_6_140 : subd5_6 [-1, -1, -4] = true := by decide +kernel
theorem subd5_6_141 : subd5_6 [-1, -1, -3] = true := by decide +kernel
theorem subd5_6_142 : subd5_6 [-1, -1, -2] = true := by decide +kernel
theorem subd5_6_143 : subd5_6 [-1, -1, -1] = true := by decide +kernel
theorem subd5_6_144 : subd5_6 [-1, -1, 0] = true := by decide +kernel
theorem subd5_6_145 : subd5_6 [-1, -1, 1] = true := by decide +kernel
theorem subd5_6_146 : subd5_6 [-1, -1, 2] = true := by decide +kernel
theorem subd5_6_147 : subd5_6 [-1, -1, 3] = true := by decide +kernel
theorem subd5_6_148 : subd5_6 [-1, -1, 4] = true := by decide +kernel
theorem subd5_6_149 : subd5_6 [-1, -1, 5] = true := by decide +kernel
theorem subd5_6_150 : subd5_6 [-1, -1, 6] = true := by decide +kernel
theorem subd5_6_151 : subd5_6 [-1, -1, 7] = true := by decide +kernel
theorem subd5_6_152 : subd5_6 [-1, 0, -8] = true := by decide +kernel
theorem subd5_6_153 : subd5_6 [-1, 0, -7] = true := by decide +kernel
theorem subd5_6_154 : subd5_6 [-1, 0, -6] = true := by decide +kernel
theorem subd5_6_155 : subd5_6 [-1, 0, -5] = true := by decide +kernel
theorem subd5_6_156 : subd5_6 [-1, 0, -4] = true := by decide +kernel
theorem subd5_6_157 : subd5_6 [-1, 0, -3] = true := by decide +kernel
theorem subd5_6_158 : subd5_6 [-1, 0, -2] = true := by decide +kernel
theorem subd5_6_159 : subd5_6 [-1, 0, -1] = true := by decide +kernel
theorem sbd5_6_4 : ∀ q ∈ blkd5_6_4, subd5_6 q = true := by
  unfold blkd5_6_4
  exact List.forall_mem_cons.2 ⟨subd5_6_128, List.forall_mem_cons.2 ⟨subd5_6_129, List.forall_mem_cons.2 ⟨subd5_6_130, List.forall_mem_cons.2 ⟨subd5_6_131, List.forall_mem_cons.2 ⟨subd5_6_132, List.forall_mem_cons.2 ⟨subd5_6_133, List.forall_mem_cons.2 ⟨subd5_6_134, List.forall_mem_cons.2 ⟨subd5_6_135, List.forall_mem_cons.2 ⟨subd5_6_136, List.forall_mem_cons.2 ⟨subd5_6_137, List.forall_mem_cons.2 ⟨subd5_6_138, List.forall_mem_cons.2 ⟨subd5_6_139, List.forall_mem_cons.2 ⟨subd5_6_140, List.forall_mem_cons.2 ⟨subd5_6_141, List.forall_mem_cons.2 ⟨subd5_6_142, List.forall_mem_cons.2 ⟨subd5_6_143, List.forall_mem_cons.2 ⟨subd5_6_144, List.forall_mem_cons.2 ⟨subd5_6_145, List.forall_mem_cons.2 ⟨subd5_6_146, List.forall_mem_cons.2 ⟨subd5_6_147, List.forall_mem_cons.2 ⟨subd5_6_148, List.forall_mem_cons.2 ⟨subd5_6_149, List.forall_mem_cons.2 ⟨subd5_6_150, List.forall_mem_cons.2 ⟨subd5_6_151, List.forall_mem_cons.2 ⟨subd5_6_152, List.forall_mem_cons.2 ⟨subd5_6_153, List.forall_mem_cons.2 ⟨subd5_6_154, List.forall_mem_cons.2 ⟨subd5_6_155, List.forall_mem_cons.2 ⟨subd5_6_156, List.forall_mem_cons.2 ⟨subd5_6_157, List.forall_mem_cons.2 ⟨subd5_6_158, List.forall_mem_cons.2 ⟨subd5_6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_160 : subd5_6 [-1, 0, 0] = true := by decide +kernel
theorem subd5_6_161 : subd5_6 [-1, 0, 1] = true := by decide +kernel
theorem subd5_6_162 : subd5_6 [-1, 0, 2] = true := by decide +kernel
theorem subd5_6_163 : subd5_6 [-1, 0, 3] = true := by decide +kernel
theorem subd5_6_164 : subd5_6 [-1, 0, 4] = true := by decide +kernel
theorem subd5_6_165 : subd5_6 [-1, 0, 5] = true := by decide +kernel
theorem subd5_6_166 : subd5_6 [-1, 0, 6] = true := by decide +kernel
theorem subd5_6_167 : subd5_6 [-1, 0, 7] = true := by decide +kernel
theorem subd5_6_168 : subd5_6 [-1, 1, -8] = true := by decide +kernel
theorem subd5_6_169 : subd5_6 [-1, 1, -7] = true := by decide +kernel
theorem subd5_6_170 : subd5_6 [-1, 1, -6] = true := by decide +kernel
theorem subd5_6_171 : subd5_6 [-1, 1, -5] = true := by decide +kernel
theorem subd5_6_172 : subd5_6 [-1, 1, -4] = true := by decide +kernel
theorem subd5_6_173 : subd5_6 [-1, 1, -3] = true := by decide +kernel
theorem subd5_6_174 : subd5_6 [-1, 1, -2] = true := by decide +kernel
theorem subd5_6_175 : subd5_6 [-1, 1, -1] = true := by decide +kernel
theorem subd5_6_176 : subd5_6 [-1, 1, 0] = true := by decide +kernel
theorem subd5_6_177 : subd5_6 [-1, 1, 1] = true := by decide +kernel
theorem subd5_6_178 : subd5_6 [-1, 1, 2] = true := by decide +kernel
theorem subd5_6_179 : subd5_6 [-1, 1, 3] = true := by decide +kernel
theorem subd5_6_180 : subd5_6 [-1, 1, 4] = true := by decide +kernel
theorem subd5_6_181 : subd5_6 [-1, 1, 5] = true := by decide +kernel
theorem subd5_6_182 : subd5_6 [-1, 1, 6] = true := by decide +kernel
theorem subd5_6_183 : subd5_6 [-1, 1, 7] = true := by decide +kernel
theorem subd5_6_184 : subd5_6 [-1, 2, -8] = true := by decide +kernel
theorem subd5_6_185 : subd5_6 [-1, 2, -7] = true := by decide +kernel
theorem subd5_6_186 : subd5_6 [-1, 2, -6] = true := by decide +kernel
theorem subd5_6_187 : subd5_6 [-1, 2, -5] = true := by decide +kernel
theorem subd5_6_188 : subd5_6 [-1, 2, -4] = true := by decide +kernel
theorem subd5_6_189 : subd5_6 [-1, 2, -3] = true := by decide +kernel
theorem subd5_6_190 : subd5_6 [-1, 2, -2] = true := by decide +kernel
theorem subd5_6_191 : subd5_6 [-1, 2, -1] = true := by decide +kernel
theorem sbd5_6_5 : ∀ q ∈ blkd5_6_5, subd5_6 q = true := by
  unfold blkd5_6_5
  exact List.forall_mem_cons.2 ⟨subd5_6_160, List.forall_mem_cons.2 ⟨subd5_6_161, List.forall_mem_cons.2 ⟨subd5_6_162, List.forall_mem_cons.2 ⟨subd5_6_163, List.forall_mem_cons.2 ⟨subd5_6_164, List.forall_mem_cons.2 ⟨subd5_6_165, List.forall_mem_cons.2 ⟨subd5_6_166, List.forall_mem_cons.2 ⟨subd5_6_167, List.forall_mem_cons.2 ⟨subd5_6_168, List.forall_mem_cons.2 ⟨subd5_6_169, List.forall_mem_cons.2 ⟨subd5_6_170, List.forall_mem_cons.2 ⟨subd5_6_171, List.forall_mem_cons.2 ⟨subd5_6_172, List.forall_mem_cons.2 ⟨subd5_6_173, List.forall_mem_cons.2 ⟨subd5_6_174, List.forall_mem_cons.2 ⟨subd5_6_175, List.forall_mem_cons.2 ⟨subd5_6_176, List.forall_mem_cons.2 ⟨subd5_6_177, List.forall_mem_cons.2 ⟨subd5_6_178, List.forall_mem_cons.2 ⟨subd5_6_179, List.forall_mem_cons.2 ⟨subd5_6_180, List.forall_mem_cons.2 ⟨subd5_6_181, List.forall_mem_cons.2 ⟨subd5_6_182, List.forall_mem_cons.2 ⟨subd5_6_183, List.forall_mem_cons.2 ⟨subd5_6_184, List.forall_mem_cons.2 ⟨subd5_6_185, List.forall_mem_cons.2 ⟨subd5_6_186, List.forall_mem_cons.2 ⟨subd5_6_187, List.forall_mem_cons.2 ⟨subd5_6_188, List.forall_mem_cons.2 ⟨subd5_6_189, List.forall_mem_cons.2 ⟨subd5_6_190, List.forall_mem_cons.2 ⟨subd5_6_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_192 : subd5_6 [-1, 2, 0] = true := by decide +kernel
theorem subd5_6_193 : subd5_6 [-1, 2, 1] = true := by decide +kernel
theorem subd5_6_194 : subd5_6 [-1, 2, 2] = true := by decide +kernel
theorem subd5_6_195 : subd5_6 [-1, 2, 3] = true := by decide +kernel
theorem subd5_6_196 : subd5_6 [-1, 2, 4] = true := by decide +kernel
theorem subd5_6_197 : subd5_6 [-1, 2, 5] = true := by decide +kernel
theorem subd5_6_198 : subd5_6 [-1, 2, 6] = true := by decide +kernel
theorem subd5_6_199 : subd5_6 [-1, 2, 7] = true := by decide +kernel
theorem subd5_6_200 : subd5_6 [-1, 3] = true := by decide +kernel
theorem subd5_6_201 : subd5_6 [-1, 4] = true := by decide +kernel
theorem subd5_6_202 : subd5_6 [-1, 5] = true := by decide +kernel
theorem subd5_6_203 : subd5_6 [-1, 6] = true := by decide +kernel
theorem subd5_6_204 : subd5_6 [0, -7] = true := by decide +kernel
theorem subd5_6_205 : subd5_6 [0, -6] = true := by decide +kernel
theorem subd5_6_206 : subd5_6 [0, -5] = true := by decide +kernel
theorem subd5_6_207 : subd5_6 [0, -4] = true := by decide +kernel
theorem subd5_6_208 : subd5_6 [0, -3, -7] = true := by decide +kernel
theorem subd5_6_209 : subd5_6 [0, -3, -6] = true := by decide +kernel
theorem subd5_6_210 : subd5_6 [0, -3, -5] = true := by decide +kernel
theorem subd5_6_211 : subd5_6 [0, -3, -4] = true := by decide +kernel
theorem subd5_6_212 : subd5_6 [0, -3, -3] = true := by decide +kernel
theorem subd5_6_213 : subd5_6 [0, -3, -2] = true := by decide +kernel
theorem subd5_6_214 : subd5_6 [0, -3, -1] = true := by decide +kernel
theorem subd5_6_215 : subd5_6 [0, -3, 0] = true := by decide +kernel
theorem subd5_6_216 : subd5_6 [0, -3, 1] = true := by decide +kernel
theorem subd5_6_217 : subd5_6 [0, -3, 2] = true := by decide +kernel
theorem subd5_6_218 : subd5_6 [0, -3, 3] = true := by decide +kernel
theorem subd5_6_219 : subd5_6 [0, -3, 4] = true := by decide +kernel
theorem subd5_6_220 : subd5_6 [0, -3, 5] = true := by decide +kernel
theorem subd5_6_221 : subd5_6 [0, -3, 6] = true := by decide +kernel
theorem subd5_6_222 : subd5_6 [0, -3, 7] = true := by decide +kernel
theorem subd5_6_223 : subd5_6 [0, -2, -8] = true := by decide +kernel
theorem sbd5_6_6 : ∀ q ∈ blkd5_6_6, subd5_6 q = true := by
  unfold blkd5_6_6
  exact List.forall_mem_cons.2 ⟨subd5_6_192, List.forall_mem_cons.2 ⟨subd5_6_193, List.forall_mem_cons.2 ⟨subd5_6_194, List.forall_mem_cons.2 ⟨subd5_6_195, List.forall_mem_cons.2 ⟨subd5_6_196, List.forall_mem_cons.2 ⟨subd5_6_197, List.forall_mem_cons.2 ⟨subd5_6_198, List.forall_mem_cons.2 ⟨subd5_6_199, List.forall_mem_cons.2 ⟨subd5_6_200, List.forall_mem_cons.2 ⟨subd5_6_201, List.forall_mem_cons.2 ⟨subd5_6_202, List.forall_mem_cons.2 ⟨subd5_6_203, List.forall_mem_cons.2 ⟨subd5_6_204, List.forall_mem_cons.2 ⟨subd5_6_205, List.forall_mem_cons.2 ⟨subd5_6_206, List.forall_mem_cons.2 ⟨subd5_6_207, List.forall_mem_cons.2 ⟨subd5_6_208, List.forall_mem_cons.2 ⟨subd5_6_209, List.forall_mem_cons.2 ⟨subd5_6_210, List.forall_mem_cons.2 ⟨subd5_6_211, List.forall_mem_cons.2 ⟨subd5_6_212, List.forall_mem_cons.2 ⟨subd5_6_213, List.forall_mem_cons.2 ⟨subd5_6_214, List.forall_mem_cons.2 ⟨subd5_6_215, List.forall_mem_cons.2 ⟨subd5_6_216, List.forall_mem_cons.2 ⟨subd5_6_217, List.forall_mem_cons.2 ⟨subd5_6_218, List.forall_mem_cons.2 ⟨subd5_6_219, List.forall_mem_cons.2 ⟨subd5_6_220, List.forall_mem_cons.2 ⟨subd5_6_221, List.forall_mem_cons.2 ⟨subd5_6_222, List.forall_mem_cons.2 ⟨subd5_6_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_224 : subd5_6 [0, -2, -7] = true := by decide +kernel
theorem subd5_6_225 : subd5_6 [0, -2, -6] = true := by decide +kernel
theorem subd5_6_226 : subd5_6 [0, -2, -5] = true := by decide +kernel
theorem subd5_6_227 : subd5_6 [0, -2, -4] = true := by decide +kernel
theorem subd5_6_228 : subd5_6 [0, -2, -3] = true := by decide +kernel
theorem subd5_6_229 : subd5_6 [0, -2, -2] = true := by decide +kernel
theorem subd5_6_230 : subd5_6 [0, -2, -1] = true := by decide +kernel
theorem subd5_6_231 : subd5_6 [0, -2, 0] = true := by decide +kernel
theorem subd5_6_232 : subd5_6 [0, -2, 1] = true := by decide +kernel
theorem subd5_6_233 : subd5_6 [0, -2, 2] = true := by decide +kernel
theorem subd5_6_234 : subd5_6 [0, -2, 3] = true := by decide +kernel
theorem subd5_6_235 : subd5_6 [0, -2, 4] = true := by decide +kernel
theorem subd5_6_236 : subd5_6 [0, -2, 5] = true := by decide +kernel
theorem subd5_6_237 : subd5_6 [0, -2, 6] = true := by decide +kernel
theorem subd5_6_238 : subd5_6 [0, -2, 7] = true := by decide +kernel
theorem subd5_6_239 : subd5_6 [0, -1, -8] = true := by decide +kernel
theorem subd5_6_240 : subd5_6 [0, -1, -7] = true := by decide +kernel
theorem subd5_6_241 : subd5_6 [0, -1, -6] = true := by decide +kernel
theorem subd5_6_242 : subd5_6 [0, -1, -5] = true := by decide +kernel
theorem subd5_6_243 : subd5_6 [0, -1, -4] = true := by decide +kernel
theorem subd5_6_244 : subd5_6 [0, -1, -3] = true := by decide +kernel
theorem subd5_6_245 : subd5_6 [0, -1, -2] = true := by decide +kernel
theorem subd5_6_246 : subd5_6 [0, -1, -1] = true := by decide +kernel
theorem subd5_6_247 : subd5_6 [0, -1, 0] = true := by decide +kernel
theorem subd5_6_248 : subd5_6 [0, -1, 1] = true := by decide +kernel
theorem subd5_6_249 : subd5_6 [0, -1, 2] = true := by decide +kernel
theorem subd5_6_250 : subd5_6 [0, -1, 3] = true := by decide +kernel
theorem subd5_6_251 : subd5_6 [0, -1, 4] = true := by decide +kernel
theorem subd5_6_252 : subd5_6 [0, -1, 5] = true := by decide +kernel
theorem subd5_6_253 : subd5_6 [0, -1, 6] = true := by decide +kernel
theorem subd5_6_254 : subd5_6 [0, -1, 7] = true := by decide +kernel
theorem subd5_6_255 : subd5_6 [0, 0, -8] = true := by decide +kernel
theorem sbd5_6_7 : ∀ q ∈ blkd5_6_7, subd5_6 q = true := by
  unfold blkd5_6_7
  exact List.forall_mem_cons.2 ⟨subd5_6_224, List.forall_mem_cons.2 ⟨subd5_6_225, List.forall_mem_cons.2 ⟨subd5_6_226, List.forall_mem_cons.2 ⟨subd5_6_227, List.forall_mem_cons.2 ⟨subd5_6_228, List.forall_mem_cons.2 ⟨subd5_6_229, List.forall_mem_cons.2 ⟨subd5_6_230, List.forall_mem_cons.2 ⟨subd5_6_231, List.forall_mem_cons.2 ⟨subd5_6_232, List.forall_mem_cons.2 ⟨subd5_6_233, List.forall_mem_cons.2 ⟨subd5_6_234, List.forall_mem_cons.2 ⟨subd5_6_235, List.forall_mem_cons.2 ⟨subd5_6_236, List.forall_mem_cons.2 ⟨subd5_6_237, List.forall_mem_cons.2 ⟨subd5_6_238, List.forall_mem_cons.2 ⟨subd5_6_239, List.forall_mem_cons.2 ⟨subd5_6_240, List.forall_mem_cons.2 ⟨subd5_6_241, List.forall_mem_cons.2 ⟨subd5_6_242, List.forall_mem_cons.2 ⟨subd5_6_243, List.forall_mem_cons.2 ⟨subd5_6_244, List.forall_mem_cons.2 ⟨subd5_6_245, List.forall_mem_cons.2 ⟨subd5_6_246, List.forall_mem_cons.2 ⟨subd5_6_247, List.forall_mem_cons.2 ⟨subd5_6_248, List.forall_mem_cons.2 ⟨subd5_6_249, List.forall_mem_cons.2 ⟨subd5_6_250, List.forall_mem_cons.2 ⟨subd5_6_251, List.forall_mem_cons.2 ⟨subd5_6_252, List.forall_mem_cons.2 ⟨subd5_6_253, List.forall_mem_cons.2 ⟨subd5_6_254, List.forall_mem_cons.2 ⟨subd5_6_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_256 : subd5_6 [0, 0, -7] = true := by decide +kernel
theorem subd5_6_257 : subd5_6 [0, 0, -6] = true := by decide +kernel
theorem subd5_6_258 : subd5_6 [0, 0, -5] = true := by decide +kernel
theorem subd5_6_259 : subd5_6 [0, 0, -4] = true := by decide +kernel
theorem subd5_6_260 : subd5_6 [0, 0, -3] = true := by decide +kernel
theorem subd5_6_261 : subd5_6 [0, 0, -2] = true := by decide +kernel
theorem subd5_6_262 : subd5_6 [0, 0, -1] = true := by decide +kernel
theorem subd5_6_263 : subd5_6 [0, 0, 0] = true := by decide +kernel
theorem subd5_6_264 : subd5_6 [0, 0, 1] = true := by decide +kernel
theorem subd5_6_265 : subd5_6 [0, 0, 2] = true := by decide +kernel
theorem subd5_6_266 : subd5_6 [0, 0, 3] = true := by decide +kernel
theorem subd5_6_267 : subd5_6 [0, 0, 4] = true := by decide +kernel
theorem subd5_6_268 : subd5_6 [0, 0, 5] = true := by decide +kernel
theorem subd5_6_269 : subd5_6 [0, 0, 6] = true := by decide +kernel
theorem subd5_6_270 : subd5_6 [0, 0, 7] = true := by decide +kernel
theorem subd5_6_271 : subd5_6 [0, 1, -8] = true := by decide +kernel
theorem subd5_6_272 : subd5_6 [0, 1, -7] = true := by decide +kernel
theorem subd5_6_273 : subd5_6 [0, 1, -6] = true := by decide +kernel
theorem subd5_6_274 : subd5_6 [0, 1, -5] = true := by decide +kernel
theorem subd5_6_275 : subd5_6 [0, 1, -4] = true := by decide +kernel
theorem subd5_6_276 : subd5_6 [0, 1, -3] = true := by decide +kernel
theorem subd5_6_277 : subd5_6 [0, 1, -2] = true := by decide +kernel
theorem subd5_6_278 : subd5_6 [0, 1, -1] = true := by decide +kernel
theorem subd5_6_279 : subd5_6 [0, 1, 0] = true := by decide +kernel
theorem subd5_6_280 : subd5_6 [0, 1, 1] = true := by decide +kernel
theorem subd5_6_281 : subd5_6 [0, 1, 2] = true := by decide +kernel
theorem subd5_6_282 : subd5_6 [0, 1, 3] = true := by decide +kernel
theorem subd5_6_283 : subd5_6 [0, 1, 4] = true := by decide +kernel
theorem subd5_6_284 : subd5_6 [0, 1, 5] = true := by decide +kernel
theorem subd5_6_285 : subd5_6 [0, 1, 6] = true := by decide +kernel
theorem subd5_6_286 : subd5_6 [0, 1, 7] = true := by decide +kernel
theorem subd5_6_287 : subd5_6 [0, 2, -8] = true := by decide +kernel
theorem sbd5_6_8 : ∀ q ∈ blkd5_6_8, subd5_6 q = true := by
  unfold blkd5_6_8
  exact List.forall_mem_cons.2 ⟨subd5_6_256, List.forall_mem_cons.2 ⟨subd5_6_257, List.forall_mem_cons.2 ⟨subd5_6_258, List.forall_mem_cons.2 ⟨subd5_6_259, List.forall_mem_cons.2 ⟨subd5_6_260, List.forall_mem_cons.2 ⟨subd5_6_261, List.forall_mem_cons.2 ⟨subd5_6_262, List.forall_mem_cons.2 ⟨subd5_6_263, List.forall_mem_cons.2 ⟨subd5_6_264, List.forall_mem_cons.2 ⟨subd5_6_265, List.forall_mem_cons.2 ⟨subd5_6_266, List.forall_mem_cons.2 ⟨subd5_6_267, List.forall_mem_cons.2 ⟨subd5_6_268, List.forall_mem_cons.2 ⟨subd5_6_269, List.forall_mem_cons.2 ⟨subd5_6_270, List.forall_mem_cons.2 ⟨subd5_6_271, List.forall_mem_cons.2 ⟨subd5_6_272, List.forall_mem_cons.2 ⟨subd5_6_273, List.forall_mem_cons.2 ⟨subd5_6_274, List.forall_mem_cons.2 ⟨subd5_6_275, List.forall_mem_cons.2 ⟨subd5_6_276, List.forall_mem_cons.2 ⟨subd5_6_277, List.forall_mem_cons.2 ⟨subd5_6_278, List.forall_mem_cons.2 ⟨subd5_6_279, List.forall_mem_cons.2 ⟨subd5_6_280, List.forall_mem_cons.2 ⟨subd5_6_281, List.forall_mem_cons.2 ⟨subd5_6_282, List.forall_mem_cons.2 ⟨subd5_6_283, List.forall_mem_cons.2 ⟨subd5_6_284, List.forall_mem_cons.2 ⟨subd5_6_285, List.forall_mem_cons.2 ⟨subd5_6_286, List.forall_mem_cons.2 ⟨subd5_6_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_288 : subd5_6 [0, 2, -7] = true := by decide +kernel
theorem subd5_6_289 : subd5_6 [0, 2, -6] = true := by decide +kernel
theorem subd5_6_290 : subd5_6 [0, 2, -5] = true := by decide +kernel
theorem subd5_6_291 : subd5_6 [0, 2, -4] = true := by decide +kernel
theorem subd5_6_292 : subd5_6 [0, 2, -3] = true := by decide +kernel
theorem subd5_6_293 : subd5_6 [0, 2, -2] = true := by decide +kernel
theorem subd5_6_294 : subd5_6 [0, 2, -1] = true := by decide +kernel
theorem subd5_6_295 : subd5_6 [0, 2, 0] = true := by decide +kernel
theorem subd5_6_296 : subd5_6 [0, 2, 1] = true := by decide +kernel
theorem subd5_6_297 : subd5_6 [0, 2, 2] = true := by decide +kernel
theorem subd5_6_298 : subd5_6 [0, 2, 3] = true := by decide +kernel
theorem subd5_6_299 : subd5_6 [0, 2, 4] = true := by decide +kernel
theorem subd5_6_300 : subd5_6 [0, 2, 5] = true := by decide +kernel
theorem subd5_6_301 : subd5_6 [0, 2, 6] = true := by decide +kernel
theorem subd5_6_302 : subd5_6 [0, 2, 7] = true := by decide +kernel
theorem subd5_6_303 : subd5_6 [0, 3, -8] = true := by decide +kernel
theorem subd5_6_304 : subd5_6 [0, 3, -7] = true := by decide +kernel
theorem subd5_6_305 : subd5_6 [0, 3, -6] = true := by decide +kernel
theorem subd5_6_306 : subd5_6 [0, 3, -5] = true := by decide +kernel
theorem subd5_6_307 : subd5_6 [0, 3, -4] = true := by decide +kernel
theorem subd5_6_308 : subd5_6 [0, 3, -3] = true := by decide +kernel
theorem subd5_6_309 : subd5_6 [0, 3, -2] = true := by decide +kernel
theorem subd5_6_310 : subd5_6 [0, 3, -1] = true := by decide +kernel
theorem subd5_6_311 : subd5_6 [0, 3, 0] = true := by decide +kernel
theorem subd5_6_312 : subd5_6 [0, 3, 1] = true := by decide +kernel
theorem subd5_6_313 : subd5_6 [0, 3, 2] = true := by decide +kernel
theorem subd5_6_314 : subd5_6 [0, 3, 3] = true := by decide +kernel
theorem subd5_6_315 : subd5_6 [0, 3, 4] = true := by decide +kernel
theorem subd5_6_316 : subd5_6 [0, 3, 5] = true := by decide +kernel
theorem subd5_6_317 : subd5_6 [0, 3, 6] = true := by decide +kernel
theorem subd5_6_318 : subd5_6 [0, 4] = true := by decide +kernel
theorem subd5_6_319 : subd5_6 [0, 5] = true := by decide +kernel
theorem sbd5_6_9 : ∀ q ∈ blkd5_6_9, subd5_6 q = true := by
  unfold blkd5_6_9
  exact List.forall_mem_cons.2 ⟨subd5_6_288, List.forall_mem_cons.2 ⟨subd5_6_289, List.forall_mem_cons.2 ⟨subd5_6_290, List.forall_mem_cons.2 ⟨subd5_6_291, List.forall_mem_cons.2 ⟨subd5_6_292, List.forall_mem_cons.2 ⟨subd5_6_293, List.forall_mem_cons.2 ⟨subd5_6_294, List.forall_mem_cons.2 ⟨subd5_6_295, List.forall_mem_cons.2 ⟨subd5_6_296, List.forall_mem_cons.2 ⟨subd5_6_297, List.forall_mem_cons.2 ⟨subd5_6_298, List.forall_mem_cons.2 ⟨subd5_6_299, List.forall_mem_cons.2 ⟨subd5_6_300, List.forall_mem_cons.2 ⟨subd5_6_301, List.forall_mem_cons.2 ⟨subd5_6_302, List.forall_mem_cons.2 ⟨subd5_6_303, List.forall_mem_cons.2 ⟨subd5_6_304, List.forall_mem_cons.2 ⟨subd5_6_305, List.forall_mem_cons.2 ⟨subd5_6_306, List.forall_mem_cons.2 ⟨subd5_6_307, List.forall_mem_cons.2 ⟨subd5_6_308, List.forall_mem_cons.2 ⟨subd5_6_309, List.forall_mem_cons.2 ⟨subd5_6_310, List.forall_mem_cons.2 ⟨subd5_6_311, List.forall_mem_cons.2 ⟨subd5_6_312, List.forall_mem_cons.2 ⟨subd5_6_313, List.forall_mem_cons.2 ⟨subd5_6_314, List.forall_mem_cons.2 ⟨subd5_6_315, List.forall_mem_cons.2 ⟨subd5_6_316, List.forall_mem_cons.2 ⟨subd5_6_317, List.forall_mem_cons.2 ⟨subd5_6_318, List.forall_mem_cons.2 ⟨subd5_6_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_320 : subd5_6 [0, 6] = true := by decide +kernel
theorem subd5_6_321 : subd5_6 [1, -7] = true := by decide +kernel
theorem subd5_6_322 : subd5_6 [1, -6] = true := by decide +kernel
theorem subd5_6_323 : subd5_6 [1, -5] = true := by decide +kernel
theorem subd5_6_324 : subd5_6 [1, -4] = true := by decide +kernel
theorem subd5_6_325 : subd5_6 [1, -3] = true := by decide +kernel
theorem subd5_6_326 : subd5_6 [1, -2, -8] = true := by decide +kernel
theorem subd5_6_327 : subd5_6 [1, -2, -7] = true := by decide +kernel
theorem subd5_6_328 : subd5_6 [1, -2, -6] = true := by decide +kernel
theorem subd5_6_329 : subd5_6 [1, -2, -5] = true := by decide +kernel
theorem subd5_6_330 : subd5_6 [1, -2, -4] = true := by decide +kernel
theorem subd5_6_331 : subd5_6 [1, -2, -3] = true := by decide +kernel
theorem subd5_6_332 : subd5_6 [1, -2, -2] = true := by decide +kernel
theorem subd5_6_333 : subd5_6 [1, -2, -1] = true := by decide +kernel
theorem subd5_6_334 : subd5_6 [1, -2, 0] = true := by decide +kernel
theorem subd5_6_335 : subd5_6 [1, -2, 1] = true := by decide +kernel
theorem subd5_6_336 : subd5_6 [1, -2, 2] = true := by decide +kernel
theorem subd5_6_337 : subd5_6 [1, -2, 3] = true := by decide +kernel
theorem subd5_6_338 : subd5_6 [1, -2, 4] = true := by decide +kernel
theorem subd5_6_339 : subd5_6 [1, -2, 5] = true := by decide +kernel
theorem subd5_6_340 : subd5_6 [1, -2, 6] = true := by decide +kernel
theorem subd5_6_341 : subd5_6 [1, -2, 7] = true := by decide +kernel
theorem subd5_6_342 : subd5_6 [1, -1, -8] = true := by decide +kernel
theorem subd5_6_343 : subd5_6 [1, -1, -7] = true := by decide +kernel
theorem subd5_6_344 : subd5_6 [1, -1, -6] = true := by decide +kernel
theorem subd5_6_345 : subd5_6 [1, -1, -5] = true := by decide +kernel
theorem subd5_6_346 : subd5_6 [1, -1, -4] = true := by decide +kernel
theorem subd5_6_347 : subd5_6 [1, -1, -3] = true := by decide +kernel
theorem subd5_6_348 : subd5_6 [1, -1, -2] = true := by decide +kernel
theorem subd5_6_349 : subd5_6 [1, -1, -1] = true := by decide +kernel
theorem subd5_6_350 : subd5_6 [1, -1, 0] = true := by decide +kernel
theorem subd5_6_351 : subd5_6 [1, -1, 1] = true := by decide +kernel
theorem sbd5_6_10 : ∀ q ∈ blkd5_6_10, subd5_6 q = true := by
  unfold blkd5_6_10
  exact List.forall_mem_cons.2 ⟨subd5_6_320, List.forall_mem_cons.2 ⟨subd5_6_321, List.forall_mem_cons.2 ⟨subd5_6_322, List.forall_mem_cons.2 ⟨subd5_6_323, List.forall_mem_cons.2 ⟨subd5_6_324, List.forall_mem_cons.2 ⟨subd5_6_325, List.forall_mem_cons.2 ⟨subd5_6_326, List.forall_mem_cons.2 ⟨subd5_6_327, List.forall_mem_cons.2 ⟨subd5_6_328, List.forall_mem_cons.2 ⟨subd5_6_329, List.forall_mem_cons.2 ⟨subd5_6_330, List.forall_mem_cons.2 ⟨subd5_6_331, List.forall_mem_cons.2 ⟨subd5_6_332, List.forall_mem_cons.2 ⟨subd5_6_333, List.forall_mem_cons.2 ⟨subd5_6_334, List.forall_mem_cons.2 ⟨subd5_6_335, List.forall_mem_cons.2 ⟨subd5_6_336, List.forall_mem_cons.2 ⟨subd5_6_337, List.forall_mem_cons.2 ⟨subd5_6_338, List.forall_mem_cons.2 ⟨subd5_6_339, List.forall_mem_cons.2 ⟨subd5_6_340, List.forall_mem_cons.2 ⟨subd5_6_341, List.forall_mem_cons.2 ⟨subd5_6_342, List.forall_mem_cons.2 ⟨subd5_6_343, List.forall_mem_cons.2 ⟨subd5_6_344, List.forall_mem_cons.2 ⟨subd5_6_345, List.forall_mem_cons.2 ⟨subd5_6_346, List.forall_mem_cons.2 ⟨subd5_6_347, List.forall_mem_cons.2 ⟨subd5_6_348, List.forall_mem_cons.2 ⟨subd5_6_349, List.forall_mem_cons.2 ⟨subd5_6_350, List.forall_mem_cons.2 ⟨subd5_6_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_352 : subd5_6 [1, -1, 2] = true := by decide +kernel
theorem subd5_6_353 : subd5_6 [1, -1, 3] = true := by decide +kernel
theorem subd5_6_354 : subd5_6 [1, -1, 4] = true := by decide +kernel
theorem subd5_6_355 : subd5_6 [1, -1, 5] = true := by decide +kernel
theorem subd5_6_356 : subd5_6 [1, -1, 6] = true := by decide +kernel
theorem subd5_6_357 : subd5_6 [1, -1, 7] = true := by decide +kernel
theorem subd5_6_358 : subd5_6 [1, 0, -8] = true := by decide +kernel
theorem subd5_6_359 : subd5_6 [1, 0, -7] = true := by decide +kernel
theorem subd5_6_360 : subd5_6 [1, 0, -6] = true := by decide +kernel
theorem subd5_6_361 : subd5_6 [1, 0, -5] = true := by decide +kernel
theorem subd5_6_362 : subd5_6 [1, 0, -4] = true := by decide +kernel
theorem subd5_6_363 : subd5_6 [1, 0, -3] = true := by decide +kernel
theorem subd5_6_364 : subd5_6 [1, 0, -2] = true := by decide +kernel
theorem subd5_6_365 : subd5_6 [1, 0, -1] = true := by decide +kernel
theorem subd5_6_366 : subd5_6 [1, 0, 0] = true := by decide +kernel
theorem subd5_6_367 : subd5_6 [1, 0, 1] = true := by decide +kernel
theorem subd5_6_368 : subd5_6 [1, 0, 2] = true := by decide +kernel
theorem subd5_6_369 : subd5_6 [1, 0, 3] = true := by decide +kernel
theorem subd5_6_370 : subd5_6 [1, 0, 4] = true := by decide +kernel
theorem subd5_6_371 : subd5_6 [1, 0, 5] = true := by decide +kernel
theorem subd5_6_372 : subd5_6 [1, 0, 6] = true := by decide +kernel
theorem subd5_6_373 : subd5_6 [1, 0, 7] = true := by decide +kernel
theorem subd5_6_374 : subd5_6 [1, 1, -8] = true := by decide +kernel
theorem subd5_6_375 : subd5_6 [1, 1, -7] = true := by decide +kernel
theorem subd5_6_376 : subd5_6 [1, 1, -6] = true := by decide +kernel
theorem subd5_6_377 : subd5_6 [1, 1, -5] = true := by decide +kernel
theorem subd5_6_378 : subd5_6 [1, 1, -4] = true := by decide +kernel
theorem subd5_6_379 : subd5_6 [1, 1, -3] = true := by decide +kernel
theorem subd5_6_380 : subd5_6 [1, 1, -2] = true := by decide +kernel
theorem subd5_6_381 : subd5_6 [1, 1, -1] = true := by decide +kernel
theorem subd5_6_382 : subd5_6 [1, 1, 0] = true := by decide +kernel
theorem subd5_6_383 : subd5_6 [1, 1, 1] = true := by decide +kernel
theorem sbd5_6_11 : ∀ q ∈ blkd5_6_11, subd5_6 q = true := by
  unfold blkd5_6_11
  exact List.forall_mem_cons.2 ⟨subd5_6_352, List.forall_mem_cons.2 ⟨subd5_6_353, List.forall_mem_cons.2 ⟨subd5_6_354, List.forall_mem_cons.2 ⟨subd5_6_355, List.forall_mem_cons.2 ⟨subd5_6_356, List.forall_mem_cons.2 ⟨subd5_6_357, List.forall_mem_cons.2 ⟨subd5_6_358, List.forall_mem_cons.2 ⟨subd5_6_359, List.forall_mem_cons.2 ⟨subd5_6_360, List.forall_mem_cons.2 ⟨subd5_6_361, List.forall_mem_cons.2 ⟨subd5_6_362, List.forall_mem_cons.2 ⟨subd5_6_363, List.forall_mem_cons.2 ⟨subd5_6_364, List.forall_mem_cons.2 ⟨subd5_6_365, List.forall_mem_cons.2 ⟨subd5_6_366, List.forall_mem_cons.2 ⟨subd5_6_367, List.forall_mem_cons.2 ⟨subd5_6_368, List.forall_mem_cons.2 ⟨subd5_6_369, List.forall_mem_cons.2 ⟨subd5_6_370, List.forall_mem_cons.2 ⟨subd5_6_371, List.forall_mem_cons.2 ⟨subd5_6_372, List.forall_mem_cons.2 ⟨subd5_6_373, List.forall_mem_cons.2 ⟨subd5_6_374, List.forall_mem_cons.2 ⟨subd5_6_375, List.forall_mem_cons.2 ⟨subd5_6_376, List.forall_mem_cons.2 ⟨subd5_6_377, List.forall_mem_cons.2 ⟨subd5_6_378, List.forall_mem_cons.2 ⟨subd5_6_379, List.forall_mem_cons.2 ⟨subd5_6_380, List.forall_mem_cons.2 ⟨subd5_6_381, List.forall_mem_cons.2 ⟨subd5_6_382, List.forall_mem_cons.2 ⟨subd5_6_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_384 : subd5_6 [1, 1, 2] = true := by decide +kernel
theorem subd5_6_385 : subd5_6 [1, 1, 3] = true := by decide +kernel
theorem subd5_6_386 : subd5_6 [1, 1, 4] = true := by decide +kernel
theorem subd5_6_387 : subd5_6 [1, 1, 5] = true := by decide +kernel
theorem subd5_6_388 : subd5_6 [1, 1, 6] = true := by decide +kernel
theorem subd5_6_389 : subd5_6 [1, 1, 7] = true := by decide +kernel
theorem subd5_6_390 : subd5_6 [1, 2, -8] = true := by decide +kernel
theorem subd5_6_391 : subd5_6 [1, 2, -7] = true := by decide +kernel
theorem subd5_6_392 : subd5_6 [1, 2, -6] = true := by decide +kernel
theorem subd5_6_393 : subd5_6 [1, 2, -5] = true := by decide +kernel
theorem subd5_6_394 : subd5_6 [1, 2, -4] = true := by decide +kernel
theorem subd5_6_395 : subd5_6 [1, 2, -3] = true := by decide +kernel
theorem subd5_6_396 : subd5_6 [1, 2, -2] = true := by decide +kernel
theorem subd5_6_397 : subd5_6 [1, 2, -1] = true := by decide +kernel
theorem subd5_6_398 : subd5_6 [1, 2, 0] = true := by decide +kernel
theorem subd5_6_399 : subd5_6 [1, 2, 1] = true := by decide +kernel
theorem subd5_6_400 : subd5_6 [1, 2, 2] = true := by decide +kernel
theorem subd5_6_401 : subd5_6 [1, 2, 3] = true := by decide +kernel
theorem subd5_6_402 : subd5_6 [1, 2, 4] = true := by decide +kernel
theorem subd5_6_403 : subd5_6 [1, 2, 5] = true := by decide +kernel
theorem subd5_6_404 : subd5_6 [1, 2, 6] = true := by decide +kernel
theorem subd5_6_405 : subd5_6 [1, 3, -8] = true := by decide +kernel
theorem subd5_6_406 : subd5_6 [1, 3, -7] = true := by decide +kernel
theorem subd5_6_407 : subd5_6 [1, 3, -6] = true := by decide +kernel
theorem subd5_6_408 : subd5_6 [1, 3, -5] = true := by decide +kernel
theorem subd5_6_409 : subd5_6 [1, 3, -4] = true := by decide +kernel
theorem subd5_6_410 : subd5_6 [1, 3, -3] = true := by decide +kernel
theorem subd5_6_411 : subd5_6 [1, 3, -2] = true := by decide +kernel
theorem subd5_6_412 : subd5_6 [1, 3, -1] = true := by decide +kernel
theorem subd5_6_413 : subd5_6 [1, 3, 0] = true := by decide +kernel
theorem subd5_6_414 : subd5_6 [1, 3, 1] = true := by decide +kernel
theorem subd5_6_415 : subd5_6 [1, 3, 2] = true := by decide +kernel
theorem sbd5_6_12 : ∀ q ∈ blkd5_6_12, subd5_6 q = true := by
  unfold blkd5_6_12
  exact List.forall_mem_cons.2 ⟨subd5_6_384, List.forall_mem_cons.2 ⟨subd5_6_385, List.forall_mem_cons.2 ⟨subd5_6_386, List.forall_mem_cons.2 ⟨subd5_6_387, List.forall_mem_cons.2 ⟨subd5_6_388, List.forall_mem_cons.2 ⟨subd5_6_389, List.forall_mem_cons.2 ⟨subd5_6_390, List.forall_mem_cons.2 ⟨subd5_6_391, List.forall_mem_cons.2 ⟨subd5_6_392, List.forall_mem_cons.2 ⟨subd5_6_393, List.forall_mem_cons.2 ⟨subd5_6_394, List.forall_mem_cons.2 ⟨subd5_6_395, List.forall_mem_cons.2 ⟨subd5_6_396, List.forall_mem_cons.2 ⟨subd5_6_397, List.forall_mem_cons.2 ⟨subd5_6_398, List.forall_mem_cons.2 ⟨subd5_6_399, List.forall_mem_cons.2 ⟨subd5_6_400, List.forall_mem_cons.2 ⟨subd5_6_401, List.forall_mem_cons.2 ⟨subd5_6_402, List.forall_mem_cons.2 ⟨subd5_6_403, List.forall_mem_cons.2 ⟨subd5_6_404, List.forall_mem_cons.2 ⟨subd5_6_405, List.forall_mem_cons.2 ⟨subd5_6_406, List.forall_mem_cons.2 ⟨subd5_6_407, List.forall_mem_cons.2 ⟨subd5_6_408, List.forall_mem_cons.2 ⟨subd5_6_409, List.forall_mem_cons.2 ⟨subd5_6_410, List.forall_mem_cons.2 ⟨subd5_6_411, List.forall_mem_cons.2 ⟨subd5_6_412, List.forall_mem_cons.2 ⟨subd5_6_413, List.forall_mem_cons.2 ⟨subd5_6_414, List.forall_mem_cons.2 ⟨subd5_6_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_416 : subd5_6 [1, 3, 3] = true := by decide +kernel
theorem subd5_6_417 : subd5_6 [1, 3, 4] = true := by decide +kernel
theorem subd5_6_418 : subd5_6 [1, 3, 5] = true := by decide +kernel
theorem subd5_6_419 : subd5_6 [1, 3, 6] = true := by decide +kernel
theorem subd5_6_420 : subd5_6 [1, 4] = true := by decide +kernel
theorem subd5_6_421 : subd5_6 [1, 5] = true := by decide +kernel
theorem subd5_6_422 : subd5_6 [1, 6] = true := by decide +kernel
theorem subd5_6_423 : subd5_6 [2, -6] = true := by decide +kernel
theorem subd5_6_424 : subd5_6 [2, -5] = true := by decide +kernel
theorem subd5_6_425 : subd5_6 [2, -4] = true := by decide +kernel
theorem subd5_6_426 : subd5_6 [2, -3] = true := by decide +kernel
theorem subd5_6_427 : subd5_6 [2, -2] = true := by decide +kernel
theorem subd5_6_428 : subd5_6 [2, -1, -8] = true := by decide +kernel
theorem subd5_6_429 : subd5_6 [2, -1, -7] = true := by decide +kernel
theorem subd5_6_430 : subd5_6 [2, -1, -6] = true := by decide +kernel
theorem subd5_6_431 : subd5_6 [2, -1, -5] = true := by decide +kernel
theorem subd5_6_432 : subd5_6 [2, -1, -4] = true := by decide +kernel
theorem subd5_6_433 : subd5_6 [2, -1, -3] = true := by decide +kernel
theorem subd5_6_434 : subd5_6 [2, -1, -2] = true := by decide +kernel
theorem subd5_6_435 : subd5_6 [2, -1, -1] = true := by decide +kernel
theorem subd5_6_436 : subd5_6 [2, -1, 0] = true := by decide +kernel
theorem subd5_6_437 : subd5_6 [2, -1, 1] = true := by decide +kernel
theorem subd5_6_438 : subd5_6 [2, -1, 2] = true := by decide +kernel
theorem subd5_6_439 : subd5_6 [2, -1, 3] = true := by decide +kernel
theorem subd5_6_440 : subd5_6 [2, -1, 4] = true := by decide +kernel
theorem subd5_6_441 : subd5_6 [2, -1, 5] = true := by decide +kernel
theorem subd5_6_442 : subd5_6 [2, -1, 6] = true := by decide +kernel
theorem subd5_6_443 : subd5_6 [2, 0, -8] = true := by decide +kernel
theorem subd5_6_444 : subd5_6 [2, 0, -7] = true := by decide +kernel
theorem subd5_6_445 : subd5_6 [2, 0, -6] = true := by decide +kernel
theorem subd5_6_446 : subd5_6 [2, 0, -5] = true := by decide +kernel
theorem subd5_6_447 : subd5_6 [2, 0, -4] = true := by decide +kernel
theorem sbd5_6_13 : ∀ q ∈ blkd5_6_13, subd5_6 q = true := by
  unfold blkd5_6_13
  exact List.forall_mem_cons.2 ⟨subd5_6_416, List.forall_mem_cons.2 ⟨subd5_6_417, List.forall_mem_cons.2 ⟨subd5_6_418, List.forall_mem_cons.2 ⟨subd5_6_419, List.forall_mem_cons.2 ⟨subd5_6_420, List.forall_mem_cons.2 ⟨subd5_6_421, List.forall_mem_cons.2 ⟨subd5_6_422, List.forall_mem_cons.2 ⟨subd5_6_423, List.forall_mem_cons.2 ⟨subd5_6_424, List.forall_mem_cons.2 ⟨subd5_6_425, List.forall_mem_cons.2 ⟨subd5_6_426, List.forall_mem_cons.2 ⟨subd5_6_427, List.forall_mem_cons.2 ⟨subd5_6_428, List.forall_mem_cons.2 ⟨subd5_6_429, List.forall_mem_cons.2 ⟨subd5_6_430, List.forall_mem_cons.2 ⟨subd5_6_431, List.forall_mem_cons.2 ⟨subd5_6_432, List.forall_mem_cons.2 ⟨subd5_6_433, List.forall_mem_cons.2 ⟨subd5_6_434, List.forall_mem_cons.2 ⟨subd5_6_435, List.forall_mem_cons.2 ⟨subd5_6_436, List.forall_mem_cons.2 ⟨subd5_6_437, List.forall_mem_cons.2 ⟨subd5_6_438, List.forall_mem_cons.2 ⟨subd5_6_439, List.forall_mem_cons.2 ⟨subd5_6_440, List.forall_mem_cons.2 ⟨subd5_6_441, List.forall_mem_cons.2 ⟨subd5_6_442, List.forall_mem_cons.2 ⟨subd5_6_443, List.forall_mem_cons.2 ⟨subd5_6_444, List.forall_mem_cons.2 ⟨subd5_6_445, List.forall_mem_cons.2 ⟨subd5_6_446, List.forall_mem_cons.2 ⟨subd5_6_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_448 : subd5_6 [2, 0, -3] = true := by decide +kernel
theorem subd5_6_449 : subd5_6 [2, 0, -2] = true := by decide +kernel
theorem subd5_6_450 : subd5_6 [2, 0, -1] = true := by decide +kernel
theorem subd5_6_451 : subd5_6 [2, 0, 0] = true := by decide +kernel
theorem subd5_6_452 : subd5_6 [2, 0, 1] = true := by decide +kernel
theorem subd5_6_453 : subd5_6 [2, 0, 2] = true := by decide +kernel
theorem subd5_6_454 : subd5_6 [2, 0, 3] = true := by decide +kernel
theorem subd5_6_455 : subd5_6 [2, 0, 4] = true := by decide +kernel
theorem subd5_6_456 : subd5_6 [2, 0, 5] = true := by decide +kernel
theorem subd5_6_457 : subd5_6 [2, 0, 6] = true := by decide +kernel
theorem subd5_6_458 : subd5_6 [2, 1, -8] = true := by decide +kernel
theorem subd5_6_459 : subd5_6 [2, 1, -7] = true := by decide +kernel
theorem subd5_6_460 : subd5_6 [2, 1, -6] = true := by decide +kernel
theorem subd5_6_461 : subd5_6 [2, 1, -5] = true := by decide +kernel
theorem subd5_6_462 : subd5_6 [2, 1, -4] = true := by decide +kernel
theorem subd5_6_463 : subd5_6 [2, 1, -3] = true := by decide +kernel
theorem subd5_6_464 : subd5_6 [2, 1, -2] = true := by decide +kernel
theorem subd5_6_465 : subd5_6 [2, 1, -1] = true := by decide +kernel
theorem subd5_6_466 : subd5_6 [2, 1, 0] = true := by decide +kernel
theorem subd5_6_467 : subd5_6 [2, 1, 1] = true := by decide +kernel
theorem subd5_6_468 : subd5_6 [2, 1, 2] = true := by decide +kernel
theorem subd5_6_469 : subd5_6 [2, 1, 3] = true := by decide +kernel
theorem subd5_6_470 : subd5_6 [2, 1, 4] = true := by decide +kernel
theorem subd5_6_471 : subd5_6 [2, 1, 5] = true := by decide +kernel
theorem subd5_6_472 : subd5_6 [2, 1, 6] = true := by decide +kernel
theorem subd5_6_473 : subd5_6 [2, 2, -8] = true := by decide +kernel
theorem subd5_6_474 : subd5_6 [2, 2, -7] = true := by decide +kernel
theorem subd5_6_475 : subd5_6 [2, 2, -6] = true := by decide +kernel
theorem subd5_6_476 : subd5_6 [2, 2, -5] = true := by decide +kernel
theorem subd5_6_477 : subd5_6 [2, 2, -4] = true := by decide +kernel
theorem subd5_6_478 : subd5_6 [2, 2, -3] = true := by decide +kernel
theorem subd5_6_479 : subd5_6 [2, 2, -2] = true := by decide +kernel
theorem sbd5_6_14 : ∀ q ∈ blkd5_6_14, subd5_6 q = true := by
  unfold blkd5_6_14
  exact List.forall_mem_cons.2 ⟨subd5_6_448, List.forall_mem_cons.2 ⟨subd5_6_449, List.forall_mem_cons.2 ⟨subd5_6_450, List.forall_mem_cons.2 ⟨subd5_6_451, List.forall_mem_cons.2 ⟨subd5_6_452, List.forall_mem_cons.2 ⟨subd5_6_453, List.forall_mem_cons.2 ⟨subd5_6_454, List.forall_mem_cons.2 ⟨subd5_6_455, List.forall_mem_cons.2 ⟨subd5_6_456, List.forall_mem_cons.2 ⟨subd5_6_457, List.forall_mem_cons.2 ⟨subd5_6_458, List.forall_mem_cons.2 ⟨subd5_6_459, List.forall_mem_cons.2 ⟨subd5_6_460, List.forall_mem_cons.2 ⟨subd5_6_461, List.forall_mem_cons.2 ⟨subd5_6_462, List.forall_mem_cons.2 ⟨subd5_6_463, List.forall_mem_cons.2 ⟨subd5_6_464, List.forall_mem_cons.2 ⟨subd5_6_465, List.forall_mem_cons.2 ⟨subd5_6_466, List.forall_mem_cons.2 ⟨subd5_6_467, List.forall_mem_cons.2 ⟨subd5_6_468, List.forall_mem_cons.2 ⟨subd5_6_469, List.forall_mem_cons.2 ⟨subd5_6_470, List.forall_mem_cons.2 ⟨subd5_6_471, List.forall_mem_cons.2 ⟨subd5_6_472, List.forall_mem_cons.2 ⟨subd5_6_473, List.forall_mem_cons.2 ⟨subd5_6_474, List.forall_mem_cons.2 ⟨subd5_6_475, List.forall_mem_cons.2 ⟨subd5_6_476, List.forall_mem_cons.2 ⟨subd5_6_477, List.forall_mem_cons.2 ⟨subd5_6_478, List.forall_mem_cons.2 ⟨subd5_6_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C099
