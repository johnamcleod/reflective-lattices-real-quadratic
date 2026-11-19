import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_2_96 : subd9_2 [-1, 0, -1] = true := by decide +kernel
theorem subd9_2_97 : subd9_2 [-1, 0, 0] = true := by decide +kernel
theorem subd9_2_98 : subd9_2 [-1, 0, 1] = true := by decide +kernel
theorem subd9_2_99 : subd9_2 [-1, 0, 2] = true := by decide +kernel
theorem subd9_2_100 : subd9_2 [-1, 0, 3] = true := by decide +kernel
theorem subd9_2_101 : subd9_2 [-1, 0, 4] = true := by decide +kernel
theorem subd9_2_102 : subd9_2 [-1, 0, 5] = true := by decide +kernel
theorem subd9_2_103 : subd9_2 [-1, 0, 6] = true := by decide +kernel
theorem subd9_2_104 : subd9_2 [-1, 1, -7] = true := by decide +kernel
theorem subd9_2_105 : subd9_2 [-1, 1, -6] = true := by decide +kernel
theorem subd9_2_106 : subd9_2 [-1, 1, -5] = true := by decide +kernel
theorem subd9_2_107 : subd9_2 [-1, 1, -4] = true := by decide +kernel
theorem subd9_2_108 : subd9_2 [-1, 1, -3] = true := by decide +kernel
theorem subd9_2_109 : subd9_2 [-1, 1, -2] = true := by decide +kernel
theorem subd9_2_110 : subd9_2 [-1, 1, -1] = true := by decide +kernel
theorem subd9_2_111 : subd9_2 [-1, 1, 0] = true := by decide +kernel
theorem subd9_2_112 : subd9_2 [-1, 1, 1] = true := by decide +kernel
theorem subd9_2_113 : subd9_2 [-1, 1, 2] = true := by decide +kernel
theorem subd9_2_114 : subd9_2 [-1, 1, 3] = true := by decide +kernel
theorem subd9_2_115 : subd9_2 [-1, 1, 4] = true := by decide +kernel
theorem subd9_2_116 : subd9_2 [-1, 1, 5] = true := by decide +kernel
theorem subd9_2_117 : subd9_2 [-1, 1, 6] = true := by decide +kernel
theorem subd9_2_118 : subd9_2 [-1, 1, 7] = true := by decide +kernel
theorem subd9_2_119 : subd9_2 [-1, 2, -6] = true := by decide +kernel
theorem subd9_2_120 : subd9_2 [-1, 2, -5] = true := by decide +kernel
theorem subd9_2_121 : subd9_2 [-1, 2, -4] = true := by decide +kernel
theorem subd9_2_122 : subd9_2 [-1, 2, -3] = true := by decide +kernel
theorem subd9_2_123 : subd9_2 [-1, 2, -2] = true := by decide +kernel
theorem subd9_2_124 : subd9_2 [-1, 2, -1] = true := by decide +kernel
theorem subd9_2_125 : subd9_2 [-1, 2, 0] = true := by decide +kernel
theorem subd9_2_126 : subd9_2 [-1, 2, 1] = true := by decide +kernel
theorem subd9_2_127 : subd9_2 [-1, 2, 2] = true := by decide +kernel
theorem sbd9_2_3 : ∀ q ∈ blkd9_2_3, subd9_2 q = true := by
  unfold blkd9_2_3
  exact List.forall_mem_cons.2 ⟨subd9_2_96, List.forall_mem_cons.2 ⟨subd9_2_97, List.forall_mem_cons.2 ⟨subd9_2_98, List.forall_mem_cons.2 ⟨subd9_2_99, List.forall_mem_cons.2 ⟨subd9_2_100, List.forall_mem_cons.2 ⟨subd9_2_101, List.forall_mem_cons.2 ⟨subd9_2_102, List.forall_mem_cons.2 ⟨subd9_2_103, List.forall_mem_cons.2 ⟨subd9_2_104, List.forall_mem_cons.2 ⟨subd9_2_105, List.forall_mem_cons.2 ⟨subd9_2_106, List.forall_mem_cons.2 ⟨subd9_2_107, List.forall_mem_cons.2 ⟨subd9_2_108, List.forall_mem_cons.2 ⟨subd9_2_109, List.forall_mem_cons.2 ⟨subd9_2_110, List.forall_mem_cons.2 ⟨subd9_2_111, List.forall_mem_cons.2 ⟨subd9_2_112, List.forall_mem_cons.2 ⟨subd9_2_113, List.forall_mem_cons.2 ⟨subd9_2_114, List.forall_mem_cons.2 ⟨subd9_2_115, List.forall_mem_cons.2 ⟨subd9_2_116, List.forall_mem_cons.2 ⟨subd9_2_117, List.forall_mem_cons.2 ⟨subd9_2_118, List.forall_mem_cons.2 ⟨subd9_2_119, List.forall_mem_cons.2 ⟨subd9_2_120, List.forall_mem_cons.2 ⟨subd9_2_121, List.forall_mem_cons.2 ⟨subd9_2_122, List.forall_mem_cons.2 ⟨subd9_2_123, List.forall_mem_cons.2 ⟨subd9_2_124, List.forall_mem_cons.2 ⟨subd9_2_125, List.forall_mem_cons.2 ⟨subd9_2_126, List.forall_mem_cons.2 ⟨subd9_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_128 : subd9_2 [-1, 2, 3] = true := by decide +kernel
theorem subd9_2_129 : subd9_2 [-1, 2, 4] = true := by decide +kernel
theorem subd9_2_130 : subd9_2 [-1, 2, 5] = true := by decide +kernel
theorem subd9_2_131 : subd9_2 [-1, 2, 6] = true := by decide +kernel
theorem subd9_2_132 : subd9_2 [-1, 2, 7] = true := by decide +kernel
theorem subd9_2_133 : subd9_2 [-1, 3] = true := by decide +kernel
theorem subd9_2_134 : subd9_2 [-1, 4] = true := by decide +kernel
theorem subd9_2_135 : subd9_2 [-1, 5] = true := by decide +kernel
theorem subd9_2_136 : subd9_2 [-1, 6] = true := by decide +kernel
theorem subd9_2_137 : subd9_2 [0, -7] = true := by decide +kernel
theorem subd9_2_138 : subd9_2 [0, -6] = true := by decide +kernel
theorem subd9_2_139 : subd9_2 [0, -5] = true := by decide +kernel
theorem subd9_2_140 : subd9_2 [0, -4] = true := by decide +kernel
theorem subd9_2_141 : subd9_2 [0, -3] = true := by decide +kernel
theorem subd9_2_142 : subd9_2 [0, -2, -7] = true := by decide +kernel
theorem subd9_2_143 : subd9_2 [0, -2, -6] = true := by decide +kernel
theorem subd9_2_144 : subd9_2 [0, -2, -5] = true := by decide +kernel
theorem subd9_2_145 : subd9_2 [0, -2, -4] = true := by decide +kernel
theorem subd9_2_146 : subd9_2 [0, -2, -3] = true := by decide +kernel
theorem subd9_2_147 : subd9_2 [0, -2, -2] = true := by decide +kernel
theorem subd9_2_148 : subd9_2 [0, -2, -1] = true := by decide +kernel
theorem subd9_2_149 : subd9_2 [0, -2, 0] = true := by decide +kernel
theorem subd9_2_150 : subd9_2 [0, -2, 1] = true := by decide +kernel
theorem subd9_2_151 : subd9_2 [0, -2, 2] = true := by decide +kernel
theorem subd9_2_152 : subd9_2 [0, -2, 3] = true := by decide +kernel
theorem subd9_2_153 : subd9_2 [0, -2, 4] = true := by decide +kernel
theorem subd9_2_154 : subd9_2 [0, -2, 5] = true := by decide +kernel
theorem subd9_2_155 : subd9_2 [0, -2, 6] = true := by decide +kernel
theorem subd9_2_156 : subd9_2 [0, -1, -7] = true := by decide +kernel
theorem subd9_2_157 : subd9_2 [0, -1, -6] = true := by decide +kernel
theorem subd9_2_158 : subd9_2 [0, -1, -5] = true := by decide +kernel
theorem subd9_2_159 : subd9_2 [0, -1, -4] = true := by decide +kernel
theorem sbd9_2_4 : ∀ q ∈ blkd9_2_4, subd9_2 q = true := by
  unfold blkd9_2_4
  exact List.forall_mem_cons.2 ⟨subd9_2_128, List.forall_mem_cons.2 ⟨subd9_2_129, List.forall_mem_cons.2 ⟨subd9_2_130, List.forall_mem_cons.2 ⟨subd9_2_131, List.forall_mem_cons.2 ⟨subd9_2_132, List.forall_mem_cons.2 ⟨subd9_2_133, List.forall_mem_cons.2 ⟨subd9_2_134, List.forall_mem_cons.2 ⟨subd9_2_135, List.forall_mem_cons.2 ⟨subd9_2_136, List.forall_mem_cons.2 ⟨subd9_2_137, List.forall_mem_cons.2 ⟨subd9_2_138, List.forall_mem_cons.2 ⟨subd9_2_139, List.forall_mem_cons.2 ⟨subd9_2_140, List.forall_mem_cons.2 ⟨subd9_2_141, List.forall_mem_cons.2 ⟨subd9_2_142, List.forall_mem_cons.2 ⟨subd9_2_143, List.forall_mem_cons.2 ⟨subd9_2_144, List.forall_mem_cons.2 ⟨subd9_2_145, List.forall_mem_cons.2 ⟨subd9_2_146, List.forall_mem_cons.2 ⟨subd9_2_147, List.forall_mem_cons.2 ⟨subd9_2_148, List.forall_mem_cons.2 ⟨subd9_2_149, List.forall_mem_cons.2 ⟨subd9_2_150, List.forall_mem_cons.2 ⟨subd9_2_151, List.forall_mem_cons.2 ⟨subd9_2_152, List.forall_mem_cons.2 ⟨subd9_2_153, List.forall_mem_cons.2 ⟨subd9_2_154, List.forall_mem_cons.2 ⟨subd9_2_155, List.forall_mem_cons.2 ⟨subd9_2_156, List.forall_mem_cons.2 ⟨subd9_2_157, List.forall_mem_cons.2 ⟨subd9_2_158, List.forall_mem_cons.2 ⟨subd9_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_160 : subd9_2 [0, -1, -3] = true := by decide +kernel
theorem subd9_2_161 : subd9_2 [0, -1, -2] = true := by decide +kernel
theorem subd9_2_162 : subd9_2 [0, -1, -1] = true := by decide +kernel
theorem subd9_2_163 : subd9_2 [0, -1, 0] = true := by decide +kernel
theorem subd9_2_164 : subd9_2 [0, -1, 1] = true := by decide +kernel
theorem subd9_2_165 : subd9_2 [0, -1, 2] = true := by decide +kernel
theorem subd9_2_166 : subd9_2 [0, -1, 3] = true := by decide +kernel
theorem subd9_2_167 : subd9_2 [0, -1, 4] = true := by decide +kernel
theorem subd9_2_168 : subd9_2 [0, -1, 5] = true := by decide +kernel
theorem subd9_2_169 : subd9_2 [0, -1, 6] = true := by decide +kernel
theorem subd9_2_170 : subd9_2 [0, 0, -7] = true := by decide +kernel
theorem subd9_2_171 : subd9_2 [0, 0, -6] = true := by decide +kernel
theorem subd9_2_172 : subd9_2 [0, 0, -5] = true := by decide +kernel
theorem subd9_2_173 : subd9_2 [0, 0, -4] = true := by decide +kernel
theorem subd9_2_174 : subd9_2 [0, 0, -3] = true := by decide +kernel
theorem subd9_2_175 : subd9_2 [0, 0, -2] = true := by decide +kernel
theorem subd9_2_176 : subd9_2 [0, 0, -1] = true := by decide +kernel
theorem subd9_2_177 : subd9_2 [0, 0, 0] = true := by decide +kernel
theorem subd9_2_178 : subd9_2 [0, 0, 1] = true := by decide +kernel
theorem subd9_2_179 : subd9_2 [0, 0, 2] = true := by decide +kernel
theorem subd9_2_180 : subd9_2 [0, 0, 3] = true := by decide +kernel
theorem subd9_2_181 : subd9_2 [0, 0, 4] = true := by decide +kernel
theorem subd9_2_182 : subd9_2 [0, 0, 5] = true := by decide +kernel
theorem subd9_2_183 : subd9_2 [0, 0, 6] = true := by decide +kernel
theorem subd9_2_184 : subd9_2 [0, 1, -7] = true := by decide +kernel
theorem subd9_2_185 : subd9_2 [0, 1, -6] = true := by decide +kernel
theorem subd9_2_186 : subd9_2 [0, 1, -5] = true := by decide +kernel
theorem subd9_2_187 : subd9_2 [0, 1, -4] = true := by decide +kernel
theorem subd9_2_188 : subd9_2 [0, 1, -3] = true := by decide +kernel
theorem subd9_2_189 : subd9_2 [0, 1, -2] = true := by decide +kernel
theorem subd9_2_190 : subd9_2 [0, 1, -1] = true := by decide +kernel
theorem subd9_2_191 : subd9_2 [0, 1, 0] = true := by decide +kernel
theorem sbd9_2_5 : ∀ q ∈ blkd9_2_5, subd9_2 q = true := by
  unfold blkd9_2_5
  exact List.forall_mem_cons.2 ⟨subd9_2_160, List.forall_mem_cons.2 ⟨subd9_2_161, List.forall_mem_cons.2 ⟨subd9_2_162, List.forall_mem_cons.2 ⟨subd9_2_163, List.forall_mem_cons.2 ⟨subd9_2_164, List.forall_mem_cons.2 ⟨subd9_2_165, List.forall_mem_cons.2 ⟨subd9_2_166, List.forall_mem_cons.2 ⟨subd9_2_167, List.forall_mem_cons.2 ⟨subd9_2_168, List.forall_mem_cons.2 ⟨subd9_2_169, List.forall_mem_cons.2 ⟨subd9_2_170, List.forall_mem_cons.2 ⟨subd9_2_171, List.forall_mem_cons.2 ⟨subd9_2_172, List.forall_mem_cons.2 ⟨subd9_2_173, List.forall_mem_cons.2 ⟨subd9_2_174, List.forall_mem_cons.2 ⟨subd9_2_175, List.forall_mem_cons.2 ⟨subd9_2_176, List.forall_mem_cons.2 ⟨subd9_2_177, List.forall_mem_cons.2 ⟨subd9_2_178, List.forall_mem_cons.2 ⟨subd9_2_179, List.forall_mem_cons.2 ⟨subd9_2_180, List.forall_mem_cons.2 ⟨subd9_2_181, List.forall_mem_cons.2 ⟨subd9_2_182, List.forall_mem_cons.2 ⟨subd9_2_183, List.forall_mem_cons.2 ⟨subd9_2_184, List.forall_mem_cons.2 ⟨subd9_2_185, List.forall_mem_cons.2 ⟨subd9_2_186, List.forall_mem_cons.2 ⟨subd9_2_187, List.forall_mem_cons.2 ⟨subd9_2_188, List.forall_mem_cons.2 ⟨subd9_2_189, List.forall_mem_cons.2 ⟨subd9_2_190, List.forall_mem_cons.2 ⟨subd9_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_192 : subd9_2 [0, 1, 1] = true := by decide +kernel
theorem subd9_2_193 : subd9_2 [0, 1, 2] = true := by decide +kernel
theorem subd9_2_194 : subd9_2 [0, 1, 3] = true := by decide +kernel
theorem subd9_2_195 : subd9_2 [0, 1, 4] = true := by decide +kernel
theorem subd9_2_196 : subd9_2 [0, 1, 5] = true := by decide +kernel
theorem subd9_2_197 : subd9_2 [0, 1, 6] = true := by decide +kernel
theorem subd9_2_198 : subd9_2 [0, 2, -7] = true := by decide +kernel
theorem subd9_2_199 : subd9_2 [0, 2, -6] = true := by decide +kernel
theorem subd9_2_200 : subd9_2 [0, 2, -5] = true := by decide +kernel
theorem subd9_2_201 : subd9_2 [0, 2, -4] = true := by decide +kernel
theorem subd9_2_202 : subd9_2 [0, 2, -3] = true := by decide +kernel
theorem subd9_2_203 : subd9_2 [0, 2, -2] = true := by decide +kernel
theorem subd9_2_204 : subd9_2 [0, 2, -1] = true := by decide +kernel
theorem subd9_2_205 : subd9_2 [0, 2, 0] = true := by decide +kernel
theorem subd9_2_206 : subd9_2 [0, 2, 1] = true := by decide +kernel
theorem subd9_2_207 : subd9_2 [0, 2, 2] = true := by decide +kernel
theorem subd9_2_208 : subd9_2 [0, 2, 3] = true := by decide +kernel
theorem subd9_2_209 : subd9_2 [0, 2, 4] = true := by decide +kernel
theorem subd9_2_210 : subd9_2 [0, 2, 5] = true := by decide +kernel
theorem subd9_2_211 : subd9_2 [0, 2, 6] = true := by decide +kernel
theorem subd9_2_212 : subd9_2 [0, 3] = true := by decide +kernel
theorem subd9_2_213 : subd9_2 [0, 4] = true := by decide +kernel
theorem subd9_2_214 : subd9_2 [0, 5] = true := by decide +kernel
theorem subd9_2_215 : subd9_2 [0, 6] = true := by decide +kernel
theorem subd9_2_216 : subd9_2 [1, -7] = true := by decide +kernel
theorem subd9_2_217 : subd9_2 [1, -6] = true := by decide +kernel
theorem subd9_2_218 : subd9_2 [1, -5] = true := by decide +kernel
theorem subd9_2_219 : subd9_2 [1, -4] = true := by decide +kernel
theorem subd9_2_220 : subd9_2 [1, -3] = true := by decide +kernel
theorem subd9_2_221 : subd9_2 [1, -2, -8] = true := by decide +kernel
theorem subd9_2_222 : subd9_2 [1, -2, -7] = true := by decide +kernel
theorem subd9_2_223 : subd9_2 [1, -2, -6] = true := by decide +kernel
theorem sbd9_2_6 : ∀ q ∈ blkd9_2_6, subd9_2 q = true := by
  unfold blkd9_2_6
  exact List.forall_mem_cons.2 ⟨subd9_2_192, List.forall_mem_cons.2 ⟨subd9_2_193, List.forall_mem_cons.2 ⟨subd9_2_194, List.forall_mem_cons.2 ⟨subd9_2_195, List.forall_mem_cons.2 ⟨subd9_2_196, List.forall_mem_cons.2 ⟨subd9_2_197, List.forall_mem_cons.2 ⟨subd9_2_198, List.forall_mem_cons.2 ⟨subd9_2_199, List.forall_mem_cons.2 ⟨subd9_2_200, List.forall_mem_cons.2 ⟨subd9_2_201, List.forall_mem_cons.2 ⟨subd9_2_202, List.forall_mem_cons.2 ⟨subd9_2_203, List.forall_mem_cons.2 ⟨subd9_2_204, List.forall_mem_cons.2 ⟨subd9_2_205, List.forall_mem_cons.2 ⟨subd9_2_206, List.forall_mem_cons.2 ⟨subd9_2_207, List.forall_mem_cons.2 ⟨subd9_2_208, List.forall_mem_cons.2 ⟨subd9_2_209, List.forall_mem_cons.2 ⟨subd9_2_210, List.forall_mem_cons.2 ⟨subd9_2_211, List.forall_mem_cons.2 ⟨subd9_2_212, List.forall_mem_cons.2 ⟨subd9_2_213, List.forall_mem_cons.2 ⟨subd9_2_214, List.forall_mem_cons.2 ⟨subd9_2_215, List.forall_mem_cons.2 ⟨subd9_2_216, List.forall_mem_cons.2 ⟨subd9_2_217, List.forall_mem_cons.2 ⟨subd9_2_218, List.forall_mem_cons.2 ⟨subd9_2_219, List.forall_mem_cons.2 ⟨subd9_2_220, List.forall_mem_cons.2 ⟨subd9_2_221, List.forall_mem_cons.2 ⟨subd9_2_222, List.forall_mem_cons.2 ⟨subd9_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_224 : subd9_2 [1, -2, -5] = true := by decide +kernel
theorem subd9_2_225 : subd9_2 [1, -2, -4] = true := by decide +kernel
theorem subd9_2_226 : subd9_2 [1, -2, -3] = true := by decide +kernel
theorem subd9_2_227 : subd9_2 [1, -2, -2] = true := by decide +kernel
theorem subd9_2_228 : subd9_2 [1, -2, -1] = true := by decide +kernel
theorem subd9_2_229 : subd9_2 [1, -2, 0] = true := by decide +kernel
theorem subd9_2_230 : subd9_2 [1, -2, 1] = true := by decide +kernel
theorem subd9_2_231 : subd9_2 [1, -2, 2] = true := by decide +kernel
theorem subd9_2_232 : subd9_2 [1, -2, 3] = true := by decide +kernel
theorem subd9_2_233 : subd9_2 [1, -2, 4] = true := by decide +kernel
theorem subd9_2_234 : subd9_2 [1, -2, 5] = true := by decide +kernel
theorem subd9_2_235 : subd9_2 [1, -1, -8] = true := by decide +kernel
theorem subd9_2_236 : subd9_2 [1, -1, -7] = true := by decide +kernel
theorem subd9_2_237 : subd9_2 [1, -1, -6] = true := by decide +kernel
theorem subd9_2_238 : subd9_2 [1, -1, -5] = true := by decide +kernel
theorem subd9_2_239 : subd9_2 [1, -1, -4] = true := by decide +kernel
theorem subd9_2_240 : subd9_2 [1, -1, -3] = true := by decide +kernel
theorem subd9_2_241 : subd9_2 [1, -1, -2] = true := by decide +kernel
theorem subd9_2_242 : subd9_2 [1, -1, -1] = true := by decide +kernel
theorem subd9_2_243 : subd9_2 [1, -1, 0] = true := by decide +kernel
theorem subd9_2_244 : subd9_2 [1, -1, 1] = true := by decide +kernel
theorem subd9_2_245 : subd9_2 [1, -1, 2] = true := by decide +kernel
theorem subd9_2_246 : subd9_2 [1, -1, 3] = true := by decide +kernel
theorem subd9_2_247 : subd9_2 [1, -1, 4] = true := by decide +kernel
theorem subd9_2_248 : subd9_2 [1, -1, 5] = true := by decide +kernel
theorem subd9_2_249 : subd9_2 [1, -1, 6] = true := by decide +kernel
theorem subd9_2_250 : subd9_2 [1, 0, -7] = true := by decide +kernel
theorem subd9_2_251 : subd9_2 [1, 0, -6] = true := by decide +kernel
theorem subd9_2_252 : subd9_2 [1, 0, -5] = true := by decide +kernel
theorem subd9_2_253 : subd9_2 [1, 0, -4] = true := by decide +kernel
theorem subd9_2_254 : subd9_2 [1, 0, -3] = true := by decide +kernel
theorem subd9_2_255 : subd9_2 [1, 0, -2] = true := by decide +kernel
theorem sbd9_2_7 : ∀ q ∈ blkd9_2_7, subd9_2 q = true := by
  unfold blkd9_2_7
  exact List.forall_mem_cons.2 ⟨subd9_2_224, List.forall_mem_cons.2 ⟨subd9_2_225, List.forall_mem_cons.2 ⟨subd9_2_226, List.forall_mem_cons.2 ⟨subd9_2_227, List.forall_mem_cons.2 ⟨subd9_2_228, List.forall_mem_cons.2 ⟨subd9_2_229, List.forall_mem_cons.2 ⟨subd9_2_230, List.forall_mem_cons.2 ⟨subd9_2_231, List.forall_mem_cons.2 ⟨subd9_2_232, List.forall_mem_cons.2 ⟨subd9_2_233, List.forall_mem_cons.2 ⟨subd9_2_234, List.forall_mem_cons.2 ⟨subd9_2_235, List.forall_mem_cons.2 ⟨subd9_2_236, List.forall_mem_cons.2 ⟨subd9_2_237, List.forall_mem_cons.2 ⟨subd9_2_238, List.forall_mem_cons.2 ⟨subd9_2_239, List.forall_mem_cons.2 ⟨subd9_2_240, List.forall_mem_cons.2 ⟨subd9_2_241, List.forall_mem_cons.2 ⟨subd9_2_242, List.forall_mem_cons.2 ⟨subd9_2_243, List.forall_mem_cons.2 ⟨subd9_2_244, List.forall_mem_cons.2 ⟨subd9_2_245, List.forall_mem_cons.2 ⟨subd9_2_246, List.forall_mem_cons.2 ⟨subd9_2_247, List.forall_mem_cons.2 ⟨subd9_2_248, List.forall_mem_cons.2 ⟨subd9_2_249, List.forall_mem_cons.2 ⟨subd9_2_250, List.forall_mem_cons.2 ⟨subd9_2_251, List.forall_mem_cons.2 ⟨subd9_2_252, List.forall_mem_cons.2 ⟨subd9_2_253, List.forall_mem_cons.2 ⟨subd9_2_254, List.forall_mem_cons.2 ⟨subd9_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_256 : subd9_2 [1, 0, -1] = true := by decide +kernel
theorem subd9_2_257 : subd9_2 [1, 0, 0] = true := by decide +kernel
theorem subd9_2_258 : subd9_2 [1, 0, 1] = true := by decide +kernel
theorem subd9_2_259 : subd9_2 [1, 0, 2] = true := by decide +kernel
theorem subd9_2_260 : subd9_2 [1, 0, 3] = true := by decide +kernel
theorem subd9_2_261 : subd9_2 [1, 0, 4] = true := by decide +kernel
theorem subd9_2_262 : subd9_2 [1, 0, 5] = true := by decide +kernel
theorem subd9_2_263 : subd9_2 [1, 0, 6] = true := by decide +kernel
theorem subd9_2_264 : subd9_2 [1, 1, -7] = true := by decide +kernel
theorem subd9_2_265 : subd9_2 [1, 1, -6] = true := by decide +kernel
theorem subd9_2_266 : subd9_2 [1, 1, -5] = true := by decide +kernel
theorem subd9_2_267 : subd9_2 [1, 1, -4] = true := by decide +kernel
theorem subd9_2_268 : subd9_2 [1, 1, -3] = true := by decide +kernel
theorem subd9_2_269 : subd9_2 [1, 1, -2] = true := by decide +kernel
theorem subd9_2_270 : subd9_2 [1, 1, -1] = true := by decide +kernel
theorem subd9_2_271 : subd9_2 [1, 1, 0] = true := by decide +kernel
theorem subd9_2_272 : subd9_2 [1, 1, 1] = true := by decide +kernel
theorem subd9_2_273 : subd9_2 [1, 1, 2] = true := by decide +kernel
theorem subd9_2_274 : subd9_2 [1, 1, 3] = true := by decide +kernel
theorem subd9_2_275 : subd9_2 [1, 1, 4] = true := by decide +kernel
theorem subd9_2_276 : subd9_2 [1, 1, 5] = true := by decide +kernel
theorem subd9_2_277 : subd9_2 [1, 1, 6] = true := by decide +kernel
theorem subd9_2_278 : subd9_2 [1, 2] = true := by decide +kernel
theorem subd9_2_279 : subd9_2 [1, 3] = true := by decide +kernel
theorem subd9_2_280 : subd9_2 [1, 4] = true := by decide +kernel
theorem subd9_2_281 : subd9_2 [1, 5] = true := by decide +kernel
theorem subd9_2_282 : subd9_2 [2, -7] = true := by decide +kernel
theorem subd9_2_283 : subd9_2 [2, -6] = true := by decide +kernel
theorem subd9_2_284 : subd9_2 [2, -5] = true := by decide +kernel
theorem subd9_2_285 : subd9_2 [2, -4] = true := by decide +kernel
theorem subd9_2_286 : subd9_2 [2, -3] = true := by decide +kernel
theorem subd9_2_287 : subd9_2 [2, -2, -8] = true := by decide +kernel
theorem sbd9_2_8 : ∀ q ∈ blkd9_2_8, subd9_2 q = true := by
  unfold blkd9_2_8
  exact List.forall_mem_cons.2 ⟨subd9_2_256, List.forall_mem_cons.2 ⟨subd9_2_257, List.forall_mem_cons.2 ⟨subd9_2_258, List.forall_mem_cons.2 ⟨subd9_2_259, List.forall_mem_cons.2 ⟨subd9_2_260, List.forall_mem_cons.2 ⟨subd9_2_261, List.forall_mem_cons.2 ⟨subd9_2_262, List.forall_mem_cons.2 ⟨subd9_2_263, List.forall_mem_cons.2 ⟨subd9_2_264, List.forall_mem_cons.2 ⟨subd9_2_265, List.forall_mem_cons.2 ⟨subd9_2_266, List.forall_mem_cons.2 ⟨subd9_2_267, List.forall_mem_cons.2 ⟨subd9_2_268, List.forall_mem_cons.2 ⟨subd9_2_269, List.forall_mem_cons.2 ⟨subd9_2_270, List.forall_mem_cons.2 ⟨subd9_2_271, List.forall_mem_cons.2 ⟨subd9_2_272, List.forall_mem_cons.2 ⟨subd9_2_273, List.forall_mem_cons.2 ⟨subd9_2_274, List.forall_mem_cons.2 ⟨subd9_2_275, List.forall_mem_cons.2 ⟨subd9_2_276, List.forall_mem_cons.2 ⟨subd9_2_277, List.forall_mem_cons.2 ⟨subd9_2_278, List.forall_mem_cons.2 ⟨subd9_2_279, List.forall_mem_cons.2 ⟨subd9_2_280, List.forall_mem_cons.2 ⟨subd9_2_281, List.forall_mem_cons.2 ⟨subd9_2_282, List.forall_mem_cons.2 ⟨subd9_2_283, List.forall_mem_cons.2 ⟨subd9_2_284, List.forall_mem_cons.2 ⟨subd9_2_285, List.forall_mem_cons.2 ⟨subd9_2_286, List.forall_mem_cons.2 ⟨subd9_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_288 : subd9_2 [2, -2, -7] = true := by decide +kernel
theorem subd9_2_289 : subd9_2 [2, -2, -6] = true := by decide +kernel
theorem subd9_2_290 : subd9_2 [2, -2, -5] = true := by decide +kernel
theorem subd9_2_291 : subd9_2 [2, -2, -4] = true := by decide +kernel
theorem subd9_2_292 : subd9_2 [2, -2, -3] = true := by decide +kernel
theorem subd9_2_293 : subd9_2 [2, -2, -2] = true := by decide +kernel
theorem subd9_2_294 : subd9_2 [2, -2, -1] = true := by decide +kernel
theorem subd9_2_295 : subd9_2 [2, -2, 0] = true := by decide +kernel
theorem subd9_2_296 : subd9_2 [2, -2, 1] = true := by decide +kernel
theorem subd9_2_297 : subd9_2 [2, -2, 2] = true := by decide +kernel
theorem subd9_2_298 : subd9_2 [2, -2, 3] = true := by decide +kernel
theorem subd9_2_299 : subd9_2 [2, -2, 4] = true := by decide +kernel
theorem subd9_2_300 : subd9_2 [2, -2, 5] = true := by decide +kernel
theorem subd9_2_301 : subd9_2 [2, -1, -8] = true := by decide +kernel
theorem subd9_2_302 : subd9_2 [2, -1, -7] = true := by decide +kernel
theorem subd9_2_303 : subd9_2 [2, -1, -6] = true := by decide +kernel
theorem subd9_2_304 : subd9_2 [2, -1, -5] = true := by decide +kernel
theorem subd9_2_305 : subd9_2 [2, -1, -4] = true := by decide +kernel
theorem subd9_2_306 : subd9_2 [2, -1, -3] = true := by decide +kernel
theorem subd9_2_307 : subd9_2 [2, -1, -2] = true := by decide +kernel
theorem subd9_2_308 : subd9_2 [2, -1, -1] = true := by decide +kernel
theorem subd9_2_309 : subd9_2 [2, -1, 0] = true := by decide +kernel
theorem subd9_2_310 : subd9_2 [2, -1, 1] = true := by decide +kernel
theorem subd9_2_311 : subd9_2 [2, -1, 2] = true := by decide +kernel
theorem subd9_2_312 : subd9_2 [2, -1, 3] = true := by decide +kernel
theorem subd9_2_313 : subd9_2 [2, -1, 4] = true := by decide +kernel
theorem subd9_2_314 : subd9_2 [2, -1, 5] = true := by decide +kernel
theorem subd9_2_315 : subd9_2 [2, 0] = true := by decide +kernel
theorem subd9_2_316 : subd9_2 [2, 1] = true := by decide +kernel
theorem subd9_2_317 : subd9_2 [2, 2] = true := by decide +kernel
theorem subd9_2_318 : subd9_2 [2, 3] = true := by decide +kernel
theorem subd9_2_319 : subd9_2 [2, 4] = true := by decide +kernel
theorem sbd9_2_9 : ∀ q ∈ blkd9_2_9, subd9_2 q = true := by
  unfold blkd9_2_9
  exact List.forall_mem_cons.2 ⟨subd9_2_288, List.forall_mem_cons.2 ⟨subd9_2_289, List.forall_mem_cons.2 ⟨subd9_2_290, List.forall_mem_cons.2 ⟨subd9_2_291, List.forall_mem_cons.2 ⟨subd9_2_292, List.forall_mem_cons.2 ⟨subd9_2_293, List.forall_mem_cons.2 ⟨subd9_2_294, List.forall_mem_cons.2 ⟨subd9_2_295, List.forall_mem_cons.2 ⟨subd9_2_296, List.forall_mem_cons.2 ⟨subd9_2_297, List.forall_mem_cons.2 ⟨subd9_2_298, List.forall_mem_cons.2 ⟨subd9_2_299, List.forall_mem_cons.2 ⟨subd9_2_300, List.forall_mem_cons.2 ⟨subd9_2_301, List.forall_mem_cons.2 ⟨subd9_2_302, List.forall_mem_cons.2 ⟨subd9_2_303, List.forall_mem_cons.2 ⟨subd9_2_304, List.forall_mem_cons.2 ⟨subd9_2_305, List.forall_mem_cons.2 ⟨subd9_2_306, List.forall_mem_cons.2 ⟨subd9_2_307, List.forall_mem_cons.2 ⟨subd9_2_308, List.forall_mem_cons.2 ⟨subd9_2_309, List.forall_mem_cons.2 ⟨subd9_2_310, List.forall_mem_cons.2 ⟨subd9_2_311, List.forall_mem_cons.2 ⟨subd9_2_312, List.forall_mem_cons.2 ⟨subd9_2_313, List.forall_mem_cons.2 ⟨subd9_2_314, List.forall_mem_cons.2 ⟨subd9_2_315, List.forall_mem_cons.2 ⟨subd9_2_316, List.forall_mem_cons.2 ⟨subd9_2_317, List.forall_mem_cons.2 ⟨subd9_2_318, List.forall_mem_cons.2 ⟨subd9_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_320 : subd9_2 [2, 5] = true := by decide +kernel
theorem subd9_2_321 : subd9_2 [3, -7] = true := by decide +kernel
theorem subd9_2_322 : subd9_2 [3, -6] = true := by decide +kernel
theorem subd9_2_323 : subd9_2 [3, -5] = true := by decide +kernel
theorem subd9_2_324 : subd9_2 [3, -4] = true := by decide +kernel
theorem subd9_2_325 : subd9_2 [3, -3] = true := by decide +kernel
theorem subd9_2_326 : subd9_2 [3, -2] = true := by decide +kernel
theorem subd9_2_327 : subd9_2 [3, -1] = true := by decide +kernel
theorem subd9_2_328 : subd9_2 [3, 0] = true := by decide +kernel
theorem subd9_2_329 : subd9_2 [3, 1] = true := by decide +kernel
theorem subd9_2_330 : subd9_2 [3, 2] = true := by decide +kernel
theorem subd9_2_331 : subd9_2 [3, 3] = true := by decide +kernel
theorem subd9_2_332 : subd9_2 [3, 4] = true := by decide +kernel
theorem subd9_2_333 : subd9_2 [4, -7] = true := by decide +kernel
theorem subd9_2_334 : subd9_2 [4, -6] = true := by decide +kernel
theorem subd9_2_335 : subd9_2 [4, -5] = true := by decide +kernel
theorem subd9_2_336 : subd9_2 [4, -4] = true := by decide +kernel
theorem subd9_2_337 : subd9_2 [4, -3] = true := by decide +kernel
theorem subd9_2_338 : subd9_2 [4, -2] = true := by decide +kernel
theorem subd9_2_339 : subd9_2 [4, -1] = true := by decide +kernel
theorem subd9_2_340 : subd9_2 [4, 0] = true := by decide +kernel
theorem subd9_2_341 : subd9_2 [4, 1] = true := by decide +kernel
theorem subd9_2_342 : subd9_2 [4, 2] = true := by decide +kernel
theorem subd9_2_343 : subd9_2 [4, 3] = true := by decide +kernel
theorem subd9_2_344 : subd9_2 [5, -6] = true := by decide +kernel
theorem subd9_2_345 : subd9_2 [5, -5] = true := by decide +kernel
theorem subd9_2_346 : subd9_2 [5, -4] = true := by decide +kernel
theorem subd9_2_347 : subd9_2 [5, -3] = true := by decide +kernel
theorem subd9_2_348 : subd9_2 [5, -2] = true := by decide +kernel
theorem subd9_2_349 : subd9_2 [5, -1] = true := by decide +kernel
theorem subd9_2_350 : subd9_2 [5, 0] = true := by decide +kernel
theorem subd9_2_351 : subd9_2 [5, 1] = true := by decide +kernel
theorem sbd9_2_10 : ∀ q ∈ blkd9_2_10, subd9_2 q = true := by
  unfold blkd9_2_10
  exact List.forall_mem_cons.2 ⟨subd9_2_320, List.forall_mem_cons.2 ⟨subd9_2_321, List.forall_mem_cons.2 ⟨subd9_2_322, List.forall_mem_cons.2 ⟨subd9_2_323, List.forall_mem_cons.2 ⟨subd9_2_324, List.forall_mem_cons.2 ⟨subd9_2_325, List.forall_mem_cons.2 ⟨subd9_2_326, List.forall_mem_cons.2 ⟨subd9_2_327, List.forall_mem_cons.2 ⟨subd9_2_328, List.forall_mem_cons.2 ⟨subd9_2_329, List.forall_mem_cons.2 ⟨subd9_2_330, List.forall_mem_cons.2 ⟨subd9_2_331, List.forall_mem_cons.2 ⟨subd9_2_332, List.forall_mem_cons.2 ⟨subd9_2_333, List.forall_mem_cons.2 ⟨subd9_2_334, List.forall_mem_cons.2 ⟨subd9_2_335, List.forall_mem_cons.2 ⟨subd9_2_336, List.forall_mem_cons.2 ⟨subd9_2_337, List.forall_mem_cons.2 ⟨subd9_2_338, List.forall_mem_cons.2 ⟨subd9_2_339, List.forall_mem_cons.2 ⟨subd9_2_340, List.forall_mem_cons.2 ⟨subd9_2_341, List.forall_mem_cons.2 ⟨subd9_2_342, List.forall_mem_cons.2 ⟨subd9_2_343, List.forall_mem_cons.2 ⟨subd9_2_344, List.forall_mem_cons.2 ⟨subd9_2_345, List.forall_mem_cons.2 ⟨subd9_2_346, List.forall_mem_cons.2 ⟨subd9_2_347, List.forall_mem_cons.2 ⟨subd9_2_348, List.forall_mem_cons.2 ⟨subd9_2_349, List.forall_mem_cons.2 ⟨subd9_2_350, List.forall_mem_cons.2 ⟨subd9_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_352 : subd9_2 [6] = true := by decide +kernel
theorem sbd9_2_11 : ∀ q ∈ blkd9_2_11, subd9_2 q = true := by
  unfold blkd9_2_11
  exact List.forall_mem_cons.2 ⟨subd9_2_352, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C141
