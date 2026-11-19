import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_96 : subd9_1 [-1, 1, 0] = true := by decide +kernel
theorem subd9_1_97 : subd9_1 [-1, 1, 1] = true := by decide +kernel
theorem subd9_1_98 : subd9_1 [-1, 1, 2] = true := by decide +kernel
theorem subd9_1_99 : subd9_1 [-1, 1, 3] = true := by decide +kernel
theorem subd9_1_100 : subd9_1 [-1, 1, 4] = true := by decide +kernel
theorem subd9_1_101 : subd9_1 [-1, 1, 5] = true := by decide +kernel
theorem subd9_1_102 : subd9_1 [-1, 1, 6] = true := by decide +kernel
theorem subd9_1_103 : subd9_1 [-1, 2] = true := by decide +kernel
theorem subd9_1_104 : subd9_1 [-1, 3] = true := by decide +kernel
theorem subd9_1_105 : subd9_1 [-1, 4] = true := by decide +kernel
theorem subd9_1_106 : subd9_1 [-1, 5] = true := by decide +kernel
theorem subd9_1_107 : subd9_1 [-1, 6] = true := by decide +kernel
theorem subd9_1_108 : subd9_1 [-1, 7] = true := by decide +kernel
theorem subd9_1_109 : subd9_1 [0, -7] = true := by decide +kernel
theorem subd9_1_110 : subd9_1 [0, -6] = true := by decide +kernel
theorem subd9_1_111 : subd9_1 [0, -5] = true := by decide +kernel
theorem subd9_1_112 : subd9_1 [0, -4] = true := by decide +kernel
theorem subd9_1_113 : subd9_1 [0, -3] = true := by decide +kernel
theorem subd9_1_114 : subd9_1 [0, -2, -6] = true := by decide +kernel
theorem subd9_1_115 : subd9_1 [0, -2, -5] = true := by decide +kernel
theorem subd9_1_116 : subd9_1 [0, -2, -4] = true := by decide +kernel
theorem subd9_1_117 : subd9_1 [0, -2, -3] = true := by decide +kernel
theorem subd9_1_118 : subd9_1 [0, -2, -2] = true := by decide +kernel
theorem subd9_1_119 : subd9_1 [0, -2, -1] = true := by decide +kernel
theorem subd9_1_120 : subd9_1 [0, -2, 0] = true := by decide +kernel
theorem subd9_1_121 : subd9_1 [0, -2, 1] = true := by decide +kernel
theorem subd9_1_122 : subd9_1 [0, -2, 2] = true := by decide +kernel
theorem subd9_1_123 : subd9_1 [0, -2, 3] = true := by decide +kernel
theorem subd9_1_124 : subd9_1 [0, -2, 4] = true := by decide +kernel
theorem subd9_1_125 : subd9_1 [0, -2, 5] = true := by decide +kernel
theorem subd9_1_126 : subd9_1 [0, -2, 6] = true := by decide +kernel
theorem subd9_1_127 : subd9_1 [0, -1, -6] = true := by decide +kernel
theorem sbd9_1_3 : ∀ q ∈ blkd9_1_3, subd9_1 q = true := by
  unfold blkd9_1_3
  exact List.forall_mem_cons.2 ⟨subd9_1_96, List.forall_mem_cons.2 ⟨subd9_1_97, List.forall_mem_cons.2 ⟨subd9_1_98, List.forall_mem_cons.2 ⟨subd9_1_99, List.forall_mem_cons.2 ⟨subd9_1_100, List.forall_mem_cons.2 ⟨subd9_1_101, List.forall_mem_cons.2 ⟨subd9_1_102, List.forall_mem_cons.2 ⟨subd9_1_103, List.forall_mem_cons.2 ⟨subd9_1_104, List.forall_mem_cons.2 ⟨subd9_1_105, List.forall_mem_cons.2 ⟨subd9_1_106, List.forall_mem_cons.2 ⟨subd9_1_107, List.forall_mem_cons.2 ⟨subd9_1_108, List.forall_mem_cons.2 ⟨subd9_1_109, List.forall_mem_cons.2 ⟨subd9_1_110, List.forall_mem_cons.2 ⟨subd9_1_111, List.forall_mem_cons.2 ⟨subd9_1_112, List.forall_mem_cons.2 ⟨subd9_1_113, List.forall_mem_cons.2 ⟨subd9_1_114, List.forall_mem_cons.2 ⟨subd9_1_115, List.forall_mem_cons.2 ⟨subd9_1_116, List.forall_mem_cons.2 ⟨subd9_1_117, List.forall_mem_cons.2 ⟨subd9_1_118, List.forall_mem_cons.2 ⟨subd9_1_119, List.forall_mem_cons.2 ⟨subd9_1_120, List.forall_mem_cons.2 ⟨subd9_1_121, List.forall_mem_cons.2 ⟨subd9_1_122, List.forall_mem_cons.2 ⟨subd9_1_123, List.forall_mem_cons.2 ⟨subd9_1_124, List.forall_mem_cons.2 ⟨subd9_1_125, List.forall_mem_cons.2 ⟨subd9_1_126, List.forall_mem_cons.2 ⟨subd9_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_128 : subd9_1 [0, -1, -5] = true := by decide +kernel
theorem subd9_1_129 : subd9_1 [0, -1, -4] = true := by decide +kernel
theorem subd9_1_130 : subd9_1 [0, -1, -3] = true := by decide +kernel
theorem subd9_1_131 : subd9_1 [0, -1, -2] = true := by decide +kernel
theorem subd9_1_132 : subd9_1 [0, -1, -1] = true := by decide +kernel
theorem subd9_1_133 : subd9_1 [0, -1, 0] = true := by decide +kernel
theorem subd9_1_134 : subd9_1 [0, -1, 1] = true := by decide +kernel
theorem subd9_1_135 : subd9_1 [0, -1, 2] = true := by decide +kernel
theorem subd9_1_136 : subd9_1 [0, -1, 3] = true := by decide +kernel
theorem subd9_1_137 : subd9_1 [0, -1, 4] = true := by decide +kernel
theorem subd9_1_138 : subd9_1 [0, -1, 5] = true := by decide +kernel
theorem subd9_1_139 : subd9_1 [0, -1, 6] = true := by decide +kernel
theorem subd9_1_140 : subd9_1 [0, 0, -7] = true := by decide +kernel
theorem subd9_1_141 : subd9_1 [0, 0, -6] = true := by decide +kernel
theorem subd9_1_142 : subd9_1 [0, 0, -5] = true := by decide +kernel
theorem subd9_1_143 : subd9_1 [0, 0, -4] = true := by decide +kernel
theorem subd9_1_144 : subd9_1 [0, 0, -3] = true := by decide +kernel
theorem subd9_1_145 : subd9_1 [0, 0, -2] = true := by decide +kernel
theorem subd9_1_146 : subd9_1 [0, 0, -1] = true := by decide +kernel
theorem subd9_1_147 : subd9_1 [0, 0, 0] = true := by decide +kernel
theorem subd9_1_148 : subd9_1 [0, 0, 1] = true := by decide +kernel
theorem subd9_1_149 : subd9_1 [0, 0, 2] = true := by decide +kernel
theorem subd9_1_150 : subd9_1 [0, 0, 3] = true := by decide +kernel
theorem subd9_1_151 : subd9_1 [0, 0, 4] = true := by decide +kernel
theorem subd9_1_152 : subd9_1 [0, 0, 5] = true := by decide +kernel
theorem subd9_1_153 : subd9_1 [0, 0, 6] = true := by decide +kernel
theorem subd9_1_154 : subd9_1 [0, 1, -7] = true := by decide +kernel
theorem subd9_1_155 : subd9_1 [0, 1, -6] = true := by decide +kernel
theorem subd9_1_156 : subd9_1 [0, 1, -5] = true := by decide +kernel
theorem subd9_1_157 : subd9_1 [0, 1, -4] = true := by decide +kernel
theorem subd9_1_158 : subd9_1 [0, 1, -3] = true := by decide +kernel
theorem subd9_1_159 : subd9_1 [0, 1, -2] = true := by decide +kernel
theorem sbd9_1_4 : ∀ q ∈ blkd9_1_4, subd9_1 q = true := by
  unfold blkd9_1_4
  exact List.forall_mem_cons.2 ⟨subd9_1_128, List.forall_mem_cons.2 ⟨subd9_1_129, List.forall_mem_cons.2 ⟨subd9_1_130, List.forall_mem_cons.2 ⟨subd9_1_131, List.forall_mem_cons.2 ⟨subd9_1_132, List.forall_mem_cons.2 ⟨subd9_1_133, List.forall_mem_cons.2 ⟨subd9_1_134, List.forall_mem_cons.2 ⟨subd9_1_135, List.forall_mem_cons.2 ⟨subd9_1_136, List.forall_mem_cons.2 ⟨subd9_1_137, List.forall_mem_cons.2 ⟨subd9_1_138, List.forall_mem_cons.2 ⟨subd9_1_139, List.forall_mem_cons.2 ⟨subd9_1_140, List.forall_mem_cons.2 ⟨subd9_1_141, List.forall_mem_cons.2 ⟨subd9_1_142, List.forall_mem_cons.2 ⟨subd9_1_143, List.forall_mem_cons.2 ⟨subd9_1_144, List.forall_mem_cons.2 ⟨subd9_1_145, List.forall_mem_cons.2 ⟨subd9_1_146, List.forall_mem_cons.2 ⟨subd9_1_147, List.forall_mem_cons.2 ⟨subd9_1_148, List.forall_mem_cons.2 ⟨subd9_1_149, List.forall_mem_cons.2 ⟨subd9_1_150, List.forall_mem_cons.2 ⟨subd9_1_151, List.forall_mem_cons.2 ⟨subd9_1_152, List.forall_mem_cons.2 ⟨subd9_1_153, List.forall_mem_cons.2 ⟨subd9_1_154, List.forall_mem_cons.2 ⟨subd9_1_155, List.forall_mem_cons.2 ⟨subd9_1_156, List.forall_mem_cons.2 ⟨subd9_1_157, List.forall_mem_cons.2 ⟨subd9_1_158, List.forall_mem_cons.2 ⟨subd9_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_160 : subd9_1 [0, 1, -1] = true := by decide +kernel
theorem subd9_1_161 : subd9_1 [0, 1, 0] = true := by decide +kernel
theorem subd9_1_162 : subd9_1 [0, 1, 1] = true := by decide +kernel
theorem subd9_1_163 : subd9_1 [0, 1, 2] = true := by decide +kernel
theorem subd9_1_164 : subd9_1 [0, 1, 3] = true := by decide +kernel
theorem subd9_1_165 : subd9_1 [0, 1, 4] = true := by decide +kernel
theorem subd9_1_166 : subd9_1 [0, 1, 5] = true := by decide +kernel
theorem subd9_1_167 : subd9_1 [0, 2, -7] = true := by decide +kernel
theorem subd9_1_168 : subd9_1 [0, 2, -6] = true := by decide +kernel
theorem subd9_1_169 : subd9_1 [0, 2, -5] = true := by decide +kernel
theorem subd9_1_170 : subd9_1 [0, 2, -4] = true := by decide +kernel
theorem subd9_1_171 : subd9_1 [0, 2, -3] = true := by decide +kernel
theorem subd9_1_172 : subd9_1 [0, 2, -2] = true := by decide +kernel
theorem subd9_1_173 : subd9_1 [0, 2, -1] = true := by decide +kernel
theorem subd9_1_174 : subd9_1 [0, 2, 0] = true := by decide +kernel
theorem subd9_1_175 : subd9_1 [0, 2, 1] = true := by decide +kernel
theorem subd9_1_176 : subd9_1 [0, 2, 2] = true := by decide +kernel
theorem subd9_1_177 : subd9_1 [0, 2, 3] = true := by decide +kernel
theorem subd9_1_178 : subd9_1 [0, 2, 4] = true := by decide +kernel
theorem subd9_1_179 : subd9_1 [0, 2, 5] = true := by decide +kernel
theorem subd9_1_180 : subd9_1 [0, 3] = true := by decide +kernel
theorem subd9_1_181 : subd9_1 [0, 4] = true := by decide +kernel
theorem subd9_1_182 : subd9_1 [0, 5] = true := by decide +kernel
theorem subd9_1_183 : subd9_1 [0, 6] = true := by decide +kernel
theorem subd9_1_184 : subd9_1 [1, -8] = true := by decide +kernel
theorem subd9_1_185 : subd9_1 [1, -7] = true := by decide +kernel
theorem subd9_1_186 : subd9_1 [1, -6] = true := by decide +kernel
theorem subd9_1_187 : subd9_1 [1, -5] = true := by decide +kernel
theorem subd9_1_188 : subd9_1 [1, -4] = true := by decide +kernel
theorem subd9_1_189 : subd9_1 [1, -3] = true := by decide +kernel
theorem subd9_1_190 : subd9_1 [1, -2] = true := by decide +kernel
theorem subd9_1_191 : subd9_1 [1, -1, -7] = true := by decide +kernel
theorem sbd9_1_5 : ∀ q ∈ blkd9_1_5, subd9_1 q = true := by
  unfold blkd9_1_5
  exact List.forall_mem_cons.2 ⟨subd9_1_160, List.forall_mem_cons.2 ⟨subd9_1_161, List.forall_mem_cons.2 ⟨subd9_1_162, List.forall_mem_cons.2 ⟨subd9_1_163, List.forall_mem_cons.2 ⟨subd9_1_164, List.forall_mem_cons.2 ⟨subd9_1_165, List.forall_mem_cons.2 ⟨subd9_1_166, List.forall_mem_cons.2 ⟨subd9_1_167, List.forall_mem_cons.2 ⟨subd9_1_168, List.forall_mem_cons.2 ⟨subd9_1_169, List.forall_mem_cons.2 ⟨subd9_1_170, List.forall_mem_cons.2 ⟨subd9_1_171, List.forall_mem_cons.2 ⟨subd9_1_172, List.forall_mem_cons.2 ⟨subd9_1_173, List.forall_mem_cons.2 ⟨subd9_1_174, List.forall_mem_cons.2 ⟨subd9_1_175, List.forall_mem_cons.2 ⟨subd9_1_176, List.forall_mem_cons.2 ⟨subd9_1_177, List.forall_mem_cons.2 ⟨subd9_1_178, List.forall_mem_cons.2 ⟨subd9_1_179, List.forall_mem_cons.2 ⟨subd9_1_180, List.forall_mem_cons.2 ⟨subd9_1_181, List.forall_mem_cons.2 ⟨subd9_1_182, List.forall_mem_cons.2 ⟨subd9_1_183, List.forall_mem_cons.2 ⟨subd9_1_184, List.forall_mem_cons.2 ⟨subd9_1_185, List.forall_mem_cons.2 ⟨subd9_1_186, List.forall_mem_cons.2 ⟨subd9_1_187, List.forall_mem_cons.2 ⟨subd9_1_188, List.forall_mem_cons.2 ⟨subd9_1_189, List.forall_mem_cons.2 ⟨subd9_1_190, List.forall_mem_cons.2 ⟨subd9_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_192 : subd9_1 [1, -1, -6] = true := by decide +kernel
theorem subd9_1_193 : subd9_1 [1, -1, -5] = true := by decide +kernel
theorem subd9_1_194 : subd9_1 [1, -1, -4] = true := by decide +kernel
theorem subd9_1_195 : subd9_1 [1, -1, -3] = true := by decide +kernel
theorem subd9_1_196 : subd9_1 [1, -1, -2] = true := by decide +kernel
theorem subd9_1_197 : subd9_1 [1, -1, -1] = true := by decide +kernel
theorem subd9_1_198 : subd9_1 [1, -1, 0] = true := by decide +kernel
theorem subd9_1_199 : subd9_1 [1, -1, 1] = true := by decide +kernel
theorem subd9_1_200 : subd9_1 [1, -1, 2] = true := by decide +kernel
theorem subd9_1_201 : subd9_1 [1, -1, 3] = true := by decide +kernel
theorem subd9_1_202 : subd9_1 [1, -1, 4] = true := by decide +kernel
theorem subd9_1_203 : subd9_1 [1, -1, 5] = true := by decide +kernel
theorem subd9_1_204 : subd9_1 [1, 0, -7] = true := by decide +kernel
theorem subd9_1_205 : subd9_1 [1, 0, -6] = true := by decide +kernel
theorem subd9_1_206 : subd9_1 [1, 0, -5] = true := by decide +kernel
theorem subd9_1_207 : subd9_1 [1, 0, -4] = true := by decide +kernel
theorem subd9_1_208 : subd9_1 [1, 0, -3] = true := by decide +kernel
theorem subd9_1_209 : subd9_1 [1, 0, -2] = true := by decide +kernel
theorem subd9_1_210 : subd9_1 [1, 0, -1] = true := by decide +kernel
theorem subd9_1_211 : subd9_1 [1, 0, 0] = true := by decide +kernel
theorem subd9_1_212 : subd9_1 [1, 0, 1] = true := by decide +kernel
theorem subd9_1_213 : subd9_1 [1, 0, 2] = true := by decide +kernel
theorem subd9_1_214 : subd9_1 [1, 0, 3] = true := by decide +kernel
theorem subd9_1_215 : subd9_1 [1, 0, 4] = true := by decide +kernel
theorem subd9_1_216 : subd9_1 [1, 0, 5] = true := by decide +kernel
theorem subd9_1_217 : subd9_1 [1, 1, -7] = true := by decide +kernel
theorem subd9_1_218 : subd9_1 [1, 1, -6] = true := by decide +kernel
theorem subd9_1_219 : subd9_1 [1, 1, -5] = true := by decide +kernel
theorem subd9_1_220 : subd9_1 [1, 1, -4] = true := by decide +kernel
theorem subd9_1_221 : subd9_1 [1, 1, -3] = true := by decide +kernel
theorem subd9_1_222 : subd9_1 [1, 1, -2] = true := by decide +kernel
theorem subd9_1_223 : subd9_1 [1, 1, -1] = true := by decide +kernel
theorem sbd9_1_6 : ∀ q ∈ blkd9_1_6, subd9_1 q = true := by
  unfold blkd9_1_6
  exact List.forall_mem_cons.2 ⟨subd9_1_192, List.forall_mem_cons.2 ⟨subd9_1_193, List.forall_mem_cons.2 ⟨subd9_1_194, List.forall_mem_cons.2 ⟨subd9_1_195, List.forall_mem_cons.2 ⟨subd9_1_196, List.forall_mem_cons.2 ⟨subd9_1_197, List.forall_mem_cons.2 ⟨subd9_1_198, List.forall_mem_cons.2 ⟨subd9_1_199, List.forall_mem_cons.2 ⟨subd9_1_200, List.forall_mem_cons.2 ⟨subd9_1_201, List.forall_mem_cons.2 ⟨subd9_1_202, List.forall_mem_cons.2 ⟨subd9_1_203, List.forall_mem_cons.2 ⟨subd9_1_204, List.forall_mem_cons.2 ⟨subd9_1_205, List.forall_mem_cons.2 ⟨subd9_1_206, List.forall_mem_cons.2 ⟨subd9_1_207, List.forall_mem_cons.2 ⟨subd9_1_208, List.forall_mem_cons.2 ⟨subd9_1_209, List.forall_mem_cons.2 ⟨subd9_1_210, List.forall_mem_cons.2 ⟨subd9_1_211, List.forall_mem_cons.2 ⟨subd9_1_212, List.forall_mem_cons.2 ⟨subd9_1_213, List.forall_mem_cons.2 ⟨subd9_1_214, List.forall_mem_cons.2 ⟨subd9_1_215, List.forall_mem_cons.2 ⟨subd9_1_216, List.forall_mem_cons.2 ⟨subd9_1_217, List.forall_mem_cons.2 ⟨subd9_1_218, List.forall_mem_cons.2 ⟨subd9_1_219, List.forall_mem_cons.2 ⟨subd9_1_220, List.forall_mem_cons.2 ⟨subd9_1_221, List.forall_mem_cons.2 ⟨subd9_1_222, List.forall_mem_cons.2 ⟨subd9_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_224 : subd9_1 [1, 1, 0] = true := by decide +kernel
theorem subd9_1_225 : subd9_1 [1, 1, 1] = true := by decide +kernel
theorem subd9_1_226 : subd9_1 [1, 1, 2] = true := by decide +kernel
theorem subd9_1_227 : subd9_1 [1, 1, 3] = true := by decide +kernel
theorem subd9_1_228 : subd9_1 [1, 1, 4] = true := by decide +kernel
theorem subd9_1_229 : subd9_1 [1, 1, 5] = true := by decide +kernel
theorem subd9_1_230 : subd9_1 [1, 2] = true := by decide +kernel
theorem subd9_1_231 : subd9_1 [1, 3] = true := by decide +kernel
theorem subd9_1_232 : subd9_1 [1, 4] = true := by decide +kernel
theorem subd9_1_233 : subd9_1 [1, 5] = true := by decide +kernel
theorem subd9_1_234 : subd9_1 [1, 6] = true := by decide +kernel
theorem subd9_1_235 : subd9_1 [2, -8] = true := by decide +kernel
theorem subd9_1_236 : subd9_1 [2, -7] = true := by decide +kernel
theorem subd9_1_237 : subd9_1 [2, -6] = true := by decide +kernel
theorem subd9_1_238 : subd9_1 [2, -5] = true := by decide +kernel
theorem subd9_1_239 : subd9_1 [2, -4] = true := by decide +kernel
theorem subd9_1_240 : subd9_1 [2, -3] = true := by decide +kernel
theorem subd9_1_241 : subd9_1 [2, -2] = true := by decide +kernel
theorem subd9_1_242 : subd9_1 [2, -1, -7] = true := by decide +kernel
theorem subd9_1_243 : subd9_1 [2, -1, -6] = true := by decide +kernel
theorem subd9_1_244 : subd9_1 [2, -1, -5] = true := by decide +kernel
theorem subd9_1_245 : subd9_1 [2, -1, -4] = true := by decide +kernel
theorem subd9_1_246 : subd9_1 [2, -1, -3] = true := by decide +kernel
theorem subd9_1_247 : subd9_1 [2, -1, -2] = true := by decide +kernel
theorem subd9_1_248 : subd9_1 [2, -1, -1] = true := by decide +kernel
theorem subd9_1_249 : subd9_1 [2, -1, 0] = true := by decide +kernel
theorem subd9_1_250 : subd9_1 [2, -1, 1] = true := by decide +kernel
theorem subd9_1_251 : subd9_1 [2, -1, 2] = true := by decide +kernel
theorem subd9_1_252 : subd9_1 [2, -1, 3] = true := by decide +kernel
theorem subd9_1_253 : subd9_1 [2, -1, 4] = true := by decide +kernel
theorem subd9_1_254 : subd9_1 [2, -1, 5] = true := by decide +kernel
theorem subd9_1_255 : subd9_1 [2, 0] = true := by decide +kernel
theorem sbd9_1_7 : ∀ q ∈ blkd9_1_7, subd9_1 q = true := by
  unfold blkd9_1_7
  exact List.forall_mem_cons.2 ⟨subd9_1_224, List.forall_mem_cons.2 ⟨subd9_1_225, List.forall_mem_cons.2 ⟨subd9_1_226, List.forall_mem_cons.2 ⟨subd9_1_227, List.forall_mem_cons.2 ⟨subd9_1_228, List.forall_mem_cons.2 ⟨subd9_1_229, List.forall_mem_cons.2 ⟨subd9_1_230, List.forall_mem_cons.2 ⟨subd9_1_231, List.forall_mem_cons.2 ⟨subd9_1_232, List.forall_mem_cons.2 ⟨subd9_1_233, List.forall_mem_cons.2 ⟨subd9_1_234, List.forall_mem_cons.2 ⟨subd9_1_235, List.forall_mem_cons.2 ⟨subd9_1_236, List.forall_mem_cons.2 ⟨subd9_1_237, List.forall_mem_cons.2 ⟨subd9_1_238, List.forall_mem_cons.2 ⟨subd9_1_239, List.forall_mem_cons.2 ⟨subd9_1_240, List.forall_mem_cons.2 ⟨subd9_1_241, List.forall_mem_cons.2 ⟨subd9_1_242, List.forall_mem_cons.2 ⟨subd9_1_243, List.forall_mem_cons.2 ⟨subd9_1_244, List.forall_mem_cons.2 ⟨subd9_1_245, List.forall_mem_cons.2 ⟨subd9_1_246, List.forall_mem_cons.2 ⟨subd9_1_247, List.forall_mem_cons.2 ⟨subd9_1_248, List.forall_mem_cons.2 ⟨subd9_1_249, List.forall_mem_cons.2 ⟨subd9_1_250, List.forall_mem_cons.2 ⟨subd9_1_251, List.forall_mem_cons.2 ⟨subd9_1_252, List.forall_mem_cons.2 ⟨subd9_1_253, List.forall_mem_cons.2 ⟨subd9_1_254, List.forall_mem_cons.2 ⟨subd9_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_256 : subd9_1 [2, 1] = true := by decide +kernel
theorem subd9_1_257 : subd9_1 [2, 2] = true := by decide +kernel
theorem subd9_1_258 : subd9_1 [2, 3] = true := by decide +kernel
theorem subd9_1_259 : subd9_1 [2, 4] = true := by decide +kernel
theorem subd9_1_260 : subd9_1 [2, 5] = true := by decide +kernel
theorem subd9_1_261 : subd9_1 [3, -8] = true := by decide +kernel
theorem subd9_1_262 : subd9_1 [3, -7] = true := by decide +kernel
theorem subd9_1_263 : subd9_1 [3, -6] = true := by decide +kernel
theorem subd9_1_264 : subd9_1 [3, -5] = true := by decide +kernel
theorem subd9_1_265 : subd9_1 [3, -4] = true := by decide +kernel
theorem subd9_1_266 : subd9_1 [3, -3] = true := by decide +kernel
theorem subd9_1_267 : subd9_1 [3, -2] = true := by decide +kernel
theorem subd9_1_268 : subd9_1 [3, -1] = true := by decide +kernel
theorem subd9_1_269 : subd9_1 [3, 0] = true := by decide +kernel
theorem subd9_1_270 : subd9_1 [3, 1] = true := by decide +kernel
theorem subd9_1_271 : subd9_1 [3, 2] = true := by decide +kernel
theorem subd9_1_272 : subd9_1 [3, 3] = true := by decide +kernel
theorem subd9_1_273 : subd9_1 [3, 4] = true := by decide +kernel
theorem subd9_1_274 : subd9_1 [4, -7] = true := by decide +kernel
theorem subd9_1_275 : subd9_1 [4, -6] = true := by decide +kernel
theorem subd9_1_276 : subd9_1 [4, -5] = true := by decide +kernel
theorem subd9_1_277 : subd9_1 [4, -4] = true := by decide +kernel
theorem subd9_1_278 : subd9_1 [4, -3] = true := by decide +kernel
theorem subd9_1_279 : subd9_1 [4, -2] = true := by decide +kernel
theorem subd9_1_280 : subd9_1 [4, -1] = true := by decide +kernel
theorem subd9_1_281 : subd9_1 [4, 0] = true := by decide +kernel
theorem subd9_1_282 : subd9_1 [4, 1] = true := by decide +kernel
theorem subd9_1_283 : subd9_1 [4, 2] = true := by decide +kernel
theorem subd9_1_284 : subd9_1 [4, 3] = true := by decide +kernel
theorem subd9_1_285 : subd9_1 [5, -6] = true := by decide +kernel
theorem subd9_1_286 : subd9_1 [5, -5] = true := by decide +kernel
theorem subd9_1_287 : subd9_1 [5, -4] = true := by decide +kernel
theorem sbd9_1_8 : ∀ q ∈ blkd9_1_8, subd9_1 q = true := by
  unfold blkd9_1_8
  exact List.forall_mem_cons.2 ⟨subd9_1_256, List.forall_mem_cons.2 ⟨subd9_1_257, List.forall_mem_cons.2 ⟨subd9_1_258, List.forall_mem_cons.2 ⟨subd9_1_259, List.forall_mem_cons.2 ⟨subd9_1_260, List.forall_mem_cons.2 ⟨subd9_1_261, List.forall_mem_cons.2 ⟨subd9_1_262, List.forall_mem_cons.2 ⟨subd9_1_263, List.forall_mem_cons.2 ⟨subd9_1_264, List.forall_mem_cons.2 ⟨subd9_1_265, List.forall_mem_cons.2 ⟨subd9_1_266, List.forall_mem_cons.2 ⟨subd9_1_267, List.forall_mem_cons.2 ⟨subd9_1_268, List.forall_mem_cons.2 ⟨subd9_1_269, List.forall_mem_cons.2 ⟨subd9_1_270, List.forall_mem_cons.2 ⟨subd9_1_271, List.forall_mem_cons.2 ⟨subd9_1_272, List.forall_mem_cons.2 ⟨subd9_1_273, List.forall_mem_cons.2 ⟨subd9_1_274, List.forall_mem_cons.2 ⟨subd9_1_275, List.forall_mem_cons.2 ⟨subd9_1_276, List.forall_mem_cons.2 ⟨subd9_1_277, List.forall_mem_cons.2 ⟨subd9_1_278, List.forall_mem_cons.2 ⟨subd9_1_279, List.forall_mem_cons.2 ⟨subd9_1_280, List.forall_mem_cons.2 ⟨subd9_1_281, List.forall_mem_cons.2 ⟨subd9_1_282, List.forall_mem_cons.2 ⟨subd9_1_283, List.forall_mem_cons.2 ⟨subd9_1_284, List.forall_mem_cons.2 ⟨subd9_1_285, List.forall_mem_cons.2 ⟨subd9_1_286, List.forall_mem_cons.2 ⟨subd9_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_288 : subd9_1 [5, -3] = true := by decide +kernel
theorem subd9_1_289 : subd9_1 [5, -2] = true := by decide +kernel
theorem subd9_1_290 : subd9_1 [5, -1] = true := by decide +kernel
theorem subd9_1_291 : subd9_1 [5, 0] = true := by decide +kernel
theorem subd9_1_292 : subd9_1 [5, 1] = true := by decide +kernel
theorem sbd9_1_9 : ∀ q ∈ blkd9_1_9, subd9_1 q = true := by
  unfold blkd9_1_9
  exact List.forall_mem_cons.2 ⟨subd9_1_288, List.forall_mem_cons.2 ⟨subd9_1_289, List.forall_mem_cons.2 ⟨subd9_1_290, List.forall_mem_cons.2 ⟨subd9_1_291, List.forall_mem_cons.2 ⟨subd9_1_292, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
