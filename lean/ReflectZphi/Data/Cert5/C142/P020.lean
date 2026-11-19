import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_2_96 : subd12_2 [-2, -1, -2] = true := by decide +kernel
theorem subd12_2_97 : subd12_2 [-2, -1, -1] = true := by decide +kernel
theorem subd12_2_98 : subd12_2 [-2, -1, 0] = true := by decide +kernel
theorem subd12_2_99 : subd12_2 [-2, -1, 1] = true := by decide +kernel
theorem subd12_2_100 : subd12_2 [-2, -1, 2] = true := by decide +kernel
theorem subd12_2_101 : subd12_2 [-2, -1, 3] = true := by decide +kernel
theorem subd12_2_102 : subd12_2 [-2, -1, 4] = true := by decide +kernel
theorem subd12_2_103 : subd12_2 [-2, -1, 5] = true := by decide +kernel
theorem subd12_2_104 : subd12_2 [-2, -1, 6] = true := by decide +kernel
theorem subd12_2_105 : subd12_2 [-2, -1, 7] = true := by decide +kernel
theorem subd12_2_106 : subd12_2 [-2, -1, 8] = true := by decide +kernel
theorem subd12_2_107 : subd12_2 [-2, 0, -8] = true := by decide +kernel
theorem subd12_2_108 : subd12_2 [-2, 0, -7] = true := by decide +kernel
theorem subd12_2_109 : subd12_2 [-2, 0, -6] = true := by decide +kernel
theorem subd12_2_110 : subd12_2 [-2, 0, -5] = true := by decide +kernel
theorem subd12_2_111 : subd12_2 [-2, 0, -4] = true := by decide +kernel
theorem subd12_2_112 : subd12_2 [-2, 0, -3] = true := by decide +kernel
theorem subd12_2_113 : subd12_2 [-2, 0, -2] = true := by decide +kernel
theorem subd12_2_114 : subd12_2 [-2, 0, -1] = true := by decide +kernel
theorem subd12_2_115 : subd12_2 [-2, 0, 0] = true := by decide +kernel
theorem subd12_2_116 : subd12_2 [-2, 0, 1] = true := by decide +kernel
theorem subd12_2_117 : subd12_2 [-2, 0, 2] = true := by decide +kernel
theorem subd12_2_118 : subd12_2 [-2, 0, 3] = true := by decide +kernel
theorem subd12_2_119 : subd12_2 [-2, 0, 4] = true := by decide +kernel
theorem subd12_2_120 : subd12_2 [-2, 0, 5] = true := by decide +kernel
theorem subd12_2_121 : subd12_2 [-2, 0, 6] = true := by decide +kernel
theorem subd12_2_122 : subd12_2 [-2, 0, 7] = true := by decide +kernel
theorem subd12_2_123 : subd12_2 [-2, 0, 8] = true := by decide +kernel
theorem subd12_2_124 : subd12_2 [-2, 1, -8] = true := by decide +kernel
theorem subd12_2_125 : subd12_2 [-2, 1, -7] = true := by decide +kernel
theorem subd12_2_126 : subd12_2 [-2, 1, -6] = true := by decide +kernel
theorem subd12_2_127 : subd12_2 [-2, 1, -5] = true := by decide +kernel
theorem sbd12_2_3 : ∀ q ∈ blkd12_2_3, subd12_2 q = true := by
  unfold blkd12_2_3
  exact List.forall_mem_cons.2 ⟨subd12_2_96, List.forall_mem_cons.2 ⟨subd12_2_97, List.forall_mem_cons.2 ⟨subd12_2_98, List.forall_mem_cons.2 ⟨subd12_2_99, List.forall_mem_cons.2 ⟨subd12_2_100, List.forall_mem_cons.2 ⟨subd12_2_101, List.forall_mem_cons.2 ⟨subd12_2_102, List.forall_mem_cons.2 ⟨subd12_2_103, List.forall_mem_cons.2 ⟨subd12_2_104, List.forall_mem_cons.2 ⟨subd12_2_105, List.forall_mem_cons.2 ⟨subd12_2_106, List.forall_mem_cons.2 ⟨subd12_2_107, List.forall_mem_cons.2 ⟨subd12_2_108, List.forall_mem_cons.2 ⟨subd12_2_109, List.forall_mem_cons.2 ⟨subd12_2_110, List.forall_mem_cons.2 ⟨subd12_2_111, List.forall_mem_cons.2 ⟨subd12_2_112, List.forall_mem_cons.2 ⟨subd12_2_113, List.forall_mem_cons.2 ⟨subd12_2_114, List.forall_mem_cons.2 ⟨subd12_2_115, List.forall_mem_cons.2 ⟨subd12_2_116, List.forall_mem_cons.2 ⟨subd12_2_117, List.forall_mem_cons.2 ⟨subd12_2_118, List.forall_mem_cons.2 ⟨subd12_2_119, List.forall_mem_cons.2 ⟨subd12_2_120, List.forall_mem_cons.2 ⟨subd12_2_121, List.forall_mem_cons.2 ⟨subd12_2_122, List.forall_mem_cons.2 ⟨subd12_2_123, List.forall_mem_cons.2 ⟨subd12_2_124, List.forall_mem_cons.2 ⟨subd12_2_125, List.forall_mem_cons.2 ⟨subd12_2_126, List.forall_mem_cons.2 ⟨subd12_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_128 : subd12_2 [-2, 1, -4] = true := by decide +kernel
theorem subd12_2_129 : subd12_2 [-2, 1, -3] = true := by decide +kernel
theorem subd12_2_130 : subd12_2 [-2, 1, -2] = true := by decide +kernel
theorem subd12_2_131 : subd12_2 [-2, 1, -1] = true := by decide +kernel
theorem subd12_2_132 : subd12_2 [-2, 1, 0] = true := by decide +kernel
theorem subd12_2_133 : subd12_2 [-2, 1, 1] = true := by decide +kernel
theorem subd12_2_134 : subd12_2 [-2, 1, 2] = true := by decide +kernel
theorem subd12_2_135 : subd12_2 [-2, 1, 3] = true := by decide +kernel
theorem subd12_2_136 : subd12_2 [-2, 1, 4] = true := by decide +kernel
theorem subd12_2_137 : subd12_2 [-2, 1, 5] = true := by decide +kernel
theorem subd12_2_138 : subd12_2 [-2, 1, 6] = true := by decide +kernel
theorem subd12_2_139 : subd12_2 [-2, 1, 7] = true := by decide +kernel
theorem subd12_2_140 : subd12_2 [-2, 1, 8] = true := by decide +kernel
theorem subd12_2_141 : subd12_2 [-2, 2, -8] = true := by decide +kernel
theorem subd12_2_142 : subd12_2 [-2, 2, -7] = true := by decide +kernel
theorem subd12_2_143 : subd12_2 [-2, 2, -6] = true := by decide +kernel
theorem subd12_2_144 : subd12_2 [-2, 2, -5] = true := by decide +kernel
theorem subd12_2_145 : subd12_2 [-2, 2, -4] = true := by decide +kernel
theorem subd12_2_146 : subd12_2 [-2, 2, -3] = true := by decide +kernel
theorem subd12_2_147 : subd12_2 [-2, 2, -2] = true := by decide +kernel
theorem subd12_2_148 : subd12_2 [-2, 2, -1] = true := by decide +kernel
theorem subd12_2_149 : subd12_2 [-2, 2, 0] = true := by decide +kernel
theorem subd12_2_150 : subd12_2 [-2, 2, 1] = true := by decide +kernel
theorem subd12_2_151 : subd12_2 [-2, 2, 2] = true := by decide +kernel
theorem subd12_2_152 : subd12_2 [-2, 2, 3] = true := by decide +kernel
theorem subd12_2_153 : subd12_2 [-2, 2, 4] = true := by decide +kernel
theorem subd12_2_154 : subd12_2 [-2, 2, 5] = true := by decide +kernel
theorem subd12_2_155 : subd12_2 [-2, 2, 6] = true := by decide +kernel
theorem subd12_2_156 : subd12_2 [-2, 2, 7] = true := by decide +kernel
theorem subd12_2_157 : subd12_2 [-2, 3, -7] = true := by decide +kernel
theorem subd12_2_158 : subd12_2 [-2, 3, -6] = true := by decide +kernel
theorem subd12_2_159 : subd12_2 [-2, 3, -5] = true := by decide +kernel
theorem sbd12_2_4 : ∀ q ∈ blkd12_2_4, subd12_2 q = true := by
  unfold blkd12_2_4
  exact List.forall_mem_cons.2 ⟨subd12_2_128, List.forall_mem_cons.2 ⟨subd12_2_129, List.forall_mem_cons.2 ⟨subd12_2_130, List.forall_mem_cons.2 ⟨subd12_2_131, List.forall_mem_cons.2 ⟨subd12_2_132, List.forall_mem_cons.2 ⟨subd12_2_133, List.forall_mem_cons.2 ⟨subd12_2_134, List.forall_mem_cons.2 ⟨subd12_2_135, List.forall_mem_cons.2 ⟨subd12_2_136, List.forall_mem_cons.2 ⟨subd12_2_137, List.forall_mem_cons.2 ⟨subd12_2_138, List.forall_mem_cons.2 ⟨subd12_2_139, List.forall_mem_cons.2 ⟨subd12_2_140, List.forall_mem_cons.2 ⟨subd12_2_141, List.forall_mem_cons.2 ⟨subd12_2_142, List.forall_mem_cons.2 ⟨subd12_2_143, List.forall_mem_cons.2 ⟨subd12_2_144, List.forall_mem_cons.2 ⟨subd12_2_145, List.forall_mem_cons.2 ⟨subd12_2_146, List.forall_mem_cons.2 ⟨subd12_2_147, List.forall_mem_cons.2 ⟨subd12_2_148, List.forall_mem_cons.2 ⟨subd12_2_149, List.forall_mem_cons.2 ⟨subd12_2_150, List.forall_mem_cons.2 ⟨subd12_2_151, List.forall_mem_cons.2 ⟨subd12_2_152, List.forall_mem_cons.2 ⟨subd12_2_153, List.forall_mem_cons.2 ⟨subd12_2_154, List.forall_mem_cons.2 ⟨subd12_2_155, List.forall_mem_cons.2 ⟨subd12_2_156, List.forall_mem_cons.2 ⟨subd12_2_157, List.forall_mem_cons.2 ⟨subd12_2_158, List.forall_mem_cons.2 ⟨subd12_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_160 : subd12_2 [-2, 3, -4] = true := by decide +kernel
theorem subd12_2_161 : subd12_2 [-2, 3, -3] = true := by decide +kernel
theorem subd12_2_162 : subd12_2 [-2, 3, -2] = true := by decide +kernel
theorem subd12_2_163 : subd12_2 [-2, 3, -1] = true := by decide +kernel
theorem subd12_2_164 : subd12_2 [-2, 3, 0] = true := by decide +kernel
theorem subd12_2_165 : subd12_2 [-2, 3, 1] = true := by decide +kernel
theorem subd12_2_166 : subd12_2 [-2, 3, 2] = true := by decide +kernel
theorem subd12_2_167 : subd12_2 [-2, 3, 3] = true := by decide +kernel
theorem subd12_2_168 : subd12_2 [-2, 3, 4] = true := by decide +kernel
theorem subd12_2_169 : subd12_2 [-2, 3, 5] = true := by decide +kernel
theorem subd12_2_170 : subd12_2 [-2, 4] = true := by decide +kernel
theorem subd12_2_171 : subd12_2 [-1, -5] = true := by decide +kernel
theorem subd12_2_172 : subd12_2 [-1, -4] = true := by decide +kernel
theorem subd12_2_173 : subd12_2 [-1, -3, -6] = true := by decide +kernel
theorem subd12_2_174 : subd12_2 [-1, -3, -5] = true := by decide +kernel
theorem subd12_2_175 : subd12_2 [-1, -3, -4] = true := by decide +kernel
theorem subd12_2_176 : subd12_2 [-1, -3, -3] = true := by decide +kernel
theorem subd12_2_177 : subd12_2 [-1, -3, -2] = true := by decide +kernel
theorem subd12_2_178 : subd12_2 [-1, -3, -1] = true := by decide +kernel
theorem subd12_2_179 : subd12_2 [-1, -3, 0] = true := by decide +kernel
theorem subd12_2_180 : subd12_2 [-1, -3, 1] = true := by decide +kernel
theorem subd12_2_181 : subd12_2 [-1, -3, 2] = true := by decide +kernel
theorem subd12_2_182 : subd12_2 [-1, -3, 3] = true := by decide +kernel
theorem subd12_2_183 : subd12_2 [-1, -3, 4] = true := by decide +kernel
theorem subd12_2_184 : subd12_2 [-1, -3, 5] = true := by decide +kernel
theorem subd12_2_185 : subd12_2 [-1, -3, 6] = true := by decide +kernel
theorem subd12_2_186 : subd12_2 [-1, -3, 7] = true := by decide +kernel
theorem subd12_2_187 : subd12_2 [-1, -3, 8] = true := by decide +kernel
theorem subd12_2_188 : subd12_2 [-1, -2, -7] = true := by decide +kernel
theorem subd12_2_189 : subd12_2 [-1, -2, -6] = true := by decide +kernel
theorem subd12_2_190 : subd12_2 [-1, -2, -5] = true := by decide +kernel
theorem subd12_2_191 : subd12_2 [-1, -2, -4] = true := by decide +kernel
theorem sbd12_2_5 : ∀ q ∈ blkd12_2_5, subd12_2 q = true := by
  unfold blkd12_2_5
  exact List.forall_mem_cons.2 ⟨subd12_2_160, List.forall_mem_cons.2 ⟨subd12_2_161, List.forall_mem_cons.2 ⟨subd12_2_162, List.forall_mem_cons.2 ⟨subd12_2_163, List.forall_mem_cons.2 ⟨subd12_2_164, List.forall_mem_cons.2 ⟨subd12_2_165, List.forall_mem_cons.2 ⟨subd12_2_166, List.forall_mem_cons.2 ⟨subd12_2_167, List.forall_mem_cons.2 ⟨subd12_2_168, List.forall_mem_cons.2 ⟨subd12_2_169, List.forall_mem_cons.2 ⟨subd12_2_170, List.forall_mem_cons.2 ⟨subd12_2_171, List.forall_mem_cons.2 ⟨subd12_2_172, List.forall_mem_cons.2 ⟨subd12_2_173, List.forall_mem_cons.2 ⟨subd12_2_174, List.forall_mem_cons.2 ⟨subd12_2_175, List.forall_mem_cons.2 ⟨subd12_2_176, List.forall_mem_cons.2 ⟨subd12_2_177, List.forall_mem_cons.2 ⟨subd12_2_178, List.forall_mem_cons.2 ⟨subd12_2_179, List.forall_mem_cons.2 ⟨subd12_2_180, List.forall_mem_cons.2 ⟨subd12_2_181, List.forall_mem_cons.2 ⟨subd12_2_182, List.forall_mem_cons.2 ⟨subd12_2_183, List.forall_mem_cons.2 ⟨subd12_2_184, List.forall_mem_cons.2 ⟨subd12_2_185, List.forall_mem_cons.2 ⟨subd12_2_186, List.forall_mem_cons.2 ⟨subd12_2_187, List.forall_mem_cons.2 ⟨subd12_2_188, List.forall_mem_cons.2 ⟨subd12_2_189, List.forall_mem_cons.2 ⟨subd12_2_190, List.forall_mem_cons.2 ⟨subd12_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_192 : subd12_2 [-1, -2, -3] = true := by decide +kernel
theorem subd12_2_193 : subd12_2 [-1, -2, -2] = true := by decide +kernel
theorem subd12_2_194 : subd12_2 [-1, -2, -1] = true := by decide +kernel
theorem subd12_2_195 : subd12_2 [-1, -2, 0] = true := by decide +kernel
theorem subd12_2_196 : subd12_2 [-1, -2, 1] = true := by decide +kernel
theorem subd12_2_197 : subd12_2 [-1, -2, 2] = true := by decide +kernel
theorem subd12_2_198 : subd12_2 [-1, -2, 3] = true := by decide +kernel
theorem subd12_2_199 : subd12_2 [-1, -2, 4] = true := by decide +kernel
theorem subd12_2_200 : subd12_2 [-1, -2, 5] = true := by decide +kernel
theorem subd12_2_201 : subd12_2 [-1, -2, 6] = true := by decide +kernel
theorem subd12_2_202 : subd12_2 [-1, -2, 7] = true := by decide +kernel
theorem subd12_2_203 : subd12_2 [-1, -2, 8] = true := by decide +kernel
theorem subd12_2_204 : subd12_2 [-1, -1, -8] = true := by decide +kernel
theorem subd12_2_205 : subd12_2 [-1, -1, -7] = true := by decide +kernel
theorem subd12_2_206 : subd12_2 [-1, -1, -6] = true := by decide +kernel
theorem subd12_2_207 : subd12_2 [-1, -1, -5] = true := by decide +kernel
theorem subd12_2_208 : subd12_2 [-1, -1, -4] = true := by decide +kernel
theorem subd12_2_209 : subd12_2 [-1, -1, -3] = true := by decide +kernel
theorem subd12_2_210 : subd12_2 [-1, -1, -2] = true := by decide +kernel
theorem subd12_2_211 : subd12_2 [-1, -1, -1] = true := by decide +kernel
theorem subd12_2_212 : subd12_2 [-1, -1, 0] = true := by decide +kernel
theorem subd12_2_213 : subd12_2 [-1, -1, 1] = true := by decide +kernel
theorem subd12_2_214 : subd12_2 [-1, -1, 2] = true := by decide +kernel
theorem subd12_2_215 : subd12_2 [-1, -1, 3] = true := by decide +kernel
theorem subd12_2_216 : subd12_2 [-1, -1, 4] = true := by decide +kernel
theorem subd12_2_217 : subd12_2 [-1, -1, 5] = true := by decide +kernel
theorem subd12_2_218 : subd12_2 [-1, -1, 6] = true := by decide +kernel
theorem subd12_2_219 : subd12_2 [-1, -1, 7] = true := by decide +kernel
theorem subd12_2_220 : subd12_2 [-1, -1, 8] = true := by decide +kernel
theorem subd12_2_221 : subd12_2 [-1, 0, -9] = true := by decide +kernel
theorem subd12_2_222 : subd12_2 [-1, 0, -8] = true := by decide +kernel
theorem subd12_2_223 : subd12_2 [-1, 0, -7] = true := by decide +kernel
theorem sbd12_2_6 : ∀ q ∈ blkd12_2_6, subd12_2 q = true := by
  unfold blkd12_2_6
  exact List.forall_mem_cons.2 ⟨subd12_2_192, List.forall_mem_cons.2 ⟨subd12_2_193, List.forall_mem_cons.2 ⟨subd12_2_194, List.forall_mem_cons.2 ⟨subd12_2_195, List.forall_mem_cons.2 ⟨subd12_2_196, List.forall_mem_cons.2 ⟨subd12_2_197, List.forall_mem_cons.2 ⟨subd12_2_198, List.forall_mem_cons.2 ⟨subd12_2_199, List.forall_mem_cons.2 ⟨subd12_2_200, List.forall_mem_cons.2 ⟨subd12_2_201, List.forall_mem_cons.2 ⟨subd12_2_202, List.forall_mem_cons.2 ⟨subd12_2_203, List.forall_mem_cons.2 ⟨subd12_2_204, List.forall_mem_cons.2 ⟨subd12_2_205, List.forall_mem_cons.2 ⟨subd12_2_206, List.forall_mem_cons.2 ⟨subd12_2_207, List.forall_mem_cons.2 ⟨subd12_2_208, List.forall_mem_cons.2 ⟨subd12_2_209, List.forall_mem_cons.2 ⟨subd12_2_210, List.forall_mem_cons.2 ⟨subd12_2_211, List.forall_mem_cons.2 ⟨subd12_2_212, List.forall_mem_cons.2 ⟨subd12_2_213, List.forall_mem_cons.2 ⟨subd12_2_214, List.forall_mem_cons.2 ⟨subd12_2_215, List.forall_mem_cons.2 ⟨subd12_2_216, List.forall_mem_cons.2 ⟨subd12_2_217, List.forall_mem_cons.2 ⟨subd12_2_218, List.forall_mem_cons.2 ⟨subd12_2_219, List.forall_mem_cons.2 ⟨subd12_2_220, List.forall_mem_cons.2 ⟨subd12_2_221, List.forall_mem_cons.2 ⟨subd12_2_222, List.forall_mem_cons.2 ⟨subd12_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_224 : subd12_2 [-1, 0, -6] = true := by decide +kernel
theorem subd12_2_225 : subd12_2 [-1, 0, -5] = true := by decide +kernel
theorem subd12_2_226 : subd12_2 [-1, 0, -4] = true := by decide +kernel
theorem subd12_2_227 : subd12_2 [-1, 0, -3] = true := by decide +kernel
theorem subd12_2_228 : subd12_2 [-1, 0, -2] = true := by decide +kernel
theorem subd12_2_229 : subd12_2 [-1, 0, -1] = true := by decide +kernel
theorem subd12_2_230 : subd12_2 [-1, 0, 0] = true := by decide +kernel
theorem subd12_2_231 : subd12_2 [-1, 0, 1] = true := by decide +kernel
theorem subd12_2_232 : subd12_2 [-1, 0, 2] = true := by decide +kernel
theorem subd12_2_233 : subd12_2 [-1, 0, 3] = true := by decide +kernel
theorem subd12_2_234 : subd12_2 [-1, 0, 4] = true := by decide +kernel
theorem subd12_2_235 : subd12_2 [-1, 0, 5] = true := by decide +kernel
theorem subd12_2_236 : subd12_2 [-1, 0, 6] = true := by decide +kernel
theorem subd12_2_237 : subd12_2 [-1, 0, 7] = true := by decide +kernel
theorem subd12_2_238 : subd12_2 [-1, 0, 8] = true := by decide +kernel
theorem subd12_2_239 : subd12_2 [-1, 1, -9] = true := by decide +kernel
theorem subd12_2_240 : subd12_2 [-1, 1, -8] = true := by decide +kernel
theorem subd12_2_241 : subd12_2 [-1, 1, -7] = true := by decide +kernel
theorem subd12_2_242 : subd12_2 [-1, 1, -6] = true := by decide +kernel
theorem subd12_2_243 : subd12_2 [-1, 1, -5] = true := by decide +kernel
theorem subd12_2_244 : subd12_2 [-1, 1, -4] = true := by decide +kernel
theorem subd12_2_245 : subd12_2 [-1, 1, -3] = true := by decide +kernel
theorem subd12_2_246 : subd12_2 [-1, 1, -2] = true := by decide +kernel
theorem subd12_2_247 : subd12_2 [-1, 1, -1] = true := by decide +kernel
theorem subd12_2_248 : subd12_2 [-1, 1, 0] = true := by decide +kernel
theorem subd12_2_249 : subd12_2 [-1, 1, 1] = true := by decide +kernel
theorem subd12_2_250 : subd12_2 [-1, 1, 2] = true := by decide +kernel
theorem subd12_2_251 : subd12_2 [-1, 1, 3] = true := by decide +kernel
theorem subd12_2_252 : subd12_2 [-1, 1, 4] = true := by decide +kernel
theorem subd12_2_253 : subd12_2 [-1, 1, 5] = true := by decide +kernel
theorem subd12_2_254 : subd12_2 [-1, 1, 6] = true := by decide +kernel
theorem subd12_2_255 : subd12_2 [-1, 1, 7] = true := by decide +kernel
theorem sbd12_2_7 : ∀ q ∈ blkd12_2_7, subd12_2 q = true := by
  unfold blkd12_2_7
  exact List.forall_mem_cons.2 ⟨subd12_2_224, List.forall_mem_cons.2 ⟨subd12_2_225, List.forall_mem_cons.2 ⟨subd12_2_226, List.forall_mem_cons.2 ⟨subd12_2_227, List.forall_mem_cons.2 ⟨subd12_2_228, List.forall_mem_cons.2 ⟨subd12_2_229, List.forall_mem_cons.2 ⟨subd12_2_230, List.forall_mem_cons.2 ⟨subd12_2_231, List.forall_mem_cons.2 ⟨subd12_2_232, List.forall_mem_cons.2 ⟨subd12_2_233, List.forall_mem_cons.2 ⟨subd12_2_234, List.forall_mem_cons.2 ⟨subd12_2_235, List.forall_mem_cons.2 ⟨subd12_2_236, List.forall_mem_cons.2 ⟨subd12_2_237, List.forall_mem_cons.2 ⟨subd12_2_238, List.forall_mem_cons.2 ⟨subd12_2_239, List.forall_mem_cons.2 ⟨subd12_2_240, List.forall_mem_cons.2 ⟨subd12_2_241, List.forall_mem_cons.2 ⟨subd12_2_242, List.forall_mem_cons.2 ⟨subd12_2_243, List.forall_mem_cons.2 ⟨subd12_2_244, List.forall_mem_cons.2 ⟨subd12_2_245, List.forall_mem_cons.2 ⟨subd12_2_246, List.forall_mem_cons.2 ⟨subd12_2_247, List.forall_mem_cons.2 ⟨subd12_2_248, List.forall_mem_cons.2 ⟨subd12_2_249, List.forall_mem_cons.2 ⟨subd12_2_250, List.forall_mem_cons.2 ⟨subd12_2_251, List.forall_mem_cons.2 ⟨subd12_2_252, List.forall_mem_cons.2 ⟨subd12_2_253, List.forall_mem_cons.2 ⟨subd12_2_254, List.forall_mem_cons.2 ⟨subd12_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_256 : subd12_2 [-1, 1, 8] = true := by decide +kernel
theorem subd12_2_257 : subd12_2 [-1, 2, -9] = true := by decide +kernel
theorem subd12_2_258 : subd12_2 [-1, 2, -8] = true := by decide +kernel
theorem subd12_2_259 : subd12_2 [-1, 2, -7] = true := by decide +kernel
theorem subd12_2_260 : subd12_2 [-1, 2, -6] = true := by decide +kernel
theorem subd12_2_261 : subd12_2 [-1, 2, -5] = true := by decide +kernel
theorem subd12_2_262 : subd12_2 [-1, 2, -4] = true := by decide +kernel
theorem subd12_2_263 : subd12_2 [-1, 2, -3] = true := by decide +kernel
theorem subd12_2_264 : subd12_2 [-1, 2, -2] = true := by decide +kernel
theorem subd12_2_265 : subd12_2 [-1, 2, -1] = true := by decide +kernel
theorem subd12_2_266 : subd12_2 [-1, 2, 0] = true := by decide +kernel
theorem subd12_2_267 : subd12_2 [-1, 2, 1] = true := by decide +kernel
theorem subd12_2_268 : subd12_2 [-1, 2, 2] = true := by decide +kernel
theorem subd12_2_269 : subd12_2 [-1, 2, 3] = true := by decide +kernel
theorem subd12_2_270 : subd12_2 [-1, 2, 4] = true := by decide +kernel
theorem subd12_2_271 : subd12_2 [-1, 2, 5] = true := by decide +kernel
theorem subd12_2_272 : subd12_2 [-1, 2, 6] = true := by decide +kernel
theorem subd12_2_273 : subd12_2 [-1, 2, 7] = true := by decide +kernel
theorem subd12_2_274 : subd12_2 [-1, 3, -8] = true := by decide +kernel
theorem subd12_2_275 : subd12_2 [-1, 3, -7] = true := by decide +kernel
theorem subd12_2_276 : subd12_2 [-1, 3, -6] = true := by decide +kernel
theorem subd12_2_277 : subd12_2 [-1, 3, -5] = true := by decide +kernel
theorem subd12_2_278 : subd12_2 [-1, 3, -4] = true := by decide +kernel
theorem subd12_2_279 : subd12_2 [-1, 3, -3] = true := by decide +kernel
theorem subd12_2_280 : subd12_2 [-1, 3, -2] = true := by decide +kernel
theorem subd12_2_281 : subd12_2 [-1, 3, -1] = true := by decide +kernel
theorem subd12_2_282 : subd12_2 [-1, 3, 0] = true := by decide +kernel
theorem subd12_2_283 : subd12_2 [-1, 3, 1] = true := by decide +kernel
theorem subd12_2_284 : subd12_2 [-1, 3, 2] = true := by decide +kernel
theorem subd12_2_285 : subd12_2 [-1, 3, 3] = true := by decide +kernel
theorem subd12_2_286 : subd12_2 [-1, 3, 4] = true := by decide +kernel
theorem subd12_2_287 : subd12_2 [-1, 3, 5] = true := by decide +kernel
theorem sbd12_2_8 : ∀ q ∈ blkd12_2_8, subd12_2 q = true := by
  unfold blkd12_2_8
  exact List.forall_mem_cons.2 ⟨subd12_2_256, List.forall_mem_cons.2 ⟨subd12_2_257, List.forall_mem_cons.2 ⟨subd12_2_258, List.forall_mem_cons.2 ⟨subd12_2_259, List.forall_mem_cons.2 ⟨subd12_2_260, List.forall_mem_cons.2 ⟨subd12_2_261, List.forall_mem_cons.2 ⟨subd12_2_262, List.forall_mem_cons.2 ⟨subd12_2_263, List.forall_mem_cons.2 ⟨subd12_2_264, List.forall_mem_cons.2 ⟨subd12_2_265, List.forall_mem_cons.2 ⟨subd12_2_266, List.forall_mem_cons.2 ⟨subd12_2_267, List.forall_mem_cons.2 ⟨subd12_2_268, List.forall_mem_cons.2 ⟨subd12_2_269, List.forall_mem_cons.2 ⟨subd12_2_270, List.forall_mem_cons.2 ⟨subd12_2_271, List.forall_mem_cons.2 ⟨subd12_2_272, List.forall_mem_cons.2 ⟨subd12_2_273, List.forall_mem_cons.2 ⟨subd12_2_274, List.forall_mem_cons.2 ⟨subd12_2_275, List.forall_mem_cons.2 ⟨subd12_2_276, List.forall_mem_cons.2 ⟨subd12_2_277, List.forall_mem_cons.2 ⟨subd12_2_278, List.forall_mem_cons.2 ⟨subd12_2_279, List.forall_mem_cons.2 ⟨subd12_2_280, List.forall_mem_cons.2 ⟨subd12_2_281, List.forall_mem_cons.2 ⟨subd12_2_282, List.forall_mem_cons.2 ⟨subd12_2_283, List.forall_mem_cons.2 ⟨subd12_2_284, List.forall_mem_cons.2 ⟨subd12_2_285, List.forall_mem_cons.2 ⟨subd12_2_286, List.forall_mem_cons.2 ⟨subd12_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_288 : subd12_2 [-1, 3, 6] = true := by decide +kernel
theorem subd12_2_289 : subd12_2 [-1, 4] = true := by decide +kernel
theorem subd12_2_290 : subd12_2 [-1, 5] = true := by decide +kernel
theorem subd12_2_291 : subd12_2 [0, -6] = true := by decide +kernel
theorem subd12_2_292 : subd12_2 [0, -5] = true := by decide +kernel
theorem subd12_2_293 : subd12_2 [0, -4] = true := by decide +kernel
theorem subd12_2_294 : subd12_2 [0, -3, -6] = true := by decide +kernel
theorem subd12_2_295 : subd12_2 [0, -3, -5] = true := by decide +kernel
theorem subd12_2_296 : subd12_2 [0, -3, -4] = true := by decide +kernel
theorem subd12_2_297 : subd12_2 [0, -3, -3] = true := by decide +kernel
theorem subd12_2_298 : subd12_2 [0, -3, -2] = true := by decide +kernel
theorem subd12_2_299 : subd12_2 [0, -3, -1] = true := by decide +kernel
theorem subd12_2_300 : subd12_2 [0, -3, 0] = true := by decide +kernel
theorem subd12_2_301 : subd12_2 [0, -3, 1] = true := by decide +kernel
theorem subd12_2_302 : subd12_2 [0, -3, 2] = true := by decide +kernel
theorem subd12_2_303 : subd12_2 [0, -3, 3] = true := by decide +kernel
theorem subd12_2_304 : subd12_2 [0, -3, 4] = true := by decide +kernel
theorem subd12_2_305 : subd12_2 [0, -3, 5] = true := by decide +kernel
theorem subd12_2_306 : subd12_2 [0, -3, 6] = true := by decide +kernel
theorem subd12_2_307 : subd12_2 [0, -3, 7] = true := by decide +kernel
theorem subd12_2_308 : subd12_2 [0, -3, 8] = true := by decide +kernel
theorem subd12_2_309 : subd12_2 [0, -2, -8] = true := by decide +kernel
theorem subd12_2_310 : subd12_2 [0, -2, -7] = true := by decide +kernel
theorem subd12_2_311 : subd12_2 [0, -2, -6] = true := by decide +kernel
theorem subd12_2_312 : subd12_2 [0, -2, -5] = true := by decide +kernel
theorem subd12_2_313 : subd12_2 [0, -2, -4] = true := by decide +kernel
theorem subd12_2_314 : subd12_2 [0, -2, -3] = true := by decide +kernel
theorem subd12_2_315 : subd12_2 [0, -2, -2] = true := by decide +kernel
theorem subd12_2_316 : subd12_2 [0, -2, -1] = true := by decide +kernel
theorem subd12_2_317 : subd12_2 [0, -2, 0] = true := by decide +kernel
theorem subd12_2_318 : subd12_2 [0, -2, 1] = true := by decide +kernel
theorem subd12_2_319 : subd12_2 [0, -2, 2] = true := by decide +kernel
theorem sbd12_2_9 : ∀ q ∈ blkd12_2_9, subd12_2 q = true := by
  unfold blkd12_2_9
  exact List.forall_mem_cons.2 ⟨subd12_2_288, List.forall_mem_cons.2 ⟨subd12_2_289, List.forall_mem_cons.2 ⟨subd12_2_290, List.forall_mem_cons.2 ⟨subd12_2_291, List.forall_mem_cons.2 ⟨subd12_2_292, List.forall_mem_cons.2 ⟨subd12_2_293, List.forall_mem_cons.2 ⟨subd12_2_294, List.forall_mem_cons.2 ⟨subd12_2_295, List.forall_mem_cons.2 ⟨subd12_2_296, List.forall_mem_cons.2 ⟨subd12_2_297, List.forall_mem_cons.2 ⟨subd12_2_298, List.forall_mem_cons.2 ⟨subd12_2_299, List.forall_mem_cons.2 ⟨subd12_2_300, List.forall_mem_cons.2 ⟨subd12_2_301, List.forall_mem_cons.2 ⟨subd12_2_302, List.forall_mem_cons.2 ⟨subd12_2_303, List.forall_mem_cons.2 ⟨subd12_2_304, List.forall_mem_cons.2 ⟨subd12_2_305, List.forall_mem_cons.2 ⟨subd12_2_306, List.forall_mem_cons.2 ⟨subd12_2_307, List.forall_mem_cons.2 ⟨subd12_2_308, List.forall_mem_cons.2 ⟨subd12_2_309, List.forall_mem_cons.2 ⟨subd12_2_310, List.forall_mem_cons.2 ⟨subd12_2_311, List.forall_mem_cons.2 ⟨subd12_2_312, List.forall_mem_cons.2 ⟨subd12_2_313, List.forall_mem_cons.2 ⟨subd12_2_314, List.forall_mem_cons.2 ⟨subd12_2_315, List.forall_mem_cons.2 ⟨subd12_2_316, List.forall_mem_cons.2 ⟨subd12_2_317, List.forall_mem_cons.2 ⟨subd12_2_318, List.forall_mem_cons.2 ⟨subd12_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_320 : subd12_2 [0, -2, 3] = true := by decide +kernel
theorem subd12_2_321 : subd12_2 [0, -2, 4] = true := by decide +kernel
theorem subd12_2_322 : subd12_2 [0, -2, 5] = true := by decide +kernel
theorem subd12_2_323 : subd12_2 [0, -2, 6] = true := by decide +kernel
theorem subd12_2_324 : subd12_2 [0, -2, 7] = true := by decide +kernel
theorem subd12_2_325 : subd12_2 [0, -2, 8] = true := by decide +kernel
theorem subd12_2_326 : subd12_2 [0, -1, -9] = true := by decide +kernel
theorem subd12_2_327 : subd12_2 [0, -1, -8] = true := by decide +kernel
theorem subd12_2_328 : subd12_2 [0, -1, -7] = true := by decide +kernel
theorem subd12_2_329 : subd12_2 [0, -1, -6] = true := by decide +kernel
theorem subd12_2_330 : subd12_2 [0, -1, -5] = true := by decide +kernel
theorem subd12_2_331 : subd12_2 [0, -1, -4] = true := by decide +kernel
theorem subd12_2_332 : subd12_2 [0, -1, -3] = true := by decide +kernel
theorem subd12_2_333 : subd12_2 [0, -1, -2] = true := by decide +kernel
theorem subd12_2_334 : subd12_2 [0, -1, -1] = true := by decide +kernel
theorem subd12_2_335 : subd12_2 [0, -1, 0] = true := by decide +kernel
theorem subd12_2_336 : subd12_2 [0, -1, 1] = true := by decide +kernel
theorem subd12_2_337 : subd12_2 [0, -1, 2] = true := by decide +kernel
theorem subd12_2_338 : subd12_2 [0, -1, 3] = true := by decide +kernel
theorem subd12_2_339 : subd12_2 [0, -1, 4] = true := by decide +kernel
theorem subd12_2_340 : subd12_2 [0, -1, 5] = true := by decide +kernel
theorem subd12_2_341 : subd12_2 [0, -1, 6] = true := by decide +kernel
theorem subd12_2_342 : subd12_2 [0, -1, 7] = true := by decide +kernel
theorem subd12_2_343 : subd12_2 [0, -1, 8] = true := by decide +kernel
theorem subd12_2_344 : subd12_2 [0, 0, -9] = true := by decide +kernel
theorem subd12_2_345 : subd12_2 [0, 0, -8] = true := by decide +kernel
theorem subd12_2_346 : subd12_2 [0, 0, -7] = true := by decide +kernel
theorem subd12_2_347 : subd12_2 [0, 0, -6] = true := by decide +kernel
theorem subd12_2_348 : subd12_2 [0, 0, -5] = true := by decide +kernel
theorem subd12_2_349 : subd12_2 [0, 0, -4] = true := by decide +kernel
theorem subd12_2_350 : subd12_2 [0, 0, -3] = true := by decide +kernel
theorem subd12_2_351 : subd12_2 [0, 0, -2] = true := by decide +kernel
theorem sbd12_2_10 : ∀ q ∈ blkd12_2_10, subd12_2 q = true := by
  unfold blkd12_2_10
  exact List.forall_mem_cons.2 ⟨subd12_2_320, List.forall_mem_cons.2 ⟨subd12_2_321, List.forall_mem_cons.2 ⟨subd12_2_322, List.forall_mem_cons.2 ⟨subd12_2_323, List.forall_mem_cons.2 ⟨subd12_2_324, List.forall_mem_cons.2 ⟨subd12_2_325, List.forall_mem_cons.2 ⟨subd12_2_326, List.forall_mem_cons.2 ⟨subd12_2_327, List.forall_mem_cons.2 ⟨subd12_2_328, List.forall_mem_cons.2 ⟨subd12_2_329, List.forall_mem_cons.2 ⟨subd12_2_330, List.forall_mem_cons.2 ⟨subd12_2_331, List.forall_mem_cons.2 ⟨subd12_2_332, List.forall_mem_cons.2 ⟨subd12_2_333, List.forall_mem_cons.2 ⟨subd12_2_334, List.forall_mem_cons.2 ⟨subd12_2_335, List.forall_mem_cons.2 ⟨subd12_2_336, List.forall_mem_cons.2 ⟨subd12_2_337, List.forall_mem_cons.2 ⟨subd12_2_338, List.forall_mem_cons.2 ⟨subd12_2_339, List.forall_mem_cons.2 ⟨subd12_2_340, List.forall_mem_cons.2 ⟨subd12_2_341, List.forall_mem_cons.2 ⟨subd12_2_342, List.forall_mem_cons.2 ⟨subd12_2_343, List.forall_mem_cons.2 ⟨subd12_2_344, List.forall_mem_cons.2 ⟨subd12_2_345, List.forall_mem_cons.2 ⟨subd12_2_346, List.forall_mem_cons.2 ⟨subd12_2_347, List.forall_mem_cons.2 ⟨subd12_2_348, List.forall_mem_cons.2 ⟨subd12_2_349, List.forall_mem_cons.2 ⟨subd12_2_350, List.forall_mem_cons.2 ⟨subd12_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_352 : subd12_2 [0, 0, -1] = true := by decide +kernel
theorem subd12_2_353 : subd12_2 [0, 0, 0] = true := by decide +kernel
theorem subd12_2_354 : subd12_2 [0, 0, 1] = true := by decide +kernel
theorem subd12_2_355 : subd12_2 [0, 0, 2] = true := by decide +kernel
theorem subd12_2_356 : subd12_2 [0, 0, 3] = true := by decide +kernel
theorem subd12_2_357 : subd12_2 [0, 0, 4] = true := by decide +kernel
theorem subd12_2_358 : subd12_2 [0, 0, 5] = true := by decide +kernel
theorem subd12_2_359 : subd12_2 [0, 0, 6] = true := by decide +kernel
theorem subd12_2_360 : subd12_2 [0, 0, 7] = true := by decide +kernel
theorem subd12_2_361 : subd12_2 [0, 0, 8] = true := by decide +kernel
theorem subd12_2_362 : subd12_2 [0, 1, -9] = true := by decide +kernel
theorem subd12_2_363 : subd12_2 [0, 1, -8] = true := by decide +kernel
theorem subd12_2_364 : subd12_2 [0, 1, -7] = true := by decide +kernel
theorem subd12_2_365 : subd12_2 [0, 1, -6] = true := by decide +kernel
theorem subd12_2_366 : subd12_2 [0, 1, -5] = true := by decide +kernel
theorem subd12_2_367 : subd12_2 [0, 1, -4] = true := by decide +kernel
theorem subd12_2_368 : subd12_2 [0, 1, -3] = true := by decide +kernel
theorem subd12_2_369 : subd12_2 [0, 1, -2] = true := by decide +kernel
theorem subd12_2_370 : subd12_2 [0, 1, -1] = true := by decide +kernel
theorem subd12_2_371 : subd12_2 [0, 1, 0] = true := by decide +kernel
theorem subd12_2_372 : subd12_2 [0, 1, 1] = true := by decide +kernel
theorem subd12_2_373 : subd12_2 [0, 1, 2] = true := by decide +kernel
theorem subd12_2_374 : subd12_2 [0, 1, 3] = true := by decide +kernel
theorem subd12_2_375 : subd12_2 [0, 1, 4] = true := by decide +kernel
theorem subd12_2_376 : subd12_2 [0, 1, 5] = true := by decide +kernel
theorem subd12_2_377 : subd12_2 [0, 1, 6] = true := by decide +kernel
theorem subd12_2_378 : subd12_2 [0, 1, 7] = true := by decide +kernel
theorem subd12_2_379 : subd12_2 [0, 1, 8] = true := by decide +kernel
theorem subd12_2_380 : subd12_2 [0, 2, -9] = true := by decide +kernel
theorem subd12_2_381 : subd12_2 [0, 2, -8] = true := by decide +kernel
theorem subd12_2_382 : subd12_2 [0, 2, -7] = true := by decide +kernel
theorem subd12_2_383 : subd12_2 [0, 2, -6] = true := by decide +kernel
theorem sbd12_2_11 : ∀ q ∈ blkd12_2_11, subd12_2 q = true := by
  unfold blkd12_2_11
  exact List.forall_mem_cons.2 ⟨subd12_2_352, List.forall_mem_cons.2 ⟨subd12_2_353, List.forall_mem_cons.2 ⟨subd12_2_354, List.forall_mem_cons.2 ⟨subd12_2_355, List.forall_mem_cons.2 ⟨subd12_2_356, List.forall_mem_cons.2 ⟨subd12_2_357, List.forall_mem_cons.2 ⟨subd12_2_358, List.forall_mem_cons.2 ⟨subd12_2_359, List.forall_mem_cons.2 ⟨subd12_2_360, List.forall_mem_cons.2 ⟨subd12_2_361, List.forall_mem_cons.2 ⟨subd12_2_362, List.forall_mem_cons.2 ⟨subd12_2_363, List.forall_mem_cons.2 ⟨subd12_2_364, List.forall_mem_cons.2 ⟨subd12_2_365, List.forall_mem_cons.2 ⟨subd12_2_366, List.forall_mem_cons.2 ⟨subd12_2_367, List.forall_mem_cons.2 ⟨subd12_2_368, List.forall_mem_cons.2 ⟨subd12_2_369, List.forall_mem_cons.2 ⟨subd12_2_370, List.forall_mem_cons.2 ⟨subd12_2_371, List.forall_mem_cons.2 ⟨subd12_2_372, List.forall_mem_cons.2 ⟨subd12_2_373, List.forall_mem_cons.2 ⟨subd12_2_374, List.forall_mem_cons.2 ⟨subd12_2_375, List.forall_mem_cons.2 ⟨subd12_2_376, List.forall_mem_cons.2 ⟨subd12_2_377, List.forall_mem_cons.2 ⟨subd12_2_378, List.forall_mem_cons.2 ⟨subd12_2_379, List.forall_mem_cons.2 ⟨subd12_2_380, List.forall_mem_cons.2 ⟨subd12_2_381, List.forall_mem_cons.2 ⟨subd12_2_382, List.forall_mem_cons.2 ⟨subd12_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_384 : subd12_2 [0, 2, -5] = true := by decide +kernel
theorem subd12_2_385 : subd12_2 [0, 2, -4] = true := by decide +kernel
theorem subd12_2_386 : subd12_2 [0, 2, -3] = true := by decide +kernel
theorem subd12_2_387 : subd12_2 [0, 2, -2] = true := by decide +kernel
theorem subd12_2_388 : subd12_2 [0, 2, -1] = true := by decide +kernel
theorem subd12_2_389 : subd12_2 [0, 2, 0] = true := by decide +kernel
theorem subd12_2_390 : subd12_2 [0, 2, 1] = true := by decide +kernel
theorem subd12_2_391 : subd12_2 [0, 2, 2] = true := by decide +kernel
theorem subd12_2_392 : subd12_2 [0, 2, 3] = true := by decide +kernel
theorem subd12_2_393 : subd12_2 [0, 2, 4] = true := by decide +kernel
theorem subd12_2_394 : subd12_2 [0, 2, 5] = true := by decide +kernel
theorem subd12_2_395 : subd12_2 [0, 2, 6] = true := by decide +kernel
theorem subd12_2_396 : subd12_2 [0, 2, 7] = true := by decide +kernel
theorem subd12_2_397 : subd12_2 [0, 3, -9] = true := by decide +kernel
theorem subd12_2_398 : subd12_2 [0, 3, -8] = true := by decide +kernel
theorem subd12_2_399 : subd12_2 [0, 3, -7] = true := by decide +kernel
theorem subd12_2_400 : subd12_2 [0, 3, -6] = true := by decide +kernel
theorem subd12_2_401 : subd12_2 [0, 3, -5] = true := by decide +kernel
theorem subd12_2_402 : subd12_2 [0, 3, -4] = true := by decide +kernel
theorem subd12_2_403 : subd12_2 [0, 3, -3] = true := by decide +kernel
theorem subd12_2_404 : subd12_2 [0, 3, -2] = true := by decide +kernel
theorem subd12_2_405 : subd12_2 [0, 3, -1] = true := by decide +kernel
theorem subd12_2_406 : subd12_2 [0, 3, 0] = true := by decide +kernel
theorem subd12_2_407 : subd12_2 [0, 3, 1] = true := by decide +kernel
theorem subd12_2_408 : subd12_2 [0, 3, 2] = true := by decide +kernel
theorem subd12_2_409 : subd12_2 [0, 3, 3] = true := by decide +kernel
theorem subd12_2_410 : subd12_2 [0, 3, 4] = true := by decide +kernel
theorem subd12_2_411 : subd12_2 [0, 3, 5] = true := by decide +kernel
theorem subd12_2_412 : subd12_2 [0, 4] = true := by decide +kernel
theorem subd12_2_413 : subd12_2 [0, 5] = true := by decide +kernel
theorem subd12_2_414 : subd12_2 [1, -6] = true := by decide +kernel
theorem subd12_2_415 : subd12_2 [1, -5] = true := by decide +kernel
theorem sbd12_2_12 : ∀ q ∈ blkd12_2_12, subd12_2 q = true := by
  unfold blkd12_2_12
  exact List.forall_mem_cons.2 ⟨subd12_2_384, List.forall_mem_cons.2 ⟨subd12_2_385, List.forall_mem_cons.2 ⟨subd12_2_386, List.forall_mem_cons.2 ⟨subd12_2_387, List.forall_mem_cons.2 ⟨subd12_2_388, List.forall_mem_cons.2 ⟨subd12_2_389, List.forall_mem_cons.2 ⟨subd12_2_390, List.forall_mem_cons.2 ⟨subd12_2_391, List.forall_mem_cons.2 ⟨subd12_2_392, List.forall_mem_cons.2 ⟨subd12_2_393, List.forall_mem_cons.2 ⟨subd12_2_394, List.forall_mem_cons.2 ⟨subd12_2_395, List.forall_mem_cons.2 ⟨subd12_2_396, List.forall_mem_cons.2 ⟨subd12_2_397, List.forall_mem_cons.2 ⟨subd12_2_398, List.forall_mem_cons.2 ⟨subd12_2_399, List.forall_mem_cons.2 ⟨subd12_2_400, List.forall_mem_cons.2 ⟨subd12_2_401, List.forall_mem_cons.2 ⟨subd12_2_402, List.forall_mem_cons.2 ⟨subd12_2_403, List.forall_mem_cons.2 ⟨subd12_2_404, List.forall_mem_cons.2 ⟨subd12_2_405, List.forall_mem_cons.2 ⟨subd12_2_406, List.forall_mem_cons.2 ⟨subd12_2_407, List.forall_mem_cons.2 ⟨subd12_2_408, List.forall_mem_cons.2 ⟨subd12_2_409, List.forall_mem_cons.2 ⟨subd12_2_410, List.forall_mem_cons.2 ⟨subd12_2_411, List.forall_mem_cons.2 ⟨subd12_2_412, List.forall_mem_cons.2 ⟨subd12_2_413, List.forall_mem_cons.2 ⟨subd12_2_414, List.forall_mem_cons.2 ⟨subd12_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_416 : subd12_2 [1, -4] = true := by decide +kernel
theorem subd12_2_417 : subd12_2 [1, -3, -7] = true := by decide +kernel
theorem subd12_2_418 : subd12_2 [1, -3, -6] = true := by decide +kernel
theorem subd12_2_419 : subd12_2 [1, -3, -5] = true := by decide +kernel
theorem subd12_2_420 : subd12_2 [1, -3, -4] = true := by decide +kernel
theorem subd12_2_421 : subd12_2 [1, -3, -3] = true := by decide +kernel
theorem subd12_2_422 : subd12_2 [1, -3, -2] = true := by decide +kernel
theorem subd12_2_423 : subd12_2 [1, -3, -1] = true := by decide +kernel
theorem subd12_2_424 : subd12_2 [1, -3, 0] = true := by decide +kernel
theorem subd12_2_425 : subd12_2 [1, -3, 1] = true := by decide +kernel
theorem subd12_2_426 : subd12_2 [1, -3, 2] = true := by decide +kernel
theorem subd12_2_427 : subd12_2 [1, -3, 3] = true := by decide +kernel
theorem subd12_2_428 : subd12_2 [1, -3, 4] = true := by decide +kernel
theorem subd12_2_429 : subd12_2 [1, -3, 5] = true := by decide +kernel
theorem subd12_2_430 : subd12_2 [1, -3, 6] = true := by decide +kernel
theorem subd12_2_431 : subd12_2 [1, -3, 7] = true := by decide +kernel
theorem subd12_2_432 : subd12_2 [1, -2, -8] = true := by decide +kernel
theorem subd12_2_433 : subd12_2 [1, -2, -7] = true := by decide +kernel
theorem subd12_2_434 : subd12_2 [1, -2, -6] = true := by decide +kernel
theorem subd12_2_435 : subd12_2 [1, -2, -5] = true := by decide +kernel
theorem subd12_2_436 : subd12_2 [1, -2, -4] = true := by decide +kernel
theorem subd12_2_437 : subd12_2 [1, -2, -3] = true := by decide +kernel
theorem subd12_2_438 : subd12_2 [1, -2, -2] = true := by decide +kernel
theorem subd12_2_439 : subd12_2 [1, -2, -1] = true := by decide +kernel
theorem subd12_2_440 : subd12_2 [1, -2, 0] = true := by decide +kernel
theorem subd12_2_441 : subd12_2 [1, -2, 1] = true := by decide +kernel
theorem subd12_2_442 : subd12_2 [1, -2, 2] = true := by decide +kernel
theorem subd12_2_443 : subd12_2 [1, -2, 3] = true := by decide +kernel
theorem subd12_2_444 : subd12_2 [1, -2, 4] = true := by decide +kernel
theorem subd12_2_445 : subd12_2 [1, -2, 5] = true := by decide +kernel
theorem subd12_2_446 : subd12_2 [1, -2, 6] = true := by decide +kernel
theorem subd12_2_447 : subd12_2 [1, -2, 7] = true := by decide +kernel
theorem sbd12_2_13 : ∀ q ∈ blkd12_2_13, subd12_2 q = true := by
  unfold blkd12_2_13
  exact List.forall_mem_cons.2 ⟨subd12_2_416, List.forall_mem_cons.2 ⟨subd12_2_417, List.forall_mem_cons.2 ⟨subd12_2_418, List.forall_mem_cons.2 ⟨subd12_2_419, List.forall_mem_cons.2 ⟨subd12_2_420, List.forall_mem_cons.2 ⟨subd12_2_421, List.forall_mem_cons.2 ⟨subd12_2_422, List.forall_mem_cons.2 ⟨subd12_2_423, List.forall_mem_cons.2 ⟨subd12_2_424, List.forall_mem_cons.2 ⟨subd12_2_425, List.forall_mem_cons.2 ⟨subd12_2_426, List.forall_mem_cons.2 ⟨subd12_2_427, List.forall_mem_cons.2 ⟨subd12_2_428, List.forall_mem_cons.2 ⟨subd12_2_429, List.forall_mem_cons.2 ⟨subd12_2_430, List.forall_mem_cons.2 ⟨subd12_2_431, List.forall_mem_cons.2 ⟨subd12_2_432, List.forall_mem_cons.2 ⟨subd12_2_433, List.forall_mem_cons.2 ⟨subd12_2_434, List.forall_mem_cons.2 ⟨subd12_2_435, List.forall_mem_cons.2 ⟨subd12_2_436, List.forall_mem_cons.2 ⟨subd12_2_437, List.forall_mem_cons.2 ⟨subd12_2_438, List.forall_mem_cons.2 ⟨subd12_2_439, List.forall_mem_cons.2 ⟨subd12_2_440, List.forall_mem_cons.2 ⟨subd12_2_441, List.forall_mem_cons.2 ⟨subd12_2_442, List.forall_mem_cons.2 ⟨subd12_2_443, List.forall_mem_cons.2 ⟨subd12_2_444, List.forall_mem_cons.2 ⟨subd12_2_445, List.forall_mem_cons.2 ⟨subd12_2_446, List.forall_mem_cons.2 ⟨subd12_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_448 : subd12_2 [1, -2, 8] = true := by decide +kernel
theorem subd12_2_449 : subd12_2 [1, -1, -9] = true := by decide +kernel
theorem subd12_2_450 : subd12_2 [1, -1, -8] = true := by decide +kernel
theorem subd12_2_451 : subd12_2 [1, -1, -7] = true := by decide +kernel
theorem subd12_2_452 : subd12_2 [1, -1, -6] = true := by decide +kernel
theorem subd12_2_453 : subd12_2 [1, -1, -5] = true := by decide +kernel
theorem subd12_2_454 : subd12_2 [1, -1, -4] = true := by decide +kernel
theorem subd12_2_455 : subd12_2 [1, -1, -3] = true := by decide +kernel
theorem subd12_2_456 : subd12_2 [1, -1, -2] = true := by decide +kernel
theorem subd12_2_457 : subd12_2 [1, -1, -1] = true := by decide +kernel
theorem subd12_2_458 : subd12_2 [1, -1, 0] = true := by decide +kernel
theorem subd12_2_459 : subd12_2 [1, -1, 1] = true := by decide +kernel
theorem subd12_2_460 : subd12_2 [1, -1, 2] = true := by decide +kernel
theorem subd12_2_461 : subd12_2 [1, -1, 3] = true := by decide +kernel
theorem subd12_2_462 : subd12_2 [1, -1, 4] = true := by decide +kernel
theorem subd12_2_463 : subd12_2 [1, -1, 5] = true := by decide +kernel
theorem subd12_2_464 : subd12_2 [1, -1, 6] = true := by decide +kernel
theorem subd12_2_465 : subd12_2 [1, -1, 7] = true := by decide +kernel
theorem subd12_2_466 : subd12_2 [1, -1, 8] = true := by decide +kernel
theorem subd12_2_467 : subd12_2 [1, 0, -9] = true := by decide +kernel
theorem subd12_2_468 : subd12_2 [1, 0, -8] = true := by decide +kernel
theorem subd12_2_469 : subd12_2 [1, 0, -7] = true := by decide +kernel
theorem subd12_2_470 : subd12_2 [1, 0, -6] = true := by decide +kernel
theorem subd12_2_471 : subd12_2 [1, 0, -5] = true := by decide +kernel
theorem subd12_2_472 : subd12_2 [1, 0, -4] = true := by decide +kernel
theorem subd12_2_473 : subd12_2 [1, 0, -3] = true := by decide +kernel
theorem subd12_2_474 : subd12_2 [1, 0, -2] = true := by decide +kernel
theorem subd12_2_475 : subd12_2 [1, 0, -1] = true := by decide +kernel
theorem subd12_2_476 : subd12_2 [1, 0, 0] = true := by decide +kernel
theorem subd12_2_477 : subd12_2 [1, 0, 1] = true := by decide +kernel
theorem subd12_2_478 : subd12_2 [1, 0, 2] = true := by decide +kernel
theorem subd12_2_479 : subd12_2 [1, 0, 3] = true := by decide +kernel
theorem sbd12_2_14 : ∀ q ∈ blkd12_2_14, subd12_2 q = true := by
  unfold blkd12_2_14
  exact List.forall_mem_cons.2 ⟨subd12_2_448, List.forall_mem_cons.2 ⟨subd12_2_449, List.forall_mem_cons.2 ⟨subd12_2_450, List.forall_mem_cons.2 ⟨subd12_2_451, List.forall_mem_cons.2 ⟨subd12_2_452, List.forall_mem_cons.2 ⟨subd12_2_453, List.forall_mem_cons.2 ⟨subd12_2_454, List.forall_mem_cons.2 ⟨subd12_2_455, List.forall_mem_cons.2 ⟨subd12_2_456, List.forall_mem_cons.2 ⟨subd12_2_457, List.forall_mem_cons.2 ⟨subd12_2_458, List.forall_mem_cons.2 ⟨subd12_2_459, List.forall_mem_cons.2 ⟨subd12_2_460, List.forall_mem_cons.2 ⟨subd12_2_461, List.forall_mem_cons.2 ⟨subd12_2_462, List.forall_mem_cons.2 ⟨subd12_2_463, List.forall_mem_cons.2 ⟨subd12_2_464, List.forall_mem_cons.2 ⟨subd12_2_465, List.forall_mem_cons.2 ⟨subd12_2_466, List.forall_mem_cons.2 ⟨subd12_2_467, List.forall_mem_cons.2 ⟨subd12_2_468, List.forall_mem_cons.2 ⟨subd12_2_469, List.forall_mem_cons.2 ⟨subd12_2_470, List.forall_mem_cons.2 ⟨subd12_2_471, List.forall_mem_cons.2 ⟨subd12_2_472, List.forall_mem_cons.2 ⟨subd12_2_473, List.forall_mem_cons.2 ⟨subd12_2_474, List.forall_mem_cons.2 ⟨subd12_2_475, List.forall_mem_cons.2 ⟨subd12_2_476, List.forall_mem_cons.2 ⟨subd12_2_477, List.forall_mem_cons.2 ⟨subd12_2_478, List.forall_mem_cons.2 ⟨subd12_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_480 : subd12_2 [1, 0, 4] = true := by decide +kernel
theorem subd12_2_481 : subd12_2 [1, 0, 5] = true := by decide +kernel
theorem subd12_2_482 : subd12_2 [1, 0, 6] = true := by decide +kernel
theorem subd12_2_483 : subd12_2 [1, 0, 7] = true := by decide +kernel
theorem subd12_2_484 : subd12_2 [1, 0, 8] = true := by decide +kernel
theorem subd12_2_485 : subd12_2 [1, 1, -9] = true := by decide +kernel
theorem subd12_2_486 : subd12_2 [1, 1, -8] = true := by decide +kernel
theorem subd12_2_487 : subd12_2 [1, 1, -7] = true := by decide +kernel
theorem subd12_2_488 : subd12_2 [1, 1, -6] = true := by decide +kernel
theorem subd12_2_489 : subd12_2 [1, 1, -5] = true := by decide +kernel
theorem subd12_2_490 : subd12_2 [1, 1, -4] = true := by decide +kernel
theorem subd12_2_491 : subd12_2 [1, 1, -3] = true := by decide +kernel
theorem subd12_2_492 : subd12_2 [1, 1, -2] = true := by decide +kernel
theorem subd12_2_493 : subd12_2 [1, 1, -1] = true := by decide +kernel
theorem subd12_2_494 : subd12_2 [1, 1, 0] = true := by decide +kernel
theorem subd12_2_495 : subd12_2 [1, 1, 1] = true := by decide +kernel
theorem subd12_2_496 : subd12_2 [1, 1, 2] = true := by decide +kernel
theorem subd12_2_497 : subd12_2 [1, 1, 3] = true := by decide +kernel
theorem subd12_2_498 : subd12_2 [1, 1, 4] = true := by decide +kernel
theorem subd12_2_499 : subd12_2 [1, 1, 5] = true := by decide +kernel
theorem subd12_2_500 : subd12_2 [1, 1, 6] = true := by decide +kernel
theorem subd12_2_501 : subd12_2 [1, 1, 7] = true := by decide +kernel
theorem subd12_2_502 : subd12_2 [1, 2, -9] = true := by decide +kernel
theorem subd12_2_503 : subd12_2 [1, 2, -8] = true := by decide +kernel
theorem subd12_2_504 : subd12_2 [1, 2, -7] = true := by decide +kernel
theorem subd12_2_505 : subd12_2 [1, 2, -6] = true := by decide +kernel
theorem subd12_2_506 : subd12_2 [1, 2, -5] = true := by decide +kernel
theorem subd12_2_507 : subd12_2 [1, 2, -4] = true := by decide +kernel
theorem subd12_2_508 : subd12_2 [1, 2, -3] = true := by decide +kernel
theorem subd12_2_509 : subd12_2 [1, 2, -2] = true := by decide +kernel
theorem subd12_2_510 : subd12_2 [1, 2, -1] = true := by decide +kernel
theorem subd12_2_511 : subd12_2 [1, 2, 0] = true := by decide +kernel
theorem sbd12_2_15 : ∀ q ∈ blkd12_2_15, subd12_2 q = true := by
  unfold blkd12_2_15
  exact List.forall_mem_cons.2 ⟨subd12_2_480, List.forall_mem_cons.2 ⟨subd12_2_481, List.forall_mem_cons.2 ⟨subd12_2_482, List.forall_mem_cons.2 ⟨subd12_2_483, List.forall_mem_cons.2 ⟨subd12_2_484, List.forall_mem_cons.2 ⟨subd12_2_485, List.forall_mem_cons.2 ⟨subd12_2_486, List.forall_mem_cons.2 ⟨subd12_2_487, List.forall_mem_cons.2 ⟨subd12_2_488, List.forall_mem_cons.2 ⟨subd12_2_489, List.forall_mem_cons.2 ⟨subd12_2_490, List.forall_mem_cons.2 ⟨subd12_2_491, List.forall_mem_cons.2 ⟨subd12_2_492, List.forall_mem_cons.2 ⟨subd12_2_493, List.forall_mem_cons.2 ⟨subd12_2_494, List.forall_mem_cons.2 ⟨subd12_2_495, List.forall_mem_cons.2 ⟨subd12_2_496, List.forall_mem_cons.2 ⟨subd12_2_497, List.forall_mem_cons.2 ⟨subd12_2_498, List.forall_mem_cons.2 ⟨subd12_2_499, List.forall_mem_cons.2 ⟨subd12_2_500, List.forall_mem_cons.2 ⟨subd12_2_501, List.forall_mem_cons.2 ⟨subd12_2_502, List.forall_mem_cons.2 ⟨subd12_2_503, List.forall_mem_cons.2 ⟨subd12_2_504, List.forall_mem_cons.2 ⟨subd12_2_505, List.forall_mem_cons.2 ⟨subd12_2_506, List.forall_mem_cons.2 ⟨subd12_2_507, List.forall_mem_cons.2 ⟨subd12_2_508, List.forall_mem_cons.2 ⟨subd12_2_509, List.forall_mem_cons.2 ⟨subd12_2_510, List.forall_mem_cons.2 ⟨subd12_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_512 : subd12_2 [1, 2, 1] = true := by decide +kernel
theorem subd12_2_513 : subd12_2 [1, 2, 2] = true := by decide +kernel
theorem subd12_2_514 : subd12_2 [1, 2, 3] = true := by decide +kernel
theorem subd12_2_515 : subd12_2 [1, 2, 4] = true := by decide +kernel
theorem subd12_2_516 : subd12_2 [1, 2, 5] = true := by decide +kernel
theorem subd12_2_517 : subd12_2 [1, 2, 6] = true := by decide +kernel
theorem subd12_2_518 : subd12_2 [1, 3, -9] = true := by decide +kernel
theorem subd12_2_519 : subd12_2 [1, 3, -8] = true := by decide +kernel
theorem subd12_2_520 : subd12_2 [1, 3, -7] = true := by decide +kernel
theorem subd12_2_521 : subd12_2 [1, 3, -6] = true := by decide +kernel
theorem subd12_2_522 : subd12_2 [1, 3, -5] = true := by decide +kernel
theorem subd12_2_523 : subd12_2 [1, 3, -4] = true := by decide +kernel
theorem subd12_2_524 : subd12_2 [1, 3, -3] = true := by decide +kernel
theorem subd12_2_525 : subd12_2 [1, 3, -2] = true := by decide +kernel
theorem subd12_2_526 : subd12_2 [1, 3, -1] = true := by decide +kernel
theorem subd12_2_527 : subd12_2 [1, 3, 0] = true := by decide +kernel
theorem subd12_2_528 : subd12_2 [1, 3, 1] = true := by decide +kernel
theorem subd12_2_529 : subd12_2 [1, 3, 2] = true := by decide +kernel
theorem subd12_2_530 : subd12_2 [1, 3, 3] = true := by decide +kernel
theorem subd12_2_531 : subd12_2 [1, 3, 4] = true := by decide +kernel
theorem subd12_2_532 : subd12_2 [1, 3, 5] = true := by decide +kernel
theorem subd12_2_533 : subd12_2 [1, 4] = true := by decide +kernel
theorem subd12_2_534 : subd12_2 [2, -5] = true := by decide +kernel
theorem subd12_2_535 : subd12_2 [2, -4] = true := by decide +kernel
theorem subd12_2_536 : subd12_2 [2, -3, -6] = true := by decide +kernel
theorem subd12_2_537 : subd12_2 [2, -3, -5] = true := by decide +kernel
theorem subd12_2_538 : subd12_2 [2, -3, -4] = true := by decide +kernel
theorem subd12_2_539 : subd12_2 [2, -3, -3] = true := by decide +kernel
theorem subd12_2_540 : subd12_2 [2, -3, -2] = true := by decide +kernel
theorem subd12_2_541 : subd12_2 [2, -3, -1] = true := by decide +kernel
theorem subd12_2_542 : subd12_2 [2, -3, 0] = true := by decide +kernel
theorem subd12_2_543 : subd12_2 [2, -3, 1] = true := by decide +kernel
theorem sbd12_2_16 : ∀ q ∈ blkd12_2_16, subd12_2 q = true := by
  unfold blkd12_2_16
  exact List.forall_mem_cons.2 ⟨subd12_2_512, List.forall_mem_cons.2 ⟨subd12_2_513, List.forall_mem_cons.2 ⟨subd12_2_514, List.forall_mem_cons.2 ⟨subd12_2_515, List.forall_mem_cons.2 ⟨subd12_2_516, List.forall_mem_cons.2 ⟨subd12_2_517, List.forall_mem_cons.2 ⟨subd12_2_518, List.forall_mem_cons.2 ⟨subd12_2_519, List.forall_mem_cons.2 ⟨subd12_2_520, List.forall_mem_cons.2 ⟨subd12_2_521, List.forall_mem_cons.2 ⟨subd12_2_522, List.forall_mem_cons.2 ⟨subd12_2_523, List.forall_mem_cons.2 ⟨subd12_2_524, List.forall_mem_cons.2 ⟨subd12_2_525, List.forall_mem_cons.2 ⟨subd12_2_526, List.forall_mem_cons.2 ⟨subd12_2_527, List.forall_mem_cons.2 ⟨subd12_2_528, List.forall_mem_cons.2 ⟨subd12_2_529, List.forall_mem_cons.2 ⟨subd12_2_530, List.forall_mem_cons.2 ⟨subd12_2_531, List.forall_mem_cons.2 ⟨subd12_2_532, List.forall_mem_cons.2 ⟨subd12_2_533, List.forall_mem_cons.2 ⟨subd12_2_534, List.forall_mem_cons.2 ⟨subd12_2_535, List.forall_mem_cons.2 ⟨subd12_2_536, List.forall_mem_cons.2 ⟨subd12_2_537, List.forall_mem_cons.2 ⟨subd12_2_538, List.forall_mem_cons.2 ⟨subd12_2_539, List.forall_mem_cons.2 ⟨subd12_2_540, List.forall_mem_cons.2 ⟨subd12_2_541, List.forall_mem_cons.2 ⟨subd12_2_542, List.forall_mem_cons.2 ⟨subd12_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_544 : subd12_2 [2, -3, 2] = true := by decide +kernel
theorem subd12_2_545 : subd12_2 [2, -3, 3] = true := by decide +kernel
theorem subd12_2_546 : subd12_2 [2, -3, 4] = true := by decide +kernel
theorem subd12_2_547 : subd12_2 [2, -3, 5] = true := by decide +kernel
theorem subd12_2_548 : subd12_2 [2, -3, 6] = true := by decide +kernel
theorem subd12_2_549 : subd12_2 [2, -2, -8] = true := by decide +kernel
theorem subd12_2_550 : subd12_2 [2, -2, -7] = true := by decide +kernel
theorem subd12_2_551 : subd12_2 [2, -2, -6] = true := by decide +kernel
theorem subd12_2_552 : subd12_2 [2, -2, -5] = true := by decide +kernel
theorem subd12_2_553 : subd12_2 [2, -2, -4] = true := by decide +kernel
theorem subd12_2_554 : subd12_2 [2, -2, -3] = true := by decide +kernel
theorem subd12_2_555 : subd12_2 [2, -2, -2] = true := by decide +kernel
theorem subd12_2_556 : subd12_2 [2, -2, -1] = true := by decide +kernel
theorem subd12_2_557 : subd12_2 [2, -2, 0] = true := by decide +kernel
theorem subd12_2_558 : subd12_2 [2, -2, 1] = true := by decide +kernel
theorem subd12_2_559 : subd12_2 [2, -2, 2] = true := by decide +kernel
theorem subd12_2_560 : subd12_2 [2, -2, 3] = true := by decide +kernel
theorem subd12_2_561 : subd12_2 [2, -2, 4] = true := by decide +kernel
theorem subd12_2_562 : subd12_2 [2, -2, 5] = true := by decide +kernel
theorem subd12_2_563 : subd12_2 [2, -2, 6] = true := by decide +kernel
theorem subd12_2_564 : subd12_2 [2, -2, 7] = true := by decide +kernel
theorem subd12_2_565 : subd12_2 [2, -1, -9] = true := by decide +kernel
theorem subd12_2_566 : subd12_2 [2, -1, -8] = true := by decide +kernel
theorem subd12_2_567 : subd12_2 [2, -1, -7] = true := by decide +kernel
theorem subd12_2_568 : subd12_2 [2, -1, -6] = true := by decide +kernel
theorem subd12_2_569 : subd12_2 [2, -1, -5] = true := by decide +kernel
theorem subd12_2_570 : subd12_2 [2, -1, -4] = true := by decide +kernel
theorem subd12_2_571 : subd12_2 [2, -1, -3] = true := by decide +kernel
theorem subd12_2_572 : subd12_2 [2, -1, -2] = true := by decide +kernel
theorem subd12_2_573 : subd12_2 [2, -1, -1] = true := by decide +kernel
theorem subd12_2_574 : subd12_2 [2, -1, 0] = true := by decide +kernel
theorem subd12_2_575 : subd12_2 [2, -1, 1] = true := by decide +kernel
theorem sbd12_2_17 : ∀ q ∈ blkd12_2_17, subd12_2 q = true := by
  unfold blkd12_2_17
  exact List.forall_mem_cons.2 ⟨subd12_2_544, List.forall_mem_cons.2 ⟨subd12_2_545, List.forall_mem_cons.2 ⟨subd12_2_546, List.forall_mem_cons.2 ⟨subd12_2_547, List.forall_mem_cons.2 ⟨subd12_2_548, List.forall_mem_cons.2 ⟨subd12_2_549, List.forall_mem_cons.2 ⟨subd12_2_550, List.forall_mem_cons.2 ⟨subd12_2_551, List.forall_mem_cons.2 ⟨subd12_2_552, List.forall_mem_cons.2 ⟨subd12_2_553, List.forall_mem_cons.2 ⟨subd12_2_554, List.forall_mem_cons.2 ⟨subd12_2_555, List.forall_mem_cons.2 ⟨subd12_2_556, List.forall_mem_cons.2 ⟨subd12_2_557, List.forall_mem_cons.2 ⟨subd12_2_558, List.forall_mem_cons.2 ⟨subd12_2_559, List.forall_mem_cons.2 ⟨subd12_2_560, List.forall_mem_cons.2 ⟨subd12_2_561, List.forall_mem_cons.2 ⟨subd12_2_562, List.forall_mem_cons.2 ⟨subd12_2_563, List.forall_mem_cons.2 ⟨subd12_2_564, List.forall_mem_cons.2 ⟨subd12_2_565, List.forall_mem_cons.2 ⟨subd12_2_566, List.forall_mem_cons.2 ⟨subd12_2_567, List.forall_mem_cons.2 ⟨subd12_2_568, List.forall_mem_cons.2 ⟨subd12_2_569, List.forall_mem_cons.2 ⟨subd12_2_570, List.forall_mem_cons.2 ⟨subd12_2_571, List.forall_mem_cons.2 ⟨subd12_2_572, List.forall_mem_cons.2 ⟨subd12_2_573, List.forall_mem_cons.2 ⟨subd12_2_574, List.forall_mem_cons.2 ⟨subd12_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_576 : subd12_2 [2, -1, 2] = true := by decide +kernel
theorem subd12_2_577 : subd12_2 [2, -1, 3] = true := by decide +kernel
theorem subd12_2_578 : subd12_2 [2, -1, 4] = true := by decide +kernel
theorem subd12_2_579 : subd12_2 [2, -1, 5] = true := by decide +kernel
theorem subd12_2_580 : subd12_2 [2, -1, 6] = true := by decide +kernel
theorem subd12_2_581 : subd12_2 [2, -1, 7] = true := by decide +kernel
theorem subd12_2_582 : subd12_2 [2, 0, -9] = true := by decide +kernel
theorem subd12_2_583 : subd12_2 [2, 0, -8] = true := by decide +kernel
theorem subd12_2_584 : subd12_2 [2, 0, -7] = true := by decide +kernel
theorem subd12_2_585 : subd12_2 [2, 0, -6] = true := by decide +kernel
theorem subd12_2_586 : subd12_2 [2, 0, -5] = true := by decide +kernel
theorem subd12_2_587 : subd12_2 [2, 0, -4] = true := by decide +kernel
theorem subd12_2_588 : subd12_2 [2, 0, -3] = true := by decide +kernel
theorem subd12_2_589 : subd12_2 [2, 0, -2] = true := by decide +kernel
theorem subd12_2_590 : subd12_2 [2, 0, -1] = true := by decide +kernel
theorem subd12_2_591 : subd12_2 [2, 0, 0] = true := by decide +kernel
theorem subd12_2_592 : subd12_2 [2, 0, 1] = true := by decide +kernel
theorem subd12_2_593 : subd12_2 [2, 0, 2] = true := by decide +kernel
theorem subd12_2_594 : subd12_2 [2, 0, 3] = true := by decide +kernel
theorem subd12_2_595 : subd12_2 [2, 0, 4] = true := by decide +kernel
theorem subd12_2_596 : subd12_2 [2, 0, 5] = true := by decide +kernel
theorem subd12_2_597 : subd12_2 [2, 0, 6] = true := by decide +kernel
theorem subd12_2_598 : subd12_2 [2, 0, 7] = true := by decide +kernel
theorem subd12_2_599 : subd12_2 [2, 1, -9] = true := by decide +kernel
theorem subd12_2_600 : subd12_2 [2, 1, -8] = true := by decide +kernel
theorem subd12_2_601 : subd12_2 [2, 1, -7] = true := by decide +kernel
theorem subd12_2_602 : subd12_2 [2, 1, -6] = true := by decide +kernel
theorem subd12_2_603 : subd12_2 [2, 1, -5] = true := by decide +kernel
theorem subd12_2_604 : subd12_2 [2, 1, -4] = true := by decide +kernel
theorem subd12_2_605 : subd12_2 [2, 1, -3] = true := by decide +kernel
theorem subd12_2_606 : subd12_2 [2, 1, -2] = true := by decide +kernel
theorem subd12_2_607 : subd12_2 [2, 1, -1] = true := by decide +kernel
theorem sbd12_2_18 : ∀ q ∈ blkd12_2_18, subd12_2 q = true := by
  unfold blkd12_2_18
  exact List.forall_mem_cons.2 ⟨subd12_2_576, List.forall_mem_cons.2 ⟨subd12_2_577, List.forall_mem_cons.2 ⟨subd12_2_578, List.forall_mem_cons.2 ⟨subd12_2_579, List.forall_mem_cons.2 ⟨subd12_2_580, List.forall_mem_cons.2 ⟨subd12_2_581, List.forall_mem_cons.2 ⟨subd12_2_582, List.forall_mem_cons.2 ⟨subd12_2_583, List.forall_mem_cons.2 ⟨subd12_2_584, List.forall_mem_cons.2 ⟨subd12_2_585, List.forall_mem_cons.2 ⟨subd12_2_586, List.forall_mem_cons.2 ⟨subd12_2_587, List.forall_mem_cons.2 ⟨subd12_2_588, List.forall_mem_cons.2 ⟨subd12_2_589, List.forall_mem_cons.2 ⟨subd12_2_590, List.forall_mem_cons.2 ⟨subd12_2_591, List.forall_mem_cons.2 ⟨subd12_2_592, List.forall_mem_cons.2 ⟨subd12_2_593, List.forall_mem_cons.2 ⟨subd12_2_594, List.forall_mem_cons.2 ⟨subd12_2_595, List.forall_mem_cons.2 ⟨subd12_2_596, List.forall_mem_cons.2 ⟨subd12_2_597, List.forall_mem_cons.2 ⟨subd12_2_598, List.forall_mem_cons.2 ⟨subd12_2_599, List.forall_mem_cons.2 ⟨subd12_2_600, List.forall_mem_cons.2 ⟨subd12_2_601, List.forall_mem_cons.2 ⟨subd12_2_602, List.forall_mem_cons.2 ⟨subd12_2_603, List.forall_mem_cons.2 ⟨subd12_2_604, List.forall_mem_cons.2 ⟨subd12_2_605, List.forall_mem_cons.2 ⟨subd12_2_606, List.forall_mem_cons.2 ⟨subd12_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
