import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_0_96 : subd12_0 [0, -1, -4] = true := by decide +kernel
theorem subd12_0_97 : subd12_0 [0, -1, -3] = true := by decide +kernel
theorem subd12_0_98 : subd12_0 [0, -1, -2] = true := by decide +kernel
theorem subd12_0_99 : subd12_0 [0, -1, -1] = true := by decide +kernel
theorem subd12_0_100 : subd12_0 [0, -1, 0] = true := by decide +kernel
theorem subd12_0_101 : subd12_0 [0, -1, 1] = true := by decide +kernel
theorem subd12_0_102 : subd12_0 [0, -1, 2] = true := by decide +kernel
theorem subd12_0_103 : subd12_0 [0, -1, 3] = true := by decide +kernel
theorem subd12_0_104 : subd12_0 [0, -1, 4] = true := by decide +kernel
theorem subd12_0_105 : subd12_0 [0, -1, 5] = true := by decide +kernel
theorem subd12_0_106 : subd12_0 [0, -1, 6] = true := by decide +kernel
theorem subd12_0_107 : subd12_0 [0, 0, -8] = true := by decide +kernel
theorem subd12_0_108 : subd12_0 [0, 0, -7] = true := by decide +kernel
theorem subd12_0_109 : subd12_0 [0, 0, -6] = true := by decide +kernel
theorem subd12_0_110 : subd12_0 [0, 0, -5] = true := by decide +kernel
theorem subd12_0_111 : subd12_0 [0, 0, -4] = true := by decide +kernel
theorem subd12_0_112 : subd12_0 [0, 0, -3] = true := by decide +kernel
theorem subd12_0_113 : subd12_0 [0, 0, -2] = true := by decide +kernel
theorem subd12_0_114 : subd12_0 [0, 0, -1] = true := by decide +kernel
theorem subd12_0_115 : subd12_0 [0, 0, 0] = true := by decide +kernel
theorem subd12_0_116 : subd12_0 [0, 0, 1] = true := by decide +kernel
theorem subd12_0_117 : subd12_0 [0, 0, 2] = true := by decide +kernel
theorem subd12_0_118 : subd12_0 [0, 0, 3] = true := by decide +kernel
theorem subd12_0_119 : subd12_0 [0, 0, 4] = true := by decide +kernel
theorem subd12_0_120 : subd12_0 [0, 0, 5] = true := by decide +kernel
theorem subd12_0_121 : subd12_0 [0, 0, 6] = true := by decide +kernel
theorem subd12_0_122 : subd12_0 [0, 0, 7] = true := by decide +kernel
theorem subd12_0_123 : subd12_0 [0, 1, -7] = true := by decide +kernel
theorem subd12_0_124 : subd12_0 [0, 1, -6] = true := by decide +kernel
theorem subd12_0_125 : subd12_0 [0, 1, -5] = true := by decide +kernel
theorem subd12_0_126 : subd12_0 [0, 1, -4] = true := by decide +kernel
theorem subd12_0_127 : subd12_0 [0, 1, -3] = true := by decide +kernel
theorem sbd12_0_3 : ∀ q ∈ blkd12_0_3, subd12_0 q = true := by
  unfold blkd12_0_3
  exact List.forall_mem_cons.2 ⟨subd12_0_96, List.forall_mem_cons.2 ⟨subd12_0_97, List.forall_mem_cons.2 ⟨subd12_0_98, List.forall_mem_cons.2 ⟨subd12_0_99, List.forall_mem_cons.2 ⟨subd12_0_100, List.forall_mem_cons.2 ⟨subd12_0_101, List.forall_mem_cons.2 ⟨subd12_0_102, List.forall_mem_cons.2 ⟨subd12_0_103, List.forall_mem_cons.2 ⟨subd12_0_104, List.forall_mem_cons.2 ⟨subd12_0_105, List.forall_mem_cons.2 ⟨subd12_0_106, List.forall_mem_cons.2 ⟨subd12_0_107, List.forall_mem_cons.2 ⟨subd12_0_108, List.forall_mem_cons.2 ⟨subd12_0_109, List.forall_mem_cons.2 ⟨subd12_0_110, List.forall_mem_cons.2 ⟨subd12_0_111, List.forall_mem_cons.2 ⟨subd12_0_112, List.forall_mem_cons.2 ⟨subd12_0_113, List.forall_mem_cons.2 ⟨subd12_0_114, List.forall_mem_cons.2 ⟨subd12_0_115, List.forall_mem_cons.2 ⟨subd12_0_116, List.forall_mem_cons.2 ⟨subd12_0_117, List.forall_mem_cons.2 ⟨subd12_0_118, List.forall_mem_cons.2 ⟨subd12_0_119, List.forall_mem_cons.2 ⟨subd12_0_120, List.forall_mem_cons.2 ⟨subd12_0_121, List.forall_mem_cons.2 ⟨subd12_0_122, List.forall_mem_cons.2 ⟨subd12_0_123, List.forall_mem_cons.2 ⟨subd12_0_124, List.forall_mem_cons.2 ⟨subd12_0_125, List.forall_mem_cons.2 ⟨subd12_0_126, List.forall_mem_cons.2 ⟨subd12_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_128 : subd12_0 [0, 1, -2] = true := by decide +kernel
theorem subd12_0_129 : subd12_0 [0, 1, -1] = true := by decide +kernel
theorem subd12_0_130 : subd12_0 [0, 1, 0] = true := by decide +kernel
theorem subd12_0_131 : subd12_0 [0, 1, 1] = true := by decide +kernel
theorem subd12_0_132 : subd12_0 [0, 1, 2] = true := by decide +kernel
theorem subd12_0_133 : subd12_0 [0, 1, 3] = true := by decide +kernel
theorem subd12_0_134 : subd12_0 [0, 1, 4] = true := by decide +kernel
theorem subd12_0_135 : subd12_0 [0, 1, 5] = true := by decide +kernel
theorem subd12_0_136 : subd12_0 [0, 1, 6] = true := by decide +kernel
theorem subd12_0_137 : subd12_0 [0, 1, 7] = true := by decide +kernel
theorem subd12_0_138 : subd12_0 [0, 2, -6] = true := by decide +kernel
theorem subd12_0_139 : subd12_0 [0, 2, -5] = true := by decide +kernel
theorem subd12_0_140 : subd12_0 [0, 2, -4] = true := by decide +kernel
theorem subd12_0_141 : subd12_0 [0, 2, -3] = true := by decide +kernel
theorem subd12_0_142 : subd12_0 [0, 2, -2] = true := by decide +kernel
theorem subd12_0_143 : subd12_0 [0, 2, -1] = true := by decide +kernel
theorem subd12_0_144 : subd12_0 [0, 2, 0] = true := by decide +kernel
theorem subd12_0_145 : subd12_0 [0, 2, 1] = true := by decide +kernel
theorem subd12_0_146 : subd12_0 [0, 2, 2] = true := by decide +kernel
theorem subd12_0_147 : subd12_0 [0, 2, 3] = true := by decide +kernel
theorem subd12_0_148 : subd12_0 [0, 2, 4] = true := by decide +kernel
theorem subd12_0_149 : subd12_0 [0, 2, 5] = true := by decide +kernel
theorem subd12_0_150 : subd12_0 [0, 2, 6] = true := by decide +kernel
theorem subd12_0_151 : subd12_0 [0, 2, 7] = true := by decide +kernel
theorem subd12_0_152 : subd12_0 [0, 3] = true := by decide +kernel
theorem subd12_0_153 : subd12_0 [0, 4] = true := by decide +kernel
theorem subd12_0_154 : subd12_0 [1, -5] = true := by decide +kernel
theorem subd12_0_155 : subd12_0 [1, -4] = true := by decide +kernel
theorem subd12_0_156 : subd12_0 [1, -3] = true := by decide +kernel
theorem subd12_0_157 : subd12_0 [1, -2, -7] = true := by decide +kernel
theorem subd12_0_158 : subd12_0 [1, -2, -6] = true := by decide +kernel
theorem subd12_0_159 : subd12_0 [1, -2, -5] = true := by decide +kernel
theorem sbd12_0_4 : ∀ q ∈ blkd12_0_4, subd12_0 q = true := by
  unfold blkd12_0_4
  exact List.forall_mem_cons.2 ⟨subd12_0_128, List.forall_mem_cons.2 ⟨subd12_0_129, List.forall_mem_cons.2 ⟨subd12_0_130, List.forall_mem_cons.2 ⟨subd12_0_131, List.forall_mem_cons.2 ⟨subd12_0_132, List.forall_mem_cons.2 ⟨subd12_0_133, List.forall_mem_cons.2 ⟨subd12_0_134, List.forall_mem_cons.2 ⟨subd12_0_135, List.forall_mem_cons.2 ⟨subd12_0_136, List.forall_mem_cons.2 ⟨subd12_0_137, List.forall_mem_cons.2 ⟨subd12_0_138, List.forall_mem_cons.2 ⟨subd12_0_139, List.forall_mem_cons.2 ⟨subd12_0_140, List.forall_mem_cons.2 ⟨subd12_0_141, List.forall_mem_cons.2 ⟨subd12_0_142, List.forall_mem_cons.2 ⟨subd12_0_143, List.forall_mem_cons.2 ⟨subd12_0_144, List.forall_mem_cons.2 ⟨subd12_0_145, List.forall_mem_cons.2 ⟨subd12_0_146, List.forall_mem_cons.2 ⟨subd12_0_147, List.forall_mem_cons.2 ⟨subd12_0_148, List.forall_mem_cons.2 ⟨subd12_0_149, List.forall_mem_cons.2 ⟨subd12_0_150, List.forall_mem_cons.2 ⟨subd12_0_151, List.forall_mem_cons.2 ⟨subd12_0_152, List.forall_mem_cons.2 ⟨subd12_0_153, List.forall_mem_cons.2 ⟨subd12_0_154, List.forall_mem_cons.2 ⟨subd12_0_155, List.forall_mem_cons.2 ⟨subd12_0_156, List.forall_mem_cons.2 ⟨subd12_0_157, List.forall_mem_cons.2 ⟨subd12_0_158, List.forall_mem_cons.2 ⟨subd12_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_160 : subd12_0 [1, -2, -4] = true := by decide +kernel
theorem subd12_0_161 : subd12_0 [1, -2, -3] = true := by decide +kernel
theorem subd12_0_162 : subd12_0 [1, -2, -2] = true := by decide +kernel
theorem subd12_0_163 : subd12_0 [1, -2, -1] = true := by decide +kernel
theorem subd12_0_164 : subd12_0 [1, -2, 0] = true := by decide +kernel
theorem subd12_0_165 : subd12_0 [1, -2, 1] = true := by decide +kernel
theorem subd12_0_166 : subd12_0 [1, -2, 2] = true := by decide +kernel
theorem subd12_0_167 : subd12_0 [1, -2, 3] = true := by decide +kernel
theorem subd12_0_168 : subd12_0 [1, -2, 4] = true := by decide +kernel
theorem subd12_0_169 : subd12_0 [1, -2, 5] = true := by decide +kernel
theorem subd12_0_170 : subd12_0 [1, -1, -7] = true := by decide +kernel
theorem subd12_0_171 : subd12_0 [1, -1, -6] = true := by decide +kernel
theorem subd12_0_172 : subd12_0 [1, -1, -5] = true := by decide +kernel
theorem subd12_0_173 : subd12_0 [1, -1, -4] = true := by decide +kernel
theorem subd12_0_174 : subd12_0 [1, -1, -3] = true := by decide +kernel
theorem subd12_0_175 : subd12_0 [1, -1, -2] = true := by decide +kernel
theorem subd12_0_176 : subd12_0 [1, -1, -1] = true := by decide +kernel
theorem subd12_0_177 : subd12_0 [1, -1, 0] = true := by decide +kernel
theorem subd12_0_178 : subd12_0 [1, -1, 1] = true := by decide +kernel
theorem subd12_0_179 : subd12_0 [1, -1, 2] = true := by decide +kernel
theorem subd12_0_180 : subd12_0 [1, -1, 3] = true := by decide +kernel
theorem subd12_0_181 : subd12_0 [1, -1, 4] = true := by decide +kernel
theorem subd12_0_182 : subd12_0 [1, -1, 5] = true := by decide +kernel
theorem subd12_0_183 : subd12_0 [1, -1, 6] = true := by decide +kernel
theorem subd12_0_184 : subd12_0 [1, 0, -7] = true := by decide +kernel
theorem subd12_0_185 : subd12_0 [1, 0, -6] = true := by decide +kernel
theorem subd12_0_186 : subd12_0 [1, 0, -5] = true := by decide +kernel
theorem subd12_0_187 : subd12_0 [1, 0, -4] = true := by decide +kernel
theorem subd12_0_188 : subd12_0 [1, 0, -3] = true := by decide +kernel
theorem subd12_0_189 : subd12_0 [1, 0, -2] = true := by decide +kernel
theorem subd12_0_190 : subd12_0 [1, 0, -1] = true := by decide +kernel
theorem subd12_0_191 : subd12_0 [1, 0, 0] = true := by decide +kernel
theorem sbd12_0_5 : ∀ q ∈ blkd12_0_5, subd12_0 q = true := by
  unfold blkd12_0_5
  exact List.forall_mem_cons.2 ⟨subd12_0_160, List.forall_mem_cons.2 ⟨subd12_0_161, List.forall_mem_cons.2 ⟨subd12_0_162, List.forall_mem_cons.2 ⟨subd12_0_163, List.forall_mem_cons.2 ⟨subd12_0_164, List.forall_mem_cons.2 ⟨subd12_0_165, List.forall_mem_cons.2 ⟨subd12_0_166, List.forall_mem_cons.2 ⟨subd12_0_167, List.forall_mem_cons.2 ⟨subd12_0_168, List.forall_mem_cons.2 ⟨subd12_0_169, List.forall_mem_cons.2 ⟨subd12_0_170, List.forall_mem_cons.2 ⟨subd12_0_171, List.forall_mem_cons.2 ⟨subd12_0_172, List.forall_mem_cons.2 ⟨subd12_0_173, List.forall_mem_cons.2 ⟨subd12_0_174, List.forall_mem_cons.2 ⟨subd12_0_175, List.forall_mem_cons.2 ⟨subd12_0_176, List.forall_mem_cons.2 ⟨subd12_0_177, List.forall_mem_cons.2 ⟨subd12_0_178, List.forall_mem_cons.2 ⟨subd12_0_179, List.forall_mem_cons.2 ⟨subd12_0_180, List.forall_mem_cons.2 ⟨subd12_0_181, List.forall_mem_cons.2 ⟨subd12_0_182, List.forall_mem_cons.2 ⟨subd12_0_183, List.forall_mem_cons.2 ⟨subd12_0_184, List.forall_mem_cons.2 ⟨subd12_0_185, List.forall_mem_cons.2 ⟨subd12_0_186, List.forall_mem_cons.2 ⟨subd12_0_187, List.forall_mem_cons.2 ⟨subd12_0_188, List.forall_mem_cons.2 ⟨subd12_0_189, List.forall_mem_cons.2 ⟨subd12_0_190, List.forall_mem_cons.2 ⟨subd12_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_192 : subd12_0 [1, 0, 1] = true := by decide +kernel
theorem subd12_0_193 : subd12_0 [1, 0, 2] = true := by decide +kernel
theorem subd12_0_194 : subd12_0 [1, 0, 3] = true := by decide +kernel
theorem subd12_0_195 : subd12_0 [1, 0, 4] = true := by decide +kernel
theorem subd12_0_196 : subd12_0 [1, 0, 5] = true := by decide +kernel
theorem subd12_0_197 : subd12_0 [1, 0, 6] = true := by decide +kernel
theorem subd12_0_198 : subd12_0 [1, 0, 7] = true := by decide +kernel
theorem subd12_0_199 : subd12_0 [1, 1, -6] = true := by decide +kernel
theorem subd12_0_200 : subd12_0 [1, 1, -5] = true := by decide +kernel
theorem subd12_0_201 : subd12_0 [1, 1, -4] = true := by decide +kernel
theorem subd12_0_202 : subd12_0 [1, 1, -3] = true := by decide +kernel
theorem subd12_0_203 : subd12_0 [1, 1, -2] = true := by decide +kernel
theorem subd12_0_204 : subd12_0 [1, 1, -1] = true := by decide +kernel
theorem subd12_0_205 : subd12_0 [1, 1, 0] = true := by decide +kernel
theorem subd12_0_206 : subd12_0 [1, 1, 1] = true := by decide +kernel
theorem subd12_0_207 : subd12_0 [1, 1, 2] = true := by decide +kernel
theorem subd12_0_208 : subd12_0 [1, 1, 3] = true := by decide +kernel
theorem subd12_0_209 : subd12_0 [1, 1, 4] = true := by decide +kernel
theorem subd12_0_210 : subd12_0 [1, 1, 5] = true := by decide +kernel
theorem subd12_0_211 : subd12_0 [1, 1, 6] = true := by decide +kernel
theorem subd12_0_212 : subd12_0 [1, 1, 7] = true := by decide +kernel
theorem subd12_0_213 : subd12_0 [1, 2] = true := by decide +kernel
theorem subd12_0_214 : subd12_0 [1, 3] = true := by decide +kernel
theorem subd12_0_215 : subd12_0 [2, -5] = true := by decide +kernel
theorem subd12_0_216 : subd12_0 [2, -4] = true := by decide +kernel
theorem subd12_0_217 : subd12_0 [2, -3] = true := by decide +kernel
theorem subd12_0_218 : subd12_0 [2, -2] = true := by decide +kernel
theorem subd12_0_219 : subd12_0 [2, -1] = true := by decide +kernel
theorem subd12_0_220 : subd12_0 [2, 0] = true := by decide +kernel
theorem subd12_0_221 : subd12_0 [2, 1] = true := by decide +kernel
theorem subd12_0_222 : subd12_0 [2, 2] = true := by decide +kernel
theorem subd12_0_223 : subd12_0 [3, -4] = true := by decide +kernel
theorem sbd12_0_6 : ∀ q ∈ blkd12_0_6, subd12_0 q = true := by
  unfold blkd12_0_6
  exact List.forall_mem_cons.2 ⟨subd12_0_192, List.forall_mem_cons.2 ⟨subd12_0_193, List.forall_mem_cons.2 ⟨subd12_0_194, List.forall_mem_cons.2 ⟨subd12_0_195, List.forall_mem_cons.2 ⟨subd12_0_196, List.forall_mem_cons.2 ⟨subd12_0_197, List.forall_mem_cons.2 ⟨subd12_0_198, List.forall_mem_cons.2 ⟨subd12_0_199, List.forall_mem_cons.2 ⟨subd12_0_200, List.forall_mem_cons.2 ⟨subd12_0_201, List.forall_mem_cons.2 ⟨subd12_0_202, List.forall_mem_cons.2 ⟨subd12_0_203, List.forall_mem_cons.2 ⟨subd12_0_204, List.forall_mem_cons.2 ⟨subd12_0_205, List.forall_mem_cons.2 ⟨subd12_0_206, List.forall_mem_cons.2 ⟨subd12_0_207, List.forall_mem_cons.2 ⟨subd12_0_208, List.forall_mem_cons.2 ⟨subd12_0_209, List.forall_mem_cons.2 ⟨subd12_0_210, List.forall_mem_cons.2 ⟨subd12_0_211, List.forall_mem_cons.2 ⟨subd12_0_212, List.forall_mem_cons.2 ⟨subd12_0_213, List.forall_mem_cons.2 ⟨subd12_0_214, List.forall_mem_cons.2 ⟨subd12_0_215, List.forall_mem_cons.2 ⟨subd12_0_216, List.forall_mem_cons.2 ⟨subd12_0_217, List.forall_mem_cons.2 ⟨subd12_0_218, List.forall_mem_cons.2 ⟨subd12_0_219, List.forall_mem_cons.2 ⟨subd12_0_220, List.forall_mem_cons.2 ⟨subd12_0_221, List.forall_mem_cons.2 ⟨subd12_0_222, List.forall_mem_cons.2 ⟨subd12_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_224 : subd12_0 [3, -3] = true := by decide +kernel
theorem subd12_0_225 : subd12_0 [3, -2] = true := by decide +kernel
theorem subd12_0_226 : subd12_0 [3, -1] = true := by decide +kernel
theorem subd12_0_227 : subd12_0 [3, 0] = true := by decide +kernel
theorem subd12_0_228 : subd12_0 [3, 1] = true := by decide +kernel
theorem sbd12_0_7 : ∀ q ∈ blkd12_0_7, subd12_0 q = true := by
  unfold blkd12_0_7
  exact List.forall_mem_cons.2 ⟨subd12_0_224, List.forall_mem_cons.2 ⟨subd12_0_225, List.forall_mem_cons.2 ⟨subd12_0_226, List.forall_mem_cons.2 ⟨subd12_0_227, List.forall_mem_cons.2 ⟨subd12_0_228, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [-1, -2] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [-1, -1, -13] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [-1, -1, -12] = true := by decide +kernel
theorem subd12_1_3 : subd12_1 [-1, -1, -11] = true := by decide +kernel
theorem subd12_1_4 : subd12_1 [-1, -1, -10] = true := by decide +kernel
theorem subd12_1_5 : subd12_1 [-1, -1, -9] = true := by decide +kernel
theorem subd12_1_6 : subd12_1 [-1, -1, -8] = true := by decide +kernel
theorem subd12_1_7 : subd12_1 [-1, -1, -7] = true := by decide +kernel
theorem subd12_1_8 : subd12_1 [-1, -1, -6] = true := by decide +kernel
theorem subd12_1_9 : subd12_1 [-1, -1, -5] = true := by decide +kernel
theorem subd12_1_10 : subd12_1 [-1, -1, -4] = true := by decide +kernel
theorem subd12_1_11 : subd12_1 [-1, -1, -3] = true := by decide +kernel
theorem subd12_1_12 : subd12_1 [-1, -1, -2] = true := by decide +kernel
theorem subd12_1_13 : subd12_1 [-1, -1, -1] = true := by decide +kernel
theorem subd12_1_14 : subd12_1 [-1, -1, 0] = true := by decide +kernel
theorem subd12_1_15 : subd12_1 [-1, -1, 1] = true := by decide +kernel
theorem subd12_1_16 : subd12_1 [-1, -1, 2] = true := by decide +kernel
theorem subd12_1_17 : subd12_1 [-1, -1, 3] = true := by decide +kernel
theorem subd12_1_18 : subd12_1 [-1, -1, 4] = true := by decide +kernel
theorem subd12_1_19 : subd12_1 [-1, -1, 5] = true := by decide +kernel
theorem subd12_1_20 : subd12_1 [-1, -1, 6] = true := by decide +kernel
theorem subd12_1_21 : subd12_1 [-1, -1, 7] = true := by decide +kernel
theorem subd12_1_22 : subd12_1 [-1, -1, 8] = true := by decide +kernel
theorem subd12_1_23 : subd12_1 [-1, -1, 9] = true := by decide +kernel
theorem subd12_1_24 : subd12_1 [-1, -1, 10] = true := by decide +kernel
theorem subd12_1_25 : subd12_1 [-1, -1, 11] = true := by decide +kernel
theorem subd12_1_26 : subd12_1 [-1, -1, 12] = true := by decide +kernel
theorem subd12_1_27 : subd12_1 [-1, -1, 13] = true := by decide +kernel
theorem subd12_1_28 : subd12_1 [-1, 0, -14] = true := by decide +kernel
theorem subd12_1_29 : subd12_1 [-1, 0, -13] = true := by decide +kernel
theorem subd12_1_30 : subd12_1 [-1, 0, -12] = true := by decide +kernel
theorem subd12_1_31 : subd12_1 [-1, 0, -11] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_cons.2 ⟨subd12_1_3, List.forall_mem_cons.2 ⟨subd12_1_4, List.forall_mem_cons.2 ⟨subd12_1_5, List.forall_mem_cons.2 ⟨subd12_1_6, List.forall_mem_cons.2 ⟨subd12_1_7, List.forall_mem_cons.2 ⟨subd12_1_8, List.forall_mem_cons.2 ⟨subd12_1_9, List.forall_mem_cons.2 ⟨subd12_1_10, List.forall_mem_cons.2 ⟨subd12_1_11, List.forall_mem_cons.2 ⟨subd12_1_12, List.forall_mem_cons.2 ⟨subd12_1_13, List.forall_mem_cons.2 ⟨subd12_1_14, List.forall_mem_cons.2 ⟨subd12_1_15, List.forall_mem_cons.2 ⟨subd12_1_16, List.forall_mem_cons.2 ⟨subd12_1_17, List.forall_mem_cons.2 ⟨subd12_1_18, List.forall_mem_cons.2 ⟨subd12_1_19, List.forall_mem_cons.2 ⟨subd12_1_20, List.forall_mem_cons.2 ⟨subd12_1_21, List.forall_mem_cons.2 ⟨subd12_1_22, List.forall_mem_cons.2 ⟨subd12_1_23, List.forall_mem_cons.2 ⟨subd12_1_24, List.forall_mem_cons.2 ⟨subd12_1_25, List.forall_mem_cons.2 ⟨subd12_1_26, List.forall_mem_cons.2 ⟨subd12_1_27, List.forall_mem_cons.2 ⟨subd12_1_28, List.forall_mem_cons.2 ⟨subd12_1_29, List.forall_mem_cons.2 ⟨subd12_1_30, List.forall_mem_cons.2 ⟨subd12_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_32 : subd12_1 [-1, 0, -10] = true := by decide +kernel
theorem subd12_1_33 : subd12_1 [-1, 0, -9] = true := by decide +kernel
theorem subd12_1_34 : subd12_1 [-1, 0, -8] = true := by decide +kernel
theorem subd12_1_35 : subd12_1 [-1, 0, -7] = true := by decide +kernel
theorem subd12_1_36 : subd12_1 [-1, 0, -6] = true := by decide +kernel
theorem subd12_1_37 : subd12_1 [-1, 0, -5] = true := by decide +kernel
theorem subd12_1_38 : subd12_1 [-1, 0, -4] = true := by decide +kernel
theorem subd12_1_39 : subd12_1 [-1, 0, -3] = true := by decide +kernel
theorem subd12_1_40 : subd12_1 [-1, 0, -2] = true := by decide +kernel
theorem subd12_1_41 : subd12_1 [-1, 0, -1] = true := by decide +kernel
theorem subd12_1_42 : subd12_1 [-1, 0, 0] = true := by decide +kernel
theorem subd12_1_43 : subd12_1 [-1, 0, 1] = true := by decide +kernel
theorem subd12_1_44 : subd12_1 [-1, 0, 2] = true := by decide +kernel
theorem subd12_1_45 : subd12_1 [-1, 0, 3] = true := by decide +kernel
theorem subd12_1_46 : subd12_1 [-1, 0, 4] = true := by decide +kernel
theorem subd12_1_47 : subd12_1 [-1, 0, 5] = true := by decide +kernel
theorem subd12_1_48 : subd12_1 [-1, 0, 6] = true := by decide +kernel
theorem subd12_1_49 : subd12_1 [-1, 0, 7] = true := by decide +kernel
theorem subd12_1_50 : subd12_1 [-1, 0, 8] = true := by decide +kernel
theorem subd12_1_51 : subd12_1 [-1, 0, 9] = true := by decide +kernel
theorem subd12_1_52 : subd12_1 [-1, 0, 10] = true := by decide +kernel
theorem subd12_1_53 : subd12_1 [-1, 0, 11] = true := by decide +kernel
theorem subd12_1_54 : subd12_1 [-1, 0, 12] = true := by decide +kernel
theorem subd12_1_55 : subd12_1 [-1, 0, 13] = true := by decide +kernel
theorem subd12_1_56 : subd12_1 [0, -2] = true := by decide +kernel
theorem subd12_1_57 : subd12_1 [0, -1, -18] = true := by decide +kernel
theorem subd12_1_58 : subd12_1 [0, -1, -17] = true := by decide +kernel
theorem subd12_1_59 : subd12_1 [0, -1, -16] = true := by decide +kernel
theorem subd12_1_60 : subd12_1 [0, -1, -15] = true := by decide +kernel
theorem subd12_1_61 : subd12_1 [0, -1, -14] = true := by decide +kernel
theorem subd12_1_62 : subd12_1 [0, -1, -13] = true := by decide +kernel
theorem subd12_1_63 : subd12_1 [0, -1, -12] = true := by decide +kernel
theorem sbd12_1_1 : ∀ q ∈ blkd12_1_1, subd12_1 q = true := by
  unfold blkd12_1_1
  exact List.forall_mem_cons.2 ⟨subd12_1_32, List.forall_mem_cons.2 ⟨subd12_1_33, List.forall_mem_cons.2 ⟨subd12_1_34, List.forall_mem_cons.2 ⟨subd12_1_35, List.forall_mem_cons.2 ⟨subd12_1_36, List.forall_mem_cons.2 ⟨subd12_1_37, List.forall_mem_cons.2 ⟨subd12_1_38, List.forall_mem_cons.2 ⟨subd12_1_39, List.forall_mem_cons.2 ⟨subd12_1_40, List.forall_mem_cons.2 ⟨subd12_1_41, List.forall_mem_cons.2 ⟨subd12_1_42, List.forall_mem_cons.2 ⟨subd12_1_43, List.forall_mem_cons.2 ⟨subd12_1_44, List.forall_mem_cons.2 ⟨subd12_1_45, List.forall_mem_cons.2 ⟨subd12_1_46, List.forall_mem_cons.2 ⟨subd12_1_47, List.forall_mem_cons.2 ⟨subd12_1_48, List.forall_mem_cons.2 ⟨subd12_1_49, List.forall_mem_cons.2 ⟨subd12_1_50, List.forall_mem_cons.2 ⟨subd12_1_51, List.forall_mem_cons.2 ⟨subd12_1_52, List.forall_mem_cons.2 ⟨subd12_1_53, List.forall_mem_cons.2 ⟨subd12_1_54, List.forall_mem_cons.2 ⟨subd12_1_55, List.forall_mem_cons.2 ⟨subd12_1_56, List.forall_mem_cons.2 ⟨subd12_1_57, List.forall_mem_cons.2 ⟨subd12_1_58, List.forall_mem_cons.2 ⟨subd12_1_59, List.forall_mem_cons.2 ⟨subd12_1_60, List.forall_mem_cons.2 ⟨subd12_1_61, List.forall_mem_cons.2 ⟨subd12_1_62, List.forall_mem_cons.2 ⟨subd12_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_64 : subd12_1 [0, -1, -11] = true := by decide +kernel
theorem subd12_1_65 : subd12_1 [0, -1, -10] = true := by decide +kernel
theorem subd12_1_66 : subd12_1 [0, -1, -9] = true := by decide +kernel
theorem subd12_1_67 : subd12_1 [0, -1, -8] = true := by decide +kernel
theorem subd12_1_68 : subd12_1 [0, -1, -7] = true := by decide +kernel
theorem subd12_1_69 : subd12_1 [0, -1, -6] = true := by decide +kernel
theorem subd12_1_70 : subd12_1 [0, -1, -5] = true := by decide +kernel
theorem subd12_1_71 : subd12_1 [0, -1, -4] = true := by decide +kernel
theorem subd12_1_72 : subd12_1 [0, -1, -3] = true := by decide +kernel
theorem subd12_1_73 : subd12_1 [0, -1, -2] = true := by decide +kernel
theorem subd12_1_74 : subd12_1 [0, -1, -1] = true := by decide +kernel
theorem subd12_1_75 : subd12_1 [0, -1, 0] = true := by decide +kernel
theorem subd12_1_76 : subd12_1 [0, -1, 1] = true := by decide +kernel
theorem subd12_1_77 : subd12_1 [0, -1, 2] = true := by decide +kernel
theorem subd12_1_78 : subd12_1 [0, -1, 3] = true := by decide +kernel
theorem subd12_1_79 : subd12_1 [0, -1, 4] = true := by decide +kernel
theorem subd12_1_80 : subd12_1 [0, -1, 5] = true := by decide +kernel
theorem subd12_1_81 : subd12_1 [0, -1, 6] = true := by decide +kernel
theorem subd12_1_82 : subd12_1 [0, -1, 7] = true := by decide +kernel
theorem subd12_1_83 : subd12_1 [0, -1, 8] = true := by decide +kernel
theorem subd12_1_84 : subd12_1 [0, -1, 9] = true := by decide +kernel
theorem subd12_1_85 : subd12_1 [0, -1, 10] = true := by decide +kernel
theorem subd12_1_86 : subd12_1 [0, -1, 11] = true := by decide +kernel
theorem subd12_1_87 : subd12_1 [0, -1, 12] = true := by decide +kernel
theorem subd12_1_88 : subd12_1 [0, -1, 13] = true := by decide +kernel
theorem subd12_1_89 : subd12_1 [0, -1, 14] = true := by decide +kernel
theorem subd12_1_90 : subd12_1 [0, -1, 15] = true := by decide +kernel
theorem subd12_1_91 : subd12_1 [0, -1, 16] = true := by decide +kernel
theorem subd12_1_92 : subd12_1 [0, -1, 17] = true := by decide +kernel
theorem subd12_1_93 : subd12_1 [0, 0, -24] = true := by decide +kernel
theorem subd12_1_94 : subd12_1 [0, 0, -23] = true := by decide +kernel
theorem subd12_1_95 : subd12_1 [0, 0, -22] = true := by decide +kernel
theorem sbd12_1_2 : ∀ q ∈ blkd12_1_2, subd12_1 q = true := by
  unfold blkd12_1_2
  exact List.forall_mem_cons.2 ⟨subd12_1_64, List.forall_mem_cons.2 ⟨subd12_1_65, List.forall_mem_cons.2 ⟨subd12_1_66, List.forall_mem_cons.2 ⟨subd12_1_67, List.forall_mem_cons.2 ⟨subd12_1_68, List.forall_mem_cons.2 ⟨subd12_1_69, List.forall_mem_cons.2 ⟨subd12_1_70, List.forall_mem_cons.2 ⟨subd12_1_71, List.forall_mem_cons.2 ⟨subd12_1_72, List.forall_mem_cons.2 ⟨subd12_1_73, List.forall_mem_cons.2 ⟨subd12_1_74, List.forall_mem_cons.2 ⟨subd12_1_75, List.forall_mem_cons.2 ⟨subd12_1_76, List.forall_mem_cons.2 ⟨subd12_1_77, List.forall_mem_cons.2 ⟨subd12_1_78, List.forall_mem_cons.2 ⟨subd12_1_79, List.forall_mem_cons.2 ⟨subd12_1_80, List.forall_mem_cons.2 ⟨subd12_1_81, List.forall_mem_cons.2 ⟨subd12_1_82, List.forall_mem_cons.2 ⟨subd12_1_83, List.forall_mem_cons.2 ⟨subd12_1_84, List.forall_mem_cons.2 ⟨subd12_1_85, List.forall_mem_cons.2 ⟨subd12_1_86, List.forall_mem_cons.2 ⟨subd12_1_87, List.forall_mem_cons.2 ⟨subd12_1_88, List.forall_mem_cons.2 ⟨subd12_1_89, List.forall_mem_cons.2 ⟨subd12_1_90, List.forall_mem_cons.2 ⟨subd12_1_91, List.forall_mem_cons.2 ⟨subd12_1_92, List.forall_mem_cons.2 ⟨subd12_1_93, List.forall_mem_cons.2 ⟨subd12_1_94, List.forall_mem_cons.2 ⟨subd12_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_96 : subd12_1 [0, 0, -21] = true := by decide +kernel
theorem subd12_1_97 : subd12_1 [0, 0, -20] = true := by decide +kernel
theorem subd12_1_98 : subd12_1 [0, 0, -19] = true := by decide +kernel
theorem subd12_1_99 : subd12_1 [0, 0, -18] = true := by decide +kernel
theorem subd12_1_100 : subd12_1 [0, 0, -17] = true := by decide +kernel
theorem subd12_1_101 : subd12_1 [0, 0, -16] = true := by decide +kernel
theorem subd12_1_102 : subd12_1 [0, 0, -15] = true := by decide +kernel
theorem subd12_1_103 : subd12_1 [0, 0, -14] = true := by decide +kernel
theorem subd12_1_104 : subd12_1 [0, 0, -13] = true := by decide +kernel
theorem subd12_1_105 : subd12_1 [0, 0, -12] = true := by decide +kernel
theorem subd12_1_106 : subd12_1 [0, 0, -11] = true := by decide +kernel
theorem subd12_1_107 : subd12_1 [0, 0, -10] = true := by decide +kernel
theorem subd12_1_108 : subd12_1 [0, 0, -9] = true := by decide +kernel
theorem subd12_1_109 : subd12_1 [0, 0, -8] = true := by decide +kernel
theorem subd12_1_110 : subd12_1 [0, 0, -7] = true := by decide +kernel
theorem subd12_1_111 : subd12_1 [0, 0, -6] = true := by decide +kernel
theorem subd12_1_112 : subd12_1 [0, 0, -5] = true := by decide +kernel
theorem subd12_1_113 : subd12_1 [0, 0, -4] = true := by decide +kernel
theorem subd12_1_114 : subd12_1 [0, 0, -3] = true := by decide +kernel
theorem subd12_1_115 : subd12_1 [0, 0, -2] = true := by decide +kernel
theorem subd12_1_116 : subd12_1 [0, 0, -1] = true := by decide +kernel
theorem subd12_1_117 : subd12_1 [0, 0, 0] = true := by decide +kernel
theorem subd12_1_118 : subd12_1 [0, 0, 1] = true := by decide +kernel
theorem subd12_1_119 : subd12_1 [0, 0, 2] = true := by decide +kernel
theorem subd12_1_120 : subd12_1 [0, 0, 3] = true := by decide +kernel
theorem subd12_1_121 : subd12_1 [0, 0, 4] = true := by decide +kernel
theorem subd12_1_122 : subd12_1 [0, 0, 5] = true := by decide +kernel
theorem subd12_1_123 : subd12_1 [0, 0, 6] = true := by decide +kernel
theorem subd12_1_124 : subd12_1 [0, 0, 7] = true := by decide +kernel
theorem subd12_1_125 : subd12_1 [0, 0, 8] = true := by decide +kernel
theorem subd12_1_126 : subd12_1 [0, 0, 9] = true := by decide +kernel
theorem subd12_1_127 : subd12_1 [0, 0, 10] = true := by decide +kernel
theorem sbd12_1_3 : ∀ q ∈ blkd12_1_3, subd12_1 q = true := by
  unfold blkd12_1_3
  exact List.forall_mem_cons.2 ⟨subd12_1_96, List.forall_mem_cons.2 ⟨subd12_1_97, List.forall_mem_cons.2 ⟨subd12_1_98, List.forall_mem_cons.2 ⟨subd12_1_99, List.forall_mem_cons.2 ⟨subd12_1_100, List.forall_mem_cons.2 ⟨subd12_1_101, List.forall_mem_cons.2 ⟨subd12_1_102, List.forall_mem_cons.2 ⟨subd12_1_103, List.forall_mem_cons.2 ⟨subd12_1_104, List.forall_mem_cons.2 ⟨subd12_1_105, List.forall_mem_cons.2 ⟨subd12_1_106, List.forall_mem_cons.2 ⟨subd12_1_107, List.forall_mem_cons.2 ⟨subd12_1_108, List.forall_mem_cons.2 ⟨subd12_1_109, List.forall_mem_cons.2 ⟨subd12_1_110, List.forall_mem_cons.2 ⟨subd12_1_111, List.forall_mem_cons.2 ⟨subd12_1_112, List.forall_mem_cons.2 ⟨subd12_1_113, List.forall_mem_cons.2 ⟨subd12_1_114, List.forall_mem_cons.2 ⟨subd12_1_115, List.forall_mem_cons.2 ⟨subd12_1_116, List.forall_mem_cons.2 ⟨subd12_1_117, List.forall_mem_cons.2 ⟨subd12_1_118, List.forall_mem_cons.2 ⟨subd12_1_119, List.forall_mem_cons.2 ⟨subd12_1_120, List.forall_mem_cons.2 ⟨subd12_1_121, List.forall_mem_cons.2 ⟨subd12_1_122, List.forall_mem_cons.2 ⟨subd12_1_123, List.forall_mem_cons.2 ⟨subd12_1_124, List.forall_mem_cons.2 ⟨subd12_1_125, List.forall_mem_cons.2 ⟨subd12_1_126, List.forall_mem_cons.2 ⟨subd12_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_128 : subd12_1 [0, 0, 11] = true := by decide +kernel
theorem subd12_1_129 : subd12_1 [0, 0, 12] = true := by decide +kernel
theorem subd12_1_130 : subd12_1 [0, 0, 13] = true := by decide +kernel
theorem subd12_1_131 : subd12_1 [0, 0, 14] = true := by decide +kernel
theorem subd12_1_132 : subd12_1 [0, 0, 15] = true := by decide +kernel
theorem subd12_1_133 : subd12_1 [0, 0, 16] = true := by decide +kernel
theorem subd12_1_134 : subd12_1 [0, 0, 17] = true := by decide +kernel
theorem subd12_1_135 : subd12_1 [0, 0, 18] = true := by decide +kernel
theorem subd12_1_136 : subd12_1 [0, 0, 19] = true := by decide +kernel
theorem subd12_1_137 : subd12_1 [0, 0, 20] = true := by decide +kernel
theorem subd12_1_138 : subd12_1 [0, 0, 21] = true := by decide +kernel
theorem subd12_1_139 : subd12_1 [0, 0, 22] = true := by decide +kernel
theorem subd12_1_140 : subd12_1 [0, 0, 23] = true := by decide +kernel
theorem subd12_1_141 : subd12_1 [0, 1, -18] = true := by decide +kernel
theorem subd12_1_142 : subd12_1 [0, 1, -17] = true := by decide +kernel
theorem subd12_1_143 : subd12_1 [0, 1, -16] = true := by decide +kernel
theorem subd12_1_144 : subd12_1 [0, 1, -15] = true := by decide +kernel
theorem subd12_1_145 : subd12_1 [0, 1, -14] = true := by decide +kernel
theorem subd12_1_146 : subd12_1 [0, 1, -13] = true := by decide +kernel
theorem subd12_1_147 : subd12_1 [0, 1, -12] = true := by decide +kernel
theorem subd12_1_148 : subd12_1 [0, 1, -11] = true := by decide +kernel
theorem subd12_1_149 : subd12_1 [0, 1, -10] = true := by decide +kernel
theorem subd12_1_150 : subd12_1 [0, 1, -9] = true := by decide +kernel
theorem subd12_1_151 : subd12_1 [0, 1, -8] = true := by decide +kernel
theorem subd12_1_152 : subd12_1 [0, 1, -7] = true := by decide +kernel
theorem subd12_1_153 : subd12_1 [0, 1, -6] = true := by decide +kernel
theorem subd12_1_154 : subd12_1 [0, 1, -5] = true := by decide +kernel
theorem subd12_1_155 : subd12_1 [0, 1, -4] = true := by decide +kernel
theorem subd12_1_156 : subd12_1 [0, 1, -3] = true := by decide +kernel
theorem subd12_1_157 : subd12_1 [0, 1, -2] = true := by decide +kernel
theorem subd12_1_158 : subd12_1 [0, 1, -1] = true := by decide +kernel
theorem subd12_1_159 : subd12_1 [0, 1, 0] = true := by decide +kernel
theorem sbd12_1_4 : ∀ q ∈ blkd12_1_4, subd12_1 q = true := by
  unfold blkd12_1_4
  exact List.forall_mem_cons.2 ⟨subd12_1_128, List.forall_mem_cons.2 ⟨subd12_1_129, List.forall_mem_cons.2 ⟨subd12_1_130, List.forall_mem_cons.2 ⟨subd12_1_131, List.forall_mem_cons.2 ⟨subd12_1_132, List.forall_mem_cons.2 ⟨subd12_1_133, List.forall_mem_cons.2 ⟨subd12_1_134, List.forall_mem_cons.2 ⟨subd12_1_135, List.forall_mem_cons.2 ⟨subd12_1_136, List.forall_mem_cons.2 ⟨subd12_1_137, List.forall_mem_cons.2 ⟨subd12_1_138, List.forall_mem_cons.2 ⟨subd12_1_139, List.forall_mem_cons.2 ⟨subd12_1_140, List.forall_mem_cons.2 ⟨subd12_1_141, List.forall_mem_cons.2 ⟨subd12_1_142, List.forall_mem_cons.2 ⟨subd12_1_143, List.forall_mem_cons.2 ⟨subd12_1_144, List.forall_mem_cons.2 ⟨subd12_1_145, List.forall_mem_cons.2 ⟨subd12_1_146, List.forall_mem_cons.2 ⟨subd12_1_147, List.forall_mem_cons.2 ⟨subd12_1_148, List.forall_mem_cons.2 ⟨subd12_1_149, List.forall_mem_cons.2 ⟨subd12_1_150, List.forall_mem_cons.2 ⟨subd12_1_151, List.forall_mem_cons.2 ⟨subd12_1_152, List.forall_mem_cons.2 ⟨subd12_1_153, List.forall_mem_cons.2 ⟨subd12_1_154, List.forall_mem_cons.2 ⟨subd12_1_155, List.forall_mem_cons.2 ⟨subd12_1_156, List.forall_mem_cons.2 ⟨subd12_1_157, List.forall_mem_cons.2 ⟨subd12_1_158, List.forall_mem_cons.2 ⟨subd12_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
