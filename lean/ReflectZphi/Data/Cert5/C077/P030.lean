import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_1_128 : subd12_1 [1, -7] = true := by decide +kernel
theorem subd12_1_129 : subd12_1 [1, -6] = true := by decide +kernel
theorem subd12_1_130 : subd12_1 [1, -5] = true := by decide +kernel
theorem subd12_1_131 : subd12_1 [1, -4] = true := by decide +kernel
theorem subd12_1_132 : subd12_1 [1, -3] = true := by decide +kernel
theorem subd12_1_133 : subd12_1 [1, -2] = true := by decide +kernel
theorem subd12_1_134 : subd12_1 [1, -1] = true := by decide +kernel
theorem subd12_1_135 : subd12_1 [1, 0] = true := by decide +kernel
theorem subd12_1_136 : subd12_1 [1, 1] = true := by decide +kernel
theorem subd12_1_137 : subd12_1 [1, 2] = true := by decide +kernel
theorem subd12_1_138 : subd12_1 [1, 3] = true := by decide +kernel
theorem subd12_1_139 : subd12_1 [1, 4] = true := by decide +kernel
theorem subd12_1_140 : subd12_1 [1, 5] = true := by decide +kernel
theorem subd12_1_141 : subd12_1 [1, 6] = true := by decide +kernel
theorem subd12_1_142 : subd12_1 [1, 7] = true := by decide +kernel
theorem subd12_1_143 : subd12_1 [1, 8] = true := by decide +kernel
theorem subd12_1_144 : subd12_1 [2, -9] = true := by decide +kernel
theorem subd12_1_145 : subd12_1 [2, -8] = true := by decide +kernel
theorem subd12_1_146 : subd12_1 [2, -7] = true := by decide +kernel
theorem subd12_1_147 : subd12_1 [2, -6] = true := by decide +kernel
theorem subd12_1_148 : subd12_1 [2, -5] = true := by decide +kernel
theorem subd12_1_149 : subd12_1 [2, -4] = true := by decide +kernel
theorem subd12_1_150 : subd12_1 [2, -3] = true := by decide +kernel
theorem subd12_1_151 : subd12_1 [2, -2] = true := by decide +kernel
theorem subd12_1_152 : subd12_1 [2, -1] = true := by decide +kernel
theorem subd12_1_153 : subd12_1 [2, 0] = true := by decide +kernel
theorem subd12_1_154 : subd12_1 [2, 1] = true := by decide +kernel
theorem subd12_1_155 : subd12_1 [2, 2] = true := by decide +kernel
theorem subd12_1_156 : subd12_1 [2, 3] = true := by decide +kernel
theorem subd12_1_157 : subd12_1 [2, 4] = true := by decide +kernel
theorem subd12_1_158 : subd12_1 [2, 5] = true := by decide +kernel
theorem subd12_1_159 : subd12_1 [2, 6] = true := by decide +kernel
theorem sbd12_1_4 : ∀ q ∈ blkd12_1_4, subd12_1 q = true := by
  unfold blkd12_1_4
  exact List.forall_mem_cons.2 ⟨subd12_1_128, List.forall_mem_cons.2 ⟨subd12_1_129, List.forall_mem_cons.2 ⟨subd12_1_130, List.forall_mem_cons.2 ⟨subd12_1_131, List.forall_mem_cons.2 ⟨subd12_1_132, List.forall_mem_cons.2 ⟨subd12_1_133, List.forall_mem_cons.2 ⟨subd12_1_134, List.forall_mem_cons.2 ⟨subd12_1_135, List.forall_mem_cons.2 ⟨subd12_1_136, List.forall_mem_cons.2 ⟨subd12_1_137, List.forall_mem_cons.2 ⟨subd12_1_138, List.forall_mem_cons.2 ⟨subd12_1_139, List.forall_mem_cons.2 ⟨subd12_1_140, List.forall_mem_cons.2 ⟨subd12_1_141, List.forall_mem_cons.2 ⟨subd12_1_142, List.forall_mem_cons.2 ⟨subd12_1_143, List.forall_mem_cons.2 ⟨subd12_1_144, List.forall_mem_cons.2 ⟨subd12_1_145, List.forall_mem_cons.2 ⟨subd12_1_146, List.forall_mem_cons.2 ⟨subd12_1_147, List.forall_mem_cons.2 ⟨subd12_1_148, List.forall_mem_cons.2 ⟨subd12_1_149, List.forall_mem_cons.2 ⟨subd12_1_150, List.forall_mem_cons.2 ⟨subd12_1_151, List.forall_mem_cons.2 ⟨subd12_1_152, List.forall_mem_cons.2 ⟨subd12_1_153, List.forall_mem_cons.2 ⟨subd12_1_154, List.forall_mem_cons.2 ⟨subd12_1_155, List.forall_mem_cons.2 ⟨subd12_1_156, List.forall_mem_cons.2 ⟨subd12_1_157, List.forall_mem_cons.2 ⟨subd12_1_158, List.forall_mem_cons.2 ⟨subd12_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_160 : subd12_1 [2, 7] = true := by decide +kernel
theorem subd12_1_161 : subd12_1 [3, -10] = true := by decide +kernel
theorem subd12_1_162 : subd12_1 [3, -9] = true := by decide +kernel
theorem subd12_1_163 : subd12_1 [3, -8] = true := by decide +kernel
theorem subd12_1_164 : subd12_1 [3, -7] = true := by decide +kernel
theorem subd12_1_165 : subd12_1 [3, -6] = true := by decide +kernel
theorem subd12_1_166 : subd12_1 [3, -5] = true := by decide +kernel
theorem subd12_1_167 : subd12_1 [3, -4] = true := by decide +kernel
theorem subd12_1_168 : subd12_1 [3, -3] = true := by decide +kernel
theorem subd12_1_169 : subd12_1 [3, -2] = true := by decide +kernel
theorem subd12_1_170 : subd12_1 [3, -1] = true := by decide +kernel
theorem subd12_1_171 : subd12_1 [3, 0] = true := by decide +kernel
theorem subd12_1_172 : subd12_1 [3, 1] = true := by decide +kernel
theorem subd12_1_173 : subd12_1 [3, 2] = true := by decide +kernel
theorem subd12_1_174 : subd12_1 [3, 3] = true := by decide +kernel
theorem subd12_1_175 : subd12_1 [3, 4] = true := by decide +kernel
theorem subd12_1_176 : subd12_1 [3, 5] = true := by decide +kernel
theorem subd12_1_177 : subd12_1 [3, 6] = true := by decide +kernel
theorem subd12_1_178 : subd12_1 [4, -9] = true := by decide +kernel
theorem subd12_1_179 : subd12_1 [4, -8] = true := by decide +kernel
theorem subd12_1_180 : subd12_1 [4, -7] = true := by decide +kernel
theorem subd12_1_181 : subd12_1 [4, -6] = true := by decide +kernel
theorem subd12_1_182 : subd12_1 [4, -5] = true := by decide +kernel
theorem subd12_1_183 : subd12_1 [4, -4] = true := by decide +kernel
theorem subd12_1_184 : subd12_1 [4, -3] = true := by decide +kernel
theorem subd12_1_185 : subd12_1 [4, -2] = true := by decide +kernel
theorem subd12_1_186 : subd12_1 [4, -1] = true := by decide +kernel
theorem subd12_1_187 : subd12_1 [4, 0] = true := by decide +kernel
theorem subd12_1_188 : subd12_1 [4, 1] = true := by decide +kernel
theorem subd12_1_189 : subd12_1 [4, 2] = true := by decide +kernel
theorem subd12_1_190 : subd12_1 [4, 3] = true := by decide +kernel
theorem subd12_1_191 : subd12_1 [4, 4] = true := by decide +kernel
theorem sbd12_1_5 : ∀ q ∈ blkd12_1_5, subd12_1 q = true := by
  unfold blkd12_1_5
  exact List.forall_mem_cons.2 ⟨subd12_1_160, List.forall_mem_cons.2 ⟨subd12_1_161, List.forall_mem_cons.2 ⟨subd12_1_162, List.forall_mem_cons.2 ⟨subd12_1_163, List.forall_mem_cons.2 ⟨subd12_1_164, List.forall_mem_cons.2 ⟨subd12_1_165, List.forall_mem_cons.2 ⟨subd12_1_166, List.forall_mem_cons.2 ⟨subd12_1_167, List.forall_mem_cons.2 ⟨subd12_1_168, List.forall_mem_cons.2 ⟨subd12_1_169, List.forall_mem_cons.2 ⟨subd12_1_170, List.forall_mem_cons.2 ⟨subd12_1_171, List.forall_mem_cons.2 ⟨subd12_1_172, List.forall_mem_cons.2 ⟨subd12_1_173, List.forall_mem_cons.2 ⟨subd12_1_174, List.forall_mem_cons.2 ⟨subd12_1_175, List.forall_mem_cons.2 ⟨subd12_1_176, List.forall_mem_cons.2 ⟨subd12_1_177, List.forall_mem_cons.2 ⟨subd12_1_178, List.forall_mem_cons.2 ⟨subd12_1_179, List.forall_mem_cons.2 ⟨subd12_1_180, List.forall_mem_cons.2 ⟨subd12_1_181, List.forall_mem_cons.2 ⟨subd12_1_182, List.forall_mem_cons.2 ⟨subd12_1_183, List.forall_mem_cons.2 ⟨subd12_1_184, List.forall_mem_cons.2 ⟨subd12_1_185, List.forall_mem_cons.2 ⟨subd12_1_186, List.forall_mem_cons.2 ⟨subd12_1_187, List.forall_mem_cons.2 ⟨subd12_1_188, List.forall_mem_cons.2 ⟨subd12_1_189, List.forall_mem_cons.2 ⟨subd12_1_190, List.forall_mem_cons.2 ⟨subd12_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_192 : subd12_1 [4, 5] = true := by decide +kernel
theorem subd12_1_193 : subd12_1 [4, 6] = true := by decide +kernel
theorem subd12_1_194 : subd12_1 [5, -9] = true := by decide +kernel
theorem subd12_1_195 : subd12_1 [5, -8] = true := by decide +kernel
theorem subd12_1_196 : subd12_1 [5, -7] = true := by decide +kernel
theorem subd12_1_197 : subd12_1 [5, -6] = true := by decide +kernel
theorem subd12_1_198 : subd12_1 [5, -5] = true := by decide +kernel
theorem subd12_1_199 : subd12_1 [5, -4] = true := by decide +kernel
theorem subd12_1_200 : subd12_1 [5, -3] = true := by decide +kernel
theorem subd12_1_201 : subd12_1 [5, -2] = true := by decide +kernel
theorem subd12_1_202 : subd12_1 [5, -1] = true := by decide +kernel
theorem subd12_1_203 : subd12_1 [5, 0] = true := by decide +kernel
theorem subd12_1_204 : subd12_1 [5, 1] = true := by decide +kernel
theorem subd12_1_205 : subd12_1 [5, 2] = true := by decide +kernel
theorem subd12_1_206 : subd12_1 [5, 3] = true := by decide +kernel
theorem subd12_1_207 : subd12_1 [5, 4] = true := by decide +kernel
theorem subd12_1_208 : subd12_1 [5, 5] = true := by decide +kernel
theorem subd12_1_209 : subd12_1 [6, -9] = true := by decide +kernel
theorem subd12_1_210 : subd12_1 [6, -8] = true := by decide +kernel
theorem subd12_1_211 : subd12_1 [6, -7] = true := by decide +kernel
theorem subd12_1_212 : subd12_1 [6, -6] = true := by decide +kernel
theorem subd12_1_213 : subd12_1 [6, -5] = true := by decide +kernel
theorem subd12_1_214 : subd12_1 [6, -4] = true := by decide +kernel
theorem subd12_1_215 : subd12_1 [6, -3] = true := by decide +kernel
theorem subd12_1_216 : subd12_1 [6, -2] = true := by decide +kernel
theorem subd12_1_217 : subd12_1 [6, -1] = true := by decide +kernel
theorem subd12_1_218 : subd12_1 [6, 0] = true := by decide +kernel
theorem subd12_1_219 : subd12_1 [6, 1] = true := by decide +kernel
theorem subd12_1_220 : subd12_1 [6, 2] = true := by decide +kernel
theorem subd12_1_221 : subd12_1 [6, 3] = true := by decide +kernel
theorem subd12_1_222 : subd12_1 [7, -8] = true := by decide +kernel
theorem subd12_1_223 : subd12_1 [7, -7] = true := by decide +kernel
theorem sbd12_1_6 : ∀ q ∈ blkd12_1_6, subd12_1 q = true := by
  unfold blkd12_1_6
  exact List.forall_mem_cons.2 ⟨subd12_1_192, List.forall_mem_cons.2 ⟨subd12_1_193, List.forall_mem_cons.2 ⟨subd12_1_194, List.forall_mem_cons.2 ⟨subd12_1_195, List.forall_mem_cons.2 ⟨subd12_1_196, List.forall_mem_cons.2 ⟨subd12_1_197, List.forall_mem_cons.2 ⟨subd12_1_198, List.forall_mem_cons.2 ⟨subd12_1_199, List.forall_mem_cons.2 ⟨subd12_1_200, List.forall_mem_cons.2 ⟨subd12_1_201, List.forall_mem_cons.2 ⟨subd12_1_202, List.forall_mem_cons.2 ⟨subd12_1_203, List.forall_mem_cons.2 ⟨subd12_1_204, List.forall_mem_cons.2 ⟨subd12_1_205, List.forall_mem_cons.2 ⟨subd12_1_206, List.forall_mem_cons.2 ⟨subd12_1_207, List.forall_mem_cons.2 ⟨subd12_1_208, List.forall_mem_cons.2 ⟨subd12_1_209, List.forall_mem_cons.2 ⟨subd12_1_210, List.forall_mem_cons.2 ⟨subd12_1_211, List.forall_mem_cons.2 ⟨subd12_1_212, List.forall_mem_cons.2 ⟨subd12_1_213, List.forall_mem_cons.2 ⟨subd12_1_214, List.forall_mem_cons.2 ⟨subd12_1_215, List.forall_mem_cons.2 ⟨subd12_1_216, List.forall_mem_cons.2 ⟨subd12_1_217, List.forall_mem_cons.2 ⟨subd12_1_218, List.forall_mem_cons.2 ⟨subd12_1_219, List.forall_mem_cons.2 ⟨subd12_1_220, List.forall_mem_cons.2 ⟨subd12_1_221, List.forall_mem_cons.2 ⟨subd12_1_222, List.forall_mem_cons.2 ⟨subd12_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_224 : subd12_1 [7, -6] = true := by decide +kernel
theorem subd12_1_225 : subd12_1 [7, -5] = true := by decide +kernel
theorem subd12_1_226 : subd12_1 [7, -4] = true := by decide +kernel
theorem subd12_1_227 : subd12_1 [7, -3] = true := by decide +kernel
theorem subd12_1_228 : subd12_1 [7, -2] = true := by decide +kernel
theorem subd12_1_229 : subd12_1 [7, -1] = true := by decide +kernel
theorem subd12_1_230 : subd12_1 [7, 0] = true := by decide +kernel
theorem subd12_1_231 : subd12_1 [7, 1] = true := by decide +kernel
theorem subd12_1_232 : subd12_1 [7, 2] = true := by decide +kernel
theorem subd12_1_233 : subd12_1 [8] = true := by decide +kernel
theorem sbd12_1_7 : ∀ q ∈ blkd12_1_7, subd12_1 q = true := by
  unfold blkd12_1_7
  exact List.forall_mem_cons.2 ⟨subd12_1_224, List.forall_mem_cons.2 ⟨subd12_1_225, List.forall_mem_cons.2 ⟨subd12_1_226, List.forall_mem_cons.2 ⟨subd12_1_227, List.forall_mem_cons.2 ⟨subd12_1_228, List.forall_mem_cons.2 ⟨subd12_1_229, List.forall_mem_cons.2 ⟨subd12_1_230, List.forall_mem_cons.2 ⟨subd12_1_231, List.forall_mem_cons.2 ⟨subd12_1_232, List.forall_mem_cons.2 ⟨subd12_1_233, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
