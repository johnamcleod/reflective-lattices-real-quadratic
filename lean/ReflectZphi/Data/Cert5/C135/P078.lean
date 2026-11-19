import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_2_160 : subd12_2 [0, 2, -2] = true := by decide +kernel
theorem subd12_2_161 : subd12_2 [0, 2, -1] = true := by decide +kernel
theorem subd12_2_162 : subd12_2 [0, 2, 0] = true := by decide +kernel
theorem subd12_2_163 : subd12_2 [0, 2, 1] = true := by decide +kernel
theorem subd12_2_164 : subd12_2 [0, 2, 2] = true := by decide +kernel
theorem subd12_2_165 : subd12_2 [0, 2, 3] = true := by decide +kernel
theorem subd12_2_166 : subd12_2 [0, 2, 4] = true := by decide +kernel
theorem subd12_2_167 : subd12_2 [0, 2, 5] = true := by decide +kernel
theorem subd12_2_168 : subd12_2 [1, -3] = true := by decide +kernel
theorem subd12_2_169 : subd12_2 [1, -2] = true := by decide +kernel
theorem subd12_2_170 : subd12_2 [1, -1, -8] = true := by decide +kernel
theorem subd12_2_171 : subd12_2 [1, -1, -7] = true := by decide +kernel
theorem subd12_2_172 : subd12_2 [1, -1, -6] = true := by decide +kernel
theorem subd12_2_173 : subd12_2 [1, -1, -5] = true := by decide +kernel
theorem subd12_2_174 : subd12_2 [1, -1, -4] = true := by decide +kernel
theorem subd12_2_175 : subd12_2 [1, -1, -3] = true := by decide +kernel
theorem subd12_2_176 : subd12_2 [1, -1, -2] = true := by decide +kernel
theorem subd12_2_177 : subd12_2 [1, -1, -1] = true := by decide +kernel
theorem subd12_2_178 : subd12_2 [1, -1, 0] = true := by decide +kernel
theorem subd12_2_179 : subd12_2 [1, -1, 1] = true := by decide +kernel
theorem subd12_2_180 : subd12_2 [1, -1, 2] = true := by decide +kernel
theorem subd12_2_181 : subd12_2 [1, -1, 3] = true := by decide +kernel
theorem subd12_2_182 : subd12_2 [1, -1, 4] = true := by decide +kernel
theorem subd12_2_183 : subd12_2 [1, -1, 5] = true := by decide +kernel
theorem subd12_2_184 : subd12_2 [1, -1, 6] = true := by decide +kernel
theorem subd12_2_185 : subd12_2 [1, -1, 7] = true := by decide +kernel
theorem subd12_2_186 : subd12_2 [1, -1, 8] = true := by decide +kernel
theorem subd12_2_187 : subd12_2 [1, 0, -9] = true := by decide +kernel
theorem subd12_2_188 : subd12_2 [1, 0, -8] = true := by decide +kernel
theorem subd12_2_189 : subd12_2 [1, 0, -7] = true := by decide +kernel
theorem subd12_2_190 : subd12_2 [1, 0, -6] = true := by decide +kernel
theorem subd12_2_191 : subd12_2 [1, 0, -5] = true := by decide +kernel
theorem sbd12_2_5 : ∀ q ∈ blkd12_2_5, subd12_2 q = true := by
  unfold blkd12_2_5
  exact List.forall_mem_cons.2 ⟨subd12_2_160, List.forall_mem_cons.2 ⟨subd12_2_161, List.forall_mem_cons.2 ⟨subd12_2_162, List.forall_mem_cons.2 ⟨subd12_2_163, List.forall_mem_cons.2 ⟨subd12_2_164, List.forall_mem_cons.2 ⟨subd12_2_165, List.forall_mem_cons.2 ⟨subd12_2_166, List.forall_mem_cons.2 ⟨subd12_2_167, List.forall_mem_cons.2 ⟨subd12_2_168, List.forall_mem_cons.2 ⟨subd12_2_169, List.forall_mem_cons.2 ⟨subd12_2_170, List.forall_mem_cons.2 ⟨subd12_2_171, List.forall_mem_cons.2 ⟨subd12_2_172, List.forall_mem_cons.2 ⟨subd12_2_173, List.forall_mem_cons.2 ⟨subd12_2_174, List.forall_mem_cons.2 ⟨subd12_2_175, List.forall_mem_cons.2 ⟨subd12_2_176, List.forall_mem_cons.2 ⟨subd12_2_177, List.forall_mem_cons.2 ⟨subd12_2_178, List.forall_mem_cons.2 ⟨subd12_2_179, List.forall_mem_cons.2 ⟨subd12_2_180, List.forall_mem_cons.2 ⟨subd12_2_181, List.forall_mem_cons.2 ⟨subd12_2_182, List.forall_mem_cons.2 ⟨subd12_2_183, List.forall_mem_cons.2 ⟨subd12_2_184, List.forall_mem_cons.2 ⟨subd12_2_185, List.forall_mem_cons.2 ⟨subd12_2_186, List.forall_mem_cons.2 ⟨subd12_2_187, List.forall_mem_cons.2 ⟨subd12_2_188, List.forall_mem_cons.2 ⟨subd12_2_189, List.forall_mem_cons.2 ⟨subd12_2_190, List.forall_mem_cons.2 ⟨subd12_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_192 : subd12_2 [1, 0, -4] = true := by decide +kernel
theorem subd12_2_193 : subd12_2 [1, 0, -3] = true := by decide +kernel
theorem subd12_2_194 : subd12_2 [1, 0, -2] = true := by decide +kernel
theorem subd12_2_195 : subd12_2 [1, 0, -1] = true := by decide +kernel
theorem subd12_2_196 : subd12_2 [1, 0, 0] = true := by decide +kernel
theorem subd12_2_197 : subd12_2 [1, 0, 1] = true := by decide +kernel
theorem subd12_2_198 : subd12_2 [1, 0, 2] = true := by decide +kernel
theorem subd12_2_199 : subd12_2 [1, 0, 3] = true := by decide +kernel
theorem subd12_2_200 : subd12_2 [1, 0, 4] = true := by decide +kernel
theorem subd12_2_201 : subd12_2 [1, 0, 5] = true := by decide +kernel
theorem subd12_2_202 : subd12_2 [1, 0, 6] = true := by decide +kernel
theorem subd12_2_203 : subd12_2 [1, 0, 7] = true := by decide +kernel
theorem subd12_2_204 : subd12_2 [1, 0, 8] = true := by decide +kernel
theorem subd12_2_205 : subd12_2 [1, 1, -9] = true := by decide +kernel
theorem subd12_2_206 : subd12_2 [1, 1, -8] = true := by decide +kernel
theorem subd12_2_207 : subd12_2 [1, 1, -7] = true := by decide +kernel
theorem subd12_2_208 : subd12_2 [1, 1, -6] = true := by decide +kernel
theorem subd12_2_209 : subd12_2 [1, 1, -5] = true := by decide +kernel
theorem subd12_2_210 : subd12_2 [1, 1, -4] = true := by decide +kernel
theorem subd12_2_211 : subd12_2 [1, 1, -3] = true := by decide +kernel
theorem subd12_2_212 : subd12_2 [1, 1, -2] = true := by decide +kernel
theorem subd12_2_213 : subd12_2 [1, 1, -1] = true := by decide +kernel
theorem subd12_2_214 : subd12_2 [1, 1, 0] = true := by decide +kernel
theorem subd12_2_215 : subd12_2 [1, 1, 1] = true := by decide +kernel
theorem subd12_2_216 : subd12_2 [1, 1, 2] = true := by decide +kernel
theorem subd12_2_217 : subd12_2 [1, 1, 3] = true := by decide +kernel
theorem subd12_2_218 : subd12_2 [1, 1, 4] = true := by decide +kernel
theorem subd12_2_219 : subd12_2 [1, 1, 5] = true := by decide +kernel
theorem subd12_2_220 : subd12_2 [1, 1, 6] = true := by decide +kernel
theorem subd12_2_221 : subd12_2 [1, 2] = true := by decide +kernel
theorem subd12_2_222 : subd12_2 [2, -3] = true := by decide +kernel
theorem subd12_2_223 : subd12_2 [2, -2] = true := by decide +kernel
theorem sbd12_2_6 : ∀ q ∈ blkd12_2_6, subd12_2 q = true := by
  unfold blkd12_2_6
  exact List.forall_mem_cons.2 ⟨subd12_2_192, List.forall_mem_cons.2 ⟨subd12_2_193, List.forall_mem_cons.2 ⟨subd12_2_194, List.forall_mem_cons.2 ⟨subd12_2_195, List.forall_mem_cons.2 ⟨subd12_2_196, List.forall_mem_cons.2 ⟨subd12_2_197, List.forall_mem_cons.2 ⟨subd12_2_198, List.forall_mem_cons.2 ⟨subd12_2_199, List.forall_mem_cons.2 ⟨subd12_2_200, List.forall_mem_cons.2 ⟨subd12_2_201, List.forall_mem_cons.2 ⟨subd12_2_202, List.forall_mem_cons.2 ⟨subd12_2_203, List.forall_mem_cons.2 ⟨subd12_2_204, List.forall_mem_cons.2 ⟨subd12_2_205, List.forall_mem_cons.2 ⟨subd12_2_206, List.forall_mem_cons.2 ⟨subd12_2_207, List.forall_mem_cons.2 ⟨subd12_2_208, List.forall_mem_cons.2 ⟨subd12_2_209, List.forall_mem_cons.2 ⟨subd12_2_210, List.forall_mem_cons.2 ⟨subd12_2_211, List.forall_mem_cons.2 ⟨subd12_2_212, List.forall_mem_cons.2 ⟨subd12_2_213, List.forall_mem_cons.2 ⟨subd12_2_214, List.forall_mem_cons.2 ⟨subd12_2_215, List.forall_mem_cons.2 ⟨subd12_2_216, List.forall_mem_cons.2 ⟨subd12_2_217, List.forall_mem_cons.2 ⟨subd12_2_218, List.forall_mem_cons.2 ⟨subd12_2_219, List.forall_mem_cons.2 ⟨subd12_2_220, List.forall_mem_cons.2 ⟨subd12_2_221, List.forall_mem_cons.2 ⟨subd12_2_222, List.forall_mem_cons.2 ⟨subd12_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_224 : subd12_2 [2, -1, -7] = true := by decide +kernel
theorem subd12_2_225 : subd12_2 [2, -1, -6] = true := by decide +kernel
theorem subd12_2_226 : subd12_2 [2, -1, -5] = true := by decide +kernel
theorem subd12_2_227 : subd12_2 [2, -1, -4] = true := by decide +kernel
theorem subd12_2_228 : subd12_2 [2, -1, -3] = true := by decide +kernel
theorem subd12_2_229 : subd12_2 [2, -1, -2] = true := by decide +kernel
theorem subd12_2_230 : subd12_2 [2, -1, -1] = true := by decide +kernel
theorem subd12_2_231 : subd12_2 [2, -1, 0] = true := by decide +kernel
theorem subd12_2_232 : subd12_2 [2, -1, 1] = true := by decide +kernel
theorem subd12_2_233 : subd12_2 [2, -1, 2] = true := by decide +kernel
theorem subd12_2_234 : subd12_2 [2, -1, 3] = true := by decide +kernel
theorem subd12_2_235 : subd12_2 [2, -1, 4] = true := by decide +kernel
theorem subd12_2_236 : subd12_2 [2, -1, 5] = true := by decide +kernel
theorem subd12_2_237 : subd12_2 [2, -1, 6] = true := by decide +kernel
theorem subd12_2_238 : subd12_2 [2, 0, -8] = true := by decide +kernel
theorem subd12_2_239 : subd12_2 [2, 0, -7] = true := by decide +kernel
theorem subd12_2_240 : subd12_2 [2, 0, -6] = true := by decide +kernel
theorem subd12_2_241 : subd12_2 [2, 0, -5] = true := by decide +kernel
theorem subd12_2_242 : subd12_2 [2, 0, -4] = true := by decide +kernel
theorem subd12_2_243 : subd12_2 [2, 0, -3] = true := by decide +kernel
theorem subd12_2_244 : subd12_2 [2, 0, -2] = true := by decide +kernel
theorem subd12_2_245 : subd12_2 [2, 0, -1] = true := by decide +kernel
theorem subd12_2_246 : subd12_2 [2, 0, 0] = true := by decide +kernel
theorem subd12_2_247 : subd12_2 [2, 0, 1] = true := by decide +kernel
theorem subd12_2_248 : subd12_2 [2, 0, 2] = true := by decide +kernel
theorem subd12_2_249 : subd12_2 [2, 0, 3] = true := by decide +kernel
theorem subd12_2_250 : subd12_2 [2, 0, 4] = true := by decide +kernel
theorem subd12_2_251 : subd12_2 [2, 0, 5] = true := by decide +kernel
theorem subd12_2_252 : subd12_2 [2, 0, 6] = true := by decide +kernel
theorem subd12_2_253 : subd12_2 [2, 1] = true := by decide +kernel
theorem subd12_2_254 : subd12_2 [3] = true := by decide +kernel
theorem sbd12_2_7 : ∀ q ∈ blkd12_2_7, subd12_2 q = true := by
  unfold blkd12_2_7
  exact List.forall_mem_cons.2 ⟨subd12_2_224, List.forall_mem_cons.2 ⟨subd12_2_225, List.forall_mem_cons.2 ⟨subd12_2_226, List.forall_mem_cons.2 ⟨subd12_2_227, List.forall_mem_cons.2 ⟨subd12_2_228, List.forall_mem_cons.2 ⟨subd12_2_229, List.forall_mem_cons.2 ⟨subd12_2_230, List.forall_mem_cons.2 ⟨subd12_2_231, List.forall_mem_cons.2 ⟨subd12_2_232, List.forall_mem_cons.2 ⟨subd12_2_233, List.forall_mem_cons.2 ⟨subd12_2_234, List.forall_mem_cons.2 ⟨subd12_2_235, List.forall_mem_cons.2 ⟨subd12_2_236, List.forall_mem_cons.2 ⟨subd12_2_237, List.forall_mem_cons.2 ⟨subd12_2_238, List.forall_mem_cons.2 ⟨subd12_2_239, List.forall_mem_cons.2 ⟨subd12_2_240, List.forall_mem_cons.2 ⟨subd12_2_241, List.forall_mem_cons.2 ⟨subd12_2_242, List.forall_mem_cons.2 ⟨subd12_2_243, List.forall_mem_cons.2 ⟨subd12_2_244, List.forall_mem_cons.2 ⟨subd12_2_245, List.forall_mem_cons.2 ⟨subd12_2_246, List.forall_mem_cons.2 ⟨subd12_2_247, List.forall_mem_cons.2 ⟨subd12_2_248, List.forall_mem_cons.2 ⟨subd12_2_249, List.forall_mem_cons.2 ⟨subd12_2_250, List.forall_mem_cons.2 ⟨subd12_2_251, List.forall_mem_cons.2 ⟨subd12_2_252, List.forall_mem_cons.2 ⟨subd12_2_253, List.forall_mem_cons.2 ⟨subd12_2_254, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel
theorem subd12_3_0 : subd12_3 [-5] = true := by decide +kernel
theorem subd12_3_1 : subd12_3 [-4, -5] = true := by decide +kernel
theorem subd12_3_2 : subd12_3 [-4, -4] = true := by decide +kernel
theorem subd12_3_3 : subd12_3 [-4, -3] = true := by decide +kernel
theorem subd12_3_4 : subd12_3 [-4, -2] = true := by decide +kernel
theorem subd12_3_5 : subd12_3 [-4, -1] = true := by decide +kernel
theorem subd12_3_6 : subd12_3 [-4, 0] = true := by decide +kernel
theorem subd12_3_7 : subd12_3 [-4, 1] = true := by decide +kernel
theorem subd12_3_8 : subd12_3 [-4, 2] = true := by decide +kernel
theorem subd12_3_9 : subd12_3 [-4, 3] = true := by decide +kernel
theorem subd12_3_10 : subd12_3 [-3, -6] = true := by decide +kernel
theorem subd12_3_11 : subd12_3 [-3, -5] = true := by decide +kernel
theorem subd12_3_12 : subd12_3 [-3, -4] = true := by decide +kernel
theorem subd12_3_13 : subd12_3 [-3, -3] = true := by decide +kernel
theorem subd12_3_14 : subd12_3 [-3, -2] = true := by decide +kernel
theorem subd12_3_15 : subd12_3 [-3, -1] = true := by decide +kernel
theorem subd12_3_16 : subd12_3 [-3, 0] = true := by decide +kernel
theorem subd12_3_17 : subd12_3 [-3, 1] = true := by decide +kernel
theorem subd12_3_18 : subd12_3 [-3, 2] = true := by decide +kernel
theorem subd12_3_19 : subd12_3 [-3, 3] = true := by decide +kernel
theorem subd12_3_20 : subd12_3 [-3, 4] = true := by decide +kernel
theorem subd12_3_21 : subd12_3 [-2, -6] = true := by decide +kernel
theorem subd12_3_22 : subd12_3 [-2, -5] = true := by decide +kernel
theorem subd12_3_23 : subd12_3 [-2, -4] = true := by decide +kernel
theorem subd12_3_24 : subd12_3 [-2, -3] = true := by decide +kernel
theorem subd12_3_25 : subd12_3 [-2, -2] = true := by decide +kernel
theorem subd12_3_26 : subd12_3 [-2, -1] = true := by decide +kernel
theorem subd12_3_27 : subd12_3 [-2, 0] = true := by decide +kernel
theorem subd12_3_28 : subd12_3 [-2, 1] = true := by decide +kernel
theorem subd12_3_29 : subd12_3 [-2, 2] = true := by decide +kernel
theorem subd12_3_30 : subd12_3 [-2, 3] = true := by decide +kernel
theorem subd12_3_31 : subd12_3 [-2, 4] = true := by decide +kernel
theorem sbd12_3_0 : ∀ q ∈ blkd12_3_0, subd12_3 q = true := by
  unfold blkd12_3_0
  exact List.forall_mem_cons.2 ⟨subd12_3_0, List.forall_mem_cons.2 ⟨subd12_3_1, List.forall_mem_cons.2 ⟨subd12_3_2, List.forall_mem_cons.2 ⟨subd12_3_3, List.forall_mem_cons.2 ⟨subd12_3_4, List.forall_mem_cons.2 ⟨subd12_3_5, List.forall_mem_cons.2 ⟨subd12_3_6, List.forall_mem_cons.2 ⟨subd12_3_7, List.forall_mem_cons.2 ⟨subd12_3_8, List.forall_mem_cons.2 ⟨subd12_3_9, List.forall_mem_cons.2 ⟨subd12_3_10, List.forall_mem_cons.2 ⟨subd12_3_11, List.forall_mem_cons.2 ⟨subd12_3_12, List.forall_mem_cons.2 ⟨subd12_3_13, List.forall_mem_cons.2 ⟨subd12_3_14, List.forall_mem_cons.2 ⟨subd12_3_15, List.forall_mem_cons.2 ⟨subd12_3_16, List.forall_mem_cons.2 ⟨subd12_3_17, List.forall_mem_cons.2 ⟨subd12_3_18, List.forall_mem_cons.2 ⟨subd12_3_19, List.forall_mem_cons.2 ⟨subd12_3_20, List.forall_mem_cons.2 ⟨subd12_3_21, List.forall_mem_cons.2 ⟨subd12_3_22, List.forall_mem_cons.2 ⟨subd12_3_23, List.forall_mem_cons.2 ⟨subd12_3_24, List.forall_mem_cons.2 ⟨subd12_3_25, List.forall_mem_cons.2 ⟨subd12_3_26, List.forall_mem_cons.2 ⟨subd12_3_27, List.forall_mem_cons.2 ⟨subd12_3_28, List.forall_mem_cons.2 ⟨subd12_3_29, List.forall_mem_cons.2 ⟨subd12_3_30, List.forall_mem_cons.2 ⟨subd12_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_32 : subd12_3 [-2, 5] = true := by decide +kernel
theorem subd12_3_33 : subd12_3 [-1, -7] = true := by decide +kernel
theorem subd12_3_34 : subd12_3 [-1, -6] = true := by decide +kernel
theorem subd12_3_35 : subd12_3 [-1, -5] = true := by decide +kernel
theorem subd12_3_36 : subd12_3 [-1, -4] = true := by decide +kernel
theorem subd12_3_37 : subd12_3 [-1, -3] = true := by decide +kernel
theorem subd12_3_38 : subd12_3 [-1, -2] = true := by decide +kernel
theorem subd12_3_39 : subd12_3 [-1, -1] = true := by decide +kernel
theorem subd12_3_40 : subd12_3 [-1, 0] = true := by decide +kernel
theorem subd12_3_41 : subd12_3 [-1, 1] = true := by decide +kernel
theorem subd12_3_42 : subd12_3 [-1, 2] = true := by decide +kernel
theorem subd12_3_43 : subd12_3 [-1, 3] = true := by decide +kernel
theorem subd12_3_44 : subd12_3 [-1, 4] = true := by decide +kernel
theorem subd12_3_45 : subd12_3 [-1, 5] = true := by decide +kernel
theorem subd12_3_46 : subd12_3 [0, -7] = true := by decide +kernel
theorem subd12_3_47 : subd12_3 [0, -6] = true := by decide +kernel
theorem subd12_3_48 : subd12_3 [0, -5] = true := by decide +kernel
theorem subd12_3_49 : subd12_3 [0, -4] = true := by decide +kernel
theorem subd12_3_50 : subd12_3 [0, -3] = true := by decide +kernel
theorem subd12_3_51 : subd12_3 [0, -2] = true := by decide +kernel
theorem subd12_3_52 : subd12_3 [0, -1] = true := by decide +kernel
theorem subd12_3_53 : subd12_3 [0, 0] = true := by decide +kernel
theorem subd12_3_54 : subd12_3 [0, 1] = true := by decide +kernel
theorem subd12_3_55 : subd12_3 [0, 2] = true := by decide +kernel
theorem subd12_3_56 : subd12_3 [0, 3] = true := by decide +kernel
theorem subd12_3_57 : subd12_3 [0, 4] = true := by decide +kernel
theorem subd12_3_58 : subd12_3 [0, 5] = true := by decide +kernel
theorem subd12_3_59 : subd12_3 [0, 6] = true := by decide +kernel
theorem subd12_3_60 : subd12_3 [1, -6] = true := by decide +kernel
theorem subd12_3_61 : subd12_3 [1, -5] = true := by decide +kernel
theorem subd12_3_62 : subd12_3 [1, -4] = true := by decide +kernel
theorem subd12_3_63 : subd12_3 [1, -3] = true := by decide +kernel
theorem sbd12_3_1 : ∀ q ∈ blkd12_3_1, subd12_3 q = true := by
  unfold blkd12_3_1
  exact List.forall_mem_cons.2 ⟨subd12_3_32, List.forall_mem_cons.2 ⟨subd12_3_33, List.forall_mem_cons.2 ⟨subd12_3_34, List.forall_mem_cons.2 ⟨subd12_3_35, List.forall_mem_cons.2 ⟨subd12_3_36, List.forall_mem_cons.2 ⟨subd12_3_37, List.forall_mem_cons.2 ⟨subd12_3_38, List.forall_mem_cons.2 ⟨subd12_3_39, List.forall_mem_cons.2 ⟨subd12_3_40, List.forall_mem_cons.2 ⟨subd12_3_41, List.forall_mem_cons.2 ⟨subd12_3_42, List.forall_mem_cons.2 ⟨subd12_3_43, List.forall_mem_cons.2 ⟨subd12_3_44, List.forall_mem_cons.2 ⟨subd12_3_45, List.forall_mem_cons.2 ⟨subd12_3_46, List.forall_mem_cons.2 ⟨subd12_3_47, List.forall_mem_cons.2 ⟨subd12_3_48, List.forall_mem_cons.2 ⟨subd12_3_49, List.forall_mem_cons.2 ⟨subd12_3_50, List.forall_mem_cons.2 ⟨subd12_3_51, List.forall_mem_cons.2 ⟨subd12_3_52, List.forall_mem_cons.2 ⟨subd12_3_53, List.forall_mem_cons.2 ⟨subd12_3_54, List.forall_mem_cons.2 ⟨subd12_3_55, List.forall_mem_cons.2 ⟨subd12_3_56, List.forall_mem_cons.2 ⟨subd12_3_57, List.forall_mem_cons.2 ⟨subd12_3_58, List.forall_mem_cons.2 ⟨subd12_3_59, List.forall_mem_cons.2 ⟨subd12_3_60, List.forall_mem_cons.2 ⟨subd12_3_61, List.forall_mem_cons.2 ⟨subd12_3_62, List.forall_mem_cons.2 ⟨subd12_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
