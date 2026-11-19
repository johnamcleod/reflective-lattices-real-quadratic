import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_8_160 : subd7_8 [0, 0, 37] = true := by decide +kernel
theorem subd7_8_161 : subd7_8 [0, 0, 38] = true := by decide +kernel
theorem subd7_8_162 : subd7_8 [0, 0, 39] = true := by decide +kernel
theorem subd7_8_163 : subd7_8 [0, 0, 40] = true := by decide +kernel
theorem subd7_8_164 : subd7_8 [0, 0, 41] = true := by decide +kernel
theorem subd7_8_165 : subd7_8 [0, 0, 42] = true := by decide +kernel
theorem subd7_8_166 : subd7_8 [0, 0, 43] = true := by decide +kernel
theorem subd7_8_167 : subd7_8 [0, 0, 44] = true := by decide +kernel
theorem subd7_8_168 : subd7_8 [0, 1, -23] = true := by decide +kernel
theorem subd7_8_169 : subd7_8 [0, 1, -22] = true := by decide +kernel
theorem subd7_8_170 : subd7_8 [0, 1, -21] = true := by decide +kernel
theorem subd7_8_171 : subd7_8 [0, 1, -20] = true := by decide +kernel
theorem subd7_8_172 : subd7_8 [0, 1, -19] = true := by decide +kernel
theorem subd7_8_173 : subd7_8 [0, 1, -18] = true := by decide +kernel
theorem subd7_8_174 : subd7_8 [0, 1, -17] = true := by decide +kernel
theorem subd7_8_175 : subd7_8 [0, 1, -16] = true := by decide +kernel
theorem subd7_8_176 : subd7_8 [0, 1, -15] = true := by decide +kernel
theorem subd7_8_177 : subd7_8 [0, 1, -14] = true := by decide +kernel
theorem subd7_8_178 : subd7_8 [0, 1, -13] = true := by decide +kernel
theorem subd7_8_179 : subd7_8 [0, 1, -12] = true := by decide +kernel
theorem subd7_8_180 : subd7_8 [0, 1, -11] = true := by decide +kernel
theorem subd7_8_181 : subd7_8 [0, 1, -10] = true := by decide +kernel
theorem subd7_8_182 : subd7_8 [0, 1, -9] = true := by decide +kernel
theorem subd7_8_183 : subd7_8 [0, 1, -8] = true := by decide +kernel
theorem subd7_8_184 : subd7_8 [0, 1, -7] = true := by decide +kernel
theorem subd7_8_185 : subd7_8 [0, 1, -6] = true := by decide +kernel
theorem subd7_8_186 : subd7_8 [0, 1, -5] = true := by decide +kernel
theorem subd7_8_187 : subd7_8 [0, 1, -4] = true := by decide +kernel
theorem subd7_8_188 : subd7_8 [0, 1, -3] = true := by decide +kernel
theorem subd7_8_189 : subd7_8 [0, 1, -2] = true := by decide +kernel
theorem subd7_8_190 : subd7_8 [0, 1, -1] = true := by decide +kernel
theorem subd7_8_191 : subd7_8 [0, 1, 0] = true := by decide +kernel
theorem sbd7_8_5 : ∀ q ∈ blkd7_8_5, subd7_8 q = true := by
  unfold blkd7_8_5
  exact List.forall_mem_cons.2 ⟨subd7_8_160, List.forall_mem_cons.2 ⟨subd7_8_161, List.forall_mem_cons.2 ⟨subd7_8_162, List.forall_mem_cons.2 ⟨subd7_8_163, List.forall_mem_cons.2 ⟨subd7_8_164, List.forall_mem_cons.2 ⟨subd7_8_165, List.forall_mem_cons.2 ⟨subd7_8_166, List.forall_mem_cons.2 ⟨subd7_8_167, List.forall_mem_cons.2 ⟨subd7_8_168, List.forall_mem_cons.2 ⟨subd7_8_169, List.forall_mem_cons.2 ⟨subd7_8_170, List.forall_mem_cons.2 ⟨subd7_8_171, List.forall_mem_cons.2 ⟨subd7_8_172, List.forall_mem_cons.2 ⟨subd7_8_173, List.forall_mem_cons.2 ⟨subd7_8_174, List.forall_mem_cons.2 ⟨subd7_8_175, List.forall_mem_cons.2 ⟨subd7_8_176, List.forall_mem_cons.2 ⟨subd7_8_177, List.forall_mem_cons.2 ⟨subd7_8_178, List.forall_mem_cons.2 ⟨subd7_8_179, List.forall_mem_cons.2 ⟨subd7_8_180, List.forall_mem_cons.2 ⟨subd7_8_181, List.forall_mem_cons.2 ⟨subd7_8_182, List.forall_mem_cons.2 ⟨subd7_8_183, List.forall_mem_cons.2 ⟨subd7_8_184, List.forall_mem_cons.2 ⟨subd7_8_185, List.forall_mem_cons.2 ⟨subd7_8_186, List.forall_mem_cons.2 ⟨subd7_8_187, List.forall_mem_cons.2 ⟨subd7_8_188, List.forall_mem_cons.2 ⟨subd7_8_189, List.forall_mem_cons.2 ⟨subd7_8_190, List.forall_mem_cons.2 ⟨subd7_8_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_8_192 : subd7_8 [0, 1, 1] = true := by decide +kernel
theorem subd7_8_193 : subd7_8 [0, 1, 2] = true := by decide +kernel
theorem subd7_8_194 : subd7_8 [0, 1, 3] = true := by decide +kernel
theorem subd7_8_195 : subd7_8 [0, 1, 4] = true := by decide +kernel
theorem subd7_8_196 : subd7_8 [0, 1, 5] = true := by decide +kernel
theorem subd7_8_197 : subd7_8 [0, 1, 6] = true := by decide +kernel
theorem subd7_8_198 : subd7_8 [0, 1, 7] = true := by decide +kernel
theorem subd7_8_199 : subd7_8 [0, 1, 8] = true := by decide +kernel
theorem subd7_8_200 : subd7_8 [0, 1, 9] = true := by decide +kernel
theorem subd7_8_201 : subd7_8 [0, 1, 10] = true := by decide +kernel
theorem subd7_8_202 : subd7_8 [0, 1, 11] = true := by decide +kernel
theorem subd7_8_203 : subd7_8 [0, 1, 12] = true := by decide +kernel
theorem subd7_8_204 : subd7_8 [0, 1, 13] = true := by decide +kernel
theorem subd7_8_205 : subd7_8 [0, 1, 14] = true := by decide +kernel
theorem subd7_8_206 : subd7_8 [0, 1, 15] = true := by decide +kernel
theorem subd7_8_207 : subd7_8 [0, 1, 16] = true := by decide +kernel
theorem subd7_8_208 : subd7_8 [0, 1, 17] = true := by decide +kernel
theorem subd7_8_209 : subd7_8 [0, 1, 18] = true := by decide +kernel
theorem subd7_8_210 : subd7_8 [0, 1, 19] = true := by decide +kernel
theorem subd7_8_211 : subd7_8 [0, 1, 20] = true := by decide +kernel
theorem subd7_8_212 : subd7_8 [0, 1, 21] = true := by decide +kernel
theorem subd7_8_213 : subd7_8 [0, 1, 22] = true := by decide +kernel
theorem subd7_8_214 : subd7_8 [1, -1] = true := by decide +kernel
theorem subd7_8_215 : subd7_8 [1, 0, -15] = true := by decide +kernel
theorem subd7_8_216 : subd7_8 [1, 0, -14] = true := by decide +kernel
theorem subd7_8_217 : subd7_8 [1, 0, -13] = true := by decide +kernel
theorem subd7_8_218 : subd7_8 [1, 0, -12] = true := by decide +kernel
theorem subd7_8_219 : subd7_8 [1, 0, -11] = true := by decide +kernel
theorem subd7_8_220 : subd7_8 [1, 0, -10] = true := by decide +kernel
theorem subd7_8_221 : subd7_8 [1, 0, -9] = true := by decide +kernel
theorem subd7_8_222 : subd7_8 [1, 0, -8] = true := by decide +kernel
theorem subd7_8_223 : subd7_8 [1, 0, -7] = true := by decide +kernel
theorem sbd7_8_6 : ∀ q ∈ blkd7_8_6, subd7_8 q = true := by
  unfold blkd7_8_6
  exact List.forall_mem_cons.2 ⟨subd7_8_192, List.forall_mem_cons.2 ⟨subd7_8_193, List.forall_mem_cons.2 ⟨subd7_8_194, List.forall_mem_cons.2 ⟨subd7_8_195, List.forall_mem_cons.2 ⟨subd7_8_196, List.forall_mem_cons.2 ⟨subd7_8_197, List.forall_mem_cons.2 ⟨subd7_8_198, List.forall_mem_cons.2 ⟨subd7_8_199, List.forall_mem_cons.2 ⟨subd7_8_200, List.forall_mem_cons.2 ⟨subd7_8_201, List.forall_mem_cons.2 ⟨subd7_8_202, List.forall_mem_cons.2 ⟨subd7_8_203, List.forall_mem_cons.2 ⟨subd7_8_204, List.forall_mem_cons.2 ⟨subd7_8_205, List.forall_mem_cons.2 ⟨subd7_8_206, List.forall_mem_cons.2 ⟨subd7_8_207, List.forall_mem_cons.2 ⟨subd7_8_208, List.forall_mem_cons.2 ⟨subd7_8_209, List.forall_mem_cons.2 ⟨subd7_8_210, List.forall_mem_cons.2 ⟨subd7_8_211, List.forall_mem_cons.2 ⟨subd7_8_212, List.forall_mem_cons.2 ⟨subd7_8_213, List.forall_mem_cons.2 ⟨subd7_8_214, List.forall_mem_cons.2 ⟨subd7_8_215, List.forall_mem_cons.2 ⟨subd7_8_216, List.forall_mem_cons.2 ⟨subd7_8_217, List.forall_mem_cons.2 ⟨subd7_8_218, List.forall_mem_cons.2 ⟨subd7_8_219, List.forall_mem_cons.2 ⟨subd7_8_220, List.forall_mem_cons.2 ⟨subd7_8_221, List.forall_mem_cons.2 ⟨subd7_8_222, List.forall_mem_cons.2 ⟨subd7_8_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_8_224 : subd7_8 [1, 0, -6] = true := by decide +kernel
theorem subd7_8_225 : subd7_8 [1, 0, -5] = true := by decide +kernel
theorem subd7_8_226 : subd7_8 [1, 0, -4] = true := by decide +kernel
theorem subd7_8_227 : subd7_8 [1, 0, -3] = true := by decide +kernel
theorem subd7_8_228 : subd7_8 [1, 0, -2] = true := by decide +kernel
theorem subd7_8_229 : subd7_8 [1, 0, -1] = true := by decide +kernel
theorem subd7_8_230 : subd7_8 [1, 0, 0] = true := by decide +kernel
theorem subd7_8_231 : subd7_8 [1, 0, 1] = true := by decide +kernel
theorem subd7_8_232 : subd7_8 [1, 0, 2] = true := by decide +kernel
theorem subd7_8_233 : subd7_8 [1, 0, 3] = true := by decide +kernel
theorem subd7_8_234 : subd7_8 [1, 0, 4] = true := by decide +kernel
theorem subd7_8_235 : subd7_8 [1, 0, 5] = true := by decide +kernel
theorem subd7_8_236 : subd7_8 [1, 0, 6] = true := by decide +kernel
theorem subd7_8_237 : subd7_8 [1, 0, 7] = true := by decide +kernel
theorem subd7_8_238 : subd7_8 [1, 0, 8] = true := by decide +kernel
theorem subd7_8_239 : subd7_8 [1, 0, 9] = true := by decide +kernel
theorem subd7_8_240 : subd7_8 [1, 0, 10] = true := by decide +kernel
theorem subd7_8_241 : subd7_8 [1, 0, 11] = true := by decide +kernel
theorem subd7_8_242 : subd7_8 [1, 0, 12] = true := by decide +kernel
theorem subd7_8_243 : subd7_8 [1, 0, 13] = true := by decide +kernel
theorem subd7_8_244 : subd7_8 [1, 0, 14] = true := by decide +kernel
theorem sbd7_8_7 : ∀ q ∈ blkd7_8_7, subd7_8 q = true := by
  unfold blkd7_8_7
  exact List.forall_mem_cons.2 ⟨subd7_8_224, List.forall_mem_cons.2 ⟨subd7_8_225, List.forall_mem_cons.2 ⟨subd7_8_226, List.forall_mem_cons.2 ⟨subd7_8_227, List.forall_mem_cons.2 ⟨subd7_8_228, List.forall_mem_cons.2 ⟨subd7_8_229, List.forall_mem_cons.2 ⟨subd7_8_230, List.forall_mem_cons.2 ⟨subd7_8_231, List.forall_mem_cons.2 ⟨subd7_8_232, List.forall_mem_cons.2 ⟨subd7_8_233, List.forall_mem_cons.2 ⟨subd7_8_234, List.forall_mem_cons.2 ⟨subd7_8_235, List.forall_mem_cons.2 ⟨subd7_8_236, List.forall_mem_cons.2 ⟨subd7_8_237, List.forall_mem_cons.2 ⟨subd7_8_238, List.forall_mem_cons.2 ⟨subd7_8_239, List.forall_mem_cons.2 ⟨subd7_8_240, List.forall_mem_cons.2 ⟨subd7_8_241, List.forall_mem_cons.2 ⟨subd7_8_242, List.forall_mem_cons.2 ⟨subd7_8_243, List.forall_mem_cons.2 ⟨subd7_8_244, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_9 : ldCheck G d7_9.U d7_9.ms ldd7_9 = true := by decide +kernel
theorem pre_okd7_9 : subPre G cell7 d7_9 = true := by decide +kernel
theorem subd7_9_0 : subd7_9 [-6] = true := by decide +kernel
theorem subd7_9_1 : subd7_9 [-5, -4] = true := by decide +kernel
theorem subd7_9_2 : subd7_9 [-5, -3] = true := by decide +kernel
theorem subd7_9_3 : subd7_9 [-5, -2] = true := by decide +kernel
theorem subd7_9_4 : subd7_9 [-5, -1] = true := by decide +kernel
theorem subd7_9_5 : subd7_9 [-5, 0] = true := by decide +kernel
theorem subd7_9_6 : subd7_9 [-5, 1] = true := by decide +kernel
theorem subd7_9_7 : subd7_9 [-5, 2] = true := by decide +kernel
theorem subd7_9_8 : subd7_9 [-5, 3] = true := by decide +kernel
theorem subd7_9_9 : subd7_9 [-4, -5] = true := by decide +kernel
theorem subd7_9_10 : subd7_9 [-4, -4] = true := by decide +kernel
theorem subd7_9_11 : subd7_9 [-4, -3] = true := by decide +kernel
theorem subd7_9_12 : subd7_9 [-4, -2] = true := by decide +kernel
theorem subd7_9_13 : subd7_9 [-4, -1] = true := by decide +kernel
theorem subd7_9_14 : subd7_9 [-4, 0] = true := by decide +kernel
theorem subd7_9_15 : subd7_9 [-4, 1] = true := by decide +kernel
theorem subd7_9_16 : subd7_9 [-4, 2] = true := by decide +kernel
theorem subd7_9_17 : subd7_9 [-4, 3] = true := by decide +kernel
theorem subd7_9_18 : subd7_9 [-4, 4] = true := by decide +kernel
theorem subd7_9_19 : subd7_9 [-3, -6] = true := by decide +kernel
theorem subd7_9_20 : subd7_9 [-3, -5] = true := by decide +kernel
theorem subd7_9_21 : subd7_9 [-3, -4] = true := by decide +kernel
theorem subd7_9_22 : subd7_9 [-3, -3] = true := by decide +kernel
theorem subd7_9_23 : subd7_9 [-3, -2] = true := by decide +kernel
theorem subd7_9_24 : subd7_9 [-3, -1] = true := by decide +kernel
theorem subd7_9_25 : subd7_9 [-3, 0] = true := by decide +kernel
theorem subd7_9_26 : subd7_9 [-3, 1] = true := by decide +kernel
theorem subd7_9_27 : subd7_9 [-3, 2] = true := by decide +kernel
theorem subd7_9_28 : subd7_9 [-3, 3] = true := by decide +kernel
theorem subd7_9_29 : subd7_9 [-3, 4] = true := by decide +kernel
theorem subd7_9_30 : subd7_9 [-3, 5] = true := by decide +kernel
theorem subd7_9_31 : subd7_9 [-2, -6] = true := by decide +kernel
theorem sbd7_9_0 : ∀ q ∈ blkd7_9_0, subd7_9 q = true := by
  unfold blkd7_9_0
  exact List.forall_mem_cons.2 ⟨subd7_9_0, List.forall_mem_cons.2 ⟨subd7_9_1, List.forall_mem_cons.2 ⟨subd7_9_2, List.forall_mem_cons.2 ⟨subd7_9_3, List.forall_mem_cons.2 ⟨subd7_9_4, List.forall_mem_cons.2 ⟨subd7_9_5, List.forall_mem_cons.2 ⟨subd7_9_6, List.forall_mem_cons.2 ⟨subd7_9_7, List.forall_mem_cons.2 ⟨subd7_9_8, List.forall_mem_cons.2 ⟨subd7_9_9, List.forall_mem_cons.2 ⟨subd7_9_10, List.forall_mem_cons.2 ⟨subd7_9_11, List.forall_mem_cons.2 ⟨subd7_9_12, List.forall_mem_cons.2 ⟨subd7_9_13, List.forall_mem_cons.2 ⟨subd7_9_14, List.forall_mem_cons.2 ⟨subd7_9_15, List.forall_mem_cons.2 ⟨subd7_9_16, List.forall_mem_cons.2 ⟨subd7_9_17, List.forall_mem_cons.2 ⟨subd7_9_18, List.forall_mem_cons.2 ⟨subd7_9_19, List.forall_mem_cons.2 ⟨subd7_9_20, List.forall_mem_cons.2 ⟨subd7_9_21, List.forall_mem_cons.2 ⟨subd7_9_22, List.forall_mem_cons.2 ⟨subd7_9_23, List.forall_mem_cons.2 ⟨subd7_9_24, List.forall_mem_cons.2 ⟨subd7_9_25, List.forall_mem_cons.2 ⟨subd7_9_26, List.forall_mem_cons.2 ⟨subd7_9_27, List.forall_mem_cons.2 ⟨subd7_9_28, List.forall_mem_cons.2 ⟨subd7_9_29, List.forall_mem_cons.2 ⟨subd7_9_30, List.forall_mem_cons.2 ⟨subd7_9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_9_32 : subd7_9 [-2, -5] = true := by decide +kernel
theorem subd7_9_33 : subd7_9 [-2, -4] = true := by decide +kernel
theorem subd7_9_34 : subd7_9 [-2, -3] = true := by decide +kernel
theorem subd7_9_35 : subd7_9 [-2, -2] = true := by decide +kernel
theorem subd7_9_36 : subd7_9 [-2, -1, -7] = true := by decide +kernel
theorem subd7_9_37 : subd7_9 [-2, -1, -6] = true := by decide +kernel
theorem subd7_9_38 : subd7_9 [-2, -1, -5] = true := by decide +kernel
theorem subd7_9_39 : subd7_9 [-2, -1, -4] = true := by decide +kernel
theorem subd7_9_40 : subd7_9 [-2, -1, -3] = true := by decide +kernel
theorem subd7_9_41 : subd7_9 [-2, -1, -2] = true := by decide +kernel
theorem subd7_9_42 : subd7_9 [-2, -1, -1] = true := by decide +kernel
theorem subd7_9_43 : subd7_9 [-2, -1, 0] = true := by decide +kernel
theorem subd7_9_44 : subd7_9 [-2, -1, 1] = true := by decide +kernel
theorem subd7_9_45 : subd7_9 [-2, -1, 2] = true := by decide +kernel
theorem subd7_9_46 : subd7_9 [-2, -1, 3] = true := by decide +kernel
theorem subd7_9_47 : subd7_9 [-2, -1, 4] = true := by decide +kernel
theorem subd7_9_48 : subd7_9 [-2, -1, 5] = true := by decide +kernel
theorem subd7_9_49 : subd7_9 [-2, 0, -7] = true := by decide +kernel
theorem subd7_9_50 : subd7_9 [-2, 0, -6] = true := by decide +kernel
theorem subd7_9_51 : subd7_9 [-2, 0, -5] = true := by decide +kernel
theorem subd7_9_52 : subd7_9 [-2, 0, -4] = true := by decide +kernel
theorem subd7_9_53 : subd7_9 [-2, 0, -3] = true := by decide +kernel
theorem subd7_9_54 : subd7_9 [-2, 0, -2] = true := by decide +kernel
theorem subd7_9_55 : subd7_9 [-2, 0, -1] = true := by decide +kernel
theorem subd7_9_56 : subd7_9 [-2, 0, 0] = true := by decide +kernel
theorem subd7_9_57 : subd7_9 [-2, 0, 1] = true := by decide +kernel
theorem subd7_9_58 : subd7_9 [-2, 0, 2] = true := by decide +kernel
theorem subd7_9_59 : subd7_9 [-2, 0, 3] = true := by decide +kernel
theorem subd7_9_60 : subd7_9 [-2, 0, 4] = true := by decide +kernel
theorem subd7_9_61 : subd7_9 [-2, 0, 5] = true := by decide +kernel
theorem subd7_9_62 : subd7_9 [-2, 1] = true := by decide +kernel
theorem subd7_9_63 : subd7_9 [-2, 2] = true := by decide +kernel
theorem sbd7_9_1 : ∀ q ∈ blkd7_9_1, subd7_9 q = true := by
  unfold blkd7_9_1
  exact List.forall_mem_cons.2 ⟨subd7_9_32, List.forall_mem_cons.2 ⟨subd7_9_33, List.forall_mem_cons.2 ⟨subd7_9_34, List.forall_mem_cons.2 ⟨subd7_9_35, List.forall_mem_cons.2 ⟨subd7_9_36, List.forall_mem_cons.2 ⟨subd7_9_37, List.forall_mem_cons.2 ⟨subd7_9_38, List.forall_mem_cons.2 ⟨subd7_9_39, List.forall_mem_cons.2 ⟨subd7_9_40, List.forall_mem_cons.2 ⟨subd7_9_41, List.forall_mem_cons.2 ⟨subd7_9_42, List.forall_mem_cons.2 ⟨subd7_9_43, List.forall_mem_cons.2 ⟨subd7_9_44, List.forall_mem_cons.2 ⟨subd7_9_45, List.forall_mem_cons.2 ⟨subd7_9_46, List.forall_mem_cons.2 ⟨subd7_9_47, List.forall_mem_cons.2 ⟨subd7_9_48, List.forall_mem_cons.2 ⟨subd7_9_49, List.forall_mem_cons.2 ⟨subd7_9_50, List.forall_mem_cons.2 ⟨subd7_9_51, List.forall_mem_cons.2 ⟨subd7_9_52, List.forall_mem_cons.2 ⟨subd7_9_53, List.forall_mem_cons.2 ⟨subd7_9_54, List.forall_mem_cons.2 ⟨subd7_9_55, List.forall_mem_cons.2 ⟨subd7_9_56, List.forall_mem_cons.2 ⟨subd7_9_57, List.forall_mem_cons.2 ⟨subd7_9_58, List.forall_mem_cons.2 ⟨subd7_9_59, List.forall_mem_cons.2 ⟨subd7_9_60, List.forall_mem_cons.2 ⟨subd7_9_61, List.forall_mem_cons.2 ⟨subd7_9_62, List.forall_mem_cons.2 ⟨subd7_9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_9_64 : subd7_9 [-2, 3] = true := by decide +kernel
theorem subd7_9_65 : subd7_9 [-2, 4] = true := by decide +kernel
theorem subd7_9_66 : subd7_9 [-2, 5] = true := by decide +kernel
theorem subd7_9_67 : subd7_9 [-1, -6] = true := by decide +kernel
theorem subd7_9_68 : subd7_9 [-1, -5] = true := by decide +kernel
theorem subd7_9_69 : subd7_9 [-1, -4] = true := by decide +kernel
theorem subd7_9_70 : subd7_9 [-1, -3] = true := by decide +kernel
theorem subd7_9_71 : subd7_9 [-1, -2, -7] = true := by decide +kernel
theorem subd7_9_72 : subd7_9 [-1, -2, -6] = true := by decide +kernel
theorem subd7_9_73 : subd7_9 [-1, -2, -5] = true := by decide +kernel
theorem subd7_9_74 : subd7_9 [-1, -2, -4] = true := by decide +kernel
theorem subd7_9_75 : subd7_9 [-1, -2, -3] = true := by decide +kernel
theorem subd7_9_76 : subd7_9 [-1, -2, -2] = true := by decide +kernel
theorem subd7_9_77 : subd7_9 [-1, -2, -1] = true := by decide +kernel
theorem subd7_9_78 : subd7_9 [-1, -2, 0] = true := by decide +kernel
theorem subd7_9_79 : subd7_9 [-1, -2, 1] = true := by decide +kernel
theorem subd7_9_80 : subd7_9 [-1, -2, 2] = true := by decide +kernel
theorem subd7_9_81 : subd7_9 [-1, -2, 3] = true := by decide +kernel
theorem subd7_9_82 : subd7_9 [-1, -2, 4] = true := by decide +kernel
theorem subd7_9_83 : subd7_9 [-1, -2, 5] = true := by decide +kernel
theorem subd7_9_84 : subd7_9 [-1, -2, 6] = true := by decide +kernel
theorem subd7_9_85 : subd7_9 [-1, -1, -7] = true := by decide +kernel
theorem subd7_9_86 : subd7_9 [-1, -1, -6] = true := by decide +kernel
theorem subd7_9_87 : subd7_9 [-1, -1, -5] = true := by decide +kernel
theorem subd7_9_88 : subd7_9 [-1, -1, -4] = true := by decide +kernel
theorem subd7_9_89 : subd7_9 [-1, -1, -3] = true := by decide +kernel
theorem subd7_9_90 : subd7_9 [-1, -1, -2] = true := by decide +kernel
theorem subd7_9_91 : subd7_9 [-1, -1, -1] = true := by decide +kernel
theorem subd7_9_92 : subd7_9 [-1, -1, 0] = true := by decide +kernel
theorem subd7_9_93 : subd7_9 [-1, -1, 1] = true := by decide +kernel
theorem subd7_9_94 : subd7_9 [-1, -1, 2] = true := by decide +kernel
theorem subd7_9_95 : subd7_9 [-1, -1, 3] = true := by decide +kernel
theorem sbd7_9_2 : ∀ q ∈ blkd7_9_2, subd7_9 q = true := by
  unfold blkd7_9_2
  exact List.forall_mem_cons.2 ⟨subd7_9_64, List.forall_mem_cons.2 ⟨subd7_9_65, List.forall_mem_cons.2 ⟨subd7_9_66, List.forall_mem_cons.2 ⟨subd7_9_67, List.forall_mem_cons.2 ⟨subd7_9_68, List.forall_mem_cons.2 ⟨subd7_9_69, List.forall_mem_cons.2 ⟨subd7_9_70, List.forall_mem_cons.2 ⟨subd7_9_71, List.forall_mem_cons.2 ⟨subd7_9_72, List.forall_mem_cons.2 ⟨subd7_9_73, List.forall_mem_cons.2 ⟨subd7_9_74, List.forall_mem_cons.2 ⟨subd7_9_75, List.forall_mem_cons.2 ⟨subd7_9_76, List.forall_mem_cons.2 ⟨subd7_9_77, List.forall_mem_cons.2 ⟨subd7_9_78, List.forall_mem_cons.2 ⟨subd7_9_79, List.forall_mem_cons.2 ⟨subd7_9_80, List.forall_mem_cons.2 ⟨subd7_9_81, List.forall_mem_cons.2 ⟨subd7_9_82, List.forall_mem_cons.2 ⟨subd7_9_83, List.forall_mem_cons.2 ⟨subd7_9_84, List.forall_mem_cons.2 ⟨subd7_9_85, List.forall_mem_cons.2 ⟨subd7_9_86, List.forall_mem_cons.2 ⟨subd7_9_87, List.forall_mem_cons.2 ⟨subd7_9_88, List.forall_mem_cons.2 ⟨subd7_9_89, List.forall_mem_cons.2 ⟨subd7_9_90, List.forall_mem_cons.2 ⟨subd7_9_91, List.forall_mem_cons.2 ⟨subd7_9_92, List.forall_mem_cons.2 ⟨subd7_9_93, List.forall_mem_cons.2 ⟨subd7_9_94, List.forall_mem_cons.2 ⟨subd7_9_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
