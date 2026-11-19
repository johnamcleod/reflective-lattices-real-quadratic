import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_5_160 : subd7_5 [0, 1, -3] = true := by decide +kernel
theorem subd7_5_161 : subd7_5 [0, 1, -2] = true := by decide +kernel
theorem subd7_5_162 : subd7_5 [0, 1, -1] = true := by decide +kernel
theorem subd7_5_163 : subd7_5 [0, 1, 0] = true := by decide +kernel
theorem subd7_5_164 : subd7_5 [0, 1, 1] = true := by decide +kernel
theorem subd7_5_165 : subd7_5 [0, 1, 2] = true := by decide +kernel
theorem subd7_5_166 : subd7_5 [0, 1, 3] = true := by decide +kernel
theorem subd7_5_167 : subd7_5 [0, 1, 4] = true := by decide +kernel
theorem subd7_5_168 : subd7_5 [0, 1, 5] = true := by decide +kernel
theorem subd7_5_169 : subd7_5 [0, 1, 6] = true := by decide +kernel
theorem subd7_5_170 : subd7_5 [0, 1, 7] = true := by decide +kernel
theorem subd7_5_171 : subd7_5 [0, 1, 8] = true := by decide +kernel
theorem subd7_5_172 : subd7_5 [0, 1, 9] = true := by decide +kernel
theorem subd7_5_173 : subd7_5 [0, 1, 10] = true := by decide +kernel
theorem subd7_5_174 : subd7_5 [0, 1, 11] = true := by decide +kernel
theorem subd7_5_175 : subd7_5 [0, 1, 12] = true := by decide +kernel
theorem subd7_5_176 : subd7_5 [0, 1, 13] = true := by decide +kernel
theorem subd7_5_177 : subd7_5 [0, 1, 14] = true := by decide +kernel
theorem subd7_5_178 : subd7_5 [0, 1, 15] = true := by decide +kernel
theorem subd7_5_179 : subd7_5 [0, 1, 16] = true := by decide +kernel
theorem subd7_5_180 : subd7_5 [1, -2] = true := by decide +kernel
theorem subd7_5_181 : subd7_5 [1, -1, -10] = true := by decide +kernel
theorem subd7_5_182 : subd7_5 [1, -1, -9] = true := by decide +kernel
theorem subd7_5_183 : subd7_5 [1, -1, -8] = true := by decide +kernel
theorem subd7_5_184 : subd7_5 [1, -1, -7] = true := by decide +kernel
theorem subd7_5_185 : subd7_5 [1, -1, -6] = true := by decide +kernel
theorem subd7_5_186 : subd7_5 [1, -1, -5] = true := by decide +kernel
theorem subd7_5_187 : subd7_5 [1, -1, -4] = true := by decide +kernel
theorem subd7_5_188 : subd7_5 [1, -1, -3] = true := by decide +kernel
theorem subd7_5_189 : subd7_5 [1, -1, -2] = true := by decide +kernel
theorem subd7_5_190 : subd7_5 [1, -1, -1] = true := by decide +kernel
theorem subd7_5_191 : subd7_5 [1, -1, 0] = true := by decide +kernel
theorem sbd7_5_5 : ∀ q ∈ blkd7_5_5, subd7_5 q = true := by
  unfold blkd7_5_5
  exact List.forall_mem_cons.2 ⟨subd7_5_160, List.forall_mem_cons.2 ⟨subd7_5_161, List.forall_mem_cons.2 ⟨subd7_5_162, List.forall_mem_cons.2 ⟨subd7_5_163, List.forall_mem_cons.2 ⟨subd7_5_164, List.forall_mem_cons.2 ⟨subd7_5_165, List.forall_mem_cons.2 ⟨subd7_5_166, List.forall_mem_cons.2 ⟨subd7_5_167, List.forall_mem_cons.2 ⟨subd7_5_168, List.forall_mem_cons.2 ⟨subd7_5_169, List.forall_mem_cons.2 ⟨subd7_5_170, List.forall_mem_cons.2 ⟨subd7_5_171, List.forall_mem_cons.2 ⟨subd7_5_172, List.forall_mem_cons.2 ⟨subd7_5_173, List.forall_mem_cons.2 ⟨subd7_5_174, List.forall_mem_cons.2 ⟨subd7_5_175, List.forall_mem_cons.2 ⟨subd7_5_176, List.forall_mem_cons.2 ⟨subd7_5_177, List.forall_mem_cons.2 ⟨subd7_5_178, List.forall_mem_cons.2 ⟨subd7_5_179, List.forall_mem_cons.2 ⟨subd7_5_180, List.forall_mem_cons.2 ⟨subd7_5_181, List.forall_mem_cons.2 ⟨subd7_5_182, List.forall_mem_cons.2 ⟨subd7_5_183, List.forall_mem_cons.2 ⟨subd7_5_184, List.forall_mem_cons.2 ⟨subd7_5_185, List.forall_mem_cons.2 ⟨subd7_5_186, List.forall_mem_cons.2 ⟨subd7_5_187, List.forall_mem_cons.2 ⟨subd7_5_188, List.forall_mem_cons.2 ⟨subd7_5_189, List.forall_mem_cons.2 ⟨subd7_5_190, List.forall_mem_cons.2 ⟨subd7_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_192 : subd7_5 [1, -1, 1] = true := by decide +kernel
theorem subd7_5_193 : subd7_5 [1, -1, 2] = true := by decide +kernel
theorem subd7_5_194 : subd7_5 [1, -1, 3] = true := by decide +kernel
theorem subd7_5_195 : subd7_5 [1, -1, 4] = true := by decide +kernel
theorem subd7_5_196 : subd7_5 [1, -1, 5] = true := by decide +kernel
theorem subd7_5_197 : subd7_5 [1, -1, 6] = true := by decide +kernel
theorem subd7_5_198 : subd7_5 [1, -1, 7] = true := by decide +kernel
theorem subd7_5_199 : subd7_5 [1, -1, 8] = true := by decide +kernel
theorem subd7_5_200 : subd7_5 [1, -1, 9] = true := by decide +kernel
theorem subd7_5_201 : subd7_5 [1, -1, 10] = true := by decide +kernel
theorem subd7_5_202 : subd7_5 [1, 0, -18] = true := by decide +kernel
theorem subd7_5_203 : subd7_5 [1, 0, -17] = true := by decide +kernel
theorem subd7_5_204 : subd7_5 [1, 0, -16] = true := by decide +kernel
theorem subd7_5_205 : subd7_5 [1, 0, -15] = true := by decide +kernel
theorem subd7_5_206 : subd7_5 [1, 0, -14] = true := by decide +kernel
theorem subd7_5_207 : subd7_5 [1, 0, -13] = true := by decide +kernel
theorem subd7_5_208 : subd7_5 [1, 0, -12] = true := by decide +kernel
theorem subd7_5_209 : subd7_5 [1, 0, -11] = true := by decide +kernel
theorem subd7_5_210 : subd7_5 [1, 0, -10] = true := by decide +kernel
theorem subd7_5_211 : subd7_5 [1, 0, -9] = true := by decide +kernel
theorem subd7_5_212 : subd7_5 [1, 0, -8] = true := by decide +kernel
theorem subd7_5_213 : subd7_5 [1, 0, -7] = true := by decide +kernel
theorem subd7_5_214 : subd7_5 [1, 0, -6] = true := by decide +kernel
theorem subd7_5_215 : subd7_5 [1, 0, -5] = true := by decide +kernel
theorem subd7_5_216 : subd7_5 [1, 0, -4] = true := by decide +kernel
theorem subd7_5_217 : subd7_5 [1, 0, -3] = true := by decide +kernel
theorem subd7_5_218 : subd7_5 [1, 0, -2] = true := by decide +kernel
theorem subd7_5_219 : subd7_5 [1, 0, -1] = true := by decide +kernel
theorem subd7_5_220 : subd7_5 [1, 0, 0] = true := by decide +kernel
theorem subd7_5_221 : subd7_5 [1, 0, 1] = true := by decide +kernel
theorem subd7_5_222 : subd7_5 [1, 0, 2] = true := by decide +kernel
theorem subd7_5_223 : subd7_5 [1, 0, 3] = true := by decide +kernel
theorem sbd7_5_6 : ∀ q ∈ blkd7_5_6, subd7_5 q = true := by
  unfold blkd7_5_6
  exact List.forall_mem_cons.2 ⟨subd7_5_192, List.forall_mem_cons.2 ⟨subd7_5_193, List.forall_mem_cons.2 ⟨subd7_5_194, List.forall_mem_cons.2 ⟨subd7_5_195, List.forall_mem_cons.2 ⟨subd7_5_196, List.forall_mem_cons.2 ⟨subd7_5_197, List.forall_mem_cons.2 ⟨subd7_5_198, List.forall_mem_cons.2 ⟨subd7_5_199, List.forall_mem_cons.2 ⟨subd7_5_200, List.forall_mem_cons.2 ⟨subd7_5_201, List.forall_mem_cons.2 ⟨subd7_5_202, List.forall_mem_cons.2 ⟨subd7_5_203, List.forall_mem_cons.2 ⟨subd7_5_204, List.forall_mem_cons.2 ⟨subd7_5_205, List.forall_mem_cons.2 ⟨subd7_5_206, List.forall_mem_cons.2 ⟨subd7_5_207, List.forall_mem_cons.2 ⟨subd7_5_208, List.forall_mem_cons.2 ⟨subd7_5_209, List.forall_mem_cons.2 ⟨subd7_5_210, List.forall_mem_cons.2 ⟨subd7_5_211, List.forall_mem_cons.2 ⟨subd7_5_212, List.forall_mem_cons.2 ⟨subd7_5_213, List.forall_mem_cons.2 ⟨subd7_5_214, List.forall_mem_cons.2 ⟨subd7_5_215, List.forall_mem_cons.2 ⟨subd7_5_216, List.forall_mem_cons.2 ⟨subd7_5_217, List.forall_mem_cons.2 ⟨subd7_5_218, List.forall_mem_cons.2 ⟨subd7_5_219, List.forall_mem_cons.2 ⟨subd7_5_220, List.forall_mem_cons.2 ⟨subd7_5_221, List.forall_mem_cons.2 ⟨subd7_5_222, List.forall_mem_cons.2 ⟨subd7_5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_224 : subd7_5 [1, 0, 4] = true := by decide +kernel
theorem subd7_5_225 : subd7_5 [1, 0, 5] = true := by decide +kernel
theorem subd7_5_226 : subd7_5 [1, 0, 6] = true := by decide +kernel
theorem subd7_5_227 : subd7_5 [1, 0, 7] = true := by decide +kernel
theorem subd7_5_228 : subd7_5 [1, 0, 8] = true := by decide +kernel
theorem subd7_5_229 : subd7_5 [1, 0, 9] = true := by decide +kernel
theorem subd7_5_230 : subd7_5 [1, 0, 10] = true := by decide +kernel
theorem subd7_5_231 : subd7_5 [1, 0, 11] = true := by decide +kernel
theorem subd7_5_232 : subd7_5 [1, 0, 12] = true := by decide +kernel
theorem subd7_5_233 : subd7_5 [1, 0, 13] = true := by decide +kernel
theorem subd7_5_234 : subd7_5 [1, 0, 14] = true := by decide +kernel
theorem subd7_5_235 : subd7_5 [1, 0, 15] = true := by decide +kernel
theorem subd7_5_236 : subd7_5 [1, 0, 16] = true := by decide +kernel
theorem subd7_5_237 : subd7_5 [1, 0, 17] = true := by decide +kernel
theorem subd7_5_238 : subd7_5 [1, 0, 18] = true := by decide +kernel
theorem sbd7_5_7 : ∀ q ∈ blkd7_5_7, subd7_5 q = true := by
  unfold blkd7_5_7
  exact List.forall_mem_cons.2 ⟨subd7_5_224, List.forall_mem_cons.2 ⟨subd7_5_225, List.forall_mem_cons.2 ⟨subd7_5_226, List.forall_mem_cons.2 ⟨subd7_5_227, List.forall_mem_cons.2 ⟨subd7_5_228, List.forall_mem_cons.2 ⟨subd7_5_229, List.forall_mem_cons.2 ⟨subd7_5_230, List.forall_mem_cons.2 ⟨subd7_5_231, List.forall_mem_cons.2 ⟨subd7_5_232, List.forall_mem_cons.2 ⟨subd7_5_233, List.forall_mem_cons.2 ⟨subd7_5_234, List.forall_mem_cons.2 ⟨subd7_5_235, List.forall_mem_cons.2 ⟨subd7_5_236, List.forall_mem_cons.2 ⟨subd7_5_237, List.forall_mem_cons.2 ⟨subd7_5_238, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_6 : ldCheck G d7_6.U d7_6.ms ldd7_6 = true := by decide +kernel
theorem pre_okd7_6 : subPre G cell7 d7_6 = true := by decide +kernel
theorem subd7_6_0 : subd7_6 [-4] = true := by decide +kernel
theorem subd7_6_1 : subd7_6 [-3, -4] = true := by decide +kernel
theorem subd7_6_2 : subd7_6 [-3, -3] = true := by decide +kernel
theorem subd7_6_3 : subd7_6 [-3, -2] = true := by decide +kernel
theorem subd7_6_4 : subd7_6 [-3, -1] = true := by decide +kernel
theorem subd7_6_5 : subd7_6 [-3, 0] = true := by decide +kernel
theorem subd7_6_6 : subd7_6 [-3, 1] = true := by decide +kernel
theorem subd7_6_7 : subd7_6 [-3, 2] = true := by decide +kernel
theorem subd7_6_8 : subd7_6 [-3, 3] = true := by decide +kernel
theorem subd7_6_9 : subd7_6 [-2, -4] = true := by decide +kernel
theorem subd7_6_10 : subd7_6 [-2, -3] = true := by decide +kernel
theorem subd7_6_11 : subd7_6 [-2, -2] = true := by decide +kernel
theorem subd7_6_12 : subd7_6 [-2, -1] = true := by decide +kernel
theorem subd7_6_13 : subd7_6 [-2, 0] = true := by decide +kernel
theorem subd7_6_14 : subd7_6 [-2, 1] = true := by decide +kernel
theorem subd7_6_15 : subd7_6 [-2, 2] = true := by decide +kernel
theorem subd7_6_16 : subd7_6 [-2, 3] = true := by decide +kernel
theorem subd7_6_17 : subd7_6 [-2, 4] = true := by decide +kernel
theorem subd7_6_18 : subd7_6 [-1, -5] = true := by decide +kernel
theorem subd7_6_19 : subd7_6 [-1, -4] = true := by decide +kernel
theorem subd7_6_20 : subd7_6 [-1, -3] = true := by decide +kernel
theorem subd7_6_21 : subd7_6 [-1, -2] = true := by decide +kernel
theorem subd7_6_22 : subd7_6 [-1, -1] = true := by decide +kernel
theorem subd7_6_23 : subd7_6 [-1, 0] = true := by decide +kernel
theorem subd7_6_24 : subd7_6 [-1, 1] = true := by decide +kernel
theorem subd7_6_25 : subd7_6 [-1, 2] = true := by decide +kernel
theorem subd7_6_26 : subd7_6 [-1, 3] = true := by decide +kernel
theorem subd7_6_27 : subd7_6 [-1, 4] = true := by decide +kernel
theorem subd7_6_28 : subd7_6 [0, -5] = true := by decide +kernel
theorem subd7_6_29 : subd7_6 [0, -4] = true := by decide +kernel
theorem subd7_6_30 : subd7_6 [0, -3] = true := by decide +kernel
theorem subd7_6_31 : subd7_6 [0, -2] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_cons.2 ⟨subd7_6_1, List.forall_mem_cons.2 ⟨subd7_6_2, List.forall_mem_cons.2 ⟨subd7_6_3, List.forall_mem_cons.2 ⟨subd7_6_4, List.forall_mem_cons.2 ⟨subd7_6_5, List.forall_mem_cons.2 ⟨subd7_6_6, List.forall_mem_cons.2 ⟨subd7_6_7, List.forall_mem_cons.2 ⟨subd7_6_8, List.forall_mem_cons.2 ⟨subd7_6_9, List.forall_mem_cons.2 ⟨subd7_6_10, List.forall_mem_cons.2 ⟨subd7_6_11, List.forall_mem_cons.2 ⟨subd7_6_12, List.forall_mem_cons.2 ⟨subd7_6_13, List.forall_mem_cons.2 ⟨subd7_6_14, List.forall_mem_cons.2 ⟨subd7_6_15, List.forall_mem_cons.2 ⟨subd7_6_16, List.forall_mem_cons.2 ⟨subd7_6_17, List.forall_mem_cons.2 ⟨subd7_6_18, List.forall_mem_cons.2 ⟨subd7_6_19, List.forall_mem_cons.2 ⟨subd7_6_20, List.forall_mem_cons.2 ⟨subd7_6_21, List.forall_mem_cons.2 ⟨subd7_6_22, List.forall_mem_cons.2 ⟨subd7_6_23, List.forall_mem_cons.2 ⟨subd7_6_24, List.forall_mem_cons.2 ⟨subd7_6_25, List.forall_mem_cons.2 ⟨subd7_6_26, List.forall_mem_cons.2 ⟨subd7_6_27, List.forall_mem_cons.2 ⟨subd7_6_28, List.forall_mem_cons.2 ⟨subd7_6_29, List.forall_mem_cons.2 ⟨subd7_6_30, List.forall_mem_cons.2 ⟨subd7_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_32 : subd7_6 [0, -1] = true := by decide +kernel
theorem subd7_6_33 : subd7_6 [0, 0] = true := by decide +kernel
theorem subd7_6_34 : subd7_6 [0, 1] = true := by decide +kernel
theorem subd7_6_35 : subd7_6 [0, 2] = true := by decide +kernel
theorem subd7_6_36 : subd7_6 [0, 3] = true := by decide +kernel
theorem subd7_6_37 : subd7_6 [0, 4] = true := by decide +kernel
theorem subd7_6_38 : subd7_6 [1, -5] = true := by decide +kernel
theorem subd7_6_39 : subd7_6 [1, -4] = true := by decide +kernel
theorem subd7_6_40 : subd7_6 [1, -3] = true := by decide +kernel
theorem subd7_6_41 : subd7_6 [1, -2] = true := by decide +kernel
theorem subd7_6_42 : subd7_6 [1, -1] = true := by decide +kernel
theorem subd7_6_43 : subd7_6 [1, 0] = true := by decide +kernel
theorem subd7_6_44 : subd7_6 [1, 1] = true := by decide +kernel
theorem subd7_6_45 : subd7_6 [1, 2] = true := by decide +kernel
theorem subd7_6_46 : subd7_6 [1, 3] = true := by decide +kernel
theorem subd7_6_47 : subd7_6 [1, 4] = true := by decide +kernel
theorem subd7_6_48 : subd7_6 [2, -5] = true := by decide +kernel
theorem subd7_6_49 : subd7_6 [2, -4] = true := by decide +kernel
theorem subd7_6_50 : subd7_6 [2, -3] = true := by decide +kernel
theorem subd7_6_51 : subd7_6 [2, -2] = true := by decide +kernel
theorem subd7_6_52 : subd7_6 [2, -1] = true := by decide +kernel
theorem subd7_6_53 : subd7_6 [2, 0] = true := by decide +kernel
theorem subd7_6_54 : subd7_6 [2, 1] = true := by decide +kernel
theorem subd7_6_55 : subd7_6 [2, 2] = true := by decide +kernel
theorem subd7_6_56 : subd7_6 [2, 3] = true := by decide +kernel
theorem subd7_6_57 : subd7_6 [3, -4] = true := by decide +kernel
theorem subd7_6_58 : subd7_6 [3, -3] = true := by decide +kernel
theorem subd7_6_59 : subd7_6 [3, -2] = true := by decide +kernel
theorem subd7_6_60 : subd7_6 [3, -1] = true := by decide +kernel
theorem subd7_6_61 : subd7_6 [3, 0] = true := by decide +kernel
theorem subd7_6_62 : subd7_6 [3, 1] = true := by decide +kernel
theorem subd7_6_63 : subd7_6 [3, 2] = true := by decide +kernel
theorem sbd7_6_1 : ∀ q ∈ blkd7_6_1, subd7_6 q = true := by
  unfold blkd7_6_1
  exact List.forall_mem_cons.2 ⟨subd7_6_32, List.forall_mem_cons.2 ⟨subd7_6_33, List.forall_mem_cons.2 ⟨subd7_6_34, List.forall_mem_cons.2 ⟨subd7_6_35, List.forall_mem_cons.2 ⟨subd7_6_36, List.forall_mem_cons.2 ⟨subd7_6_37, List.forall_mem_cons.2 ⟨subd7_6_38, List.forall_mem_cons.2 ⟨subd7_6_39, List.forall_mem_cons.2 ⟨subd7_6_40, List.forall_mem_cons.2 ⟨subd7_6_41, List.forall_mem_cons.2 ⟨subd7_6_42, List.forall_mem_cons.2 ⟨subd7_6_43, List.forall_mem_cons.2 ⟨subd7_6_44, List.forall_mem_cons.2 ⟨subd7_6_45, List.forall_mem_cons.2 ⟨subd7_6_46, List.forall_mem_cons.2 ⟨subd7_6_47, List.forall_mem_cons.2 ⟨subd7_6_48, List.forall_mem_cons.2 ⟨subd7_6_49, List.forall_mem_cons.2 ⟨subd7_6_50, List.forall_mem_cons.2 ⟨subd7_6_51, List.forall_mem_cons.2 ⟨subd7_6_52, List.forall_mem_cons.2 ⟨subd7_6_53, List.forall_mem_cons.2 ⟨subd7_6_54, List.forall_mem_cons.2 ⟨subd7_6_55, List.forall_mem_cons.2 ⟨subd7_6_56, List.forall_mem_cons.2 ⟨subd7_6_57, List.forall_mem_cons.2 ⟨subd7_6_58, List.forall_mem_cons.2 ⟨subd7_6_59, List.forall_mem_cons.2 ⟨subd7_6_60, List.forall_mem_cons.2 ⟨subd7_6_61, List.forall_mem_cons.2 ⟨subd7_6_62, List.forall_mem_cons.2 ⟨subd7_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_64 : subd7_6 [3, 3] = true := by decide +kernel
theorem subd7_6_65 : subd7_6 [4] = true := by decide +kernel
theorem sbd7_6_2 : ∀ q ∈ blkd7_6_2, subd7_6 q = true := by
  unfold blkd7_6_2
  exact List.forall_mem_cons.2 ⟨subd7_6_64, List.forall_mem_cons.2 ⟨subd7_6_65, List.forall_mem_nil _⟩⟩

end ReflectZphi.Data.Cert5.C135
