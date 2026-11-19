import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_7_160 : subd4_7 [0, 2, -4] = true := by decide +kernel
theorem subd4_7_161 : subd4_7 [0, 2, -3] = true := by decide +kernel
theorem subd4_7_162 : subd4_7 [0, 2, -2] = true := by decide +kernel
theorem subd4_7_163 : subd4_7 [0, 2, -1] = true := by decide +kernel
theorem subd4_7_164 : subd4_7 [0, 2, 0] = true := by decide +kernel
theorem subd4_7_165 : subd4_7 [0, 2, 1] = true := by decide +kernel
theorem subd4_7_166 : subd4_7 [0, 2, 2] = true := by decide +kernel
theorem subd4_7_167 : subd4_7 [0, 2, 3] = true := by decide +kernel
theorem subd4_7_168 : subd4_7 [0, 2, 4] = true := by decide +kernel
theorem subd4_7_169 : subd4_7 [0, 2, 5] = true := by decide +kernel
theorem subd4_7_170 : subd4_7 [0, 2, 6] = true := by decide +kernel
theorem subd4_7_171 : subd4_7 [0, 2, 7] = true := by decide +kernel
theorem subd4_7_172 : subd4_7 [0, 2, 8] = true := by decide +kernel
theorem subd4_7_173 : subd4_7 [0, 3] = true := by decide +kernel
theorem subd4_7_174 : subd4_7 [0, 4] = true := by decide +kernel
theorem subd4_7_175 : subd4_7 [1, -5] = true := by decide +kernel
theorem subd4_7_176 : subd4_7 [1, -4] = true := by decide +kernel
theorem subd4_7_177 : subd4_7 [1, -3] = true := by decide +kernel
theorem subd4_7_178 : subd4_7 [1, -2, -9] = true := by decide +kernel
theorem subd4_7_179 : subd4_7 [1, -2, -8] = true := by decide +kernel
theorem subd4_7_180 : subd4_7 [1, -2, -7] = true := by decide +kernel
theorem subd4_7_181 : subd4_7 [1, -2, -6] = true := by decide +kernel
theorem subd4_7_182 : subd4_7 [1, -2, -5] = true := by decide +kernel
theorem subd4_7_183 : subd4_7 [1, -2, -4] = true := by decide +kernel
theorem subd4_7_184 : subd4_7 [1, -2, -3] = true := by decide +kernel
theorem subd4_7_185 : subd4_7 [1, -2, -2] = true := by decide +kernel
theorem subd4_7_186 : subd4_7 [1, -2, -1] = true := by decide +kernel
theorem subd4_7_187 : subd4_7 [1, -2, 0] = true := by decide +kernel
theorem subd4_7_188 : subd4_7 [1, -2, 1] = true := by decide +kernel
theorem subd4_7_189 : subd4_7 [1, -2, 2] = true := by decide +kernel
theorem subd4_7_190 : subd4_7 [1, -2, 3] = true := by decide +kernel
theorem subd4_7_191 : subd4_7 [1, -2, 4] = true := by decide +kernel
theorem sbd4_7_5 : ∀ q ∈ blkd4_7_5, subd4_7 q = true := by
  unfold blkd4_7_5
  exact List.forall_mem_cons.2 ⟨subd4_7_160, List.forall_mem_cons.2 ⟨subd4_7_161, List.forall_mem_cons.2 ⟨subd4_7_162, List.forall_mem_cons.2 ⟨subd4_7_163, List.forall_mem_cons.2 ⟨subd4_7_164, List.forall_mem_cons.2 ⟨subd4_7_165, List.forall_mem_cons.2 ⟨subd4_7_166, List.forall_mem_cons.2 ⟨subd4_7_167, List.forall_mem_cons.2 ⟨subd4_7_168, List.forall_mem_cons.2 ⟨subd4_7_169, List.forall_mem_cons.2 ⟨subd4_7_170, List.forall_mem_cons.2 ⟨subd4_7_171, List.forall_mem_cons.2 ⟨subd4_7_172, List.forall_mem_cons.2 ⟨subd4_7_173, List.forall_mem_cons.2 ⟨subd4_7_174, List.forall_mem_cons.2 ⟨subd4_7_175, List.forall_mem_cons.2 ⟨subd4_7_176, List.forall_mem_cons.2 ⟨subd4_7_177, List.forall_mem_cons.2 ⟨subd4_7_178, List.forall_mem_cons.2 ⟨subd4_7_179, List.forall_mem_cons.2 ⟨subd4_7_180, List.forall_mem_cons.2 ⟨subd4_7_181, List.forall_mem_cons.2 ⟨subd4_7_182, List.forall_mem_cons.2 ⟨subd4_7_183, List.forall_mem_cons.2 ⟨subd4_7_184, List.forall_mem_cons.2 ⟨subd4_7_185, List.forall_mem_cons.2 ⟨subd4_7_186, List.forall_mem_cons.2 ⟨subd4_7_187, List.forall_mem_cons.2 ⟨subd4_7_188, List.forall_mem_cons.2 ⟨subd4_7_189, List.forall_mem_cons.2 ⟨subd4_7_190, List.forall_mem_cons.2 ⟨subd4_7_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_192 : subd4_7 [1, -2, 5] = true := by decide +kernel
theorem subd4_7_193 : subd4_7 [1, -2, 6] = true := by decide +kernel
theorem subd4_7_194 : subd4_7 [1, -1, -9] = true := by decide +kernel
theorem subd4_7_195 : subd4_7 [1, -1, -8] = true := by decide +kernel
theorem subd4_7_196 : subd4_7 [1, -1, -7] = true := by decide +kernel
theorem subd4_7_197 : subd4_7 [1, -1, -6] = true := by decide +kernel
theorem subd4_7_198 : subd4_7 [1, -1, -5] = true := by decide +kernel
theorem subd4_7_199 : subd4_7 [1, -1, -4] = true := by decide +kernel
theorem subd4_7_200 : subd4_7 [1, -1, -3] = true := by decide +kernel
theorem subd4_7_201 : subd4_7 [1, -1, -2] = true := by decide +kernel
theorem subd4_7_202 : subd4_7 [1, -1, -1] = true := by decide +kernel
theorem subd4_7_203 : subd4_7 [1, -1, 0] = true := by decide +kernel
theorem subd4_7_204 : subd4_7 [1, -1, 1] = true := by decide +kernel
theorem subd4_7_205 : subd4_7 [1, -1, 2] = true := by decide +kernel
theorem subd4_7_206 : subd4_7 [1, -1, 3] = true := by decide +kernel
theorem subd4_7_207 : subd4_7 [1, -1, 4] = true := by decide +kernel
theorem subd4_7_208 : subd4_7 [1, -1, 5] = true := by decide +kernel
theorem subd4_7_209 : subd4_7 [1, -1, 6] = true := by decide +kernel
theorem subd4_7_210 : subd4_7 [1, -1, 7] = true := by decide +kernel
theorem subd4_7_211 : subd4_7 [1, 0, -8] = true := by decide +kernel
theorem subd4_7_212 : subd4_7 [1, 0, -7] = true := by decide +kernel
theorem subd4_7_213 : subd4_7 [1, 0, -6] = true := by decide +kernel
theorem subd4_7_214 : subd4_7 [1, 0, -5] = true := by decide +kernel
theorem subd4_7_215 : subd4_7 [1, 0, -4] = true := by decide +kernel
theorem subd4_7_216 : subd4_7 [1, 0, -3] = true := by decide +kernel
theorem subd4_7_217 : subd4_7 [1, 0, -2] = true := by decide +kernel
theorem subd4_7_218 : subd4_7 [1, 0, -1] = true := by decide +kernel
theorem subd4_7_219 : subd4_7 [1, 0, 0] = true := by decide +kernel
theorem subd4_7_220 : subd4_7 [1, 0, 1] = true := by decide +kernel
theorem subd4_7_221 : subd4_7 [1, 0, 2] = true := by decide +kernel
theorem subd4_7_222 : subd4_7 [1, 0, 3] = true := by decide +kernel
theorem subd4_7_223 : subd4_7 [1, 0, 4] = true := by decide +kernel
theorem sbd4_7_6 : ∀ q ∈ blkd4_7_6, subd4_7 q = true := by
  unfold blkd4_7_6
  exact List.forall_mem_cons.2 ⟨subd4_7_192, List.forall_mem_cons.2 ⟨subd4_7_193, List.forall_mem_cons.2 ⟨subd4_7_194, List.forall_mem_cons.2 ⟨subd4_7_195, List.forall_mem_cons.2 ⟨subd4_7_196, List.forall_mem_cons.2 ⟨subd4_7_197, List.forall_mem_cons.2 ⟨subd4_7_198, List.forall_mem_cons.2 ⟨subd4_7_199, List.forall_mem_cons.2 ⟨subd4_7_200, List.forall_mem_cons.2 ⟨subd4_7_201, List.forall_mem_cons.2 ⟨subd4_7_202, List.forall_mem_cons.2 ⟨subd4_7_203, List.forall_mem_cons.2 ⟨subd4_7_204, List.forall_mem_cons.2 ⟨subd4_7_205, List.forall_mem_cons.2 ⟨subd4_7_206, List.forall_mem_cons.2 ⟨subd4_7_207, List.forall_mem_cons.2 ⟨subd4_7_208, List.forall_mem_cons.2 ⟨subd4_7_209, List.forall_mem_cons.2 ⟨subd4_7_210, List.forall_mem_cons.2 ⟨subd4_7_211, List.forall_mem_cons.2 ⟨subd4_7_212, List.forall_mem_cons.2 ⟨subd4_7_213, List.forall_mem_cons.2 ⟨subd4_7_214, List.forall_mem_cons.2 ⟨subd4_7_215, List.forall_mem_cons.2 ⟨subd4_7_216, List.forall_mem_cons.2 ⟨subd4_7_217, List.forall_mem_cons.2 ⟨subd4_7_218, List.forall_mem_cons.2 ⟨subd4_7_219, List.forall_mem_cons.2 ⟨subd4_7_220, List.forall_mem_cons.2 ⟨subd4_7_221, List.forall_mem_cons.2 ⟨subd4_7_222, List.forall_mem_cons.2 ⟨subd4_7_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_224 : subd4_7 [1, 0, 5] = true := by decide +kernel
theorem subd4_7_225 : subd4_7 [1, 0, 6] = true := by decide +kernel
theorem subd4_7_226 : subd4_7 [1, 0, 7] = true := by decide +kernel
theorem subd4_7_227 : subd4_7 [1, 1, -7] = true := by decide +kernel
theorem subd4_7_228 : subd4_7 [1, 1, -6] = true := by decide +kernel
theorem subd4_7_229 : subd4_7 [1, 1, -5] = true := by decide +kernel
theorem subd4_7_230 : subd4_7 [1, 1, -4] = true := by decide +kernel
theorem subd4_7_231 : subd4_7 [1, 1, -3] = true := by decide +kernel
theorem subd4_7_232 : subd4_7 [1, 1, -2] = true := by decide +kernel
theorem subd4_7_233 : subd4_7 [1, 1, -1] = true := by decide +kernel
theorem subd4_7_234 : subd4_7 [1, 1, 0] = true := by decide +kernel
theorem subd4_7_235 : subd4_7 [1, 1, 1] = true := by decide +kernel
theorem subd4_7_236 : subd4_7 [1, 1, 2] = true := by decide +kernel
theorem subd4_7_237 : subd4_7 [1, 1, 3] = true := by decide +kernel
theorem subd4_7_238 : subd4_7 [1, 1, 4] = true := by decide +kernel
theorem subd4_7_239 : subd4_7 [1, 1, 5] = true := by decide +kernel
theorem subd4_7_240 : subd4_7 [1, 1, 6] = true := by decide +kernel
theorem subd4_7_241 : subd4_7 [1, 1, 7] = true := by decide +kernel
theorem subd4_7_242 : subd4_7 [1, 2] = true := by decide +kernel
theorem subd4_7_243 : subd4_7 [1, 3] = true := by decide +kernel
theorem subd4_7_244 : subd4_7 [1, 4] = true := by decide +kernel
theorem subd4_7_245 : subd4_7 [2, -5] = true := by decide +kernel
theorem subd4_7_246 : subd4_7 [2, -4] = true := by decide +kernel
theorem subd4_7_247 : subd4_7 [2, -3] = true := by decide +kernel
theorem subd4_7_248 : subd4_7 [2, -2] = true := by decide +kernel
theorem subd4_7_249 : subd4_7 [2, -1] = true := by decide +kernel
theorem subd4_7_250 : subd4_7 [2, 0] = true := by decide +kernel
theorem subd4_7_251 : subd4_7 [2, 1] = true := by decide +kernel
theorem subd4_7_252 : subd4_7 [2, 2] = true := by decide +kernel
theorem subd4_7_253 : subd4_7 [2, 3] = true := by decide +kernel
theorem subd4_7_254 : subd4_7 [3, -5] = true := by decide +kernel
theorem subd4_7_255 : subd4_7 [3, -4] = true := by decide +kernel
theorem sbd4_7_7 : ∀ q ∈ blkd4_7_7, subd4_7 q = true := by
  unfold blkd4_7_7
  exact List.forall_mem_cons.2 ⟨subd4_7_224, List.forall_mem_cons.2 ⟨subd4_7_225, List.forall_mem_cons.2 ⟨subd4_7_226, List.forall_mem_cons.2 ⟨subd4_7_227, List.forall_mem_cons.2 ⟨subd4_7_228, List.forall_mem_cons.2 ⟨subd4_7_229, List.forall_mem_cons.2 ⟨subd4_7_230, List.forall_mem_cons.2 ⟨subd4_7_231, List.forall_mem_cons.2 ⟨subd4_7_232, List.forall_mem_cons.2 ⟨subd4_7_233, List.forall_mem_cons.2 ⟨subd4_7_234, List.forall_mem_cons.2 ⟨subd4_7_235, List.forall_mem_cons.2 ⟨subd4_7_236, List.forall_mem_cons.2 ⟨subd4_7_237, List.forall_mem_cons.2 ⟨subd4_7_238, List.forall_mem_cons.2 ⟨subd4_7_239, List.forall_mem_cons.2 ⟨subd4_7_240, List.forall_mem_cons.2 ⟨subd4_7_241, List.forall_mem_cons.2 ⟨subd4_7_242, List.forall_mem_cons.2 ⟨subd4_7_243, List.forall_mem_cons.2 ⟨subd4_7_244, List.forall_mem_cons.2 ⟨subd4_7_245, List.forall_mem_cons.2 ⟨subd4_7_246, List.forall_mem_cons.2 ⟨subd4_7_247, List.forall_mem_cons.2 ⟨subd4_7_248, List.forall_mem_cons.2 ⟨subd4_7_249, List.forall_mem_cons.2 ⟨subd4_7_250, List.forall_mem_cons.2 ⟨subd4_7_251, List.forall_mem_cons.2 ⟨subd4_7_252, List.forall_mem_cons.2 ⟨subd4_7_253, List.forall_mem_cons.2 ⟨subd4_7_254, List.forall_mem_cons.2 ⟨subd4_7_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_256 : subd4_7 [3, -3] = true := by decide +kernel
theorem subd4_7_257 : subd4_7 [3, -2] = true := by decide +kernel
theorem subd4_7_258 : subd4_7 [3, -1] = true := by decide +kernel
theorem subd4_7_259 : subd4_7 [3, 0] = true := by decide +kernel
theorem subd4_7_260 : subd4_7 [3, 1] = true := by decide +kernel
theorem subd4_7_261 : subd4_7 [3, 2] = true := by decide +kernel
theorem subd4_7_262 : subd4_7 [4] = true := by decide +kernel
theorem sbd4_7_8 : ∀ q ∈ blkd4_7_8, subd4_7 q = true := by
  unfold blkd4_7_8
  exact List.forall_mem_cons.2 ⟨subd4_7_256, List.forall_mem_cons.2 ⟨subd4_7_257, List.forall_mem_cons.2 ⟨subd4_7_258, List.forall_mem_cons.2 ⟨subd4_7_259, List.forall_mem_cons.2 ⟨subd4_7_260, List.forall_mem_cons.2 ⟨subd4_7_261, List.forall_mem_cons.2 ⟨subd4_7_262, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-3] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-2] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [-1, -4] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [-1, -3] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [-1, -2] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [-1, -1] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [-1, 0] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [-1, 1] = true := by decide +kernel
theorem subd5_0_8 : subd5_0 [-1, 2] = true := by decide +kernel
theorem subd5_0_9 : subd5_0 [-1, 3] = true := by decide +kernel
theorem subd5_0_10 : subd5_0 [0, -4] = true := by decide +kernel
theorem subd5_0_11 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_12 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_13 : subd5_0 [0, -1] = true := by decide +kernel
theorem subd5_0_14 : subd5_0 [0, 0] = true := by decide +kernel
theorem subd5_0_15 : subd5_0 [0, 1] = true := by decide +kernel
theorem subd5_0_16 : subd5_0 [0, 2] = true := by decide +kernel
theorem subd5_0_17 : subd5_0 [0, 3] = true := by decide +kernel
theorem subd5_0_18 : subd5_0 [1, -4] = true := by decide +kernel
theorem subd5_0_19 : subd5_0 [1, -3] = true := by decide +kernel
theorem subd5_0_20 : subd5_0 [1, -2] = true := by decide +kernel
theorem subd5_0_21 : subd5_0 [1, -1] = true := by decide +kernel
theorem subd5_0_22 : subd5_0 [1, 0] = true := by decide +kernel
theorem subd5_0_23 : subd5_0 [1, 1] = true := by decide +kernel
theorem subd5_0_24 : subd5_0 [1, 2] = true := by decide +kernel
theorem subd5_0_25 : subd5_0 [1, 3] = true := by decide +kernel
theorem subd5_0_26 : subd5_0 [2] = true := by decide +kernel
theorem subd5_0_27 : subd5_0 [3] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_cons.2 ⟨subd5_0_8, List.forall_mem_cons.2 ⟨subd5_0_9, List.forall_mem_cons.2 ⟨subd5_0_10, List.forall_mem_cons.2 ⟨subd5_0_11, List.forall_mem_cons.2 ⟨subd5_0_12, List.forall_mem_cons.2 ⟨subd5_0_13, List.forall_mem_cons.2 ⟨subd5_0_14, List.forall_mem_cons.2 ⟨subd5_0_15, List.forall_mem_cons.2 ⟨subd5_0_16, List.forall_mem_cons.2 ⟨subd5_0_17, List.forall_mem_cons.2 ⟨subd5_0_18, List.forall_mem_cons.2 ⟨subd5_0_19, List.forall_mem_cons.2 ⟨subd5_0_20, List.forall_mem_cons.2 ⟨subd5_0_21, List.forall_mem_cons.2 ⟨subd5_0_22, List.forall_mem_cons.2 ⟨subd5_0_23, List.forall_mem_cons.2 ⟨subd5_0_24, List.forall_mem_cons.2 ⟨subd5_0_25, List.forall_mem_cons.2 ⟨subd5_0_26, List.forall_mem_cons.2 ⟨subd5_0_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [-5, -4] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-5, -3] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [-5, -2] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [-5, -1] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [-5, 0] = true := by decide +kernel
theorem subd5_1_5 : subd5_1 [-5, 1] = true := by decide +kernel
theorem subd5_1_6 : subd5_1 [-5, 2] = true := by decide +kernel
theorem subd5_1_7 : subd5_1 [-4, -5] = true := by decide +kernel
theorem subd5_1_8 : subd5_1 [-4, -4] = true := by decide +kernel
theorem subd5_1_9 : subd5_1 [-4, -3] = true := by decide +kernel
theorem subd5_1_10 : subd5_1 [-4, -2] = true := by decide +kernel
theorem subd5_1_11 : subd5_1 [-4, -1] = true := by decide +kernel
theorem subd5_1_12 : subd5_1 [-4, 0] = true := by decide +kernel
theorem subd5_1_13 : subd5_1 [-4, 1] = true := by decide +kernel
theorem subd5_1_14 : subd5_1 [-4, 2] = true := by decide +kernel
theorem subd5_1_15 : subd5_1 [-4, 3] = true := by decide +kernel
theorem subd5_1_16 : subd5_1 [-4, 4] = true := by decide +kernel
theorem subd5_1_17 : subd5_1 [-3, -6] = true := by decide +kernel
theorem subd5_1_18 : subd5_1 [-3, -5] = true := by decide +kernel
theorem subd5_1_19 : subd5_1 [-3, -4] = true := by decide +kernel
theorem subd5_1_20 : subd5_1 [-3, -3] = true := by decide +kernel
theorem subd5_1_21 : subd5_1 [-3, -2] = true := by decide +kernel
theorem subd5_1_22 : subd5_1 [-3, -1, -8] = true := by decide +kernel
theorem subd5_1_23 : subd5_1 [-3, -1, -7] = true := by decide +kernel
theorem subd5_1_24 : subd5_1 [-3, -1, -6] = true := by decide +kernel
theorem subd5_1_25 : subd5_1 [-3, -1, -5] = true := by decide +kernel
theorem subd5_1_26 : subd5_1 [-3, -1, -4] = true := by decide +kernel
theorem subd5_1_27 : subd5_1 [-3, -1, -3] = true := by decide +kernel
theorem subd5_1_28 : subd5_1 [-3, -1, -2] = true := by decide +kernel
theorem subd5_1_29 : subd5_1 [-3, -1, -1] = true := by decide +kernel
theorem subd5_1_30 : subd5_1 [-3, -1, 0] = true := by decide +kernel
theorem subd5_1_31 : subd5_1 [-3, -1, 1] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_cons.2 ⟨subd5_1_5, List.forall_mem_cons.2 ⟨subd5_1_6, List.forall_mem_cons.2 ⟨subd5_1_7, List.forall_mem_cons.2 ⟨subd5_1_8, List.forall_mem_cons.2 ⟨subd5_1_9, List.forall_mem_cons.2 ⟨subd5_1_10, List.forall_mem_cons.2 ⟨subd5_1_11, List.forall_mem_cons.2 ⟨subd5_1_12, List.forall_mem_cons.2 ⟨subd5_1_13, List.forall_mem_cons.2 ⟨subd5_1_14, List.forall_mem_cons.2 ⟨subd5_1_15, List.forall_mem_cons.2 ⟨subd5_1_16, List.forall_mem_cons.2 ⟨subd5_1_17, List.forall_mem_cons.2 ⟨subd5_1_18, List.forall_mem_cons.2 ⟨subd5_1_19, List.forall_mem_cons.2 ⟨subd5_1_20, List.forall_mem_cons.2 ⟨subd5_1_21, List.forall_mem_cons.2 ⟨subd5_1_22, List.forall_mem_cons.2 ⟨subd5_1_23, List.forall_mem_cons.2 ⟨subd5_1_24, List.forall_mem_cons.2 ⟨subd5_1_25, List.forall_mem_cons.2 ⟨subd5_1_26, List.forall_mem_cons.2 ⟨subd5_1_27, List.forall_mem_cons.2 ⟨subd5_1_28, List.forall_mem_cons.2 ⟨subd5_1_29, List.forall_mem_cons.2 ⟨subd5_1_30, List.forall_mem_cons.2 ⟨subd5_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
