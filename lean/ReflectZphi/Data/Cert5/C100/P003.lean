import ReflectZphi.Data.Cert5.C100.Base

namespace ReflectZphi.Data.Cert5.C100

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_0_192 : subd4_0 [1, -2, -1] = true := by decide +kernel
theorem subd4_0_193 : subd4_0 [1, -2, 0] = true := by decide +kernel
theorem subd4_0_194 : subd4_0 [1, -2, 1] = true := by decide +kernel
theorem subd4_0_195 : subd4_0 [1, -2, 2] = true := by decide +kernel
theorem subd4_0_196 : subd4_0 [1, -2, 3] = true := by decide +kernel
theorem subd4_0_197 : subd4_0 [1, -2, 4] = true := by decide +kernel
theorem subd4_0_198 : subd4_0 [1, -2, 5] = true := by decide +kernel
theorem subd4_0_199 : subd4_0 [1, -2, 6] = true := by decide +kernel
theorem subd4_0_200 : subd4_0 [1, -1, -9] = true := by decide +kernel
theorem subd4_0_201 : subd4_0 [1, -1, -8] = true := by decide +kernel
theorem subd4_0_202 : subd4_0 [1, -1, -7] = true := by decide +kernel
theorem subd4_0_203 : subd4_0 [1, -1, -6] = true := by decide +kernel
theorem subd4_0_204 : subd4_0 [1, -1, -5] = true := by decide +kernel
theorem subd4_0_205 : subd4_0 [1, -1, -4] = true := by decide +kernel
theorem subd4_0_206 : subd4_0 [1, -1, -3] = true := by decide +kernel
theorem subd4_0_207 : subd4_0 [1, -1, -2] = true := by decide +kernel
theorem subd4_0_208 : subd4_0 [1, -1, -1] = true := by decide +kernel
theorem subd4_0_209 : subd4_0 [1, -1, 0] = true := by decide +kernel
theorem subd4_0_210 : subd4_0 [1, -1, 1] = true := by decide +kernel
theorem subd4_0_211 : subd4_0 [1, -1, 2] = true := by decide +kernel
theorem subd4_0_212 : subd4_0 [1, -1, 3] = true := by decide +kernel
theorem subd4_0_213 : subd4_0 [1, -1, 4] = true := by decide +kernel
theorem subd4_0_214 : subd4_0 [1, -1, 5] = true := by decide +kernel
theorem subd4_0_215 : subd4_0 [1, -1, 6] = true := by decide +kernel
theorem subd4_0_216 : subd4_0 [1, 0, -8] = true := by decide +kernel
theorem subd4_0_217 : subd4_0 [1, 0, -7] = true := by decide +kernel
theorem subd4_0_218 : subd4_0 [1, 0, -6] = true := by decide +kernel
theorem subd4_0_219 : subd4_0 [1, 0, -5] = true := by decide +kernel
theorem subd4_0_220 : subd4_0 [1, 0, -4] = true := by decide +kernel
theorem subd4_0_221 : subd4_0 [1, 0, -3] = true := by decide +kernel
theorem subd4_0_222 : subd4_0 [1, 0, -2] = true := by decide +kernel
theorem subd4_0_223 : subd4_0 [1, 0, -1] = true := by decide +kernel
theorem sbd4_0_6 : ∀ q ∈ blkd4_0_6, subd4_0 q = true := by
  unfold blkd4_0_6
  exact List.forall_mem_cons.2 ⟨subd4_0_192, List.forall_mem_cons.2 ⟨subd4_0_193, List.forall_mem_cons.2 ⟨subd4_0_194, List.forall_mem_cons.2 ⟨subd4_0_195, List.forall_mem_cons.2 ⟨subd4_0_196, List.forall_mem_cons.2 ⟨subd4_0_197, List.forall_mem_cons.2 ⟨subd4_0_198, List.forall_mem_cons.2 ⟨subd4_0_199, List.forall_mem_cons.2 ⟨subd4_0_200, List.forall_mem_cons.2 ⟨subd4_0_201, List.forall_mem_cons.2 ⟨subd4_0_202, List.forall_mem_cons.2 ⟨subd4_0_203, List.forall_mem_cons.2 ⟨subd4_0_204, List.forall_mem_cons.2 ⟨subd4_0_205, List.forall_mem_cons.2 ⟨subd4_0_206, List.forall_mem_cons.2 ⟨subd4_0_207, List.forall_mem_cons.2 ⟨subd4_0_208, List.forall_mem_cons.2 ⟨subd4_0_209, List.forall_mem_cons.2 ⟨subd4_0_210, List.forall_mem_cons.2 ⟨subd4_0_211, List.forall_mem_cons.2 ⟨subd4_0_212, List.forall_mem_cons.2 ⟨subd4_0_213, List.forall_mem_cons.2 ⟨subd4_0_214, List.forall_mem_cons.2 ⟨subd4_0_215, List.forall_mem_cons.2 ⟨subd4_0_216, List.forall_mem_cons.2 ⟨subd4_0_217, List.forall_mem_cons.2 ⟨subd4_0_218, List.forall_mem_cons.2 ⟨subd4_0_219, List.forall_mem_cons.2 ⟨subd4_0_220, List.forall_mem_cons.2 ⟨subd4_0_221, List.forall_mem_cons.2 ⟨subd4_0_222, List.forall_mem_cons.2 ⟨subd4_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_0_224 : subd4_0 [1, 0, 0] = true := by decide +kernel
theorem subd4_0_225 : subd4_0 [1, 0, 1] = true := by decide +kernel
theorem subd4_0_226 : subd4_0 [1, 0, 2] = true := by decide +kernel
theorem subd4_0_227 : subd4_0 [1, 0, 3] = true := by decide +kernel
theorem subd4_0_228 : subd4_0 [1, 0, 4] = true := by decide +kernel
theorem subd4_0_229 : subd4_0 [1, 0, 5] = true := by decide +kernel
theorem subd4_0_230 : subd4_0 [1, 0, 6] = true := by decide +kernel
theorem subd4_0_231 : subd4_0 [1, 0, 7] = true := by decide +kernel
theorem subd4_0_232 : subd4_0 [1, 1, -8] = true := by decide +kernel
theorem subd4_0_233 : subd4_0 [1, 1, -7] = true := by decide +kernel
theorem subd4_0_234 : subd4_0 [1, 1, -6] = true := by decide +kernel
theorem subd4_0_235 : subd4_0 [1, 1, -5] = true := by decide +kernel
theorem subd4_0_236 : subd4_0 [1, 1, -4] = true := by decide +kernel
theorem subd4_0_237 : subd4_0 [1, 1, -3] = true := by decide +kernel
theorem subd4_0_238 : subd4_0 [1, 1, -2] = true := by decide +kernel
theorem subd4_0_239 : subd4_0 [1, 1, -1] = true := by decide +kernel
theorem subd4_0_240 : subd4_0 [1, 1, 0] = true := by decide +kernel
theorem subd4_0_241 : subd4_0 [1, 1, 1] = true := by decide +kernel
theorem subd4_0_242 : subd4_0 [1, 1, 2] = true := by decide +kernel
theorem subd4_0_243 : subd4_0 [1, 1, 3] = true := by decide +kernel
theorem subd4_0_244 : subd4_0 [1, 1, 4] = true := by decide +kernel
theorem subd4_0_245 : subd4_0 [1, 1, 5] = true := by decide +kernel
theorem subd4_0_246 : subd4_0 [1, 1, 6] = true := by decide +kernel
theorem subd4_0_247 : subd4_0 [1, 1, 7] = true := by decide +kernel
theorem subd4_0_248 : subd4_0 [1, 2] = true := by decide +kernel
theorem subd4_0_249 : subd4_0 [1, 3] = true := by decide +kernel
theorem subd4_0_250 : subd4_0 [1, 4] = true := by decide +kernel
theorem subd4_0_251 : subd4_0 [2, -6] = true := by decide +kernel
theorem subd4_0_252 : subd4_0 [2, -5] = true := by decide +kernel
theorem subd4_0_253 : subd4_0 [2, -4] = true := by decide +kernel
theorem subd4_0_254 : subd4_0 [2, -3] = true := by decide +kernel
theorem subd4_0_255 : subd4_0 [2, -2] = true := by decide +kernel
theorem sbd4_0_7 : ∀ q ∈ blkd4_0_7, subd4_0 q = true := by
  unfold blkd4_0_7
  exact List.forall_mem_cons.2 ⟨subd4_0_224, List.forall_mem_cons.2 ⟨subd4_0_225, List.forall_mem_cons.2 ⟨subd4_0_226, List.forall_mem_cons.2 ⟨subd4_0_227, List.forall_mem_cons.2 ⟨subd4_0_228, List.forall_mem_cons.2 ⟨subd4_0_229, List.forall_mem_cons.2 ⟨subd4_0_230, List.forall_mem_cons.2 ⟨subd4_0_231, List.forall_mem_cons.2 ⟨subd4_0_232, List.forall_mem_cons.2 ⟨subd4_0_233, List.forall_mem_cons.2 ⟨subd4_0_234, List.forall_mem_cons.2 ⟨subd4_0_235, List.forall_mem_cons.2 ⟨subd4_0_236, List.forall_mem_cons.2 ⟨subd4_0_237, List.forall_mem_cons.2 ⟨subd4_0_238, List.forall_mem_cons.2 ⟨subd4_0_239, List.forall_mem_cons.2 ⟨subd4_0_240, List.forall_mem_cons.2 ⟨subd4_0_241, List.forall_mem_cons.2 ⟨subd4_0_242, List.forall_mem_cons.2 ⟨subd4_0_243, List.forall_mem_cons.2 ⟨subd4_0_244, List.forall_mem_cons.2 ⟨subd4_0_245, List.forall_mem_cons.2 ⟨subd4_0_246, List.forall_mem_cons.2 ⟨subd4_0_247, List.forall_mem_cons.2 ⟨subd4_0_248, List.forall_mem_cons.2 ⟨subd4_0_249, List.forall_mem_cons.2 ⟨subd4_0_250, List.forall_mem_cons.2 ⟨subd4_0_251, List.forall_mem_cons.2 ⟨subd4_0_252, List.forall_mem_cons.2 ⟨subd4_0_253, List.forall_mem_cons.2 ⟨subd4_0_254, List.forall_mem_cons.2 ⟨subd4_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_0_256 : subd4_0 [2, -1] = true := by decide +kernel
theorem subd4_0_257 : subd4_0 [2, 0] = true := by decide +kernel
theorem subd4_0_258 : subd4_0 [2, 1] = true := by decide +kernel
theorem subd4_0_259 : subd4_0 [2, 2] = true := by decide +kernel
theorem subd4_0_260 : subd4_0 [2, 3] = true := by decide +kernel
theorem subd4_0_261 : subd4_0 [3, -6] = true := by decide +kernel
theorem subd4_0_262 : subd4_0 [3, -5] = true := by decide +kernel
theorem subd4_0_263 : subd4_0 [3, -4] = true := by decide +kernel
theorem subd4_0_264 : subd4_0 [3, -3] = true := by decide +kernel
theorem subd4_0_265 : subd4_0 [3, -2] = true := by decide +kernel
theorem subd4_0_266 : subd4_0 [3, -1] = true := by decide +kernel
theorem subd4_0_267 : subd4_0 [3, 0] = true := by decide +kernel
theorem subd4_0_268 : subd4_0 [3, 1] = true := by decide +kernel
theorem subd4_0_269 : subd4_0 [3, 2] = true := by decide +kernel
theorem subd4_0_270 : subd4_0 [4] = true := by decide +kernel
theorem sbd4_0_8 : ∀ q ∈ blkd4_0_8, subd4_0 q = true := by
  unfold blkd4_0_8
  exact List.forall_mem_cons.2 ⟨subd4_0_256, List.forall_mem_cons.2 ⟨subd4_0_257, List.forall_mem_cons.2 ⟨subd4_0_258, List.forall_mem_cons.2 ⟨subd4_0_259, List.forall_mem_cons.2 ⟨subd4_0_260, List.forall_mem_cons.2 ⟨subd4_0_261, List.forall_mem_cons.2 ⟨subd4_0_262, List.forall_mem_cons.2 ⟨subd4_0_263, List.forall_mem_cons.2 ⟨subd4_0_264, List.forall_mem_cons.2 ⟨subd4_0_265, List.forall_mem_cons.2 ⟨subd4_0_266, List.forall_mem_cons.2 ⟨subd4_0_267, List.forall_mem_cons.2 ⟨subd4_0_268, List.forall_mem_cons.2 ⟨subd4_0_269, List.forall_mem_cons.2 ⟨subd4_0_270, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_1_0 : subd4_1 [-2] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [-1, -3] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [-1, -2] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [-1, -1] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [-1, 0] = true := by decide +kernel
theorem subd4_1_5 : subd4_1 [-1, 1] = true := by decide +kernel
theorem subd4_1_6 : subd4_1 [-1, 2] = true := by decide +kernel
theorem subd4_1_7 : subd4_1 [0, -3] = true := by decide +kernel
theorem subd4_1_8 : subd4_1 [0, -2] = true := by decide +kernel
theorem subd4_1_9 : subd4_1 [0, -1] = true := by decide +kernel
theorem subd4_1_10 : subd4_1 [0, 0] = true := by decide +kernel
theorem subd4_1_11 : subd4_1 [0, 1] = true := by decide +kernel
theorem subd4_1_12 : subd4_1 [0, 2] = true := by decide +kernel
theorem subd4_1_13 : subd4_1 [1, -3] = true := by decide +kernel
theorem subd4_1_14 : subd4_1 [1, -2] = true := by decide +kernel
theorem subd4_1_15 : subd4_1 [1, -1] = true := by decide +kernel
theorem subd4_1_16 : subd4_1 [1, 0] = true := by decide +kernel
theorem subd4_1_17 : subd4_1 [1, 1] = true := by decide +kernel
theorem subd4_1_18 : subd4_1 [1, 2] = true := by decide +kernel
theorem subd4_1_19 : subd4_1 [2] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_cons.2 ⟨subd4_1_5, List.forall_mem_cons.2 ⟨subd4_1_6, List.forall_mem_cons.2 ⟨subd4_1_7, List.forall_mem_cons.2 ⟨subd4_1_8, List.forall_mem_cons.2 ⟨subd4_1_9, List.forall_mem_cons.2 ⟨subd4_1_10, List.forall_mem_cons.2 ⟨subd4_1_11, List.forall_mem_cons.2 ⟨subd4_1_12, List.forall_mem_cons.2 ⟨subd4_1_13, List.forall_mem_cons.2 ⟨subd4_1_14, List.forall_mem_cons.2 ⟨subd4_1_15, List.forall_mem_cons.2 ⟨subd4_1_16, List.forall_mem_cons.2 ⟨subd4_1_17, List.forall_mem_cons.2 ⟨subd4_1_18, List.forall_mem_cons.2 ⟨subd4_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_0 : subd5_0 [-5, -4] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-5, -3] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [-5, -2] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [-5, -1] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [-5, 0] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [-5, 1] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [-5, 2] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [-4, -6] = true := by decide +kernel
theorem subd5_0_8 : subd5_0 [-4, -5] = true := by decide +kernel
theorem subd5_0_9 : subd5_0 [-4, -4] = true := by decide +kernel
theorem subd5_0_10 : subd5_0 [-4, -3] = true := by decide +kernel
theorem subd5_0_11 : subd5_0 [-4, -2] = true := by decide +kernel
theorem subd5_0_12 : subd5_0 [-4, -1] = true := by decide +kernel
theorem subd5_0_13 : subd5_0 [-4, 0] = true := by decide +kernel
theorem subd5_0_14 : subd5_0 [-4, 1] = true := by decide +kernel
theorem subd5_0_15 : subd5_0 [-4, 2] = true := by decide +kernel
theorem subd5_0_16 : subd5_0 [-4, 3] = true := by decide +kernel
theorem subd5_0_17 : subd5_0 [-3, -6] = true := by decide +kernel
theorem subd5_0_18 : subd5_0 [-3, -5] = true := by decide +kernel
theorem subd5_0_19 : subd5_0 [-3, -4] = true := by decide +kernel
theorem subd5_0_20 : subd5_0 [-3, -3] = true := by decide +kernel
theorem subd5_0_21 : subd5_0 [-3, -2] = true := by decide +kernel
theorem subd5_0_22 : subd5_0 [-3, -1] = true := by decide +kernel
theorem subd5_0_23 : subd5_0 [-3, 0] = true := by decide +kernel
theorem subd5_0_24 : subd5_0 [-3, 1] = true := by decide +kernel
theorem subd5_0_25 : subd5_0 [-3, 2] = true := by decide +kernel
theorem subd5_0_26 : subd5_0 [-3, 3] = true := by decide +kernel
theorem subd5_0_27 : subd5_0 [-3, 4] = true := by decide +kernel
theorem subd5_0_28 : subd5_0 [-2, -7] = true := by decide +kernel
theorem subd5_0_29 : subd5_0 [-2, -6] = true := by decide +kernel
theorem subd5_0_30 : subd5_0 [-2, -5] = true := by decide +kernel
theorem subd5_0_31 : subd5_0 [-2, -4] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_cons.2 ⟨subd5_0_8, List.forall_mem_cons.2 ⟨subd5_0_9, List.forall_mem_cons.2 ⟨subd5_0_10, List.forall_mem_cons.2 ⟨subd5_0_11, List.forall_mem_cons.2 ⟨subd5_0_12, List.forall_mem_cons.2 ⟨subd5_0_13, List.forall_mem_cons.2 ⟨subd5_0_14, List.forall_mem_cons.2 ⟨subd5_0_15, List.forall_mem_cons.2 ⟨subd5_0_16, List.forall_mem_cons.2 ⟨subd5_0_17, List.forall_mem_cons.2 ⟨subd5_0_18, List.forall_mem_cons.2 ⟨subd5_0_19, List.forall_mem_cons.2 ⟨subd5_0_20, List.forall_mem_cons.2 ⟨subd5_0_21, List.forall_mem_cons.2 ⟨subd5_0_22, List.forall_mem_cons.2 ⟨subd5_0_23, List.forall_mem_cons.2 ⟨subd5_0_24, List.forall_mem_cons.2 ⟨subd5_0_25, List.forall_mem_cons.2 ⟨subd5_0_26, List.forall_mem_cons.2 ⟨subd5_0_27, List.forall_mem_cons.2 ⟨subd5_0_28, List.forall_mem_cons.2 ⟨subd5_0_29, List.forall_mem_cons.2 ⟨subd5_0_30, List.forall_mem_cons.2 ⟨subd5_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C100
