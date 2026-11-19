import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_3_224 : subd5_3 [1, 1, 1] = true := by decide +kernel
theorem subd5_3_225 : subd5_3 [1, 1, 2] = true := by decide +kernel
theorem subd5_3_226 : subd5_3 [1, 1, 3] = true := by decide +kernel
theorem subd5_3_227 : subd5_3 [1, 1, 4] = true := by decide +kernel
theorem subd5_3_228 : subd5_3 [1, 1, 5] = true := by decide +kernel
theorem subd5_3_229 : subd5_3 [1, 2] = true := by decide +kernel
theorem subd5_3_230 : subd5_3 [1, 3] = true := by decide +kernel
theorem subd5_3_231 : subd5_3 [1, 4] = true := by decide +kernel
theorem subd5_3_232 : subd5_3 [1, 5] = true := by decide +kernel
theorem subd5_3_233 : subd5_3 [2, -7] = true := by decide +kernel
theorem subd5_3_234 : subd5_3 [2, -6] = true := by decide +kernel
theorem subd5_3_235 : subd5_3 [2, -5] = true := by decide +kernel
theorem subd5_3_236 : subd5_3 [2, -4] = true := by decide +kernel
theorem subd5_3_237 : subd5_3 [2, -3] = true := by decide +kernel
theorem subd5_3_238 : subd5_3 [2, -2] = true := by decide +kernel
theorem subd5_3_239 : subd5_3 [2, -1] = true := by decide +kernel
theorem subd5_3_240 : subd5_3 [2, 0] = true := by decide +kernel
theorem subd5_3_241 : subd5_3 [2, 1] = true := by decide +kernel
theorem subd5_3_242 : subd5_3 [2, 2] = true := by decide +kernel
theorem subd5_3_243 : subd5_3 [2, 3] = true := by decide +kernel
theorem subd5_3_244 : subd5_3 [2, 4] = true := by decide +kernel
theorem subd5_3_245 : subd5_3 [3, -6] = true := by decide +kernel
theorem subd5_3_246 : subd5_3 [3, -5] = true := by decide +kernel
theorem subd5_3_247 : subd5_3 [3, -4] = true := by decide +kernel
theorem subd5_3_248 : subd5_3 [3, -3] = true := by decide +kernel
theorem subd5_3_249 : subd5_3 [3, -2] = true := by decide +kernel
theorem subd5_3_250 : subd5_3 [3, -1] = true := by decide +kernel
theorem subd5_3_251 : subd5_3 [3, 0] = true := by decide +kernel
theorem subd5_3_252 : subd5_3 [3, 1] = true := by decide +kernel
theorem subd5_3_253 : subd5_3 [3, 2] = true := by decide +kernel
theorem subd5_3_254 : subd5_3 [3, 3] = true := by decide +kernel
theorem subd5_3_255 : subd5_3 [4, -6] = true := by decide +kernel
theorem sbd5_3_7 : ∀ q ∈ blkd5_3_7, subd5_3 q = true := by
  unfold blkd5_3_7
  exact List.forall_mem_cons.2 ⟨subd5_3_224, List.forall_mem_cons.2 ⟨subd5_3_225, List.forall_mem_cons.2 ⟨subd5_3_226, List.forall_mem_cons.2 ⟨subd5_3_227, List.forall_mem_cons.2 ⟨subd5_3_228, List.forall_mem_cons.2 ⟨subd5_3_229, List.forall_mem_cons.2 ⟨subd5_3_230, List.forall_mem_cons.2 ⟨subd5_3_231, List.forall_mem_cons.2 ⟨subd5_3_232, List.forall_mem_cons.2 ⟨subd5_3_233, List.forall_mem_cons.2 ⟨subd5_3_234, List.forall_mem_cons.2 ⟨subd5_3_235, List.forall_mem_cons.2 ⟨subd5_3_236, List.forall_mem_cons.2 ⟨subd5_3_237, List.forall_mem_cons.2 ⟨subd5_3_238, List.forall_mem_cons.2 ⟨subd5_3_239, List.forall_mem_cons.2 ⟨subd5_3_240, List.forall_mem_cons.2 ⟨subd5_3_241, List.forall_mem_cons.2 ⟨subd5_3_242, List.forall_mem_cons.2 ⟨subd5_3_243, List.forall_mem_cons.2 ⟨subd5_3_244, List.forall_mem_cons.2 ⟨subd5_3_245, List.forall_mem_cons.2 ⟨subd5_3_246, List.forall_mem_cons.2 ⟨subd5_3_247, List.forall_mem_cons.2 ⟨subd5_3_248, List.forall_mem_cons.2 ⟨subd5_3_249, List.forall_mem_cons.2 ⟨subd5_3_250, List.forall_mem_cons.2 ⟨subd5_3_251, List.forall_mem_cons.2 ⟨subd5_3_252, List.forall_mem_cons.2 ⟨subd5_3_253, List.forall_mem_cons.2 ⟨subd5_3_254, List.forall_mem_cons.2 ⟨subd5_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_256 : subd5_3 [4, -5] = true := by decide +kernel
theorem subd5_3_257 : subd5_3 [4, -4] = true := by decide +kernel
theorem subd5_3_258 : subd5_3 [4, -3] = true := by decide +kernel
theorem subd5_3_259 : subd5_3 [4, -2] = true := by decide +kernel
theorem subd5_3_260 : subd5_3 [4, -1] = true := by decide +kernel
theorem subd5_3_261 : subd5_3 [4, 0] = true := by decide +kernel
theorem subd5_3_262 : subd5_3 [4, 1] = true := by decide +kernel
theorem subd5_3_263 : subd5_3 [4, 2] = true := by decide +kernel
theorem subd5_3_264 : subd5_3 [5] = true := by decide +kernel
theorem sbd5_3_8 : ∀ q ∈ blkd5_3_8, subd5_3 q = true := by
  unfold blkd5_3_8
  exact List.forall_mem_cons.2 ⟨subd5_3_256, List.forall_mem_cons.2 ⟨subd5_3_257, List.forall_mem_cons.2 ⟨subd5_3_258, List.forall_mem_cons.2 ⟨subd5_3_259, List.forall_mem_cons.2 ⟨subd5_3_260, List.forall_mem_cons.2 ⟨subd5_3_261, List.forall_mem_cons.2 ⟨subd5_3_262, List.forall_mem_cons.2 ⟨subd5_3_263, List.forall_mem_cons.2 ⟨subd5_3_264, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel
theorem subd5_4_0 : subd5_4 [-6] = true := by decide +kernel
theorem subd5_4_1 : subd5_4 [-5, -4] = true := by decide +kernel
theorem subd5_4_2 : subd5_4 [-5, -3] = true := by decide +kernel
theorem subd5_4_3 : subd5_4 [-5, -2] = true := by decide +kernel
theorem subd5_4_4 : subd5_4 [-5, -1] = true := by decide +kernel
theorem subd5_4_5 : subd5_4 [-5, 0] = true := by decide +kernel
theorem subd5_4_6 : subd5_4 [-5, 1] = true := by decide +kernel
theorem subd5_4_7 : subd5_4 [-5, 2] = true := by decide +kernel
theorem subd5_4_8 : subd5_4 [-5, 3] = true := by decide +kernel
theorem subd5_4_9 : subd5_4 [-4, -5] = true := by decide +kernel
theorem subd5_4_10 : subd5_4 [-4, -4] = true := by decide +kernel
theorem subd5_4_11 : subd5_4 [-4, -3] = true := by decide +kernel
theorem subd5_4_12 : subd5_4 [-4, -2] = true := by decide +kernel
theorem subd5_4_13 : subd5_4 [-4, -1] = true := by decide +kernel
theorem subd5_4_14 : subd5_4 [-4, 0] = true := by decide +kernel
theorem subd5_4_15 : subd5_4 [-4, 1] = true := by decide +kernel
theorem subd5_4_16 : subd5_4 [-4, 2] = true := by decide +kernel
theorem subd5_4_17 : subd5_4 [-4, 3] = true := by decide +kernel
theorem subd5_4_18 : subd5_4 [-4, 4] = true := by decide +kernel
theorem subd5_4_19 : subd5_4 [-3, -6] = true := by decide +kernel
theorem subd5_4_20 : subd5_4 [-3, -5] = true := by decide +kernel
theorem subd5_4_21 : subd5_4 [-3, -4] = true := by decide +kernel
theorem subd5_4_22 : subd5_4 [-3, -3] = true := by decide +kernel
theorem subd5_4_23 : subd5_4 [-3, -2] = true := by decide +kernel
theorem subd5_4_24 : subd5_4 [-3, -1] = true := by decide +kernel
theorem subd5_4_25 : subd5_4 [-3, 0] = true := by decide +kernel
theorem subd5_4_26 : subd5_4 [-3, 1] = true := by decide +kernel
theorem subd5_4_27 : subd5_4 [-3, 2] = true := by decide +kernel
theorem subd5_4_28 : subd5_4 [-3, 3] = true := by decide +kernel
theorem subd5_4_29 : subd5_4 [-3, 4] = true := by decide +kernel
theorem subd5_4_30 : subd5_4 [-3, 5] = true := by decide +kernel
theorem subd5_4_31 : subd5_4 [-2, -6] = true := by decide +kernel
theorem sbd5_4_0 : ∀ q ∈ blkd5_4_0, subd5_4 q = true := by
  unfold blkd5_4_0
  exact List.forall_mem_cons.2 ⟨subd5_4_0, List.forall_mem_cons.2 ⟨subd5_4_1, List.forall_mem_cons.2 ⟨subd5_4_2, List.forall_mem_cons.2 ⟨subd5_4_3, List.forall_mem_cons.2 ⟨subd5_4_4, List.forall_mem_cons.2 ⟨subd5_4_5, List.forall_mem_cons.2 ⟨subd5_4_6, List.forall_mem_cons.2 ⟨subd5_4_7, List.forall_mem_cons.2 ⟨subd5_4_8, List.forall_mem_cons.2 ⟨subd5_4_9, List.forall_mem_cons.2 ⟨subd5_4_10, List.forall_mem_cons.2 ⟨subd5_4_11, List.forall_mem_cons.2 ⟨subd5_4_12, List.forall_mem_cons.2 ⟨subd5_4_13, List.forall_mem_cons.2 ⟨subd5_4_14, List.forall_mem_cons.2 ⟨subd5_4_15, List.forall_mem_cons.2 ⟨subd5_4_16, List.forall_mem_cons.2 ⟨subd5_4_17, List.forall_mem_cons.2 ⟨subd5_4_18, List.forall_mem_cons.2 ⟨subd5_4_19, List.forall_mem_cons.2 ⟨subd5_4_20, List.forall_mem_cons.2 ⟨subd5_4_21, List.forall_mem_cons.2 ⟨subd5_4_22, List.forall_mem_cons.2 ⟨subd5_4_23, List.forall_mem_cons.2 ⟨subd5_4_24, List.forall_mem_cons.2 ⟨subd5_4_25, List.forall_mem_cons.2 ⟨subd5_4_26, List.forall_mem_cons.2 ⟨subd5_4_27, List.forall_mem_cons.2 ⟨subd5_4_28, List.forall_mem_cons.2 ⟨subd5_4_29, List.forall_mem_cons.2 ⟨subd5_4_30, List.forall_mem_cons.2 ⟨subd5_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
