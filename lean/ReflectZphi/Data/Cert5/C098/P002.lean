import ReflectZphi.Data.Cert5.C098.Base

namespace ReflectZphi.Data.Cert5.C098
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_160 : sub5 [0, 2, -6] = true := by decide +kernel
theorem sub5_161 : sub5 [0, 2, -5] = true := by decide +kernel
theorem sub5_162 : sub5 [0, 2, -4] = true := by decide +kernel
theorem sub5_163 : sub5 [0, 2, -3] = true := by decide +kernel
theorem sub5_164 : sub5 [0, 2, -2] = true := by decide +kernel
theorem sub5_165 : sub5 [0, 2, -1] = true := by decide +kernel
theorem sub5_166 : sub5 [0, 2, 0] = true := by decide +kernel
theorem sub5_167 : sub5 [0, 2, 1] = true := by decide +kernel
theorem sub5_168 : sub5 [0, 2, 2] = true := by decide +kernel
theorem sub5_169 : sub5 [0, 2, 3] = true := by decide +kernel
theorem sub5_170 : sub5 [0, 2, 4] = true := by decide +kernel
theorem sub5_171 : sub5 [0, 2, 5] = true := by decide +kernel
theorem sub5_172 : sub5 [0, 2, 6] = true := by decide +kernel
theorem sub5_173 : sub5 [0, 3] = true := by decide +kernel
theorem sub5_174 : sub5 [0, 4] = true := by decide +kernel
theorem sub5_175 : sub5 [0, 5] = true := by decide +kernel
theorem sub5_176 : sub5 [0, 6] = true := by decide +kernel
theorem sub5_177 : sub5 [1, -7] = true := by decide +kernel
theorem sub5_178 : sub5 [1, -6] = true := by decide +kernel
theorem sub5_179 : sub5 [1, -5] = true := by decide +kernel
theorem sub5_180 : sub5 [1, -4] = true := by decide +kernel
theorem sub5_181 : sub5 [1, -3] = true := by decide +kernel
theorem sub5_182 : sub5 [1, -2] = true := by decide +kernel
theorem sub5_183 : sub5 [1, -1, -7] = true := by decide +kernel
theorem sub5_184 : sub5 [1, -1, -6] = true := by decide +kernel
theorem sub5_185 : sub5 [1, -1, -5] = true := by decide +kernel
theorem sub5_186 : sub5 [1, -1, -4] = true := by decide +kernel
theorem sub5_187 : sub5 [1, -1, -3] = true := by decide +kernel
theorem sub5_188 : sub5 [1, -1, -2] = true := by decide +kernel
theorem sub5_189 : sub5 [1, -1, -1] = true := by decide +kernel
theorem sub5_190 : sub5 [1, -1, 0] = true := by decide +kernel
theorem sub5_191 : sub5 [1, -1, 1] = true := by decide +kernel
theorem sb5_5 : ∀ q ∈ blk5_5, sub5 q = true := by
  unfold blk5_5
  exact List.forall_mem_cons.2 ⟨sub5_160, List.forall_mem_cons.2 ⟨sub5_161, List.forall_mem_cons.2 ⟨sub5_162, List.forall_mem_cons.2 ⟨sub5_163, List.forall_mem_cons.2 ⟨sub5_164, List.forall_mem_cons.2 ⟨sub5_165, List.forall_mem_cons.2 ⟨sub5_166, List.forall_mem_cons.2 ⟨sub5_167, List.forall_mem_cons.2 ⟨sub5_168, List.forall_mem_cons.2 ⟨sub5_169, List.forall_mem_cons.2 ⟨sub5_170, List.forall_mem_cons.2 ⟨sub5_171, List.forall_mem_cons.2 ⟨sub5_172, List.forall_mem_cons.2 ⟨sub5_173, List.forall_mem_cons.2 ⟨sub5_174, List.forall_mem_cons.2 ⟨sub5_175, List.forall_mem_cons.2 ⟨sub5_176, List.forall_mem_cons.2 ⟨sub5_177, List.forall_mem_cons.2 ⟨sub5_178, List.forall_mem_cons.2 ⟨sub5_179, List.forall_mem_cons.2 ⟨sub5_180, List.forall_mem_cons.2 ⟨sub5_181, List.forall_mem_cons.2 ⟨sub5_182, List.forall_mem_cons.2 ⟨sub5_183, List.forall_mem_cons.2 ⟨sub5_184, List.forall_mem_cons.2 ⟨sub5_185, List.forall_mem_cons.2 ⟨sub5_186, List.forall_mem_cons.2 ⟨sub5_187, List.forall_mem_cons.2 ⟨sub5_188, List.forall_mem_cons.2 ⟨sub5_189, List.forall_mem_cons.2 ⟨sub5_190, List.forall_mem_cons.2 ⟨sub5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_192 : sub5 [1, -1, 2] = true := by decide +kernel
theorem sub5_193 : sub5 [1, -1, 3] = true := by decide +kernel
theorem sub5_194 : sub5 [1, -1, 4] = true := by decide +kernel
theorem sub5_195 : sub5 [1, -1, 5] = true := by decide +kernel
theorem sub5_196 : sub5 [1, 0, -7] = true := by decide +kernel
theorem sub5_197 : sub5 [1, 0, -6] = true := by decide +kernel
theorem sub5_198 : sub5 [1, 0, -5] = true := by decide +kernel
theorem sub5_199 : sub5 [1, 0, -4] = true := by decide +kernel
theorem sub5_200 : sub5 [1, 0, -3] = true := by decide +kernel
theorem sub5_201 : sub5 [1, 0, -2] = true := by decide +kernel
theorem sub5_202 : sub5 [1, 0, -1] = true := by decide +kernel
theorem sub5_203 : sub5 [1, 0, 0] = true := by decide +kernel
theorem sub5_204 : sub5 [1, 0, 1] = true := by decide +kernel
theorem sub5_205 : sub5 [1, 0, 2] = true := by decide +kernel
theorem sub5_206 : sub5 [1, 0, 3] = true := by decide +kernel
theorem sub5_207 : sub5 [1, 0, 4] = true := by decide +kernel
theorem sub5_208 : sub5 [1, 0, 5] = true := by decide +kernel
theorem sub5_209 : sub5 [1, 0, 6] = true := by decide +kernel
theorem sub5_210 : sub5 [1, 1, -7] = true := by decide +kernel
theorem sub5_211 : sub5 [1, 1, -6] = true := by decide +kernel
theorem sub5_212 : sub5 [1, 1, -5] = true := by decide +kernel
theorem sub5_213 : sub5 [1, 1, -4] = true := by decide +kernel
theorem sub5_214 : sub5 [1, 1, -3] = true := by decide +kernel
theorem sub5_215 : sub5 [1, 1, -2] = true := by decide +kernel
theorem sub5_216 : sub5 [1, 1, -1] = true := by decide +kernel
theorem sub5_217 : sub5 [1, 1, 0] = true := by decide +kernel
theorem sub5_218 : sub5 [1, 1, 1] = true := by decide +kernel
theorem sub5_219 : sub5 [1, 1, 2] = true := by decide +kernel
theorem sub5_220 : sub5 [1, 1, 3] = true := by decide +kernel
theorem sub5_221 : sub5 [1, 1, 4] = true := by decide +kernel
theorem sub5_222 : sub5 [1, 1, 5] = true := by decide +kernel
theorem sub5_223 : sub5 [1, 2] = true := by decide +kernel
theorem sb5_6 : ∀ q ∈ blk5_6, sub5 q = true := by
  unfold blk5_6
  exact List.forall_mem_cons.2 ⟨sub5_192, List.forall_mem_cons.2 ⟨sub5_193, List.forall_mem_cons.2 ⟨sub5_194, List.forall_mem_cons.2 ⟨sub5_195, List.forall_mem_cons.2 ⟨sub5_196, List.forall_mem_cons.2 ⟨sub5_197, List.forall_mem_cons.2 ⟨sub5_198, List.forall_mem_cons.2 ⟨sub5_199, List.forall_mem_cons.2 ⟨sub5_200, List.forall_mem_cons.2 ⟨sub5_201, List.forall_mem_cons.2 ⟨sub5_202, List.forall_mem_cons.2 ⟨sub5_203, List.forall_mem_cons.2 ⟨sub5_204, List.forall_mem_cons.2 ⟨sub5_205, List.forall_mem_cons.2 ⟨sub5_206, List.forall_mem_cons.2 ⟨sub5_207, List.forall_mem_cons.2 ⟨sub5_208, List.forall_mem_cons.2 ⟨sub5_209, List.forall_mem_cons.2 ⟨sub5_210, List.forall_mem_cons.2 ⟨sub5_211, List.forall_mem_cons.2 ⟨sub5_212, List.forall_mem_cons.2 ⟨sub5_213, List.forall_mem_cons.2 ⟨sub5_214, List.forall_mem_cons.2 ⟨sub5_215, List.forall_mem_cons.2 ⟨sub5_216, List.forall_mem_cons.2 ⟨sub5_217, List.forall_mem_cons.2 ⟨sub5_218, List.forall_mem_cons.2 ⟨sub5_219, List.forall_mem_cons.2 ⟨sub5_220, List.forall_mem_cons.2 ⟨sub5_221, List.forall_mem_cons.2 ⟨sub5_222, List.forall_mem_cons.2 ⟨sub5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_224 : sub5 [1, 3] = true := by decide +kernel
theorem sub5_225 : sub5 [1, 4] = true := by decide +kernel
theorem sub5_226 : sub5 [1, 5] = true := by decide +kernel
theorem sub5_227 : sub5 [1, 6] = true := by decide +kernel
theorem sub5_228 : sub5 [1, 7] = true := by decide +kernel
theorem sub5_229 : sub5 [2, -6] = true := by decide +kernel
theorem sub5_230 : sub5 [2, -5] = true := by decide +kernel
theorem sub5_231 : sub5 [2, -4] = true := by decide +kernel
theorem sub5_232 : sub5 [2, -3] = true := by decide +kernel
theorem sub5_233 : sub5 [2, -2] = true := by decide +kernel
theorem sub5_234 : sub5 [2, -1] = true := by decide +kernel
theorem sub5_235 : sub5 [2, 0] = true := by decide +kernel
theorem sub5_236 : sub5 [2, 1] = true := by decide +kernel
theorem sub5_237 : sub5 [2, 2] = true := by decide +kernel
theorem sub5_238 : sub5 [2, 3] = true := by decide +kernel
theorem sub5_239 : sub5 [2, 4] = true := by decide +kernel
theorem sub5_240 : sub5 [2, 5] = true := by decide +kernel
theorem sub5_241 : sub5 [2, 6] = true := by decide +kernel
theorem sub5_242 : sub5 [2, 7] = true := by decide +kernel
theorem sub5_243 : sub5 [3, -5] = true := by decide +kernel
theorem sub5_244 : sub5 [3, -4] = true := by decide +kernel
theorem sub5_245 : sub5 [3, -3] = true := by decide +kernel
theorem sub5_246 : sub5 [3, -2] = true := by decide +kernel
theorem sub5_247 : sub5 [3, -1] = true := by decide +kernel
theorem sub5_248 : sub5 [3, 0] = true := by decide +kernel
theorem sub5_249 : sub5 [3, 1] = true := by decide +kernel
theorem sub5_250 : sub5 [3, 2] = true := by decide +kernel
theorem sub5_251 : sub5 [3, 3] = true := by decide +kernel
theorem sub5_252 : sub5 [3, 4] = true := by decide +kernel
theorem sub5_253 : sub5 [3, 5] = true := by decide +kernel
theorem sub5_254 : sub5 [3, 6] = true := by decide +kernel
theorem sub5_255 : sub5 [3, 7] = true := by decide +kernel
theorem sb5_7 : ∀ q ∈ blk5_7, sub5 q = true := by
  unfold blk5_7
  exact List.forall_mem_cons.2 ⟨sub5_224, List.forall_mem_cons.2 ⟨sub5_225, List.forall_mem_cons.2 ⟨sub5_226, List.forall_mem_cons.2 ⟨sub5_227, List.forall_mem_cons.2 ⟨sub5_228, List.forall_mem_cons.2 ⟨sub5_229, List.forall_mem_cons.2 ⟨sub5_230, List.forall_mem_cons.2 ⟨sub5_231, List.forall_mem_cons.2 ⟨sub5_232, List.forall_mem_cons.2 ⟨sub5_233, List.forall_mem_cons.2 ⟨sub5_234, List.forall_mem_cons.2 ⟨sub5_235, List.forall_mem_cons.2 ⟨sub5_236, List.forall_mem_cons.2 ⟨sub5_237, List.forall_mem_cons.2 ⟨sub5_238, List.forall_mem_cons.2 ⟨sub5_239, List.forall_mem_cons.2 ⟨sub5_240, List.forall_mem_cons.2 ⟨sub5_241, List.forall_mem_cons.2 ⟨sub5_242, List.forall_mem_cons.2 ⟨sub5_243, List.forall_mem_cons.2 ⟨sub5_244, List.forall_mem_cons.2 ⟨sub5_245, List.forall_mem_cons.2 ⟨sub5_246, List.forall_mem_cons.2 ⟨sub5_247, List.forall_mem_cons.2 ⟨sub5_248, List.forall_mem_cons.2 ⟨sub5_249, List.forall_mem_cons.2 ⟨sub5_250, List.forall_mem_cons.2 ⟨sub5_251, List.forall_mem_cons.2 ⟨sub5_252, List.forall_mem_cons.2 ⟨sub5_253, List.forall_mem_cons.2 ⟨sub5_254, List.forall_mem_cons.2 ⟨sub5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_256 : sub5 [4, -4] = true := by decide +kernel
theorem sub5_257 : sub5 [4, -3] = true := by decide +kernel
theorem sub5_258 : sub5 [4, -2] = true := by decide +kernel
theorem sub5_259 : sub5 [4, -1] = true := by decide +kernel
theorem sub5_260 : sub5 [4, 0] = true := by decide +kernel
theorem sub5_261 : sub5 [4, 1] = true := by decide +kernel
theorem sub5_262 : sub5 [4, 2] = true := by decide +kernel
theorem sub5_263 : sub5 [4, 3] = true := by decide +kernel
theorem sub5_264 : sub5 [4, 4] = true := by decide +kernel
theorem sub5_265 : sub5 [4, 5] = true := by decide +kernel
theorem sub5_266 : sub5 [4, 6] = true := by decide +kernel
theorem sub5_267 : sub5 [5, -2] = true := by decide +kernel
theorem sub5_268 : sub5 [5, -1] = true := by decide +kernel
theorem sub5_269 : sub5 [5, 0] = true := by decide +kernel
theorem sub5_270 : sub5 [5, 1] = true := by decide +kernel
theorem sub5_271 : sub5 [5, 2] = true := by decide +kernel
theorem sub5_272 : sub5 [5, 3] = true := by decide +kernel
theorem sub5_273 : sub5 [5, 4] = true := by decide +kernel
theorem sub5_274 : sub5 [5, 5] = true := by decide +kernel
theorem sb5_8 : ∀ q ∈ blk5_8, sub5 q = true := by
  unfold blk5_8
  exact List.forall_mem_cons.2 ⟨sub5_256, List.forall_mem_cons.2 ⟨sub5_257, List.forall_mem_cons.2 ⟨sub5_258, List.forall_mem_cons.2 ⟨sub5_259, List.forall_mem_cons.2 ⟨sub5_260, List.forall_mem_cons.2 ⟨sub5_261, List.forall_mem_cons.2 ⟨sub5_262, List.forall_mem_cons.2 ⟨sub5_263, List.forall_mem_cons.2 ⟨sub5_264, List.forall_mem_cons.2 ⟨sub5_265, List.forall_mem_cons.2 ⟨sub5_266, List.forall_mem_cons.2 ⟨sub5_267, List.forall_mem_cons.2 ⟨sub5_268, List.forall_mem_cons.2 ⟨sub5_269, List.forall_mem_cons.2 ⟨sub5_270, List.forall_mem_cons.2 ⟨sub5_271, List.forall_mem_cons.2 ⟨sub5_272, List.forall_mem_cons.2 ⟨sub5_273, List.forall_mem_cons.2 ⟨sub5_274, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-5] = true := by decide +kernel
theorem sub6_1 : sub6 [-4, -4] = true := by decide +kernel
theorem sub6_2 : sub6 [-4, -3] = true := by decide +kernel
theorem sub6_3 : sub6 [-4, -2] = true := by decide +kernel
theorem sub6_4 : sub6 [-4, -1] = true := by decide +kernel
theorem sub6_5 : sub6 [-4, 0] = true := by decide +kernel
theorem sub6_6 : sub6 [-4, 1] = true := by decide +kernel
theorem sub6_7 : sub6 [-4, 2] = true := by decide +kernel
theorem sub6_8 : sub6 [-3, -5] = true := by decide +kernel
theorem sub6_9 : sub6 [-3, -4] = true := by decide +kernel
theorem sub6_10 : sub6 [-3, -3] = true := by decide +kernel
theorem sub6_11 : sub6 [-3, -2, -5] = true := by decide +kernel
theorem sub6_12 : sub6 [-3, -2, -4] = true := by decide +kernel
theorem sub6_13 : sub6 [-3, -2, -3] = true := by decide +kernel
theorem sub6_14 : sub6 [-3, -2, -2] = true := by decide +kernel
theorem sub6_15 : sub6 [-3, -2, -1] = true := by decide +kernel
theorem sub6_16 : sub6 [-3, -2, 0] = true := by decide +kernel
theorem sub6_17 : sub6 [-3, -2, 1] = true := by decide +kernel
theorem sub6_18 : sub6 [-3, -2, 2] = true := by decide +kernel
theorem sub6_19 : sub6 [-3, -2, 3] = true := by decide +kernel
theorem sub6_20 : sub6 [-3, -2, 4] = true := by decide +kernel
theorem sub6_21 : sub6 [-3, -2, 5] = true := by decide +kernel
theorem sub6_22 : sub6 [-3, -2, 6] = true := by decide +kernel
theorem sub6_23 : sub6 [-3, -2, 7] = true := by decide +kernel
theorem sub6_24 : sub6 [-3, -2, 8] = true := by decide +kernel
theorem sub6_25 : sub6 [-3, -1, -6] = true := by decide +kernel
theorem sub6_26 : sub6 [-3, -1, -5] = true := by decide +kernel
theorem sub6_27 : sub6 [-3, -1, -4] = true := by decide +kernel
theorem sub6_28 : sub6 [-3, -1, -3] = true := by decide +kernel
theorem sub6_29 : sub6 [-3, -1, -2] = true := by decide +kernel
theorem sub6_30 : sub6 [-3, -1, -1] = true := by decide +kernel
theorem sub6_31 : sub6 [-3, -1, 0] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_32 : sub6 [-3, -1, 1] = true := by decide +kernel
theorem sub6_33 : sub6 [-3, -1, 2] = true := by decide +kernel
theorem sub6_34 : sub6 [-3, -1, 3] = true := by decide +kernel
theorem sub6_35 : sub6 [-3, -1, 4] = true := by decide +kernel
theorem sub6_36 : sub6 [-3, -1, 5] = true := by decide +kernel
theorem sub6_37 : sub6 [-3, -1, 6] = true := by decide +kernel
theorem sub6_38 : sub6 [-3, -1, 7] = true := by decide +kernel
theorem sub6_39 : sub6 [-3, -1, 8] = true := by decide +kernel
theorem sub6_40 : sub6 [-3, 0, -6] = true := by decide +kernel
theorem sub6_41 : sub6 [-3, 0, -5] = true := by decide +kernel
theorem sub6_42 : sub6 [-3, 0, -4] = true := by decide +kernel
theorem sub6_43 : sub6 [-3, 0, -3] = true := by decide +kernel
theorem sub6_44 : sub6 [-3, 0, -2] = true := by decide +kernel
theorem sub6_45 : sub6 [-3, 0, -1] = true := by decide +kernel
theorem sub6_46 : sub6 [-3, 0, 0] = true := by decide +kernel
theorem sub6_47 : sub6 [-3, 0, 1] = true := by decide +kernel
theorem sub6_48 : sub6 [-3, 0, 2] = true := by decide +kernel
theorem sub6_49 : sub6 [-3, 0, 3] = true := by decide +kernel
theorem sub6_50 : sub6 [-3, 0, 4] = true := by decide +kernel
theorem sub6_51 : sub6 [-3, 0, 5] = true := by decide +kernel
theorem sub6_52 : sub6 [-3, 0, 6] = true := by decide +kernel
theorem sub6_53 : sub6 [-3, 0, 7] = true := by decide +kernel
theorem sub6_54 : sub6 [-3, 0, 8] = true := by decide +kernel
theorem sub6_55 : sub6 [-3, 1, -6] = true := by decide +kernel
theorem sub6_56 : sub6 [-3, 1, -5] = true := by decide +kernel
theorem sub6_57 : sub6 [-3, 1, -4] = true := by decide +kernel
theorem sub6_58 : sub6 [-3, 1, -3] = true := by decide +kernel
theorem sub6_59 : sub6 [-3, 1, -2] = true := by decide +kernel
theorem sub6_60 : sub6 [-3, 1, -1] = true := by decide +kernel
theorem sub6_61 : sub6 [-3, 1, 0] = true := by decide +kernel
theorem sub6_62 : sub6 [-3, 1, 1] = true := by decide +kernel
theorem sub6_63 : sub6 [-3, 1, 2] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_cons.2 ⟨sub6_38, List.forall_mem_cons.2 ⟨sub6_39, List.forall_mem_cons.2 ⟨sub6_40, List.forall_mem_cons.2 ⟨sub6_41, List.forall_mem_cons.2 ⟨sub6_42, List.forall_mem_cons.2 ⟨sub6_43, List.forall_mem_cons.2 ⟨sub6_44, List.forall_mem_cons.2 ⟨sub6_45, List.forall_mem_cons.2 ⟨sub6_46, List.forall_mem_cons.2 ⟨sub6_47, List.forall_mem_cons.2 ⟨sub6_48, List.forall_mem_cons.2 ⟨sub6_49, List.forall_mem_cons.2 ⟨sub6_50, List.forall_mem_cons.2 ⟨sub6_51, List.forall_mem_cons.2 ⟨sub6_52, List.forall_mem_cons.2 ⟨sub6_53, List.forall_mem_cons.2 ⟨sub6_54, List.forall_mem_cons.2 ⟨sub6_55, List.forall_mem_cons.2 ⟨sub6_56, List.forall_mem_cons.2 ⟨sub6_57, List.forall_mem_cons.2 ⟨sub6_58, List.forall_mem_cons.2 ⟨sub6_59, List.forall_mem_cons.2 ⟨sub6_60, List.forall_mem_cons.2 ⟨sub6_61, List.forall_mem_cons.2 ⟨sub6_62, List.forall_mem_cons.2 ⟨sub6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_64 : sub6 [-3, 1, 3] = true := by decide +kernel
theorem sub6_65 : sub6 [-3, 1, 4] = true := by decide +kernel
theorem sub6_66 : sub6 [-3, 1, 5] = true := by decide +kernel
theorem sub6_67 : sub6 [-3, 1, 6] = true := by decide +kernel
theorem sub6_68 : sub6 [-3, 1, 7] = true := by decide +kernel
theorem sub6_69 : sub6 [-3, 2] = true := by decide +kernel
theorem sub6_70 : sub6 [-3, 3] = true := by decide +kernel
theorem sub6_71 : sub6 [-2, -5] = true := by decide +kernel
theorem sub6_72 : sub6 [-2, -4] = true := by decide +kernel
theorem sub6_73 : sub6 [-2, -3, -5] = true := by decide +kernel
theorem sub6_74 : sub6 [-2, -3, -4] = true := by decide +kernel
theorem sub6_75 : sub6 [-2, -3, -3] = true := by decide +kernel
theorem sub6_76 : sub6 [-2, -3, -2] = true := by decide +kernel
theorem sub6_77 : sub6 [-2, -3, -1] = true := by decide +kernel
theorem sub6_78 : sub6 [-2, -3, 0] = true := by decide +kernel
theorem sub6_79 : sub6 [-2, -3, 1] = true := by decide +kernel
theorem sub6_80 : sub6 [-2, -3, 2] = true := by decide +kernel
theorem sub6_81 : sub6 [-2, -3, 3] = true := by decide +kernel
theorem sub6_82 : sub6 [-2, -3, 4] = true := by decide +kernel
theorem sub6_83 : sub6 [-2, -3, 5] = true := by decide +kernel
theorem sub6_84 : sub6 [-2, -3, 6] = true := by decide +kernel
theorem sub6_85 : sub6 [-2, -3, 7] = true := by decide +kernel
theorem sub6_86 : sub6 [-2, -2, -7] = true := by decide +kernel
theorem sub6_87 : sub6 [-2, -2, -6] = true := by decide +kernel
theorem sub6_88 : sub6 [-2, -2, -5] = true := by decide +kernel
theorem sub6_89 : sub6 [-2, -2, -4] = true := by decide +kernel
theorem sub6_90 : sub6 [-2, -2, -3] = true := by decide +kernel
theorem sub6_91 : sub6 [-2, -2, -2] = true := by decide +kernel
theorem sub6_92 : sub6 [-2, -2, -1] = true := by decide +kernel
theorem sub6_93 : sub6 [-2, -2, 0] = true := by decide +kernel
theorem sub6_94 : sub6 [-2, -2, 1] = true := by decide +kernel
theorem sub6_95 : sub6 [-2, -2, 2] = true := by decide +kernel
theorem sb6_2 : ∀ q ∈ blk6_2, sub6 q = true := by
  unfold blk6_2
  exact List.forall_mem_cons.2 ⟨sub6_64, List.forall_mem_cons.2 ⟨sub6_65, List.forall_mem_cons.2 ⟨sub6_66, List.forall_mem_cons.2 ⟨sub6_67, List.forall_mem_cons.2 ⟨sub6_68, List.forall_mem_cons.2 ⟨sub6_69, List.forall_mem_cons.2 ⟨sub6_70, List.forall_mem_cons.2 ⟨sub6_71, List.forall_mem_cons.2 ⟨sub6_72, List.forall_mem_cons.2 ⟨sub6_73, List.forall_mem_cons.2 ⟨sub6_74, List.forall_mem_cons.2 ⟨sub6_75, List.forall_mem_cons.2 ⟨sub6_76, List.forall_mem_cons.2 ⟨sub6_77, List.forall_mem_cons.2 ⟨sub6_78, List.forall_mem_cons.2 ⟨sub6_79, List.forall_mem_cons.2 ⟨sub6_80, List.forall_mem_cons.2 ⟨sub6_81, List.forall_mem_cons.2 ⟨sub6_82, List.forall_mem_cons.2 ⟨sub6_83, List.forall_mem_cons.2 ⟨sub6_84, List.forall_mem_cons.2 ⟨sub6_85, List.forall_mem_cons.2 ⟨sub6_86, List.forall_mem_cons.2 ⟨sub6_87, List.forall_mem_cons.2 ⟨sub6_88, List.forall_mem_cons.2 ⟨sub6_89, List.forall_mem_cons.2 ⟨sub6_90, List.forall_mem_cons.2 ⟨sub6_91, List.forall_mem_cons.2 ⟨sub6_92, List.forall_mem_cons.2 ⟨sub6_93, List.forall_mem_cons.2 ⟨sub6_94, List.forall_mem_cons.2 ⟨sub6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_96 : sub6 [-2, -2, 3] = true := by decide +kernel
theorem sub6_97 : sub6 [-2, -2, 4] = true := by decide +kernel
theorem sub6_98 : sub6 [-2, -2, 5] = true := by decide +kernel
theorem sub6_99 : sub6 [-2, -2, 6] = true := by decide +kernel
theorem sub6_100 : sub6 [-2, -2, 7] = true := by decide +kernel
theorem sub6_101 : sub6 [-2, -2, 8] = true := by decide +kernel
theorem sub6_102 : sub6 [-2, -1, -7] = true := by decide +kernel
theorem sub6_103 : sub6 [-2, -1, -6] = true := by decide +kernel
theorem sub6_104 : sub6 [-2, -1, -5] = true := by decide +kernel
theorem sub6_105 : sub6 [-2, -1, -4] = true := by decide +kernel
theorem sub6_106 : sub6 [-2, -1, -3] = true := by decide +kernel
theorem sub6_107 : sub6 [-2, -1, -2] = true := by decide +kernel
theorem sub6_108 : sub6 [-2, -1, -1] = true := by decide +kernel
theorem sub6_109 : sub6 [-2, -1, 0] = true := by decide +kernel
theorem sub6_110 : sub6 [-2, -1, 1] = true := by decide +kernel
theorem sub6_111 : sub6 [-2, -1, 2] = true := by decide +kernel
theorem sub6_112 : sub6 [-2, -1, 3] = true := by decide +kernel
theorem sub6_113 : sub6 [-2, -1, 4] = true := by decide +kernel
theorem sub6_114 : sub6 [-2, -1, 5] = true := by decide +kernel
theorem sub6_115 : sub6 [-2, -1, 6] = true := by decide +kernel
theorem sub6_116 : sub6 [-2, -1, 7] = true := by decide +kernel
theorem sub6_117 : sub6 [-2, -1, 8] = true := by decide +kernel
theorem sub6_118 : sub6 [-2, 0, -8] = true := by decide +kernel
theorem sub6_119 : sub6 [-2, 0, -7] = true := by decide +kernel
theorem sub6_120 : sub6 [-2, 0, -6] = true := by decide +kernel
theorem sub6_121 : sub6 [-2, 0, -5] = true := by decide +kernel
theorem sub6_122 : sub6 [-2, 0, -4] = true := by decide +kernel
theorem sub6_123 : sub6 [-2, 0, -3] = true := by decide +kernel
theorem sub6_124 : sub6 [-2, 0, -2] = true := by decide +kernel
theorem sub6_125 : sub6 [-2, 0, -1] = true := by decide +kernel
theorem sub6_126 : sub6 [-2, 0, 0] = true := by decide +kernel
theorem sub6_127 : sub6 [-2, 0, 1] = true := by decide +kernel
theorem sb6_3 : ∀ q ∈ blk6_3, sub6 q = true := by
  unfold blk6_3
  exact List.forall_mem_cons.2 ⟨sub6_96, List.forall_mem_cons.2 ⟨sub6_97, List.forall_mem_cons.2 ⟨sub6_98, List.forall_mem_cons.2 ⟨sub6_99, List.forall_mem_cons.2 ⟨sub6_100, List.forall_mem_cons.2 ⟨sub6_101, List.forall_mem_cons.2 ⟨sub6_102, List.forall_mem_cons.2 ⟨sub6_103, List.forall_mem_cons.2 ⟨sub6_104, List.forall_mem_cons.2 ⟨sub6_105, List.forall_mem_cons.2 ⟨sub6_106, List.forall_mem_cons.2 ⟨sub6_107, List.forall_mem_cons.2 ⟨sub6_108, List.forall_mem_cons.2 ⟨sub6_109, List.forall_mem_cons.2 ⟨sub6_110, List.forall_mem_cons.2 ⟨sub6_111, List.forall_mem_cons.2 ⟨sub6_112, List.forall_mem_cons.2 ⟨sub6_113, List.forall_mem_cons.2 ⟨sub6_114, List.forall_mem_cons.2 ⟨sub6_115, List.forall_mem_cons.2 ⟨sub6_116, List.forall_mem_cons.2 ⟨sub6_117, List.forall_mem_cons.2 ⟨sub6_118, List.forall_mem_cons.2 ⟨sub6_119, List.forall_mem_cons.2 ⟨sub6_120, List.forall_mem_cons.2 ⟨sub6_121, List.forall_mem_cons.2 ⟨sub6_122, List.forall_mem_cons.2 ⟨sub6_123, List.forall_mem_cons.2 ⟨sub6_124, List.forall_mem_cons.2 ⟨sub6_125, List.forall_mem_cons.2 ⟨sub6_126, List.forall_mem_cons.2 ⟨sub6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C098
