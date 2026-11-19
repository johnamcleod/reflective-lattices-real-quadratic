import ReflectZphi.Data.Cert5.C058.Base

namespace ReflectZphi.Data.Cert5.C058
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_160 : sub4 [0, -1, 6] = true := by decide +kernel
theorem sub4_161 : sub4 [0, 0, -8] = true := by decide +kernel
theorem sub4_162 : sub4 [0, 0, -7] = true := by decide +kernel
theorem sub4_163 : sub4 [0, 0, -6] = true := by decide +kernel
theorem sub4_164 : sub4 [0, 0, -5] = true := by decide +kernel
theorem sub4_165 : sub4 [0, 0, -4] = true := by decide +kernel
theorem sub4_166 : sub4 [0, 0, -3] = true := by decide +kernel
theorem sub4_167 : sub4 [0, 0, -2] = true := by decide +kernel
theorem sub4_168 : sub4 [0, 0, -1] = true := by decide +kernel
theorem sub4_169 : sub4 [0, 0, 0] = true := by decide +kernel
theorem sub4_170 : sub4 [0, 0, 1] = true := by decide +kernel
theorem sub4_171 : sub4 [0, 0, 2] = true := by decide +kernel
theorem sub4_172 : sub4 [0, 0, 3] = true := by decide +kernel
theorem sub4_173 : sub4 [0, 0, 4] = true := by decide +kernel
theorem sub4_174 : sub4 [0, 0, 5] = true := by decide +kernel
theorem sub4_175 : sub4 [0, 0, 6] = true := by decide +kernel
theorem sub4_176 : sub4 [0, 0, 7] = true := by decide +kernel
theorem sub4_177 : sub4 [0, 1, -7] = true := by decide +kernel
theorem sub4_178 : sub4 [0, 1, -6] = true := by decide +kernel
theorem sub4_179 : sub4 [0, 1, -5] = true := by decide +kernel
theorem sub4_180 : sub4 [0, 1, -4] = true := by decide +kernel
theorem sub4_181 : sub4 [0, 1, -3] = true := by decide +kernel
theorem sub4_182 : sub4 [0, 1, -2] = true := by decide +kernel
theorem sub4_183 : sub4 [0, 1, -1] = true := by decide +kernel
theorem sub4_184 : sub4 [0, 1, 0] = true := by decide +kernel
theorem sub4_185 : sub4 [0, 1, 1] = true := by decide +kernel
theorem sub4_186 : sub4 [0, 1, 2] = true := by decide +kernel
theorem sub4_187 : sub4 [0, 1, 3] = true := by decide +kernel
theorem sub4_188 : sub4 [0, 1, 4] = true := by decide +kernel
theorem sub4_189 : sub4 [0, 1, 5] = true := by decide +kernel
theorem sub4_190 : sub4 [0, 1, 6] = true := by decide +kernel
theorem sub4_191 : sub4 [0, 1, 7] = true := by decide +kernel
theorem sb4_5 : ∀ q ∈ blk4_5, sub4 q = true := by
  unfold blk4_5
  exact List.forall_mem_cons.2 ⟨sub4_160, List.forall_mem_cons.2 ⟨sub4_161, List.forall_mem_cons.2 ⟨sub4_162, List.forall_mem_cons.2 ⟨sub4_163, List.forall_mem_cons.2 ⟨sub4_164, List.forall_mem_cons.2 ⟨sub4_165, List.forall_mem_cons.2 ⟨sub4_166, List.forall_mem_cons.2 ⟨sub4_167, List.forall_mem_cons.2 ⟨sub4_168, List.forall_mem_cons.2 ⟨sub4_169, List.forall_mem_cons.2 ⟨sub4_170, List.forall_mem_cons.2 ⟨sub4_171, List.forall_mem_cons.2 ⟨sub4_172, List.forall_mem_cons.2 ⟨sub4_173, List.forall_mem_cons.2 ⟨sub4_174, List.forall_mem_cons.2 ⟨sub4_175, List.forall_mem_cons.2 ⟨sub4_176, List.forall_mem_cons.2 ⟨sub4_177, List.forall_mem_cons.2 ⟨sub4_178, List.forall_mem_cons.2 ⟨sub4_179, List.forall_mem_cons.2 ⟨sub4_180, List.forall_mem_cons.2 ⟨sub4_181, List.forall_mem_cons.2 ⟨sub4_182, List.forall_mem_cons.2 ⟨sub4_183, List.forall_mem_cons.2 ⟨sub4_184, List.forall_mem_cons.2 ⟨sub4_185, List.forall_mem_cons.2 ⟨sub4_186, List.forall_mem_cons.2 ⟨sub4_187, List.forall_mem_cons.2 ⟨sub4_188, List.forall_mem_cons.2 ⟨sub4_189, List.forall_mem_cons.2 ⟨sub4_190, List.forall_mem_cons.2 ⟨sub4_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_192 : sub4 [0, 2, -7] = true := by decide +kernel
theorem sub4_193 : sub4 [0, 2, -6] = true := by decide +kernel
theorem sub4_194 : sub4 [0, 2, -5] = true := by decide +kernel
theorem sub4_195 : sub4 [0, 2, -4] = true := by decide +kernel
theorem sub4_196 : sub4 [0, 2, -3] = true := by decide +kernel
theorem sub4_197 : sub4 [0, 2, -2] = true := by decide +kernel
theorem sub4_198 : sub4 [0, 2, -1] = true := by decide +kernel
theorem sub4_199 : sub4 [0, 2, 0] = true := by decide +kernel
theorem sub4_200 : sub4 [0, 2, 1] = true := by decide +kernel
theorem sub4_201 : sub4 [0, 2, 2] = true := by decide +kernel
theorem sub4_202 : sub4 [0, 2, 3] = true := by decide +kernel
theorem sub4_203 : sub4 [0, 2, 4] = true := by decide +kernel
theorem sub4_204 : sub4 [0, 2, 5] = true := by decide +kernel
theorem sub4_205 : sub4 [0, 2, 6] = true := by decide +kernel
theorem sub4_206 : sub4 [0, 2, 7] = true := by decide +kernel
theorem sub4_207 : sub4 [0, 3] = true := by decide +kernel
theorem sub4_208 : sub4 [0, 4] = true := by decide +kernel
theorem sub4_209 : sub4 [0, 5] = true := by decide +kernel
theorem sub4_210 : sub4 [0, 6] = true := by decide +kernel
theorem sub4_211 : sub4 [1, -6] = true := by decide +kernel
theorem sub4_212 : sub4 [1, -5] = true := by decide +kernel
theorem sub4_213 : sub4 [1, -4] = true := by decide +kernel
theorem sub4_214 : sub4 [1, -3] = true := by decide +kernel
theorem sub4_215 : sub4 [1, -2] = true := by decide +kernel
theorem sub4_216 : sub4 [1, -1, -8] = true := by decide +kernel
theorem sub4_217 : sub4 [1, -1, -7] = true := by decide +kernel
theorem sub4_218 : sub4 [1, -1, -6] = true := by decide +kernel
theorem sub4_219 : sub4 [1, -1, -5] = true := by decide +kernel
theorem sub4_220 : sub4 [1, -1, -4] = true := by decide +kernel
theorem sub4_221 : sub4 [1, -1, -3] = true := by decide +kernel
theorem sub4_222 : sub4 [1, -1, -2] = true := by decide +kernel
theorem sub4_223 : sub4 [1, -1, -1] = true := by decide +kernel
theorem sb4_6 : ∀ q ∈ blk4_6, sub4 q = true := by
  unfold blk4_6
  exact List.forall_mem_cons.2 ⟨sub4_192, List.forall_mem_cons.2 ⟨sub4_193, List.forall_mem_cons.2 ⟨sub4_194, List.forall_mem_cons.2 ⟨sub4_195, List.forall_mem_cons.2 ⟨sub4_196, List.forall_mem_cons.2 ⟨sub4_197, List.forall_mem_cons.2 ⟨sub4_198, List.forall_mem_cons.2 ⟨sub4_199, List.forall_mem_cons.2 ⟨sub4_200, List.forall_mem_cons.2 ⟨sub4_201, List.forall_mem_cons.2 ⟨sub4_202, List.forall_mem_cons.2 ⟨sub4_203, List.forall_mem_cons.2 ⟨sub4_204, List.forall_mem_cons.2 ⟨sub4_205, List.forall_mem_cons.2 ⟨sub4_206, List.forall_mem_cons.2 ⟨sub4_207, List.forall_mem_cons.2 ⟨sub4_208, List.forall_mem_cons.2 ⟨sub4_209, List.forall_mem_cons.2 ⟨sub4_210, List.forall_mem_cons.2 ⟨sub4_211, List.forall_mem_cons.2 ⟨sub4_212, List.forall_mem_cons.2 ⟨sub4_213, List.forall_mem_cons.2 ⟨sub4_214, List.forall_mem_cons.2 ⟨sub4_215, List.forall_mem_cons.2 ⟨sub4_216, List.forall_mem_cons.2 ⟨sub4_217, List.forall_mem_cons.2 ⟨sub4_218, List.forall_mem_cons.2 ⟨sub4_219, List.forall_mem_cons.2 ⟨sub4_220, List.forall_mem_cons.2 ⟨sub4_221, List.forall_mem_cons.2 ⟨sub4_222, List.forall_mem_cons.2 ⟨sub4_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_224 : sub4 [1, -1, 0] = true := by decide +kernel
theorem sub4_225 : sub4 [1, -1, 1] = true := by decide +kernel
theorem sub4_226 : sub4 [1, -1, 2] = true := by decide +kernel
theorem sub4_227 : sub4 [1, -1, 3] = true := by decide +kernel
theorem sub4_228 : sub4 [1, -1, 4] = true := by decide +kernel
theorem sub4_229 : sub4 [1, -1, 5] = true := by decide +kernel
theorem sub4_230 : sub4 [1, -1, 6] = true := by decide +kernel
theorem sub4_231 : sub4 [1, 0, -7] = true := by decide +kernel
theorem sub4_232 : sub4 [1, 0, -6] = true := by decide +kernel
theorem sub4_233 : sub4 [1, 0, -5] = true := by decide +kernel
theorem sub4_234 : sub4 [1, 0, -4] = true := by decide +kernel
theorem sub4_235 : sub4 [1, 0, -3] = true := by decide +kernel
theorem sub4_236 : sub4 [1, 0, -2] = true := by decide +kernel
theorem sub4_237 : sub4 [1, 0, -1] = true := by decide +kernel
theorem sub4_238 : sub4 [1, 0, 0] = true := by decide +kernel
theorem sub4_239 : sub4 [1, 0, 1] = true := by decide +kernel
theorem sub4_240 : sub4 [1, 0, 2] = true := by decide +kernel
theorem sub4_241 : sub4 [1, 0, 3] = true := by decide +kernel
theorem sub4_242 : sub4 [1, 0, 4] = true := by decide +kernel
theorem sub4_243 : sub4 [1, 0, 5] = true := by decide +kernel
theorem sub4_244 : sub4 [1, 0, 6] = true := by decide +kernel
theorem sub4_245 : sub4 [1, 0, 7] = true := by decide +kernel
theorem sub4_246 : sub4 [1, 1, -7] = true := by decide +kernel
theorem sub4_247 : sub4 [1, 1, -6] = true := by decide +kernel
theorem sub4_248 : sub4 [1, 1, -5] = true := by decide +kernel
theorem sub4_249 : sub4 [1, 1, -4] = true := by decide +kernel
theorem sub4_250 : sub4 [1, 1, -3] = true := by decide +kernel
theorem sub4_251 : sub4 [1, 1, -2] = true := by decide +kernel
theorem sub4_252 : sub4 [1, 1, -1] = true := by decide +kernel
theorem sub4_253 : sub4 [1, 1, 0] = true := by decide +kernel
theorem sub4_254 : sub4 [1, 1, 1] = true := by decide +kernel
theorem sub4_255 : sub4 [1, 1, 2] = true := by decide +kernel
theorem sb4_7 : ∀ q ∈ blk4_7, sub4 q = true := by
  unfold blk4_7
  exact List.forall_mem_cons.2 ⟨sub4_224, List.forall_mem_cons.2 ⟨sub4_225, List.forall_mem_cons.2 ⟨sub4_226, List.forall_mem_cons.2 ⟨sub4_227, List.forall_mem_cons.2 ⟨sub4_228, List.forall_mem_cons.2 ⟨sub4_229, List.forall_mem_cons.2 ⟨sub4_230, List.forall_mem_cons.2 ⟨sub4_231, List.forall_mem_cons.2 ⟨sub4_232, List.forall_mem_cons.2 ⟨sub4_233, List.forall_mem_cons.2 ⟨sub4_234, List.forall_mem_cons.2 ⟨sub4_235, List.forall_mem_cons.2 ⟨sub4_236, List.forall_mem_cons.2 ⟨sub4_237, List.forall_mem_cons.2 ⟨sub4_238, List.forall_mem_cons.2 ⟨sub4_239, List.forall_mem_cons.2 ⟨sub4_240, List.forall_mem_cons.2 ⟨sub4_241, List.forall_mem_cons.2 ⟨sub4_242, List.forall_mem_cons.2 ⟨sub4_243, List.forall_mem_cons.2 ⟨sub4_244, List.forall_mem_cons.2 ⟨sub4_245, List.forall_mem_cons.2 ⟨sub4_246, List.forall_mem_cons.2 ⟨sub4_247, List.forall_mem_cons.2 ⟨sub4_248, List.forall_mem_cons.2 ⟨sub4_249, List.forall_mem_cons.2 ⟨sub4_250, List.forall_mem_cons.2 ⟨sub4_251, List.forall_mem_cons.2 ⟨sub4_252, List.forall_mem_cons.2 ⟨sub4_253, List.forall_mem_cons.2 ⟨sub4_254, List.forall_mem_cons.2 ⟨sub4_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_256 : sub4 [1, 1, 3] = true := by decide +kernel
theorem sub4_257 : sub4 [1, 1, 4] = true := by decide +kernel
theorem sub4_258 : sub4 [1, 1, 5] = true := by decide +kernel
theorem sub4_259 : sub4 [1, 1, 6] = true := by decide +kernel
theorem sub4_260 : sub4 [1, 1, 7] = true := by decide +kernel
theorem sub4_261 : sub4 [1, 2, -6] = true := by decide +kernel
theorem sub4_262 : sub4 [1, 2, -5] = true := by decide +kernel
theorem sub4_263 : sub4 [1, 2, -4] = true := by decide +kernel
theorem sub4_264 : sub4 [1, 2, -3] = true := by decide +kernel
theorem sub4_265 : sub4 [1, 2, -2] = true := by decide +kernel
theorem sub4_266 : sub4 [1, 2, -1] = true := by decide +kernel
theorem sub4_267 : sub4 [1, 2, 0] = true := by decide +kernel
theorem sub4_268 : sub4 [1, 2, 1] = true := by decide +kernel
theorem sub4_269 : sub4 [1, 2, 2] = true := by decide +kernel
theorem sub4_270 : sub4 [1, 2, 3] = true := by decide +kernel
theorem sub4_271 : sub4 [1, 2, 4] = true := by decide +kernel
theorem sub4_272 : sub4 [1, 2, 5] = true := by decide +kernel
theorem sub4_273 : sub4 [1, 2, 6] = true := by decide +kernel
theorem sub4_274 : sub4 [1, 2, 7] = true := by decide +kernel
theorem sub4_275 : sub4 [1, 3] = true := by decide +kernel
theorem sub4_276 : sub4 [1, 4] = true := by decide +kernel
theorem sub4_277 : sub4 [1, 5] = true := by decide +kernel
theorem sub4_278 : sub4 [1, 6] = true := by decide +kernel
theorem sub4_279 : sub4 [2, -6] = true := by decide +kernel
theorem sub4_280 : sub4 [2, -5] = true := by decide +kernel
theorem sub4_281 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_282 : sub4 [2, -3] = true := by decide +kernel
theorem sub4_283 : sub4 [2, -2] = true := by decide +kernel
theorem sub4_284 : sub4 [2, -1] = true := by decide +kernel
theorem sub4_285 : sub4 [2, 0, -7] = true := by decide +kernel
theorem sub4_286 : sub4 [2, 0, -6] = true := by decide +kernel
theorem sub4_287 : sub4 [2, 0, -5] = true := by decide +kernel
theorem sb4_8 : ∀ q ∈ blk4_8, sub4 q = true := by
  unfold blk4_8
  exact List.forall_mem_cons.2 ⟨sub4_256, List.forall_mem_cons.2 ⟨sub4_257, List.forall_mem_cons.2 ⟨sub4_258, List.forall_mem_cons.2 ⟨sub4_259, List.forall_mem_cons.2 ⟨sub4_260, List.forall_mem_cons.2 ⟨sub4_261, List.forall_mem_cons.2 ⟨sub4_262, List.forall_mem_cons.2 ⟨sub4_263, List.forall_mem_cons.2 ⟨sub4_264, List.forall_mem_cons.2 ⟨sub4_265, List.forall_mem_cons.2 ⟨sub4_266, List.forall_mem_cons.2 ⟨sub4_267, List.forall_mem_cons.2 ⟨sub4_268, List.forall_mem_cons.2 ⟨sub4_269, List.forall_mem_cons.2 ⟨sub4_270, List.forall_mem_cons.2 ⟨sub4_271, List.forall_mem_cons.2 ⟨sub4_272, List.forall_mem_cons.2 ⟨sub4_273, List.forall_mem_cons.2 ⟨sub4_274, List.forall_mem_cons.2 ⟨sub4_275, List.forall_mem_cons.2 ⟨sub4_276, List.forall_mem_cons.2 ⟨sub4_277, List.forall_mem_cons.2 ⟨sub4_278, List.forall_mem_cons.2 ⟨sub4_279, List.forall_mem_cons.2 ⟨sub4_280, List.forall_mem_cons.2 ⟨sub4_281, List.forall_mem_cons.2 ⟨sub4_282, List.forall_mem_cons.2 ⟨sub4_283, List.forall_mem_cons.2 ⟨sub4_284, List.forall_mem_cons.2 ⟨sub4_285, List.forall_mem_cons.2 ⟨sub4_286, List.forall_mem_cons.2 ⟨sub4_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_288 : sub4 [2, 0, -4] = true := by decide +kernel
theorem sub4_289 : sub4 [2, 0, -3] = true := by decide +kernel
theorem sub4_290 : sub4 [2, 0, -2] = true := by decide +kernel
theorem sub4_291 : sub4 [2, 0, -1] = true := by decide +kernel
theorem sub4_292 : sub4 [2, 0, 0] = true := by decide +kernel
theorem sub4_293 : sub4 [2, 0, 1] = true := by decide +kernel
theorem sub4_294 : sub4 [2, 0, 2] = true := by decide +kernel
theorem sub4_295 : sub4 [2, 0, 3] = true := by decide +kernel
theorem sub4_296 : sub4 [2, 0, 4] = true := by decide +kernel
theorem sub4_297 : sub4 [2, 0, 5] = true := by decide +kernel
theorem sub4_298 : sub4 [2, 0, 6] = true := by decide +kernel
theorem sub4_299 : sub4 [2, 0, 7] = true := by decide +kernel
theorem sub4_300 : sub4 [2, 1] = true := by decide +kernel
theorem sub4_301 : sub4 [2, 2] = true := by decide +kernel
theorem sub4_302 : sub4 [2, 3] = true := by decide +kernel
theorem sub4_303 : sub4 [2, 4] = true := by decide +kernel
theorem sub4_304 : sub4 [2, 5] = true := by decide +kernel
theorem sub4_305 : sub4 [2, 6] = true := by decide +kernel
theorem sub4_306 : sub4 [3, -5] = true := by decide +kernel
theorem sub4_307 : sub4 [3, -4] = true := by decide +kernel
theorem sub4_308 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_309 : sub4 [3, -2] = true := by decide +kernel
theorem sub4_310 : sub4 [3, -1] = true := by decide +kernel
theorem sub4_311 : sub4 [3, 0] = true := by decide +kernel
theorem sub4_312 : sub4 [3, 1] = true := by decide +kernel
theorem sub4_313 : sub4 [3, 2] = true := by decide +kernel
theorem sub4_314 : sub4 [3, 3] = true := by decide +kernel
theorem sub4_315 : sub4 [3, 4] = true := by decide +kernel
theorem sub4_316 : sub4 [3, 5] = true := by decide +kernel
theorem sub4_317 : sub4 [3, 6] = true := by decide +kernel
theorem sub4_318 : sub4 [4, -4] = true := by decide +kernel
theorem sub4_319 : sub4 [4, -3] = true := by decide +kernel
theorem sb4_9 : ∀ q ∈ blk4_9, sub4 q = true := by
  unfold blk4_9
  exact List.forall_mem_cons.2 ⟨sub4_288, List.forall_mem_cons.2 ⟨sub4_289, List.forall_mem_cons.2 ⟨sub4_290, List.forall_mem_cons.2 ⟨sub4_291, List.forall_mem_cons.2 ⟨sub4_292, List.forall_mem_cons.2 ⟨sub4_293, List.forall_mem_cons.2 ⟨sub4_294, List.forall_mem_cons.2 ⟨sub4_295, List.forall_mem_cons.2 ⟨sub4_296, List.forall_mem_cons.2 ⟨sub4_297, List.forall_mem_cons.2 ⟨sub4_298, List.forall_mem_cons.2 ⟨sub4_299, List.forall_mem_cons.2 ⟨sub4_300, List.forall_mem_cons.2 ⟨sub4_301, List.forall_mem_cons.2 ⟨sub4_302, List.forall_mem_cons.2 ⟨sub4_303, List.forall_mem_cons.2 ⟨sub4_304, List.forall_mem_cons.2 ⟨sub4_305, List.forall_mem_cons.2 ⟨sub4_306, List.forall_mem_cons.2 ⟨sub4_307, List.forall_mem_cons.2 ⟨sub4_308, List.forall_mem_cons.2 ⟨sub4_309, List.forall_mem_cons.2 ⟨sub4_310, List.forall_mem_cons.2 ⟨sub4_311, List.forall_mem_cons.2 ⟨sub4_312, List.forall_mem_cons.2 ⟨sub4_313, List.forall_mem_cons.2 ⟨sub4_314, List.forall_mem_cons.2 ⟨sub4_315, List.forall_mem_cons.2 ⟨sub4_316, List.forall_mem_cons.2 ⟨sub4_317, List.forall_mem_cons.2 ⟨sub4_318, List.forall_mem_cons.2 ⟨sub4_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_320 : sub4 [4, -2] = true := by decide +kernel
theorem sub4_321 : sub4 [4, -1] = true := by decide +kernel
theorem sub4_322 : sub4 [4, 0] = true := by decide +kernel
theorem sub4_323 : sub4 [4, 1] = true := by decide +kernel
theorem sub4_324 : sub4 [4, 2] = true := by decide +kernel
theorem sub4_325 : sub4 [4, 3] = true := by decide +kernel
theorem sub4_326 : sub4 [4, 4] = true := by decide +kernel
theorem sub4_327 : sub4 [4, 5] = true := by decide +kernel
theorem sub4_328 : sub4 [4, 6] = true := by decide +kernel
theorem sub4_329 : sub4 [5, -2] = true := by decide +kernel
theorem sub4_330 : sub4 [5, -1] = true := by decide +kernel
theorem sub4_331 : sub4 [5, 0] = true := by decide +kernel
theorem sub4_332 : sub4 [5, 1] = true := by decide +kernel
theorem sub4_333 : sub4 [5, 2] = true := by decide +kernel
theorem sub4_334 : sub4 [5, 3] = true := by decide +kernel
theorem sub4_335 : sub4 [5, 4] = true := by decide +kernel
theorem sub4_336 : sub4 [5, 5] = true := by decide +kernel
theorem sb4_10 : ∀ q ∈ blk4_10, sub4 q = true := by
  unfold blk4_10
  exact List.forall_mem_cons.2 ⟨sub4_320, List.forall_mem_cons.2 ⟨sub4_321, List.forall_mem_cons.2 ⟨sub4_322, List.forall_mem_cons.2 ⟨sub4_323, List.forall_mem_cons.2 ⟨sub4_324, List.forall_mem_cons.2 ⟨sub4_325, List.forall_mem_cons.2 ⟨sub4_326, List.forall_mem_cons.2 ⟨sub4_327, List.forall_mem_cons.2 ⟨sub4_328, List.forall_mem_cons.2 ⟨sub4_329, List.forall_mem_cons.2 ⟨sub4_330, List.forall_mem_cons.2 ⟨sub4_331, List.forall_mem_cons.2 ⟨sub4_332, List.forall_mem_cons.2 ⟨sub4_333, List.forall_mem_cons.2 ⟨sub4_334, List.forall_mem_cons.2 ⟨sub4_335, List.forall_mem_cons.2 ⟨sub4_336, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_0 : sub5 [-6] = true := by decide +kernel
theorem sub5_1 : sub5 [-5, -3] = true := by decide +kernel
theorem sub5_2 : sub5 [-5, -2] = true := by decide +kernel
theorem sub5_3 : sub5 [-5, -1] = true := by decide +kernel
theorem sub5_4 : sub5 [-5, 0] = true := by decide +kernel
theorem sub5_5 : sub5 [-5, 1] = true := by decide +kernel
theorem sub5_6 : sub5 [-5, 2] = true := by decide +kernel
theorem sub5_7 : sub5 [-5, 3] = true := by decide +kernel
theorem sub5_8 : sub5 [-5, 4] = true := by decide +kernel
theorem sub5_9 : sub5 [-5, 5] = true := by decide +kernel
theorem sub5_10 : sub5 [-5, 6] = true := by decide +kernel
theorem sub5_11 : sub5 [-4, -4] = true := by decide +kernel
theorem sub5_12 : sub5 [-4, -3] = true := by decide +kernel
theorem sub5_13 : sub5 [-4, -2] = true := by decide +kernel
theorem sub5_14 : sub5 [-4, -1] = true := by decide +kernel
theorem sub5_15 : sub5 [-4, 0] = true := by decide +kernel
theorem sub5_16 : sub5 [-4, 1] = true := by decide +kernel
theorem sub5_17 : sub5 [-4, 2] = true := by decide +kernel
theorem sub5_18 : sub5 [-4, 3] = true := by decide +kernel
theorem sub5_19 : sub5 [-4, 4] = true := by decide +kernel
theorem sub5_20 : sub5 [-4, 5] = true := by decide +kernel
theorem sub5_21 : sub5 [-4, 6] = true := by decide +kernel
theorem sub5_22 : sub5 [-4, 7] = true := by decide +kernel
theorem sub5_23 : sub5 [-3, -6] = true := by decide +kernel
theorem sub5_24 : sub5 [-3, -5] = true := by decide +kernel
theorem sub5_25 : sub5 [-3, -4] = true := by decide +kernel
theorem sub5_26 : sub5 [-3, -3] = true := by decide +kernel
theorem sub5_27 : sub5 [-3, -2] = true := by decide +kernel
theorem sub5_28 : sub5 [-3, -1] = true := by decide +kernel
theorem sub5_29 : sub5 [-3, 0] = true := by decide +kernel
theorem sub5_30 : sub5 [-3, 1] = true := by decide +kernel
theorem sub5_31 : sub5 [-3, 2] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C058
