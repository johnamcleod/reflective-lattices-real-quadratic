import ReflectZphi.Data.Cert5.C104.Base

namespace ReflectZphi.Data.Cert5.C104
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub9_160 : sub9 [-1, 2, -4] = true := by decide +kernel
theorem sub9_161 : sub9 [-1, 2, -3] = true := by decide +kernel
theorem sub9_162 : sub9 [-1, 2, -2] = true := by decide +kernel
theorem sub9_163 : sub9 [-1, 2, -1] = true := by decide +kernel
theorem sub9_164 : sub9 [-1, 2, 0] = true := by decide +kernel
theorem sub9_165 : sub9 [-1, 2, 1] = true := by decide +kernel
theorem sub9_166 : sub9 [-1, 2, 2] = true := by decide +kernel
theorem sub9_167 : sub9 [-1, 2, 3] = true := by decide +kernel
theorem sub9_168 : sub9 [-1, 2, 4] = true := by decide +kernel
theorem sub9_169 : sub9 [-1, 2, 5] = true := by decide +kernel
theorem sub9_170 : sub9 [-1, 3] = true := by decide +kernel
theorem sub9_171 : sub9 [-1, 4] = true := by decide +kernel
theorem sub9_172 : sub9 [-1, 5] = true := by decide +kernel
theorem sub9_173 : sub9 [-1, 6] = true := by decide +kernel
theorem sub9_174 : sub9 [0, -8] = true := by decide +kernel
theorem sub9_175 : sub9 [0, -7] = true := by decide +kernel
theorem sub9_176 : sub9 [0, -6] = true := by decide +kernel
theorem sub9_177 : sub9 [0, -5] = true := by decide +kernel
theorem sub9_178 : sub9 [0, -4] = true := by decide +kernel
theorem sub9_179 : sub9 [0, -3] = true := by decide +kernel
theorem sub9_180 : sub9 [0, -2, -6] = true := by decide +kernel
theorem sub9_181 : sub9 [0, -2, -5] = true := by decide +kernel
theorem sub9_182 : sub9 [0, -2, -4] = true := by decide +kernel
theorem sub9_183 : sub9 [0, -2, -3] = true := by decide +kernel
theorem sub9_184 : sub9 [0, -2, -2] = true := by decide +kernel
theorem sub9_185 : sub9 [0, -2, -1] = true := by decide +kernel
theorem sub9_186 : sub9 [0, -2, 0] = true := by decide +kernel
theorem sub9_187 : sub9 [0, -2, 1] = true := by decide +kernel
theorem sub9_188 : sub9 [0, -2, 2] = true := by decide +kernel
theorem sub9_189 : sub9 [0, -2, 3] = true := by decide +kernel
theorem sub9_190 : sub9 [0, -2, 4] = true := by decide +kernel
theorem sub9_191 : sub9 [0, -2, 5] = true := by decide +kernel
theorem sb9_5 : ∀ q ∈ blk9_5, sub9 q = true := by
  unfold blk9_5
  exact List.forall_mem_cons.2 ⟨sub9_160, List.forall_mem_cons.2 ⟨sub9_161, List.forall_mem_cons.2 ⟨sub9_162, List.forall_mem_cons.2 ⟨sub9_163, List.forall_mem_cons.2 ⟨sub9_164, List.forall_mem_cons.2 ⟨sub9_165, List.forall_mem_cons.2 ⟨sub9_166, List.forall_mem_cons.2 ⟨sub9_167, List.forall_mem_cons.2 ⟨sub9_168, List.forall_mem_cons.2 ⟨sub9_169, List.forall_mem_cons.2 ⟨sub9_170, List.forall_mem_cons.2 ⟨sub9_171, List.forall_mem_cons.2 ⟨sub9_172, List.forall_mem_cons.2 ⟨sub9_173, List.forall_mem_cons.2 ⟨sub9_174, List.forall_mem_cons.2 ⟨sub9_175, List.forall_mem_cons.2 ⟨sub9_176, List.forall_mem_cons.2 ⟨sub9_177, List.forall_mem_cons.2 ⟨sub9_178, List.forall_mem_cons.2 ⟨sub9_179, List.forall_mem_cons.2 ⟨sub9_180, List.forall_mem_cons.2 ⟨sub9_181, List.forall_mem_cons.2 ⟨sub9_182, List.forall_mem_cons.2 ⟨sub9_183, List.forall_mem_cons.2 ⟨sub9_184, List.forall_mem_cons.2 ⟨sub9_185, List.forall_mem_cons.2 ⟨sub9_186, List.forall_mem_cons.2 ⟨sub9_187, List.forall_mem_cons.2 ⟨sub9_188, List.forall_mem_cons.2 ⟨sub9_189, List.forall_mem_cons.2 ⟨sub9_190, List.forall_mem_cons.2 ⟨sub9_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_192 : sub9 [0, -2, 6] = true := by decide +kernel
theorem sub9_193 : sub9 [0, -2, 7] = true := by decide +kernel
theorem sub9_194 : sub9 [0, -1, -7] = true := by decide +kernel
theorem sub9_195 : sub9 [0, -1, -6] = true := by decide +kernel
theorem sub9_196 : sub9 [0, -1, -5] = true := by decide +kernel
theorem sub9_197 : sub9 [0, -1, -4] = true := by decide +kernel
theorem sub9_198 : sub9 [0, -1, -3] = true := by decide +kernel
theorem sub9_199 : sub9 [0, -1, -2] = true := by decide +kernel
theorem sub9_200 : sub9 [0, -1, -1] = true := by decide +kernel
theorem sub9_201 : sub9 [0, -1, 0] = true := by decide +kernel
theorem sub9_202 : sub9 [0, -1, 1] = true := by decide +kernel
theorem sub9_203 : sub9 [0, -1, 2] = true := by decide +kernel
theorem sub9_204 : sub9 [0, -1, 3] = true := by decide +kernel
theorem sub9_205 : sub9 [0, -1, 4] = true := by decide +kernel
theorem sub9_206 : sub9 [0, -1, 5] = true := by decide +kernel
theorem sub9_207 : sub9 [0, -1, 6] = true := by decide +kernel
theorem sub9_208 : sub9 [0, -1, 7] = true := by decide +kernel
theorem sub9_209 : sub9 [0, 0, -8] = true := by decide +kernel
theorem sub9_210 : sub9 [0, 0, -7] = true := by decide +kernel
theorem sub9_211 : sub9 [0, 0, -6] = true := by decide +kernel
theorem sub9_212 : sub9 [0, 0, -5] = true := by decide +kernel
theorem sub9_213 : sub9 [0, 0, -4] = true := by decide +kernel
theorem sub9_214 : sub9 [0, 0, -3] = true := by decide +kernel
theorem sub9_215 : sub9 [0, 0, -2] = true := by decide +kernel
theorem sub9_216 : sub9 [0, 0, -1] = true := by decide +kernel
theorem sub9_217 : sub9 [0, 0, 0] = true := by decide +kernel
theorem sub9_218 : sub9 [0, 0, 1] = true := by decide +kernel
theorem sub9_219 : sub9 [0, 0, 2] = true := by decide +kernel
theorem sub9_220 : sub9 [0, 0, 3] = true := by decide +kernel
theorem sub9_221 : sub9 [0, 0, 4] = true := by decide +kernel
theorem sub9_222 : sub9 [0, 0, 5] = true := by decide +kernel
theorem sub9_223 : sub9 [0, 0, 6] = true := by decide +kernel
theorem sb9_6 : ∀ q ∈ blk9_6, sub9 q = true := by
  unfold blk9_6
  exact List.forall_mem_cons.2 ⟨sub9_192, List.forall_mem_cons.2 ⟨sub9_193, List.forall_mem_cons.2 ⟨sub9_194, List.forall_mem_cons.2 ⟨sub9_195, List.forall_mem_cons.2 ⟨sub9_196, List.forall_mem_cons.2 ⟨sub9_197, List.forall_mem_cons.2 ⟨sub9_198, List.forall_mem_cons.2 ⟨sub9_199, List.forall_mem_cons.2 ⟨sub9_200, List.forall_mem_cons.2 ⟨sub9_201, List.forall_mem_cons.2 ⟨sub9_202, List.forall_mem_cons.2 ⟨sub9_203, List.forall_mem_cons.2 ⟨sub9_204, List.forall_mem_cons.2 ⟨sub9_205, List.forall_mem_cons.2 ⟨sub9_206, List.forall_mem_cons.2 ⟨sub9_207, List.forall_mem_cons.2 ⟨sub9_208, List.forall_mem_cons.2 ⟨sub9_209, List.forall_mem_cons.2 ⟨sub9_210, List.forall_mem_cons.2 ⟨sub9_211, List.forall_mem_cons.2 ⟨sub9_212, List.forall_mem_cons.2 ⟨sub9_213, List.forall_mem_cons.2 ⟨sub9_214, List.forall_mem_cons.2 ⟨sub9_215, List.forall_mem_cons.2 ⟨sub9_216, List.forall_mem_cons.2 ⟨sub9_217, List.forall_mem_cons.2 ⟨sub9_218, List.forall_mem_cons.2 ⟨sub9_219, List.forall_mem_cons.2 ⟨sub9_220, List.forall_mem_cons.2 ⟨sub9_221, List.forall_mem_cons.2 ⟨sub9_222, List.forall_mem_cons.2 ⟨sub9_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_224 : sub9 [0, 0, 7] = true := by decide +kernel
theorem sub9_225 : sub9 [0, 1, -8] = true := by decide +kernel
theorem sub9_226 : sub9 [0, 1, -7] = true := by decide +kernel
theorem sub9_227 : sub9 [0, 1, -6] = true := by decide +kernel
theorem sub9_228 : sub9 [0, 1, -5] = true := by decide +kernel
theorem sub9_229 : sub9 [0, 1, -4] = true := by decide +kernel
theorem sub9_230 : sub9 [0, 1, -3] = true := by decide +kernel
theorem sub9_231 : sub9 [0, 1, -2] = true := by decide +kernel
theorem sub9_232 : sub9 [0, 1, -1] = true := by decide +kernel
theorem sub9_233 : sub9 [0, 1, 0] = true := by decide +kernel
theorem sub9_234 : sub9 [0, 1, 1] = true := by decide +kernel
theorem sub9_235 : sub9 [0, 1, 2] = true := by decide +kernel
theorem sub9_236 : sub9 [0, 1, 3] = true := by decide +kernel
theorem sub9_237 : sub9 [0, 1, 4] = true := by decide +kernel
theorem sub9_238 : sub9 [0, 1, 5] = true := by decide +kernel
theorem sub9_239 : sub9 [0, 1, 6] = true := by decide +kernel
theorem sub9_240 : sub9 [0, 2, -8] = true := by decide +kernel
theorem sub9_241 : sub9 [0, 2, -7] = true := by decide +kernel
theorem sub9_242 : sub9 [0, 2, -6] = true := by decide +kernel
theorem sub9_243 : sub9 [0, 2, -5] = true := by decide +kernel
theorem sub9_244 : sub9 [0, 2, -4] = true := by decide +kernel
theorem sub9_245 : sub9 [0, 2, -3] = true := by decide +kernel
theorem sub9_246 : sub9 [0, 2, -2] = true := by decide +kernel
theorem sub9_247 : sub9 [0, 2, -1] = true := by decide +kernel
theorem sub9_248 : sub9 [0, 2, 0] = true := by decide +kernel
theorem sub9_249 : sub9 [0, 2, 1] = true := by decide +kernel
theorem sub9_250 : sub9 [0, 2, 2] = true := by decide +kernel
theorem sub9_251 : sub9 [0, 2, 3] = true := by decide +kernel
theorem sub9_252 : sub9 [0, 2, 4] = true := by decide +kernel
theorem sub9_253 : sub9 [0, 2, 5] = true := by decide +kernel
theorem sub9_254 : sub9 [0, 3] = true := by decide +kernel
theorem sub9_255 : sub9 [0, 4] = true := by decide +kernel
theorem sb9_7 : ∀ q ∈ blk9_7, sub9 q = true := by
  unfold blk9_7
  exact List.forall_mem_cons.2 ⟨sub9_224, List.forall_mem_cons.2 ⟨sub9_225, List.forall_mem_cons.2 ⟨sub9_226, List.forall_mem_cons.2 ⟨sub9_227, List.forall_mem_cons.2 ⟨sub9_228, List.forall_mem_cons.2 ⟨sub9_229, List.forall_mem_cons.2 ⟨sub9_230, List.forall_mem_cons.2 ⟨sub9_231, List.forall_mem_cons.2 ⟨sub9_232, List.forall_mem_cons.2 ⟨sub9_233, List.forall_mem_cons.2 ⟨sub9_234, List.forall_mem_cons.2 ⟨sub9_235, List.forall_mem_cons.2 ⟨sub9_236, List.forall_mem_cons.2 ⟨sub9_237, List.forall_mem_cons.2 ⟨sub9_238, List.forall_mem_cons.2 ⟨sub9_239, List.forall_mem_cons.2 ⟨sub9_240, List.forall_mem_cons.2 ⟨sub9_241, List.forall_mem_cons.2 ⟨sub9_242, List.forall_mem_cons.2 ⟨sub9_243, List.forall_mem_cons.2 ⟨sub9_244, List.forall_mem_cons.2 ⟨sub9_245, List.forall_mem_cons.2 ⟨sub9_246, List.forall_mem_cons.2 ⟨sub9_247, List.forall_mem_cons.2 ⟨sub9_248, List.forall_mem_cons.2 ⟨sub9_249, List.forall_mem_cons.2 ⟨sub9_250, List.forall_mem_cons.2 ⟨sub9_251, List.forall_mem_cons.2 ⟨sub9_252, List.forall_mem_cons.2 ⟨sub9_253, List.forall_mem_cons.2 ⟨sub9_254, List.forall_mem_cons.2 ⟨sub9_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_256 : sub9 [0, 5] = true := by decide +kernel
theorem sub9_257 : sub9 [0, 6] = true := by decide +kernel
theorem sub9_258 : sub9 [0, 7] = true := by decide +kernel
theorem sub9_259 : sub9 [1, -7] = true := by decide +kernel
theorem sub9_260 : sub9 [1, -6] = true := by decide +kernel
theorem sub9_261 : sub9 [1, -5] = true := by decide +kernel
theorem sub9_262 : sub9 [1, -4] = true := by decide +kernel
theorem sub9_263 : sub9 [1, -3] = true := by decide +kernel
theorem sub9_264 : sub9 [1, -2, -6] = true := by decide +kernel
theorem sub9_265 : sub9 [1, -2, -5] = true := by decide +kernel
theorem sub9_266 : sub9 [1, -2, -4] = true := by decide +kernel
theorem sub9_267 : sub9 [1, -2, -3] = true := by decide +kernel
theorem sub9_268 : sub9 [1, -2, -2] = true := by decide +kernel
theorem sub9_269 : sub9 [1, -2, -1] = true := by decide +kernel
theorem sub9_270 : sub9 [1, -2, 0] = true := by decide +kernel
theorem sub9_271 : sub9 [1, -2, 1] = true := by decide +kernel
theorem sub9_272 : sub9 [1, -2, 2] = true := by decide +kernel
theorem sub9_273 : sub9 [1, -2, 3] = true := by decide +kernel
theorem sub9_274 : sub9 [1, -2, 4] = true := by decide +kernel
theorem sub9_275 : sub9 [1, -2, 5] = true := by decide +kernel
theorem sub9_276 : sub9 [1, -2, 6] = true := by decide +kernel
theorem sub9_277 : sub9 [1, -2, 7] = true := by decide +kernel
theorem sub9_278 : sub9 [1, -1, -7] = true := by decide +kernel
theorem sub9_279 : sub9 [1, -1, -6] = true := by decide +kernel
theorem sub9_280 : sub9 [1, -1, -5] = true := by decide +kernel
theorem sub9_281 : sub9 [1, -1, -4] = true := by decide +kernel
theorem sub9_282 : sub9 [1, -1, -3] = true := by decide +kernel
theorem sub9_283 : sub9 [1, -1, -2] = true := by decide +kernel
theorem sub9_284 : sub9 [1, -1, -1] = true := by decide +kernel
theorem sub9_285 : sub9 [1, -1, 0] = true := by decide +kernel
theorem sub9_286 : sub9 [1, -1, 1] = true := by decide +kernel
theorem sub9_287 : sub9 [1, -1, 2] = true := by decide +kernel
theorem sb9_8 : ∀ q ∈ blk9_8, sub9 q = true := by
  unfold blk9_8
  exact List.forall_mem_cons.2 ⟨sub9_256, List.forall_mem_cons.2 ⟨sub9_257, List.forall_mem_cons.2 ⟨sub9_258, List.forall_mem_cons.2 ⟨sub9_259, List.forall_mem_cons.2 ⟨sub9_260, List.forall_mem_cons.2 ⟨sub9_261, List.forall_mem_cons.2 ⟨sub9_262, List.forall_mem_cons.2 ⟨sub9_263, List.forall_mem_cons.2 ⟨sub9_264, List.forall_mem_cons.2 ⟨sub9_265, List.forall_mem_cons.2 ⟨sub9_266, List.forall_mem_cons.2 ⟨sub9_267, List.forall_mem_cons.2 ⟨sub9_268, List.forall_mem_cons.2 ⟨sub9_269, List.forall_mem_cons.2 ⟨sub9_270, List.forall_mem_cons.2 ⟨sub9_271, List.forall_mem_cons.2 ⟨sub9_272, List.forall_mem_cons.2 ⟨sub9_273, List.forall_mem_cons.2 ⟨sub9_274, List.forall_mem_cons.2 ⟨sub9_275, List.forall_mem_cons.2 ⟨sub9_276, List.forall_mem_cons.2 ⟨sub9_277, List.forall_mem_cons.2 ⟨sub9_278, List.forall_mem_cons.2 ⟨sub9_279, List.forall_mem_cons.2 ⟨sub9_280, List.forall_mem_cons.2 ⟨sub9_281, List.forall_mem_cons.2 ⟨sub9_282, List.forall_mem_cons.2 ⟨sub9_283, List.forall_mem_cons.2 ⟨sub9_284, List.forall_mem_cons.2 ⟨sub9_285, List.forall_mem_cons.2 ⟨sub9_286, List.forall_mem_cons.2 ⟨sub9_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_288 : sub9 [1, -1, 3] = true := by decide +kernel
theorem sub9_289 : sub9 [1, -1, 4] = true := by decide +kernel
theorem sub9_290 : sub9 [1, -1, 5] = true := by decide +kernel
theorem sub9_291 : sub9 [1, -1, 6] = true := by decide +kernel
theorem sub9_292 : sub9 [1, -1, 7] = true := by decide +kernel
theorem sub9_293 : sub9 [1, 0, -8] = true := by decide +kernel
theorem sub9_294 : sub9 [1, 0, -7] = true := by decide +kernel
theorem sub9_295 : sub9 [1, 0, -6] = true := by decide +kernel
theorem sub9_296 : sub9 [1, 0, -5] = true := by decide +kernel
theorem sub9_297 : sub9 [1, 0, -4] = true := by decide +kernel
theorem sub9_298 : sub9 [1, 0, -3] = true := by decide +kernel
theorem sub9_299 : sub9 [1, 0, -2] = true := by decide +kernel
theorem sub9_300 : sub9 [1, 0, -1] = true := by decide +kernel
theorem sub9_301 : sub9 [1, 0, 0] = true := by decide +kernel
theorem sub9_302 : sub9 [1, 0, 1] = true := by decide +kernel
theorem sub9_303 : sub9 [1, 0, 2] = true := by decide +kernel
theorem sub9_304 : sub9 [1, 0, 3] = true := by decide +kernel
theorem sub9_305 : sub9 [1, 0, 4] = true := by decide +kernel
theorem sub9_306 : sub9 [1, 0, 5] = true := by decide +kernel
theorem sub9_307 : sub9 [1, 0, 6] = true := by decide +kernel
theorem sub9_308 : sub9 [1, 1, -8] = true := by decide +kernel
theorem sub9_309 : sub9 [1, 1, -7] = true := by decide +kernel
theorem sub9_310 : sub9 [1, 1, -6] = true := by decide +kernel
theorem sub9_311 : sub9 [1, 1, -5] = true := by decide +kernel
theorem sub9_312 : sub9 [1, 1, -4] = true := by decide +kernel
theorem sub9_313 : sub9 [1, 1, -3] = true := by decide +kernel
theorem sub9_314 : sub9 [1, 1, -2] = true := by decide +kernel
theorem sub9_315 : sub9 [1, 1, -1] = true := by decide +kernel
theorem sub9_316 : sub9 [1, 1, 0] = true := by decide +kernel
theorem sub9_317 : sub9 [1, 1, 1] = true := by decide +kernel
theorem sub9_318 : sub9 [1, 1, 2] = true := by decide +kernel
theorem sub9_319 : sub9 [1, 1, 3] = true := by decide +kernel
theorem sb9_9 : ∀ q ∈ blk9_9, sub9 q = true := by
  unfold blk9_9
  exact List.forall_mem_cons.2 ⟨sub9_288, List.forall_mem_cons.2 ⟨sub9_289, List.forall_mem_cons.2 ⟨sub9_290, List.forall_mem_cons.2 ⟨sub9_291, List.forall_mem_cons.2 ⟨sub9_292, List.forall_mem_cons.2 ⟨sub9_293, List.forall_mem_cons.2 ⟨sub9_294, List.forall_mem_cons.2 ⟨sub9_295, List.forall_mem_cons.2 ⟨sub9_296, List.forall_mem_cons.2 ⟨sub9_297, List.forall_mem_cons.2 ⟨sub9_298, List.forall_mem_cons.2 ⟨sub9_299, List.forall_mem_cons.2 ⟨sub9_300, List.forall_mem_cons.2 ⟨sub9_301, List.forall_mem_cons.2 ⟨sub9_302, List.forall_mem_cons.2 ⟨sub9_303, List.forall_mem_cons.2 ⟨sub9_304, List.forall_mem_cons.2 ⟨sub9_305, List.forall_mem_cons.2 ⟨sub9_306, List.forall_mem_cons.2 ⟨sub9_307, List.forall_mem_cons.2 ⟨sub9_308, List.forall_mem_cons.2 ⟨sub9_309, List.forall_mem_cons.2 ⟨sub9_310, List.forall_mem_cons.2 ⟨sub9_311, List.forall_mem_cons.2 ⟨sub9_312, List.forall_mem_cons.2 ⟨sub9_313, List.forall_mem_cons.2 ⟨sub9_314, List.forall_mem_cons.2 ⟨sub9_315, List.forall_mem_cons.2 ⟨sub9_316, List.forall_mem_cons.2 ⟨sub9_317, List.forall_mem_cons.2 ⟨sub9_318, List.forall_mem_cons.2 ⟨sub9_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_320 : sub9 [1, 1, 4] = true := by decide +kernel
theorem sub9_321 : sub9 [1, 1, 5] = true := by decide +kernel
theorem sub9_322 : sub9 [1, 1, 6] = true := by decide +kernel
theorem sub9_323 : sub9 [1, 2, -8] = true := by decide +kernel
theorem sub9_324 : sub9 [1, 2, -7] = true := by decide +kernel
theorem sub9_325 : sub9 [1, 2, -6] = true := by decide +kernel
theorem sub9_326 : sub9 [1, 2, -5] = true := by decide +kernel
theorem sub9_327 : sub9 [1, 2, -4] = true := by decide +kernel
theorem sub9_328 : sub9 [1, 2, -3] = true := by decide +kernel
theorem sub9_329 : sub9 [1, 2, -2] = true := by decide +kernel
theorem sub9_330 : sub9 [1, 2, -1] = true := by decide +kernel
theorem sub9_331 : sub9 [1, 2, 0] = true := by decide +kernel
theorem sub9_332 : sub9 [1, 2, 1] = true := by decide +kernel
theorem sub9_333 : sub9 [1, 2, 2] = true := by decide +kernel
theorem sub9_334 : sub9 [1, 2, 3] = true := by decide +kernel
theorem sub9_335 : sub9 [1, 2, 4] = true := by decide +kernel
theorem sub9_336 : sub9 [1, 2, 5] = true := by decide +kernel
theorem sub9_337 : sub9 [1, 3] = true := by decide +kernel
theorem sub9_338 : sub9 [1, 4] = true := by decide +kernel
theorem sub9_339 : sub9 [1, 5] = true := by decide +kernel
theorem sub9_340 : sub9 [1, 6] = true := by decide +kernel
theorem sub9_341 : sub9 [1, 7] = true := by decide +kernel
theorem sub9_342 : sub9 [2, -7] = true := by decide +kernel
theorem sub9_343 : sub9 [2, -6] = true := by decide +kernel
theorem sub9_344 : sub9 [2, -5] = true := by decide +kernel
theorem sub9_345 : sub9 [2, -4] = true := by decide +kernel
theorem sub9_346 : sub9 [2, -3] = true := by decide +kernel
theorem sub9_347 : sub9 [2, -2] = true := by decide +kernel
theorem sub9_348 : sub9 [2, -1] = true := by decide +kernel
theorem sub9_349 : sub9 [2, 0, -7] = true := by decide +kernel
theorem sub9_350 : sub9 [2, 0, -6] = true := by decide +kernel
theorem sub9_351 : sub9 [2, 0, -5] = true := by decide +kernel
theorem sb9_10 : ∀ q ∈ blk9_10, sub9 q = true := by
  unfold blk9_10
  exact List.forall_mem_cons.2 ⟨sub9_320, List.forall_mem_cons.2 ⟨sub9_321, List.forall_mem_cons.2 ⟨sub9_322, List.forall_mem_cons.2 ⟨sub9_323, List.forall_mem_cons.2 ⟨sub9_324, List.forall_mem_cons.2 ⟨sub9_325, List.forall_mem_cons.2 ⟨sub9_326, List.forall_mem_cons.2 ⟨sub9_327, List.forall_mem_cons.2 ⟨sub9_328, List.forall_mem_cons.2 ⟨sub9_329, List.forall_mem_cons.2 ⟨sub9_330, List.forall_mem_cons.2 ⟨sub9_331, List.forall_mem_cons.2 ⟨sub9_332, List.forall_mem_cons.2 ⟨sub9_333, List.forall_mem_cons.2 ⟨sub9_334, List.forall_mem_cons.2 ⟨sub9_335, List.forall_mem_cons.2 ⟨sub9_336, List.forall_mem_cons.2 ⟨sub9_337, List.forall_mem_cons.2 ⟨sub9_338, List.forall_mem_cons.2 ⟨sub9_339, List.forall_mem_cons.2 ⟨sub9_340, List.forall_mem_cons.2 ⟨sub9_341, List.forall_mem_cons.2 ⟨sub9_342, List.forall_mem_cons.2 ⟨sub9_343, List.forall_mem_cons.2 ⟨sub9_344, List.forall_mem_cons.2 ⟨sub9_345, List.forall_mem_cons.2 ⟨sub9_346, List.forall_mem_cons.2 ⟨sub9_347, List.forall_mem_cons.2 ⟨sub9_348, List.forall_mem_cons.2 ⟨sub9_349, List.forall_mem_cons.2 ⟨sub9_350, List.forall_mem_cons.2 ⟨sub9_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_352 : sub9 [2, 0, -4] = true := by decide +kernel
theorem sub9_353 : sub9 [2, 0, -3] = true := by decide +kernel
theorem sub9_354 : sub9 [2, 0, -2] = true := by decide +kernel
theorem sub9_355 : sub9 [2, 0, -1] = true := by decide +kernel
theorem sub9_356 : sub9 [2, 0, 0] = true := by decide +kernel
theorem sub9_357 : sub9 [2, 0, 1] = true := by decide +kernel
theorem sub9_358 : sub9 [2, 0, 2] = true := by decide +kernel
theorem sub9_359 : sub9 [2, 0, 3] = true := by decide +kernel
theorem sub9_360 : sub9 [2, 0, 4] = true := by decide +kernel
theorem sub9_361 : sub9 [2, 0, 5] = true := by decide +kernel
theorem sub9_362 : sub9 [2, 0, 6] = true := by decide +kernel
theorem sub9_363 : sub9 [2, 1, -8] = true := by decide +kernel
theorem sub9_364 : sub9 [2, 1, -7] = true := by decide +kernel
theorem sub9_365 : sub9 [2, 1, -6] = true := by decide +kernel
theorem sub9_366 : sub9 [2, 1, -5] = true := by decide +kernel
theorem sub9_367 : sub9 [2, 1, -4] = true := by decide +kernel
theorem sub9_368 : sub9 [2, 1, -3] = true := by decide +kernel
theorem sub9_369 : sub9 [2, 1, -2] = true := by decide +kernel
theorem sub9_370 : sub9 [2, 1, -1] = true := by decide +kernel
theorem sub9_371 : sub9 [2, 1, 0] = true := by decide +kernel
theorem sub9_372 : sub9 [2, 1, 1] = true := by decide +kernel
theorem sub9_373 : sub9 [2, 1, 2] = true := by decide +kernel
theorem sub9_374 : sub9 [2, 1, 3] = true := by decide +kernel
theorem sub9_375 : sub9 [2, 1, 4] = true := by decide +kernel
theorem sub9_376 : sub9 [2, 1, 5] = true := by decide +kernel
theorem sub9_377 : sub9 [2, 1, 6] = true := by decide +kernel
theorem sub9_378 : sub9 [2, 2, -8] = true := by decide +kernel
theorem sub9_379 : sub9 [2, 2, -7] = true := by decide +kernel
theorem sub9_380 : sub9 [2, 2, -6] = true := by decide +kernel
theorem sub9_381 : sub9 [2, 2, -5] = true := by decide +kernel
theorem sub9_382 : sub9 [2, 2, -4] = true := by decide +kernel
theorem sub9_383 : sub9 [2, 2, -3] = true := by decide +kernel
theorem sb9_11 : ∀ q ∈ blk9_11, sub9 q = true := by
  unfold blk9_11
  exact List.forall_mem_cons.2 ⟨sub9_352, List.forall_mem_cons.2 ⟨sub9_353, List.forall_mem_cons.2 ⟨sub9_354, List.forall_mem_cons.2 ⟨sub9_355, List.forall_mem_cons.2 ⟨sub9_356, List.forall_mem_cons.2 ⟨sub9_357, List.forall_mem_cons.2 ⟨sub9_358, List.forall_mem_cons.2 ⟨sub9_359, List.forall_mem_cons.2 ⟨sub9_360, List.forall_mem_cons.2 ⟨sub9_361, List.forall_mem_cons.2 ⟨sub9_362, List.forall_mem_cons.2 ⟨sub9_363, List.forall_mem_cons.2 ⟨sub9_364, List.forall_mem_cons.2 ⟨sub9_365, List.forall_mem_cons.2 ⟨sub9_366, List.forall_mem_cons.2 ⟨sub9_367, List.forall_mem_cons.2 ⟨sub9_368, List.forall_mem_cons.2 ⟨sub9_369, List.forall_mem_cons.2 ⟨sub9_370, List.forall_mem_cons.2 ⟨sub9_371, List.forall_mem_cons.2 ⟨sub9_372, List.forall_mem_cons.2 ⟨sub9_373, List.forall_mem_cons.2 ⟨sub9_374, List.forall_mem_cons.2 ⟨sub9_375, List.forall_mem_cons.2 ⟨sub9_376, List.forall_mem_cons.2 ⟨sub9_377, List.forall_mem_cons.2 ⟨sub9_378, List.forall_mem_cons.2 ⟨sub9_379, List.forall_mem_cons.2 ⟨sub9_380, List.forall_mem_cons.2 ⟨sub9_381, List.forall_mem_cons.2 ⟨sub9_382, List.forall_mem_cons.2 ⟨sub9_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_384 : sub9 [2, 2, -2] = true := by decide +kernel
theorem sub9_385 : sub9 [2, 2, -1] = true := by decide +kernel
theorem sub9_386 : sub9 [2, 2, 0] = true := by decide +kernel
theorem sub9_387 : sub9 [2, 2, 1] = true := by decide +kernel
theorem sub9_388 : sub9 [2, 2, 2] = true := by decide +kernel
theorem sub9_389 : sub9 [2, 2, 3] = true := by decide +kernel
theorem sub9_390 : sub9 [2, 2, 4] = true := by decide +kernel
theorem sub9_391 : sub9 [2, 2, 5] = true := by decide +kernel
theorem sub9_392 : sub9 [2, 3] = true := by decide +kernel
theorem sub9_393 : sub9 [2, 4] = true := by decide +kernel
theorem sub9_394 : sub9 [2, 5] = true := by decide +kernel
theorem sub9_395 : sub9 [2, 6] = true := by decide +kernel
theorem sub9_396 : sub9 [2, 7] = true := by decide +kernel
theorem sub9_397 : sub9 [3, -6] = true := by decide +kernel
theorem sub9_398 : sub9 [3, -5] = true := by decide +kernel
theorem sub9_399 : sub9 [3, -4] = true := by decide +kernel
theorem sub9_400 : sub9 [3, -3] = true := by decide +kernel
theorem sub9_401 : sub9 [3, -2] = true := by decide +kernel
theorem sub9_402 : sub9 [3, -1] = true := by decide +kernel
theorem sub9_403 : sub9 [3, 0] = true := by decide +kernel
theorem sub9_404 : sub9 [3, 1] = true := by decide +kernel
theorem sub9_405 : sub9 [3, 2] = true := by decide +kernel
theorem sub9_406 : sub9 [3, 3] = true := by decide +kernel
theorem sub9_407 : sub9 [3, 4] = true := by decide +kernel
theorem sub9_408 : sub9 [3, 5] = true := by decide +kernel
theorem sub9_409 : sub9 [3, 6] = true := by decide +kernel
theorem sub9_410 : sub9 [3, 7] = true := by decide +kernel
theorem sub9_411 : sub9 [4, -5] = true := by decide +kernel
theorem sub9_412 : sub9 [4, -4] = true := by decide +kernel
theorem sub9_413 : sub9 [4, -3] = true := by decide +kernel
theorem sub9_414 : sub9 [4, -2] = true := by decide +kernel
theorem sub9_415 : sub9 [4, -1] = true := by decide +kernel
theorem sb9_12 : ∀ q ∈ blk9_12, sub9 q = true := by
  unfold blk9_12
  exact List.forall_mem_cons.2 ⟨sub9_384, List.forall_mem_cons.2 ⟨sub9_385, List.forall_mem_cons.2 ⟨sub9_386, List.forall_mem_cons.2 ⟨sub9_387, List.forall_mem_cons.2 ⟨sub9_388, List.forall_mem_cons.2 ⟨sub9_389, List.forall_mem_cons.2 ⟨sub9_390, List.forall_mem_cons.2 ⟨sub9_391, List.forall_mem_cons.2 ⟨sub9_392, List.forall_mem_cons.2 ⟨sub9_393, List.forall_mem_cons.2 ⟨sub9_394, List.forall_mem_cons.2 ⟨sub9_395, List.forall_mem_cons.2 ⟨sub9_396, List.forall_mem_cons.2 ⟨sub9_397, List.forall_mem_cons.2 ⟨sub9_398, List.forall_mem_cons.2 ⟨sub9_399, List.forall_mem_cons.2 ⟨sub9_400, List.forall_mem_cons.2 ⟨sub9_401, List.forall_mem_cons.2 ⟨sub9_402, List.forall_mem_cons.2 ⟨sub9_403, List.forall_mem_cons.2 ⟨sub9_404, List.forall_mem_cons.2 ⟨sub9_405, List.forall_mem_cons.2 ⟨sub9_406, List.forall_mem_cons.2 ⟨sub9_407, List.forall_mem_cons.2 ⟨sub9_408, List.forall_mem_cons.2 ⟨sub9_409, List.forall_mem_cons.2 ⟨sub9_410, List.forall_mem_cons.2 ⟨sub9_411, List.forall_mem_cons.2 ⟨sub9_412, List.forall_mem_cons.2 ⟨sub9_413, List.forall_mem_cons.2 ⟨sub9_414, List.forall_mem_cons.2 ⟨sub9_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C104
