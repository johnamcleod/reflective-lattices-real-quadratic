import ReflectZphi.Data.Cert5.C125.Base

namespace ReflectZphi.Data.Cert5.C125
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_160 : sub8 [-1, -1, 2] = true := by decide +kernel
theorem sub8_161 : sub8 [-1, -1, 3] = true := by decide +kernel
theorem sub8_162 : sub8 [-1, -1, 4] = true := by decide +kernel
theorem sub8_163 : sub8 [-1, -1, 5] = true := by decide +kernel
theorem sub8_164 : sub8 [-1, -1, 6] = true := by decide +kernel
theorem sub8_165 : sub8 [-1, -1, 7] = true := by decide +kernel
theorem sub8_166 : sub8 [-1, 0, -7] = true := by decide +kernel
theorem sub8_167 : sub8 [-1, 0, -6] = true := by decide +kernel
theorem sub8_168 : sub8 [-1, 0, -5] = true := by decide +kernel
theorem sub8_169 : sub8 [-1, 0, -4] = true := by decide +kernel
theorem sub8_170 : sub8 [-1, 0, -3] = true := by decide +kernel
theorem sub8_171 : sub8 [-1, 0, -2] = true := by decide +kernel
theorem sub8_172 : sub8 [-1, 0, -1] = true := by decide +kernel
theorem sub8_173 : sub8 [-1, 0, 0] = true := by decide +kernel
theorem sub8_174 : sub8 [-1, 0, 1] = true := by decide +kernel
theorem sub8_175 : sub8 [-1, 0, 2] = true := by decide +kernel
theorem sub8_176 : sub8 [-1, 0, 3] = true := by decide +kernel
theorem sub8_177 : sub8 [-1, 0, 4] = true := by decide +kernel
theorem sub8_178 : sub8 [-1, 0, 5] = true := by decide +kernel
theorem sub8_179 : sub8 [-1, 0, 6] = true := by decide +kernel
theorem sub8_180 : sub8 [-1, 0, 7] = true := by decide +kernel
theorem sub8_181 : sub8 [-1, 1, -7] = true := by decide +kernel
theorem sub8_182 : sub8 [-1, 1, -6] = true := by decide +kernel
theorem sub8_183 : sub8 [-1, 1, -5] = true := by decide +kernel
theorem sub8_184 : sub8 [-1, 1, -4] = true := by decide +kernel
theorem sub8_185 : sub8 [-1, 1, -3] = true := by decide +kernel
theorem sub8_186 : sub8 [-1, 1, -2] = true := by decide +kernel
theorem sub8_187 : sub8 [-1, 1, -1] = true := by decide +kernel
theorem sub8_188 : sub8 [-1, 1, 0] = true := by decide +kernel
theorem sub8_189 : sub8 [-1, 1, 1] = true := by decide +kernel
theorem sub8_190 : sub8 [-1, 1, 2] = true := by decide +kernel
theorem sub8_191 : sub8 [-1, 1, 3] = true := by decide +kernel
theorem sb8_5 : ∀ q ∈ blk8_5, sub8 q = true := by
  unfold blk8_5
  exact List.forall_mem_cons.2 ⟨sub8_160, List.forall_mem_cons.2 ⟨sub8_161, List.forall_mem_cons.2 ⟨sub8_162, List.forall_mem_cons.2 ⟨sub8_163, List.forall_mem_cons.2 ⟨sub8_164, List.forall_mem_cons.2 ⟨sub8_165, List.forall_mem_cons.2 ⟨sub8_166, List.forall_mem_cons.2 ⟨sub8_167, List.forall_mem_cons.2 ⟨sub8_168, List.forall_mem_cons.2 ⟨sub8_169, List.forall_mem_cons.2 ⟨sub8_170, List.forall_mem_cons.2 ⟨sub8_171, List.forall_mem_cons.2 ⟨sub8_172, List.forall_mem_cons.2 ⟨sub8_173, List.forall_mem_cons.2 ⟨sub8_174, List.forall_mem_cons.2 ⟨sub8_175, List.forall_mem_cons.2 ⟨sub8_176, List.forall_mem_cons.2 ⟨sub8_177, List.forall_mem_cons.2 ⟨sub8_178, List.forall_mem_cons.2 ⟨sub8_179, List.forall_mem_cons.2 ⟨sub8_180, List.forall_mem_cons.2 ⟨sub8_181, List.forall_mem_cons.2 ⟨sub8_182, List.forall_mem_cons.2 ⟨sub8_183, List.forall_mem_cons.2 ⟨sub8_184, List.forall_mem_cons.2 ⟨sub8_185, List.forall_mem_cons.2 ⟨sub8_186, List.forall_mem_cons.2 ⟨sub8_187, List.forall_mem_cons.2 ⟨sub8_188, List.forall_mem_cons.2 ⟨sub8_189, List.forall_mem_cons.2 ⟨sub8_190, List.forall_mem_cons.2 ⟨sub8_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_192 : sub8 [-1, 1, 4] = true := by decide +kernel
theorem sub8_193 : sub8 [-1, 1, 5] = true := by decide +kernel
theorem sub8_194 : sub8 [-1, 1, 6] = true := by decide +kernel
theorem sub8_195 : sub8 [-1, 1, 7] = true := by decide +kernel
theorem sub8_196 : sub8 [-1, 2, -7] = true := by decide +kernel
theorem sub8_197 : sub8 [-1, 2, -6] = true := by decide +kernel
theorem sub8_198 : sub8 [-1, 2, -5] = true := by decide +kernel
theorem sub8_199 : sub8 [-1, 2, -4] = true := by decide +kernel
theorem sub8_200 : sub8 [-1, 2, -3] = true := by decide +kernel
theorem sub8_201 : sub8 [-1, 2, -2] = true := by decide +kernel
theorem sub8_202 : sub8 [-1, 2, -1] = true := by decide +kernel
theorem sub8_203 : sub8 [-1, 2, 0] = true := by decide +kernel
theorem sub8_204 : sub8 [-1, 2, 1] = true := by decide +kernel
theorem sub8_205 : sub8 [-1, 2, 2] = true := by decide +kernel
theorem sub8_206 : sub8 [-1, 2, 3] = true := by decide +kernel
theorem sub8_207 : sub8 [-1, 2, 4] = true := by decide +kernel
theorem sub8_208 : sub8 [-1, 2, 5] = true := by decide +kernel
theorem sub8_209 : sub8 [-1, 2, 6] = true := by decide +kernel
theorem sub8_210 : sub8 [-1, 2, 7] = true := by decide +kernel
theorem sub8_211 : sub8 [-1, 3, -7] = true := by decide +kernel
theorem sub8_212 : sub8 [-1, 3, -6] = true := by decide +kernel
theorem sub8_213 : sub8 [-1, 3, -5] = true := by decide +kernel
theorem sub8_214 : sub8 [-1, 3, -4] = true := by decide +kernel
theorem sub8_215 : sub8 [-1, 3, -3] = true := by decide +kernel
theorem sub8_216 : sub8 [-1, 3, -2] = true := by decide +kernel
theorem sub8_217 : sub8 [-1, 3, -1] = true := by decide +kernel
theorem sub8_218 : sub8 [-1, 3, 0] = true := by decide +kernel
theorem sub8_219 : sub8 [-1, 3, 1] = true := by decide +kernel
theorem sub8_220 : sub8 [-1, 3, 2] = true := by decide +kernel
theorem sub8_221 : sub8 [-1, 3, 3] = true := by decide +kernel
theorem sub8_222 : sub8 [-1, 3, 4] = true := by decide +kernel
theorem sub8_223 : sub8 [-1, 3, 5] = true := by decide +kernel
theorem sb8_6 : ∀ q ∈ blk8_6, sub8 q = true := by
  unfold blk8_6
  exact List.forall_mem_cons.2 ⟨sub8_192, List.forall_mem_cons.2 ⟨sub8_193, List.forall_mem_cons.2 ⟨sub8_194, List.forall_mem_cons.2 ⟨sub8_195, List.forall_mem_cons.2 ⟨sub8_196, List.forall_mem_cons.2 ⟨sub8_197, List.forall_mem_cons.2 ⟨sub8_198, List.forall_mem_cons.2 ⟨sub8_199, List.forall_mem_cons.2 ⟨sub8_200, List.forall_mem_cons.2 ⟨sub8_201, List.forall_mem_cons.2 ⟨sub8_202, List.forall_mem_cons.2 ⟨sub8_203, List.forall_mem_cons.2 ⟨sub8_204, List.forall_mem_cons.2 ⟨sub8_205, List.forall_mem_cons.2 ⟨sub8_206, List.forall_mem_cons.2 ⟨sub8_207, List.forall_mem_cons.2 ⟨sub8_208, List.forall_mem_cons.2 ⟨sub8_209, List.forall_mem_cons.2 ⟨sub8_210, List.forall_mem_cons.2 ⟨sub8_211, List.forall_mem_cons.2 ⟨sub8_212, List.forall_mem_cons.2 ⟨sub8_213, List.forall_mem_cons.2 ⟨sub8_214, List.forall_mem_cons.2 ⟨sub8_215, List.forall_mem_cons.2 ⟨sub8_216, List.forall_mem_cons.2 ⟨sub8_217, List.forall_mem_cons.2 ⟨sub8_218, List.forall_mem_cons.2 ⟨sub8_219, List.forall_mem_cons.2 ⟨sub8_220, List.forall_mem_cons.2 ⟨sub8_221, List.forall_mem_cons.2 ⟨sub8_222, List.forall_mem_cons.2 ⟨sub8_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_224 : sub8 [-1, 3, 6] = true := by decide +kernel
theorem sub8_225 : sub8 [-1, 4] = true := by decide +kernel
theorem sub8_226 : sub8 [-1, 5] = true := by decide +kernel
theorem sub8_227 : sub8 [-1, 6] = true := by decide +kernel
theorem sub8_228 : sub8 [0, -7] = true := by decide +kernel
theorem sub8_229 : sub8 [0, -6] = true := by decide +kernel
theorem sub8_230 : sub8 [0, -5] = true := by decide +kernel
theorem sub8_231 : sub8 [0, -4] = true := by decide +kernel
theorem sub8_232 : sub8 [0, -3, -7] = true := by decide +kernel
theorem sub8_233 : sub8 [0, -3, -6] = true := by decide +kernel
theorem sub8_234 : sub8 [0, -3, -5] = true := by decide +kernel
theorem sub8_235 : sub8 [0, -3, -4] = true := by decide +kernel
theorem sub8_236 : sub8 [0, -3, -3] = true := by decide +kernel
theorem sub8_237 : sub8 [0, -3, -2] = true := by decide +kernel
theorem sub8_238 : sub8 [0, -3, -1] = true := by decide +kernel
theorem sub8_239 : sub8 [0, -3, 0] = true := by decide +kernel
theorem sub8_240 : sub8 [0, -3, 1] = true := by decide +kernel
theorem sub8_241 : sub8 [0, -3, 2] = true := by decide +kernel
theorem sub8_242 : sub8 [0, -3, 3] = true := by decide +kernel
theorem sub8_243 : sub8 [0, -3, 4] = true := by decide +kernel
theorem sub8_244 : sub8 [0, -3, 5] = true := by decide +kernel
theorem sub8_245 : sub8 [0, -3, 6] = true := by decide +kernel
theorem sub8_246 : sub8 [0, -2, -7] = true := by decide +kernel
theorem sub8_247 : sub8 [0, -2, -6] = true := by decide +kernel
theorem sub8_248 : sub8 [0, -2, -5] = true := by decide +kernel
theorem sub8_249 : sub8 [0, -2, -4] = true := by decide +kernel
theorem sub8_250 : sub8 [0, -2, -3] = true := by decide +kernel
theorem sub8_251 : sub8 [0, -2, -2] = true := by decide +kernel
theorem sub8_252 : sub8 [0, -2, -1] = true := by decide +kernel
theorem sub8_253 : sub8 [0, -2, 0] = true := by decide +kernel
theorem sub8_254 : sub8 [0, -2, 1] = true := by decide +kernel
theorem sub8_255 : sub8 [0, -2, 2] = true := by decide +kernel
theorem sb8_7 : ∀ q ∈ blk8_7, sub8 q = true := by
  unfold blk8_7
  exact List.forall_mem_cons.2 ⟨sub8_224, List.forall_mem_cons.2 ⟨sub8_225, List.forall_mem_cons.2 ⟨sub8_226, List.forall_mem_cons.2 ⟨sub8_227, List.forall_mem_cons.2 ⟨sub8_228, List.forall_mem_cons.2 ⟨sub8_229, List.forall_mem_cons.2 ⟨sub8_230, List.forall_mem_cons.2 ⟨sub8_231, List.forall_mem_cons.2 ⟨sub8_232, List.forall_mem_cons.2 ⟨sub8_233, List.forall_mem_cons.2 ⟨sub8_234, List.forall_mem_cons.2 ⟨sub8_235, List.forall_mem_cons.2 ⟨sub8_236, List.forall_mem_cons.2 ⟨sub8_237, List.forall_mem_cons.2 ⟨sub8_238, List.forall_mem_cons.2 ⟨sub8_239, List.forall_mem_cons.2 ⟨sub8_240, List.forall_mem_cons.2 ⟨sub8_241, List.forall_mem_cons.2 ⟨sub8_242, List.forall_mem_cons.2 ⟨sub8_243, List.forall_mem_cons.2 ⟨sub8_244, List.forall_mem_cons.2 ⟨sub8_245, List.forall_mem_cons.2 ⟨sub8_246, List.forall_mem_cons.2 ⟨sub8_247, List.forall_mem_cons.2 ⟨sub8_248, List.forall_mem_cons.2 ⟨sub8_249, List.forall_mem_cons.2 ⟨sub8_250, List.forall_mem_cons.2 ⟨sub8_251, List.forall_mem_cons.2 ⟨sub8_252, List.forall_mem_cons.2 ⟨sub8_253, List.forall_mem_cons.2 ⟨sub8_254, List.forall_mem_cons.2 ⟨sub8_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_256 : sub8 [0, -2, 3] = true := by decide +kernel
theorem sub8_257 : sub8 [0, -2, 4] = true := by decide +kernel
theorem sub8_258 : sub8 [0, -2, 5] = true := by decide +kernel
theorem sub8_259 : sub8 [0, -2, 6] = true := by decide +kernel
theorem sub8_260 : sub8 [0, -2, 7] = true := by decide +kernel
theorem sub8_261 : sub8 [0, -1, -8] = true := by decide +kernel
theorem sub8_262 : sub8 [0, -1, -7] = true := by decide +kernel
theorem sub8_263 : sub8 [0, -1, -6] = true := by decide +kernel
theorem sub8_264 : sub8 [0, -1, -5] = true := by decide +kernel
theorem sub8_265 : sub8 [0, -1, -4] = true := by decide +kernel
theorem sub8_266 : sub8 [0, -1, -3] = true := by decide +kernel
theorem sub8_267 : sub8 [0, -1, -2] = true := by decide +kernel
theorem sub8_268 : sub8 [0, -1, -1] = true := by decide +kernel
theorem sub8_269 : sub8 [0, -1, 0] = true := by decide +kernel
theorem sub8_270 : sub8 [0, -1, 1] = true := by decide +kernel
theorem sub8_271 : sub8 [0, -1, 2] = true := by decide +kernel
theorem sub8_272 : sub8 [0, -1, 3] = true := by decide +kernel
theorem sub8_273 : sub8 [0, -1, 4] = true := by decide +kernel
theorem sub8_274 : sub8 [0, -1, 5] = true := by decide +kernel
theorem sub8_275 : sub8 [0, -1, 6] = true := by decide +kernel
theorem sub8_276 : sub8 [0, -1, 7] = true := by decide +kernel
theorem sub8_277 : sub8 [0, 0, -8] = true := by decide +kernel
theorem sub8_278 : sub8 [0, 0, -7] = true := by decide +kernel
theorem sub8_279 : sub8 [0, 0, -6] = true := by decide +kernel
theorem sub8_280 : sub8 [0, 0, -5] = true := by decide +kernel
theorem sub8_281 : sub8 [0, 0, -4] = true := by decide +kernel
theorem sub8_282 : sub8 [0, 0, -3] = true := by decide +kernel
theorem sub8_283 : sub8 [0, 0, -2] = true := by decide +kernel
theorem sub8_284 : sub8 [0, 0, -1] = true := by decide +kernel
theorem sub8_285 : sub8 [0, 0, 0] = true := by decide +kernel
theorem sub8_286 : sub8 [0, 0, 1] = true := by decide +kernel
theorem sub8_287 : sub8 [0, 0, 2] = true := by decide +kernel
theorem sb8_8 : ∀ q ∈ blk8_8, sub8 q = true := by
  unfold blk8_8
  exact List.forall_mem_cons.2 ⟨sub8_256, List.forall_mem_cons.2 ⟨sub8_257, List.forall_mem_cons.2 ⟨sub8_258, List.forall_mem_cons.2 ⟨sub8_259, List.forall_mem_cons.2 ⟨sub8_260, List.forall_mem_cons.2 ⟨sub8_261, List.forall_mem_cons.2 ⟨sub8_262, List.forall_mem_cons.2 ⟨sub8_263, List.forall_mem_cons.2 ⟨sub8_264, List.forall_mem_cons.2 ⟨sub8_265, List.forall_mem_cons.2 ⟨sub8_266, List.forall_mem_cons.2 ⟨sub8_267, List.forall_mem_cons.2 ⟨sub8_268, List.forall_mem_cons.2 ⟨sub8_269, List.forall_mem_cons.2 ⟨sub8_270, List.forall_mem_cons.2 ⟨sub8_271, List.forall_mem_cons.2 ⟨sub8_272, List.forall_mem_cons.2 ⟨sub8_273, List.forall_mem_cons.2 ⟨sub8_274, List.forall_mem_cons.2 ⟨sub8_275, List.forall_mem_cons.2 ⟨sub8_276, List.forall_mem_cons.2 ⟨sub8_277, List.forall_mem_cons.2 ⟨sub8_278, List.forall_mem_cons.2 ⟨sub8_279, List.forall_mem_cons.2 ⟨sub8_280, List.forall_mem_cons.2 ⟨sub8_281, List.forall_mem_cons.2 ⟨sub8_282, List.forall_mem_cons.2 ⟨sub8_283, List.forall_mem_cons.2 ⟨sub8_284, List.forall_mem_cons.2 ⟨sub8_285, List.forall_mem_cons.2 ⟨sub8_286, List.forall_mem_cons.2 ⟨sub8_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_288 : sub8 [0, 0, 3] = true := by decide +kernel
theorem sub8_289 : sub8 [0, 0, 4] = true := by decide +kernel
theorem sub8_290 : sub8 [0, 0, 5] = true := by decide +kernel
theorem sub8_291 : sub8 [0, 0, 6] = true := by decide +kernel
theorem sub8_292 : sub8 [0, 0, 7] = true := by decide +kernel
theorem sub8_293 : sub8 [0, 1, -8] = true := by decide +kernel
theorem sub8_294 : sub8 [0, 1, -7] = true := by decide +kernel
theorem sub8_295 : sub8 [0, 1, -6] = true := by decide +kernel
theorem sub8_296 : sub8 [0, 1, -5] = true := by decide +kernel
theorem sub8_297 : sub8 [0, 1, -4] = true := by decide +kernel
theorem sub8_298 : sub8 [0, 1, -3] = true := by decide +kernel
theorem sub8_299 : sub8 [0, 1, -2] = true := by decide +kernel
theorem sub8_300 : sub8 [0, 1, -1] = true := by decide +kernel
theorem sub8_301 : sub8 [0, 1, 0] = true := by decide +kernel
theorem sub8_302 : sub8 [0, 1, 1] = true := by decide +kernel
theorem sub8_303 : sub8 [0, 1, 2] = true := by decide +kernel
theorem sub8_304 : sub8 [0, 1, 3] = true := by decide +kernel
theorem sub8_305 : sub8 [0, 1, 4] = true := by decide +kernel
theorem sub8_306 : sub8 [0, 1, 5] = true := by decide +kernel
theorem sub8_307 : sub8 [0, 1, 6] = true := by decide +kernel
theorem sub8_308 : sub8 [0, 1, 7] = true := by decide +kernel
theorem sub8_309 : sub8 [0, 2, -8] = true := by decide +kernel
theorem sub8_310 : sub8 [0, 2, -7] = true := by decide +kernel
theorem sub8_311 : sub8 [0, 2, -6] = true := by decide +kernel
theorem sub8_312 : sub8 [0, 2, -5] = true := by decide +kernel
theorem sub8_313 : sub8 [0, 2, -4] = true := by decide +kernel
theorem sub8_314 : sub8 [0, 2, -3] = true := by decide +kernel
theorem sub8_315 : sub8 [0, 2, -2] = true := by decide +kernel
theorem sub8_316 : sub8 [0, 2, -1] = true := by decide +kernel
theorem sub8_317 : sub8 [0, 2, 0] = true := by decide +kernel
theorem sub8_318 : sub8 [0, 2, 1] = true := by decide +kernel
theorem sub8_319 : sub8 [0, 2, 2] = true := by decide +kernel
theorem sb8_9 : ∀ q ∈ blk8_9, sub8 q = true := by
  unfold blk8_9
  exact List.forall_mem_cons.2 ⟨sub8_288, List.forall_mem_cons.2 ⟨sub8_289, List.forall_mem_cons.2 ⟨sub8_290, List.forall_mem_cons.2 ⟨sub8_291, List.forall_mem_cons.2 ⟨sub8_292, List.forall_mem_cons.2 ⟨sub8_293, List.forall_mem_cons.2 ⟨sub8_294, List.forall_mem_cons.2 ⟨sub8_295, List.forall_mem_cons.2 ⟨sub8_296, List.forall_mem_cons.2 ⟨sub8_297, List.forall_mem_cons.2 ⟨sub8_298, List.forall_mem_cons.2 ⟨sub8_299, List.forall_mem_cons.2 ⟨sub8_300, List.forall_mem_cons.2 ⟨sub8_301, List.forall_mem_cons.2 ⟨sub8_302, List.forall_mem_cons.2 ⟨sub8_303, List.forall_mem_cons.2 ⟨sub8_304, List.forall_mem_cons.2 ⟨sub8_305, List.forall_mem_cons.2 ⟨sub8_306, List.forall_mem_cons.2 ⟨sub8_307, List.forall_mem_cons.2 ⟨sub8_308, List.forall_mem_cons.2 ⟨sub8_309, List.forall_mem_cons.2 ⟨sub8_310, List.forall_mem_cons.2 ⟨sub8_311, List.forall_mem_cons.2 ⟨sub8_312, List.forall_mem_cons.2 ⟨sub8_313, List.forall_mem_cons.2 ⟨sub8_314, List.forall_mem_cons.2 ⟨sub8_315, List.forall_mem_cons.2 ⟨sub8_316, List.forall_mem_cons.2 ⟨sub8_317, List.forall_mem_cons.2 ⟨sub8_318, List.forall_mem_cons.2 ⟨sub8_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_320 : sub8 [0, 2, 3] = true := by decide +kernel
theorem sub8_321 : sub8 [0, 2, 4] = true := by decide +kernel
theorem sub8_322 : sub8 [0, 2, 5] = true := by decide +kernel
theorem sub8_323 : sub8 [0, 2, 6] = true := by decide +kernel
theorem sub8_324 : sub8 [0, 3, -7] = true := by decide +kernel
theorem sub8_325 : sub8 [0, 3, -6] = true := by decide +kernel
theorem sub8_326 : sub8 [0, 3, -5] = true := by decide +kernel
theorem sub8_327 : sub8 [0, 3, -4] = true := by decide +kernel
theorem sub8_328 : sub8 [0, 3, -3] = true := by decide +kernel
theorem sub8_329 : sub8 [0, 3, -2] = true := by decide +kernel
theorem sub8_330 : sub8 [0, 3, -1] = true := by decide +kernel
theorem sub8_331 : sub8 [0, 3, 0] = true := by decide +kernel
theorem sub8_332 : sub8 [0, 3, 1] = true := by decide +kernel
theorem sub8_333 : sub8 [0, 3, 2] = true := by decide +kernel
theorem sub8_334 : sub8 [0, 3, 3] = true := by decide +kernel
theorem sub8_335 : sub8 [0, 3, 4] = true := by decide +kernel
theorem sub8_336 : sub8 [0, 3, 5] = true := by decide +kernel
theorem sub8_337 : sub8 [0, 3, 6] = true := by decide +kernel
theorem sub8_338 : sub8 [0, 4] = true := by decide +kernel
theorem sub8_339 : sub8 [0, 5] = true := by decide +kernel
theorem sub8_340 : sub8 [0, 6] = true := by decide +kernel
theorem sub8_341 : sub8 [1, -7] = true := by decide +kernel
theorem sub8_342 : sub8 [1, -6] = true := by decide +kernel
theorem sub8_343 : sub8 [1, -5] = true := by decide +kernel
theorem sub8_344 : sub8 [1, -4] = true := by decide +kernel
theorem sub8_345 : sub8 [1, -3, -7] = true := by decide +kernel
theorem sub8_346 : sub8 [1, -3, -6] = true := by decide +kernel
theorem sub8_347 : sub8 [1, -3, -5] = true := by decide +kernel
theorem sub8_348 : sub8 [1, -3, -4] = true := by decide +kernel
theorem sub8_349 : sub8 [1, -3, -3] = true := by decide +kernel
theorem sub8_350 : sub8 [1, -3, -2] = true := by decide +kernel
theorem sub8_351 : sub8 [1, -3, -1] = true := by decide +kernel
theorem sb8_10 : ∀ q ∈ blk8_10, sub8 q = true := by
  unfold blk8_10
  exact List.forall_mem_cons.2 ⟨sub8_320, List.forall_mem_cons.2 ⟨sub8_321, List.forall_mem_cons.2 ⟨sub8_322, List.forall_mem_cons.2 ⟨sub8_323, List.forall_mem_cons.2 ⟨sub8_324, List.forall_mem_cons.2 ⟨sub8_325, List.forall_mem_cons.2 ⟨sub8_326, List.forall_mem_cons.2 ⟨sub8_327, List.forall_mem_cons.2 ⟨sub8_328, List.forall_mem_cons.2 ⟨sub8_329, List.forall_mem_cons.2 ⟨sub8_330, List.forall_mem_cons.2 ⟨sub8_331, List.forall_mem_cons.2 ⟨sub8_332, List.forall_mem_cons.2 ⟨sub8_333, List.forall_mem_cons.2 ⟨sub8_334, List.forall_mem_cons.2 ⟨sub8_335, List.forall_mem_cons.2 ⟨sub8_336, List.forall_mem_cons.2 ⟨sub8_337, List.forall_mem_cons.2 ⟨sub8_338, List.forall_mem_cons.2 ⟨sub8_339, List.forall_mem_cons.2 ⟨sub8_340, List.forall_mem_cons.2 ⟨sub8_341, List.forall_mem_cons.2 ⟨sub8_342, List.forall_mem_cons.2 ⟨sub8_343, List.forall_mem_cons.2 ⟨sub8_344, List.forall_mem_cons.2 ⟨sub8_345, List.forall_mem_cons.2 ⟨sub8_346, List.forall_mem_cons.2 ⟨sub8_347, List.forall_mem_cons.2 ⟨sub8_348, List.forall_mem_cons.2 ⟨sub8_349, List.forall_mem_cons.2 ⟨sub8_350, List.forall_mem_cons.2 ⟨sub8_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_352 : sub8 [1, -3, 0] = true := by decide +kernel
theorem sub8_353 : sub8 [1, -3, 1] = true := by decide +kernel
theorem sub8_354 : sub8 [1, -3, 2] = true := by decide +kernel
theorem sub8_355 : sub8 [1, -3, 3] = true := by decide +kernel
theorem sub8_356 : sub8 [1, -3, 4] = true := by decide +kernel
theorem sub8_357 : sub8 [1, -3, 5] = true := by decide +kernel
theorem sub8_358 : sub8 [1, -3, 6] = true := by decide +kernel
theorem sub8_359 : sub8 [1, -2, -8] = true := by decide +kernel
theorem sub8_360 : sub8 [1, -2, -7] = true := by decide +kernel
theorem sub8_361 : sub8 [1, -2, -6] = true := by decide +kernel
theorem sub8_362 : sub8 [1, -2, -5] = true := by decide +kernel
theorem sub8_363 : sub8 [1, -2, -4] = true := by decide +kernel
theorem sub8_364 : sub8 [1, -2, -3] = true := by decide +kernel
theorem sub8_365 : sub8 [1, -2, -2] = true := by decide +kernel
theorem sub8_366 : sub8 [1, -2, -1] = true := by decide +kernel
theorem sub8_367 : sub8 [1, -2, 0] = true := by decide +kernel
theorem sub8_368 : sub8 [1, -2, 1] = true := by decide +kernel
theorem sub8_369 : sub8 [1, -2, 2] = true := by decide +kernel
theorem sub8_370 : sub8 [1, -2, 3] = true := by decide +kernel
theorem sub8_371 : sub8 [1, -2, 4] = true := by decide +kernel
theorem sub8_372 : sub8 [1, -2, 5] = true := by decide +kernel
theorem sub8_373 : sub8 [1, -2, 6] = true := by decide +kernel
theorem sub8_374 : sub8 [1, -1, -8] = true := by decide +kernel
theorem sub8_375 : sub8 [1, -1, -7] = true := by decide +kernel
theorem sub8_376 : sub8 [1, -1, -6] = true := by decide +kernel
theorem sub8_377 : sub8 [1, -1, -5] = true := by decide +kernel
theorem sub8_378 : sub8 [1, -1, -4] = true := by decide +kernel
theorem sub8_379 : sub8 [1, -1, -3] = true := by decide +kernel
theorem sub8_380 : sub8 [1, -1, -2] = true := by decide +kernel
theorem sub8_381 : sub8 [1, -1, -1] = true := by decide +kernel
theorem sub8_382 : sub8 [1, -1, 0] = true := by decide +kernel
theorem sub8_383 : sub8 [1, -1, 1] = true := by decide +kernel
theorem sb8_11 : ∀ q ∈ blk8_11, sub8 q = true := by
  unfold blk8_11
  exact List.forall_mem_cons.2 ⟨sub8_352, List.forall_mem_cons.2 ⟨sub8_353, List.forall_mem_cons.2 ⟨sub8_354, List.forall_mem_cons.2 ⟨sub8_355, List.forall_mem_cons.2 ⟨sub8_356, List.forall_mem_cons.2 ⟨sub8_357, List.forall_mem_cons.2 ⟨sub8_358, List.forall_mem_cons.2 ⟨sub8_359, List.forall_mem_cons.2 ⟨sub8_360, List.forall_mem_cons.2 ⟨sub8_361, List.forall_mem_cons.2 ⟨sub8_362, List.forall_mem_cons.2 ⟨sub8_363, List.forall_mem_cons.2 ⟨sub8_364, List.forall_mem_cons.2 ⟨sub8_365, List.forall_mem_cons.2 ⟨sub8_366, List.forall_mem_cons.2 ⟨sub8_367, List.forall_mem_cons.2 ⟨sub8_368, List.forall_mem_cons.2 ⟨sub8_369, List.forall_mem_cons.2 ⟨sub8_370, List.forall_mem_cons.2 ⟨sub8_371, List.forall_mem_cons.2 ⟨sub8_372, List.forall_mem_cons.2 ⟨sub8_373, List.forall_mem_cons.2 ⟨sub8_374, List.forall_mem_cons.2 ⟨sub8_375, List.forall_mem_cons.2 ⟨sub8_376, List.forall_mem_cons.2 ⟨sub8_377, List.forall_mem_cons.2 ⟨sub8_378, List.forall_mem_cons.2 ⟨sub8_379, List.forall_mem_cons.2 ⟨sub8_380, List.forall_mem_cons.2 ⟨sub8_381, List.forall_mem_cons.2 ⟨sub8_382, List.forall_mem_cons.2 ⟨sub8_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_384 : sub8 [1, -1, 2] = true := by decide +kernel
theorem sub8_385 : sub8 [1, -1, 3] = true := by decide +kernel
theorem sub8_386 : sub8 [1, -1, 4] = true := by decide +kernel
theorem sub8_387 : sub8 [1, -1, 5] = true := by decide +kernel
theorem sub8_388 : sub8 [1, -1, 6] = true := by decide +kernel
theorem sub8_389 : sub8 [1, 0, -8] = true := by decide +kernel
theorem sub8_390 : sub8 [1, 0, -7] = true := by decide +kernel
theorem sub8_391 : sub8 [1, 0, -6] = true := by decide +kernel
theorem sub8_392 : sub8 [1, 0, -5] = true := by decide +kernel
theorem sub8_393 : sub8 [1, 0, -4] = true := by decide +kernel
theorem sub8_394 : sub8 [1, 0, -3] = true := by decide +kernel
theorem sub8_395 : sub8 [1, 0, -2] = true := by decide +kernel
theorem sub8_396 : sub8 [1, 0, -1] = true := by decide +kernel
theorem sub8_397 : sub8 [1, 0, 0] = true := by decide +kernel
theorem sub8_398 : sub8 [1, 0, 1] = true := by decide +kernel
theorem sub8_399 : sub8 [1, 0, 2] = true := by decide +kernel
theorem sub8_400 : sub8 [1, 0, 3] = true := by decide +kernel
theorem sub8_401 : sub8 [1, 0, 4] = true := by decide +kernel
theorem sub8_402 : sub8 [1, 0, 5] = true := by decide +kernel
theorem sub8_403 : sub8 [1, 0, 6] = true := by decide +kernel
theorem sub8_404 : sub8 [1, 1, -8] = true := by decide +kernel
theorem sub8_405 : sub8 [1, 1, -7] = true := by decide +kernel
theorem sub8_406 : sub8 [1, 1, -6] = true := by decide +kernel
theorem sub8_407 : sub8 [1, 1, -5] = true := by decide +kernel
theorem sub8_408 : sub8 [1, 1, -4] = true := by decide +kernel
theorem sub8_409 : sub8 [1, 1, -3] = true := by decide +kernel
theorem sub8_410 : sub8 [1, 1, -2] = true := by decide +kernel
theorem sub8_411 : sub8 [1, 1, -1] = true := by decide +kernel
theorem sub8_412 : sub8 [1, 1, 0] = true := by decide +kernel
theorem sub8_413 : sub8 [1, 1, 1] = true := by decide +kernel
theorem sub8_414 : sub8 [1, 1, 2] = true := by decide +kernel
theorem sub8_415 : sub8 [1, 1, 3] = true := by decide +kernel
theorem sb8_12 : ∀ q ∈ blk8_12, sub8 q = true := by
  unfold blk8_12
  exact List.forall_mem_cons.2 ⟨sub8_384, List.forall_mem_cons.2 ⟨sub8_385, List.forall_mem_cons.2 ⟨sub8_386, List.forall_mem_cons.2 ⟨sub8_387, List.forall_mem_cons.2 ⟨sub8_388, List.forall_mem_cons.2 ⟨sub8_389, List.forall_mem_cons.2 ⟨sub8_390, List.forall_mem_cons.2 ⟨sub8_391, List.forall_mem_cons.2 ⟨sub8_392, List.forall_mem_cons.2 ⟨sub8_393, List.forall_mem_cons.2 ⟨sub8_394, List.forall_mem_cons.2 ⟨sub8_395, List.forall_mem_cons.2 ⟨sub8_396, List.forall_mem_cons.2 ⟨sub8_397, List.forall_mem_cons.2 ⟨sub8_398, List.forall_mem_cons.2 ⟨sub8_399, List.forall_mem_cons.2 ⟨sub8_400, List.forall_mem_cons.2 ⟨sub8_401, List.forall_mem_cons.2 ⟨sub8_402, List.forall_mem_cons.2 ⟨sub8_403, List.forall_mem_cons.2 ⟨sub8_404, List.forall_mem_cons.2 ⟨sub8_405, List.forall_mem_cons.2 ⟨sub8_406, List.forall_mem_cons.2 ⟨sub8_407, List.forall_mem_cons.2 ⟨sub8_408, List.forall_mem_cons.2 ⟨sub8_409, List.forall_mem_cons.2 ⟨sub8_410, List.forall_mem_cons.2 ⟨sub8_411, List.forall_mem_cons.2 ⟨sub8_412, List.forall_mem_cons.2 ⟨sub8_413, List.forall_mem_cons.2 ⟨sub8_414, List.forall_mem_cons.2 ⟨sub8_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_416 : sub8 [1, 1, 4] = true := by decide +kernel
theorem sub8_417 : sub8 [1, 1, 5] = true := by decide +kernel
theorem sub8_418 : sub8 [1, 1, 6] = true := by decide +kernel
theorem sub8_419 : sub8 [1, 2, -8] = true := by decide +kernel
theorem sub8_420 : sub8 [1, 2, -7] = true := by decide +kernel
theorem sub8_421 : sub8 [1, 2, -6] = true := by decide +kernel
theorem sub8_422 : sub8 [1, 2, -5] = true := by decide +kernel
theorem sub8_423 : sub8 [1, 2, -4] = true := by decide +kernel
theorem sub8_424 : sub8 [1, 2, -3] = true := by decide +kernel
theorem sub8_425 : sub8 [1, 2, -2] = true := by decide +kernel
theorem sub8_426 : sub8 [1, 2, -1] = true := by decide +kernel
theorem sub8_427 : sub8 [1, 2, 0] = true := by decide +kernel
theorem sub8_428 : sub8 [1, 2, 1] = true := by decide +kernel
theorem sub8_429 : sub8 [1, 2, 2] = true := by decide +kernel
theorem sub8_430 : sub8 [1, 2, 3] = true := by decide +kernel
theorem sub8_431 : sub8 [1, 2, 4] = true := by decide +kernel
theorem sub8_432 : sub8 [1, 2, 5] = true := by decide +kernel
theorem sub8_433 : sub8 [1, 2, 6] = true := by decide +kernel
theorem sub8_434 : sub8 [1, 3] = true := by decide +kernel
theorem sub8_435 : sub8 [1, 4] = true := by decide +kernel
theorem sub8_436 : sub8 [1, 5] = true := by decide +kernel
theorem sub8_437 : sub8 [2, -7] = true := by decide +kernel
theorem sub8_438 : sub8 [2, -6] = true := by decide +kernel
theorem sub8_439 : sub8 [2, -5] = true := by decide +kernel
theorem sub8_440 : sub8 [2, -4] = true := by decide +kernel
theorem sub8_441 : sub8 [2, -3, -7] = true := by decide +kernel
theorem sub8_442 : sub8 [2, -3, -6] = true := by decide +kernel
theorem sub8_443 : sub8 [2, -3, -5] = true := by decide +kernel
theorem sub8_444 : sub8 [2, -3, -4] = true := by decide +kernel
theorem sub8_445 : sub8 [2, -3, -3] = true := by decide +kernel
theorem sub8_446 : sub8 [2, -3, -2] = true := by decide +kernel
theorem sub8_447 : sub8 [2, -3, -1] = true := by decide +kernel
theorem sb8_13 : ∀ q ∈ blk8_13, sub8 q = true := by
  unfold blk8_13
  exact List.forall_mem_cons.2 ⟨sub8_416, List.forall_mem_cons.2 ⟨sub8_417, List.forall_mem_cons.2 ⟨sub8_418, List.forall_mem_cons.2 ⟨sub8_419, List.forall_mem_cons.2 ⟨sub8_420, List.forall_mem_cons.2 ⟨sub8_421, List.forall_mem_cons.2 ⟨sub8_422, List.forall_mem_cons.2 ⟨sub8_423, List.forall_mem_cons.2 ⟨sub8_424, List.forall_mem_cons.2 ⟨sub8_425, List.forall_mem_cons.2 ⟨sub8_426, List.forall_mem_cons.2 ⟨sub8_427, List.forall_mem_cons.2 ⟨sub8_428, List.forall_mem_cons.2 ⟨sub8_429, List.forall_mem_cons.2 ⟨sub8_430, List.forall_mem_cons.2 ⟨sub8_431, List.forall_mem_cons.2 ⟨sub8_432, List.forall_mem_cons.2 ⟨sub8_433, List.forall_mem_cons.2 ⟨sub8_434, List.forall_mem_cons.2 ⟨sub8_435, List.forall_mem_cons.2 ⟨sub8_436, List.forall_mem_cons.2 ⟨sub8_437, List.forall_mem_cons.2 ⟨sub8_438, List.forall_mem_cons.2 ⟨sub8_439, List.forall_mem_cons.2 ⟨sub8_440, List.forall_mem_cons.2 ⟨sub8_441, List.forall_mem_cons.2 ⟨sub8_442, List.forall_mem_cons.2 ⟨sub8_443, List.forall_mem_cons.2 ⟨sub8_444, List.forall_mem_cons.2 ⟨sub8_445, List.forall_mem_cons.2 ⟨sub8_446, List.forall_mem_cons.2 ⟨sub8_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_448 : sub8 [2, -3, 0] = true := by decide +kernel
theorem sub8_449 : sub8 [2, -3, 1] = true := by decide +kernel
theorem sub8_450 : sub8 [2, -3, 2] = true := by decide +kernel
theorem sub8_451 : sub8 [2, -3, 3] = true := by decide +kernel
theorem sub8_452 : sub8 [2, -3, 4] = true := by decide +kernel
theorem sub8_453 : sub8 [2, -3, 5] = true := by decide +kernel
theorem sub8_454 : sub8 [2, -2, -8] = true := by decide +kernel
theorem sub8_455 : sub8 [2, -2, -7] = true := by decide +kernel
theorem sub8_456 : sub8 [2, -2, -6] = true := by decide +kernel
theorem sub8_457 : sub8 [2, -2, -5] = true := by decide +kernel
theorem sub8_458 : sub8 [2, -2, -4] = true := by decide +kernel
theorem sub8_459 : sub8 [2, -2, -3] = true := by decide +kernel
theorem sub8_460 : sub8 [2, -2, -2] = true := by decide +kernel
theorem sub8_461 : sub8 [2, -2, -1] = true := by decide +kernel
theorem sub8_462 : sub8 [2, -2, 0] = true := by decide +kernel
theorem sub8_463 : sub8 [2, -2, 1] = true := by decide +kernel
theorem sub8_464 : sub8 [2, -2, 2] = true := by decide +kernel
theorem sub8_465 : sub8 [2, -2, 3] = true := by decide +kernel
theorem sub8_466 : sub8 [2, -2, 4] = true := by decide +kernel
theorem sub8_467 : sub8 [2, -2, 5] = true := by decide +kernel
theorem sub8_468 : sub8 [2, -2, 6] = true := by decide +kernel
theorem sub8_469 : sub8 [2, -1, -8] = true := by decide +kernel
theorem sub8_470 : sub8 [2, -1, -7] = true := by decide +kernel
theorem sub8_471 : sub8 [2, -1, -6] = true := by decide +kernel
theorem sub8_472 : sub8 [2, -1, -5] = true := by decide +kernel
theorem sub8_473 : sub8 [2, -1, -4] = true := by decide +kernel
theorem sub8_474 : sub8 [2, -1, -3] = true := by decide +kernel
theorem sub8_475 : sub8 [2, -1, -2] = true := by decide +kernel
theorem sub8_476 : sub8 [2, -1, -1] = true := by decide +kernel
theorem sub8_477 : sub8 [2, -1, 0] = true := by decide +kernel
theorem sub8_478 : sub8 [2, -1, 1] = true := by decide +kernel
theorem sub8_479 : sub8 [2, -1, 2] = true := by decide +kernel
theorem sb8_14 : ∀ q ∈ blk8_14, sub8 q = true := by
  unfold blk8_14
  exact List.forall_mem_cons.2 ⟨sub8_448, List.forall_mem_cons.2 ⟨sub8_449, List.forall_mem_cons.2 ⟨sub8_450, List.forall_mem_cons.2 ⟨sub8_451, List.forall_mem_cons.2 ⟨sub8_452, List.forall_mem_cons.2 ⟨sub8_453, List.forall_mem_cons.2 ⟨sub8_454, List.forall_mem_cons.2 ⟨sub8_455, List.forall_mem_cons.2 ⟨sub8_456, List.forall_mem_cons.2 ⟨sub8_457, List.forall_mem_cons.2 ⟨sub8_458, List.forall_mem_cons.2 ⟨sub8_459, List.forall_mem_cons.2 ⟨sub8_460, List.forall_mem_cons.2 ⟨sub8_461, List.forall_mem_cons.2 ⟨sub8_462, List.forall_mem_cons.2 ⟨sub8_463, List.forall_mem_cons.2 ⟨sub8_464, List.forall_mem_cons.2 ⟨sub8_465, List.forall_mem_cons.2 ⟨sub8_466, List.forall_mem_cons.2 ⟨sub8_467, List.forall_mem_cons.2 ⟨sub8_468, List.forall_mem_cons.2 ⟨sub8_469, List.forall_mem_cons.2 ⟨sub8_470, List.forall_mem_cons.2 ⟨sub8_471, List.forall_mem_cons.2 ⟨sub8_472, List.forall_mem_cons.2 ⟨sub8_473, List.forall_mem_cons.2 ⟨sub8_474, List.forall_mem_cons.2 ⟨sub8_475, List.forall_mem_cons.2 ⟨sub8_476, List.forall_mem_cons.2 ⟨sub8_477, List.forall_mem_cons.2 ⟨sub8_478, List.forall_mem_cons.2 ⟨sub8_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_480 : sub8 [2, -1, 3] = true := by decide +kernel
theorem sub8_481 : sub8 [2, -1, 4] = true := by decide +kernel
theorem sub8_482 : sub8 [2, -1, 5] = true := by decide +kernel
theorem sub8_483 : sub8 [2, -1, 6] = true := by decide +kernel
theorem sub8_484 : sub8 [2, 0, -8] = true := by decide +kernel
theorem sub8_485 : sub8 [2, 0, -7] = true := by decide +kernel
theorem sub8_486 : sub8 [2, 0, -6] = true := by decide +kernel
theorem sub8_487 : sub8 [2, 0, -5] = true := by decide +kernel
theorem sub8_488 : sub8 [2, 0, -4] = true := by decide +kernel
theorem sub8_489 : sub8 [2, 0, -3] = true := by decide +kernel
theorem sub8_490 : sub8 [2, 0, -2] = true := by decide +kernel
theorem sub8_491 : sub8 [2, 0, -1] = true := by decide +kernel
theorem sub8_492 : sub8 [2, 0, 0] = true := by decide +kernel
theorem sub8_493 : sub8 [2, 0, 1] = true := by decide +kernel
theorem sub8_494 : sub8 [2, 0, 2] = true := by decide +kernel
theorem sub8_495 : sub8 [2, 0, 3] = true := by decide +kernel
theorem sub8_496 : sub8 [2, 0, 4] = true := by decide +kernel
theorem sub8_497 : sub8 [2, 0, 5] = true := by decide +kernel
theorem sub8_498 : sub8 [2, 0, 6] = true := by decide +kernel
theorem sub8_499 : sub8 [2, 1, -8] = true := by decide +kernel
theorem sub8_500 : sub8 [2, 1, -7] = true := by decide +kernel
theorem sub8_501 : sub8 [2, 1, -6] = true := by decide +kernel
theorem sub8_502 : sub8 [2, 1, -5] = true := by decide +kernel
theorem sub8_503 : sub8 [2, 1, -4] = true := by decide +kernel
theorem sub8_504 : sub8 [2, 1, -3] = true := by decide +kernel
theorem sub8_505 : sub8 [2, 1, -2] = true := by decide +kernel
theorem sub8_506 : sub8 [2, 1, -1] = true := by decide +kernel
theorem sub8_507 : sub8 [2, 1, 0] = true := by decide +kernel
theorem sub8_508 : sub8 [2, 1, 1] = true := by decide +kernel
theorem sub8_509 : sub8 [2, 1, 2] = true := by decide +kernel
theorem sub8_510 : sub8 [2, 1, 3] = true := by decide +kernel
theorem sub8_511 : sub8 [2, 1, 4] = true := by decide +kernel
theorem sb8_15 : ∀ q ∈ blk8_15, sub8 q = true := by
  unfold blk8_15
  exact List.forall_mem_cons.2 ⟨sub8_480, List.forall_mem_cons.2 ⟨sub8_481, List.forall_mem_cons.2 ⟨sub8_482, List.forall_mem_cons.2 ⟨sub8_483, List.forall_mem_cons.2 ⟨sub8_484, List.forall_mem_cons.2 ⟨sub8_485, List.forall_mem_cons.2 ⟨sub8_486, List.forall_mem_cons.2 ⟨sub8_487, List.forall_mem_cons.2 ⟨sub8_488, List.forall_mem_cons.2 ⟨sub8_489, List.forall_mem_cons.2 ⟨sub8_490, List.forall_mem_cons.2 ⟨sub8_491, List.forall_mem_cons.2 ⟨sub8_492, List.forall_mem_cons.2 ⟨sub8_493, List.forall_mem_cons.2 ⟨sub8_494, List.forall_mem_cons.2 ⟨sub8_495, List.forall_mem_cons.2 ⟨sub8_496, List.forall_mem_cons.2 ⟨sub8_497, List.forall_mem_cons.2 ⟨sub8_498, List.forall_mem_cons.2 ⟨sub8_499, List.forall_mem_cons.2 ⟨sub8_500, List.forall_mem_cons.2 ⟨sub8_501, List.forall_mem_cons.2 ⟨sub8_502, List.forall_mem_cons.2 ⟨sub8_503, List.forall_mem_cons.2 ⟨sub8_504, List.forall_mem_cons.2 ⟨sub8_505, List.forall_mem_cons.2 ⟨sub8_506, List.forall_mem_cons.2 ⟨sub8_507, List.forall_mem_cons.2 ⟨sub8_508, List.forall_mem_cons.2 ⟨sub8_509, List.forall_mem_cons.2 ⟨sub8_510, List.forall_mem_cons.2 ⟨sub8_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_512 : sub8 [2, 1, 5] = true := by decide +kernel
theorem sub8_513 : sub8 [2, 2] = true := by decide +kernel
theorem sub8_514 : sub8 [2, 3] = true := by decide +kernel
theorem sub8_515 : sub8 [2, 4] = true := by decide +kernel
theorem sub8_516 : sub8 [3, -7] = true := by decide +kernel
theorem sub8_517 : sub8 [3, -6] = true := by decide +kernel
theorem sub8_518 : sub8 [3, -5] = true := by decide +kernel
theorem sub8_519 : sub8 [3, -4] = true := by decide +kernel
theorem sub8_520 : sub8 [3, -3] = true := by decide +kernel
theorem sub8_521 : sub8 [3, -2, -8] = true := by decide +kernel
theorem sub8_522 : sub8 [3, -2, -7] = true := by decide +kernel
theorem sub8_523 : sub8 [3, -2, -6] = true := by decide +kernel
theorem sub8_524 : sub8 [3, -2, -5] = true := by decide +kernel
theorem sub8_525 : sub8 [3, -2, -4] = true := by decide +kernel
theorem sub8_526 : sub8 [3, -2, -3] = true := by decide +kernel
theorem sub8_527 : sub8 [3, -2, -2] = true := by decide +kernel
theorem sub8_528 : sub8 [3, -2, -1] = true := by decide +kernel
theorem sub8_529 : sub8 [3, -2, 0] = true := by decide +kernel
theorem sub8_530 : sub8 [3, -2, 1] = true := by decide +kernel
theorem sub8_531 : sub8 [3, -2, 2] = true := by decide +kernel
theorem sub8_532 : sub8 [3, -2, 3] = true := by decide +kernel
theorem sub8_533 : sub8 [3, -2, 4] = true := by decide +kernel
theorem sub8_534 : sub8 [3, -2, 5] = true := by decide +kernel
theorem sub8_535 : sub8 [3, -1, -8] = true := by decide +kernel
theorem sub8_536 : sub8 [3, -1, -7] = true := by decide +kernel
theorem sub8_537 : sub8 [3, -1, -6] = true := by decide +kernel
theorem sub8_538 : sub8 [3, -1, -5] = true := by decide +kernel
theorem sub8_539 : sub8 [3, -1, -4] = true := by decide +kernel
theorem sub8_540 : sub8 [3, -1, -3] = true := by decide +kernel
theorem sub8_541 : sub8 [3, -1, -2] = true := by decide +kernel
theorem sub8_542 : sub8 [3, -1, -1] = true := by decide +kernel
theorem sub8_543 : sub8 [3, -1, 0] = true := by decide +kernel
theorem sb8_16 : ∀ q ∈ blk8_16, sub8 q = true := by
  unfold blk8_16
  exact List.forall_mem_cons.2 ⟨sub8_512, List.forall_mem_cons.2 ⟨sub8_513, List.forall_mem_cons.2 ⟨sub8_514, List.forall_mem_cons.2 ⟨sub8_515, List.forall_mem_cons.2 ⟨sub8_516, List.forall_mem_cons.2 ⟨sub8_517, List.forall_mem_cons.2 ⟨sub8_518, List.forall_mem_cons.2 ⟨sub8_519, List.forall_mem_cons.2 ⟨sub8_520, List.forall_mem_cons.2 ⟨sub8_521, List.forall_mem_cons.2 ⟨sub8_522, List.forall_mem_cons.2 ⟨sub8_523, List.forall_mem_cons.2 ⟨sub8_524, List.forall_mem_cons.2 ⟨sub8_525, List.forall_mem_cons.2 ⟨sub8_526, List.forall_mem_cons.2 ⟨sub8_527, List.forall_mem_cons.2 ⟨sub8_528, List.forall_mem_cons.2 ⟨sub8_529, List.forall_mem_cons.2 ⟨sub8_530, List.forall_mem_cons.2 ⟨sub8_531, List.forall_mem_cons.2 ⟨sub8_532, List.forall_mem_cons.2 ⟨sub8_533, List.forall_mem_cons.2 ⟨sub8_534, List.forall_mem_cons.2 ⟨sub8_535, List.forall_mem_cons.2 ⟨sub8_536, List.forall_mem_cons.2 ⟨sub8_537, List.forall_mem_cons.2 ⟨sub8_538, List.forall_mem_cons.2 ⟨sub8_539, List.forall_mem_cons.2 ⟨sub8_540, List.forall_mem_cons.2 ⟨sub8_541, List.forall_mem_cons.2 ⟨sub8_542, List.forall_mem_cons.2 ⟨sub8_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C125
