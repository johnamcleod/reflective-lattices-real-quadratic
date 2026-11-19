import ReflectZphi.Data.Cert5.C035.Base

namespace ReflectZphi.Data.Cert5.C035
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub2_160 : sub2 [-1, 0, 4] = true := by decide +kernel
theorem sub2_161 : sub2 [-1, 0, 5] = true := by decide +kernel
theorem sub2_162 : sub2 [-1, 0, 6] = true := by decide +kernel
theorem sub2_163 : sub2 [-1, 0, 7] = true := by decide +kernel
theorem sub2_164 : sub2 [-1, 1, -7] = true := by decide +kernel
theorem sub2_165 : sub2 [-1, 1, -6] = true := by decide +kernel
theorem sub2_166 : sub2 [-1, 1, -5] = true := by decide +kernel
theorem sub2_167 : sub2 [-1, 1, -4] = true := by decide +kernel
theorem sub2_168 : sub2 [-1, 1, -3] = true := by decide +kernel
theorem sub2_169 : sub2 [-1, 1, -2] = true := by decide +kernel
theorem sub2_170 : sub2 [-1, 1, -1] = true := by decide +kernel
theorem sub2_171 : sub2 [-1, 1, 0] = true := by decide +kernel
theorem sub2_172 : sub2 [-1, 1, 1] = true := by decide +kernel
theorem sub2_173 : sub2 [-1, 1, 2] = true := by decide +kernel
theorem sub2_174 : sub2 [-1, 1, 3] = true := by decide +kernel
theorem sub2_175 : sub2 [-1, 1, 4] = true := by decide +kernel
theorem sub2_176 : sub2 [-1, 1, 5] = true := by decide +kernel
theorem sub2_177 : sub2 [-1, 1, 6] = true := by decide +kernel
theorem sub2_178 : sub2 [-1, 1, 7] = true := by decide +kernel
theorem sub2_179 : sub2 [-1, 2] = true := by decide +kernel
theorem sub2_180 : sub2 [-1, 3] = true := by decide +kernel
theorem sub2_181 : sub2 [-1, 4] = true := by decide +kernel
theorem sub2_182 : sub2 [-1, 5] = true := by decide +kernel
theorem sub2_183 : sub2 [-1, 6] = true := by decide +kernel
theorem sub2_184 : sub2 [0, -7] = true := by decide +kernel
theorem sub2_185 : sub2 [0, -6] = true := by decide +kernel
theorem sub2_186 : sub2 [0, -5] = true := by decide +kernel
theorem sub2_187 : sub2 [0, -4] = true := by decide +kernel
theorem sub2_188 : sub2 [0, -3] = true := by decide +kernel
theorem sub2_189 : sub2 [0, -2, -8] = true := by decide +kernel
theorem sub2_190 : sub2 [0, -2, -7] = true := by decide +kernel
theorem sub2_191 : sub2 [0, -2, -6] = true := by decide +kernel
theorem sb2_5 : ∀ q ∈ blk2_5, sub2 q = true := by
  unfold blk2_5
  exact List.forall_mem_cons.2 ⟨sub2_160, List.forall_mem_cons.2 ⟨sub2_161, List.forall_mem_cons.2 ⟨sub2_162, List.forall_mem_cons.2 ⟨sub2_163, List.forall_mem_cons.2 ⟨sub2_164, List.forall_mem_cons.2 ⟨sub2_165, List.forall_mem_cons.2 ⟨sub2_166, List.forall_mem_cons.2 ⟨sub2_167, List.forall_mem_cons.2 ⟨sub2_168, List.forall_mem_cons.2 ⟨sub2_169, List.forall_mem_cons.2 ⟨sub2_170, List.forall_mem_cons.2 ⟨sub2_171, List.forall_mem_cons.2 ⟨sub2_172, List.forall_mem_cons.2 ⟨sub2_173, List.forall_mem_cons.2 ⟨sub2_174, List.forall_mem_cons.2 ⟨sub2_175, List.forall_mem_cons.2 ⟨sub2_176, List.forall_mem_cons.2 ⟨sub2_177, List.forall_mem_cons.2 ⟨sub2_178, List.forall_mem_cons.2 ⟨sub2_179, List.forall_mem_cons.2 ⟨sub2_180, List.forall_mem_cons.2 ⟨sub2_181, List.forall_mem_cons.2 ⟨sub2_182, List.forall_mem_cons.2 ⟨sub2_183, List.forall_mem_cons.2 ⟨sub2_184, List.forall_mem_cons.2 ⟨sub2_185, List.forall_mem_cons.2 ⟨sub2_186, List.forall_mem_cons.2 ⟨sub2_187, List.forall_mem_cons.2 ⟨sub2_188, List.forall_mem_cons.2 ⟨sub2_189, List.forall_mem_cons.2 ⟨sub2_190, List.forall_mem_cons.2 ⟨sub2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_192 : sub2 [0, -2, -5] = true := by decide +kernel
theorem sub2_193 : sub2 [0, -2, -4] = true := by decide +kernel
theorem sub2_194 : sub2 [0, -2, -3] = true := by decide +kernel
theorem sub2_195 : sub2 [0, -2, -2] = true := by decide +kernel
theorem sub2_196 : sub2 [0, -2, -1] = true := by decide +kernel
theorem sub2_197 : sub2 [0, -2, 0] = true := by decide +kernel
theorem sub2_198 : sub2 [0, -2, 1] = true := by decide +kernel
theorem sub2_199 : sub2 [0, -2, 2] = true := by decide +kernel
theorem sub2_200 : sub2 [0, -2, 3] = true := by decide +kernel
theorem sub2_201 : sub2 [0, -2, 4] = true := by decide +kernel
theorem sub2_202 : sub2 [0, -2, 5] = true := by decide +kernel
theorem sub2_203 : sub2 [0, -2, 6] = true := by decide +kernel
theorem sub2_204 : sub2 [0, -1, -8] = true := by decide +kernel
theorem sub2_205 : sub2 [0, -1, -7] = true := by decide +kernel
theorem sub2_206 : sub2 [0, -1, -6] = true := by decide +kernel
theorem sub2_207 : sub2 [0, -1, -5] = true := by decide +kernel
theorem sub2_208 : sub2 [0, -1, -4] = true := by decide +kernel
theorem sub2_209 : sub2 [0, -1, -3] = true := by decide +kernel
theorem sub2_210 : sub2 [0, -1, -2] = true := by decide +kernel
theorem sub2_211 : sub2 [0, -1, -1] = true := by decide +kernel
theorem sub2_212 : sub2 [0, -1, 0] = true := by decide +kernel
theorem sub2_213 : sub2 [0, -1, 1] = true := by decide +kernel
theorem sub2_214 : sub2 [0, -1, 2] = true := by decide +kernel
theorem sub2_215 : sub2 [0, -1, 3] = true := by decide +kernel
theorem sub2_216 : sub2 [0, -1, 4] = true := by decide +kernel
theorem sub2_217 : sub2 [0, -1, 5] = true := by decide +kernel
theorem sub2_218 : sub2 [0, -1, 6] = true := by decide +kernel
theorem sub2_219 : sub2 [0, -1, 7] = true := by decide +kernel
theorem sub2_220 : sub2 [0, 0, -8] = true := by decide +kernel
theorem sub2_221 : sub2 [0, 0, -7] = true := by decide +kernel
theorem sub2_222 : sub2 [0, 0, -6] = true := by decide +kernel
theorem sub2_223 : sub2 [0, 0, -5] = true := by decide +kernel
theorem sb2_6 : ∀ q ∈ blk2_6, sub2 q = true := by
  unfold blk2_6
  exact List.forall_mem_cons.2 ⟨sub2_192, List.forall_mem_cons.2 ⟨sub2_193, List.forall_mem_cons.2 ⟨sub2_194, List.forall_mem_cons.2 ⟨sub2_195, List.forall_mem_cons.2 ⟨sub2_196, List.forall_mem_cons.2 ⟨sub2_197, List.forall_mem_cons.2 ⟨sub2_198, List.forall_mem_cons.2 ⟨sub2_199, List.forall_mem_cons.2 ⟨sub2_200, List.forall_mem_cons.2 ⟨sub2_201, List.forall_mem_cons.2 ⟨sub2_202, List.forall_mem_cons.2 ⟨sub2_203, List.forall_mem_cons.2 ⟨sub2_204, List.forall_mem_cons.2 ⟨sub2_205, List.forall_mem_cons.2 ⟨sub2_206, List.forall_mem_cons.2 ⟨sub2_207, List.forall_mem_cons.2 ⟨sub2_208, List.forall_mem_cons.2 ⟨sub2_209, List.forall_mem_cons.2 ⟨sub2_210, List.forall_mem_cons.2 ⟨sub2_211, List.forall_mem_cons.2 ⟨sub2_212, List.forall_mem_cons.2 ⟨sub2_213, List.forall_mem_cons.2 ⟨sub2_214, List.forall_mem_cons.2 ⟨sub2_215, List.forall_mem_cons.2 ⟨sub2_216, List.forall_mem_cons.2 ⟨sub2_217, List.forall_mem_cons.2 ⟨sub2_218, List.forall_mem_cons.2 ⟨sub2_219, List.forall_mem_cons.2 ⟨sub2_220, List.forall_mem_cons.2 ⟨sub2_221, List.forall_mem_cons.2 ⟨sub2_222, List.forall_mem_cons.2 ⟨sub2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_224 : sub2 [0, 0, -4] = true := by decide +kernel
theorem sub2_225 : sub2 [0, 0, -3] = true := by decide +kernel
theorem sub2_226 : sub2 [0, 0, -2] = true := by decide +kernel
theorem sub2_227 : sub2 [0, 0, -1] = true := by decide +kernel
theorem sub2_228 : sub2 [0, 0, 0] = true := by decide +kernel
theorem sub2_229 : sub2 [0, 0, 1] = true := by decide +kernel
theorem sub2_230 : sub2 [0, 0, 2] = true := by decide +kernel
theorem sub2_231 : sub2 [0, 0, 3] = true := by decide +kernel
theorem sub2_232 : sub2 [0, 0, 4] = true := by decide +kernel
theorem sub2_233 : sub2 [0, 0, 5] = true := by decide +kernel
theorem sub2_234 : sub2 [0, 0, 6] = true := by decide +kernel
theorem sub2_235 : sub2 [0, 0, 7] = true := by decide +kernel
theorem sub2_236 : sub2 [0, 1, -8] = true := by decide +kernel
theorem sub2_237 : sub2 [0, 1, -7] = true := by decide +kernel
theorem sub2_238 : sub2 [0, 1, -6] = true := by decide +kernel
theorem sub2_239 : sub2 [0, 1, -5] = true := by decide +kernel
theorem sub2_240 : sub2 [0, 1, -4] = true := by decide +kernel
theorem sub2_241 : sub2 [0, 1, -3] = true := by decide +kernel
theorem sub2_242 : sub2 [0, 1, -2] = true := by decide +kernel
theorem sub2_243 : sub2 [0, 1, -1] = true := by decide +kernel
theorem sub2_244 : sub2 [0, 1, 0] = true := by decide +kernel
theorem sub2_245 : sub2 [0, 1, 1] = true := by decide +kernel
theorem sub2_246 : sub2 [0, 1, 2] = true := by decide +kernel
theorem sub2_247 : sub2 [0, 1, 3] = true := by decide +kernel
theorem sub2_248 : sub2 [0, 1, 4] = true := by decide +kernel
theorem sub2_249 : sub2 [0, 1, 5] = true := by decide +kernel
theorem sub2_250 : sub2 [0, 1, 6] = true := by decide +kernel
theorem sub2_251 : sub2 [0, 1, 7] = true := by decide +kernel
theorem sub2_252 : sub2 [0, 2, -7] = true := by decide +kernel
theorem sub2_253 : sub2 [0, 2, -6] = true := by decide +kernel
theorem sub2_254 : sub2 [0, 2, -5] = true := by decide +kernel
theorem sub2_255 : sub2 [0, 2, -4] = true := by decide +kernel
theorem sb2_7 : ∀ q ∈ blk2_7, sub2 q = true := by
  unfold blk2_7
  exact List.forall_mem_cons.2 ⟨sub2_224, List.forall_mem_cons.2 ⟨sub2_225, List.forall_mem_cons.2 ⟨sub2_226, List.forall_mem_cons.2 ⟨sub2_227, List.forall_mem_cons.2 ⟨sub2_228, List.forall_mem_cons.2 ⟨sub2_229, List.forall_mem_cons.2 ⟨sub2_230, List.forall_mem_cons.2 ⟨sub2_231, List.forall_mem_cons.2 ⟨sub2_232, List.forall_mem_cons.2 ⟨sub2_233, List.forall_mem_cons.2 ⟨sub2_234, List.forall_mem_cons.2 ⟨sub2_235, List.forall_mem_cons.2 ⟨sub2_236, List.forall_mem_cons.2 ⟨sub2_237, List.forall_mem_cons.2 ⟨sub2_238, List.forall_mem_cons.2 ⟨sub2_239, List.forall_mem_cons.2 ⟨sub2_240, List.forall_mem_cons.2 ⟨sub2_241, List.forall_mem_cons.2 ⟨sub2_242, List.forall_mem_cons.2 ⟨sub2_243, List.forall_mem_cons.2 ⟨sub2_244, List.forall_mem_cons.2 ⟨sub2_245, List.forall_mem_cons.2 ⟨sub2_246, List.forall_mem_cons.2 ⟨sub2_247, List.forall_mem_cons.2 ⟨sub2_248, List.forall_mem_cons.2 ⟨sub2_249, List.forall_mem_cons.2 ⟨sub2_250, List.forall_mem_cons.2 ⟨sub2_251, List.forall_mem_cons.2 ⟨sub2_252, List.forall_mem_cons.2 ⟨sub2_253, List.forall_mem_cons.2 ⟨sub2_254, List.forall_mem_cons.2 ⟨sub2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_256 : sub2 [0, 2, -3] = true := by decide +kernel
theorem sub2_257 : sub2 [0, 2, -2] = true := by decide +kernel
theorem sub2_258 : sub2 [0, 2, -1] = true := by decide +kernel
theorem sub2_259 : sub2 [0, 2, 0] = true := by decide +kernel
theorem sub2_260 : sub2 [0, 2, 1] = true := by decide +kernel
theorem sub2_261 : sub2 [0, 2, 2] = true := by decide +kernel
theorem sub2_262 : sub2 [0, 2, 3] = true := by decide +kernel
theorem sub2_263 : sub2 [0, 2, 4] = true := by decide +kernel
theorem sub2_264 : sub2 [0, 2, 5] = true := by decide +kernel
theorem sub2_265 : sub2 [0, 2, 6] = true := by decide +kernel
theorem sub2_266 : sub2 [0, 2, 7] = true := by decide +kernel
theorem sub2_267 : sub2 [0, 3] = true := by decide +kernel
theorem sub2_268 : sub2 [0, 4] = true := by decide +kernel
theorem sub2_269 : sub2 [0, 5] = true := by decide +kernel
theorem sub2_270 : sub2 [0, 6] = true := by decide +kernel
theorem sub2_271 : sub2 [1, -7] = true := by decide +kernel
theorem sub2_272 : sub2 [1, -6] = true := by decide +kernel
theorem sub2_273 : sub2 [1, -5] = true := by decide +kernel
theorem sub2_274 : sub2 [1, -4] = true := by decide +kernel
theorem sub2_275 : sub2 [1, -3] = true := by decide +kernel
theorem sub2_276 : sub2 [1, -2] = true := by decide +kernel
theorem sub2_277 : sub2 [1, -1, -8] = true := by decide +kernel
theorem sub2_278 : sub2 [1, -1, -7] = true := by decide +kernel
theorem sub2_279 : sub2 [1, -1, -6] = true := by decide +kernel
theorem sub2_280 : sub2 [1, -1, -5] = true := by decide +kernel
theorem sub2_281 : sub2 [1, -1, -4] = true := by decide +kernel
theorem sub2_282 : sub2 [1, -1, -3] = true := by decide +kernel
theorem sub2_283 : sub2 [1, -1, -2] = true := by decide +kernel
theorem sub2_284 : sub2 [1, -1, -1] = true := by decide +kernel
theorem sub2_285 : sub2 [1, -1, 0] = true := by decide +kernel
theorem sub2_286 : sub2 [1, -1, 1] = true := by decide +kernel
theorem sub2_287 : sub2 [1, -1, 2] = true := by decide +kernel
theorem sb2_8 : ∀ q ∈ blk2_8, sub2 q = true := by
  unfold blk2_8
  exact List.forall_mem_cons.2 ⟨sub2_256, List.forall_mem_cons.2 ⟨sub2_257, List.forall_mem_cons.2 ⟨sub2_258, List.forall_mem_cons.2 ⟨sub2_259, List.forall_mem_cons.2 ⟨sub2_260, List.forall_mem_cons.2 ⟨sub2_261, List.forall_mem_cons.2 ⟨sub2_262, List.forall_mem_cons.2 ⟨sub2_263, List.forall_mem_cons.2 ⟨sub2_264, List.forall_mem_cons.2 ⟨sub2_265, List.forall_mem_cons.2 ⟨sub2_266, List.forall_mem_cons.2 ⟨sub2_267, List.forall_mem_cons.2 ⟨sub2_268, List.forall_mem_cons.2 ⟨sub2_269, List.forall_mem_cons.2 ⟨sub2_270, List.forall_mem_cons.2 ⟨sub2_271, List.forall_mem_cons.2 ⟨sub2_272, List.forall_mem_cons.2 ⟨sub2_273, List.forall_mem_cons.2 ⟨sub2_274, List.forall_mem_cons.2 ⟨sub2_275, List.forall_mem_cons.2 ⟨sub2_276, List.forall_mem_cons.2 ⟨sub2_277, List.forall_mem_cons.2 ⟨sub2_278, List.forall_mem_cons.2 ⟨sub2_279, List.forall_mem_cons.2 ⟨sub2_280, List.forall_mem_cons.2 ⟨sub2_281, List.forall_mem_cons.2 ⟨sub2_282, List.forall_mem_cons.2 ⟨sub2_283, List.forall_mem_cons.2 ⟨sub2_284, List.forall_mem_cons.2 ⟨sub2_285, List.forall_mem_cons.2 ⟨sub2_286, List.forall_mem_cons.2 ⟨sub2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_288 : sub2 [1, -1, 3] = true := by decide +kernel
theorem sub2_289 : sub2 [1, -1, 4] = true := by decide +kernel
theorem sub2_290 : sub2 [1, -1, 5] = true := by decide +kernel
theorem sub2_291 : sub2 [1, -1, 6] = true := by decide +kernel
theorem sub2_292 : sub2 [1, 0, -8] = true := by decide +kernel
theorem sub2_293 : sub2 [1, 0, -7] = true := by decide +kernel
theorem sub2_294 : sub2 [1, 0, -6] = true := by decide +kernel
theorem sub2_295 : sub2 [1, 0, -5] = true := by decide +kernel
theorem sub2_296 : sub2 [1, 0, -4] = true := by decide +kernel
theorem sub2_297 : sub2 [1, 0, -3] = true := by decide +kernel
theorem sub2_298 : sub2 [1, 0, -2] = true := by decide +kernel
theorem sub2_299 : sub2 [1, 0, -1] = true := by decide +kernel
theorem sub2_300 : sub2 [1, 0, 0] = true := by decide +kernel
theorem sub2_301 : sub2 [1, 0, 1] = true := by decide +kernel
theorem sub2_302 : sub2 [1, 0, 2] = true := by decide +kernel
theorem sub2_303 : sub2 [1, 0, 3] = true := by decide +kernel
theorem sub2_304 : sub2 [1, 0, 4] = true := by decide +kernel
theorem sub2_305 : sub2 [1, 0, 5] = true := by decide +kernel
theorem sub2_306 : sub2 [1, 0, 6] = true := by decide +kernel
theorem sub2_307 : sub2 [1, 0, 7] = true := by decide +kernel
theorem sub2_308 : sub2 [1, 1, -8] = true := by decide +kernel
theorem sub2_309 : sub2 [1, 1, -7] = true := by decide +kernel
theorem sub2_310 : sub2 [1, 1, -6] = true := by decide +kernel
theorem sub2_311 : sub2 [1, 1, -5] = true := by decide +kernel
theorem sub2_312 : sub2 [1, 1, -4] = true := by decide +kernel
theorem sub2_313 : sub2 [1, 1, -3] = true := by decide +kernel
theorem sub2_314 : sub2 [1, 1, -2] = true := by decide +kernel
theorem sub2_315 : sub2 [1, 1, -1] = true := by decide +kernel
theorem sub2_316 : sub2 [1, 1, 0] = true := by decide +kernel
theorem sub2_317 : sub2 [1, 1, 1] = true := by decide +kernel
theorem sub2_318 : sub2 [1, 1, 2] = true := by decide +kernel
theorem sub2_319 : sub2 [1, 1, 3] = true := by decide +kernel
theorem sb2_9 : ∀ q ∈ blk2_9, sub2 q = true := by
  unfold blk2_9
  exact List.forall_mem_cons.2 ⟨sub2_288, List.forall_mem_cons.2 ⟨sub2_289, List.forall_mem_cons.2 ⟨sub2_290, List.forall_mem_cons.2 ⟨sub2_291, List.forall_mem_cons.2 ⟨sub2_292, List.forall_mem_cons.2 ⟨sub2_293, List.forall_mem_cons.2 ⟨sub2_294, List.forall_mem_cons.2 ⟨sub2_295, List.forall_mem_cons.2 ⟨sub2_296, List.forall_mem_cons.2 ⟨sub2_297, List.forall_mem_cons.2 ⟨sub2_298, List.forall_mem_cons.2 ⟨sub2_299, List.forall_mem_cons.2 ⟨sub2_300, List.forall_mem_cons.2 ⟨sub2_301, List.forall_mem_cons.2 ⟨sub2_302, List.forall_mem_cons.2 ⟨sub2_303, List.forall_mem_cons.2 ⟨sub2_304, List.forall_mem_cons.2 ⟨sub2_305, List.forall_mem_cons.2 ⟨sub2_306, List.forall_mem_cons.2 ⟨sub2_307, List.forall_mem_cons.2 ⟨sub2_308, List.forall_mem_cons.2 ⟨sub2_309, List.forall_mem_cons.2 ⟨sub2_310, List.forall_mem_cons.2 ⟨sub2_311, List.forall_mem_cons.2 ⟨sub2_312, List.forall_mem_cons.2 ⟨sub2_313, List.forall_mem_cons.2 ⟨sub2_314, List.forall_mem_cons.2 ⟨sub2_315, List.forall_mem_cons.2 ⟨sub2_316, List.forall_mem_cons.2 ⟨sub2_317, List.forall_mem_cons.2 ⟨sub2_318, List.forall_mem_cons.2 ⟨sub2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_320 : sub2 [1, 1, 4] = true := by decide +kernel
theorem sub2_321 : sub2 [1, 1, 5] = true := by decide +kernel
theorem sub2_322 : sub2 [1, 1, 6] = true := by decide +kernel
theorem sub2_323 : sub2 [1, 1, 7] = true := by decide +kernel
theorem sub2_324 : sub2 [1, 2, -7] = true := by decide +kernel
theorem sub2_325 : sub2 [1, 2, -6] = true := by decide +kernel
theorem sub2_326 : sub2 [1, 2, -5] = true := by decide +kernel
theorem sub2_327 : sub2 [1, 2, -4] = true := by decide +kernel
theorem sub2_328 : sub2 [1, 2, -3] = true := by decide +kernel
theorem sub2_329 : sub2 [1, 2, -2] = true := by decide +kernel
theorem sub2_330 : sub2 [1, 2, -1] = true := by decide +kernel
theorem sub2_331 : sub2 [1, 2, 0] = true := by decide +kernel
theorem sub2_332 : sub2 [1, 2, 1] = true := by decide +kernel
theorem sub2_333 : sub2 [1, 2, 2] = true := by decide +kernel
theorem sub2_334 : sub2 [1, 2, 3] = true := by decide +kernel
theorem sub2_335 : sub2 [1, 2, 4] = true := by decide +kernel
theorem sub2_336 : sub2 [1, 2, 5] = true := by decide +kernel
theorem sub2_337 : sub2 [1, 2, 6] = true := by decide +kernel
theorem sub2_338 : sub2 [1, 2, 7] = true := by decide +kernel
theorem sub2_339 : sub2 [1, 3] = true := by decide +kernel
theorem sub2_340 : sub2 [1, 4] = true := by decide +kernel
theorem sub2_341 : sub2 [1, 5] = true := by decide +kernel
theorem sub2_342 : sub2 [1, 6] = true := by decide +kernel
theorem sub2_343 : sub2 [2, -6] = true := by decide +kernel
theorem sub2_344 : sub2 [2, -5] = true := by decide +kernel
theorem sub2_345 : sub2 [2, -4] = true := by decide +kernel
theorem sub2_346 : sub2 [2, -3] = true := by decide +kernel
theorem sub2_347 : sub2 [2, -2] = true := by decide +kernel
theorem sub2_348 : sub2 [2, -1, -8] = true := by decide +kernel
theorem sub2_349 : sub2 [2, -1, -7] = true := by decide +kernel
theorem sub2_350 : sub2 [2, -1, -6] = true := by decide +kernel
theorem sub2_351 : sub2 [2, -1, -5] = true := by decide +kernel
theorem sb2_10 : ∀ q ∈ blk2_10, sub2 q = true := by
  unfold blk2_10
  exact List.forall_mem_cons.2 ⟨sub2_320, List.forall_mem_cons.2 ⟨sub2_321, List.forall_mem_cons.2 ⟨sub2_322, List.forall_mem_cons.2 ⟨sub2_323, List.forall_mem_cons.2 ⟨sub2_324, List.forall_mem_cons.2 ⟨sub2_325, List.forall_mem_cons.2 ⟨sub2_326, List.forall_mem_cons.2 ⟨sub2_327, List.forall_mem_cons.2 ⟨sub2_328, List.forall_mem_cons.2 ⟨sub2_329, List.forall_mem_cons.2 ⟨sub2_330, List.forall_mem_cons.2 ⟨sub2_331, List.forall_mem_cons.2 ⟨sub2_332, List.forall_mem_cons.2 ⟨sub2_333, List.forall_mem_cons.2 ⟨sub2_334, List.forall_mem_cons.2 ⟨sub2_335, List.forall_mem_cons.2 ⟨sub2_336, List.forall_mem_cons.2 ⟨sub2_337, List.forall_mem_cons.2 ⟨sub2_338, List.forall_mem_cons.2 ⟨sub2_339, List.forall_mem_cons.2 ⟨sub2_340, List.forall_mem_cons.2 ⟨sub2_341, List.forall_mem_cons.2 ⟨sub2_342, List.forall_mem_cons.2 ⟨sub2_343, List.forall_mem_cons.2 ⟨sub2_344, List.forall_mem_cons.2 ⟨sub2_345, List.forall_mem_cons.2 ⟨sub2_346, List.forall_mem_cons.2 ⟨sub2_347, List.forall_mem_cons.2 ⟨sub2_348, List.forall_mem_cons.2 ⟨sub2_349, List.forall_mem_cons.2 ⟨sub2_350, List.forall_mem_cons.2 ⟨sub2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_352 : sub2 [2, -1, -4] = true := by decide +kernel
theorem sub2_353 : sub2 [2, -1, -3] = true := by decide +kernel
theorem sub2_354 : sub2 [2, -1, -2] = true := by decide +kernel
theorem sub2_355 : sub2 [2, -1, -1] = true := by decide +kernel
theorem sub2_356 : sub2 [2, -1, 0] = true := by decide +kernel
theorem sub2_357 : sub2 [2, -1, 1] = true := by decide +kernel
theorem sub2_358 : sub2 [2, -1, 2] = true := by decide +kernel
theorem sub2_359 : sub2 [2, -1, 3] = true := by decide +kernel
theorem sub2_360 : sub2 [2, -1, 4] = true := by decide +kernel
theorem sub2_361 : sub2 [2, -1, 5] = true := by decide +kernel
theorem sub2_362 : sub2 [2, -1, 6] = true := by decide +kernel
theorem sub2_363 : sub2 [2, 0, -8] = true := by decide +kernel
theorem sub2_364 : sub2 [2, 0, -7] = true := by decide +kernel
theorem sub2_365 : sub2 [2, 0, -6] = true := by decide +kernel
theorem sub2_366 : sub2 [2, 0, -5] = true := by decide +kernel
theorem sub2_367 : sub2 [2, 0, -4] = true := by decide +kernel
theorem sub2_368 : sub2 [2, 0, -3] = true := by decide +kernel
theorem sub2_369 : sub2 [2, 0, -2] = true := by decide +kernel
theorem sub2_370 : sub2 [2, 0, -1] = true := by decide +kernel
theorem sub2_371 : sub2 [2, 0, 0] = true := by decide +kernel
theorem sub2_372 : sub2 [2, 0, 1] = true := by decide +kernel
theorem sub2_373 : sub2 [2, 0, 2] = true := by decide +kernel
theorem sub2_374 : sub2 [2, 0, 3] = true := by decide +kernel
theorem sub2_375 : sub2 [2, 0, 4] = true := by decide +kernel
theorem sub2_376 : sub2 [2, 0, 5] = true := by decide +kernel
theorem sub2_377 : sub2 [2, 0, 6] = true := by decide +kernel
theorem sub2_378 : sub2 [2, 1, -8] = true := by decide +kernel
theorem sub2_379 : sub2 [2, 1, -7] = true := by decide +kernel
theorem sub2_380 : sub2 [2, 1, -6] = true := by decide +kernel
theorem sub2_381 : sub2 [2, 1, -5] = true := by decide +kernel
theorem sub2_382 : sub2 [2, 1, -4] = true := by decide +kernel
theorem sub2_383 : sub2 [2, 1, -3] = true := by decide +kernel
theorem sb2_11 : ∀ q ∈ blk2_11, sub2 q = true := by
  unfold blk2_11
  exact List.forall_mem_cons.2 ⟨sub2_352, List.forall_mem_cons.2 ⟨sub2_353, List.forall_mem_cons.2 ⟨sub2_354, List.forall_mem_cons.2 ⟨sub2_355, List.forall_mem_cons.2 ⟨sub2_356, List.forall_mem_cons.2 ⟨sub2_357, List.forall_mem_cons.2 ⟨sub2_358, List.forall_mem_cons.2 ⟨sub2_359, List.forall_mem_cons.2 ⟨sub2_360, List.forall_mem_cons.2 ⟨sub2_361, List.forall_mem_cons.2 ⟨sub2_362, List.forall_mem_cons.2 ⟨sub2_363, List.forall_mem_cons.2 ⟨sub2_364, List.forall_mem_cons.2 ⟨sub2_365, List.forall_mem_cons.2 ⟨sub2_366, List.forall_mem_cons.2 ⟨sub2_367, List.forall_mem_cons.2 ⟨sub2_368, List.forall_mem_cons.2 ⟨sub2_369, List.forall_mem_cons.2 ⟨sub2_370, List.forall_mem_cons.2 ⟨sub2_371, List.forall_mem_cons.2 ⟨sub2_372, List.forall_mem_cons.2 ⟨sub2_373, List.forall_mem_cons.2 ⟨sub2_374, List.forall_mem_cons.2 ⟨sub2_375, List.forall_mem_cons.2 ⟨sub2_376, List.forall_mem_cons.2 ⟨sub2_377, List.forall_mem_cons.2 ⟨sub2_378, List.forall_mem_cons.2 ⟨sub2_379, List.forall_mem_cons.2 ⟨sub2_380, List.forall_mem_cons.2 ⟨sub2_381, List.forall_mem_cons.2 ⟨sub2_382, List.forall_mem_cons.2 ⟨sub2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_384 : sub2 [2, 1, -2] = true := by decide +kernel
theorem sub2_385 : sub2 [2, 1, -1] = true := by decide +kernel
theorem sub2_386 : sub2 [2, 1, 0] = true := by decide +kernel
theorem sub2_387 : sub2 [2, 1, 1] = true := by decide +kernel
theorem sub2_388 : sub2 [2, 1, 2] = true := by decide +kernel
theorem sub2_389 : sub2 [2, 1, 3] = true := by decide +kernel
theorem sub2_390 : sub2 [2, 1, 4] = true := by decide +kernel
theorem sub2_391 : sub2 [2, 1, 5] = true := by decide +kernel
theorem sub2_392 : sub2 [2, 1, 6] = true := by decide +kernel
theorem sub2_393 : sub2 [2, 1, 7] = true := by decide +kernel
theorem sub2_394 : sub2 [2, 2, -7] = true := by decide +kernel
theorem sub2_395 : sub2 [2, 2, -6] = true := by decide +kernel
theorem sub2_396 : sub2 [2, 2, -5] = true := by decide +kernel
theorem sub2_397 : sub2 [2, 2, -4] = true := by decide +kernel
theorem sub2_398 : sub2 [2, 2, -3] = true := by decide +kernel
theorem sub2_399 : sub2 [2, 2, -2] = true := by decide +kernel
theorem sub2_400 : sub2 [2, 2, -1] = true := by decide +kernel
theorem sub2_401 : sub2 [2, 2, 0] = true := by decide +kernel
theorem sub2_402 : sub2 [2, 2, 1] = true := by decide +kernel
theorem sub2_403 : sub2 [2, 2, 2] = true := by decide +kernel
theorem sub2_404 : sub2 [2, 2, 3] = true := by decide +kernel
theorem sub2_405 : sub2 [2, 2, 4] = true := by decide +kernel
theorem sub2_406 : sub2 [2, 2, 5] = true := by decide +kernel
theorem sub2_407 : sub2 [2, 2, 6] = true := by decide +kernel
theorem sub2_408 : sub2 [2, 2, 7] = true := by decide +kernel
theorem sub2_409 : sub2 [2, 3] = true := by decide +kernel
theorem sub2_410 : sub2 [2, 4] = true := by decide +kernel
theorem sub2_411 : sub2 [2, 5] = true := by decide +kernel
theorem sub2_412 : sub2 [2, 6] = true := by decide +kernel
theorem sub2_413 : sub2 [3, -6] = true := by decide +kernel
theorem sub2_414 : sub2 [3, -5] = true := by decide +kernel
theorem sub2_415 : sub2 [3, -4] = true := by decide +kernel
theorem sb2_12 : ∀ q ∈ blk2_12, sub2 q = true := by
  unfold blk2_12
  exact List.forall_mem_cons.2 ⟨sub2_384, List.forall_mem_cons.2 ⟨sub2_385, List.forall_mem_cons.2 ⟨sub2_386, List.forall_mem_cons.2 ⟨sub2_387, List.forall_mem_cons.2 ⟨sub2_388, List.forall_mem_cons.2 ⟨sub2_389, List.forall_mem_cons.2 ⟨sub2_390, List.forall_mem_cons.2 ⟨sub2_391, List.forall_mem_cons.2 ⟨sub2_392, List.forall_mem_cons.2 ⟨sub2_393, List.forall_mem_cons.2 ⟨sub2_394, List.forall_mem_cons.2 ⟨sub2_395, List.forall_mem_cons.2 ⟨sub2_396, List.forall_mem_cons.2 ⟨sub2_397, List.forall_mem_cons.2 ⟨sub2_398, List.forall_mem_cons.2 ⟨sub2_399, List.forall_mem_cons.2 ⟨sub2_400, List.forall_mem_cons.2 ⟨sub2_401, List.forall_mem_cons.2 ⟨sub2_402, List.forall_mem_cons.2 ⟨sub2_403, List.forall_mem_cons.2 ⟨sub2_404, List.forall_mem_cons.2 ⟨sub2_405, List.forall_mem_cons.2 ⟨sub2_406, List.forall_mem_cons.2 ⟨sub2_407, List.forall_mem_cons.2 ⟨sub2_408, List.forall_mem_cons.2 ⟨sub2_409, List.forall_mem_cons.2 ⟨sub2_410, List.forall_mem_cons.2 ⟨sub2_411, List.forall_mem_cons.2 ⟨sub2_412, List.forall_mem_cons.2 ⟨sub2_413, List.forall_mem_cons.2 ⟨sub2_414, List.forall_mem_cons.2 ⟨sub2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C035
