import ReflectZphi.Data.Cert5.C076.Base

namespace ReflectZphi.Data.Cert5.C076
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_288 : sub8 [1, 2, -5] = true := by decide +kernel
theorem sub8_289 : sub8 [1, 2, -4] = true := by decide +kernel
theorem sub8_290 : sub8 [1, 2, -3] = true := by decide +kernel
theorem sub8_291 : sub8 [1, 2, -2] = true := by decide +kernel
theorem sub8_292 : sub8 [1, 2, -1] = true := by decide +kernel
theorem sub8_293 : sub8 [1, 2, 0] = true := by decide +kernel
theorem sub8_294 : sub8 [1, 2, 1] = true := by decide +kernel
theorem sub8_295 : sub8 [1, 2, 2] = true := by decide +kernel
theorem sub8_296 : sub8 [1, 2, 3] = true := by decide +kernel
theorem sub8_297 : sub8 [1, 2, 4] = true := by decide +kernel
theorem sub8_298 : sub8 [1, 2, 5] = true := by decide +kernel
theorem sub8_299 : sub8 [1, 2, 6] = true := by decide +kernel
theorem sub8_300 : sub8 [1, 2, 7] = true := by decide +kernel
theorem sub8_301 : sub8 [1, 2, 8] = true := by decide +kernel
theorem sub8_302 : sub8 [1, 3] = true := by decide +kernel
theorem sub8_303 : sub8 [1, 4] = true := by decide +kernel
theorem sub8_304 : sub8 [2, -4] = true := by decide +kernel
theorem sub8_305 : sub8 [2, -3] = true := by decide +kernel
theorem sub8_306 : sub8 [2, -2] = true := by decide +kernel
theorem sub8_307 : sub8 [2, -1] = true := by decide +kernel
theorem sub8_308 : sub8 [2, 0, -6] = true := by decide +kernel
theorem sub8_309 : sub8 [2, 0, -5] = true := by decide +kernel
theorem sub8_310 : sub8 [2, 0, -4] = true := by decide +kernel
theorem sub8_311 : sub8 [2, 0, -3] = true := by decide +kernel
theorem sub8_312 : sub8 [2, 0, -2] = true := by decide +kernel
theorem sub8_313 : sub8 [2, 0, -1] = true := by decide +kernel
theorem sub8_314 : sub8 [2, 0, 0] = true := by decide +kernel
theorem sub8_315 : sub8 [2, 0, 1] = true := by decide +kernel
theorem sub8_316 : sub8 [2, 0, 2] = true := by decide +kernel
theorem sub8_317 : sub8 [2, 0, 3] = true := by decide +kernel
theorem sub8_318 : sub8 [2, 0, 4] = true := by decide +kernel
theorem sub8_319 : sub8 [2, 0, 5] = true := by decide +kernel
theorem sb8_9 : ∀ q ∈ blk8_9, sub8 q = true := by
  unfold blk8_9
  exact List.forall_mem_cons.2 ⟨sub8_288, List.forall_mem_cons.2 ⟨sub8_289, List.forall_mem_cons.2 ⟨sub8_290, List.forall_mem_cons.2 ⟨sub8_291, List.forall_mem_cons.2 ⟨sub8_292, List.forall_mem_cons.2 ⟨sub8_293, List.forall_mem_cons.2 ⟨sub8_294, List.forall_mem_cons.2 ⟨sub8_295, List.forall_mem_cons.2 ⟨sub8_296, List.forall_mem_cons.2 ⟨sub8_297, List.forall_mem_cons.2 ⟨sub8_298, List.forall_mem_cons.2 ⟨sub8_299, List.forall_mem_cons.2 ⟨sub8_300, List.forall_mem_cons.2 ⟨sub8_301, List.forall_mem_cons.2 ⟨sub8_302, List.forall_mem_cons.2 ⟨sub8_303, List.forall_mem_cons.2 ⟨sub8_304, List.forall_mem_cons.2 ⟨sub8_305, List.forall_mem_cons.2 ⟨sub8_306, List.forall_mem_cons.2 ⟨sub8_307, List.forall_mem_cons.2 ⟨sub8_308, List.forall_mem_cons.2 ⟨sub8_309, List.forall_mem_cons.2 ⟨sub8_310, List.forall_mem_cons.2 ⟨sub8_311, List.forall_mem_cons.2 ⟨sub8_312, List.forall_mem_cons.2 ⟨sub8_313, List.forall_mem_cons.2 ⟨sub8_314, List.forall_mem_cons.2 ⟨sub8_315, List.forall_mem_cons.2 ⟨sub8_316, List.forall_mem_cons.2 ⟨sub8_317, List.forall_mem_cons.2 ⟨sub8_318, List.forall_mem_cons.2 ⟨sub8_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_320 : sub8 [2, 0, 6] = true := by decide +kernel
theorem sub8_321 : sub8 [2, 0, 7] = true := by decide +kernel
theorem sub8_322 : sub8 [2, 1, -6] = true := by decide +kernel
theorem sub8_323 : sub8 [2, 1, -5] = true := by decide +kernel
theorem sub8_324 : sub8 [2, 1, -4] = true := by decide +kernel
theorem sub8_325 : sub8 [2, 1, -3] = true := by decide +kernel
theorem sub8_326 : sub8 [2, 1, -2] = true := by decide +kernel
theorem sub8_327 : sub8 [2, 1, -1] = true := by decide +kernel
theorem sub8_328 : sub8 [2, 1, 0] = true := by decide +kernel
theorem sub8_329 : sub8 [2, 1, 1] = true := by decide +kernel
theorem sub8_330 : sub8 [2, 1, 2] = true := by decide +kernel
theorem sub8_331 : sub8 [2, 1, 3] = true := by decide +kernel
theorem sub8_332 : sub8 [2, 1, 4] = true := by decide +kernel
theorem sub8_333 : sub8 [2, 1, 5] = true := by decide +kernel
theorem sub8_334 : sub8 [2, 1, 6] = true := by decide +kernel
theorem sub8_335 : sub8 [2, 1, 7] = true := by decide +kernel
theorem sub8_336 : sub8 [2, 1, 8] = true := by decide +kernel
theorem sub8_337 : sub8 [2, 2, -5] = true := by decide +kernel
theorem sub8_338 : sub8 [2, 2, -4] = true := by decide +kernel
theorem sub8_339 : sub8 [2, 2, -3] = true := by decide +kernel
theorem sub8_340 : sub8 [2, 2, -2] = true := by decide +kernel
theorem sub8_341 : sub8 [2, 2, -1] = true := by decide +kernel
theorem sub8_342 : sub8 [2, 2, 0] = true := by decide +kernel
theorem sub8_343 : sub8 [2, 2, 1] = true := by decide +kernel
theorem sub8_344 : sub8 [2, 2, 2] = true := by decide +kernel
theorem sub8_345 : sub8 [2, 2, 3] = true := by decide +kernel
theorem sub8_346 : sub8 [2, 2, 4] = true := by decide +kernel
theorem sub8_347 : sub8 [2, 2, 5] = true := by decide +kernel
theorem sub8_348 : sub8 [2, 2, 6] = true := by decide +kernel
theorem sub8_349 : sub8 [2, 2, 7] = true := by decide +kernel
theorem sub8_350 : sub8 [2, 2, 8] = true := by decide +kernel
theorem sub8_351 : sub8 [2, 3] = true := by decide +kernel
theorem sb8_10 : ∀ q ∈ blk8_10, sub8 q = true := by
  unfold blk8_10
  exact List.forall_mem_cons.2 ⟨sub8_320, List.forall_mem_cons.2 ⟨sub8_321, List.forall_mem_cons.2 ⟨sub8_322, List.forall_mem_cons.2 ⟨sub8_323, List.forall_mem_cons.2 ⟨sub8_324, List.forall_mem_cons.2 ⟨sub8_325, List.forall_mem_cons.2 ⟨sub8_326, List.forall_mem_cons.2 ⟨sub8_327, List.forall_mem_cons.2 ⟨sub8_328, List.forall_mem_cons.2 ⟨sub8_329, List.forall_mem_cons.2 ⟨sub8_330, List.forall_mem_cons.2 ⟨sub8_331, List.forall_mem_cons.2 ⟨sub8_332, List.forall_mem_cons.2 ⟨sub8_333, List.forall_mem_cons.2 ⟨sub8_334, List.forall_mem_cons.2 ⟨sub8_335, List.forall_mem_cons.2 ⟨sub8_336, List.forall_mem_cons.2 ⟨sub8_337, List.forall_mem_cons.2 ⟨sub8_338, List.forall_mem_cons.2 ⟨sub8_339, List.forall_mem_cons.2 ⟨sub8_340, List.forall_mem_cons.2 ⟨sub8_341, List.forall_mem_cons.2 ⟨sub8_342, List.forall_mem_cons.2 ⟨sub8_343, List.forall_mem_cons.2 ⟨sub8_344, List.forall_mem_cons.2 ⟨sub8_345, List.forall_mem_cons.2 ⟨sub8_346, List.forall_mem_cons.2 ⟨sub8_347, List.forall_mem_cons.2 ⟨sub8_348, List.forall_mem_cons.2 ⟨sub8_349, List.forall_mem_cons.2 ⟨sub8_350, List.forall_mem_cons.2 ⟨sub8_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_352 : sub8 [2, 4] = true := by decide +kernel
theorem sub8_353 : sub8 [3, -2] = true := by decide +kernel
theorem sub8_354 : sub8 [3, -1] = true := by decide +kernel
theorem sub8_355 : sub8 [3, 0] = true := by decide +kernel
theorem sub8_356 : sub8 [3, 1] = true := by decide +kernel
theorem sub8_357 : sub8 [3, 2] = true := by decide +kernel
theorem sub8_358 : sub8 [3, 3] = true := by decide +kernel
theorem sub8_359 : sub8 [3, 4] = true := by decide +kernel
theorem sub8_360 : sub8 [4] = true := by decide +kernel
theorem sb8_11 : ∀ q ∈ blk8_11, sub8 q = true := by
  unfold blk8_11
  exact List.forall_mem_cons.2 ⟨sub8_352, List.forall_mem_cons.2 ⟨sub8_353, List.forall_mem_cons.2 ⟨sub8_354, List.forall_mem_cons.2 ⟨sub8_355, List.forall_mem_cons.2 ⟨sub8_356, List.forall_mem_cons.2 ⟨sub8_357, List.forall_mem_cons.2 ⟨sub8_358, List.forall_mem_cons.2 ⟨sub8_359, List.forall_mem_cons.2 ⟨sub8_360, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C076
