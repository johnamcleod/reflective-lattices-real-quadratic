import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub11_288 : sub11 [0, 1, -2] = true := by decide +kernel
theorem sub11_289 : sub11 [0, 1, -1] = true := by decide +kernel
theorem sub11_290 : sub11 [0, 1, 0] = true := by decide +kernel
theorem sub11_291 : sub11 [0, 1, 1] = true := by decide +kernel
theorem sub11_292 : sub11 [0, 1, 2] = true := by decide +kernel
theorem sub11_293 : sub11 [0, 1, 3] = true := by decide +kernel
theorem sub11_294 : sub11 [0, 1, 4] = true := by decide +kernel
theorem sub11_295 : sub11 [0, 1, 5] = true := by decide +kernel
theorem sub11_296 : sub11 [0, 1, 6] = true := by decide +kernel
theorem sub11_297 : sub11 [0, 2, -7] = true := by decide +kernel
theorem sub11_298 : sub11 [0, 2, -6] = true := by decide +kernel
theorem sub11_299 : sub11 [0, 2, -5] = true := by decide +kernel
theorem sub11_300 : sub11 [0, 2, -4] = true := by decide +kernel
theorem sub11_301 : sub11 [0, 2, -3] = true := by decide +kernel
theorem sub11_302 : sub11 [0, 2, -2] = true := by decide +kernel
theorem sub11_303 : sub11 [0, 2, -1] = true := by decide +kernel
theorem sub11_304 : sub11 [0, 2, 0] = true := by decide +kernel
theorem sub11_305 : sub11 [0, 2, 1] = true := by decide +kernel
theorem sub11_306 : sub11 [0, 2, 2] = true := by decide +kernel
theorem sub11_307 : sub11 [0, 2, 3] = true := by decide +kernel
theorem sub11_308 : sub11 [0, 2, 4] = true := by decide +kernel
theorem sub11_309 : sub11 [0, 2, 5] = true := by decide +kernel
theorem sub11_310 : sub11 [0, 2, 6] = true := by decide +kernel
theorem sub11_311 : sub11 [0, 3, -6] = true := by decide +kernel
theorem sub11_312 : sub11 [0, 3, -5] = true := by decide +kernel
theorem sub11_313 : sub11 [0, 3, -4] = true := by decide +kernel
theorem sub11_314 : sub11 [0, 3, -3] = true := by decide +kernel
theorem sub11_315 : sub11 [0, 3, -2] = true := by decide +kernel
theorem sub11_316 : sub11 [0, 3, -1] = true := by decide +kernel
theorem sub11_317 : sub11 [0, 3, 0] = true := by decide +kernel
theorem sub11_318 : sub11 [0, 3, 1] = true := by decide +kernel
theorem sub11_319 : sub11 [0, 3, 2] = true := by decide +kernel
theorem sb11_9 : ∀ q ∈ blk11_9, sub11 q = true := by
  unfold blk11_9
  exact List.forall_mem_cons.2 ⟨sub11_288, List.forall_mem_cons.2 ⟨sub11_289, List.forall_mem_cons.2 ⟨sub11_290, List.forall_mem_cons.2 ⟨sub11_291, List.forall_mem_cons.2 ⟨sub11_292, List.forall_mem_cons.2 ⟨sub11_293, List.forall_mem_cons.2 ⟨sub11_294, List.forall_mem_cons.2 ⟨sub11_295, List.forall_mem_cons.2 ⟨sub11_296, List.forall_mem_cons.2 ⟨sub11_297, List.forall_mem_cons.2 ⟨sub11_298, List.forall_mem_cons.2 ⟨sub11_299, List.forall_mem_cons.2 ⟨sub11_300, List.forall_mem_cons.2 ⟨sub11_301, List.forall_mem_cons.2 ⟨sub11_302, List.forall_mem_cons.2 ⟨sub11_303, List.forall_mem_cons.2 ⟨sub11_304, List.forall_mem_cons.2 ⟨sub11_305, List.forall_mem_cons.2 ⟨sub11_306, List.forall_mem_cons.2 ⟨sub11_307, List.forall_mem_cons.2 ⟨sub11_308, List.forall_mem_cons.2 ⟨sub11_309, List.forall_mem_cons.2 ⟨sub11_310, List.forall_mem_cons.2 ⟨sub11_311, List.forall_mem_cons.2 ⟨sub11_312, List.forall_mem_cons.2 ⟨sub11_313, List.forall_mem_cons.2 ⟨sub11_314, List.forall_mem_cons.2 ⟨sub11_315, List.forall_mem_cons.2 ⟨sub11_316, List.forall_mem_cons.2 ⟨sub11_317, List.forall_mem_cons.2 ⟨sub11_318, List.forall_mem_cons.2 ⟨sub11_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_320 : sub11 [0, 3, 3] = true := by decide +kernel
theorem sub11_321 : sub11 [0, 3, 4] = true := by decide +kernel
theorem sub11_322 : sub11 [0, 3, 5] = true := by decide +kernel
theorem sub11_323 : sub11 [0, 3, 6] = true := by decide +kernel
theorem sub11_324 : sub11 [0, 4] = true := by decide +kernel
theorem sub11_325 : sub11 [0, 5] = true := by decide +kernel
theorem sub11_326 : sub11 [0, 6] = true := by decide +kernel
theorem sub11_327 : sub11 [0, 7] = true := by decide +kernel
theorem sub11_328 : sub11 [1, -8] = true := by decide +kernel
theorem sub11_329 : sub11 [1, -7] = true := by decide +kernel
theorem sub11_330 : sub11 [1, -6] = true := by decide +kernel
theorem sub11_331 : sub11 [1, -5] = true := by decide +kernel
theorem sub11_332 : sub11 [1, -4] = true := by decide +kernel
theorem sub11_333 : sub11 [1, -3, -7] = true := by decide +kernel
theorem sub11_334 : sub11 [1, -3, -6] = true := by decide +kernel
theorem sub11_335 : sub11 [1, -3, -5] = true := by decide +kernel
theorem sub11_336 : sub11 [1, -3, -4] = true := by decide +kernel
theorem sub11_337 : sub11 [1, -3, -3] = true := by decide +kernel
theorem sub11_338 : sub11 [1, -3, -2] = true := by decide +kernel
theorem sub11_339 : sub11 [1, -3, -1] = true := by decide +kernel
theorem sub11_340 : sub11 [1, -3, 0] = true := by decide +kernel
theorem sub11_341 : sub11 [1, -3, 1] = true := by decide +kernel
theorem sub11_342 : sub11 [1, -3, 2] = true := by decide +kernel
theorem sub11_343 : sub11 [1, -3, 3] = true := by decide +kernel
theorem sub11_344 : sub11 [1, -3, 4] = true := by decide +kernel
theorem sub11_345 : sub11 [1, -3, 5] = true := by decide +kernel
theorem sub11_346 : sub11 [1, -2, -7] = true := by decide +kernel
theorem sub11_347 : sub11 [1, -2, -6] = true := by decide +kernel
theorem sub11_348 : sub11 [1, -2, -5] = true := by decide +kernel
theorem sub11_349 : sub11 [1, -2, -4] = true := by decide +kernel
theorem sub11_350 : sub11 [1, -2, -3] = true := by decide +kernel
theorem sub11_351 : sub11 [1, -2, -2] = true := by decide +kernel
theorem sb11_10 : ∀ q ∈ blk11_10, sub11 q = true := by
  unfold blk11_10
  exact List.forall_mem_cons.2 ⟨sub11_320, List.forall_mem_cons.2 ⟨sub11_321, List.forall_mem_cons.2 ⟨sub11_322, List.forall_mem_cons.2 ⟨sub11_323, List.forall_mem_cons.2 ⟨sub11_324, List.forall_mem_cons.2 ⟨sub11_325, List.forall_mem_cons.2 ⟨sub11_326, List.forall_mem_cons.2 ⟨sub11_327, List.forall_mem_cons.2 ⟨sub11_328, List.forall_mem_cons.2 ⟨sub11_329, List.forall_mem_cons.2 ⟨sub11_330, List.forall_mem_cons.2 ⟨sub11_331, List.forall_mem_cons.2 ⟨sub11_332, List.forall_mem_cons.2 ⟨sub11_333, List.forall_mem_cons.2 ⟨sub11_334, List.forall_mem_cons.2 ⟨sub11_335, List.forall_mem_cons.2 ⟨sub11_336, List.forall_mem_cons.2 ⟨sub11_337, List.forall_mem_cons.2 ⟨sub11_338, List.forall_mem_cons.2 ⟨sub11_339, List.forall_mem_cons.2 ⟨sub11_340, List.forall_mem_cons.2 ⟨sub11_341, List.forall_mem_cons.2 ⟨sub11_342, List.forall_mem_cons.2 ⟨sub11_343, List.forall_mem_cons.2 ⟨sub11_344, List.forall_mem_cons.2 ⟨sub11_345, List.forall_mem_cons.2 ⟨sub11_346, List.forall_mem_cons.2 ⟨sub11_347, List.forall_mem_cons.2 ⟨sub11_348, List.forall_mem_cons.2 ⟨sub11_349, List.forall_mem_cons.2 ⟨sub11_350, List.forall_mem_cons.2 ⟨sub11_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_352 : sub11 [1, -2, -1] = true := by decide +kernel
theorem sub11_353 : sub11 [1, -2, 0] = true := by decide +kernel
theorem sub11_354 : sub11 [1, -2, 1] = true := by decide +kernel
theorem sub11_355 : sub11 [1, -2, 2] = true := by decide +kernel
theorem sub11_356 : sub11 [1, -2, 3] = true := by decide +kernel
theorem sub11_357 : sub11 [1, -2, 4] = true := by decide +kernel
theorem sub11_358 : sub11 [1, -2, 5] = true := by decide +kernel
theorem sub11_359 : sub11 [1, -2, 6] = true := by decide +kernel
theorem sub11_360 : sub11 [1, -1, -7] = true := by decide +kernel
theorem sub11_361 : sub11 [1, -1, -6] = true := by decide +kernel
theorem sub11_362 : sub11 [1, -1, -5] = true := by decide +kernel
theorem sub11_363 : sub11 [1, -1, -4] = true := by decide +kernel
theorem sub11_364 : sub11 [1, -1, -3] = true := by decide +kernel
theorem sub11_365 : sub11 [1, -1, -2] = true := by decide +kernel
theorem sub11_366 : sub11 [1, -1, -1] = true := by decide +kernel
theorem sub11_367 : sub11 [1, -1, 0] = true := by decide +kernel
theorem sub11_368 : sub11 [1, -1, 1] = true := by decide +kernel
theorem sub11_369 : sub11 [1, -1, 2] = true := by decide +kernel
theorem sub11_370 : sub11 [1, -1, 3] = true := by decide +kernel
theorem sub11_371 : sub11 [1, -1, 4] = true := by decide +kernel
theorem sub11_372 : sub11 [1, -1, 5] = true := by decide +kernel
theorem sub11_373 : sub11 [1, -1, 6] = true := by decide +kernel
theorem sub11_374 : sub11 [1, 0, -7] = true := by decide +kernel
theorem sub11_375 : sub11 [1, 0, -6] = true := by decide +kernel
theorem sub11_376 : sub11 [1, 0, -5] = true := by decide +kernel
theorem sub11_377 : sub11 [1, 0, -4] = true := by decide +kernel
theorem sub11_378 : sub11 [1, 0, -3] = true := by decide +kernel
theorem sub11_379 : sub11 [1, 0, -2] = true := by decide +kernel
theorem sub11_380 : sub11 [1, 0, -1] = true := by decide +kernel
theorem sub11_381 : sub11 [1, 0, 0] = true := by decide +kernel
theorem sub11_382 : sub11 [1, 0, 1] = true := by decide +kernel
theorem sub11_383 : sub11 [1, 0, 2] = true := by decide +kernel
theorem sb11_11 : ∀ q ∈ blk11_11, sub11 q = true := by
  unfold blk11_11
  exact List.forall_mem_cons.2 ⟨sub11_352, List.forall_mem_cons.2 ⟨sub11_353, List.forall_mem_cons.2 ⟨sub11_354, List.forall_mem_cons.2 ⟨sub11_355, List.forall_mem_cons.2 ⟨sub11_356, List.forall_mem_cons.2 ⟨sub11_357, List.forall_mem_cons.2 ⟨sub11_358, List.forall_mem_cons.2 ⟨sub11_359, List.forall_mem_cons.2 ⟨sub11_360, List.forall_mem_cons.2 ⟨sub11_361, List.forall_mem_cons.2 ⟨sub11_362, List.forall_mem_cons.2 ⟨sub11_363, List.forall_mem_cons.2 ⟨sub11_364, List.forall_mem_cons.2 ⟨sub11_365, List.forall_mem_cons.2 ⟨sub11_366, List.forall_mem_cons.2 ⟨sub11_367, List.forall_mem_cons.2 ⟨sub11_368, List.forall_mem_cons.2 ⟨sub11_369, List.forall_mem_cons.2 ⟨sub11_370, List.forall_mem_cons.2 ⟨sub11_371, List.forall_mem_cons.2 ⟨sub11_372, List.forall_mem_cons.2 ⟨sub11_373, List.forall_mem_cons.2 ⟨sub11_374, List.forall_mem_cons.2 ⟨sub11_375, List.forall_mem_cons.2 ⟨sub11_376, List.forall_mem_cons.2 ⟨sub11_377, List.forall_mem_cons.2 ⟨sub11_378, List.forall_mem_cons.2 ⟨sub11_379, List.forall_mem_cons.2 ⟨sub11_380, List.forall_mem_cons.2 ⟨sub11_381, List.forall_mem_cons.2 ⟨sub11_382, List.forall_mem_cons.2 ⟨sub11_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_384 : sub11 [1, 0, 3] = true := by decide +kernel
theorem sub11_385 : sub11 [1, 0, 4] = true := by decide +kernel
theorem sub11_386 : sub11 [1, 0, 5] = true := by decide +kernel
theorem sub11_387 : sub11 [1, 0, 6] = true := by decide +kernel
theorem sub11_388 : sub11 [1, 0, 7] = true := by decide +kernel
theorem sub11_389 : sub11 [1, 1, -6] = true := by decide +kernel
theorem sub11_390 : sub11 [1, 1, -5] = true := by decide +kernel
theorem sub11_391 : sub11 [1, 1, -4] = true := by decide +kernel
theorem sub11_392 : sub11 [1, 1, -3] = true := by decide +kernel
theorem sub11_393 : sub11 [1, 1, -2] = true := by decide +kernel
theorem sub11_394 : sub11 [1, 1, -1] = true := by decide +kernel
theorem sub11_395 : sub11 [1, 1, 0] = true := by decide +kernel
theorem sub11_396 : sub11 [1, 1, 1] = true := by decide +kernel
theorem sub11_397 : sub11 [1, 1, 2] = true := by decide +kernel
theorem sub11_398 : sub11 [1, 1, 3] = true := by decide +kernel
theorem sub11_399 : sub11 [1, 1, 4] = true := by decide +kernel
theorem sub11_400 : sub11 [1, 1, 5] = true := by decide +kernel
theorem sub11_401 : sub11 [1, 1, 6] = true := by decide +kernel
theorem sub11_402 : sub11 [1, 1, 7] = true := by decide +kernel
theorem sub11_403 : sub11 [1, 2, -6] = true := by decide +kernel
theorem sub11_404 : sub11 [1, 2, -5] = true := by decide +kernel
theorem sub11_405 : sub11 [1, 2, -4] = true := by decide +kernel
theorem sub11_406 : sub11 [1, 2, -3] = true := by decide +kernel
theorem sub11_407 : sub11 [1, 2, -2] = true := by decide +kernel
theorem sub11_408 : sub11 [1, 2, -1] = true := by decide +kernel
theorem sub11_409 : sub11 [1, 2, 0] = true := by decide +kernel
theorem sub11_410 : sub11 [1, 2, 1] = true := by decide +kernel
theorem sub11_411 : sub11 [1, 2, 2] = true := by decide +kernel
theorem sub11_412 : sub11 [1, 2, 3] = true := by decide +kernel
theorem sub11_413 : sub11 [1, 2, 4] = true := by decide +kernel
theorem sub11_414 : sub11 [1, 2, 5] = true := by decide +kernel
theorem sub11_415 : sub11 [1, 2, 6] = true := by decide +kernel
theorem sb11_12 : ∀ q ∈ blk11_12, sub11 q = true := by
  unfold blk11_12
  exact List.forall_mem_cons.2 ⟨sub11_384, List.forall_mem_cons.2 ⟨sub11_385, List.forall_mem_cons.2 ⟨sub11_386, List.forall_mem_cons.2 ⟨sub11_387, List.forall_mem_cons.2 ⟨sub11_388, List.forall_mem_cons.2 ⟨sub11_389, List.forall_mem_cons.2 ⟨sub11_390, List.forall_mem_cons.2 ⟨sub11_391, List.forall_mem_cons.2 ⟨sub11_392, List.forall_mem_cons.2 ⟨sub11_393, List.forall_mem_cons.2 ⟨sub11_394, List.forall_mem_cons.2 ⟨sub11_395, List.forall_mem_cons.2 ⟨sub11_396, List.forall_mem_cons.2 ⟨sub11_397, List.forall_mem_cons.2 ⟨sub11_398, List.forall_mem_cons.2 ⟨sub11_399, List.forall_mem_cons.2 ⟨sub11_400, List.forall_mem_cons.2 ⟨sub11_401, List.forall_mem_cons.2 ⟨sub11_402, List.forall_mem_cons.2 ⟨sub11_403, List.forall_mem_cons.2 ⟨sub11_404, List.forall_mem_cons.2 ⟨sub11_405, List.forall_mem_cons.2 ⟨sub11_406, List.forall_mem_cons.2 ⟨sub11_407, List.forall_mem_cons.2 ⟨sub11_408, List.forall_mem_cons.2 ⟨sub11_409, List.forall_mem_cons.2 ⟨sub11_410, List.forall_mem_cons.2 ⟨sub11_411, List.forall_mem_cons.2 ⟨sub11_412, List.forall_mem_cons.2 ⟨sub11_413, List.forall_mem_cons.2 ⟨sub11_414, List.forall_mem_cons.2 ⟨sub11_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_416 : sub11 [1, 2, 7] = true := by decide +kernel
theorem sub11_417 : sub11 [1, 3, -6] = true := by decide +kernel
theorem sub11_418 : sub11 [1, 3, -5] = true := by decide +kernel
theorem sub11_419 : sub11 [1, 3, -4] = true := by decide +kernel
theorem sub11_420 : sub11 [1, 3, -3] = true := by decide +kernel
theorem sub11_421 : sub11 [1, 3, -2] = true := by decide +kernel
theorem sub11_422 : sub11 [1, 3, -1] = true := by decide +kernel
theorem sub11_423 : sub11 [1, 3, 0] = true := by decide +kernel
theorem sub11_424 : sub11 [1, 3, 1] = true := by decide +kernel
theorem sub11_425 : sub11 [1, 3, 2] = true := by decide +kernel
theorem sub11_426 : sub11 [1, 3, 3] = true := by decide +kernel
theorem sub11_427 : sub11 [1, 3, 4] = true := by decide +kernel
theorem sub11_428 : sub11 [1, 3, 5] = true := by decide +kernel
theorem sub11_429 : sub11 [1, 3, 6] = true := by decide +kernel
theorem sub11_430 : sub11 [1, 3, 7] = true := by decide +kernel
theorem sub11_431 : sub11 [1, 4] = true := by decide +kernel
theorem sub11_432 : sub11 [1, 5] = true := by decide +kernel
theorem sub11_433 : sub11 [1, 6] = true := by decide +kernel
theorem sub11_434 : sub11 [1, 7] = true := by decide +kernel
theorem sub11_435 : sub11 [2, -7] = true := by decide +kernel
theorem sub11_436 : sub11 [2, -6] = true := by decide +kernel
theorem sub11_437 : sub11 [2, -5] = true := by decide +kernel
theorem sub11_438 : sub11 [2, -4] = true := by decide +kernel
theorem sub11_439 : sub11 [2, -3] = true := by decide +kernel
theorem sub11_440 : sub11 [2, -2, -6] = true := by decide +kernel
theorem sub11_441 : sub11 [2, -2, -5] = true := by decide +kernel
theorem sub11_442 : sub11 [2, -2, -4] = true := by decide +kernel
theorem sub11_443 : sub11 [2, -2, -3] = true := by decide +kernel
theorem sub11_444 : sub11 [2, -2, -2] = true := by decide +kernel
theorem sub11_445 : sub11 [2, -2, -1] = true := by decide +kernel
theorem sub11_446 : sub11 [2, -2, 0] = true := by decide +kernel
theorem sub11_447 : sub11 [2, -2, 1] = true := by decide +kernel
theorem sb11_13 : ∀ q ∈ blk11_13, sub11 q = true := by
  unfold blk11_13
  exact List.forall_mem_cons.2 ⟨sub11_416, List.forall_mem_cons.2 ⟨sub11_417, List.forall_mem_cons.2 ⟨sub11_418, List.forall_mem_cons.2 ⟨sub11_419, List.forall_mem_cons.2 ⟨sub11_420, List.forall_mem_cons.2 ⟨sub11_421, List.forall_mem_cons.2 ⟨sub11_422, List.forall_mem_cons.2 ⟨sub11_423, List.forall_mem_cons.2 ⟨sub11_424, List.forall_mem_cons.2 ⟨sub11_425, List.forall_mem_cons.2 ⟨sub11_426, List.forall_mem_cons.2 ⟨sub11_427, List.forall_mem_cons.2 ⟨sub11_428, List.forall_mem_cons.2 ⟨sub11_429, List.forall_mem_cons.2 ⟨sub11_430, List.forall_mem_cons.2 ⟨sub11_431, List.forall_mem_cons.2 ⟨sub11_432, List.forall_mem_cons.2 ⟨sub11_433, List.forall_mem_cons.2 ⟨sub11_434, List.forall_mem_cons.2 ⟨sub11_435, List.forall_mem_cons.2 ⟨sub11_436, List.forall_mem_cons.2 ⟨sub11_437, List.forall_mem_cons.2 ⟨sub11_438, List.forall_mem_cons.2 ⟨sub11_439, List.forall_mem_cons.2 ⟨sub11_440, List.forall_mem_cons.2 ⟨sub11_441, List.forall_mem_cons.2 ⟨sub11_442, List.forall_mem_cons.2 ⟨sub11_443, List.forall_mem_cons.2 ⟨sub11_444, List.forall_mem_cons.2 ⟨sub11_445, List.forall_mem_cons.2 ⟨sub11_446, List.forall_mem_cons.2 ⟨sub11_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_448 : sub11 [2, -2, 2] = true := by decide +kernel
theorem sub11_449 : sub11 [2, -2, 3] = true := by decide +kernel
theorem sub11_450 : sub11 [2, -2, 4] = true := by decide +kernel
theorem sub11_451 : sub11 [2, -2, 5] = true := by decide +kernel
theorem sub11_452 : sub11 [2, -2, 6] = true := by decide +kernel
theorem sub11_453 : sub11 [2, -1, -6] = true := by decide +kernel
theorem sub11_454 : sub11 [2, -1, -5] = true := by decide +kernel
theorem sub11_455 : sub11 [2, -1, -4] = true := by decide +kernel
theorem sub11_456 : sub11 [2, -1, -3] = true := by decide +kernel
theorem sub11_457 : sub11 [2, -1, -2] = true := by decide +kernel
theorem sub11_458 : sub11 [2, -1, -1] = true := by decide +kernel
theorem sub11_459 : sub11 [2, -1, 0] = true := by decide +kernel
theorem sub11_460 : sub11 [2, -1, 1] = true := by decide +kernel
theorem sub11_461 : sub11 [2, -1, 2] = true := by decide +kernel
theorem sub11_462 : sub11 [2, -1, 3] = true := by decide +kernel
theorem sub11_463 : sub11 [2, -1, 4] = true := by decide +kernel
theorem sub11_464 : sub11 [2, -1, 5] = true := by decide +kernel
theorem sub11_465 : sub11 [2, -1, 6] = true := by decide +kernel
theorem sub11_466 : sub11 [2, -1, 7] = true := by decide +kernel
theorem sub11_467 : sub11 [2, 0, -6] = true := by decide +kernel
theorem sub11_468 : sub11 [2, 0, -5] = true := by decide +kernel
theorem sub11_469 : sub11 [2, 0, -4] = true := by decide +kernel
theorem sub11_470 : sub11 [2, 0, -3] = true := by decide +kernel
theorem sub11_471 : sub11 [2, 0, -2] = true := by decide +kernel
theorem sub11_472 : sub11 [2, 0, -1] = true := by decide +kernel
theorem sub11_473 : sub11 [2, 0, 0] = true := by decide +kernel
theorem sub11_474 : sub11 [2, 0, 1] = true := by decide +kernel
theorem sub11_475 : sub11 [2, 0, 2] = true := by decide +kernel
theorem sub11_476 : sub11 [2, 0, 3] = true := by decide +kernel
theorem sub11_477 : sub11 [2, 0, 4] = true := by decide +kernel
theorem sub11_478 : sub11 [2, 0, 5] = true := by decide +kernel
theorem sub11_479 : sub11 [2, 0, 6] = true := by decide +kernel
theorem sb11_14 : ∀ q ∈ blk11_14, sub11 q = true := by
  unfold blk11_14
  exact List.forall_mem_cons.2 ⟨sub11_448, List.forall_mem_cons.2 ⟨sub11_449, List.forall_mem_cons.2 ⟨sub11_450, List.forall_mem_cons.2 ⟨sub11_451, List.forall_mem_cons.2 ⟨sub11_452, List.forall_mem_cons.2 ⟨sub11_453, List.forall_mem_cons.2 ⟨sub11_454, List.forall_mem_cons.2 ⟨sub11_455, List.forall_mem_cons.2 ⟨sub11_456, List.forall_mem_cons.2 ⟨sub11_457, List.forall_mem_cons.2 ⟨sub11_458, List.forall_mem_cons.2 ⟨sub11_459, List.forall_mem_cons.2 ⟨sub11_460, List.forall_mem_cons.2 ⟨sub11_461, List.forall_mem_cons.2 ⟨sub11_462, List.forall_mem_cons.2 ⟨sub11_463, List.forall_mem_cons.2 ⟨sub11_464, List.forall_mem_cons.2 ⟨sub11_465, List.forall_mem_cons.2 ⟨sub11_466, List.forall_mem_cons.2 ⟨sub11_467, List.forall_mem_cons.2 ⟨sub11_468, List.forall_mem_cons.2 ⟨sub11_469, List.forall_mem_cons.2 ⟨sub11_470, List.forall_mem_cons.2 ⟨sub11_471, List.forall_mem_cons.2 ⟨sub11_472, List.forall_mem_cons.2 ⟨sub11_473, List.forall_mem_cons.2 ⟨sub11_474, List.forall_mem_cons.2 ⟨sub11_475, List.forall_mem_cons.2 ⟨sub11_476, List.forall_mem_cons.2 ⟨sub11_477, List.forall_mem_cons.2 ⟨sub11_478, List.forall_mem_cons.2 ⟨sub11_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_480 : sub11 [2, 0, 7] = true := by decide +kernel
theorem sub11_481 : sub11 [2, 1, -6] = true := by decide +kernel
theorem sub11_482 : sub11 [2, 1, -5] = true := by decide +kernel
theorem sub11_483 : sub11 [2, 1, -4] = true := by decide +kernel
theorem sub11_484 : sub11 [2, 1, -3] = true := by decide +kernel
theorem sub11_485 : sub11 [2, 1, -2] = true := by decide +kernel
theorem sub11_486 : sub11 [2, 1, -1] = true := by decide +kernel
theorem sub11_487 : sub11 [2, 1, 0] = true := by decide +kernel
theorem sub11_488 : sub11 [2, 1, 1] = true := by decide +kernel
theorem sub11_489 : sub11 [2, 1, 2] = true := by decide +kernel
theorem sub11_490 : sub11 [2, 1, 3] = true := by decide +kernel
theorem sub11_491 : sub11 [2, 1, 4] = true := by decide +kernel
theorem sub11_492 : sub11 [2, 1, 5] = true := by decide +kernel
theorem sub11_493 : sub11 [2, 1, 6] = true := by decide +kernel
theorem sub11_494 : sub11 [2, 1, 7] = true := by decide +kernel
theorem sub11_495 : sub11 [2, 2, -5] = true := by decide +kernel
theorem sub11_496 : sub11 [2, 2, -4] = true := by decide +kernel
theorem sub11_497 : sub11 [2, 2, -3] = true := by decide +kernel
theorem sub11_498 : sub11 [2, 2, -2] = true := by decide +kernel
theorem sub11_499 : sub11 [2, 2, -1] = true := by decide +kernel
theorem sub11_500 : sub11 [2, 2, 0] = true := by decide +kernel
theorem sub11_501 : sub11 [2, 2, 1] = true := by decide +kernel
theorem sub11_502 : sub11 [2, 2, 2] = true := by decide +kernel
theorem sub11_503 : sub11 [2, 2, 3] = true := by decide +kernel
theorem sub11_504 : sub11 [2, 2, 4] = true := by decide +kernel
theorem sub11_505 : sub11 [2, 2, 5] = true := by decide +kernel
theorem sub11_506 : sub11 [2, 2, 6] = true := by decide +kernel
theorem sub11_507 : sub11 [2, 2, 7] = true := by decide +kernel
theorem sub11_508 : sub11 [2, 3] = true := by decide +kernel
theorem sub11_509 : sub11 [2, 4] = true := by decide +kernel
theorem sub11_510 : sub11 [2, 5] = true := by decide +kernel
theorem sub11_511 : sub11 [2, 6] = true := by decide +kernel
theorem sb11_15 : ∀ q ∈ blk11_15, sub11 q = true := by
  unfold blk11_15
  exact List.forall_mem_cons.2 ⟨sub11_480, List.forall_mem_cons.2 ⟨sub11_481, List.forall_mem_cons.2 ⟨sub11_482, List.forall_mem_cons.2 ⟨sub11_483, List.forall_mem_cons.2 ⟨sub11_484, List.forall_mem_cons.2 ⟨sub11_485, List.forall_mem_cons.2 ⟨sub11_486, List.forall_mem_cons.2 ⟨sub11_487, List.forall_mem_cons.2 ⟨sub11_488, List.forall_mem_cons.2 ⟨sub11_489, List.forall_mem_cons.2 ⟨sub11_490, List.forall_mem_cons.2 ⟨sub11_491, List.forall_mem_cons.2 ⟨sub11_492, List.forall_mem_cons.2 ⟨sub11_493, List.forall_mem_cons.2 ⟨sub11_494, List.forall_mem_cons.2 ⟨sub11_495, List.forall_mem_cons.2 ⟨sub11_496, List.forall_mem_cons.2 ⟨sub11_497, List.forall_mem_cons.2 ⟨sub11_498, List.forall_mem_cons.2 ⟨sub11_499, List.forall_mem_cons.2 ⟨sub11_500, List.forall_mem_cons.2 ⟨sub11_501, List.forall_mem_cons.2 ⟨sub11_502, List.forall_mem_cons.2 ⟨sub11_503, List.forall_mem_cons.2 ⟨sub11_504, List.forall_mem_cons.2 ⟨sub11_505, List.forall_mem_cons.2 ⟨sub11_506, List.forall_mem_cons.2 ⟨sub11_507, List.forall_mem_cons.2 ⟨sub11_508, List.forall_mem_cons.2 ⟨sub11_509, List.forall_mem_cons.2 ⟨sub11_510, List.forall_mem_cons.2 ⟨sub11_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_512 : sub11 [2, 7] = true := by decide +kernel
theorem sub11_513 : sub11 [3, -7] = true := by decide +kernel
theorem sub11_514 : sub11 [3, -6] = true := by decide +kernel
theorem sub11_515 : sub11 [3, -5] = true := by decide +kernel
theorem sub11_516 : sub11 [3, -4] = true := by decide +kernel
theorem sub11_517 : sub11 [3, -3] = true := by decide +kernel
theorem sub11_518 : sub11 [3, -2] = true := by decide +kernel
theorem sub11_519 : sub11 [3, -1] = true := by decide +kernel
theorem sub11_520 : sub11 [3, 0] = true := by decide +kernel
theorem sub11_521 : sub11 [3, 1] = true := by decide +kernel
theorem sub11_522 : sub11 [3, 2] = true := by decide +kernel
theorem sub11_523 : sub11 [3, 3] = true := by decide +kernel
theorem sub11_524 : sub11 [3, 4] = true := by decide +kernel
theorem sub11_525 : sub11 [3, 5] = true := by decide +kernel
theorem sub11_526 : sub11 [3, 6] = true := by decide +kernel
theorem sub11_527 : sub11 [4, -6] = true := by decide +kernel
theorem sub11_528 : sub11 [4, -5] = true := by decide +kernel
theorem sub11_529 : sub11 [4, -4] = true := by decide +kernel
theorem sub11_530 : sub11 [4, -3] = true := by decide +kernel
theorem sub11_531 : sub11 [4, -2] = true := by decide +kernel
theorem sub11_532 : sub11 [4, -1] = true := by decide +kernel
theorem sub11_533 : sub11 [4, 0] = true := by decide +kernel
theorem sub11_534 : sub11 [4, 1] = true := by decide +kernel
theorem sub11_535 : sub11 [4, 2] = true := by decide +kernel
theorem sub11_536 : sub11 [4, 3] = true := by decide +kernel
theorem sub11_537 : sub11 [4, 4] = true := by decide +kernel
theorem sub11_538 : sub11 [4, 5] = true := by decide +kernel
theorem sub11_539 : sub11 [4, 6] = true := by decide +kernel
theorem sub11_540 : sub11 [5, -5] = true := by decide +kernel
theorem sub11_541 : sub11 [5, -4] = true := by decide +kernel
theorem sub11_542 : sub11 [5, -3] = true := by decide +kernel
theorem sub11_543 : sub11 [5, -2] = true := by decide +kernel
theorem sb11_16 : ∀ q ∈ blk11_16, sub11 q = true := by
  unfold blk11_16
  exact List.forall_mem_cons.2 ⟨sub11_512, List.forall_mem_cons.2 ⟨sub11_513, List.forall_mem_cons.2 ⟨sub11_514, List.forall_mem_cons.2 ⟨sub11_515, List.forall_mem_cons.2 ⟨sub11_516, List.forall_mem_cons.2 ⟨sub11_517, List.forall_mem_cons.2 ⟨sub11_518, List.forall_mem_cons.2 ⟨sub11_519, List.forall_mem_cons.2 ⟨sub11_520, List.forall_mem_cons.2 ⟨sub11_521, List.forall_mem_cons.2 ⟨sub11_522, List.forall_mem_cons.2 ⟨sub11_523, List.forall_mem_cons.2 ⟨sub11_524, List.forall_mem_cons.2 ⟨sub11_525, List.forall_mem_cons.2 ⟨sub11_526, List.forall_mem_cons.2 ⟨sub11_527, List.forall_mem_cons.2 ⟨sub11_528, List.forall_mem_cons.2 ⟨sub11_529, List.forall_mem_cons.2 ⟨sub11_530, List.forall_mem_cons.2 ⟨sub11_531, List.forall_mem_cons.2 ⟨sub11_532, List.forall_mem_cons.2 ⟨sub11_533, List.forall_mem_cons.2 ⟨sub11_534, List.forall_mem_cons.2 ⟨sub11_535, List.forall_mem_cons.2 ⟨sub11_536, List.forall_mem_cons.2 ⟨sub11_537, List.forall_mem_cons.2 ⟨sub11_538, List.forall_mem_cons.2 ⟨sub11_539, List.forall_mem_cons.2 ⟨sub11_540, List.forall_mem_cons.2 ⟨sub11_541, List.forall_mem_cons.2 ⟨sub11_542, List.forall_mem_cons.2 ⟨sub11_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_544 : sub11 [5, -1] = true := by decide +kernel
theorem sub11_545 : sub11 [5, 0] = true := by decide +kernel
theorem sub11_546 : sub11 [5, 1] = true := by decide +kernel
theorem sub11_547 : sub11 [5, 2] = true := by decide +kernel
theorem sub11_548 : sub11 [5, 3] = true := by decide +kernel
theorem sub11_549 : sub11 [5, 4] = true := by decide +kernel
theorem sub11_550 : sub11 [6] = true := by decide +kernel
theorem sb11_17 : ∀ q ∈ blk11_17, sub11 q = true := by
  unfold blk11_17
  exact List.forall_mem_cons.2 ⟨sub11_544, List.forall_mem_cons.2 ⟨sub11_545, List.forall_mem_cons.2 ⟨sub11_546, List.forall_mem_cons.2 ⟨sub11_547, List.forall_mem_cons.2 ⟨sub11_548, List.forall_mem_cons.2 ⟨sub11_549, List.forall_mem_cons.2 ⟨sub11_550, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
