import ReflectZphi.Data.Cert5.C081.Base

namespace ReflectZphi.Data.Cert5.C081
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub2_288 : sub2 [0, -1, 8] = true := by decide +kernel
theorem sub2_289 : sub2 [0, -1, 9] = true := by decide +kernel
theorem sub2_290 : sub2 [0, -1, 10] = true := by decide +kernel
theorem sub2_291 : sub2 [0, 0, -11] = true := by decide +kernel
theorem sub2_292 : sub2 [0, 0, -10] = true := by decide +kernel
theorem sub2_293 : sub2 [0, 0, -9] = true := by decide +kernel
theorem sub2_294 : sub2 [0, 0, -8] = true := by decide +kernel
theorem sub2_295 : sub2 [0, 0, -7] = true := by decide +kernel
theorem sub2_296 : sub2 [0, 0, -6] = true := by decide +kernel
theorem sub2_297 : sub2 [0, 0, -5] = true := by decide +kernel
theorem sub2_298 : sub2 [0, 0, -4] = true := by decide +kernel
theorem sub2_299 : sub2 [0, 0, -3] = true := by decide +kernel
theorem sub2_300 : sub2 [0, 0, -2] = true := by decide +kernel
theorem sub2_301 : sub2 [0, 0, -1] = true := by decide +kernel
theorem sub2_302 : sub2 [0, 0, 0] = true := by decide +kernel
theorem sub2_303 : sub2 [0, 0, 1] = true := by decide +kernel
theorem sub2_304 : sub2 [0, 0, 2] = true := by decide +kernel
theorem sub2_305 : sub2 [0, 0, 3] = true := by decide +kernel
theorem sub2_306 : sub2 [0, 0, 4] = true := by decide +kernel
theorem sub2_307 : sub2 [0, 0, 5] = true := by decide +kernel
theorem sub2_308 : sub2 [0, 0, 6] = true := by decide +kernel
theorem sub2_309 : sub2 [0, 0, 7] = true := by decide +kernel
theorem sub2_310 : sub2 [0, 0, 8] = true := by decide +kernel
theorem sub2_311 : sub2 [0, 0, 9] = true := by decide +kernel
theorem sub2_312 : sub2 [0, 0, 10] = true := by decide +kernel
theorem sub2_313 : sub2 [0, 1, -11] = true := by decide +kernel
theorem sub2_314 : sub2 [0, 1, -10] = true := by decide +kernel
theorem sub2_315 : sub2 [0, 1, -9] = true := by decide +kernel
theorem sub2_316 : sub2 [0, 1, -8] = true := by decide +kernel
theorem sub2_317 : sub2 [0, 1, -7] = true := by decide +kernel
theorem sub2_318 : sub2 [0, 1, -6] = true := by decide +kernel
theorem sub2_319 : sub2 [0, 1, -5] = true := by decide +kernel
theorem sb2_9 : ∀ q ∈ blk2_9, sub2 q = true := by
  unfold blk2_9
  exact List.forall_mem_cons.2 ⟨sub2_288, List.forall_mem_cons.2 ⟨sub2_289, List.forall_mem_cons.2 ⟨sub2_290, List.forall_mem_cons.2 ⟨sub2_291, List.forall_mem_cons.2 ⟨sub2_292, List.forall_mem_cons.2 ⟨sub2_293, List.forall_mem_cons.2 ⟨sub2_294, List.forall_mem_cons.2 ⟨sub2_295, List.forall_mem_cons.2 ⟨sub2_296, List.forall_mem_cons.2 ⟨sub2_297, List.forall_mem_cons.2 ⟨sub2_298, List.forall_mem_cons.2 ⟨sub2_299, List.forall_mem_cons.2 ⟨sub2_300, List.forall_mem_cons.2 ⟨sub2_301, List.forall_mem_cons.2 ⟨sub2_302, List.forall_mem_cons.2 ⟨sub2_303, List.forall_mem_cons.2 ⟨sub2_304, List.forall_mem_cons.2 ⟨sub2_305, List.forall_mem_cons.2 ⟨sub2_306, List.forall_mem_cons.2 ⟨sub2_307, List.forall_mem_cons.2 ⟨sub2_308, List.forall_mem_cons.2 ⟨sub2_309, List.forall_mem_cons.2 ⟨sub2_310, List.forall_mem_cons.2 ⟨sub2_311, List.forall_mem_cons.2 ⟨sub2_312, List.forall_mem_cons.2 ⟨sub2_313, List.forall_mem_cons.2 ⟨sub2_314, List.forall_mem_cons.2 ⟨sub2_315, List.forall_mem_cons.2 ⟨sub2_316, List.forall_mem_cons.2 ⟨sub2_317, List.forall_mem_cons.2 ⟨sub2_318, List.forall_mem_cons.2 ⟨sub2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_320 : sub2 [0, 1, -4] = true := by decide +kernel
theorem sub2_321 : sub2 [0, 1, -3] = true := by decide +kernel
theorem sub2_322 : sub2 [0, 1, -2] = true := by decide +kernel
theorem sub2_323 : sub2 [0, 1, -1] = true := by decide +kernel
theorem sub2_324 : sub2 [0, 1, 0] = true := by decide +kernel
theorem sub2_325 : sub2 [0, 1, 1] = true := by decide +kernel
theorem sub2_326 : sub2 [0, 1, 2] = true := by decide +kernel
theorem sub2_327 : sub2 [0, 1, 3] = true := by decide +kernel
theorem sub2_328 : sub2 [0, 1, 4] = true := by decide +kernel
theorem sub2_329 : sub2 [0, 1, 5] = true := by decide +kernel
theorem sub2_330 : sub2 [0, 1, 6] = true := by decide +kernel
theorem sub2_331 : sub2 [0, 1, 7] = true := by decide +kernel
theorem sub2_332 : sub2 [0, 1, 8] = true := by decide +kernel
theorem sub2_333 : sub2 [0, 1, 9] = true := by decide +kernel
theorem sub2_334 : sub2 [0, 2, -10] = true := by decide +kernel
theorem sub2_335 : sub2 [0, 2, -9] = true := by decide +kernel
theorem sub2_336 : sub2 [0, 2, -8] = true := by decide +kernel
theorem sub2_337 : sub2 [0, 2, -7] = true := by decide +kernel
theorem sub2_338 : sub2 [0, 2, -6] = true := by decide +kernel
theorem sub2_339 : sub2 [0, 2, -5] = true := by decide +kernel
theorem sub2_340 : sub2 [0, 2, -4] = true := by decide +kernel
theorem sub2_341 : sub2 [0, 2, -3] = true := by decide +kernel
theorem sub2_342 : sub2 [0, 2, -2] = true := by decide +kernel
theorem sub2_343 : sub2 [0, 2, -1] = true := by decide +kernel
theorem sub2_344 : sub2 [0, 2, 0] = true := by decide +kernel
theorem sub2_345 : sub2 [0, 2, 1] = true := by decide +kernel
theorem sub2_346 : sub2 [0, 2, 2] = true := by decide +kernel
theorem sub2_347 : sub2 [0, 2, 3] = true := by decide +kernel
theorem sub2_348 : sub2 [0, 2, 4] = true := by decide +kernel
theorem sub2_349 : sub2 [0, 2, 5] = true := by decide +kernel
theorem sub2_350 : sub2 [0, 2, 6] = true := by decide +kernel
theorem sub2_351 : sub2 [0, 2, 7] = true := by decide +kernel
theorem sb2_10 : ∀ q ∈ blk2_10, sub2 q = true := by
  unfold blk2_10
  exact List.forall_mem_cons.2 ⟨sub2_320, List.forall_mem_cons.2 ⟨sub2_321, List.forall_mem_cons.2 ⟨sub2_322, List.forall_mem_cons.2 ⟨sub2_323, List.forall_mem_cons.2 ⟨sub2_324, List.forall_mem_cons.2 ⟨sub2_325, List.forall_mem_cons.2 ⟨sub2_326, List.forall_mem_cons.2 ⟨sub2_327, List.forall_mem_cons.2 ⟨sub2_328, List.forall_mem_cons.2 ⟨sub2_329, List.forall_mem_cons.2 ⟨sub2_330, List.forall_mem_cons.2 ⟨sub2_331, List.forall_mem_cons.2 ⟨sub2_332, List.forall_mem_cons.2 ⟨sub2_333, List.forall_mem_cons.2 ⟨sub2_334, List.forall_mem_cons.2 ⟨sub2_335, List.forall_mem_cons.2 ⟨sub2_336, List.forall_mem_cons.2 ⟨sub2_337, List.forall_mem_cons.2 ⟨sub2_338, List.forall_mem_cons.2 ⟨sub2_339, List.forall_mem_cons.2 ⟨sub2_340, List.forall_mem_cons.2 ⟨sub2_341, List.forall_mem_cons.2 ⟨sub2_342, List.forall_mem_cons.2 ⟨sub2_343, List.forall_mem_cons.2 ⟨sub2_344, List.forall_mem_cons.2 ⟨sub2_345, List.forall_mem_cons.2 ⟨sub2_346, List.forall_mem_cons.2 ⟨sub2_347, List.forall_mem_cons.2 ⟨sub2_348, List.forall_mem_cons.2 ⟨sub2_349, List.forall_mem_cons.2 ⟨sub2_350, List.forall_mem_cons.2 ⟨sub2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_352 : sub2 [0, 2, 8] = true := by decide +kernel
theorem sub2_353 : sub2 [0, 3, -8] = true := by decide +kernel
theorem sub2_354 : sub2 [0, 3, -7] = true := by decide +kernel
theorem sub2_355 : sub2 [0, 3, -6] = true := by decide +kernel
theorem sub2_356 : sub2 [0, 3, -5] = true := by decide +kernel
theorem sub2_357 : sub2 [0, 3, -4] = true := by decide +kernel
theorem sub2_358 : sub2 [0, 3, -3] = true := by decide +kernel
theorem sub2_359 : sub2 [0, 3, -2] = true := by decide +kernel
theorem sub2_360 : sub2 [0, 3, -1] = true := by decide +kernel
theorem sub2_361 : sub2 [0, 3, 0] = true := by decide +kernel
theorem sub2_362 : sub2 [0, 3, 1] = true := by decide +kernel
theorem sub2_363 : sub2 [0, 3, 2] = true := by decide +kernel
theorem sub2_364 : sub2 [0, 3, 3] = true := by decide +kernel
theorem sub2_365 : sub2 [0, 3, 4] = true := by decide +kernel
theorem sub2_366 : sub2 [0, 3, 5] = true := by decide +kernel
theorem sub2_367 : sub2 [0, 3, 6] = true := by decide +kernel
theorem sub2_368 : sub2 [0, 4] = true := by decide +kernel
theorem sub2_369 : sub2 [1, -4] = true := by decide +kernel
theorem sub2_370 : sub2 [1, -3] = true := by decide +kernel
theorem sub2_371 : sub2 [1, -2, -8] = true := by decide +kernel
theorem sub2_372 : sub2 [1, -2, -7] = true := by decide +kernel
theorem sub2_373 : sub2 [1, -2, -6] = true := by decide +kernel
theorem sub2_374 : sub2 [1, -2, -5] = true := by decide +kernel
theorem sub2_375 : sub2 [1, -2, -4] = true := by decide +kernel
theorem sub2_376 : sub2 [1, -2, -3] = true := by decide +kernel
theorem sub2_377 : sub2 [1, -2, -2] = true := by decide +kernel
theorem sub2_378 : sub2 [1, -2, -1] = true := by decide +kernel
theorem sub2_379 : sub2 [1, -2, 0] = true := by decide +kernel
theorem sub2_380 : sub2 [1, -2, 1] = true := by decide +kernel
theorem sub2_381 : sub2 [1, -2, 2] = true := by decide +kernel
theorem sub2_382 : sub2 [1, -2, 3] = true := by decide +kernel
theorem sub2_383 : sub2 [1, -2, 4] = true := by decide +kernel
theorem sb2_11 : ∀ q ∈ blk2_11, sub2 q = true := by
  unfold blk2_11
  exact List.forall_mem_cons.2 ⟨sub2_352, List.forall_mem_cons.2 ⟨sub2_353, List.forall_mem_cons.2 ⟨sub2_354, List.forall_mem_cons.2 ⟨sub2_355, List.forall_mem_cons.2 ⟨sub2_356, List.forall_mem_cons.2 ⟨sub2_357, List.forall_mem_cons.2 ⟨sub2_358, List.forall_mem_cons.2 ⟨sub2_359, List.forall_mem_cons.2 ⟨sub2_360, List.forall_mem_cons.2 ⟨sub2_361, List.forall_mem_cons.2 ⟨sub2_362, List.forall_mem_cons.2 ⟨sub2_363, List.forall_mem_cons.2 ⟨sub2_364, List.forall_mem_cons.2 ⟨sub2_365, List.forall_mem_cons.2 ⟨sub2_366, List.forall_mem_cons.2 ⟨sub2_367, List.forall_mem_cons.2 ⟨sub2_368, List.forall_mem_cons.2 ⟨sub2_369, List.forall_mem_cons.2 ⟨sub2_370, List.forall_mem_cons.2 ⟨sub2_371, List.forall_mem_cons.2 ⟨sub2_372, List.forall_mem_cons.2 ⟨sub2_373, List.forall_mem_cons.2 ⟨sub2_374, List.forall_mem_cons.2 ⟨sub2_375, List.forall_mem_cons.2 ⟨sub2_376, List.forall_mem_cons.2 ⟨sub2_377, List.forall_mem_cons.2 ⟨sub2_378, List.forall_mem_cons.2 ⟨sub2_379, List.forall_mem_cons.2 ⟨sub2_380, List.forall_mem_cons.2 ⟨sub2_381, List.forall_mem_cons.2 ⟨sub2_382, List.forall_mem_cons.2 ⟨sub2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_384 : sub2 [1, -2, 5] = true := by decide +kernel
theorem sub2_385 : sub2 [1, -2, 6] = true := by decide +kernel
theorem sub2_386 : sub2 [1, -2, 7] = true := by decide +kernel
theorem sub2_387 : sub2 [1, -2, 8] = true := by decide +kernel
theorem sub2_388 : sub2 [1, -2, 9] = true := by decide +kernel
theorem sub2_389 : sub2 [1, -1, -10] = true := by decide +kernel
theorem sub2_390 : sub2 [1, -1, -9] = true := by decide +kernel
theorem sub2_391 : sub2 [1, -1, -8] = true := by decide +kernel
theorem sub2_392 : sub2 [1, -1, -7] = true := by decide +kernel
theorem sub2_393 : sub2 [1, -1, -6] = true := by decide +kernel
theorem sub2_394 : sub2 [1, -1, -5] = true := by decide +kernel
theorem sub2_395 : sub2 [1, -1, -4] = true := by decide +kernel
theorem sub2_396 : sub2 [1, -1, -3] = true := by decide +kernel
theorem sub2_397 : sub2 [1, -1, -2] = true := by decide +kernel
theorem sub2_398 : sub2 [1, -1, -1] = true := by decide +kernel
theorem sub2_399 : sub2 [1, -1, 0] = true := by decide +kernel
theorem sub2_400 : sub2 [1, -1, 1] = true := by decide +kernel
theorem sub2_401 : sub2 [1, -1, 2] = true := by decide +kernel
theorem sub2_402 : sub2 [1, -1, 3] = true := by decide +kernel
theorem sub2_403 : sub2 [1, -1, 4] = true := by decide +kernel
theorem sub2_404 : sub2 [1, -1, 5] = true := by decide +kernel
theorem sub2_405 : sub2 [1, -1, 6] = true := by decide +kernel
theorem sub2_406 : sub2 [1, -1, 7] = true := by decide +kernel
theorem sub2_407 : sub2 [1, -1, 8] = true := by decide +kernel
theorem sub2_408 : sub2 [1, -1, 9] = true := by decide +kernel
theorem sub2_409 : sub2 [1, -1, 10] = true := by decide +kernel
theorem sub2_410 : sub2 [1, 0, -10] = true := by decide +kernel
theorem sub2_411 : sub2 [1, 0, -9] = true := by decide +kernel
theorem sub2_412 : sub2 [1, 0, -8] = true := by decide +kernel
theorem sub2_413 : sub2 [1, 0, -7] = true := by decide +kernel
theorem sub2_414 : sub2 [1, 0, -6] = true := by decide +kernel
theorem sub2_415 : sub2 [1, 0, -5] = true := by decide +kernel
theorem sb2_12 : ∀ q ∈ blk2_12, sub2 q = true := by
  unfold blk2_12
  exact List.forall_mem_cons.2 ⟨sub2_384, List.forall_mem_cons.2 ⟨sub2_385, List.forall_mem_cons.2 ⟨sub2_386, List.forall_mem_cons.2 ⟨sub2_387, List.forall_mem_cons.2 ⟨sub2_388, List.forall_mem_cons.2 ⟨sub2_389, List.forall_mem_cons.2 ⟨sub2_390, List.forall_mem_cons.2 ⟨sub2_391, List.forall_mem_cons.2 ⟨sub2_392, List.forall_mem_cons.2 ⟨sub2_393, List.forall_mem_cons.2 ⟨sub2_394, List.forall_mem_cons.2 ⟨sub2_395, List.forall_mem_cons.2 ⟨sub2_396, List.forall_mem_cons.2 ⟨sub2_397, List.forall_mem_cons.2 ⟨sub2_398, List.forall_mem_cons.2 ⟨sub2_399, List.forall_mem_cons.2 ⟨sub2_400, List.forall_mem_cons.2 ⟨sub2_401, List.forall_mem_cons.2 ⟨sub2_402, List.forall_mem_cons.2 ⟨sub2_403, List.forall_mem_cons.2 ⟨sub2_404, List.forall_mem_cons.2 ⟨sub2_405, List.forall_mem_cons.2 ⟨sub2_406, List.forall_mem_cons.2 ⟨sub2_407, List.forall_mem_cons.2 ⟨sub2_408, List.forall_mem_cons.2 ⟨sub2_409, List.forall_mem_cons.2 ⟨sub2_410, List.forall_mem_cons.2 ⟨sub2_411, List.forall_mem_cons.2 ⟨sub2_412, List.forall_mem_cons.2 ⟨sub2_413, List.forall_mem_cons.2 ⟨sub2_414, List.forall_mem_cons.2 ⟨sub2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_416 : sub2 [1, 0, -4] = true := by decide +kernel
theorem sub2_417 : sub2 [1, 0, -3] = true := by decide +kernel
theorem sub2_418 : sub2 [1, 0, -2] = true := by decide +kernel
theorem sub2_419 : sub2 [1, 0, -1] = true := by decide +kernel
theorem sub2_420 : sub2 [1, 0, 0] = true := by decide +kernel
theorem sub2_421 : sub2 [1, 0, 1] = true := by decide +kernel
theorem sub2_422 : sub2 [1, 0, 2] = true := by decide +kernel
theorem sub2_423 : sub2 [1, 0, 3] = true := by decide +kernel
theorem sub2_424 : sub2 [1, 0, 4] = true := by decide +kernel
theorem sub2_425 : sub2 [1, 0, 5] = true := by decide +kernel
theorem sub2_426 : sub2 [1, 0, 6] = true := by decide +kernel
theorem sub2_427 : sub2 [1, 0, 7] = true := by decide +kernel
theorem sub2_428 : sub2 [1, 0, 8] = true := by decide +kernel
theorem sub2_429 : sub2 [1, 0, 9] = true := by decide +kernel
theorem sub2_430 : sub2 [1, 0, 10] = true := by decide +kernel
theorem sub2_431 : sub2 [1, 1, -10] = true := by decide +kernel
theorem sub2_432 : sub2 [1, 1, -9] = true := by decide +kernel
theorem sub2_433 : sub2 [1, 1, -8] = true := by decide +kernel
theorem sub2_434 : sub2 [1, 1, -7] = true := by decide +kernel
theorem sub2_435 : sub2 [1, 1, -6] = true := by decide +kernel
theorem sub2_436 : sub2 [1, 1, -5] = true := by decide +kernel
theorem sub2_437 : sub2 [1, 1, -4] = true := by decide +kernel
theorem sub2_438 : sub2 [1, 1, -3] = true := by decide +kernel
theorem sub2_439 : sub2 [1, 1, -2] = true := by decide +kernel
theorem sub2_440 : sub2 [1, 1, -1] = true := by decide +kernel
theorem sub2_441 : sub2 [1, 1, 0] = true := by decide +kernel
theorem sub2_442 : sub2 [1, 1, 1] = true := by decide +kernel
theorem sub2_443 : sub2 [1, 1, 2] = true := by decide +kernel
theorem sub2_444 : sub2 [1, 1, 3] = true := by decide +kernel
theorem sub2_445 : sub2 [1, 1, 4] = true := by decide +kernel
theorem sub2_446 : sub2 [1, 1, 5] = true := by decide +kernel
theorem sub2_447 : sub2 [1, 1, 6] = true := by decide +kernel
theorem sb2_13 : ∀ q ∈ blk2_13, sub2 q = true := by
  unfold blk2_13
  exact List.forall_mem_cons.2 ⟨sub2_416, List.forall_mem_cons.2 ⟨sub2_417, List.forall_mem_cons.2 ⟨sub2_418, List.forall_mem_cons.2 ⟨sub2_419, List.forall_mem_cons.2 ⟨sub2_420, List.forall_mem_cons.2 ⟨sub2_421, List.forall_mem_cons.2 ⟨sub2_422, List.forall_mem_cons.2 ⟨sub2_423, List.forall_mem_cons.2 ⟨sub2_424, List.forall_mem_cons.2 ⟨sub2_425, List.forall_mem_cons.2 ⟨sub2_426, List.forall_mem_cons.2 ⟨sub2_427, List.forall_mem_cons.2 ⟨sub2_428, List.forall_mem_cons.2 ⟨sub2_429, List.forall_mem_cons.2 ⟨sub2_430, List.forall_mem_cons.2 ⟨sub2_431, List.forall_mem_cons.2 ⟨sub2_432, List.forall_mem_cons.2 ⟨sub2_433, List.forall_mem_cons.2 ⟨sub2_434, List.forall_mem_cons.2 ⟨sub2_435, List.forall_mem_cons.2 ⟨sub2_436, List.forall_mem_cons.2 ⟨sub2_437, List.forall_mem_cons.2 ⟨sub2_438, List.forall_mem_cons.2 ⟨sub2_439, List.forall_mem_cons.2 ⟨sub2_440, List.forall_mem_cons.2 ⟨sub2_441, List.forall_mem_cons.2 ⟨sub2_442, List.forall_mem_cons.2 ⟨sub2_443, List.forall_mem_cons.2 ⟨sub2_444, List.forall_mem_cons.2 ⟨sub2_445, List.forall_mem_cons.2 ⟨sub2_446, List.forall_mem_cons.2 ⟨sub2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_448 : sub2 [1, 1, 7] = true := by decide +kernel
theorem sub2_449 : sub2 [1, 1, 8] = true := by decide +kernel
theorem sub2_450 : sub2 [1, 1, 9] = true := by decide +kernel
theorem sub2_451 : sub2 [1, 1, 10] = true := by decide +kernel
theorem sub2_452 : sub2 [1, 2, -10] = true := by decide +kernel
theorem sub2_453 : sub2 [1, 2, -9] = true := by decide +kernel
theorem sub2_454 : sub2 [1, 2, -8] = true := by decide +kernel
theorem sub2_455 : sub2 [1, 2, -7] = true := by decide +kernel
theorem sub2_456 : sub2 [1, 2, -6] = true := by decide +kernel
theorem sub2_457 : sub2 [1, 2, -5] = true := by decide +kernel
theorem sub2_458 : sub2 [1, 2, -4] = true := by decide +kernel
theorem sub2_459 : sub2 [1, 2, -3] = true := by decide +kernel
theorem sub2_460 : sub2 [1, 2, -2] = true := by decide +kernel
theorem sub2_461 : sub2 [1, 2, -1] = true := by decide +kernel
theorem sub2_462 : sub2 [1, 2, 0] = true := by decide +kernel
theorem sub2_463 : sub2 [1, 2, 1] = true := by decide +kernel
theorem sub2_464 : sub2 [1, 2, 2] = true := by decide +kernel
theorem sub2_465 : sub2 [1, 2, 3] = true := by decide +kernel
theorem sub2_466 : sub2 [1, 2, 4] = true := by decide +kernel
theorem sub2_467 : sub2 [1, 2, 5] = true := by decide +kernel
theorem sub2_468 : sub2 [1, 2, 6] = true := by decide +kernel
theorem sub2_469 : sub2 [1, 2, 7] = true := by decide +kernel
theorem sub2_470 : sub2 [1, 2, 8] = true := by decide +kernel
theorem sub2_471 : sub2 [1, 3] = true := by decide +kernel
theorem sub2_472 : sub2 [1, 4] = true := by decide +kernel
theorem sub2_473 : sub2 [2, -4] = true := by decide +kernel
theorem sub2_474 : sub2 [2, -3] = true := by decide +kernel
theorem sub2_475 : sub2 [2, -2, -6] = true := by decide +kernel
theorem sub2_476 : sub2 [2, -2, -5] = true := by decide +kernel
theorem sub2_477 : sub2 [2, -2, -4] = true := by decide +kernel
theorem sub2_478 : sub2 [2, -2, -3] = true := by decide +kernel
theorem sub2_479 : sub2 [2, -2, -2] = true := by decide +kernel
theorem sb2_14 : ∀ q ∈ blk2_14, sub2 q = true := by
  unfold blk2_14
  exact List.forall_mem_cons.2 ⟨sub2_448, List.forall_mem_cons.2 ⟨sub2_449, List.forall_mem_cons.2 ⟨sub2_450, List.forall_mem_cons.2 ⟨sub2_451, List.forall_mem_cons.2 ⟨sub2_452, List.forall_mem_cons.2 ⟨sub2_453, List.forall_mem_cons.2 ⟨sub2_454, List.forall_mem_cons.2 ⟨sub2_455, List.forall_mem_cons.2 ⟨sub2_456, List.forall_mem_cons.2 ⟨sub2_457, List.forall_mem_cons.2 ⟨sub2_458, List.forall_mem_cons.2 ⟨sub2_459, List.forall_mem_cons.2 ⟨sub2_460, List.forall_mem_cons.2 ⟨sub2_461, List.forall_mem_cons.2 ⟨sub2_462, List.forall_mem_cons.2 ⟨sub2_463, List.forall_mem_cons.2 ⟨sub2_464, List.forall_mem_cons.2 ⟨sub2_465, List.forall_mem_cons.2 ⟨sub2_466, List.forall_mem_cons.2 ⟨sub2_467, List.forall_mem_cons.2 ⟨sub2_468, List.forall_mem_cons.2 ⟨sub2_469, List.forall_mem_cons.2 ⟨sub2_470, List.forall_mem_cons.2 ⟨sub2_471, List.forall_mem_cons.2 ⟨sub2_472, List.forall_mem_cons.2 ⟨sub2_473, List.forall_mem_cons.2 ⟨sub2_474, List.forall_mem_cons.2 ⟨sub2_475, List.forall_mem_cons.2 ⟨sub2_476, List.forall_mem_cons.2 ⟨sub2_477, List.forall_mem_cons.2 ⟨sub2_478, List.forall_mem_cons.2 ⟨sub2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_480 : sub2 [2, -2, -1] = true := by decide +kernel
theorem sub2_481 : sub2 [2, -2, 0] = true := by decide +kernel
theorem sub2_482 : sub2 [2, -2, 1] = true := by decide +kernel
theorem sub2_483 : sub2 [2, -2, 2] = true := by decide +kernel
theorem sub2_484 : sub2 [2, -2, 3] = true := by decide +kernel
theorem sub2_485 : sub2 [2, -2, 4] = true := by decide +kernel
theorem sub2_486 : sub2 [2, -2, 5] = true := by decide +kernel
theorem sub2_487 : sub2 [2, -2, 6] = true := by decide +kernel
theorem sub2_488 : sub2 [2, -2, 7] = true := by decide +kernel
theorem sub2_489 : sub2 [2, -2, 8] = true := by decide +kernel
theorem sub2_490 : sub2 [2, -1, -8] = true := by decide +kernel
theorem sub2_491 : sub2 [2, -1, -7] = true := by decide +kernel
theorem sub2_492 : sub2 [2, -1, -6] = true := by decide +kernel
theorem sub2_493 : sub2 [2, -1, -5] = true := by decide +kernel
theorem sub2_494 : sub2 [2, -1, -4] = true := by decide +kernel
theorem sub2_495 : sub2 [2, -1, -3] = true := by decide +kernel
theorem sub2_496 : sub2 [2, -1, -2] = true := by decide +kernel
theorem sub2_497 : sub2 [2, -1, -1] = true := by decide +kernel
theorem sub2_498 : sub2 [2, -1, 0] = true := by decide +kernel
theorem sub2_499 : sub2 [2, -1, 1] = true := by decide +kernel
theorem sub2_500 : sub2 [2, -1, 2] = true := by decide +kernel
theorem sub2_501 : sub2 [2, -1, 3] = true := by decide +kernel
theorem sub2_502 : sub2 [2, -1, 4] = true := by decide +kernel
theorem sub2_503 : sub2 [2, -1, 5] = true := by decide +kernel
theorem sub2_504 : sub2 [2, -1, 6] = true := by decide +kernel
theorem sub2_505 : sub2 [2, -1, 7] = true := by decide +kernel
theorem sub2_506 : sub2 [2, -1, 8] = true := by decide +kernel
theorem sub2_507 : sub2 [2, -1, 9] = true := by decide +kernel
theorem sub2_508 : sub2 [2, 0, -9] = true := by decide +kernel
theorem sub2_509 : sub2 [2, 0, -8] = true := by decide +kernel
theorem sub2_510 : sub2 [2, 0, -7] = true := by decide +kernel
theorem sub2_511 : sub2 [2, 0, -6] = true := by decide +kernel
theorem sb2_15 : ∀ q ∈ blk2_15, sub2 q = true := by
  unfold blk2_15
  exact List.forall_mem_cons.2 ⟨sub2_480, List.forall_mem_cons.2 ⟨sub2_481, List.forall_mem_cons.2 ⟨sub2_482, List.forall_mem_cons.2 ⟨sub2_483, List.forall_mem_cons.2 ⟨sub2_484, List.forall_mem_cons.2 ⟨sub2_485, List.forall_mem_cons.2 ⟨sub2_486, List.forall_mem_cons.2 ⟨sub2_487, List.forall_mem_cons.2 ⟨sub2_488, List.forall_mem_cons.2 ⟨sub2_489, List.forall_mem_cons.2 ⟨sub2_490, List.forall_mem_cons.2 ⟨sub2_491, List.forall_mem_cons.2 ⟨sub2_492, List.forall_mem_cons.2 ⟨sub2_493, List.forall_mem_cons.2 ⟨sub2_494, List.forall_mem_cons.2 ⟨sub2_495, List.forall_mem_cons.2 ⟨sub2_496, List.forall_mem_cons.2 ⟨sub2_497, List.forall_mem_cons.2 ⟨sub2_498, List.forall_mem_cons.2 ⟨sub2_499, List.forall_mem_cons.2 ⟨sub2_500, List.forall_mem_cons.2 ⟨sub2_501, List.forall_mem_cons.2 ⟨sub2_502, List.forall_mem_cons.2 ⟨sub2_503, List.forall_mem_cons.2 ⟨sub2_504, List.forall_mem_cons.2 ⟨sub2_505, List.forall_mem_cons.2 ⟨sub2_506, List.forall_mem_cons.2 ⟨sub2_507, List.forall_mem_cons.2 ⟨sub2_508, List.forall_mem_cons.2 ⟨sub2_509, List.forall_mem_cons.2 ⟨sub2_510, List.forall_mem_cons.2 ⟨sub2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_512 : sub2 [2, 0, -5] = true := by decide +kernel
theorem sub2_513 : sub2 [2, 0, -4] = true := by decide +kernel
theorem sub2_514 : sub2 [2, 0, -3] = true := by decide +kernel
theorem sub2_515 : sub2 [2, 0, -2] = true := by decide +kernel
theorem sub2_516 : sub2 [2, 0, -1] = true := by decide +kernel
theorem sub2_517 : sub2 [2, 0, 0] = true := by decide +kernel
theorem sub2_518 : sub2 [2, 0, 1] = true := by decide +kernel
theorem sub2_519 : sub2 [2, 0, 2] = true := by decide +kernel
theorem sub2_520 : sub2 [2, 0, 3] = true := by decide +kernel
theorem sub2_521 : sub2 [2, 0, 4] = true := by decide +kernel
theorem sub2_522 : sub2 [2, 0, 5] = true := by decide +kernel
theorem sub2_523 : sub2 [2, 0, 6] = true := by decide +kernel
theorem sub2_524 : sub2 [2, 0, 7] = true := by decide +kernel
theorem sub2_525 : sub2 [2, 0, 8] = true := by decide +kernel
theorem sub2_526 : sub2 [2, 0, 9] = true := by decide +kernel
theorem sub2_527 : sub2 [2, 0, 10] = true := by decide +kernel
theorem sub2_528 : sub2 [2, 1, -9] = true := by decide +kernel
theorem sub2_529 : sub2 [2, 1, -8] = true := by decide +kernel
theorem sub2_530 : sub2 [2, 1, -7] = true := by decide +kernel
theorem sub2_531 : sub2 [2, 1, -6] = true := by decide +kernel
theorem sub2_532 : sub2 [2, 1, -5] = true := by decide +kernel
theorem sub2_533 : sub2 [2, 1, -4] = true := by decide +kernel
theorem sub2_534 : sub2 [2, 1, -3] = true := by decide +kernel
theorem sub2_535 : sub2 [2, 1, -2] = true := by decide +kernel
theorem sub2_536 : sub2 [2, 1, -1] = true := by decide +kernel
theorem sub2_537 : sub2 [2, 1, 0] = true := by decide +kernel
theorem sub2_538 : sub2 [2, 1, 1] = true := by decide +kernel
theorem sub2_539 : sub2 [2, 1, 2] = true := by decide +kernel
theorem sub2_540 : sub2 [2, 1, 3] = true := by decide +kernel
theorem sub2_541 : sub2 [2, 1, 4] = true := by decide +kernel
theorem sub2_542 : sub2 [2, 1, 5] = true := by decide +kernel
theorem sub2_543 : sub2 [2, 1, 6] = true := by decide +kernel
theorem sb2_16 : ∀ q ∈ blk2_16, sub2 q = true := by
  unfold blk2_16
  exact List.forall_mem_cons.2 ⟨sub2_512, List.forall_mem_cons.2 ⟨sub2_513, List.forall_mem_cons.2 ⟨sub2_514, List.forall_mem_cons.2 ⟨sub2_515, List.forall_mem_cons.2 ⟨sub2_516, List.forall_mem_cons.2 ⟨sub2_517, List.forall_mem_cons.2 ⟨sub2_518, List.forall_mem_cons.2 ⟨sub2_519, List.forall_mem_cons.2 ⟨sub2_520, List.forall_mem_cons.2 ⟨sub2_521, List.forall_mem_cons.2 ⟨sub2_522, List.forall_mem_cons.2 ⟨sub2_523, List.forall_mem_cons.2 ⟨sub2_524, List.forall_mem_cons.2 ⟨sub2_525, List.forall_mem_cons.2 ⟨sub2_526, List.forall_mem_cons.2 ⟨sub2_527, List.forall_mem_cons.2 ⟨sub2_528, List.forall_mem_cons.2 ⟨sub2_529, List.forall_mem_cons.2 ⟨sub2_530, List.forall_mem_cons.2 ⟨sub2_531, List.forall_mem_cons.2 ⟨sub2_532, List.forall_mem_cons.2 ⟨sub2_533, List.forall_mem_cons.2 ⟨sub2_534, List.forall_mem_cons.2 ⟨sub2_535, List.forall_mem_cons.2 ⟨sub2_536, List.forall_mem_cons.2 ⟨sub2_537, List.forall_mem_cons.2 ⟨sub2_538, List.forall_mem_cons.2 ⟨sub2_539, List.forall_mem_cons.2 ⟨sub2_540, List.forall_mem_cons.2 ⟨sub2_541, List.forall_mem_cons.2 ⟨sub2_542, List.forall_mem_cons.2 ⟨sub2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_544 : sub2 [2, 1, 7] = true := by decide +kernel
theorem sub2_545 : sub2 [2, 1, 8] = true := by decide +kernel
theorem sub2_546 : sub2 [2, 1, 9] = true := by decide +kernel
theorem sub2_547 : sub2 [2, 2, -8] = true := by decide +kernel
theorem sub2_548 : sub2 [2, 2, -7] = true := by decide +kernel
theorem sub2_549 : sub2 [2, 2, -6] = true := by decide +kernel
theorem sub2_550 : sub2 [2, 2, -5] = true := by decide +kernel
theorem sub2_551 : sub2 [2, 2, -4] = true := by decide +kernel
theorem sub2_552 : sub2 [2, 2, -3] = true := by decide +kernel
theorem sub2_553 : sub2 [2, 2, -2] = true := by decide +kernel
theorem sub2_554 : sub2 [2, 2, -1] = true := by decide +kernel
theorem sub2_555 : sub2 [2, 2, 0] = true := by decide +kernel
theorem sub2_556 : sub2 [2, 2, 1] = true := by decide +kernel
theorem sub2_557 : sub2 [2, 2, 2] = true := by decide +kernel
theorem sub2_558 : sub2 [2, 2, 3] = true := by decide +kernel
theorem sub2_559 : sub2 [2, 2, 4] = true := by decide +kernel
theorem sub2_560 : sub2 [2, 2, 5] = true := by decide +kernel
theorem sub2_561 : sub2 [2, 2, 6] = true := by decide +kernel
theorem sub2_562 : sub2 [2, 2, 7] = true := by decide +kernel
theorem sub2_563 : sub2 [2, 2, 8] = true := by decide +kernel
theorem sub2_564 : sub2 [2, 3] = true := by decide +kernel
theorem sub2_565 : sub2 [3, -3] = true := by decide +kernel
theorem sub2_566 : sub2 [3, -2] = true := by decide +kernel
theorem sub2_567 : sub2 [3, -1] = true := by decide +kernel
theorem sub2_568 : sub2 [3, 0, -7] = true := by decide +kernel
theorem sub2_569 : sub2 [3, 0, -6] = true := by decide +kernel
theorem sub2_570 : sub2 [3, 0, -5] = true := by decide +kernel
theorem sub2_571 : sub2 [3, 0, -4] = true := by decide +kernel
theorem sub2_572 : sub2 [3, 0, -3] = true := by decide +kernel
theorem sub2_573 : sub2 [3, 0, -2] = true := by decide +kernel
theorem sub2_574 : sub2 [3, 0, -1] = true := by decide +kernel
theorem sub2_575 : sub2 [3, 0, 0] = true := by decide +kernel
theorem sb2_17 : ∀ q ∈ blk2_17, sub2 q = true := by
  unfold blk2_17
  exact List.forall_mem_cons.2 ⟨sub2_544, List.forall_mem_cons.2 ⟨sub2_545, List.forall_mem_cons.2 ⟨sub2_546, List.forall_mem_cons.2 ⟨sub2_547, List.forall_mem_cons.2 ⟨sub2_548, List.forall_mem_cons.2 ⟨sub2_549, List.forall_mem_cons.2 ⟨sub2_550, List.forall_mem_cons.2 ⟨sub2_551, List.forall_mem_cons.2 ⟨sub2_552, List.forall_mem_cons.2 ⟨sub2_553, List.forall_mem_cons.2 ⟨sub2_554, List.forall_mem_cons.2 ⟨sub2_555, List.forall_mem_cons.2 ⟨sub2_556, List.forall_mem_cons.2 ⟨sub2_557, List.forall_mem_cons.2 ⟨sub2_558, List.forall_mem_cons.2 ⟨sub2_559, List.forall_mem_cons.2 ⟨sub2_560, List.forall_mem_cons.2 ⟨sub2_561, List.forall_mem_cons.2 ⟨sub2_562, List.forall_mem_cons.2 ⟨sub2_563, List.forall_mem_cons.2 ⟨sub2_564, List.forall_mem_cons.2 ⟨sub2_565, List.forall_mem_cons.2 ⟨sub2_566, List.forall_mem_cons.2 ⟨sub2_567, List.forall_mem_cons.2 ⟨sub2_568, List.forall_mem_cons.2 ⟨sub2_569, List.forall_mem_cons.2 ⟨sub2_570, List.forall_mem_cons.2 ⟨sub2_571, List.forall_mem_cons.2 ⟨sub2_572, List.forall_mem_cons.2 ⟨sub2_573, List.forall_mem_cons.2 ⟨sub2_574, List.forall_mem_cons.2 ⟨sub2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_576 : sub2 [3, 0, 1] = true := by decide +kernel
theorem sub2_577 : sub2 [3, 0, 2] = true := by decide +kernel
theorem sub2_578 : sub2 [3, 0, 3] = true := by decide +kernel
theorem sub2_579 : sub2 [3, 0, 4] = true := by decide +kernel
theorem sub2_580 : sub2 [3, 0, 5] = true := by decide +kernel
theorem sub2_581 : sub2 [3, 0, 6] = true := by decide +kernel
theorem sub2_582 : sub2 [3, 0, 7] = true := by decide +kernel
theorem sub2_583 : sub2 [3, 0, 8] = true := by decide +kernel
theorem sub2_584 : sub2 [3, 1, -7] = true := by decide +kernel
theorem sub2_585 : sub2 [3, 1, -6] = true := by decide +kernel
theorem sub2_586 : sub2 [3, 1, -5] = true := by decide +kernel
theorem sub2_587 : sub2 [3, 1, -4] = true := by decide +kernel
theorem sub2_588 : sub2 [3, 1, -3] = true := by decide +kernel
theorem sub2_589 : sub2 [3, 1, -2] = true := by decide +kernel
theorem sub2_590 : sub2 [3, 1, -1] = true := by decide +kernel
theorem sub2_591 : sub2 [3, 1, 0] = true := by decide +kernel
theorem sub2_592 : sub2 [3, 1, 1] = true := by decide +kernel
theorem sub2_593 : sub2 [3, 1, 2] = true := by decide +kernel
theorem sub2_594 : sub2 [3, 1, 3] = true := by decide +kernel
theorem sub2_595 : sub2 [3, 1, 4] = true := by decide +kernel
theorem sub2_596 : sub2 [3, 1, 5] = true := by decide +kernel
theorem sub2_597 : sub2 [3, 1, 6] = true := by decide +kernel
theorem sub2_598 : sub2 [3, 1, 7] = true := by decide +kernel
theorem sub2_599 : sub2 [3, 1, 8] = true := by decide +kernel
theorem sub2_600 : sub2 [3, 2] = true := by decide +kernel
theorem sub2_601 : sub2 [3, 3] = true := by decide +kernel
theorem sub2_602 : sub2 [4] = true := by decide +kernel
theorem sb2_18 : ∀ q ∈ blk2_18, sub2 q = true := by
  unfold blk2_18
  exact List.forall_mem_cons.2 ⟨sub2_576, List.forall_mem_cons.2 ⟨sub2_577, List.forall_mem_cons.2 ⟨sub2_578, List.forall_mem_cons.2 ⟨sub2_579, List.forall_mem_cons.2 ⟨sub2_580, List.forall_mem_cons.2 ⟨sub2_581, List.forall_mem_cons.2 ⟨sub2_582, List.forall_mem_cons.2 ⟨sub2_583, List.forall_mem_cons.2 ⟨sub2_584, List.forall_mem_cons.2 ⟨sub2_585, List.forall_mem_cons.2 ⟨sub2_586, List.forall_mem_cons.2 ⟨sub2_587, List.forall_mem_cons.2 ⟨sub2_588, List.forall_mem_cons.2 ⟨sub2_589, List.forall_mem_cons.2 ⟨sub2_590, List.forall_mem_cons.2 ⟨sub2_591, List.forall_mem_cons.2 ⟨sub2_592, List.forall_mem_cons.2 ⟨sub2_593, List.forall_mem_cons.2 ⟨sub2_594, List.forall_mem_cons.2 ⟨sub2_595, List.forall_mem_cons.2 ⟨sub2_596, List.forall_mem_cons.2 ⟨sub2_597, List.forall_mem_cons.2 ⟨sub2_598, List.forall_mem_cons.2 ⟨sub2_599, List.forall_mem_cons.2 ⟨sub2_600, List.forall_mem_cons.2 ⟨sub2_601, List.forall_mem_cons.2 ⟨sub2_602, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_0 : sub3 [-3, -3] = true := by decide +kernel
theorem sub3_1 : sub3 [-3, -2] = true := by decide +kernel
theorem sub3_2 : sub3 [-3, -1, -8] = true := by decide +kernel
theorem sub3_3 : sub3 [-3, -1, -7] = true := by decide +kernel
theorem sub3_4 : sub3 [-3, -1, -6] = true := by decide +kernel
theorem sub3_5 : sub3 [-3, -1, -5] = true := by decide +kernel
theorem sub3_6 : sub3 [-3, -1, -4] = true := by decide +kernel
theorem sub3_7 : sub3 [-3, -1, -3] = true := by decide +kernel
theorem sub3_8 : sub3 [-3, -1, -2] = true := by decide +kernel
theorem sub3_9 : sub3 [-3, -1, -1] = true := by decide +kernel
theorem sub3_10 : sub3 [-3, -1, 0] = true := by decide +kernel
theorem sub3_11 : sub3 [-3, -1, 1] = true := by decide +kernel
theorem sub3_12 : sub3 [-3, -1, 2] = true := by decide +kernel
theorem sub3_13 : sub3 [-3, -1, 3] = true := by decide +kernel
theorem sub3_14 : sub3 [-3, -1, 4] = true := by decide +kernel
theorem sub3_15 : sub3 [-3, -1, 5] = true := by decide +kernel
theorem sub3_16 : sub3 [-3, -1, 6] = true := by decide +kernel
theorem sub3_17 : sub3 [-3, -1, 7] = true := by decide +kernel
theorem sub3_18 : sub3 [-3, 0, -9] = true := by decide +kernel
theorem sub3_19 : sub3 [-3, 0, -8] = true := by decide +kernel
theorem sub3_20 : sub3 [-3, 0, -7] = true := by decide +kernel
theorem sub3_21 : sub3 [-3, 0, -6] = true := by decide +kernel
theorem sub3_22 : sub3 [-3, 0, -5] = true := by decide +kernel
theorem sub3_23 : sub3 [-3, 0, -4] = true := by decide +kernel
theorem sub3_24 : sub3 [-3, 0, -3] = true := by decide +kernel
theorem sub3_25 : sub3 [-3, 0, -2] = true := by decide +kernel
theorem sub3_26 : sub3 [-3, 0, -1] = true := by decide +kernel
theorem sub3_27 : sub3 [-3, 0, 0] = true := by decide +kernel
theorem sub3_28 : sub3 [-3, 0, 1] = true := by decide +kernel
theorem sub3_29 : sub3 [-3, 0, 2] = true := by decide +kernel
theorem sub3_30 : sub3 [-3, 0, 3] = true := by decide +kernel
theorem sub3_31 : sub3 [-3, 0, 4] = true := by decide +kernel
theorem sb3_0 : ∀ q ∈ blk3_0, sub3 q = true := by
  unfold blk3_0
  exact List.forall_mem_cons.2 ⟨sub3_0, List.forall_mem_cons.2 ⟨sub3_1, List.forall_mem_cons.2 ⟨sub3_2, List.forall_mem_cons.2 ⟨sub3_3, List.forall_mem_cons.2 ⟨sub3_4, List.forall_mem_cons.2 ⟨sub3_5, List.forall_mem_cons.2 ⟨sub3_6, List.forall_mem_cons.2 ⟨sub3_7, List.forall_mem_cons.2 ⟨sub3_8, List.forall_mem_cons.2 ⟨sub3_9, List.forall_mem_cons.2 ⟨sub3_10, List.forall_mem_cons.2 ⟨sub3_11, List.forall_mem_cons.2 ⟨sub3_12, List.forall_mem_cons.2 ⟨sub3_13, List.forall_mem_cons.2 ⟨sub3_14, List.forall_mem_cons.2 ⟨sub3_15, List.forall_mem_cons.2 ⟨sub3_16, List.forall_mem_cons.2 ⟨sub3_17, List.forall_mem_cons.2 ⟨sub3_18, List.forall_mem_cons.2 ⟨sub3_19, List.forall_mem_cons.2 ⟨sub3_20, List.forall_mem_cons.2 ⟨sub3_21, List.forall_mem_cons.2 ⟨sub3_22, List.forall_mem_cons.2 ⟨sub3_23, List.forall_mem_cons.2 ⟨sub3_24, List.forall_mem_cons.2 ⟨sub3_25, List.forall_mem_cons.2 ⟨sub3_26, List.forall_mem_cons.2 ⟨sub3_27, List.forall_mem_cons.2 ⟨sub3_28, List.forall_mem_cons.2 ⟨sub3_29, List.forall_mem_cons.2 ⟨sub3_30, List.forall_mem_cons.2 ⟨sub3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_32 : sub3 [-3, 0, 5] = true := by decide +kernel
theorem sub3_33 : sub3 [-3, 0, 6] = true := by decide +kernel
theorem sub3_34 : sub3 [-3, 0, 7] = true := by decide +kernel
theorem sub3_35 : sub3 [-3, 0, 8] = true := by decide +kernel
theorem sub3_36 : sub3 [-3, 1, -9] = true := by decide +kernel
theorem sub3_37 : sub3 [-3, 1, -8] = true := by decide +kernel
theorem sub3_38 : sub3 [-3, 1, -7] = true := by decide +kernel
theorem sub3_39 : sub3 [-3, 1, -6] = true := by decide +kernel
theorem sub3_40 : sub3 [-3, 1, -5] = true := by decide +kernel
theorem sub3_41 : sub3 [-3, 1, -4] = true := by decide +kernel
theorem sub3_42 : sub3 [-3, 1, -3] = true := by decide +kernel
theorem sub3_43 : sub3 [-3, 1, -2] = true := by decide +kernel
theorem sub3_44 : sub3 [-3, 1, -1] = true := by decide +kernel
theorem sub3_45 : sub3 [-3, 1, 0] = true := by decide +kernel
theorem sub3_46 : sub3 [-3, 1, 1] = true := by decide +kernel
theorem sub3_47 : sub3 [-3, 1, 2] = true := by decide +kernel
theorem sub3_48 : sub3 [-3, 1, 3] = true := by decide +kernel
theorem sub3_49 : sub3 [-3, 1, 4] = true := by decide +kernel
theorem sub3_50 : sub3 [-3, 1, 5] = true := by decide +kernel
theorem sub3_51 : sub3 [-3, 1, 6] = true := by decide +kernel
theorem sub3_52 : sub3 [-3, 1, 7] = true := by decide +kernel
theorem sub3_53 : sub3 [-3, 1, 8] = true := by decide +kernel
theorem sub3_54 : sub3 [-3, 2] = true := by decide +kernel
theorem sub3_55 : sub3 [-2, -4] = true := by decide +kernel
theorem sub3_56 : sub3 [-2, -3] = true := by decide +kernel
theorem sub3_57 : sub3 [-2, -2, -10] = true := by decide +kernel
theorem sub3_58 : sub3 [-2, -2, -9] = true := by decide +kernel
theorem sub3_59 : sub3 [-2, -2, -8] = true := by decide +kernel
theorem sub3_60 : sub3 [-2, -2, -7] = true := by decide +kernel
theorem sub3_61 : sub3 [-2, -2, -6] = true := by decide +kernel
theorem sub3_62 : sub3 [-2, -2, -5] = true := by decide +kernel
theorem sub3_63 : sub3 [-2, -2, -4] = true := by decide +kernel
theorem sb3_1 : ∀ q ∈ blk3_1, sub3 q = true := by
  unfold blk3_1
  exact List.forall_mem_cons.2 ⟨sub3_32, List.forall_mem_cons.2 ⟨sub3_33, List.forall_mem_cons.2 ⟨sub3_34, List.forall_mem_cons.2 ⟨sub3_35, List.forall_mem_cons.2 ⟨sub3_36, List.forall_mem_cons.2 ⟨sub3_37, List.forall_mem_cons.2 ⟨sub3_38, List.forall_mem_cons.2 ⟨sub3_39, List.forall_mem_cons.2 ⟨sub3_40, List.forall_mem_cons.2 ⟨sub3_41, List.forall_mem_cons.2 ⟨sub3_42, List.forall_mem_cons.2 ⟨sub3_43, List.forall_mem_cons.2 ⟨sub3_44, List.forall_mem_cons.2 ⟨sub3_45, List.forall_mem_cons.2 ⟨sub3_46, List.forall_mem_cons.2 ⟨sub3_47, List.forall_mem_cons.2 ⟨sub3_48, List.forall_mem_cons.2 ⟨sub3_49, List.forall_mem_cons.2 ⟨sub3_50, List.forall_mem_cons.2 ⟨sub3_51, List.forall_mem_cons.2 ⟨sub3_52, List.forall_mem_cons.2 ⟨sub3_53, List.forall_mem_cons.2 ⟨sub3_54, List.forall_mem_cons.2 ⟨sub3_55, List.forall_mem_cons.2 ⟨sub3_56, List.forall_mem_cons.2 ⟨sub3_57, List.forall_mem_cons.2 ⟨sub3_58, List.forall_mem_cons.2 ⟨sub3_59, List.forall_mem_cons.2 ⟨sub3_60, List.forall_mem_cons.2 ⟨sub3_61, List.forall_mem_cons.2 ⟨sub3_62, List.forall_mem_cons.2 ⟨sub3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_64 : sub3 [-2, -2, -3] = true := by decide +kernel
theorem sub3_65 : sub3 [-2, -2, -2] = true := by decide +kernel
theorem sub3_66 : sub3 [-2, -2, -1] = true := by decide +kernel
theorem sub3_67 : sub3 [-2, -2, 0] = true := by decide +kernel
theorem sub3_68 : sub3 [-2, -2, 1] = true := by decide +kernel
theorem sub3_69 : sub3 [-2, -2, 2] = true := by decide +kernel
theorem sub3_70 : sub3 [-2, -2, 3] = true := by decide +kernel
theorem sub3_71 : sub3 [-2, -2, 4] = true := by decide +kernel
theorem sub3_72 : sub3 [-2, -2, 5] = true := by decide +kernel
theorem sub3_73 : sub3 [-2, -2, 6] = true := by decide +kernel
theorem sub3_74 : sub3 [-2, -2, 7] = true := by decide +kernel
theorem sub3_75 : sub3 [-2, -2, 8] = true := by decide +kernel
theorem sub3_76 : sub3 [-2, -2, 9] = true := by decide +kernel
theorem sub3_77 : sub3 [-2, -1, -12] = true := by decide +kernel
theorem sub3_78 : sub3 [-2, -1, -11] = true := by decide +kernel
theorem sub3_79 : sub3 [-2, -1, -10] = true := by decide +kernel
theorem sub3_80 : sub3 [-2, -1, -9] = true := by decide +kernel
theorem sub3_81 : sub3 [-2, -1, -8] = true := by decide +kernel
theorem sub3_82 : sub3 [-2, -1, -7] = true := by decide +kernel
theorem sub3_83 : sub3 [-2, -1, -6] = true := by decide +kernel
theorem sub3_84 : sub3 [-2, -1, -5] = true := by decide +kernel
theorem sub3_85 : sub3 [-2, -1, -4] = true := by decide +kernel
theorem sub3_86 : sub3 [-2, -1, -3] = true := by decide +kernel
theorem sub3_87 : sub3 [-2, -1, -2] = true := by decide +kernel
theorem sub3_88 : sub3 [-2, -1, -1] = true := by decide +kernel
theorem sub3_89 : sub3 [-2, -1, 0] = true := by decide +kernel
theorem sub3_90 : sub3 [-2, -1, 1] = true := by decide +kernel
theorem sub3_91 : sub3 [-2, -1, 2] = true := by decide +kernel
theorem sub3_92 : sub3 [-2, -1, 3] = true := by decide +kernel
theorem sub3_93 : sub3 [-2, -1, 4] = true := by decide +kernel
theorem sub3_94 : sub3 [-2, -1, 5] = true := by decide +kernel
theorem sub3_95 : sub3 [-2, -1, 6] = true := by decide +kernel
theorem sb3_2 : ∀ q ∈ blk3_2, sub3 q = true := by
  unfold blk3_2
  exact List.forall_mem_cons.2 ⟨sub3_64, List.forall_mem_cons.2 ⟨sub3_65, List.forall_mem_cons.2 ⟨sub3_66, List.forall_mem_cons.2 ⟨sub3_67, List.forall_mem_cons.2 ⟨sub3_68, List.forall_mem_cons.2 ⟨sub3_69, List.forall_mem_cons.2 ⟨sub3_70, List.forall_mem_cons.2 ⟨sub3_71, List.forall_mem_cons.2 ⟨sub3_72, List.forall_mem_cons.2 ⟨sub3_73, List.forall_mem_cons.2 ⟨sub3_74, List.forall_mem_cons.2 ⟨sub3_75, List.forall_mem_cons.2 ⟨sub3_76, List.forall_mem_cons.2 ⟨sub3_77, List.forall_mem_cons.2 ⟨sub3_78, List.forall_mem_cons.2 ⟨sub3_79, List.forall_mem_cons.2 ⟨sub3_80, List.forall_mem_cons.2 ⟨sub3_81, List.forall_mem_cons.2 ⟨sub3_82, List.forall_mem_cons.2 ⟨sub3_83, List.forall_mem_cons.2 ⟨sub3_84, List.forall_mem_cons.2 ⟨sub3_85, List.forall_mem_cons.2 ⟨sub3_86, List.forall_mem_cons.2 ⟨sub3_87, List.forall_mem_cons.2 ⟨sub3_88, List.forall_mem_cons.2 ⟨sub3_89, List.forall_mem_cons.2 ⟨sub3_90, List.forall_mem_cons.2 ⟨sub3_91, List.forall_mem_cons.2 ⟨sub3_92, List.forall_mem_cons.2 ⟨sub3_93, List.forall_mem_cons.2 ⟨sub3_94, List.forall_mem_cons.2 ⟨sub3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_96 : sub3 [-2, -1, 7] = true := by decide +kernel
theorem sub3_97 : sub3 [-2, -1, 8] = true := by decide +kernel
theorem sub3_98 : sub3 [-2, -1, 9] = true := by decide +kernel
theorem sub3_99 : sub3 [-2, -1, 10] = true := by decide +kernel
theorem sub3_100 : sub3 [-2, -1, 11] = true := by decide +kernel
theorem sub3_101 : sub3 [-2, 0, -13] = true := by decide +kernel
theorem sub3_102 : sub3 [-2, 0, -12] = true := by decide +kernel
theorem sub3_103 : sub3 [-2, 0, -11] = true := by decide +kernel
theorem sub3_104 : sub3 [-2, 0, -10] = true := by decide +kernel
theorem sub3_105 : sub3 [-2, 0, -9] = true := by decide +kernel
theorem sub3_106 : sub3 [-2, 0, -8] = true := by decide +kernel
theorem sub3_107 : sub3 [-2, 0, -7] = true := by decide +kernel
theorem sub3_108 : sub3 [-2, 0, -6] = true := by decide +kernel
theorem sub3_109 : sub3 [-2, 0, -5] = true := by decide +kernel
theorem sub3_110 : sub3 [-2, 0, -4] = true := by decide +kernel
theorem sub3_111 : sub3 [-2, 0, -3] = true := by decide +kernel
theorem sub3_112 : sub3 [-2, 0, -2] = true := by decide +kernel
theorem sub3_113 : sub3 [-2, 0, -1] = true := by decide +kernel
theorem sub3_114 : sub3 [-2, 0, 0] = true := by decide +kernel
theorem sub3_115 : sub3 [-2, 0, 1] = true := by decide +kernel
theorem sub3_116 : sub3 [-2, 0, 2] = true := by decide +kernel
theorem sub3_117 : sub3 [-2, 0, 3] = true := by decide +kernel
theorem sub3_118 : sub3 [-2, 0, 4] = true := by decide +kernel
theorem sub3_119 : sub3 [-2, 0, 5] = true := by decide +kernel
theorem sub3_120 : sub3 [-2, 0, 6] = true := by decide +kernel
theorem sub3_121 : sub3 [-2, 0, 7] = true := by decide +kernel
theorem sub3_122 : sub3 [-2, 0, 8] = true := by decide +kernel
theorem sub3_123 : sub3 [-2, 0, 9] = true := by decide +kernel
theorem sub3_124 : sub3 [-2, 0, 10] = true := by decide +kernel
theorem sub3_125 : sub3 [-2, 0, 11] = true := by decide +kernel
theorem sub3_126 : sub3 [-2, 0, 12] = true := by decide +kernel
theorem sub3_127 : sub3 [-2, 1, -12] = true := by decide +kernel
theorem sb3_3 : ∀ q ∈ blk3_3, sub3 q = true := by
  unfold blk3_3
  exact List.forall_mem_cons.2 ⟨sub3_96, List.forall_mem_cons.2 ⟨sub3_97, List.forall_mem_cons.2 ⟨sub3_98, List.forall_mem_cons.2 ⟨sub3_99, List.forall_mem_cons.2 ⟨sub3_100, List.forall_mem_cons.2 ⟨sub3_101, List.forall_mem_cons.2 ⟨sub3_102, List.forall_mem_cons.2 ⟨sub3_103, List.forall_mem_cons.2 ⟨sub3_104, List.forall_mem_cons.2 ⟨sub3_105, List.forall_mem_cons.2 ⟨sub3_106, List.forall_mem_cons.2 ⟨sub3_107, List.forall_mem_cons.2 ⟨sub3_108, List.forall_mem_cons.2 ⟨sub3_109, List.forall_mem_cons.2 ⟨sub3_110, List.forall_mem_cons.2 ⟨sub3_111, List.forall_mem_cons.2 ⟨sub3_112, List.forall_mem_cons.2 ⟨sub3_113, List.forall_mem_cons.2 ⟨sub3_114, List.forall_mem_cons.2 ⟨sub3_115, List.forall_mem_cons.2 ⟨sub3_116, List.forall_mem_cons.2 ⟨sub3_117, List.forall_mem_cons.2 ⟨sub3_118, List.forall_mem_cons.2 ⟨sub3_119, List.forall_mem_cons.2 ⟨sub3_120, List.forall_mem_cons.2 ⟨sub3_121, List.forall_mem_cons.2 ⟨sub3_122, List.forall_mem_cons.2 ⟨sub3_123, List.forall_mem_cons.2 ⟨sub3_124, List.forall_mem_cons.2 ⟨sub3_125, List.forall_mem_cons.2 ⟨sub3_126, List.forall_mem_cons.2 ⟨sub3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C081
