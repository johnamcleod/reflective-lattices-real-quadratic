import ReflectZphi.Data.Cert5.C079.Base

namespace ReflectZphi.Data.Cert5.C079
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_320 : sub7 [1, 1, -4] = true := by decide +kernel
theorem sub7_321 : sub7 [1, 1, -3] = true := by decide +kernel
theorem sub7_322 : sub7 [1, 1, -2] = true := by decide +kernel
theorem sub7_323 : sub7 [1, 1, -1] = true := by decide +kernel
theorem sub7_324 : sub7 [1, 1, 0] = true := by decide +kernel
theorem sub7_325 : sub7 [1, 1, 1] = true := by decide +kernel
theorem sub7_326 : sub7 [1, 1, 2] = true := by decide +kernel
theorem sub7_327 : sub7 [1, 1, 3] = true := by decide +kernel
theorem sub7_328 : sub7 [1, 1, 4] = true := by decide +kernel
theorem sub7_329 : sub7 [1, 1, 5] = true := by decide +kernel
theorem sub7_330 : sub7 [1, 1, 6] = true := by decide +kernel
theorem sub7_331 : sub7 [1, 1, 7] = true := by decide +kernel
theorem sub7_332 : sub7 [1, 2, -7] = true := by decide +kernel
theorem sub7_333 : sub7 [1, 2, -6] = true := by decide +kernel
theorem sub7_334 : sub7 [1, 2, -5] = true := by decide +kernel
theorem sub7_335 : sub7 [1, 2, -4] = true := by decide +kernel
theorem sub7_336 : sub7 [1, 2, -3] = true := by decide +kernel
theorem sub7_337 : sub7 [1, 2, -2] = true := by decide +kernel
theorem sub7_338 : sub7 [1, 2, -1] = true := by decide +kernel
theorem sub7_339 : sub7 [1, 2, 0] = true := by decide +kernel
theorem sub7_340 : sub7 [1, 2, 1] = true := by decide +kernel
theorem sub7_341 : sub7 [1, 2, 2] = true := by decide +kernel
theorem sub7_342 : sub7 [1, 2, 3] = true := by decide +kernel
theorem sub7_343 : sub7 [1, 2, 4] = true := by decide +kernel
theorem sub7_344 : sub7 [1, 2, 5] = true := by decide +kernel
theorem sub7_345 : sub7 [1, 2, 6] = true := by decide +kernel
theorem sub7_346 : sub7 [1, 3] = true := by decide +kernel
theorem sub7_347 : sub7 [1, 4] = true := by decide +kernel
theorem sub7_348 : sub7 [1, 5] = true := by decide +kernel
theorem sub7_349 : sub7 [1, 6] = true := by decide +kernel
theorem sub7_350 : sub7 [1, 7] = true := by decide +kernel
theorem sub7_351 : sub7 [2, -9] = true := by decide +kernel
theorem sb7_10 : ∀ q ∈ blk7_10, sub7 q = true := by
  unfold blk7_10
  exact List.forall_mem_cons.2 ⟨sub7_320, List.forall_mem_cons.2 ⟨sub7_321, List.forall_mem_cons.2 ⟨sub7_322, List.forall_mem_cons.2 ⟨sub7_323, List.forall_mem_cons.2 ⟨sub7_324, List.forall_mem_cons.2 ⟨sub7_325, List.forall_mem_cons.2 ⟨sub7_326, List.forall_mem_cons.2 ⟨sub7_327, List.forall_mem_cons.2 ⟨sub7_328, List.forall_mem_cons.2 ⟨sub7_329, List.forall_mem_cons.2 ⟨sub7_330, List.forall_mem_cons.2 ⟨sub7_331, List.forall_mem_cons.2 ⟨sub7_332, List.forall_mem_cons.2 ⟨sub7_333, List.forall_mem_cons.2 ⟨sub7_334, List.forall_mem_cons.2 ⟨sub7_335, List.forall_mem_cons.2 ⟨sub7_336, List.forall_mem_cons.2 ⟨sub7_337, List.forall_mem_cons.2 ⟨sub7_338, List.forall_mem_cons.2 ⟨sub7_339, List.forall_mem_cons.2 ⟨sub7_340, List.forall_mem_cons.2 ⟨sub7_341, List.forall_mem_cons.2 ⟨sub7_342, List.forall_mem_cons.2 ⟨sub7_343, List.forall_mem_cons.2 ⟨sub7_344, List.forall_mem_cons.2 ⟨sub7_345, List.forall_mem_cons.2 ⟨sub7_346, List.forall_mem_cons.2 ⟨sub7_347, List.forall_mem_cons.2 ⟨sub7_348, List.forall_mem_cons.2 ⟨sub7_349, List.forall_mem_cons.2 ⟨sub7_350, List.forall_mem_cons.2 ⟨sub7_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_352 : sub7 [2, -8] = true := by decide +kernel
theorem sub7_353 : sub7 [2, -7] = true := by decide +kernel
theorem sub7_354 : sub7 [2, -6] = true := by decide +kernel
theorem sub7_355 : sub7 [2, -5] = true := by decide +kernel
theorem sub7_356 : sub7 [2, -4] = true := by decide +kernel
theorem sub7_357 : sub7 [2, -3] = true := by decide +kernel
theorem sub7_358 : sub7 [2, -2] = true := by decide +kernel
theorem sub7_359 : sub7 [2, -1, -7] = true := by decide +kernel
theorem sub7_360 : sub7 [2, -1, -6] = true := by decide +kernel
theorem sub7_361 : sub7 [2, -1, -5] = true := by decide +kernel
theorem sub7_362 : sub7 [2, -1, -4] = true := by decide +kernel
theorem sub7_363 : sub7 [2, -1, -3] = true := by decide +kernel
theorem sub7_364 : sub7 [2, -1, -2] = true := by decide +kernel
theorem sub7_365 : sub7 [2, -1, -1] = true := by decide +kernel
theorem sub7_366 : sub7 [2, -1, 0] = true := by decide +kernel
theorem sub7_367 : sub7 [2, -1, 1] = true := by decide +kernel
theorem sub7_368 : sub7 [2, -1, 2] = true := by decide +kernel
theorem sub7_369 : sub7 [2, -1, 3] = true := by decide +kernel
theorem sub7_370 : sub7 [2, -1, 4] = true := by decide +kernel
theorem sub7_371 : sub7 [2, -1, 5] = true := by decide +kernel
theorem sub7_372 : sub7 [2, -1, 6] = true := by decide +kernel
theorem sub7_373 : sub7 [2, -1, 7] = true := by decide +kernel
theorem sub7_374 : sub7 [2, 0, -7] = true := by decide +kernel
theorem sub7_375 : sub7 [2, 0, -6] = true := by decide +kernel
theorem sub7_376 : sub7 [2, 0, -5] = true := by decide +kernel
theorem sub7_377 : sub7 [2, 0, -4] = true := by decide +kernel
theorem sub7_378 : sub7 [2, 0, -3] = true := by decide +kernel
theorem sub7_379 : sub7 [2, 0, -2] = true := by decide +kernel
theorem sub7_380 : sub7 [2, 0, -1] = true := by decide +kernel
theorem sub7_381 : sub7 [2, 0, 0] = true := by decide +kernel
theorem sub7_382 : sub7 [2, 0, 1] = true := by decide +kernel
theorem sub7_383 : sub7 [2, 0, 2] = true := by decide +kernel
theorem sb7_11 : ∀ q ∈ blk7_11, sub7 q = true := by
  unfold blk7_11
  exact List.forall_mem_cons.2 ⟨sub7_352, List.forall_mem_cons.2 ⟨sub7_353, List.forall_mem_cons.2 ⟨sub7_354, List.forall_mem_cons.2 ⟨sub7_355, List.forall_mem_cons.2 ⟨sub7_356, List.forall_mem_cons.2 ⟨sub7_357, List.forall_mem_cons.2 ⟨sub7_358, List.forall_mem_cons.2 ⟨sub7_359, List.forall_mem_cons.2 ⟨sub7_360, List.forall_mem_cons.2 ⟨sub7_361, List.forall_mem_cons.2 ⟨sub7_362, List.forall_mem_cons.2 ⟨sub7_363, List.forall_mem_cons.2 ⟨sub7_364, List.forall_mem_cons.2 ⟨sub7_365, List.forall_mem_cons.2 ⟨sub7_366, List.forall_mem_cons.2 ⟨sub7_367, List.forall_mem_cons.2 ⟨sub7_368, List.forall_mem_cons.2 ⟨sub7_369, List.forall_mem_cons.2 ⟨sub7_370, List.forall_mem_cons.2 ⟨sub7_371, List.forall_mem_cons.2 ⟨sub7_372, List.forall_mem_cons.2 ⟨sub7_373, List.forall_mem_cons.2 ⟨sub7_374, List.forall_mem_cons.2 ⟨sub7_375, List.forall_mem_cons.2 ⟨sub7_376, List.forall_mem_cons.2 ⟨sub7_377, List.forall_mem_cons.2 ⟨sub7_378, List.forall_mem_cons.2 ⟨sub7_379, List.forall_mem_cons.2 ⟨sub7_380, List.forall_mem_cons.2 ⟨sub7_381, List.forall_mem_cons.2 ⟨sub7_382, List.forall_mem_cons.2 ⟨sub7_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_384 : sub7 [2, 0, 3] = true := by decide +kernel
theorem sub7_385 : sub7 [2, 0, 4] = true := by decide +kernel
theorem sub7_386 : sub7 [2, 0, 5] = true := by decide +kernel
theorem sub7_387 : sub7 [2, 0, 6] = true := by decide +kernel
theorem sub7_388 : sub7 [2, 0, 7] = true := by decide +kernel
theorem sub7_389 : sub7 [2, 1] = true := by decide +kernel
theorem sub7_390 : sub7 [2, 2] = true := by decide +kernel
theorem sub7_391 : sub7 [2, 3] = true := by decide +kernel
theorem sub7_392 : sub7 [2, 4] = true := by decide +kernel
theorem sub7_393 : sub7 [2, 5] = true := by decide +kernel
theorem sub7_394 : sub7 [2, 6] = true := by decide +kernel
theorem sub7_395 : sub7 [2, 7] = true := by decide +kernel
theorem sub7_396 : sub7 [3, -8] = true := by decide +kernel
theorem sub7_397 : sub7 [3, -7] = true := by decide +kernel
theorem sub7_398 : sub7 [3, -6] = true := by decide +kernel
theorem sub7_399 : sub7 [3, -5] = true := by decide +kernel
theorem sub7_400 : sub7 [3, -4] = true := by decide +kernel
theorem sub7_401 : sub7 [3, -3] = true := by decide +kernel
theorem sub7_402 : sub7 [3, -2] = true := by decide +kernel
theorem sub7_403 : sub7 [3, -1] = true := by decide +kernel
theorem sub7_404 : sub7 [3, 0] = true := by decide +kernel
theorem sub7_405 : sub7 [3, 1] = true := by decide +kernel
theorem sub7_406 : sub7 [3, 2] = true := by decide +kernel
theorem sub7_407 : sub7 [3, 3] = true := by decide +kernel
theorem sub7_408 : sub7 [3, 4] = true := by decide +kernel
theorem sub7_409 : sub7 [3, 5] = true := by decide +kernel
theorem sub7_410 : sub7 [3, 6] = true := by decide +kernel
theorem sub7_411 : sub7 [4, -8] = true := by decide +kernel
theorem sub7_412 : sub7 [4, -7] = true := by decide +kernel
theorem sub7_413 : sub7 [4, -6] = true := by decide +kernel
theorem sub7_414 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_415 : sub7 [4, -4] = true := by decide +kernel
theorem sb7_12 : ∀ q ∈ blk7_12, sub7 q = true := by
  unfold blk7_12
  exact List.forall_mem_cons.2 ⟨sub7_384, List.forall_mem_cons.2 ⟨sub7_385, List.forall_mem_cons.2 ⟨sub7_386, List.forall_mem_cons.2 ⟨sub7_387, List.forall_mem_cons.2 ⟨sub7_388, List.forall_mem_cons.2 ⟨sub7_389, List.forall_mem_cons.2 ⟨sub7_390, List.forall_mem_cons.2 ⟨sub7_391, List.forall_mem_cons.2 ⟨sub7_392, List.forall_mem_cons.2 ⟨sub7_393, List.forall_mem_cons.2 ⟨sub7_394, List.forall_mem_cons.2 ⟨sub7_395, List.forall_mem_cons.2 ⟨sub7_396, List.forall_mem_cons.2 ⟨sub7_397, List.forall_mem_cons.2 ⟨sub7_398, List.forall_mem_cons.2 ⟨sub7_399, List.forall_mem_cons.2 ⟨sub7_400, List.forall_mem_cons.2 ⟨sub7_401, List.forall_mem_cons.2 ⟨sub7_402, List.forall_mem_cons.2 ⟨sub7_403, List.forall_mem_cons.2 ⟨sub7_404, List.forall_mem_cons.2 ⟨sub7_405, List.forall_mem_cons.2 ⟨sub7_406, List.forall_mem_cons.2 ⟨sub7_407, List.forall_mem_cons.2 ⟨sub7_408, List.forall_mem_cons.2 ⟨sub7_409, List.forall_mem_cons.2 ⟨sub7_410, List.forall_mem_cons.2 ⟨sub7_411, List.forall_mem_cons.2 ⟨sub7_412, List.forall_mem_cons.2 ⟨sub7_413, List.forall_mem_cons.2 ⟨sub7_414, List.forall_mem_cons.2 ⟨sub7_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_416 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_417 : sub7 [4, -2] = true := by decide +kernel
theorem sub7_418 : sub7 [4, -1] = true := by decide +kernel
theorem sub7_419 : sub7 [4, 0] = true := by decide +kernel
theorem sub7_420 : sub7 [4, 1] = true := by decide +kernel
theorem sub7_421 : sub7 [4, 2] = true := by decide +kernel
theorem sub7_422 : sub7 [4, 3] = true := by decide +kernel
theorem sub7_423 : sub7 [4, 4] = true := by decide +kernel
theorem sub7_424 : sub7 [4, 5] = true := by decide +kernel
theorem sub7_425 : sub7 [5, -7] = true := by decide +kernel
theorem sub7_426 : sub7 [5, -6] = true := by decide +kernel
theorem sub7_427 : sub7 [5, -5] = true := by decide +kernel
theorem sub7_428 : sub7 [5, -4] = true := by decide +kernel
theorem sub7_429 : sub7 [5, -3] = true := by decide +kernel
theorem sub7_430 : sub7 [5, -2] = true := by decide +kernel
theorem sub7_431 : sub7 [5, -1] = true := by decide +kernel
theorem sub7_432 : sub7 [5, 0] = true := by decide +kernel
theorem sub7_433 : sub7 [5, 1] = true := by decide +kernel
theorem sub7_434 : sub7 [5, 2] = true := by decide +kernel
theorem sub7_435 : sub7 [5, 3] = true := by decide +kernel
theorem sub7_436 : sub7 [6, -5] = true := by decide +kernel
theorem sub7_437 : sub7 [6, -4] = true := by decide +kernel
theorem sub7_438 : sub7 [6, -3] = true := by decide +kernel
theorem sub7_439 : sub7 [6, -2] = true := by decide +kernel
theorem sub7_440 : sub7 [6, -1] = true := by decide +kernel
theorem sub7_441 : sub7 [6, 0] = true := by decide +kernel
theorem sub7_442 : sub7 [6, 1] = true := by decide +kernel
theorem sb7_13 : ∀ q ∈ blk7_13, sub7 q = true := by
  unfold blk7_13
  exact List.forall_mem_cons.2 ⟨sub7_416, List.forall_mem_cons.2 ⟨sub7_417, List.forall_mem_cons.2 ⟨sub7_418, List.forall_mem_cons.2 ⟨sub7_419, List.forall_mem_cons.2 ⟨sub7_420, List.forall_mem_cons.2 ⟨sub7_421, List.forall_mem_cons.2 ⟨sub7_422, List.forall_mem_cons.2 ⟨sub7_423, List.forall_mem_cons.2 ⟨sub7_424, List.forall_mem_cons.2 ⟨sub7_425, List.forall_mem_cons.2 ⟨sub7_426, List.forall_mem_cons.2 ⟨sub7_427, List.forall_mem_cons.2 ⟨sub7_428, List.forall_mem_cons.2 ⟨sub7_429, List.forall_mem_cons.2 ⟨sub7_430, List.forall_mem_cons.2 ⟨sub7_431, List.forall_mem_cons.2 ⟨sub7_432, List.forall_mem_cons.2 ⟨sub7_433, List.forall_mem_cons.2 ⟨sub7_434, List.forall_mem_cons.2 ⟨sub7_435, List.forall_mem_cons.2 ⟨sub7_436, List.forall_mem_cons.2 ⟨sub7_437, List.forall_mem_cons.2 ⟨sub7_438, List.forall_mem_cons.2 ⟨sub7_439, List.forall_mem_cons.2 ⟨sub7_440, List.forall_mem_cons.2 ⟨sub7_441, List.forall_mem_cons.2 ⟨sub7_442, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_0 : sub8 [-5] = true := by decide +kernel
theorem sub8_1 : sub8 [-4, -3] = true := by decide +kernel
theorem sub8_2 : sub8 [-4, -2] = true := by decide +kernel
theorem sub8_3 : sub8 [-4, -1] = true := by decide +kernel
theorem sub8_4 : sub8 [-4, 0] = true := by decide +kernel
theorem sub8_5 : sub8 [-4, 1] = true := by decide +kernel
theorem sub8_6 : sub8 [-4, 2] = true := by decide +kernel
theorem sub8_7 : sub8 [-4, 3] = true := by decide +kernel
theorem sub8_8 : sub8 [-4, 4] = true := by decide +kernel
theorem sub8_9 : sub8 [-3, -4] = true := by decide +kernel
theorem sub8_10 : sub8 [-3, -3] = true := by decide +kernel
theorem sub8_11 : sub8 [-3, -2] = true := by decide +kernel
theorem sub8_12 : sub8 [-3, -1] = true := by decide +kernel
theorem sub8_13 : sub8 [-3, 0] = true := by decide +kernel
theorem sub8_14 : sub8 [-3, 1] = true := by decide +kernel
theorem sub8_15 : sub8 [-3, 2] = true := by decide +kernel
theorem sub8_16 : sub8 [-3, 3] = true := by decide +kernel
theorem sub8_17 : sub8 [-3, 4] = true := by decide +kernel
theorem sub8_18 : sub8 [-2, -5] = true := by decide +kernel
theorem sub8_19 : sub8 [-2, -4] = true := by decide +kernel
theorem sub8_20 : sub8 [-2, -3] = true := by decide +kernel
theorem sub8_21 : sub8 [-2, -2] = true := by decide +kernel
theorem sub8_22 : sub8 [-2, -1] = true := by decide +kernel
theorem sub8_23 : sub8 [-2, 0] = true := by decide +kernel
theorem sub8_24 : sub8 [-2, 1] = true := by decide +kernel
theorem sub8_25 : sub8 [-2, 2] = true := by decide +kernel
theorem sub8_26 : sub8 [-2, 3] = true := by decide +kernel
theorem sub8_27 : sub8 [-2, 4] = true := by decide +kernel
theorem sub8_28 : sub8 [-1, -5] = true := by decide +kernel
theorem sub8_29 : sub8 [-1, -4] = true := by decide +kernel
theorem sub8_30 : sub8 [-1, -3] = true := by decide +kernel
theorem sub8_31 : sub8 [-1, -2] = true := by decide +kernel
theorem sb8_0 : ∀ q ∈ blk8_0, sub8 q = true := by
  unfold blk8_0
  exact List.forall_mem_cons.2 ⟨sub8_0, List.forall_mem_cons.2 ⟨sub8_1, List.forall_mem_cons.2 ⟨sub8_2, List.forall_mem_cons.2 ⟨sub8_3, List.forall_mem_cons.2 ⟨sub8_4, List.forall_mem_cons.2 ⟨sub8_5, List.forall_mem_cons.2 ⟨sub8_6, List.forall_mem_cons.2 ⟨sub8_7, List.forall_mem_cons.2 ⟨sub8_8, List.forall_mem_cons.2 ⟨sub8_9, List.forall_mem_cons.2 ⟨sub8_10, List.forall_mem_cons.2 ⟨sub8_11, List.forall_mem_cons.2 ⟨sub8_12, List.forall_mem_cons.2 ⟨sub8_13, List.forall_mem_cons.2 ⟨sub8_14, List.forall_mem_cons.2 ⟨sub8_15, List.forall_mem_cons.2 ⟨sub8_16, List.forall_mem_cons.2 ⟨sub8_17, List.forall_mem_cons.2 ⟨sub8_18, List.forall_mem_cons.2 ⟨sub8_19, List.forall_mem_cons.2 ⟨sub8_20, List.forall_mem_cons.2 ⟨sub8_21, List.forall_mem_cons.2 ⟨sub8_22, List.forall_mem_cons.2 ⟨sub8_23, List.forall_mem_cons.2 ⟨sub8_24, List.forall_mem_cons.2 ⟨sub8_25, List.forall_mem_cons.2 ⟨sub8_26, List.forall_mem_cons.2 ⟨sub8_27, List.forall_mem_cons.2 ⟨sub8_28, List.forall_mem_cons.2 ⟨sub8_29, List.forall_mem_cons.2 ⟨sub8_30, List.forall_mem_cons.2 ⟨sub8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C079
