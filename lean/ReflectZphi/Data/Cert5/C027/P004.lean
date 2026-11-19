import ReflectZphi.Data.Cert5.C027.Base

namespace ReflectZphi.Data.Cert5.C027
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_352 : sub4 [1, 1, -5] = true := by decide +kernel
theorem sub4_353 : sub4 [1, 1, -4] = true := by decide +kernel
theorem sub4_354 : sub4 [1, 1, -3] = true := by decide +kernel
theorem sub4_355 : sub4 [1, 1, -2] = true := by decide +kernel
theorem sub4_356 : sub4 [1, 1, -1] = true := by decide +kernel
theorem sub4_357 : sub4 [1, 1, 0] = true := by decide +kernel
theorem sub4_358 : sub4 [1, 1, 1] = true := by decide +kernel
theorem sub4_359 : sub4 [1, 1, 2] = true := by decide +kernel
theorem sub4_360 : sub4 [1, 1, 3] = true := by decide +kernel
theorem sub4_361 : sub4 [1, 1, 4] = true := by decide +kernel
theorem sub4_362 : sub4 [1, 1, 5] = true := by decide +kernel
theorem sub4_363 : sub4 [1, 1, 6] = true := by decide +kernel
theorem sub4_364 : sub4 [1, 1, 7] = true := by decide +kernel
theorem sub4_365 : sub4 [1, 2, -6] = true := by decide +kernel
theorem sub4_366 : sub4 [1, 2, -5] = true := by decide +kernel
theorem sub4_367 : sub4 [1, 2, -4] = true := by decide +kernel
theorem sub4_368 : sub4 [1, 2, -3] = true := by decide +kernel
theorem sub4_369 : sub4 [1, 2, -2] = true := by decide +kernel
theorem sub4_370 : sub4 [1, 2, -1] = true := by decide +kernel
theorem sub4_371 : sub4 [1, 2, 0] = true := by decide +kernel
theorem sub4_372 : sub4 [1, 2, 1] = true := by decide +kernel
theorem sub4_373 : sub4 [1, 2, 2] = true := by decide +kernel
theorem sub4_374 : sub4 [1, 2, 3] = true := by decide +kernel
theorem sub4_375 : sub4 [1, 2, 4] = true := by decide +kernel
theorem sub4_376 : sub4 [1, 2, 5] = true := by decide +kernel
theorem sub4_377 : sub4 [1, 2, 6] = true := by decide +kernel
theorem sub4_378 : sub4 [1, 2, 7] = true := by decide +kernel
theorem sub4_379 : sub4 [1, 3] = true := by decide +kernel
theorem sub4_380 : sub4 [1, 4] = true := by decide +kernel
theorem sub4_381 : sub4 [1, 5] = true := by decide +kernel
theorem sub4_382 : sub4 [2, -7] = true := by decide +kernel
theorem sub4_383 : sub4 [2, -6] = true := by decide +kernel
theorem sb4_11 : ∀ q ∈ blk4_11, sub4 q = true := by
  unfold blk4_11
  exact List.forall_mem_cons.2 ⟨sub4_352, List.forall_mem_cons.2 ⟨sub4_353, List.forall_mem_cons.2 ⟨sub4_354, List.forall_mem_cons.2 ⟨sub4_355, List.forall_mem_cons.2 ⟨sub4_356, List.forall_mem_cons.2 ⟨sub4_357, List.forall_mem_cons.2 ⟨sub4_358, List.forall_mem_cons.2 ⟨sub4_359, List.forall_mem_cons.2 ⟨sub4_360, List.forall_mem_cons.2 ⟨sub4_361, List.forall_mem_cons.2 ⟨sub4_362, List.forall_mem_cons.2 ⟨sub4_363, List.forall_mem_cons.2 ⟨sub4_364, List.forall_mem_cons.2 ⟨sub4_365, List.forall_mem_cons.2 ⟨sub4_366, List.forall_mem_cons.2 ⟨sub4_367, List.forall_mem_cons.2 ⟨sub4_368, List.forall_mem_cons.2 ⟨sub4_369, List.forall_mem_cons.2 ⟨sub4_370, List.forall_mem_cons.2 ⟨sub4_371, List.forall_mem_cons.2 ⟨sub4_372, List.forall_mem_cons.2 ⟨sub4_373, List.forall_mem_cons.2 ⟨sub4_374, List.forall_mem_cons.2 ⟨sub4_375, List.forall_mem_cons.2 ⟨sub4_376, List.forall_mem_cons.2 ⟨sub4_377, List.forall_mem_cons.2 ⟨sub4_378, List.forall_mem_cons.2 ⟨sub4_379, List.forall_mem_cons.2 ⟨sub4_380, List.forall_mem_cons.2 ⟨sub4_381, List.forall_mem_cons.2 ⟨sub4_382, List.forall_mem_cons.2 ⟨sub4_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_384 : sub4 [2, -5] = true := by decide +kernel
theorem sub4_385 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_386 : sub4 [2, -3] = true := by decide +kernel
theorem sub4_387 : sub4 [2, -2, -7] = true := by decide +kernel
theorem sub4_388 : sub4 [2, -2, -6] = true := by decide +kernel
theorem sub4_389 : sub4 [2, -2, -5] = true := by decide +kernel
theorem sub4_390 : sub4 [2, -2, -4] = true := by decide +kernel
theorem sub4_391 : sub4 [2, -2, -3] = true := by decide +kernel
theorem sub4_392 : sub4 [2, -2, -2] = true := by decide +kernel
theorem sub4_393 : sub4 [2, -2, -1] = true := by decide +kernel
theorem sub4_394 : sub4 [2, -2, 0] = true := by decide +kernel
theorem sub4_395 : sub4 [2, -2, 1] = true := by decide +kernel
theorem sub4_396 : sub4 [2, -2, 2] = true := by decide +kernel
theorem sub4_397 : sub4 [2, -2, 3] = true := by decide +kernel
theorem sub4_398 : sub4 [2, -2, 4] = true := by decide +kernel
theorem sub4_399 : sub4 [2, -2, 5] = true := by decide +kernel
theorem sub4_400 : sub4 [2, -2, 6] = true := by decide +kernel
theorem sub4_401 : sub4 [2, -1, -7] = true := by decide +kernel
theorem sub4_402 : sub4 [2, -1, -6] = true := by decide +kernel
theorem sub4_403 : sub4 [2, -1, -5] = true := by decide +kernel
theorem sub4_404 : sub4 [2, -1, -4] = true := by decide +kernel
theorem sub4_405 : sub4 [2, -1, -3] = true := by decide +kernel
theorem sub4_406 : sub4 [2, -1, -2] = true := by decide +kernel
theorem sub4_407 : sub4 [2, -1, -1] = true := by decide +kernel
theorem sub4_408 : sub4 [2, -1, 0] = true := by decide +kernel
theorem sub4_409 : sub4 [2, -1, 1] = true := by decide +kernel
theorem sub4_410 : sub4 [2, -1, 2] = true := by decide +kernel
theorem sub4_411 : sub4 [2, -1, 3] = true := by decide +kernel
theorem sub4_412 : sub4 [2, -1, 4] = true := by decide +kernel
theorem sub4_413 : sub4 [2, -1, 5] = true := by decide +kernel
theorem sub4_414 : sub4 [2, -1, 6] = true := by decide +kernel
theorem sub4_415 : sub4 [2, 0, -6] = true := by decide +kernel
theorem sb4_12 : ∀ q ∈ blk4_12, sub4 q = true := by
  unfold blk4_12
  exact List.forall_mem_cons.2 ⟨sub4_384, List.forall_mem_cons.2 ⟨sub4_385, List.forall_mem_cons.2 ⟨sub4_386, List.forall_mem_cons.2 ⟨sub4_387, List.forall_mem_cons.2 ⟨sub4_388, List.forall_mem_cons.2 ⟨sub4_389, List.forall_mem_cons.2 ⟨sub4_390, List.forall_mem_cons.2 ⟨sub4_391, List.forall_mem_cons.2 ⟨sub4_392, List.forall_mem_cons.2 ⟨sub4_393, List.forall_mem_cons.2 ⟨sub4_394, List.forall_mem_cons.2 ⟨sub4_395, List.forall_mem_cons.2 ⟨sub4_396, List.forall_mem_cons.2 ⟨sub4_397, List.forall_mem_cons.2 ⟨sub4_398, List.forall_mem_cons.2 ⟨sub4_399, List.forall_mem_cons.2 ⟨sub4_400, List.forall_mem_cons.2 ⟨sub4_401, List.forall_mem_cons.2 ⟨sub4_402, List.forall_mem_cons.2 ⟨sub4_403, List.forall_mem_cons.2 ⟨sub4_404, List.forall_mem_cons.2 ⟨sub4_405, List.forall_mem_cons.2 ⟨sub4_406, List.forall_mem_cons.2 ⟨sub4_407, List.forall_mem_cons.2 ⟨sub4_408, List.forall_mem_cons.2 ⟨sub4_409, List.forall_mem_cons.2 ⟨sub4_410, List.forall_mem_cons.2 ⟨sub4_411, List.forall_mem_cons.2 ⟨sub4_412, List.forall_mem_cons.2 ⟨sub4_413, List.forall_mem_cons.2 ⟨sub4_414, List.forall_mem_cons.2 ⟨sub4_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_416 : sub4 [2, 0, -5] = true := by decide +kernel
theorem sub4_417 : sub4 [2, 0, -4] = true := by decide +kernel
theorem sub4_418 : sub4 [2, 0, -3] = true := by decide +kernel
theorem sub4_419 : sub4 [2, 0, -2] = true := by decide +kernel
theorem sub4_420 : sub4 [2, 0, -1] = true := by decide +kernel
theorem sub4_421 : sub4 [2, 0, 0] = true := by decide +kernel
theorem sub4_422 : sub4 [2, 0, 1] = true := by decide +kernel
theorem sub4_423 : sub4 [2, 0, 2] = true := by decide +kernel
theorem sub4_424 : sub4 [2, 0, 3] = true := by decide +kernel
theorem sub4_425 : sub4 [2, 0, 4] = true := by decide +kernel
theorem sub4_426 : sub4 [2, 0, 5] = true := by decide +kernel
theorem sub4_427 : sub4 [2, 0, 6] = true := by decide +kernel
theorem sub4_428 : sub4 [2, 0, 7] = true := by decide +kernel
theorem sub4_429 : sub4 [2, 1, -6] = true := by decide +kernel
theorem sub4_430 : sub4 [2, 1, -5] = true := by decide +kernel
theorem sub4_431 : sub4 [2, 1, -4] = true := by decide +kernel
theorem sub4_432 : sub4 [2, 1, -3] = true := by decide +kernel
theorem sub4_433 : sub4 [2, 1, -2] = true := by decide +kernel
theorem sub4_434 : sub4 [2, 1, -1] = true := by decide +kernel
theorem sub4_435 : sub4 [2, 1, 0] = true := by decide +kernel
theorem sub4_436 : sub4 [2, 1, 1] = true := by decide +kernel
theorem sub4_437 : sub4 [2, 1, 2] = true := by decide +kernel
theorem sub4_438 : sub4 [2, 1, 3] = true := by decide +kernel
theorem sub4_439 : sub4 [2, 1, 4] = true := by decide +kernel
theorem sub4_440 : sub4 [2, 1, 5] = true := by decide +kernel
theorem sub4_441 : sub4 [2, 1, 6] = true := by decide +kernel
theorem sub4_442 : sub4 [2, 1, 7] = true := by decide +kernel
theorem sub4_443 : sub4 [2, 2] = true := by decide +kernel
theorem sub4_444 : sub4 [2, 3] = true := by decide +kernel
theorem sub4_445 : sub4 [2, 4] = true := by decide +kernel
theorem sub4_446 : sub4 [3, -7] = true := by decide +kernel
theorem sub4_447 : sub4 [3, -6] = true := by decide +kernel
theorem sb4_13 : ∀ q ∈ blk4_13, sub4 q = true := by
  unfold blk4_13
  exact List.forall_mem_cons.2 ⟨sub4_416, List.forall_mem_cons.2 ⟨sub4_417, List.forall_mem_cons.2 ⟨sub4_418, List.forall_mem_cons.2 ⟨sub4_419, List.forall_mem_cons.2 ⟨sub4_420, List.forall_mem_cons.2 ⟨sub4_421, List.forall_mem_cons.2 ⟨sub4_422, List.forall_mem_cons.2 ⟨sub4_423, List.forall_mem_cons.2 ⟨sub4_424, List.forall_mem_cons.2 ⟨sub4_425, List.forall_mem_cons.2 ⟨sub4_426, List.forall_mem_cons.2 ⟨sub4_427, List.forall_mem_cons.2 ⟨sub4_428, List.forall_mem_cons.2 ⟨sub4_429, List.forall_mem_cons.2 ⟨sub4_430, List.forall_mem_cons.2 ⟨sub4_431, List.forall_mem_cons.2 ⟨sub4_432, List.forall_mem_cons.2 ⟨sub4_433, List.forall_mem_cons.2 ⟨sub4_434, List.forall_mem_cons.2 ⟨sub4_435, List.forall_mem_cons.2 ⟨sub4_436, List.forall_mem_cons.2 ⟨sub4_437, List.forall_mem_cons.2 ⟨sub4_438, List.forall_mem_cons.2 ⟨sub4_439, List.forall_mem_cons.2 ⟨sub4_440, List.forall_mem_cons.2 ⟨sub4_441, List.forall_mem_cons.2 ⟨sub4_442, List.forall_mem_cons.2 ⟨sub4_443, List.forall_mem_cons.2 ⟨sub4_444, List.forall_mem_cons.2 ⟨sub4_445, List.forall_mem_cons.2 ⟨sub4_446, List.forall_mem_cons.2 ⟨sub4_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_448 : sub4 [3, -5] = true := by decide +kernel
theorem sub4_449 : sub4 [3, -4] = true := by decide +kernel
theorem sub4_450 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_451 : sub4 [3, -2] = true := by decide +kernel
theorem sub4_452 : sub4 [3, -1] = true := by decide +kernel
theorem sub4_453 : sub4 [3, 0] = true := by decide +kernel
theorem sub4_454 : sub4 [3, 1] = true := by decide +kernel
theorem sub4_455 : sub4 [3, 2] = true := by decide +kernel
theorem sub4_456 : sub4 [3, 3] = true := by decide +kernel
theorem sub4_457 : sub4 [4, -6] = true := by decide +kernel
theorem sub4_458 : sub4 [4, -5] = true := by decide +kernel
theorem sub4_459 : sub4 [4, -4] = true := by decide +kernel
theorem sub4_460 : sub4 [4, -3] = true := by decide +kernel
theorem sub4_461 : sub4 [4, -2] = true := by decide +kernel
theorem sub4_462 : sub4 [4, -1] = true := by decide +kernel
theorem sub4_463 : sub4 [4, 0] = true := by decide +kernel
theorem sub4_464 : sub4 [4, 1] = true := by decide +kernel
theorem sub4_465 : sub4 [4, 2] = true := by decide +kernel
theorem sub4_466 : sub4 [5] = true := by decide +kernel
theorem sb4_14 : ∀ q ∈ blk4_14, sub4 q = true := by
  unfold blk4_14
  exact List.forall_mem_cons.2 ⟨sub4_448, List.forall_mem_cons.2 ⟨sub4_449, List.forall_mem_cons.2 ⟨sub4_450, List.forall_mem_cons.2 ⟨sub4_451, List.forall_mem_cons.2 ⟨sub4_452, List.forall_mem_cons.2 ⟨sub4_453, List.forall_mem_cons.2 ⟨sub4_454, List.forall_mem_cons.2 ⟨sub4_455, List.forall_mem_cons.2 ⟨sub4_456, List.forall_mem_cons.2 ⟨sub4_457, List.forall_mem_cons.2 ⟨sub4_458, List.forall_mem_cons.2 ⟨sub4_459, List.forall_mem_cons.2 ⟨sub4_460, List.forall_mem_cons.2 ⟨sub4_461, List.forall_mem_cons.2 ⟨sub4_462, List.forall_mem_cons.2 ⟨sub4_463, List.forall_mem_cons.2 ⟨sub4_464, List.forall_mem_cons.2 ⟨sub4_465, List.forall_mem_cons.2 ⟨sub4_466, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_0 : sub5 [-7] = true := by decide +kernel
theorem sub5_1 : sub5 [-6, -3] = true := by decide +kernel
theorem sub5_2 : sub5 [-6, -2] = true := by decide +kernel
theorem sub5_3 : sub5 [-6, -1] = true := by decide +kernel
theorem sub5_4 : sub5 [-6, 0] = true := by decide +kernel
theorem sub5_5 : sub5 [-6, 1] = true := by decide +kernel
theorem sub5_6 : sub5 [-6, 2] = true := by decide +kernel
theorem sub5_7 : sub5 [-6, 3] = true := by decide +kernel
theorem sub5_8 : sub5 [-6, 4] = true := by decide +kernel
theorem sub5_9 : sub5 [-5, -5] = true := by decide +kernel
theorem sub5_10 : sub5 [-5, -4] = true := by decide +kernel
theorem sub5_11 : sub5 [-5, -3] = true := by decide +kernel
theorem sub5_12 : sub5 [-5, -2] = true := by decide +kernel
theorem sub5_13 : sub5 [-5, -1] = true := by decide +kernel
theorem sub5_14 : sub5 [-5, 0] = true := by decide +kernel
theorem sub5_15 : sub5 [-5, 1] = true := by decide +kernel
theorem sub5_16 : sub5 [-5, 2] = true := by decide +kernel
theorem sub5_17 : sub5 [-5, 3] = true := by decide +kernel
theorem sub5_18 : sub5 [-5, 4] = true := by decide +kernel
theorem sub5_19 : sub5 [-5, 5] = true := by decide +kernel
theorem sub5_20 : sub5 [-4, -5] = true := by decide +kernel
theorem sub5_21 : sub5 [-4, -4] = true := by decide +kernel
theorem sub5_22 : sub5 [-4, -3] = true := by decide +kernel
theorem sub5_23 : sub5 [-4, -2] = true := by decide +kernel
theorem sub5_24 : sub5 [-4, -1] = true := by decide +kernel
theorem sub5_25 : sub5 [-4, 0] = true := by decide +kernel
theorem sub5_26 : sub5 [-4, 1] = true := by decide +kernel
theorem sub5_27 : sub5 [-4, 2] = true := by decide +kernel
theorem sub5_28 : sub5 [-4, 3] = true := by decide +kernel
theorem sub5_29 : sub5 [-4, 4] = true := by decide +kernel
theorem sub5_30 : sub5 [-4, 5] = true := by decide +kernel
theorem sub5_31 : sub5 [-4, 6] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C027
