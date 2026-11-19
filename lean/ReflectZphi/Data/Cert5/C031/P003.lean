import ReflectZphi.Data.Cert5.C031.Base

namespace ReflectZphi.Data.Cert5.C031
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_384 : sub3 [1, 2, -5] = true := by decide +kernel
theorem sub3_385 : sub3 [1, 2, -4] = true := by decide +kernel
theorem sub3_386 : sub3 [1, 2, -3] = true := by decide +kernel
theorem sub3_387 : sub3 [1, 2, -2] = true := by decide +kernel
theorem sub3_388 : sub3 [1, 2, -1] = true := by decide +kernel
theorem sub3_389 : sub3 [1, 2, 0] = true := by decide +kernel
theorem sub3_390 : sub3 [1, 2, 1] = true := by decide +kernel
theorem sub3_391 : sub3 [1, 2, 2] = true := by decide +kernel
theorem sub3_392 : sub3 [1, 2, 3] = true := by decide +kernel
theorem sub3_393 : sub3 [1, 2, 4] = true := by decide +kernel
theorem sub3_394 : sub3 [1, 2, 5] = true := by decide +kernel
theorem sub3_395 : sub3 [1, 2, 6] = true := by decide +kernel
theorem sub3_396 : sub3 [1, 3] = true := by decide +kernel
theorem sub3_397 : sub3 [1, 4] = true := by decide +kernel
theorem sub3_398 : sub3 [1, 5] = true := by decide +kernel
theorem sub3_399 : sub3 [2, -7] = true := by decide +kernel
theorem sub3_400 : sub3 [2, -6] = true := by decide +kernel
theorem sub3_401 : sub3 [2, -5] = true := by decide +kernel
theorem sub3_402 : sub3 [2, -4] = true := by decide +kernel
theorem sub3_403 : sub3 [2, -3, -7] = true := by decide +kernel
theorem sub3_404 : sub3 [2, -3, -6] = true := by decide +kernel
theorem sub3_405 : sub3 [2, -3, -5] = true := by decide +kernel
theorem sub3_406 : sub3 [2, -3, -4] = true := by decide +kernel
theorem sub3_407 : sub3 [2, -3, -3] = true := by decide +kernel
theorem sub3_408 : sub3 [2, -3, -2] = true := by decide +kernel
theorem sub3_409 : sub3 [2, -3, -1] = true := by decide +kernel
theorem sub3_410 : sub3 [2, -3, 0] = true := by decide +kernel
theorem sub3_411 : sub3 [2, -3, 1] = true := by decide +kernel
theorem sub3_412 : sub3 [2, -3, 2] = true := by decide +kernel
theorem sub3_413 : sub3 [2, -3, 3] = true := by decide +kernel
theorem sub3_414 : sub3 [2, -3, 4] = true := by decide +kernel
theorem sub3_415 : sub3 [2, -3, 5] = true := by decide +kernel
theorem sb3_12 : ∀ q ∈ blk3_12, sub3 q = true := by
  unfold blk3_12
  exact List.forall_mem_cons.2 ⟨sub3_384, List.forall_mem_cons.2 ⟨sub3_385, List.forall_mem_cons.2 ⟨sub3_386, List.forall_mem_cons.2 ⟨sub3_387, List.forall_mem_cons.2 ⟨sub3_388, List.forall_mem_cons.2 ⟨sub3_389, List.forall_mem_cons.2 ⟨sub3_390, List.forall_mem_cons.2 ⟨sub3_391, List.forall_mem_cons.2 ⟨sub3_392, List.forall_mem_cons.2 ⟨sub3_393, List.forall_mem_cons.2 ⟨sub3_394, List.forall_mem_cons.2 ⟨sub3_395, List.forall_mem_cons.2 ⟨sub3_396, List.forall_mem_cons.2 ⟨sub3_397, List.forall_mem_cons.2 ⟨sub3_398, List.forall_mem_cons.2 ⟨sub3_399, List.forall_mem_cons.2 ⟨sub3_400, List.forall_mem_cons.2 ⟨sub3_401, List.forall_mem_cons.2 ⟨sub3_402, List.forall_mem_cons.2 ⟨sub3_403, List.forall_mem_cons.2 ⟨sub3_404, List.forall_mem_cons.2 ⟨sub3_405, List.forall_mem_cons.2 ⟨sub3_406, List.forall_mem_cons.2 ⟨sub3_407, List.forall_mem_cons.2 ⟨sub3_408, List.forall_mem_cons.2 ⟨sub3_409, List.forall_mem_cons.2 ⟨sub3_410, List.forall_mem_cons.2 ⟨sub3_411, List.forall_mem_cons.2 ⟨sub3_412, List.forall_mem_cons.2 ⟨sub3_413, List.forall_mem_cons.2 ⟨sub3_414, List.forall_mem_cons.2 ⟨sub3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_416 : sub3 [2, -2, -8] = true := by decide +kernel
theorem sub3_417 : sub3 [2, -2, -7] = true := by decide +kernel
theorem sub3_418 : sub3 [2, -2, -6] = true := by decide +kernel
theorem sub3_419 : sub3 [2, -2, -5] = true := by decide +kernel
theorem sub3_420 : sub3 [2, -2, -4] = true := by decide +kernel
theorem sub3_421 : sub3 [2, -2, -3] = true := by decide +kernel
theorem sub3_422 : sub3 [2, -2, -2] = true := by decide +kernel
theorem sub3_423 : sub3 [2, -2, -1] = true := by decide +kernel
theorem sub3_424 : sub3 [2, -2, 0] = true := by decide +kernel
theorem sub3_425 : sub3 [2, -2, 1] = true := by decide +kernel
theorem sub3_426 : sub3 [2, -2, 2] = true := by decide +kernel
theorem sub3_427 : sub3 [2, -2, 3] = true := by decide +kernel
theorem sub3_428 : sub3 [2, -2, 4] = true := by decide +kernel
theorem sub3_429 : sub3 [2, -2, 5] = true := by decide +kernel
theorem sub3_430 : sub3 [2, -2, 6] = true := by decide +kernel
theorem sub3_431 : sub3 [2, -1, -8] = true := by decide +kernel
theorem sub3_432 : sub3 [2, -1, -7] = true := by decide +kernel
theorem sub3_433 : sub3 [2, -1, -6] = true := by decide +kernel
theorem sub3_434 : sub3 [2, -1, -5] = true := by decide +kernel
theorem sub3_435 : sub3 [2, -1, -4] = true := by decide +kernel
theorem sub3_436 : sub3 [2, -1, -3] = true := by decide +kernel
theorem sub3_437 : sub3 [2, -1, -2] = true := by decide +kernel
theorem sub3_438 : sub3 [2, -1, -1] = true := by decide +kernel
theorem sub3_439 : sub3 [2, -1, 0] = true := by decide +kernel
theorem sub3_440 : sub3 [2, -1, 1] = true := by decide +kernel
theorem sub3_441 : sub3 [2, -1, 2] = true := by decide +kernel
theorem sub3_442 : sub3 [2, -1, 3] = true := by decide +kernel
theorem sub3_443 : sub3 [2, -1, 4] = true := by decide +kernel
theorem sub3_444 : sub3 [2, -1, 5] = true := by decide +kernel
theorem sub3_445 : sub3 [2, -1, 6] = true := by decide +kernel
theorem sub3_446 : sub3 [2, 0, -8] = true := by decide +kernel
theorem sub3_447 : sub3 [2, 0, -7] = true := by decide +kernel
theorem sb3_13 : ∀ q ∈ blk3_13, sub3 q = true := by
  unfold blk3_13
  exact List.forall_mem_cons.2 ⟨sub3_416, List.forall_mem_cons.2 ⟨sub3_417, List.forall_mem_cons.2 ⟨sub3_418, List.forall_mem_cons.2 ⟨sub3_419, List.forall_mem_cons.2 ⟨sub3_420, List.forall_mem_cons.2 ⟨sub3_421, List.forall_mem_cons.2 ⟨sub3_422, List.forall_mem_cons.2 ⟨sub3_423, List.forall_mem_cons.2 ⟨sub3_424, List.forall_mem_cons.2 ⟨sub3_425, List.forall_mem_cons.2 ⟨sub3_426, List.forall_mem_cons.2 ⟨sub3_427, List.forall_mem_cons.2 ⟨sub3_428, List.forall_mem_cons.2 ⟨sub3_429, List.forall_mem_cons.2 ⟨sub3_430, List.forall_mem_cons.2 ⟨sub3_431, List.forall_mem_cons.2 ⟨sub3_432, List.forall_mem_cons.2 ⟨sub3_433, List.forall_mem_cons.2 ⟨sub3_434, List.forall_mem_cons.2 ⟨sub3_435, List.forall_mem_cons.2 ⟨sub3_436, List.forall_mem_cons.2 ⟨sub3_437, List.forall_mem_cons.2 ⟨sub3_438, List.forall_mem_cons.2 ⟨sub3_439, List.forall_mem_cons.2 ⟨sub3_440, List.forall_mem_cons.2 ⟨sub3_441, List.forall_mem_cons.2 ⟨sub3_442, List.forall_mem_cons.2 ⟨sub3_443, List.forall_mem_cons.2 ⟨sub3_444, List.forall_mem_cons.2 ⟨sub3_445, List.forall_mem_cons.2 ⟨sub3_446, List.forall_mem_cons.2 ⟨sub3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_448 : sub3 [2, 0, -6] = true := by decide +kernel
theorem sub3_449 : sub3 [2, 0, -5] = true := by decide +kernel
theorem sub3_450 : sub3 [2, 0, -4] = true := by decide +kernel
theorem sub3_451 : sub3 [2, 0, -3] = true := by decide +kernel
theorem sub3_452 : sub3 [2, 0, -2] = true := by decide +kernel
theorem sub3_453 : sub3 [2, 0, -1] = true := by decide +kernel
theorem sub3_454 : sub3 [2, 0, 0] = true := by decide +kernel
theorem sub3_455 : sub3 [2, 0, 1] = true := by decide +kernel
theorem sub3_456 : sub3 [2, 0, 2] = true := by decide +kernel
theorem sub3_457 : sub3 [2, 0, 3] = true := by decide +kernel
theorem sub3_458 : sub3 [2, 0, 4] = true := by decide +kernel
theorem sub3_459 : sub3 [2, 0, 5] = true := by decide +kernel
theorem sub3_460 : sub3 [2, 0, 6] = true := by decide +kernel
theorem sub3_461 : sub3 [2, 1, -7] = true := by decide +kernel
theorem sub3_462 : sub3 [2, 1, -6] = true := by decide +kernel
theorem sub3_463 : sub3 [2, 1, -5] = true := by decide +kernel
theorem sub3_464 : sub3 [2, 1, -4] = true := by decide +kernel
theorem sub3_465 : sub3 [2, 1, -3] = true := by decide +kernel
theorem sub3_466 : sub3 [2, 1, -2] = true := by decide +kernel
theorem sub3_467 : sub3 [2, 1, -1] = true := by decide +kernel
theorem sub3_468 : sub3 [2, 1, 0] = true := by decide +kernel
theorem sub3_469 : sub3 [2, 1, 1] = true := by decide +kernel
theorem sub3_470 : sub3 [2, 1, 2] = true := by decide +kernel
theorem sub3_471 : sub3 [2, 1, 3] = true := by decide +kernel
theorem sub3_472 : sub3 [2, 1, 4] = true := by decide +kernel
theorem sub3_473 : sub3 [2, 1, 5] = true := by decide +kernel
theorem sub3_474 : sub3 [2, 1, 6] = true := by decide +kernel
theorem sub3_475 : sub3 [2, 2] = true := by decide +kernel
theorem sub3_476 : sub3 [2, 3] = true := by decide +kernel
theorem sub3_477 : sub3 [2, 4] = true := by decide +kernel
theorem sub3_478 : sub3 [3, -7] = true := by decide +kernel
theorem sub3_479 : sub3 [3, -6] = true := by decide +kernel
theorem sb3_14 : ∀ q ∈ blk3_14, sub3 q = true := by
  unfold blk3_14
  exact List.forall_mem_cons.2 ⟨sub3_448, List.forall_mem_cons.2 ⟨sub3_449, List.forall_mem_cons.2 ⟨sub3_450, List.forall_mem_cons.2 ⟨sub3_451, List.forall_mem_cons.2 ⟨sub3_452, List.forall_mem_cons.2 ⟨sub3_453, List.forall_mem_cons.2 ⟨sub3_454, List.forall_mem_cons.2 ⟨sub3_455, List.forall_mem_cons.2 ⟨sub3_456, List.forall_mem_cons.2 ⟨sub3_457, List.forall_mem_cons.2 ⟨sub3_458, List.forall_mem_cons.2 ⟨sub3_459, List.forall_mem_cons.2 ⟨sub3_460, List.forall_mem_cons.2 ⟨sub3_461, List.forall_mem_cons.2 ⟨sub3_462, List.forall_mem_cons.2 ⟨sub3_463, List.forall_mem_cons.2 ⟨sub3_464, List.forall_mem_cons.2 ⟨sub3_465, List.forall_mem_cons.2 ⟨sub3_466, List.forall_mem_cons.2 ⟨sub3_467, List.forall_mem_cons.2 ⟨sub3_468, List.forall_mem_cons.2 ⟨sub3_469, List.forall_mem_cons.2 ⟨sub3_470, List.forall_mem_cons.2 ⟨sub3_471, List.forall_mem_cons.2 ⟨sub3_472, List.forall_mem_cons.2 ⟨sub3_473, List.forall_mem_cons.2 ⟨sub3_474, List.forall_mem_cons.2 ⟨sub3_475, List.forall_mem_cons.2 ⟨sub3_476, List.forall_mem_cons.2 ⟨sub3_477, List.forall_mem_cons.2 ⟨sub3_478, List.forall_mem_cons.2 ⟨sub3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_480 : sub3 [3, -5] = true := by decide +kernel
theorem sub3_481 : sub3 [3, -4] = true := by decide +kernel
theorem sub3_482 : sub3 [3, -3] = true := by decide +kernel
theorem sub3_483 : sub3 [3, -2] = true := by decide +kernel
theorem sub3_484 : sub3 [3, -1] = true := by decide +kernel
theorem sub3_485 : sub3 [3, 0] = true := by decide +kernel
theorem sub3_486 : sub3 [3, 1] = true := by decide +kernel
theorem sub3_487 : sub3 [3, 2] = true := by decide +kernel
theorem sub3_488 : sub3 [3, 3] = true := by decide +kernel
theorem sub3_489 : sub3 [4, -6] = true := by decide +kernel
theorem sub3_490 : sub3 [4, -5] = true := by decide +kernel
theorem sub3_491 : sub3 [4, -4] = true := by decide +kernel
theorem sub3_492 : sub3 [4, -3] = true := by decide +kernel
theorem sub3_493 : sub3 [4, -2] = true := by decide +kernel
theorem sub3_494 : sub3 [4, -1] = true := by decide +kernel
theorem sub3_495 : sub3 [4, 0] = true := by decide +kernel
theorem sub3_496 : sub3 [4, 1] = true := by decide +kernel
theorem sub3_497 : sub3 [4, 2] = true := by decide +kernel
theorem sub3_498 : sub3 [5] = true := by decide +kernel
theorem sb3_15 : ∀ q ∈ blk3_15, sub3 q = true := by
  unfold blk3_15
  exact List.forall_mem_cons.2 ⟨sub3_480, List.forall_mem_cons.2 ⟨sub3_481, List.forall_mem_cons.2 ⟨sub3_482, List.forall_mem_cons.2 ⟨sub3_483, List.forall_mem_cons.2 ⟨sub3_484, List.forall_mem_cons.2 ⟨sub3_485, List.forall_mem_cons.2 ⟨sub3_486, List.forall_mem_cons.2 ⟨sub3_487, List.forall_mem_cons.2 ⟨sub3_488, List.forall_mem_cons.2 ⟨sub3_489, List.forall_mem_cons.2 ⟨sub3_490, List.forall_mem_cons.2 ⟨sub3_491, List.forall_mem_cons.2 ⟨sub3_492, List.forall_mem_cons.2 ⟨sub3_493, List.forall_mem_cons.2 ⟨sub3_494, List.forall_mem_cons.2 ⟨sub3_495, List.forall_mem_cons.2 ⟨sub3_496, List.forall_mem_cons.2 ⟨sub3_497, List.forall_mem_cons.2 ⟨sub3_498, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_0 : sub4 [-6] = true := by decide +kernel
theorem sub4_1 : sub4 [-5, -5] = true := by decide +kernel
theorem sub4_2 : sub4 [-5, -4] = true := by decide +kernel
theorem sub4_3 : sub4 [-5, -3] = true := by decide +kernel
theorem sub4_4 : sub4 [-5, -2] = true := by decide +kernel
theorem sub4_5 : sub4 [-5, -1] = true := by decide +kernel
theorem sub4_6 : sub4 [-5, 0] = true := by decide +kernel
theorem sub4_7 : sub4 [-5, 1] = true := by decide +kernel
theorem sub4_8 : sub4 [-5, 2] = true := by decide +kernel
theorem sub4_9 : sub4 [-4, -6] = true := by decide +kernel
theorem sub4_10 : sub4 [-4, -5] = true := by decide +kernel
theorem sub4_11 : sub4 [-4, -4] = true := by decide +kernel
theorem sub4_12 : sub4 [-4, -3] = true := by decide +kernel
theorem sub4_13 : sub4 [-4, -2] = true := by decide +kernel
theorem sub4_14 : sub4 [-4, -1] = true := by decide +kernel
theorem sub4_15 : sub4 [-4, 0] = true := by decide +kernel
theorem sub4_16 : sub4 [-4, 1] = true := by decide +kernel
theorem sub4_17 : sub4 [-4, 2] = true := by decide +kernel
theorem sub4_18 : sub4 [-4, 3] = true := by decide +kernel
theorem sub4_19 : sub4 [-4, 4] = true := by decide +kernel
theorem sub4_20 : sub4 [-3, -6] = true := by decide +kernel
theorem sub4_21 : sub4 [-3, -5] = true := by decide +kernel
theorem sub4_22 : sub4 [-3, -4] = true := by decide +kernel
theorem sub4_23 : sub4 [-3, -3] = true := by decide +kernel
theorem sub4_24 : sub4 [-3, -2] = true := by decide +kernel
theorem sub4_25 : sub4 [-3, -1] = true := by decide +kernel
theorem sub4_26 : sub4 [-3, 0] = true := by decide +kernel
theorem sub4_27 : sub4 [-3, 1] = true := by decide +kernel
theorem sub4_28 : sub4 [-3, 2] = true := by decide +kernel
theorem sub4_29 : sub4 [-3, 3] = true := by decide +kernel
theorem sub4_30 : sub4 [-3, 4] = true := by decide +kernel
theorem sub4_31 : sub4 [-2, -6] = true := by decide +kernel
theorem sb4_0 : ∀ q ∈ blk4_0, sub4 q = true := by
  unfold blk4_0
  exact List.forall_mem_cons.2 ⟨sub4_0, List.forall_mem_cons.2 ⟨sub4_1, List.forall_mem_cons.2 ⟨sub4_2, List.forall_mem_cons.2 ⟨sub4_3, List.forall_mem_cons.2 ⟨sub4_4, List.forall_mem_cons.2 ⟨sub4_5, List.forall_mem_cons.2 ⟨sub4_6, List.forall_mem_cons.2 ⟨sub4_7, List.forall_mem_cons.2 ⟨sub4_8, List.forall_mem_cons.2 ⟨sub4_9, List.forall_mem_cons.2 ⟨sub4_10, List.forall_mem_cons.2 ⟨sub4_11, List.forall_mem_cons.2 ⟨sub4_12, List.forall_mem_cons.2 ⟨sub4_13, List.forall_mem_cons.2 ⟨sub4_14, List.forall_mem_cons.2 ⟨sub4_15, List.forall_mem_cons.2 ⟨sub4_16, List.forall_mem_cons.2 ⟨sub4_17, List.forall_mem_cons.2 ⟨sub4_18, List.forall_mem_cons.2 ⟨sub4_19, List.forall_mem_cons.2 ⟨sub4_20, List.forall_mem_cons.2 ⟨sub4_21, List.forall_mem_cons.2 ⟨sub4_22, List.forall_mem_cons.2 ⟨sub4_23, List.forall_mem_cons.2 ⟨sub4_24, List.forall_mem_cons.2 ⟨sub4_25, List.forall_mem_cons.2 ⟨sub4_26, List.forall_mem_cons.2 ⟨sub4_27, List.forall_mem_cons.2 ⟨sub4_28, List.forall_mem_cons.2 ⟨sub4_29, List.forall_mem_cons.2 ⟨sub4_30, List.forall_mem_cons.2 ⟨sub4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_32 : sub4 [-2, -5] = true := by decide +kernel
theorem sub4_33 : sub4 [-2, -4] = true := by decide +kernel
theorem sub4_34 : sub4 [-2, -3] = true := by decide +kernel
theorem sub4_35 : sub4 [-2, -2, -7] = true := by decide +kernel
theorem sub4_36 : sub4 [-2, -2, -6] = true := by decide +kernel
theorem sub4_37 : sub4 [-2, -2, -5] = true := by decide +kernel
theorem sub4_38 : sub4 [-2, -2, -4] = true := by decide +kernel
theorem sub4_39 : sub4 [-2, -2, -3] = true := by decide +kernel
theorem sub4_40 : sub4 [-2, -2, -2] = true := by decide +kernel
theorem sub4_41 : sub4 [-2, -2, -1] = true := by decide +kernel
theorem sub4_42 : sub4 [-2, -2, 0] = true := by decide +kernel
theorem sub4_43 : sub4 [-2, -2, 1] = true := by decide +kernel
theorem sub4_44 : sub4 [-2, -2, 2] = true := by decide +kernel
theorem sub4_45 : sub4 [-2, -2, 3] = true := by decide +kernel
theorem sub4_46 : sub4 [-2, -2, 4] = true := by decide +kernel
theorem sub4_47 : sub4 [-2, -2, 5] = true := by decide +kernel
theorem sub4_48 : sub4 [-2, -2, 6] = true := by decide +kernel
theorem sub4_49 : sub4 [-2, -1, -8] = true := by decide +kernel
theorem sub4_50 : sub4 [-2, -1, -7] = true := by decide +kernel
theorem sub4_51 : sub4 [-2, -1, -6] = true := by decide +kernel
theorem sub4_52 : sub4 [-2, -1, -5] = true := by decide +kernel
theorem sub4_53 : sub4 [-2, -1, -4] = true := by decide +kernel
theorem sub4_54 : sub4 [-2, -1, -3] = true := by decide +kernel
theorem sub4_55 : sub4 [-2, -1, -2] = true := by decide +kernel
theorem sub4_56 : sub4 [-2, -1, -1] = true := by decide +kernel
theorem sub4_57 : sub4 [-2, -1, 0] = true := by decide +kernel
theorem sub4_58 : sub4 [-2, -1, 1] = true := by decide +kernel
theorem sub4_59 : sub4 [-2, -1, 2] = true := by decide +kernel
theorem sub4_60 : sub4 [-2, -1, 3] = true := by decide +kernel
theorem sub4_61 : sub4 [-2, -1, 4] = true := by decide +kernel
theorem sub4_62 : sub4 [-2, -1, 5] = true := by decide +kernel
theorem sub4_63 : sub4 [-2, -1, 6] = true := by decide +kernel
theorem sb4_1 : ∀ q ∈ blk4_1, sub4 q = true := by
  unfold blk4_1
  exact List.forall_mem_cons.2 ⟨sub4_32, List.forall_mem_cons.2 ⟨sub4_33, List.forall_mem_cons.2 ⟨sub4_34, List.forall_mem_cons.2 ⟨sub4_35, List.forall_mem_cons.2 ⟨sub4_36, List.forall_mem_cons.2 ⟨sub4_37, List.forall_mem_cons.2 ⟨sub4_38, List.forall_mem_cons.2 ⟨sub4_39, List.forall_mem_cons.2 ⟨sub4_40, List.forall_mem_cons.2 ⟨sub4_41, List.forall_mem_cons.2 ⟨sub4_42, List.forall_mem_cons.2 ⟨sub4_43, List.forall_mem_cons.2 ⟨sub4_44, List.forall_mem_cons.2 ⟨sub4_45, List.forall_mem_cons.2 ⟨sub4_46, List.forall_mem_cons.2 ⟨sub4_47, List.forall_mem_cons.2 ⟨sub4_48, List.forall_mem_cons.2 ⟨sub4_49, List.forall_mem_cons.2 ⟨sub4_50, List.forall_mem_cons.2 ⟨sub4_51, List.forall_mem_cons.2 ⟨sub4_52, List.forall_mem_cons.2 ⟨sub4_53, List.forall_mem_cons.2 ⟨sub4_54, List.forall_mem_cons.2 ⟨sub4_55, List.forall_mem_cons.2 ⟨sub4_56, List.forall_mem_cons.2 ⟨sub4_57, List.forall_mem_cons.2 ⟨sub4_58, List.forall_mem_cons.2 ⟨sub4_59, List.forall_mem_cons.2 ⟨sub4_60, List.forall_mem_cons.2 ⟨sub4_61, List.forall_mem_cons.2 ⟨sub4_62, List.forall_mem_cons.2 ⟨sub4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_64 : sub4 [-2, -1, 7] = true := by decide +kernel
theorem sub4_65 : sub4 [-2, 0, -8] = true := by decide +kernel
theorem sub4_66 : sub4 [-2, 0, -7] = true := by decide +kernel
theorem sub4_67 : sub4 [-2, 0, -6] = true := by decide +kernel
theorem sub4_68 : sub4 [-2, 0, -5] = true := by decide +kernel
theorem sub4_69 : sub4 [-2, 0, -4] = true := by decide +kernel
theorem sub4_70 : sub4 [-2, 0, -3] = true := by decide +kernel
theorem sub4_71 : sub4 [-2, 0, -2] = true := by decide +kernel
theorem sub4_72 : sub4 [-2, 0, -1] = true := by decide +kernel
theorem sub4_73 : sub4 [-2, 0, 0] = true := by decide +kernel
theorem sub4_74 : sub4 [-2, 0, 1] = true := by decide +kernel
theorem sub4_75 : sub4 [-2, 0, 2] = true := by decide +kernel
theorem sub4_76 : sub4 [-2, 0, 3] = true := by decide +kernel
theorem sub4_77 : sub4 [-2, 0, 4] = true := by decide +kernel
theorem sub4_78 : sub4 [-2, 0, 5] = true := by decide +kernel
theorem sub4_79 : sub4 [-2, 0, 6] = true := by decide +kernel
theorem sub4_80 : sub4 [-2, 1, -8] = true := by decide +kernel
theorem sub4_81 : sub4 [-2, 1, -7] = true := by decide +kernel
theorem sub4_82 : sub4 [-2, 1, -6] = true := by decide +kernel
theorem sub4_83 : sub4 [-2, 1, -5] = true := by decide +kernel
theorem sub4_84 : sub4 [-2, 1, -4] = true := by decide +kernel
theorem sub4_85 : sub4 [-2, 1, -3] = true := by decide +kernel
theorem sub4_86 : sub4 [-2, 1, -2] = true := by decide +kernel
theorem sub4_87 : sub4 [-2, 1, -1] = true := by decide +kernel
theorem sub4_88 : sub4 [-2, 1, 0] = true := by decide +kernel
theorem sub4_89 : sub4 [-2, 1, 1] = true := by decide +kernel
theorem sub4_90 : sub4 [-2, 1, 2] = true := by decide +kernel
theorem sub4_91 : sub4 [-2, 1, 3] = true := by decide +kernel
theorem sub4_92 : sub4 [-2, 1, 4] = true := by decide +kernel
theorem sub4_93 : sub4 [-2, 1, 5] = true := by decide +kernel
theorem sub4_94 : sub4 [-2, 1, 6] = true := by decide +kernel
theorem sub4_95 : sub4 [-2, 2] = true := by decide +kernel
theorem sb4_2 : ∀ q ∈ blk4_2, sub4 q = true := by
  unfold blk4_2
  exact List.forall_mem_cons.2 ⟨sub4_64, List.forall_mem_cons.2 ⟨sub4_65, List.forall_mem_cons.2 ⟨sub4_66, List.forall_mem_cons.2 ⟨sub4_67, List.forall_mem_cons.2 ⟨sub4_68, List.forall_mem_cons.2 ⟨sub4_69, List.forall_mem_cons.2 ⟨sub4_70, List.forall_mem_cons.2 ⟨sub4_71, List.forall_mem_cons.2 ⟨sub4_72, List.forall_mem_cons.2 ⟨sub4_73, List.forall_mem_cons.2 ⟨sub4_74, List.forall_mem_cons.2 ⟨sub4_75, List.forall_mem_cons.2 ⟨sub4_76, List.forall_mem_cons.2 ⟨sub4_77, List.forall_mem_cons.2 ⟨sub4_78, List.forall_mem_cons.2 ⟨sub4_79, List.forall_mem_cons.2 ⟨sub4_80, List.forall_mem_cons.2 ⟨sub4_81, List.forall_mem_cons.2 ⟨sub4_82, List.forall_mem_cons.2 ⟨sub4_83, List.forall_mem_cons.2 ⟨sub4_84, List.forall_mem_cons.2 ⟨sub4_85, List.forall_mem_cons.2 ⟨sub4_86, List.forall_mem_cons.2 ⟨sub4_87, List.forall_mem_cons.2 ⟨sub4_88, List.forall_mem_cons.2 ⟨sub4_89, List.forall_mem_cons.2 ⟨sub4_90, List.forall_mem_cons.2 ⟨sub4_91, List.forall_mem_cons.2 ⟨sub4_92, List.forall_mem_cons.2 ⟨sub4_93, List.forall_mem_cons.2 ⟨sub4_94, List.forall_mem_cons.2 ⟨sub4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_96 : sub4 [-2, 3] = true := by decide +kernel
theorem sub4_97 : sub4 [-2, 4] = true := by decide +kernel
theorem sub4_98 : sub4 [-2, 5] = true := by decide +kernel
theorem sub4_99 : sub4 [-1, -6] = true := by decide +kernel
theorem sub4_100 : sub4 [-1, -5] = true := by decide +kernel
theorem sub4_101 : sub4 [-1, -4] = true := by decide +kernel
theorem sub4_102 : sub4 [-1, -3] = true := by decide +kernel
theorem sub4_103 : sub4 [-1, -2, -7] = true := by decide +kernel
theorem sub4_104 : sub4 [-1, -2, -6] = true := by decide +kernel
theorem sub4_105 : sub4 [-1, -2, -5] = true := by decide +kernel
theorem sub4_106 : sub4 [-1, -2, -4] = true := by decide +kernel
theorem sub4_107 : sub4 [-1, -2, -3] = true := by decide +kernel
theorem sub4_108 : sub4 [-1, -2, -2] = true := by decide +kernel
theorem sub4_109 : sub4 [-1, -2, -1] = true := by decide +kernel
theorem sub4_110 : sub4 [-1, -2, 0] = true := by decide +kernel
theorem sub4_111 : sub4 [-1, -2, 1] = true := by decide +kernel
theorem sub4_112 : sub4 [-1, -2, 2] = true := by decide +kernel
theorem sub4_113 : sub4 [-1, -2, 3] = true := by decide +kernel
theorem sub4_114 : sub4 [-1, -2, 4] = true := by decide +kernel
theorem sub4_115 : sub4 [-1, -2, 5] = true := by decide +kernel
theorem sub4_116 : sub4 [-1, -2, 6] = true := by decide +kernel
theorem sub4_117 : sub4 [-1, -2, 7] = true := by decide +kernel
theorem sub4_118 : sub4 [-1, -1, -8] = true := by decide +kernel
theorem sub4_119 : sub4 [-1, -1, -7] = true := by decide +kernel
theorem sub4_120 : sub4 [-1, -1, -6] = true := by decide +kernel
theorem sub4_121 : sub4 [-1, -1, -5] = true := by decide +kernel
theorem sub4_122 : sub4 [-1, -1, -4] = true := by decide +kernel
theorem sub4_123 : sub4 [-1, -1, -3] = true := by decide +kernel
theorem sub4_124 : sub4 [-1, -1, -2] = true := by decide +kernel
theorem sub4_125 : sub4 [-1, -1, -1] = true := by decide +kernel
theorem sub4_126 : sub4 [-1, -1, 0] = true := by decide +kernel
theorem sub4_127 : sub4 [-1, -1, 1] = true := by decide +kernel
theorem sb4_3 : ∀ q ∈ blk4_3, sub4 q = true := by
  unfold blk4_3
  exact List.forall_mem_cons.2 ⟨sub4_96, List.forall_mem_cons.2 ⟨sub4_97, List.forall_mem_cons.2 ⟨sub4_98, List.forall_mem_cons.2 ⟨sub4_99, List.forall_mem_cons.2 ⟨sub4_100, List.forall_mem_cons.2 ⟨sub4_101, List.forall_mem_cons.2 ⟨sub4_102, List.forall_mem_cons.2 ⟨sub4_103, List.forall_mem_cons.2 ⟨sub4_104, List.forall_mem_cons.2 ⟨sub4_105, List.forall_mem_cons.2 ⟨sub4_106, List.forall_mem_cons.2 ⟨sub4_107, List.forall_mem_cons.2 ⟨sub4_108, List.forall_mem_cons.2 ⟨sub4_109, List.forall_mem_cons.2 ⟨sub4_110, List.forall_mem_cons.2 ⟨sub4_111, List.forall_mem_cons.2 ⟨sub4_112, List.forall_mem_cons.2 ⟨sub4_113, List.forall_mem_cons.2 ⟨sub4_114, List.forall_mem_cons.2 ⟨sub4_115, List.forall_mem_cons.2 ⟨sub4_116, List.forall_mem_cons.2 ⟨sub4_117, List.forall_mem_cons.2 ⟨sub4_118, List.forall_mem_cons.2 ⟨sub4_119, List.forall_mem_cons.2 ⟨sub4_120, List.forall_mem_cons.2 ⟨sub4_121, List.forall_mem_cons.2 ⟨sub4_122, List.forall_mem_cons.2 ⟨sub4_123, List.forall_mem_cons.2 ⟨sub4_124, List.forall_mem_cons.2 ⟨sub4_125, List.forall_mem_cons.2 ⟨sub4_126, List.forall_mem_cons.2 ⟨sub4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C031
