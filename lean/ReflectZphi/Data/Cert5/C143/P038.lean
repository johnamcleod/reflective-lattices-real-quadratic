import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd16_0_416 : subd16_0 [1, 2, -2] = true := by decide +kernel
theorem subd16_0_417 : subd16_0 [1, 2, -1] = true := by decide +kernel
theorem subd16_0_418 : subd16_0 [1, 2, 0] = true := by decide +kernel
theorem subd16_0_419 : subd16_0 [1, 2, 1] = true := by decide +kernel
theorem subd16_0_420 : subd16_0 [1, 2, 2] = true := by decide +kernel
theorem subd16_0_421 : subd16_0 [1, 2, 3] = true := by decide +kernel
theorem subd16_0_422 : subd16_0 [1, 2, 4] = true := by decide +kernel
theorem subd16_0_423 : subd16_0 [1, 2, 5] = true := by decide +kernel
theorem subd16_0_424 : subd16_0 [1, 2, 6] = true := by decide +kernel
theorem subd16_0_425 : subd16_0 [1, 3] = true := by decide +kernel
theorem subd16_0_426 : subd16_0 [1, 4] = true := by decide +kernel
theorem subd16_0_427 : subd16_0 [2, -6] = true := by decide +kernel
theorem subd16_0_428 : subd16_0 [2, -5] = true := by decide +kernel
theorem subd16_0_429 : subd16_0 [2, -4] = true := by decide +kernel
theorem subd16_0_430 : subd16_0 [2, -3, -7] = true := by decide +kernel
theorem subd16_0_431 : subd16_0 [2, -3, -6] = true := by decide +kernel
theorem subd16_0_432 : subd16_0 [2, -3, -5] = true := by decide +kernel
theorem subd16_0_433 : subd16_0 [2, -3, -4] = true := by decide +kernel
theorem subd16_0_434 : subd16_0 [2, -3, -3] = true := by decide +kernel
theorem subd16_0_435 : subd16_0 [2, -3, -2] = true := by decide +kernel
theorem subd16_0_436 : subd16_0 [2, -3, -1] = true := by decide +kernel
theorem subd16_0_437 : subd16_0 [2, -3, 0] = true := by decide +kernel
theorem subd16_0_438 : subd16_0 [2, -3, 1] = true := by decide +kernel
theorem subd16_0_439 : subd16_0 [2, -3, 2] = true := by decide +kernel
theorem subd16_0_440 : subd16_0 [2, -3, 3] = true := by decide +kernel
theorem subd16_0_441 : subd16_0 [2, -3, 4] = true := by decide +kernel
theorem subd16_0_442 : subd16_0 [2, -3, 5] = true := by decide +kernel
theorem subd16_0_443 : subd16_0 [2, -3, 6] = true := by decide +kernel
theorem subd16_0_444 : subd16_0 [2, -3, 7] = true := by decide +kernel
theorem subd16_0_445 : subd16_0 [2, -2, -8] = true := by decide +kernel
theorem subd16_0_446 : subd16_0 [2, -2, -7] = true := by decide +kernel
theorem subd16_0_447 : subd16_0 [2, -2, -6] = true := by decide +kernel
theorem sbd16_0_13 : ∀ q ∈ blkd16_0_13, subd16_0 q = true := by
  unfold blkd16_0_13
  exact List.forall_mem_cons.2 ⟨subd16_0_416, List.forall_mem_cons.2 ⟨subd16_0_417, List.forall_mem_cons.2 ⟨subd16_0_418, List.forall_mem_cons.2 ⟨subd16_0_419, List.forall_mem_cons.2 ⟨subd16_0_420, List.forall_mem_cons.2 ⟨subd16_0_421, List.forall_mem_cons.2 ⟨subd16_0_422, List.forall_mem_cons.2 ⟨subd16_0_423, List.forall_mem_cons.2 ⟨subd16_0_424, List.forall_mem_cons.2 ⟨subd16_0_425, List.forall_mem_cons.2 ⟨subd16_0_426, List.forall_mem_cons.2 ⟨subd16_0_427, List.forall_mem_cons.2 ⟨subd16_0_428, List.forall_mem_cons.2 ⟨subd16_0_429, List.forall_mem_cons.2 ⟨subd16_0_430, List.forall_mem_cons.2 ⟨subd16_0_431, List.forall_mem_cons.2 ⟨subd16_0_432, List.forall_mem_cons.2 ⟨subd16_0_433, List.forall_mem_cons.2 ⟨subd16_0_434, List.forall_mem_cons.2 ⟨subd16_0_435, List.forall_mem_cons.2 ⟨subd16_0_436, List.forall_mem_cons.2 ⟨subd16_0_437, List.forall_mem_cons.2 ⟨subd16_0_438, List.forall_mem_cons.2 ⟨subd16_0_439, List.forall_mem_cons.2 ⟨subd16_0_440, List.forall_mem_cons.2 ⟨subd16_0_441, List.forall_mem_cons.2 ⟨subd16_0_442, List.forall_mem_cons.2 ⟨subd16_0_443, List.forall_mem_cons.2 ⟨subd16_0_444, List.forall_mem_cons.2 ⟨subd16_0_445, List.forall_mem_cons.2 ⟨subd16_0_446, List.forall_mem_cons.2 ⟨subd16_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_448 : subd16_0 [2, -2, -5] = true := by decide +kernel
theorem subd16_0_449 : subd16_0 [2, -2, -4] = true := by decide +kernel
theorem subd16_0_450 : subd16_0 [2, -2, -3] = true := by decide +kernel
theorem subd16_0_451 : subd16_0 [2, -2, -2] = true := by decide +kernel
theorem subd16_0_452 : subd16_0 [2, -2, -1] = true := by decide +kernel
theorem subd16_0_453 : subd16_0 [2, -2, 0] = true := by decide +kernel
theorem subd16_0_454 : subd16_0 [2, -2, 1] = true := by decide +kernel
theorem subd16_0_455 : subd16_0 [2, -2, 2] = true := by decide +kernel
theorem subd16_0_456 : subd16_0 [2, -2, 3] = true := by decide +kernel
theorem subd16_0_457 : subd16_0 [2, -2, 4] = true := by decide +kernel
theorem subd16_0_458 : subd16_0 [2, -2, 5] = true := by decide +kernel
theorem subd16_0_459 : subd16_0 [2, -2, 6] = true := by decide +kernel
theorem subd16_0_460 : subd16_0 [2, -2, 7] = true := by decide +kernel
theorem subd16_0_461 : subd16_0 [2, -1, -8] = true := by decide +kernel
theorem subd16_0_462 : subd16_0 [2, -1, -7] = true := by decide +kernel
theorem subd16_0_463 : subd16_0 [2, -1, -6] = true := by decide +kernel
theorem subd16_0_464 : subd16_0 [2, -1, -5] = true := by decide +kernel
theorem subd16_0_465 : subd16_0 [2, -1, -4] = true := by decide +kernel
theorem subd16_0_466 : subd16_0 [2, -1, -3] = true := by decide +kernel
theorem subd16_0_467 : subd16_0 [2, -1, -2] = true := by decide +kernel
theorem subd16_0_468 : subd16_0 [2, -1, -1] = true := by decide +kernel
theorem subd16_0_469 : subd16_0 [2, -1, 0] = true := by decide +kernel
theorem subd16_0_470 : subd16_0 [2, -1, 1] = true := by decide +kernel
theorem subd16_0_471 : subd16_0 [2, -1, 2] = true := by decide +kernel
theorem subd16_0_472 : subd16_0 [2, -1, 3] = true := by decide +kernel
theorem subd16_0_473 : subd16_0 [2, -1, 4] = true := by decide +kernel
theorem subd16_0_474 : subd16_0 [2, -1, 5] = true := by decide +kernel
theorem subd16_0_475 : subd16_0 [2, -1, 6] = true := by decide +kernel
theorem subd16_0_476 : subd16_0 [2, -1, 7] = true := by decide +kernel
theorem subd16_0_477 : subd16_0 [2, 0, -9] = true := by decide +kernel
theorem subd16_0_478 : subd16_0 [2, 0, -8] = true := by decide +kernel
theorem subd16_0_479 : subd16_0 [2, 0, -7] = true := by decide +kernel
theorem sbd16_0_14 : ∀ q ∈ blkd16_0_14, subd16_0 q = true := by
  unfold blkd16_0_14
  exact List.forall_mem_cons.2 ⟨subd16_0_448, List.forall_mem_cons.2 ⟨subd16_0_449, List.forall_mem_cons.2 ⟨subd16_0_450, List.forall_mem_cons.2 ⟨subd16_0_451, List.forall_mem_cons.2 ⟨subd16_0_452, List.forall_mem_cons.2 ⟨subd16_0_453, List.forall_mem_cons.2 ⟨subd16_0_454, List.forall_mem_cons.2 ⟨subd16_0_455, List.forall_mem_cons.2 ⟨subd16_0_456, List.forall_mem_cons.2 ⟨subd16_0_457, List.forall_mem_cons.2 ⟨subd16_0_458, List.forall_mem_cons.2 ⟨subd16_0_459, List.forall_mem_cons.2 ⟨subd16_0_460, List.forall_mem_cons.2 ⟨subd16_0_461, List.forall_mem_cons.2 ⟨subd16_0_462, List.forall_mem_cons.2 ⟨subd16_0_463, List.forall_mem_cons.2 ⟨subd16_0_464, List.forall_mem_cons.2 ⟨subd16_0_465, List.forall_mem_cons.2 ⟨subd16_0_466, List.forall_mem_cons.2 ⟨subd16_0_467, List.forall_mem_cons.2 ⟨subd16_0_468, List.forall_mem_cons.2 ⟨subd16_0_469, List.forall_mem_cons.2 ⟨subd16_0_470, List.forall_mem_cons.2 ⟨subd16_0_471, List.forall_mem_cons.2 ⟨subd16_0_472, List.forall_mem_cons.2 ⟨subd16_0_473, List.forall_mem_cons.2 ⟨subd16_0_474, List.forall_mem_cons.2 ⟨subd16_0_475, List.forall_mem_cons.2 ⟨subd16_0_476, List.forall_mem_cons.2 ⟨subd16_0_477, List.forall_mem_cons.2 ⟨subd16_0_478, List.forall_mem_cons.2 ⟨subd16_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_480 : subd16_0 [2, 0, -6] = true := by decide +kernel
theorem subd16_0_481 : subd16_0 [2, 0, -5] = true := by decide +kernel
theorem subd16_0_482 : subd16_0 [2, 0, -4] = true := by decide +kernel
theorem subd16_0_483 : subd16_0 [2, 0, -3] = true := by decide +kernel
theorem subd16_0_484 : subd16_0 [2, 0, -2] = true := by decide +kernel
theorem subd16_0_485 : subd16_0 [2, 0, -1] = true := by decide +kernel
theorem subd16_0_486 : subd16_0 [2, 0, 0] = true := by decide +kernel
theorem subd16_0_487 : subd16_0 [2, 0, 1] = true := by decide +kernel
theorem subd16_0_488 : subd16_0 [2, 0, 2] = true := by decide +kernel
theorem subd16_0_489 : subd16_0 [2, 0, 3] = true := by decide +kernel
theorem subd16_0_490 : subd16_0 [2, 0, 4] = true := by decide +kernel
theorem subd16_0_491 : subd16_0 [2, 0, 5] = true := by decide +kernel
theorem subd16_0_492 : subd16_0 [2, 0, 6] = true := by decide +kernel
theorem subd16_0_493 : subd16_0 [2, 1, -9] = true := by decide +kernel
theorem subd16_0_494 : subd16_0 [2, 1, -8] = true := by decide +kernel
theorem subd16_0_495 : subd16_0 [2, 1, -7] = true := by decide +kernel
theorem subd16_0_496 : subd16_0 [2, 1, -6] = true := by decide +kernel
theorem subd16_0_497 : subd16_0 [2, 1, -5] = true := by decide +kernel
theorem subd16_0_498 : subd16_0 [2, 1, -4] = true := by decide +kernel
theorem subd16_0_499 : subd16_0 [2, 1, -3] = true := by decide +kernel
theorem subd16_0_500 : subd16_0 [2, 1, -2] = true := by decide +kernel
theorem subd16_0_501 : subd16_0 [2, 1, -1] = true := by decide +kernel
theorem subd16_0_502 : subd16_0 [2, 1, 0] = true := by decide +kernel
theorem subd16_0_503 : subd16_0 [2, 1, 1] = true := by decide +kernel
theorem subd16_0_504 : subd16_0 [2, 1, 2] = true := by decide +kernel
theorem subd16_0_505 : subd16_0 [2, 1, 3] = true := by decide +kernel
theorem subd16_0_506 : subd16_0 [2, 1, 4] = true := by decide +kernel
theorem subd16_0_507 : subd16_0 [2, 1, 5] = true := by decide +kernel
theorem subd16_0_508 : subd16_0 [2, 2] = true := by decide +kernel
theorem subd16_0_509 : subd16_0 [2, 3] = true := by decide +kernel
theorem subd16_0_510 : subd16_0 [3, -5] = true := by decide +kernel
theorem subd16_0_511 : subd16_0 [3, -4] = true := by decide +kernel
theorem sbd16_0_15 : ∀ q ∈ blkd16_0_15, subd16_0 q = true := by
  unfold blkd16_0_15
  exact List.forall_mem_cons.2 ⟨subd16_0_480, List.forall_mem_cons.2 ⟨subd16_0_481, List.forall_mem_cons.2 ⟨subd16_0_482, List.forall_mem_cons.2 ⟨subd16_0_483, List.forall_mem_cons.2 ⟨subd16_0_484, List.forall_mem_cons.2 ⟨subd16_0_485, List.forall_mem_cons.2 ⟨subd16_0_486, List.forall_mem_cons.2 ⟨subd16_0_487, List.forall_mem_cons.2 ⟨subd16_0_488, List.forall_mem_cons.2 ⟨subd16_0_489, List.forall_mem_cons.2 ⟨subd16_0_490, List.forall_mem_cons.2 ⟨subd16_0_491, List.forall_mem_cons.2 ⟨subd16_0_492, List.forall_mem_cons.2 ⟨subd16_0_493, List.forall_mem_cons.2 ⟨subd16_0_494, List.forall_mem_cons.2 ⟨subd16_0_495, List.forall_mem_cons.2 ⟨subd16_0_496, List.forall_mem_cons.2 ⟨subd16_0_497, List.forall_mem_cons.2 ⟨subd16_0_498, List.forall_mem_cons.2 ⟨subd16_0_499, List.forall_mem_cons.2 ⟨subd16_0_500, List.forall_mem_cons.2 ⟨subd16_0_501, List.forall_mem_cons.2 ⟨subd16_0_502, List.forall_mem_cons.2 ⟨subd16_0_503, List.forall_mem_cons.2 ⟨subd16_0_504, List.forall_mem_cons.2 ⟨subd16_0_505, List.forall_mem_cons.2 ⟨subd16_0_506, List.forall_mem_cons.2 ⟨subd16_0_507, List.forall_mem_cons.2 ⟨subd16_0_508, List.forall_mem_cons.2 ⟨subd16_0_509, List.forall_mem_cons.2 ⟨subd16_0_510, List.forall_mem_cons.2 ⟨subd16_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_512 : subd16_0 [3, -3] = true := by decide +kernel
theorem subd16_0_513 : subd16_0 [3, -2] = true := by decide +kernel
theorem subd16_0_514 : subd16_0 [3, -1] = true := by decide +kernel
theorem subd16_0_515 : subd16_0 [3, 0] = true := by decide +kernel
theorem subd16_0_516 : subd16_0 [3, 1] = true := by decide +kernel
theorem subd16_0_517 : subd16_0 [3, 2] = true := by decide +kernel
theorem subd16_0_518 : subd16_0 [4, -4] = true := by decide +kernel
theorem subd16_0_519 : subd16_0 [4, -3] = true := by decide +kernel
theorem subd16_0_520 : subd16_0 [4, -2] = true := by decide +kernel
theorem subd16_0_521 : subd16_0 [4, -1] = true := by decide +kernel
theorem subd16_0_522 : subd16_0 [4, 0] = true := by decide +kernel
theorem sbd16_0_16 : ∀ q ∈ blkd16_0_16, subd16_0 q = true := by
  unfold blkd16_0_16
  exact List.forall_mem_cons.2 ⟨subd16_0_512, List.forall_mem_cons.2 ⟨subd16_0_513, List.forall_mem_cons.2 ⟨subd16_0_514, List.forall_mem_cons.2 ⟨subd16_0_515, List.forall_mem_cons.2 ⟨subd16_0_516, List.forall_mem_cons.2 ⟨subd16_0_517, List.forall_mem_cons.2 ⟨subd16_0_518, List.forall_mem_cons.2 ⟨subd16_0_519, List.forall_mem_cons.2 ⟨subd16_0_520, List.forall_mem_cons.2 ⟨subd16_0_521, List.forall_mem_cons.2 ⟨subd16_0_522, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_1 : ldCheck G d16_1.U d16_1.ms ldd16_1 = true := by decide +kernel
theorem pre_okd16_1 : subPre G cell16 d16_1 = true := by decide +kernel
theorem subd16_1_0 : subd16_1 [-7] = true := by decide +kernel
theorem subd16_1_1 : subd16_1 [-6, -2] = true := by decide +kernel
theorem subd16_1_2 : subd16_1 [-6, -1] = true := by decide +kernel
theorem subd16_1_3 : subd16_1 [-6, 0] = true := by decide +kernel
theorem subd16_1_4 : subd16_1 [-6, 1] = true := by decide +kernel
theorem subd16_1_5 : subd16_1 [-6, 2] = true := by decide +kernel
theorem subd16_1_6 : subd16_1 [-6, 3] = true := by decide +kernel
theorem subd16_1_7 : subd16_1 [-6, 4] = true := by decide +kernel
theorem subd16_1_8 : subd16_1 [-6, 5] = true := by decide +kernel
theorem subd16_1_9 : subd16_1 [-5, -4] = true := by decide +kernel
theorem subd16_1_10 : subd16_1 [-5, -3] = true := by decide +kernel
theorem subd16_1_11 : subd16_1 [-5, -2] = true := by decide +kernel
theorem subd16_1_12 : subd16_1 [-5, -1] = true := by decide +kernel
theorem subd16_1_13 : subd16_1 [-5, 0] = true := by decide +kernel
theorem subd16_1_14 : subd16_1 [-5, 1] = true := by decide +kernel
theorem subd16_1_15 : subd16_1 [-5, 2] = true := by decide +kernel
theorem subd16_1_16 : subd16_1 [-5, 3] = true := by decide +kernel
theorem subd16_1_17 : subd16_1 [-5, 4] = true := by decide +kernel
theorem subd16_1_18 : subd16_1 [-5, 5] = true := by decide +kernel
theorem subd16_1_19 : subd16_1 [-5, 6] = true := by decide +kernel
theorem subd16_1_20 : subd16_1 [-4, -4] = true := by decide +kernel
theorem subd16_1_21 : subd16_1 [-4, -3] = true := by decide +kernel
theorem subd16_1_22 : subd16_1 [-4, -2] = true := by decide +kernel
theorem subd16_1_23 : subd16_1 [-4, -1] = true := by decide +kernel
theorem subd16_1_24 : subd16_1 [-4, 0] = true := by decide +kernel
theorem subd16_1_25 : subd16_1 [-4, 1] = true := by decide +kernel
theorem subd16_1_26 : subd16_1 [-4, 2] = true := by decide +kernel
theorem subd16_1_27 : subd16_1 [-4, 3] = true := by decide +kernel
theorem subd16_1_28 : subd16_1 [-4, 4] = true := by decide +kernel
theorem subd16_1_29 : subd16_1 [-4, 5] = true := by decide +kernel
theorem subd16_1_30 : subd16_1 [-4, 6] = true := by decide +kernel
theorem subd16_1_31 : subd16_1 [-3, -5] = true := by decide +kernel
theorem sbd16_1_0 : ∀ q ∈ blkd16_1_0, subd16_1 q = true := by
  unfold blkd16_1_0
  exact List.forall_mem_cons.2 ⟨subd16_1_0, List.forall_mem_cons.2 ⟨subd16_1_1, List.forall_mem_cons.2 ⟨subd16_1_2, List.forall_mem_cons.2 ⟨subd16_1_3, List.forall_mem_cons.2 ⟨subd16_1_4, List.forall_mem_cons.2 ⟨subd16_1_5, List.forall_mem_cons.2 ⟨subd16_1_6, List.forall_mem_cons.2 ⟨subd16_1_7, List.forall_mem_cons.2 ⟨subd16_1_8, List.forall_mem_cons.2 ⟨subd16_1_9, List.forall_mem_cons.2 ⟨subd16_1_10, List.forall_mem_cons.2 ⟨subd16_1_11, List.forall_mem_cons.2 ⟨subd16_1_12, List.forall_mem_cons.2 ⟨subd16_1_13, List.forall_mem_cons.2 ⟨subd16_1_14, List.forall_mem_cons.2 ⟨subd16_1_15, List.forall_mem_cons.2 ⟨subd16_1_16, List.forall_mem_cons.2 ⟨subd16_1_17, List.forall_mem_cons.2 ⟨subd16_1_18, List.forall_mem_cons.2 ⟨subd16_1_19, List.forall_mem_cons.2 ⟨subd16_1_20, List.forall_mem_cons.2 ⟨subd16_1_21, List.forall_mem_cons.2 ⟨subd16_1_22, List.forall_mem_cons.2 ⟨subd16_1_23, List.forall_mem_cons.2 ⟨subd16_1_24, List.forall_mem_cons.2 ⟨subd16_1_25, List.forall_mem_cons.2 ⟨subd16_1_26, List.forall_mem_cons.2 ⟨subd16_1_27, List.forall_mem_cons.2 ⟨subd16_1_28, List.forall_mem_cons.2 ⟨subd16_1_29, List.forall_mem_cons.2 ⟨subd16_1_30, List.forall_mem_cons.2 ⟨subd16_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_32 : subd16_1 [-3, -4] = true := by decide +kernel
theorem subd16_1_33 : subd16_1 [-3, -3] = true := by decide +kernel
theorem subd16_1_34 : subd16_1 [-3, -2] = true := by decide +kernel
theorem subd16_1_35 : subd16_1 [-3, -1] = true := by decide +kernel
theorem subd16_1_36 : subd16_1 [-3, 0] = true := by decide +kernel
theorem subd16_1_37 : subd16_1 [-3, 1] = true := by decide +kernel
theorem subd16_1_38 : subd16_1 [-3, 2] = true := by decide +kernel
theorem subd16_1_39 : subd16_1 [-3, 3] = true := by decide +kernel
theorem subd16_1_40 : subd16_1 [-3, 4] = true := by decide +kernel
theorem subd16_1_41 : subd16_1 [-3, 5] = true := by decide +kernel
theorem subd16_1_42 : subd16_1 [-3, 6] = true := by decide +kernel
theorem subd16_1_43 : subd16_1 [-2, -6] = true := by decide +kernel
theorem subd16_1_44 : subd16_1 [-2, -5] = true := by decide +kernel
theorem subd16_1_45 : subd16_1 [-2, -4] = true := by decide +kernel
theorem subd16_1_46 : subd16_1 [-2, -3] = true := by decide +kernel
theorem subd16_1_47 : subd16_1 [-2, -2] = true := by decide +kernel
theorem subd16_1_48 : subd16_1 [-2, -1, -7] = true := by decide +kernel
theorem subd16_1_49 : subd16_1 [-2, -1, -6] = true := by decide +kernel
theorem subd16_1_50 : subd16_1 [-2, -1, -5] = true := by decide +kernel
theorem subd16_1_51 : subd16_1 [-2, -1, -4] = true := by decide +kernel
theorem subd16_1_52 : subd16_1 [-2, -1, -3] = true := by decide +kernel
theorem subd16_1_53 : subd16_1 [-2, -1, -2] = true := by decide +kernel
theorem subd16_1_54 : subd16_1 [-2, -1, -1] = true := by decide +kernel
theorem subd16_1_55 : subd16_1 [-2, -1, 0] = true := by decide +kernel
theorem subd16_1_56 : subd16_1 [-2, -1, 1] = true := by decide +kernel
theorem subd16_1_57 : subd16_1 [-2, -1, 2] = true := by decide +kernel
theorem subd16_1_58 : subd16_1 [-2, -1, 3] = true := by decide +kernel
theorem subd16_1_59 : subd16_1 [-2, -1, 4] = true := by decide +kernel
theorem subd16_1_60 : subd16_1 [-2, -1, 5] = true := by decide +kernel
theorem subd16_1_61 : subd16_1 [-2, 0, -7] = true := by decide +kernel
theorem subd16_1_62 : subd16_1 [-2, 0, -6] = true := by decide +kernel
theorem subd16_1_63 : subd16_1 [-2, 0, -5] = true := by decide +kernel
theorem sbd16_1_1 : ∀ q ∈ blkd16_1_1, subd16_1 q = true := by
  unfold blkd16_1_1
  exact List.forall_mem_cons.2 ⟨subd16_1_32, List.forall_mem_cons.2 ⟨subd16_1_33, List.forall_mem_cons.2 ⟨subd16_1_34, List.forall_mem_cons.2 ⟨subd16_1_35, List.forall_mem_cons.2 ⟨subd16_1_36, List.forall_mem_cons.2 ⟨subd16_1_37, List.forall_mem_cons.2 ⟨subd16_1_38, List.forall_mem_cons.2 ⟨subd16_1_39, List.forall_mem_cons.2 ⟨subd16_1_40, List.forall_mem_cons.2 ⟨subd16_1_41, List.forall_mem_cons.2 ⟨subd16_1_42, List.forall_mem_cons.2 ⟨subd16_1_43, List.forall_mem_cons.2 ⟨subd16_1_44, List.forall_mem_cons.2 ⟨subd16_1_45, List.forall_mem_cons.2 ⟨subd16_1_46, List.forall_mem_cons.2 ⟨subd16_1_47, List.forall_mem_cons.2 ⟨subd16_1_48, List.forall_mem_cons.2 ⟨subd16_1_49, List.forall_mem_cons.2 ⟨subd16_1_50, List.forall_mem_cons.2 ⟨subd16_1_51, List.forall_mem_cons.2 ⟨subd16_1_52, List.forall_mem_cons.2 ⟨subd16_1_53, List.forall_mem_cons.2 ⟨subd16_1_54, List.forall_mem_cons.2 ⟨subd16_1_55, List.forall_mem_cons.2 ⟨subd16_1_56, List.forall_mem_cons.2 ⟨subd16_1_57, List.forall_mem_cons.2 ⟨subd16_1_58, List.forall_mem_cons.2 ⟨subd16_1_59, List.forall_mem_cons.2 ⟨subd16_1_60, List.forall_mem_cons.2 ⟨subd16_1_61, List.forall_mem_cons.2 ⟨subd16_1_62, List.forall_mem_cons.2 ⟨subd16_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_64 : subd16_1 [-2, 0, -4] = true := by decide +kernel
theorem subd16_1_65 : subd16_1 [-2, 0, -3] = true := by decide +kernel
theorem subd16_1_66 : subd16_1 [-2, 0, -2] = true := by decide +kernel
theorem subd16_1_67 : subd16_1 [-2, 0, -1] = true := by decide +kernel
theorem subd16_1_68 : subd16_1 [-2, 0, 0] = true := by decide +kernel
theorem subd16_1_69 : subd16_1 [-2, 0, 1] = true := by decide +kernel
theorem subd16_1_70 : subd16_1 [-2, 0, 2] = true := by decide +kernel
theorem subd16_1_71 : subd16_1 [-2, 0, 3] = true := by decide +kernel
theorem subd16_1_72 : subd16_1 [-2, 0, 4] = true := by decide +kernel
theorem subd16_1_73 : subd16_1 [-2, 0, 5] = true := by decide +kernel
theorem subd16_1_74 : subd16_1 [-2, 0, 6] = true := by decide +kernel
theorem subd16_1_75 : subd16_1 [-2, 1, -7] = true := by decide +kernel
theorem subd16_1_76 : subd16_1 [-2, 1, -6] = true := by decide +kernel
theorem subd16_1_77 : subd16_1 [-2, 1, -5] = true := by decide +kernel
theorem subd16_1_78 : subd16_1 [-2, 1, -4] = true := by decide +kernel
theorem subd16_1_79 : subd16_1 [-2, 1, -3] = true := by decide +kernel
theorem subd16_1_80 : subd16_1 [-2, 1, -2] = true := by decide +kernel
theorem subd16_1_81 : subd16_1 [-2, 1, -1] = true := by decide +kernel
theorem subd16_1_82 : subd16_1 [-2, 1, 0] = true := by decide +kernel
theorem subd16_1_83 : subd16_1 [-2, 1, 1] = true := by decide +kernel
theorem subd16_1_84 : subd16_1 [-2, 1, 2] = true := by decide +kernel
theorem subd16_1_85 : subd16_1 [-2, 1, 3] = true := by decide +kernel
theorem subd16_1_86 : subd16_1 [-2, 1, 4] = true := by decide +kernel
theorem subd16_1_87 : subd16_1 [-2, 1, 5] = true := by decide +kernel
theorem subd16_1_88 : subd16_1 [-2, 1, 6] = true := by decide +kernel
theorem subd16_1_89 : subd16_1 [-2, 2, -7] = true := by decide +kernel
theorem subd16_1_90 : subd16_1 [-2, 2, -6] = true := by decide +kernel
theorem subd16_1_91 : subd16_1 [-2, 2, -5] = true := by decide +kernel
theorem subd16_1_92 : subd16_1 [-2, 2, -4] = true := by decide +kernel
theorem subd16_1_93 : subd16_1 [-2, 2, -3] = true := by decide +kernel
theorem subd16_1_94 : subd16_1 [-2, 2, -2] = true := by decide +kernel
theorem subd16_1_95 : subd16_1 [-2, 2, -1] = true := by decide +kernel
theorem sbd16_1_2 : ∀ q ∈ blkd16_1_2, subd16_1 q = true := by
  unfold blkd16_1_2
  exact List.forall_mem_cons.2 ⟨subd16_1_64, List.forall_mem_cons.2 ⟨subd16_1_65, List.forall_mem_cons.2 ⟨subd16_1_66, List.forall_mem_cons.2 ⟨subd16_1_67, List.forall_mem_cons.2 ⟨subd16_1_68, List.forall_mem_cons.2 ⟨subd16_1_69, List.forall_mem_cons.2 ⟨subd16_1_70, List.forall_mem_cons.2 ⟨subd16_1_71, List.forall_mem_cons.2 ⟨subd16_1_72, List.forall_mem_cons.2 ⟨subd16_1_73, List.forall_mem_cons.2 ⟨subd16_1_74, List.forall_mem_cons.2 ⟨subd16_1_75, List.forall_mem_cons.2 ⟨subd16_1_76, List.forall_mem_cons.2 ⟨subd16_1_77, List.forall_mem_cons.2 ⟨subd16_1_78, List.forall_mem_cons.2 ⟨subd16_1_79, List.forall_mem_cons.2 ⟨subd16_1_80, List.forall_mem_cons.2 ⟨subd16_1_81, List.forall_mem_cons.2 ⟨subd16_1_82, List.forall_mem_cons.2 ⟨subd16_1_83, List.forall_mem_cons.2 ⟨subd16_1_84, List.forall_mem_cons.2 ⟨subd16_1_85, List.forall_mem_cons.2 ⟨subd16_1_86, List.forall_mem_cons.2 ⟨subd16_1_87, List.forall_mem_cons.2 ⟨subd16_1_88, List.forall_mem_cons.2 ⟨subd16_1_89, List.forall_mem_cons.2 ⟨subd16_1_90, List.forall_mem_cons.2 ⟨subd16_1_91, List.forall_mem_cons.2 ⟨subd16_1_92, List.forall_mem_cons.2 ⟨subd16_1_93, List.forall_mem_cons.2 ⟨subd16_1_94, List.forall_mem_cons.2 ⟨subd16_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
