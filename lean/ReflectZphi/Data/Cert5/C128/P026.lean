import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_5_416 : subd5_5 [1, 3, 5] = true := by decide +kernel
theorem subd5_5_417 : subd5_5 [1, 3, 6] = true := by decide +kernel
theorem subd5_5_418 : subd5_5 [1, 3, 7] = true := by decide +kernel
theorem subd5_5_419 : subd5_5 [1, 3, 8] = true := by decide +kernel
theorem subd5_5_420 : subd5_5 [1, 4] = true := by decide +kernel
theorem subd5_5_421 : subd5_5 [1, 5] = true := by decide +kernel
theorem subd5_5_422 : subd5_5 [2, -4] = true := by decide +kernel
theorem subd5_5_423 : subd5_5 [2, -3] = true := by decide +kernel
theorem subd5_5_424 : subd5_5 [2, -2] = true := by decide +kernel
theorem subd5_5_425 : subd5_5 [2, -1, -7] = true := by decide +kernel
theorem subd5_5_426 : subd5_5 [2, -1, -6] = true := by decide +kernel
theorem subd5_5_427 : subd5_5 [2, -1, -5] = true := by decide +kernel
theorem subd5_5_428 : subd5_5 [2, -1, -4] = true := by decide +kernel
theorem subd5_5_429 : subd5_5 [2, -1, -3] = true := by decide +kernel
theorem subd5_5_430 : subd5_5 [2, -1, -2] = true := by decide +kernel
theorem subd5_5_431 : subd5_5 [2, -1, -1] = true := by decide +kernel
theorem subd5_5_432 : subd5_5 [2, -1, 0] = true := by decide +kernel
theorem subd5_5_433 : subd5_5 [2, -1, 1] = true := by decide +kernel
theorem subd5_5_434 : subd5_5 [2, -1, 2] = true := by decide +kernel
theorem subd5_5_435 : subd5_5 [2, -1, 3] = true := by decide +kernel
theorem subd5_5_436 : subd5_5 [2, -1, 4] = true := by decide +kernel
theorem subd5_5_437 : subd5_5 [2, -1, 5] = true := by decide +kernel
theorem subd5_5_438 : subd5_5 [2, -1, 6] = true := by decide +kernel
theorem subd5_5_439 : subd5_5 [2, 0, -7] = true := by decide +kernel
theorem subd5_5_440 : subd5_5 [2, 0, -6] = true := by decide +kernel
theorem subd5_5_441 : subd5_5 [2, 0, -5] = true := by decide +kernel
theorem subd5_5_442 : subd5_5 [2, 0, -4] = true := by decide +kernel
theorem subd5_5_443 : subd5_5 [2, 0, -3] = true := by decide +kernel
theorem subd5_5_444 : subd5_5 [2, 0, -2] = true := by decide +kernel
theorem subd5_5_445 : subd5_5 [2, 0, -1] = true := by decide +kernel
theorem subd5_5_446 : subd5_5 [2, 0, 0] = true := by decide +kernel
theorem subd5_5_447 : subd5_5 [2, 0, 1] = true := by decide +kernel
theorem sbd5_5_13 : ∀ q ∈ blkd5_5_13, subd5_5 q = true := by
  unfold blkd5_5_13
  exact List.forall_mem_cons.2 ⟨subd5_5_416, List.forall_mem_cons.2 ⟨subd5_5_417, List.forall_mem_cons.2 ⟨subd5_5_418, List.forall_mem_cons.2 ⟨subd5_5_419, List.forall_mem_cons.2 ⟨subd5_5_420, List.forall_mem_cons.2 ⟨subd5_5_421, List.forall_mem_cons.2 ⟨subd5_5_422, List.forall_mem_cons.2 ⟨subd5_5_423, List.forall_mem_cons.2 ⟨subd5_5_424, List.forall_mem_cons.2 ⟨subd5_5_425, List.forall_mem_cons.2 ⟨subd5_5_426, List.forall_mem_cons.2 ⟨subd5_5_427, List.forall_mem_cons.2 ⟨subd5_5_428, List.forall_mem_cons.2 ⟨subd5_5_429, List.forall_mem_cons.2 ⟨subd5_5_430, List.forall_mem_cons.2 ⟨subd5_5_431, List.forall_mem_cons.2 ⟨subd5_5_432, List.forall_mem_cons.2 ⟨subd5_5_433, List.forall_mem_cons.2 ⟨subd5_5_434, List.forall_mem_cons.2 ⟨subd5_5_435, List.forall_mem_cons.2 ⟨subd5_5_436, List.forall_mem_cons.2 ⟨subd5_5_437, List.forall_mem_cons.2 ⟨subd5_5_438, List.forall_mem_cons.2 ⟨subd5_5_439, List.forall_mem_cons.2 ⟨subd5_5_440, List.forall_mem_cons.2 ⟨subd5_5_441, List.forall_mem_cons.2 ⟨subd5_5_442, List.forall_mem_cons.2 ⟨subd5_5_443, List.forall_mem_cons.2 ⟨subd5_5_444, List.forall_mem_cons.2 ⟨subd5_5_445, List.forall_mem_cons.2 ⟨subd5_5_446, List.forall_mem_cons.2 ⟨subd5_5_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_448 : subd5_5 [2, 0, 2] = true := by decide +kernel
theorem subd5_5_449 : subd5_5 [2, 0, 3] = true := by decide +kernel
theorem subd5_5_450 : subd5_5 [2, 0, 4] = true := by decide +kernel
theorem subd5_5_451 : subd5_5 [2, 0, 5] = true := by decide +kernel
theorem subd5_5_452 : subd5_5 [2, 0, 6] = true := by decide +kernel
theorem subd5_5_453 : subd5_5 [2, 0, 7] = true := by decide +kernel
theorem subd5_5_454 : subd5_5 [2, 0, 8] = true := by decide +kernel
theorem subd5_5_455 : subd5_5 [2, 1, -7] = true := by decide +kernel
theorem subd5_5_456 : subd5_5 [2, 1, -6] = true := by decide +kernel
theorem subd5_5_457 : subd5_5 [2, 1, -5] = true := by decide +kernel
theorem subd5_5_458 : subd5_5 [2, 1, -4] = true := by decide +kernel
theorem subd5_5_459 : subd5_5 [2, 1, -3] = true := by decide +kernel
theorem subd5_5_460 : subd5_5 [2, 1, -2] = true := by decide +kernel
theorem subd5_5_461 : subd5_5 [2, 1, -1] = true := by decide +kernel
theorem subd5_5_462 : subd5_5 [2, 1, 0] = true := by decide +kernel
theorem subd5_5_463 : subd5_5 [2, 1, 1] = true := by decide +kernel
theorem subd5_5_464 : subd5_5 [2, 1, 2] = true := by decide +kernel
theorem subd5_5_465 : subd5_5 [2, 1, 3] = true := by decide +kernel
theorem subd5_5_466 : subd5_5 [2, 1, 4] = true := by decide +kernel
theorem subd5_5_467 : subd5_5 [2, 1, 5] = true := by decide +kernel
theorem subd5_5_468 : subd5_5 [2, 1, 6] = true := by decide +kernel
theorem subd5_5_469 : subd5_5 [2, 1, 7] = true := by decide +kernel
theorem subd5_5_470 : subd5_5 [2, 1, 8] = true := by decide +kernel
theorem subd5_5_471 : subd5_5 [2, 2, -6] = true := by decide +kernel
theorem subd5_5_472 : subd5_5 [2, 2, -5] = true := by decide +kernel
theorem subd5_5_473 : subd5_5 [2, 2, -4] = true := by decide +kernel
theorem subd5_5_474 : subd5_5 [2, 2, -3] = true := by decide +kernel
theorem subd5_5_475 : subd5_5 [2, 2, -2] = true := by decide +kernel
theorem subd5_5_476 : subd5_5 [2, 2, -1] = true := by decide +kernel
theorem subd5_5_477 : subd5_5 [2, 2, 0] = true := by decide +kernel
theorem subd5_5_478 : subd5_5 [2, 2, 1] = true := by decide +kernel
theorem subd5_5_479 : subd5_5 [2, 2, 2] = true := by decide +kernel
theorem sbd5_5_14 : ∀ q ∈ blkd5_5_14, subd5_5 q = true := by
  unfold blkd5_5_14
  exact List.forall_mem_cons.2 ⟨subd5_5_448, List.forall_mem_cons.2 ⟨subd5_5_449, List.forall_mem_cons.2 ⟨subd5_5_450, List.forall_mem_cons.2 ⟨subd5_5_451, List.forall_mem_cons.2 ⟨subd5_5_452, List.forall_mem_cons.2 ⟨subd5_5_453, List.forall_mem_cons.2 ⟨subd5_5_454, List.forall_mem_cons.2 ⟨subd5_5_455, List.forall_mem_cons.2 ⟨subd5_5_456, List.forall_mem_cons.2 ⟨subd5_5_457, List.forall_mem_cons.2 ⟨subd5_5_458, List.forall_mem_cons.2 ⟨subd5_5_459, List.forall_mem_cons.2 ⟨subd5_5_460, List.forall_mem_cons.2 ⟨subd5_5_461, List.forall_mem_cons.2 ⟨subd5_5_462, List.forall_mem_cons.2 ⟨subd5_5_463, List.forall_mem_cons.2 ⟨subd5_5_464, List.forall_mem_cons.2 ⟨subd5_5_465, List.forall_mem_cons.2 ⟨subd5_5_466, List.forall_mem_cons.2 ⟨subd5_5_467, List.forall_mem_cons.2 ⟨subd5_5_468, List.forall_mem_cons.2 ⟨subd5_5_469, List.forall_mem_cons.2 ⟨subd5_5_470, List.forall_mem_cons.2 ⟨subd5_5_471, List.forall_mem_cons.2 ⟨subd5_5_472, List.forall_mem_cons.2 ⟨subd5_5_473, List.forall_mem_cons.2 ⟨subd5_5_474, List.forall_mem_cons.2 ⟨subd5_5_475, List.forall_mem_cons.2 ⟨subd5_5_476, List.forall_mem_cons.2 ⟨subd5_5_477, List.forall_mem_cons.2 ⟨subd5_5_478, List.forall_mem_cons.2 ⟨subd5_5_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_480 : subd5_5 [2, 2, 3] = true := by decide +kernel
theorem subd5_5_481 : subd5_5 [2, 2, 4] = true := by decide +kernel
theorem subd5_5_482 : subd5_5 [2, 2, 5] = true := by decide +kernel
theorem subd5_5_483 : subd5_5 [2, 2, 6] = true := by decide +kernel
theorem subd5_5_484 : subd5_5 [2, 2, 7] = true := by decide +kernel
theorem subd5_5_485 : subd5_5 [2, 2, 8] = true := by decide +kernel
theorem subd5_5_486 : subd5_5 [2, 2, 9] = true := by decide +kernel
theorem subd5_5_487 : subd5_5 [2, 3, -5] = true := by decide +kernel
theorem subd5_5_488 : subd5_5 [2, 3, -4] = true := by decide +kernel
theorem subd5_5_489 : subd5_5 [2, 3, -3] = true := by decide +kernel
theorem subd5_5_490 : subd5_5 [2, 3, -2] = true := by decide +kernel
theorem subd5_5_491 : subd5_5 [2, 3, -1] = true := by decide +kernel
theorem subd5_5_492 : subd5_5 [2, 3, 0] = true := by decide +kernel
theorem subd5_5_493 : subd5_5 [2, 3, 1] = true := by decide +kernel
theorem subd5_5_494 : subd5_5 [2, 3, 2] = true := by decide +kernel
theorem subd5_5_495 : subd5_5 [2, 3, 3] = true := by decide +kernel
theorem subd5_5_496 : subd5_5 [2, 3, 4] = true := by decide +kernel
theorem subd5_5_497 : subd5_5 [2, 3, 5] = true := by decide +kernel
theorem subd5_5_498 : subd5_5 [2, 3, 6] = true := by decide +kernel
theorem subd5_5_499 : subd5_5 [2, 3, 7] = true := by decide +kernel
theorem subd5_5_500 : subd5_5 [2, 3, 8] = true := by decide +kernel
theorem subd5_5_501 : subd5_5 [2, 4] = true := by decide +kernel
theorem subd5_5_502 : subd5_5 [2, 5] = true := by decide +kernel
theorem subd5_5_503 : subd5_5 [3, -2] = true := by decide +kernel
theorem subd5_5_504 : subd5_5 [3, -1] = true := by decide +kernel
theorem subd5_5_505 : subd5_5 [3, 0] = true := by decide +kernel
theorem subd5_5_506 : subd5_5 [3, 1] = true := by decide +kernel
theorem subd5_5_507 : subd5_5 [3, 2] = true := by decide +kernel
theorem subd5_5_508 : subd5_5 [3, 3] = true := by decide +kernel
theorem subd5_5_509 : subd5_5 [3, 4] = true := by decide +kernel
theorem subd5_5_510 : subd5_5 [4] = true := by decide +kernel
theorem sbd5_5_15 : ∀ q ∈ blkd5_5_15, subd5_5 q = true := by
  unfold blkd5_5_15
  exact List.forall_mem_cons.2 ⟨subd5_5_480, List.forall_mem_cons.2 ⟨subd5_5_481, List.forall_mem_cons.2 ⟨subd5_5_482, List.forall_mem_cons.2 ⟨subd5_5_483, List.forall_mem_cons.2 ⟨subd5_5_484, List.forall_mem_cons.2 ⟨subd5_5_485, List.forall_mem_cons.2 ⟨subd5_5_486, List.forall_mem_cons.2 ⟨subd5_5_487, List.forall_mem_cons.2 ⟨subd5_5_488, List.forall_mem_cons.2 ⟨subd5_5_489, List.forall_mem_cons.2 ⟨subd5_5_490, List.forall_mem_cons.2 ⟨subd5_5_491, List.forall_mem_cons.2 ⟨subd5_5_492, List.forall_mem_cons.2 ⟨subd5_5_493, List.forall_mem_cons.2 ⟨subd5_5_494, List.forall_mem_cons.2 ⟨subd5_5_495, List.forall_mem_cons.2 ⟨subd5_5_496, List.forall_mem_cons.2 ⟨subd5_5_497, List.forall_mem_cons.2 ⟨subd5_5_498, List.forall_mem_cons.2 ⟨subd5_5_499, List.forall_mem_cons.2 ⟨subd5_5_500, List.forall_mem_cons.2 ⟨subd5_5_501, List.forall_mem_cons.2 ⟨subd5_5_502, List.forall_mem_cons.2 ⟨subd5_5_503, List.forall_mem_cons.2 ⟨subd5_5_504, List.forall_mem_cons.2 ⟨subd5_5_505, List.forall_mem_cons.2 ⟨subd5_5_506, List.forall_mem_cons.2 ⟨subd5_5_507, List.forall_mem_cons.2 ⟨subd5_5_508, List.forall_mem_cons.2 ⟨subd5_5_509, List.forall_mem_cons.2 ⟨subd5_5_510, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_6 : ldCheck G d5_6.U d5_6.ms ldd5_6 = true := by decide +kernel
theorem pre_okd5_6 : subPre G cell5 d5_6 = true := by decide +kernel
theorem subd5_6_0 : subd5_6 [-6, -4] = true := by decide +kernel
theorem subd5_6_1 : subd5_6 [-6, -3] = true := by decide +kernel
theorem subd5_6_2 : subd5_6 [-6, -2] = true := by decide +kernel
theorem subd5_6_3 : subd5_6 [-6, -1] = true := by decide +kernel
theorem subd5_6_4 : subd5_6 [-6, 0] = true := by decide +kernel
theorem subd5_6_5 : subd5_6 [-6, 1] = true := by decide +kernel
theorem subd5_6_6 : subd5_6 [-5, -5] = true := by decide +kernel
theorem subd5_6_7 : subd5_6 [-5, -4] = true := by decide +kernel
theorem subd5_6_8 : subd5_6 [-5, -3] = true := by decide +kernel
theorem subd5_6_9 : subd5_6 [-5, -2] = true := by decide +kernel
theorem subd5_6_10 : subd5_6 [-5, -1] = true := by decide +kernel
theorem subd5_6_11 : subd5_6 [-5, 0] = true := by decide +kernel
theorem subd5_6_12 : subd5_6 [-5, 1] = true := by decide +kernel
theorem subd5_6_13 : subd5_6 [-5, 2] = true := by decide +kernel
theorem subd5_6_14 : subd5_6 [-5, 3] = true := by decide +kernel
theorem subd5_6_15 : subd5_6 [-4, -6] = true := by decide +kernel
theorem subd5_6_16 : subd5_6 [-4, -5] = true := by decide +kernel
theorem subd5_6_17 : subd5_6 [-4, -4] = true := by decide +kernel
theorem subd5_6_18 : subd5_6 [-4, -3] = true := by decide +kernel
theorem subd5_6_19 : subd5_6 [-4, -2] = true := by decide +kernel
theorem subd5_6_20 : subd5_6 [-4, -1] = true := by decide +kernel
theorem subd5_6_21 : subd5_6 [-4, 0] = true := by decide +kernel
theorem subd5_6_22 : subd5_6 [-4, 1] = true := by decide +kernel
theorem subd5_6_23 : subd5_6 [-4, 2] = true := by decide +kernel
theorem subd5_6_24 : subd5_6 [-4, 3] = true := by decide +kernel
theorem subd5_6_25 : subd5_6 [-4, 4] = true := by decide +kernel
theorem subd5_6_26 : subd5_6 [-3, -6] = true := by decide +kernel
theorem subd5_6_27 : subd5_6 [-3, -5] = true := by decide +kernel
theorem subd5_6_28 : subd5_6 [-3, -4] = true := by decide +kernel
theorem subd5_6_29 : subd5_6 [-3, -3] = true := by decide +kernel
theorem subd5_6_30 : subd5_6 [-3, -2] = true := by decide +kernel
theorem subd5_6_31 : subd5_6 [-3, -1, -7] = true := by decide +kernel
theorem sbd5_6_0 : ∀ q ∈ blkd5_6_0, subd5_6 q = true := by
  unfold blkd5_6_0
  exact List.forall_mem_cons.2 ⟨subd5_6_0, List.forall_mem_cons.2 ⟨subd5_6_1, List.forall_mem_cons.2 ⟨subd5_6_2, List.forall_mem_cons.2 ⟨subd5_6_3, List.forall_mem_cons.2 ⟨subd5_6_4, List.forall_mem_cons.2 ⟨subd5_6_5, List.forall_mem_cons.2 ⟨subd5_6_6, List.forall_mem_cons.2 ⟨subd5_6_7, List.forall_mem_cons.2 ⟨subd5_6_8, List.forall_mem_cons.2 ⟨subd5_6_9, List.forall_mem_cons.2 ⟨subd5_6_10, List.forall_mem_cons.2 ⟨subd5_6_11, List.forall_mem_cons.2 ⟨subd5_6_12, List.forall_mem_cons.2 ⟨subd5_6_13, List.forall_mem_cons.2 ⟨subd5_6_14, List.forall_mem_cons.2 ⟨subd5_6_15, List.forall_mem_cons.2 ⟨subd5_6_16, List.forall_mem_cons.2 ⟨subd5_6_17, List.forall_mem_cons.2 ⟨subd5_6_18, List.forall_mem_cons.2 ⟨subd5_6_19, List.forall_mem_cons.2 ⟨subd5_6_20, List.forall_mem_cons.2 ⟨subd5_6_21, List.forall_mem_cons.2 ⟨subd5_6_22, List.forall_mem_cons.2 ⟨subd5_6_23, List.forall_mem_cons.2 ⟨subd5_6_24, List.forall_mem_cons.2 ⟨subd5_6_25, List.forall_mem_cons.2 ⟨subd5_6_26, List.forall_mem_cons.2 ⟨subd5_6_27, List.forall_mem_cons.2 ⟨subd5_6_28, List.forall_mem_cons.2 ⟨subd5_6_29, List.forall_mem_cons.2 ⟨subd5_6_30, List.forall_mem_cons.2 ⟨subd5_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_32 : subd5_6 [-3, -1, -6] = true := by decide +kernel
theorem subd5_6_33 : subd5_6 [-3, -1, -5] = true := by decide +kernel
theorem subd5_6_34 : subd5_6 [-3, -1, -4] = true := by decide +kernel
theorem subd5_6_35 : subd5_6 [-3, -1, -3] = true := by decide +kernel
theorem subd5_6_36 : subd5_6 [-3, -1, -2] = true := by decide +kernel
theorem subd5_6_37 : subd5_6 [-3, -1, -1] = true := by decide +kernel
theorem subd5_6_38 : subd5_6 [-3, -1, 0] = true := by decide +kernel
theorem subd5_6_39 : subd5_6 [-3, -1, 1] = true := by decide +kernel
theorem subd5_6_40 : subd5_6 [-3, -1, 2] = true := by decide +kernel
theorem subd5_6_41 : subd5_6 [-3, -1, 3] = true := by decide +kernel
theorem subd5_6_42 : subd5_6 [-3, -1, 4] = true := by decide +kernel
theorem subd5_6_43 : subd5_6 [-3, -1, 5] = true := by decide +kernel
theorem subd5_6_44 : subd5_6 [-3, 0] = true := by decide +kernel
theorem subd5_6_45 : subd5_6 [-3, 1] = true := by decide +kernel
theorem subd5_6_46 : subd5_6 [-3, 2] = true := by decide +kernel
theorem subd5_6_47 : subd5_6 [-3, 3] = true := by decide +kernel
theorem subd5_6_48 : subd5_6 [-3, 4] = true := by decide +kernel
theorem subd5_6_49 : subd5_6 [-2, -7] = true := by decide +kernel
theorem subd5_6_50 : subd5_6 [-2, -6] = true := by decide +kernel
theorem subd5_6_51 : subd5_6 [-2, -5] = true := by decide +kernel
theorem subd5_6_52 : subd5_6 [-2, -4] = true := by decide +kernel
theorem subd5_6_53 : subd5_6 [-2, -3] = true := by decide +kernel
theorem subd5_6_54 : subd5_6 [-2, -2, -7] = true := by decide +kernel
theorem subd5_6_55 : subd5_6 [-2, -2, -6] = true := by decide +kernel
theorem subd5_6_56 : subd5_6 [-2, -2, -5] = true := by decide +kernel
theorem subd5_6_57 : subd5_6 [-2, -2, -4] = true := by decide +kernel
theorem subd5_6_58 : subd5_6 [-2, -2, -3] = true := by decide +kernel
theorem subd5_6_59 : subd5_6 [-2, -2, -2] = true := by decide +kernel
theorem subd5_6_60 : subd5_6 [-2, -2, -1] = true := by decide +kernel
theorem subd5_6_61 : subd5_6 [-2, -2, 0] = true := by decide +kernel
theorem subd5_6_62 : subd5_6 [-2, -2, 1] = true := by decide +kernel
theorem subd5_6_63 : subd5_6 [-2, -2, 2] = true := by decide +kernel
theorem sbd5_6_1 : ∀ q ∈ blkd5_6_1, subd5_6 q = true := by
  unfold blkd5_6_1
  exact List.forall_mem_cons.2 ⟨subd5_6_32, List.forall_mem_cons.2 ⟨subd5_6_33, List.forall_mem_cons.2 ⟨subd5_6_34, List.forall_mem_cons.2 ⟨subd5_6_35, List.forall_mem_cons.2 ⟨subd5_6_36, List.forall_mem_cons.2 ⟨subd5_6_37, List.forall_mem_cons.2 ⟨subd5_6_38, List.forall_mem_cons.2 ⟨subd5_6_39, List.forall_mem_cons.2 ⟨subd5_6_40, List.forall_mem_cons.2 ⟨subd5_6_41, List.forall_mem_cons.2 ⟨subd5_6_42, List.forall_mem_cons.2 ⟨subd5_6_43, List.forall_mem_cons.2 ⟨subd5_6_44, List.forall_mem_cons.2 ⟨subd5_6_45, List.forall_mem_cons.2 ⟨subd5_6_46, List.forall_mem_cons.2 ⟨subd5_6_47, List.forall_mem_cons.2 ⟨subd5_6_48, List.forall_mem_cons.2 ⟨subd5_6_49, List.forall_mem_cons.2 ⟨subd5_6_50, List.forall_mem_cons.2 ⟨subd5_6_51, List.forall_mem_cons.2 ⟨subd5_6_52, List.forall_mem_cons.2 ⟨subd5_6_53, List.forall_mem_cons.2 ⟨subd5_6_54, List.forall_mem_cons.2 ⟨subd5_6_55, List.forall_mem_cons.2 ⟨subd5_6_56, List.forall_mem_cons.2 ⟨subd5_6_57, List.forall_mem_cons.2 ⟨subd5_6_58, List.forall_mem_cons.2 ⟨subd5_6_59, List.forall_mem_cons.2 ⟨subd5_6_60, List.forall_mem_cons.2 ⟨subd5_6_61, List.forall_mem_cons.2 ⟨subd5_6_62, List.forall_mem_cons.2 ⟨subd5_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_64 : subd5_6 [-2, -2, 3] = true := by decide +kernel
theorem subd5_6_65 : subd5_6 [-2, -2, 4] = true := by decide +kernel
theorem subd5_6_66 : subd5_6 [-2, -2, 5] = true := by decide +kernel
theorem subd5_6_67 : subd5_6 [-2, -1, -7] = true := by decide +kernel
theorem subd5_6_68 : subd5_6 [-2, -1, -6] = true := by decide +kernel
theorem subd5_6_69 : subd5_6 [-2, -1, -5] = true := by decide +kernel
theorem subd5_6_70 : subd5_6 [-2, -1, -4] = true := by decide +kernel
theorem subd5_6_71 : subd5_6 [-2, -1, -3] = true := by decide +kernel
theorem subd5_6_72 : subd5_6 [-2, -1, -2] = true := by decide +kernel
theorem subd5_6_73 : subd5_6 [-2, -1, -1] = true := by decide +kernel
theorem subd5_6_74 : subd5_6 [-2, -1, 0] = true := by decide +kernel
theorem subd5_6_75 : subd5_6 [-2, -1, 1] = true := by decide +kernel
theorem subd5_6_76 : subd5_6 [-2, -1, 2] = true := by decide +kernel
theorem subd5_6_77 : subd5_6 [-2, -1, 3] = true := by decide +kernel
theorem subd5_6_78 : subd5_6 [-2, -1, 4] = true := by decide +kernel
theorem subd5_6_79 : subd5_6 [-2, -1, 5] = true := by decide +kernel
theorem subd5_6_80 : subd5_6 [-2, -1, 6] = true := by decide +kernel
theorem subd5_6_81 : subd5_6 [-2, 0, -7] = true := by decide +kernel
theorem subd5_6_82 : subd5_6 [-2, 0, -6] = true := by decide +kernel
theorem subd5_6_83 : subd5_6 [-2, 0, -5] = true := by decide +kernel
theorem subd5_6_84 : subd5_6 [-2, 0, -4] = true := by decide +kernel
theorem subd5_6_85 : subd5_6 [-2, 0, -3] = true := by decide +kernel
theorem subd5_6_86 : subd5_6 [-2, 0, -2] = true := by decide +kernel
theorem subd5_6_87 : subd5_6 [-2, 0, -1] = true := by decide +kernel
theorem subd5_6_88 : subd5_6 [-2, 0, 0] = true := by decide +kernel
theorem subd5_6_89 : subd5_6 [-2, 0, 1] = true := by decide +kernel
theorem subd5_6_90 : subd5_6 [-2, 0, 2] = true := by decide +kernel
theorem subd5_6_91 : subd5_6 [-2, 0, 3] = true := by decide +kernel
theorem subd5_6_92 : subd5_6 [-2, 0, 4] = true := by decide +kernel
theorem subd5_6_93 : subd5_6 [-2, 0, 5] = true := by decide +kernel
theorem subd5_6_94 : subd5_6 [-2, 0, 6] = true := by decide +kernel
theorem subd5_6_95 : subd5_6 [-2, 1, -7] = true := by decide +kernel
theorem sbd5_6_2 : ∀ q ∈ blkd5_6_2, subd5_6 q = true := by
  unfold blkd5_6_2
  exact List.forall_mem_cons.2 ⟨subd5_6_64, List.forall_mem_cons.2 ⟨subd5_6_65, List.forall_mem_cons.2 ⟨subd5_6_66, List.forall_mem_cons.2 ⟨subd5_6_67, List.forall_mem_cons.2 ⟨subd5_6_68, List.forall_mem_cons.2 ⟨subd5_6_69, List.forall_mem_cons.2 ⟨subd5_6_70, List.forall_mem_cons.2 ⟨subd5_6_71, List.forall_mem_cons.2 ⟨subd5_6_72, List.forall_mem_cons.2 ⟨subd5_6_73, List.forall_mem_cons.2 ⟨subd5_6_74, List.forall_mem_cons.2 ⟨subd5_6_75, List.forall_mem_cons.2 ⟨subd5_6_76, List.forall_mem_cons.2 ⟨subd5_6_77, List.forall_mem_cons.2 ⟨subd5_6_78, List.forall_mem_cons.2 ⟨subd5_6_79, List.forall_mem_cons.2 ⟨subd5_6_80, List.forall_mem_cons.2 ⟨subd5_6_81, List.forall_mem_cons.2 ⟨subd5_6_82, List.forall_mem_cons.2 ⟨subd5_6_83, List.forall_mem_cons.2 ⟨subd5_6_84, List.forall_mem_cons.2 ⟨subd5_6_85, List.forall_mem_cons.2 ⟨subd5_6_86, List.forall_mem_cons.2 ⟨subd5_6_87, List.forall_mem_cons.2 ⟨subd5_6_88, List.forall_mem_cons.2 ⟨subd5_6_89, List.forall_mem_cons.2 ⟨subd5_6_90, List.forall_mem_cons.2 ⟨subd5_6_91, List.forall_mem_cons.2 ⟨subd5_6_92, List.forall_mem_cons.2 ⟨subd5_6_93, List.forall_mem_cons.2 ⟨subd5_6_94, List.forall_mem_cons.2 ⟨subd5_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_96 : subd5_6 [-2, 1, -6] = true := by decide +kernel
theorem subd5_6_97 : subd5_6 [-2, 1, -5] = true := by decide +kernel
theorem subd5_6_98 : subd5_6 [-2, 1, -4] = true := by decide +kernel
theorem subd5_6_99 : subd5_6 [-2, 1, -3] = true := by decide +kernel
theorem subd5_6_100 : subd5_6 [-2, 1, -2] = true := by decide +kernel
theorem subd5_6_101 : subd5_6 [-2, 1, -1] = true := by decide +kernel
theorem subd5_6_102 : subd5_6 [-2, 1, 0] = true := by decide +kernel
theorem subd5_6_103 : subd5_6 [-2, 1, 1] = true := by decide +kernel
theorem subd5_6_104 : subd5_6 [-2, 1, 2] = true := by decide +kernel
theorem subd5_6_105 : subd5_6 [-2, 1, 3] = true := by decide +kernel
theorem subd5_6_106 : subd5_6 [-2, 1, 4] = true := by decide +kernel
theorem subd5_6_107 : subd5_6 [-2, 1, 5] = true := by decide +kernel
theorem subd5_6_108 : subd5_6 [-2, 1, 6] = true := by decide +kernel
theorem subd5_6_109 : subd5_6 [-2, 2] = true := by decide +kernel
theorem subd5_6_110 : subd5_6 [-2, 3] = true := by decide +kernel
theorem subd5_6_111 : subd5_6 [-2, 4] = true := by decide +kernel
theorem subd5_6_112 : subd5_6 [-2, 5] = true := by decide +kernel
theorem subd5_6_113 : subd5_6 [-1, -7] = true := by decide +kernel
theorem subd5_6_114 : subd5_6 [-1, -6] = true := by decide +kernel
theorem subd5_6_115 : subd5_6 [-1, -5] = true := by decide +kernel
theorem subd5_6_116 : subd5_6 [-1, -4] = true := by decide +kernel
theorem subd5_6_117 : subd5_6 [-1, -3] = true := by decide +kernel
theorem subd5_6_118 : subd5_6 [-1, -2, -8] = true := by decide +kernel
theorem subd5_6_119 : subd5_6 [-1, -2, -7] = true := by decide +kernel
theorem subd5_6_120 : subd5_6 [-1, -2, -6] = true := by decide +kernel
theorem subd5_6_121 : subd5_6 [-1, -2, -5] = true := by decide +kernel
theorem subd5_6_122 : subd5_6 [-1, -2, -4] = true := by decide +kernel
theorem subd5_6_123 : subd5_6 [-1, -2, -3] = true := by decide +kernel
theorem subd5_6_124 : subd5_6 [-1, -2, -2] = true := by decide +kernel
theorem subd5_6_125 : subd5_6 [-1, -2, -1] = true := by decide +kernel
theorem subd5_6_126 : subd5_6 [-1, -2, 0] = true := by decide +kernel
theorem subd5_6_127 : subd5_6 [-1, -2, 1] = true := by decide +kernel
theorem sbd5_6_3 : ∀ q ∈ blkd5_6_3, subd5_6 q = true := by
  unfold blkd5_6_3
  exact List.forall_mem_cons.2 ⟨subd5_6_96, List.forall_mem_cons.2 ⟨subd5_6_97, List.forall_mem_cons.2 ⟨subd5_6_98, List.forall_mem_cons.2 ⟨subd5_6_99, List.forall_mem_cons.2 ⟨subd5_6_100, List.forall_mem_cons.2 ⟨subd5_6_101, List.forall_mem_cons.2 ⟨subd5_6_102, List.forall_mem_cons.2 ⟨subd5_6_103, List.forall_mem_cons.2 ⟨subd5_6_104, List.forall_mem_cons.2 ⟨subd5_6_105, List.forall_mem_cons.2 ⟨subd5_6_106, List.forall_mem_cons.2 ⟨subd5_6_107, List.forall_mem_cons.2 ⟨subd5_6_108, List.forall_mem_cons.2 ⟨subd5_6_109, List.forall_mem_cons.2 ⟨subd5_6_110, List.forall_mem_cons.2 ⟨subd5_6_111, List.forall_mem_cons.2 ⟨subd5_6_112, List.forall_mem_cons.2 ⟨subd5_6_113, List.forall_mem_cons.2 ⟨subd5_6_114, List.forall_mem_cons.2 ⟨subd5_6_115, List.forall_mem_cons.2 ⟨subd5_6_116, List.forall_mem_cons.2 ⟨subd5_6_117, List.forall_mem_cons.2 ⟨subd5_6_118, List.forall_mem_cons.2 ⟨subd5_6_119, List.forall_mem_cons.2 ⟨subd5_6_120, List.forall_mem_cons.2 ⟨subd5_6_121, List.forall_mem_cons.2 ⟨subd5_6_122, List.forall_mem_cons.2 ⟨subd5_6_123, List.forall_mem_cons.2 ⟨subd5_6_124, List.forall_mem_cons.2 ⟨subd5_6_125, List.forall_mem_cons.2 ⟨subd5_6_126, List.forall_mem_cons.2 ⟨subd5_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_128 : subd5_6 [-1, -2, 2] = true := by decide +kernel
theorem subd5_6_129 : subd5_6 [-1, -2, 3] = true := by decide +kernel
theorem subd5_6_130 : subd5_6 [-1, -2, 4] = true := by decide +kernel
theorem subd5_6_131 : subd5_6 [-1, -2, 5] = true := by decide +kernel
theorem subd5_6_132 : subd5_6 [-1, -1, -8] = true := by decide +kernel
theorem subd5_6_133 : subd5_6 [-1, -1, -7] = true := by decide +kernel
theorem subd5_6_134 : subd5_6 [-1, -1, -6] = true := by decide +kernel
theorem subd5_6_135 : subd5_6 [-1, -1, -5] = true := by decide +kernel
theorem subd5_6_136 : subd5_6 [-1, -1, -4] = true := by decide +kernel
theorem subd5_6_137 : subd5_6 [-1, -1, -3] = true := by decide +kernel
theorem subd5_6_138 : subd5_6 [-1, -1, -2] = true := by decide +kernel
theorem subd5_6_139 : subd5_6 [-1, -1, -1] = true := by decide +kernel
theorem subd5_6_140 : subd5_6 [-1, -1, 0] = true := by decide +kernel
theorem subd5_6_141 : subd5_6 [-1, -1, 1] = true := by decide +kernel
theorem subd5_6_142 : subd5_6 [-1, -1, 2] = true := by decide +kernel
theorem subd5_6_143 : subd5_6 [-1, -1, 3] = true := by decide +kernel
theorem subd5_6_144 : subd5_6 [-1, -1, 4] = true := by decide +kernel
theorem subd5_6_145 : subd5_6 [-1, -1, 5] = true := by decide +kernel
theorem subd5_6_146 : subd5_6 [-1, -1, 6] = true := by decide +kernel
theorem subd5_6_147 : subd5_6 [-1, 0, -7] = true := by decide +kernel
theorem subd5_6_148 : subd5_6 [-1, 0, -6] = true := by decide +kernel
theorem subd5_6_149 : subd5_6 [-1, 0, -5] = true := by decide +kernel
theorem subd5_6_150 : subd5_6 [-1, 0, -4] = true := by decide +kernel
theorem subd5_6_151 : subd5_6 [-1, 0, -3] = true := by decide +kernel
theorem subd5_6_152 : subd5_6 [-1, 0, -2] = true := by decide +kernel
theorem subd5_6_153 : subd5_6 [-1, 0, -1] = true := by decide +kernel
theorem subd5_6_154 : subd5_6 [-1, 0, 0] = true := by decide +kernel
theorem subd5_6_155 : subd5_6 [-1, 0, 1] = true := by decide +kernel
theorem subd5_6_156 : subd5_6 [-1, 0, 2] = true := by decide +kernel
theorem subd5_6_157 : subd5_6 [-1, 0, 3] = true := by decide +kernel
theorem subd5_6_158 : subd5_6 [-1, 0, 4] = true := by decide +kernel
theorem subd5_6_159 : subd5_6 [-1, 0, 5] = true := by decide +kernel
theorem sbd5_6_4 : ∀ q ∈ blkd5_6_4, subd5_6 q = true := by
  unfold blkd5_6_4
  exact List.forall_mem_cons.2 ⟨subd5_6_128, List.forall_mem_cons.2 ⟨subd5_6_129, List.forall_mem_cons.2 ⟨subd5_6_130, List.forall_mem_cons.2 ⟨subd5_6_131, List.forall_mem_cons.2 ⟨subd5_6_132, List.forall_mem_cons.2 ⟨subd5_6_133, List.forall_mem_cons.2 ⟨subd5_6_134, List.forall_mem_cons.2 ⟨subd5_6_135, List.forall_mem_cons.2 ⟨subd5_6_136, List.forall_mem_cons.2 ⟨subd5_6_137, List.forall_mem_cons.2 ⟨subd5_6_138, List.forall_mem_cons.2 ⟨subd5_6_139, List.forall_mem_cons.2 ⟨subd5_6_140, List.forall_mem_cons.2 ⟨subd5_6_141, List.forall_mem_cons.2 ⟨subd5_6_142, List.forall_mem_cons.2 ⟨subd5_6_143, List.forall_mem_cons.2 ⟨subd5_6_144, List.forall_mem_cons.2 ⟨subd5_6_145, List.forall_mem_cons.2 ⟨subd5_6_146, List.forall_mem_cons.2 ⟨subd5_6_147, List.forall_mem_cons.2 ⟨subd5_6_148, List.forall_mem_cons.2 ⟨subd5_6_149, List.forall_mem_cons.2 ⟨subd5_6_150, List.forall_mem_cons.2 ⟨subd5_6_151, List.forall_mem_cons.2 ⟨subd5_6_152, List.forall_mem_cons.2 ⟨subd5_6_153, List.forall_mem_cons.2 ⟨subd5_6_154, List.forall_mem_cons.2 ⟨subd5_6_155, List.forall_mem_cons.2 ⟨subd5_6_156, List.forall_mem_cons.2 ⟨subd5_6_157, List.forall_mem_cons.2 ⟨subd5_6_158, List.forall_mem_cons.2 ⟨subd5_6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
