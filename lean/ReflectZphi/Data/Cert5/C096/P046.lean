import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_2_416 : subd11_2 [1, 1, 4] = true := by decide +kernel
theorem subd11_2_417 : subd11_2 [1, 1, 5] = true := by decide +kernel
theorem subd11_2_418 : subd11_2 [1, 1, 6] = true := by decide +kernel
theorem subd11_2_419 : subd11_2 [1, 1, 7] = true := by decide +kernel
theorem subd11_2_420 : subd11_2 [1, 1, 8] = true := by decide +kernel
theorem subd11_2_421 : subd11_2 [1, 2, -8] = true := by decide +kernel
theorem subd11_2_422 : subd11_2 [1, 2, -7] = true := by decide +kernel
theorem subd11_2_423 : subd11_2 [1, 2, -6] = true := by decide +kernel
theorem subd11_2_424 : subd11_2 [1, 2, -5] = true := by decide +kernel
theorem subd11_2_425 : subd11_2 [1, 2, -4] = true := by decide +kernel
theorem subd11_2_426 : subd11_2 [1, 2, -3] = true := by decide +kernel
theorem subd11_2_427 : subd11_2 [1, 2, -2] = true := by decide +kernel
theorem subd11_2_428 : subd11_2 [1, 2, -1] = true := by decide +kernel
theorem subd11_2_429 : subd11_2 [1, 2, 0] = true := by decide +kernel
theorem subd11_2_430 : subd11_2 [1, 2, 1] = true := by decide +kernel
theorem subd11_2_431 : subd11_2 [1, 2, 2] = true := by decide +kernel
theorem subd11_2_432 : subd11_2 [1, 2, 3] = true := by decide +kernel
theorem subd11_2_433 : subd11_2 [1, 2, 4] = true := by decide +kernel
theorem subd11_2_434 : subd11_2 [1, 2, 5] = true := by decide +kernel
theorem subd11_2_435 : subd11_2 [1, 2, 6] = true := by decide +kernel
theorem subd11_2_436 : subd11_2 [1, 2, 7] = true := by decide +kernel
theorem subd11_2_437 : subd11_2 [1, 3] = true := by decide +kernel
theorem subd11_2_438 : subd11_2 [2, -5] = true := by decide +kernel
theorem subd11_2_439 : subd11_2 [2, -4] = true := by decide +kernel
theorem subd11_2_440 : subd11_2 [2, -3, -7] = true := by decide +kernel
theorem subd11_2_441 : subd11_2 [2, -3, -6] = true := by decide +kernel
theorem subd11_2_442 : subd11_2 [2, -3, -5] = true := by decide +kernel
theorem subd11_2_443 : subd11_2 [2, -3, -4] = true := by decide +kernel
theorem subd11_2_444 : subd11_2 [2, -3, -3] = true := by decide +kernel
theorem subd11_2_445 : subd11_2 [2, -3, -2] = true := by decide +kernel
theorem subd11_2_446 : subd11_2 [2, -3, -1] = true := by decide +kernel
theorem subd11_2_447 : subd11_2 [2, -3, 0] = true := by decide +kernel
theorem sbd11_2_13 : ∀ q ∈ blkd11_2_13, subd11_2 q = true := by
  unfold blkd11_2_13
  exact List.forall_mem_cons.2 ⟨subd11_2_416, List.forall_mem_cons.2 ⟨subd11_2_417, List.forall_mem_cons.2 ⟨subd11_2_418, List.forall_mem_cons.2 ⟨subd11_2_419, List.forall_mem_cons.2 ⟨subd11_2_420, List.forall_mem_cons.2 ⟨subd11_2_421, List.forall_mem_cons.2 ⟨subd11_2_422, List.forall_mem_cons.2 ⟨subd11_2_423, List.forall_mem_cons.2 ⟨subd11_2_424, List.forall_mem_cons.2 ⟨subd11_2_425, List.forall_mem_cons.2 ⟨subd11_2_426, List.forall_mem_cons.2 ⟨subd11_2_427, List.forall_mem_cons.2 ⟨subd11_2_428, List.forall_mem_cons.2 ⟨subd11_2_429, List.forall_mem_cons.2 ⟨subd11_2_430, List.forall_mem_cons.2 ⟨subd11_2_431, List.forall_mem_cons.2 ⟨subd11_2_432, List.forall_mem_cons.2 ⟨subd11_2_433, List.forall_mem_cons.2 ⟨subd11_2_434, List.forall_mem_cons.2 ⟨subd11_2_435, List.forall_mem_cons.2 ⟨subd11_2_436, List.forall_mem_cons.2 ⟨subd11_2_437, List.forall_mem_cons.2 ⟨subd11_2_438, List.forall_mem_cons.2 ⟨subd11_2_439, List.forall_mem_cons.2 ⟨subd11_2_440, List.forall_mem_cons.2 ⟨subd11_2_441, List.forall_mem_cons.2 ⟨subd11_2_442, List.forall_mem_cons.2 ⟨subd11_2_443, List.forall_mem_cons.2 ⟨subd11_2_444, List.forall_mem_cons.2 ⟨subd11_2_445, List.forall_mem_cons.2 ⟨subd11_2_446, List.forall_mem_cons.2 ⟨subd11_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_448 : subd11_2 [2, -3, 1] = true := by decide +kernel
theorem subd11_2_449 : subd11_2 [2, -3, 2] = true := by decide +kernel
theorem subd11_2_450 : subd11_2 [2, -3, 3] = true := by decide +kernel
theorem subd11_2_451 : subd11_2 [2, -3, 4] = true := by decide +kernel
theorem subd11_2_452 : subd11_2 [2, -3, 5] = true := by decide +kernel
theorem subd11_2_453 : subd11_2 [2, -3, 6] = true := by decide +kernel
theorem subd11_2_454 : subd11_2 [2, -2, -8] = true := by decide +kernel
theorem subd11_2_455 : subd11_2 [2, -2, -7] = true := by decide +kernel
theorem subd11_2_456 : subd11_2 [2, -2, -6] = true := by decide +kernel
theorem subd11_2_457 : subd11_2 [2, -2, -5] = true := by decide +kernel
theorem subd11_2_458 : subd11_2 [2, -2, -4] = true := by decide +kernel
theorem subd11_2_459 : subd11_2 [2, -2, -3] = true := by decide +kernel
theorem subd11_2_460 : subd11_2 [2, -2, -2] = true := by decide +kernel
theorem subd11_2_461 : subd11_2 [2, -2, -1] = true := by decide +kernel
theorem subd11_2_462 : subd11_2 [2, -2, 0] = true := by decide +kernel
theorem subd11_2_463 : subd11_2 [2, -2, 1] = true := by decide +kernel
theorem subd11_2_464 : subd11_2 [2, -2, 2] = true := by decide +kernel
theorem subd11_2_465 : subd11_2 [2, -2, 3] = true := by decide +kernel
theorem subd11_2_466 : subd11_2 [2, -2, 4] = true := by decide +kernel
theorem subd11_2_467 : subd11_2 [2, -2, 5] = true := by decide +kernel
theorem subd11_2_468 : subd11_2 [2, -2, 6] = true := by decide +kernel
theorem subd11_2_469 : subd11_2 [2, -2, 7] = true := by decide +kernel
theorem subd11_2_470 : subd11_2 [2, -1, -9] = true := by decide +kernel
theorem subd11_2_471 : subd11_2 [2, -1, -8] = true := by decide +kernel
theorem subd11_2_472 : subd11_2 [2, -1, -7] = true := by decide +kernel
theorem subd11_2_473 : subd11_2 [2, -1, -6] = true := by decide +kernel
theorem subd11_2_474 : subd11_2 [2, -1, -5] = true := by decide +kernel
theorem subd11_2_475 : subd11_2 [2, -1, -4] = true := by decide +kernel
theorem subd11_2_476 : subd11_2 [2, -1, -3] = true := by decide +kernel
theorem subd11_2_477 : subd11_2 [2, -1, -2] = true := by decide +kernel
theorem subd11_2_478 : subd11_2 [2, -1, -1] = true := by decide +kernel
theorem subd11_2_479 : subd11_2 [2, -1, 0] = true := by decide +kernel
theorem sbd11_2_14 : ∀ q ∈ blkd11_2_14, subd11_2 q = true := by
  unfold blkd11_2_14
  exact List.forall_mem_cons.2 ⟨subd11_2_448, List.forall_mem_cons.2 ⟨subd11_2_449, List.forall_mem_cons.2 ⟨subd11_2_450, List.forall_mem_cons.2 ⟨subd11_2_451, List.forall_mem_cons.2 ⟨subd11_2_452, List.forall_mem_cons.2 ⟨subd11_2_453, List.forall_mem_cons.2 ⟨subd11_2_454, List.forall_mem_cons.2 ⟨subd11_2_455, List.forall_mem_cons.2 ⟨subd11_2_456, List.forall_mem_cons.2 ⟨subd11_2_457, List.forall_mem_cons.2 ⟨subd11_2_458, List.forall_mem_cons.2 ⟨subd11_2_459, List.forall_mem_cons.2 ⟨subd11_2_460, List.forall_mem_cons.2 ⟨subd11_2_461, List.forall_mem_cons.2 ⟨subd11_2_462, List.forall_mem_cons.2 ⟨subd11_2_463, List.forall_mem_cons.2 ⟨subd11_2_464, List.forall_mem_cons.2 ⟨subd11_2_465, List.forall_mem_cons.2 ⟨subd11_2_466, List.forall_mem_cons.2 ⟨subd11_2_467, List.forall_mem_cons.2 ⟨subd11_2_468, List.forall_mem_cons.2 ⟨subd11_2_469, List.forall_mem_cons.2 ⟨subd11_2_470, List.forall_mem_cons.2 ⟨subd11_2_471, List.forall_mem_cons.2 ⟨subd11_2_472, List.forall_mem_cons.2 ⟨subd11_2_473, List.forall_mem_cons.2 ⟨subd11_2_474, List.forall_mem_cons.2 ⟨subd11_2_475, List.forall_mem_cons.2 ⟨subd11_2_476, List.forall_mem_cons.2 ⟨subd11_2_477, List.forall_mem_cons.2 ⟨subd11_2_478, List.forall_mem_cons.2 ⟨subd11_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_480 : subd11_2 [2, -1, 1] = true := by decide +kernel
theorem subd11_2_481 : subd11_2 [2, -1, 2] = true := by decide +kernel
theorem subd11_2_482 : subd11_2 [2, -1, 3] = true := by decide +kernel
theorem subd11_2_483 : subd11_2 [2, -1, 4] = true := by decide +kernel
theorem subd11_2_484 : subd11_2 [2, -1, 5] = true := by decide +kernel
theorem subd11_2_485 : subd11_2 [2, -1, 6] = true := by decide +kernel
theorem subd11_2_486 : subd11_2 [2, -1, 7] = true := by decide +kernel
theorem subd11_2_487 : subd11_2 [2, -1, 8] = true := by decide +kernel
theorem subd11_2_488 : subd11_2 [2, 0, -9] = true := by decide +kernel
theorem subd11_2_489 : subd11_2 [2, 0, -8] = true := by decide +kernel
theorem subd11_2_490 : subd11_2 [2, 0, -7] = true := by decide +kernel
theorem subd11_2_491 : subd11_2 [2, 0, -6] = true := by decide +kernel
theorem subd11_2_492 : subd11_2 [2, 0, -5] = true := by decide +kernel
theorem subd11_2_493 : subd11_2 [2, 0, -4] = true := by decide +kernel
theorem subd11_2_494 : subd11_2 [2, 0, -3] = true := by decide +kernel
theorem subd11_2_495 : subd11_2 [2, 0, -2] = true := by decide +kernel
theorem subd11_2_496 : subd11_2 [2, 0, -1] = true := by decide +kernel
theorem subd11_2_497 : subd11_2 [2, 0, 0] = true := by decide +kernel
theorem subd11_2_498 : subd11_2 [2, 0, 1] = true := by decide +kernel
theorem subd11_2_499 : subd11_2 [2, 0, 2] = true := by decide +kernel
theorem subd11_2_500 : subd11_2 [2, 0, 3] = true := by decide +kernel
theorem subd11_2_501 : subd11_2 [2, 0, 4] = true := by decide +kernel
theorem subd11_2_502 : subd11_2 [2, 0, 5] = true := by decide +kernel
theorem subd11_2_503 : subd11_2 [2, 0, 6] = true := by decide +kernel
theorem subd11_2_504 : subd11_2 [2, 0, 7] = true := by decide +kernel
theorem subd11_2_505 : subd11_2 [2, 1, -8] = true := by decide +kernel
theorem subd11_2_506 : subd11_2 [2, 1, -7] = true := by decide +kernel
theorem subd11_2_507 : subd11_2 [2, 1, -6] = true := by decide +kernel
theorem subd11_2_508 : subd11_2 [2, 1, -5] = true := by decide +kernel
theorem subd11_2_509 : subd11_2 [2, 1, -4] = true := by decide +kernel
theorem subd11_2_510 : subd11_2 [2, 1, -3] = true := by decide +kernel
theorem subd11_2_511 : subd11_2 [2, 1, -2] = true := by decide +kernel
theorem sbd11_2_15 : ∀ q ∈ blkd11_2_15, subd11_2 q = true := by
  unfold blkd11_2_15
  exact List.forall_mem_cons.2 ⟨subd11_2_480, List.forall_mem_cons.2 ⟨subd11_2_481, List.forall_mem_cons.2 ⟨subd11_2_482, List.forall_mem_cons.2 ⟨subd11_2_483, List.forall_mem_cons.2 ⟨subd11_2_484, List.forall_mem_cons.2 ⟨subd11_2_485, List.forall_mem_cons.2 ⟨subd11_2_486, List.forall_mem_cons.2 ⟨subd11_2_487, List.forall_mem_cons.2 ⟨subd11_2_488, List.forall_mem_cons.2 ⟨subd11_2_489, List.forall_mem_cons.2 ⟨subd11_2_490, List.forall_mem_cons.2 ⟨subd11_2_491, List.forall_mem_cons.2 ⟨subd11_2_492, List.forall_mem_cons.2 ⟨subd11_2_493, List.forall_mem_cons.2 ⟨subd11_2_494, List.forall_mem_cons.2 ⟨subd11_2_495, List.forall_mem_cons.2 ⟨subd11_2_496, List.forall_mem_cons.2 ⟨subd11_2_497, List.forall_mem_cons.2 ⟨subd11_2_498, List.forall_mem_cons.2 ⟨subd11_2_499, List.forall_mem_cons.2 ⟨subd11_2_500, List.forall_mem_cons.2 ⟨subd11_2_501, List.forall_mem_cons.2 ⟨subd11_2_502, List.forall_mem_cons.2 ⟨subd11_2_503, List.forall_mem_cons.2 ⟨subd11_2_504, List.forall_mem_cons.2 ⟨subd11_2_505, List.forall_mem_cons.2 ⟨subd11_2_506, List.forall_mem_cons.2 ⟨subd11_2_507, List.forall_mem_cons.2 ⟨subd11_2_508, List.forall_mem_cons.2 ⟨subd11_2_509, List.forall_mem_cons.2 ⟨subd11_2_510, List.forall_mem_cons.2 ⟨subd11_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_512 : subd11_2 [2, 1, -1] = true := by decide +kernel
theorem subd11_2_513 : subd11_2 [2, 1, 0] = true := by decide +kernel
theorem subd11_2_514 : subd11_2 [2, 1, 1] = true := by decide +kernel
theorem subd11_2_515 : subd11_2 [2, 1, 2] = true := by decide +kernel
theorem subd11_2_516 : subd11_2 [2, 1, 3] = true := by decide +kernel
theorem subd11_2_517 : subd11_2 [2, 1, 4] = true := by decide +kernel
theorem subd11_2_518 : subd11_2 [2, 1, 5] = true := by decide +kernel
theorem subd11_2_519 : subd11_2 [2, 1, 6] = true := by decide +kernel
theorem subd11_2_520 : subd11_2 [2, 1, 7] = true := by decide +kernel
theorem subd11_2_521 : subd11_2 [2, 2] = true := by decide +kernel
theorem subd11_2_522 : subd11_2 [2, 3] = true := by decide +kernel
theorem subd11_2_523 : subd11_2 [3, -4] = true := by decide +kernel
theorem subd11_2_524 : subd11_2 [3, -3] = true := by decide +kernel
theorem subd11_2_525 : subd11_2 [3, -2] = true := by decide +kernel
theorem subd11_2_526 : subd11_2 [3, -1] = true := by decide +kernel
theorem subd11_2_527 : subd11_2 [3, 0] = true := by decide +kernel
theorem subd11_2_528 : subd11_2 [3, 1] = true := by decide +kernel
theorem sbd11_2_16 : ∀ q ∈ blkd11_2_16, subd11_2 q = true := by
  unfold blkd11_2_16
  exact List.forall_mem_cons.2 ⟨subd11_2_512, List.forall_mem_cons.2 ⟨subd11_2_513, List.forall_mem_cons.2 ⟨subd11_2_514, List.forall_mem_cons.2 ⟨subd11_2_515, List.forall_mem_cons.2 ⟨subd11_2_516, List.forall_mem_cons.2 ⟨subd11_2_517, List.forall_mem_cons.2 ⟨subd11_2_518, List.forall_mem_cons.2 ⟨subd11_2_519, List.forall_mem_cons.2 ⟨subd11_2_520, List.forall_mem_cons.2 ⟨subd11_2_521, List.forall_mem_cons.2 ⟨subd11_2_522, List.forall_mem_cons.2 ⟨subd11_2_523, List.forall_mem_cons.2 ⟨subd11_2_524, List.forall_mem_cons.2 ⟨subd11_2_525, List.forall_mem_cons.2 ⟨subd11_2_526, List.forall_mem_cons.2 ⟨subd11_2_527, List.forall_mem_cons.2 ⟨subd11_2_528, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel
theorem subd11_3_0 : subd11_3 [-5, -6] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-5, -5] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [-5, -4] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [-5, -3] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [-5, -2] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [-5, -1] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [-5, 0] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [-5, 1] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [-4, -7] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [-4, -6] = true := by decide +kernel
theorem subd11_3_10 : subd11_3 [-4, -5] = true := by decide +kernel
theorem subd11_3_11 : subd11_3 [-4, -4] = true := by decide +kernel
theorem subd11_3_12 : subd11_3 [-4, -3] = true := by decide +kernel
theorem subd11_3_13 : subd11_3 [-4, -2] = true := by decide +kernel
theorem subd11_3_14 : subd11_3 [-4, -1] = true := by decide +kernel
theorem subd11_3_15 : subd11_3 [-4, 0] = true := by decide +kernel
theorem subd11_3_16 : subd11_3 [-4, 1] = true := by decide +kernel
theorem subd11_3_17 : subd11_3 [-4, 2] = true := by decide +kernel
theorem subd11_3_18 : subd11_3 [-3, -7] = true := by decide +kernel
theorem subd11_3_19 : subd11_3 [-3, -6] = true := by decide +kernel
theorem subd11_3_20 : subd11_3 [-3, -5] = true := by decide +kernel
theorem subd11_3_21 : subd11_3 [-3, -4] = true := by decide +kernel
theorem subd11_3_22 : subd11_3 [-3, -3] = true := by decide +kernel
theorem subd11_3_23 : subd11_3 [-3, -2] = true := by decide +kernel
theorem subd11_3_24 : subd11_3 [-3, -1] = true := by decide +kernel
theorem subd11_3_25 : subd11_3 [-3, 0] = true := by decide +kernel
theorem subd11_3_26 : subd11_3 [-3, 1] = true := by decide +kernel
theorem subd11_3_27 : subd11_3 [-3, 2] = true := by decide +kernel
theorem subd11_3_28 : subd11_3 [-3, 3] = true := by decide +kernel
theorem subd11_3_29 : subd11_3 [-3, 4] = true := by decide +kernel
theorem subd11_3_30 : subd11_3 [-2, -7] = true := by decide +kernel
theorem subd11_3_31 : subd11_3 [-2, -6] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_cons.2 ⟨subd11_3_10, List.forall_mem_cons.2 ⟨subd11_3_11, List.forall_mem_cons.2 ⟨subd11_3_12, List.forall_mem_cons.2 ⟨subd11_3_13, List.forall_mem_cons.2 ⟨subd11_3_14, List.forall_mem_cons.2 ⟨subd11_3_15, List.forall_mem_cons.2 ⟨subd11_3_16, List.forall_mem_cons.2 ⟨subd11_3_17, List.forall_mem_cons.2 ⟨subd11_3_18, List.forall_mem_cons.2 ⟨subd11_3_19, List.forall_mem_cons.2 ⟨subd11_3_20, List.forall_mem_cons.2 ⟨subd11_3_21, List.forall_mem_cons.2 ⟨subd11_3_22, List.forall_mem_cons.2 ⟨subd11_3_23, List.forall_mem_cons.2 ⟨subd11_3_24, List.forall_mem_cons.2 ⟨subd11_3_25, List.forall_mem_cons.2 ⟨subd11_3_26, List.forall_mem_cons.2 ⟨subd11_3_27, List.forall_mem_cons.2 ⟨subd11_3_28, List.forall_mem_cons.2 ⟨subd11_3_29, List.forall_mem_cons.2 ⟨subd11_3_30, List.forall_mem_cons.2 ⟨subd11_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_32 : subd11_3 [-2, -5] = true := by decide +kernel
theorem subd11_3_33 : subd11_3 [-2, -4] = true := by decide +kernel
theorem subd11_3_34 : subd11_3 [-2, -3] = true := by decide +kernel
theorem subd11_3_35 : subd11_3 [-2, -2] = true := by decide +kernel
theorem subd11_3_36 : subd11_3 [-2, -1] = true := by decide +kernel
theorem subd11_3_37 : subd11_3 [-2, 0] = true := by decide +kernel
theorem subd11_3_38 : subd11_3 [-2, 1] = true := by decide +kernel
theorem subd11_3_39 : subd11_3 [-2, 2] = true := by decide +kernel
theorem subd11_3_40 : subd11_3 [-2, 3] = true := by decide +kernel
theorem subd11_3_41 : subd11_3 [-2, 4] = true := by decide +kernel
theorem subd11_3_42 : subd11_3 [-2, 5] = true := by decide +kernel
theorem subd11_3_43 : subd11_3 [-1, -7] = true := by decide +kernel
theorem subd11_3_44 : subd11_3 [-1, -6] = true := by decide +kernel
theorem subd11_3_45 : subd11_3 [-1, -5] = true := by decide +kernel
theorem subd11_3_46 : subd11_3 [-1, -4] = true := by decide +kernel
theorem subd11_3_47 : subd11_3 [-1, -3] = true := by decide +kernel
theorem subd11_3_48 : subd11_3 [-1, -2] = true := by decide +kernel
theorem subd11_3_49 : subd11_3 [-1, -1, -7] = true := by decide +kernel
theorem subd11_3_50 : subd11_3 [-1, -1, -6] = true := by decide +kernel
theorem subd11_3_51 : subd11_3 [-1, -1, -5] = true := by decide +kernel
theorem subd11_3_52 : subd11_3 [-1, -1, -4] = true := by decide +kernel
theorem subd11_3_53 : subd11_3 [-1, -1, -3] = true := by decide +kernel
theorem subd11_3_54 : subd11_3 [-1, -1, -2] = true := by decide +kernel
theorem subd11_3_55 : subd11_3 [-1, -1, -1] = true := by decide +kernel
theorem subd11_3_56 : subd11_3 [-1, -1, 0] = true := by decide +kernel
theorem subd11_3_57 : subd11_3 [-1, -1, 1] = true := by decide +kernel
theorem subd11_3_58 : subd11_3 [-1, -1, 2] = true := by decide +kernel
theorem subd11_3_59 : subd11_3 [-1, -1, 3] = true := by decide +kernel
theorem subd11_3_60 : subd11_3 [-1, -1, 4] = true := by decide +kernel
theorem subd11_3_61 : subd11_3 [-1, -1, 5] = true := by decide +kernel
theorem subd11_3_62 : subd11_3 [-1, -1, 6] = true := by decide +kernel
theorem subd11_3_63 : subd11_3 [-1, 0, -7] = true := by decide +kernel
theorem sbd11_3_1 : ∀ q ∈ blkd11_3_1, subd11_3 q = true := by
  unfold blkd11_3_1
  exact List.forall_mem_cons.2 ⟨subd11_3_32, List.forall_mem_cons.2 ⟨subd11_3_33, List.forall_mem_cons.2 ⟨subd11_3_34, List.forall_mem_cons.2 ⟨subd11_3_35, List.forall_mem_cons.2 ⟨subd11_3_36, List.forall_mem_cons.2 ⟨subd11_3_37, List.forall_mem_cons.2 ⟨subd11_3_38, List.forall_mem_cons.2 ⟨subd11_3_39, List.forall_mem_cons.2 ⟨subd11_3_40, List.forall_mem_cons.2 ⟨subd11_3_41, List.forall_mem_cons.2 ⟨subd11_3_42, List.forall_mem_cons.2 ⟨subd11_3_43, List.forall_mem_cons.2 ⟨subd11_3_44, List.forall_mem_cons.2 ⟨subd11_3_45, List.forall_mem_cons.2 ⟨subd11_3_46, List.forall_mem_cons.2 ⟨subd11_3_47, List.forall_mem_cons.2 ⟨subd11_3_48, List.forall_mem_cons.2 ⟨subd11_3_49, List.forall_mem_cons.2 ⟨subd11_3_50, List.forall_mem_cons.2 ⟨subd11_3_51, List.forall_mem_cons.2 ⟨subd11_3_52, List.forall_mem_cons.2 ⟨subd11_3_53, List.forall_mem_cons.2 ⟨subd11_3_54, List.forall_mem_cons.2 ⟨subd11_3_55, List.forall_mem_cons.2 ⟨subd11_3_56, List.forall_mem_cons.2 ⟨subd11_3_57, List.forall_mem_cons.2 ⟨subd11_3_58, List.forall_mem_cons.2 ⟨subd11_3_59, List.forall_mem_cons.2 ⟨subd11_3_60, List.forall_mem_cons.2 ⟨subd11_3_61, List.forall_mem_cons.2 ⟨subd11_3_62, List.forall_mem_cons.2 ⟨subd11_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
