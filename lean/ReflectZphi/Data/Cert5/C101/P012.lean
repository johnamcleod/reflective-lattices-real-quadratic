import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_1_384 : subd10_1 [1, -1, 6] = true := by decide +kernel
theorem subd10_1_385 : subd10_1 [1, -1, 7] = true := by decide +kernel
theorem subd10_1_386 : subd10_1 [1, -1, 8] = true := by decide +kernel
theorem subd10_1_387 : subd10_1 [1, -1, 9] = true := by decide +kernel
theorem subd10_1_388 : subd10_1 [1, -1, 10] = true := by decide +kernel
theorem subd10_1_389 : subd10_1 [1, -1, 11] = true := by decide +kernel
theorem subd10_1_390 : subd10_1 [1, -1, 12] = true := by decide +kernel
theorem subd10_1_391 : subd10_1 [1, -1, 13] = true := by decide +kernel
theorem subd10_1_392 : subd10_1 [1, -1, 14] = true := by decide +kernel
theorem subd10_1_393 : subd10_1 [1, -1, 15] = true := by decide +kernel
theorem subd10_1_394 : subd10_1 [1, -1, 16] = true := by decide +kernel
theorem subd10_1_395 : subd10_1 [1, 0, -18] = true := by decide +kernel
theorem subd10_1_396 : subd10_1 [1, 0, -17] = true := by decide +kernel
theorem subd10_1_397 : subd10_1 [1, 0, -16] = true := by decide +kernel
theorem subd10_1_398 : subd10_1 [1, 0, -15] = true := by decide +kernel
theorem subd10_1_399 : subd10_1 [1, 0, -14] = true := by decide +kernel
theorem subd10_1_400 : subd10_1 [1, 0, -13] = true := by decide +kernel
theorem subd10_1_401 : subd10_1 [1, 0, -12] = true := by decide +kernel
theorem subd10_1_402 : subd10_1 [1, 0, -11] = true := by decide +kernel
theorem subd10_1_403 : subd10_1 [1, 0, -10] = true := by decide +kernel
theorem subd10_1_404 : subd10_1 [1, 0, -9] = true := by decide +kernel
theorem subd10_1_405 : subd10_1 [1, 0, -8] = true := by decide +kernel
theorem subd10_1_406 : subd10_1 [1, 0, -7] = true := by decide +kernel
theorem subd10_1_407 : subd10_1 [1, 0, -6] = true := by decide +kernel
theorem subd10_1_408 : subd10_1 [1, 0, -5] = true := by decide +kernel
theorem subd10_1_409 : subd10_1 [1, 0, -4] = true := by decide +kernel
theorem subd10_1_410 : subd10_1 [1, 0, -3] = true := by decide +kernel
theorem subd10_1_411 : subd10_1 [1, 0, -2] = true := by decide +kernel
theorem subd10_1_412 : subd10_1 [1, 0, -1] = true := by decide +kernel
theorem subd10_1_413 : subd10_1 [1, 0, 0] = true := by decide +kernel
theorem subd10_1_414 : subd10_1 [1, 0, 1] = true := by decide +kernel
theorem subd10_1_415 : subd10_1 [1, 0, 2] = true := by decide +kernel
theorem sbd10_1_12 : ∀ q ∈ blkd10_1_12, subd10_1 q = true := by
  unfold blkd10_1_12
  exact List.forall_mem_cons.2 ⟨subd10_1_384, List.forall_mem_cons.2 ⟨subd10_1_385, List.forall_mem_cons.2 ⟨subd10_1_386, List.forall_mem_cons.2 ⟨subd10_1_387, List.forall_mem_cons.2 ⟨subd10_1_388, List.forall_mem_cons.2 ⟨subd10_1_389, List.forall_mem_cons.2 ⟨subd10_1_390, List.forall_mem_cons.2 ⟨subd10_1_391, List.forall_mem_cons.2 ⟨subd10_1_392, List.forall_mem_cons.2 ⟨subd10_1_393, List.forall_mem_cons.2 ⟨subd10_1_394, List.forall_mem_cons.2 ⟨subd10_1_395, List.forall_mem_cons.2 ⟨subd10_1_396, List.forall_mem_cons.2 ⟨subd10_1_397, List.forall_mem_cons.2 ⟨subd10_1_398, List.forall_mem_cons.2 ⟨subd10_1_399, List.forall_mem_cons.2 ⟨subd10_1_400, List.forall_mem_cons.2 ⟨subd10_1_401, List.forall_mem_cons.2 ⟨subd10_1_402, List.forall_mem_cons.2 ⟨subd10_1_403, List.forall_mem_cons.2 ⟨subd10_1_404, List.forall_mem_cons.2 ⟨subd10_1_405, List.forall_mem_cons.2 ⟨subd10_1_406, List.forall_mem_cons.2 ⟨subd10_1_407, List.forall_mem_cons.2 ⟨subd10_1_408, List.forall_mem_cons.2 ⟨subd10_1_409, List.forall_mem_cons.2 ⟨subd10_1_410, List.forall_mem_cons.2 ⟨subd10_1_411, List.forall_mem_cons.2 ⟨subd10_1_412, List.forall_mem_cons.2 ⟨subd10_1_413, List.forall_mem_cons.2 ⟨subd10_1_414, List.forall_mem_cons.2 ⟨subd10_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_416 : subd10_1 [1, 0, 3] = true := by decide +kernel
theorem subd10_1_417 : subd10_1 [1, 0, 4] = true := by decide +kernel
theorem subd10_1_418 : subd10_1 [1, 0, 5] = true := by decide +kernel
theorem subd10_1_419 : subd10_1 [1, 0, 6] = true := by decide +kernel
theorem subd10_1_420 : subd10_1 [1, 0, 7] = true := by decide +kernel
theorem subd10_1_421 : subd10_1 [1, 0, 8] = true := by decide +kernel
theorem subd10_1_422 : subd10_1 [1, 0, 9] = true := by decide +kernel
theorem subd10_1_423 : subd10_1 [1, 0, 10] = true := by decide +kernel
theorem subd10_1_424 : subd10_1 [1, 0, 11] = true := by decide +kernel
theorem subd10_1_425 : subd10_1 [1, 0, 12] = true := by decide +kernel
theorem subd10_1_426 : subd10_1 [1, 0, 13] = true := by decide +kernel
theorem subd10_1_427 : subd10_1 [1, 0, 14] = true := by decide +kernel
theorem subd10_1_428 : subd10_1 [1, 0, 15] = true := by decide +kernel
theorem subd10_1_429 : subd10_1 [1, 0, 16] = true := by decide +kernel
theorem subd10_1_430 : subd10_1 [1, 1, -16] = true := by decide +kernel
theorem subd10_1_431 : subd10_1 [1, 1, -15] = true := by decide +kernel
theorem subd10_1_432 : subd10_1 [1, 1, -14] = true := by decide +kernel
theorem subd10_1_433 : subd10_1 [1, 1, -13] = true := by decide +kernel
theorem subd10_1_434 : subd10_1 [1, 1, -12] = true := by decide +kernel
theorem subd10_1_435 : subd10_1 [1, 1, -11] = true := by decide +kernel
theorem subd10_1_436 : subd10_1 [1, 1, -10] = true := by decide +kernel
theorem subd10_1_437 : subd10_1 [1, 1, -9] = true := by decide +kernel
theorem subd10_1_438 : subd10_1 [1, 1, -8] = true := by decide +kernel
theorem subd10_1_439 : subd10_1 [1, 1, -7] = true := by decide +kernel
theorem subd10_1_440 : subd10_1 [1, 1, -6] = true := by decide +kernel
theorem subd10_1_441 : subd10_1 [1, 1, -5] = true := by decide +kernel
theorem subd10_1_442 : subd10_1 [1, 1, -4] = true := by decide +kernel
theorem subd10_1_443 : subd10_1 [1, 1, -3] = true := by decide +kernel
theorem subd10_1_444 : subd10_1 [1, 1, -2] = true := by decide +kernel
theorem subd10_1_445 : subd10_1 [1, 1, -1] = true := by decide +kernel
theorem subd10_1_446 : subd10_1 [1, 1, 0] = true := by decide +kernel
theorem subd10_1_447 : subd10_1 [1, 1, 1] = true := by decide +kernel
theorem sbd10_1_13 : ∀ q ∈ blkd10_1_13, subd10_1 q = true := by
  unfold blkd10_1_13
  exact List.forall_mem_cons.2 ⟨subd10_1_416, List.forall_mem_cons.2 ⟨subd10_1_417, List.forall_mem_cons.2 ⟨subd10_1_418, List.forall_mem_cons.2 ⟨subd10_1_419, List.forall_mem_cons.2 ⟨subd10_1_420, List.forall_mem_cons.2 ⟨subd10_1_421, List.forall_mem_cons.2 ⟨subd10_1_422, List.forall_mem_cons.2 ⟨subd10_1_423, List.forall_mem_cons.2 ⟨subd10_1_424, List.forall_mem_cons.2 ⟨subd10_1_425, List.forall_mem_cons.2 ⟨subd10_1_426, List.forall_mem_cons.2 ⟨subd10_1_427, List.forall_mem_cons.2 ⟨subd10_1_428, List.forall_mem_cons.2 ⟨subd10_1_429, List.forall_mem_cons.2 ⟨subd10_1_430, List.forall_mem_cons.2 ⟨subd10_1_431, List.forall_mem_cons.2 ⟨subd10_1_432, List.forall_mem_cons.2 ⟨subd10_1_433, List.forall_mem_cons.2 ⟨subd10_1_434, List.forall_mem_cons.2 ⟨subd10_1_435, List.forall_mem_cons.2 ⟨subd10_1_436, List.forall_mem_cons.2 ⟨subd10_1_437, List.forall_mem_cons.2 ⟨subd10_1_438, List.forall_mem_cons.2 ⟨subd10_1_439, List.forall_mem_cons.2 ⟨subd10_1_440, List.forall_mem_cons.2 ⟨subd10_1_441, List.forall_mem_cons.2 ⟨subd10_1_442, List.forall_mem_cons.2 ⟨subd10_1_443, List.forall_mem_cons.2 ⟨subd10_1_444, List.forall_mem_cons.2 ⟨subd10_1_445, List.forall_mem_cons.2 ⟨subd10_1_446, List.forall_mem_cons.2 ⟨subd10_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_448 : subd10_1 [1, 1, 2] = true := by decide +kernel
theorem subd10_1_449 : subd10_1 [1, 1, 3] = true := by decide +kernel
theorem subd10_1_450 : subd10_1 [1, 1, 4] = true := by decide +kernel
theorem subd10_1_451 : subd10_1 [1, 1, 5] = true := by decide +kernel
theorem subd10_1_452 : subd10_1 [1, 1, 6] = true := by decide +kernel
theorem subd10_1_453 : subd10_1 [1, 1, 7] = true := by decide +kernel
theorem subd10_1_454 : subd10_1 [1, 1, 8] = true := by decide +kernel
theorem subd10_1_455 : subd10_1 [1, 1, 9] = true := by decide +kernel
theorem subd10_1_456 : subd10_1 [1, 1, 10] = true := by decide +kernel
theorem subd10_1_457 : subd10_1 [1, 1, 11] = true := by decide +kernel
theorem subd10_1_458 : subd10_1 [1, 1, 12] = true := by decide +kernel
theorem subd10_1_459 : subd10_1 [1, 1, 13] = true := by decide +kernel
theorem subd10_1_460 : subd10_1 [1, 2] = true := by decide +kernel
theorem subd10_1_461 : subd10_1 [2, -2] = true := by decide +kernel
theorem subd10_1_462 : subd10_1 [2, -1, -11] = true := by decide +kernel
theorem subd10_1_463 : subd10_1 [2, -1, -10] = true := by decide +kernel
theorem subd10_1_464 : subd10_1 [2, -1, -9] = true := by decide +kernel
theorem subd10_1_465 : subd10_1 [2, -1, -8] = true := by decide +kernel
theorem subd10_1_466 : subd10_1 [2, -1, -7] = true := by decide +kernel
theorem subd10_1_467 : subd10_1 [2, -1, -6] = true := by decide +kernel
theorem subd10_1_468 : subd10_1 [2, -1, -5] = true := by decide +kernel
theorem subd10_1_469 : subd10_1 [2, -1, -4] = true := by decide +kernel
theorem subd10_1_470 : subd10_1 [2, -1, -3] = true := by decide +kernel
theorem subd10_1_471 : subd10_1 [2, -1, -2] = true := by decide +kernel
theorem subd10_1_472 : subd10_1 [2, -1, -1] = true := by decide +kernel
theorem subd10_1_473 : subd10_1 [2, -1, 0] = true := by decide +kernel
theorem subd10_1_474 : subd10_1 [2, -1, 1] = true := by decide +kernel
theorem subd10_1_475 : subd10_1 [2, -1, 2] = true := by decide +kernel
theorem subd10_1_476 : subd10_1 [2, -1, 3] = true := by decide +kernel
theorem subd10_1_477 : subd10_1 [2, -1, 4] = true := by decide +kernel
theorem subd10_1_478 : subd10_1 [2, -1, 5] = true := by decide +kernel
theorem subd10_1_479 : subd10_1 [2, -1, 6] = true := by decide +kernel
theorem sbd10_1_14 : ∀ q ∈ blkd10_1_14, subd10_1 q = true := by
  unfold blkd10_1_14
  exact List.forall_mem_cons.2 ⟨subd10_1_448, List.forall_mem_cons.2 ⟨subd10_1_449, List.forall_mem_cons.2 ⟨subd10_1_450, List.forall_mem_cons.2 ⟨subd10_1_451, List.forall_mem_cons.2 ⟨subd10_1_452, List.forall_mem_cons.2 ⟨subd10_1_453, List.forall_mem_cons.2 ⟨subd10_1_454, List.forall_mem_cons.2 ⟨subd10_1_455, List.forall_mem_cons.2 ⟨subd10_1_456, List.forall_mem_cons.2 ⟨subd10_1_457, List.forall_mem_cons.2 ⟨subd10_1_458, List.forall_mem_cons.2 ⟨subd10_1_459, List.forall_mem_cons.2 ⟨subd10_1_460, List.forall_mem_cons.2 ⟨subd10_1_461, List.forall_mem_cons.2 ⟨subd10_1_462, List.forall_mem_cons.2 ⟨subd10_1_463, List.forall_mem_cons.2 ⟨subd10_1_464, List.forall_mem_cons.2 ⟨subd10_1_465, List.forall_mem_cons.2 ⟨subd10_1_466, List.forall_mem_cons.2 ⟨subd10_1_467, List.forall_mem_cons.2 ⟨subd10_1_468, List.forall_mem_cons.2 ⟨subd10_1_469, List.forall_mem_cons.2 ⟨subd10_1_470, List.forall_mem_cons.2 ⟨subd10_1_471, List.forall_mem_cons.2 ⟨subd10_1_472, List.forall_mem_cons.2 ⟨subd10_1_473, List.forall_mem_cons.2 ⟨subd10_1_474, List.forall_mem_cons.2 ⟨subd10_1_475, List.forall_mem_cons.2 ⟨subd10_1_476, List.forall_mem_cons.2 ⟨subd10_1_477, List.forall_mem_cons.2 ⟨subd10_1_478, List.forall_mem_cons.2 ⟨subd10_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_480 : subd10_1 [2, -1, 7] = true := by decide +kernel
theorem subd10_1_481 : subd10_1 [2, -1, 8] = true := by decide +kernel
theorem subd10_1_482 : subd10_1 [2, -1, 9] = true := by decide +kernel
theorem subd10_1_483 : subd10_1 [2, 0, -11] = true := by decide +kernel
theorem subd10_1_484 : subd10_1 [2, 0, -10] = true := by decide +kernel
theorem subd10_1_485 : subd10_1 [2, 0, -9] = true := by decide +kernel
theorem subd10_1_486 : subd10_1 [2, 0, -8] = true := by decide +kernel
theorem subd10_1_487 : subd10_1 [2, 0, -7] = true := by decide +kernel
theorem subd10_1_488 : subd10_1 [2, 0, -6] = true := by decide +kernel
theorem subd10_1_489 : subd10_1 [2, 0, -5] = true := by decide +kernel
theorem subd10_1_490 : subd10_1 [2, 0, -4] = true := by decide +kernel
theorem subd10_1_491 : subd10_1 [2, 0, -3] = true := by decide +kernel
theorem subd10_1_492 : subd10_1 [2, 0, -2] = true := by decide +kernel
theorem subd10_1_493 : subd10_1 [2, 0, -1] = true := by decide +kernel
theorem subd10_1_494 : subd10_1 [2, 0, 0] = true := by decide +kernel
theorem subd10_1_495 : subd10_1 [2, 0, 1] = true := by decide +kernel
theorem subd10_1_496 : subd10_1 [2, 0, 2] = true := by decide +kernel
theorem subd10_1_497 : subd10_1 [2, 0, 3] = true := by decide +kernel
theorem subd10_1_498 : subd10_1 [2, 0, 4] = true := by decide +kernel
theorem subd10_1_499 : subd10_1 [2, 0, 5] = true := by decide +kernel
theorem subd10_1_500 : subd10_1 [2, 0, 6] = true := by decide +kernel
theorem subd10_1_501 : subd10_1 [2, 0, 7] = true := by decide +kernel
theorem subd10_1_502 : subd10_1 [2, 0, 8] = true := by decide +kernel
theorem sbd10_1_15 : ∀ q ∈ blkd10_1_15, subd10_1 q = true := by
  unfold blkd10_1_15
  exact List.forall_mem_cons.2 ⟨subd10_1_480, List.forall_mem_cons.2 ⟨subd10_1_481, List.forall_mem_cons.2 ⟨subd10_1_482, List.forall_mem_cons.2 ⟨subd10_1_483, List.forall_mem_cons.2 ⟨subd10_1_484, List.forall_mem_cons.2 ⟨subd10_1_485, List.forall_mem_cons.2 ⟨subd10_1_486, List.forall_mem_cons.2 ⟨subd10_1_487, List.forall_mem_cons.2 ⟨subd10_1_488, List.forall_mem_cons.2 ⟨subd10_1_489, List.forall_mem_cons.2 ⟨subd10_1_490, List.forall_mem_cons.2 ⟨subd10_1_491, List.forall_mem_cons.2 ⟨subd10_1_492, List.forall_mem_cons.2 ⟨subd10_1_493, List.forall_mem_cons.2 ⟨subd10_1_494, List.forall_mem_cons.2 ⟨subd10_1_495, List.forall_mem_cons.2 ⟨subd10_1_496, List.forall_mem_cons.2 ⟨subd10_1_497, List.forall_mem_cons.2 ⟨subd10_1_498, List.forall_mem_cons.2 ⟨subd10_1_499, List.forall_mem_cons.2 ⟨subd10_1_500, List.forall_mem_cons.2 ⟨subd10_1_501, List.forall_mem_cons.2 ⟨subd10_1_502, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-5, -2] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-5, -1] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-5, 0] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-5, 1] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-5, 2] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-5, 3] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [-5, 4] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [-5, 5] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [-4, -4] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [-4, -3] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [-4, -2] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [-4, -1] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [-4, 0] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [-4, 1] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [-4, 2] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [-4, 3] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [-4, 4] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [-4, 5] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [-4, 6] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [-3, -5] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [-3, -4] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [-3, -3] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [-3, -2] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [-3, -1, -8] = true := by decide +kernel
theorem subd11_0_24 : subd11_0 [-3, -1, -7] = true := by decide +kernel
theorem subd11_0_25 : subd11_0 [-3, -1, -6] = true := by decide +kernel
theorem subd11_0_26 : subd11_0 [-3, -1, -5] = true := by decide +kernel
theorem subd11_0_27 : subd11_0 [-3, -1, -4] = true := by decide +kernel
theorem subd11_0_28 : subd11_0 [-3, -1, -3] = true := by decide +kernel
theorem subd11_0_29 : subd11_0 [-3, -1, -2] = true := by decide +kernel
theorem subd11_0_30 : subd11_0 [-3, -1, -1] = true := by decide +kernel
theorem subd11_0_31 : subd11_0 [-3, -1, 0] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_cons.2 ⟨subd11_0_24, List.forall_mem_cons.2 ⟨subd11_0_25, List.forall_mem_cons.2 ⟨subd11_0_26, List.forall_mem_cons.2 ⟨subd11_0_27, List.forall_mem_cons.2 ⟨subd11_0_28, List.forall_mem_cons.2 ⟨subd11_0_29, List.forall_mem_cons.2 ⟨subd11_0_30, List.forall_mem_cons.2 ⟨subd11_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_32 : subd11_0 [-3, -1, 1] = true := by decide +kernel
theorem subd11_0_33 : subd11_0 [-3, -1, 2] = true := by decide +kernel
theorem subd11_0_34 : subd11_0 [-3, -1, 3] = true := by decide +kernel
theorem subd11_0_35 : subd11_0 [-3, -1, 4] = true := by decide +kernel
theorem subd11_0_36 : subd11_0 [-3, -1, 5] = true := by decide +kernel
theorem subd11_0_37 : subd11_0 [-3, 0, -7] = true := by decide +kernel
theorem subd11_0_38 : subd11_0 [-3, 0, -6] = true := by decide +kernel
theorem subd11_0_39 : subd11_0 [-3, 0, -5] = true := by decide +kernel
theorem subd11_0_40 : subd11_0 [-3, 0, -4] = true := by decide +kernel
theorem subd11_0_41 : subd11_0 [-3, 0, -3] = true := by decide +kernel
theorem subd11_0_42 : subd11_0 [-3, 0, -2] = true := by decide +kernel
theorem subd11_0_43 : subd11_0 [-3, 0, -1] = true := by decide +kernel
theorem subd11_0_44 : subd11_0 [-3, 0, 0] = true := by decide +kernel
theorem subd11_0_45 : subd11_0 [-3, 0, 1] = true := by decide +kernel
theorem subd11_0_46 : subd11_0 [-3, 0, 2] = true := by decide +kernel
theorem subd11_0_47 : subd11_0 [-3, 0, 3] = true := by decide +kernel
theorem subd11_0_48 : subd11_0 [-3, 0, 4] = true := by decide +kernel
theorem subd11_0_49 : subd11_0 [-3, 0, 5] = true := by decide +kernel
theorem subd11_0_50 : subd11_0 [-3, 0, 6] = true := by decide +kernel
theorem subd11_0_51 : subd11_0 [-3, 1, -7] = true := by decide +kernel
theorem subd11_0_52 : subd11_0 [-3, 1, -6] = true := by decide +kernel
theorem subd11_0_53 : subd11_0 [-3, 1, -5] = true := by decide +kernel
theorem subd11_0_54 : subd11_0 [-3, 1, -4] = true := by decide +kernel
theorem subd11_0_55 : subd11_0 [-3, 1, -3] = true := by decide +kernel
theorem subd11_0_56 : subd11_0 [-3, 1, -2] = true := by decide +kernel
theorem subd11_0_57 : subd11_0 [-3, 1, -1] = true := by decide +kernel
theorem subd11_0_58 : subd11_0 [-3, 1, 0] = true := by decide +kernel
theorem subd11_0_59 : subd11_0 [-3, 1, 1] = true := by decide +kernel
theorem subd11_0_60 : subd11_0 [-3, 1, 2] = true := by decide +kernel
theorem subd11_0_61 : subd11_0 [-3, 1, 3] = true := by decide +kernel
theorem subd11_0_62 : subd11_0 [-3, 1, 4] = true := by decide +kernel
theorem subd11_0_63 : subd11_0 [-3, 1, 5] = true := by decide +kernel
theorem sbd11_0_1 : ∀ q ∈ blkd11_0_1, subd11_0 q = true := by
  unfold blkd11_0_1
  exact List.forall_mem_cons.2 ⟨subd11_0_32, List.forall_mem_cons.2 ⟨subd11_0_33, List.forall_mem_cons.2 ⟨subd11_0_34, List.forall_mem_cons.2 ⟨subd11_0_35, List.forall_mem_cons.2 ⟨subd11_0_36, List.forall_mem_cons.2 ⟨subd11_0_37, List.forall_mem_cons.2 ⟨subd11_0_38, List.forall_mem_cons.2 ⟨subd11_0_39, List.forall_mem_cons.2 ⟨subd11_0_40, List.forall_mem_cons.2 ⟨subd11_0_41, List.forall_mem_cons.2 ⟨subd11_0_42, List.forall_mem_cons.2 ⟨subd11_0_43, List.forall_mem_cons.2 ⟨subd11_0_44, List.forall_mem_cons.2 ⟨subd11_0_45, List.forall_mem_cons.2 ⟨subd11_0_46, List.forall_mem_cons.2 ⟨subd11_0_47, List.forall_mem_cons.2 ⟨subd11_0_48, List.forall_mem_cons.2 ⟨subd11_0_49, List.forall_mem_cons.2 ⟨subd11_0_50, List.forall_mem_cons.2 ⟨subd11_0_51, List.forall_mem_cons.2 ⟨subd11_0_52, List.forall_mem_cons.2 ⟨subd11_0_53, List.forall_mem_cons.2 ⟨subd11_0_54, List.forall_mem_cons.2 ⟨subd11_0_55, List.forall_mem_cons.2 ⟨subd11_0_56, List.forall_mem_cons.2 ⟨subd11_0_57, List.forall_mem_cons.2 ⟨subd11_0_58, List.forall_mem_cons.2 ⟨subd11_0_59, List.forall_mem_cons.2 ⟨subd11_0_60, List.forall_mem_cons.2 ⟨subd11_0_61, List.forall_mem_cons.2 ⟨subd11_0_62, List.forall_mem_cons.2 ⟨subd11_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_64 : subd11_0 [-3, 1, 6] = true := by decide +kernel
theorem subd11_0_65 : subd11_0 [-3, 2, -7] = true := by decide +kernel
theorem subd11_0_66 : subd11_0 [-3, 2, -6] = true := by decide +kernel
theorem subd11_0_67 : subd11_0 [-3, 2, -5] = true := by decide +kernel
theorem subd11_0_68 : subd11_0 [-3, 2, -4] = true := by decide +kernel
theorem subd11_0_69 : subd11_0 [-3, 2, -3] = true := by decide +kernel
theorem subd11_0_70 : subd11_0 [-3, 2, -2] = true := by decide +kernel
theorem subd11_0_71 : subd11_0 [-3, 2, -1] = true := by decide +kernel
theorem subd11_0_72 : subd11_0 [-3, 2, 0] = true := by decide +kernel
theorem subd11_0_73 : subd11_0 [-3, 2, 1] = true := by decide +kernel
theorem subd11_0_74 : subd11_0 [-3, 2, 2] = true := by decide +kernel
theorem subd11_0_75 : subd11_0 [-3, 2, 3] = true := by decide +kernel
theorem subd11_0_76 : subd11_0 [-3, 2, 4] = true := by decide +kernel
theorem subd11_0_77 : subd11_0 [-3, 2, 5] = true := by decide +kernel
theorem subd11_0_78 : subd11_0 [-3, 2, 6] = true := by decide +kernel
theorem subd11_0_79 : subd11_0 [-3, 2, 7] = true := by decide +kernel
theorem subd11_0_80 : subd11_0 [-3, 3, -6] = true := by decide +kernel
theorem subd11_0_81 : subd11_0 [-3, 3, -5] = true := by decide +kernel
theorem subd11_0_82 : subd11_0 [-3, 3, -4] = true := by decide +kernel
theorem subd11_0_83 : subd11_0 [-3, 3, -3] = true := by decide +kernel
theorem subd11_0_84 : subd11_0 [-3, 3, -2] = true := by decide +kernel
theorem subd11_0_85 : subd11_0 [-3, 3, -1] = true := by decide +kernel
theorem subd11_0_86 : subd11_0 [-3, 3, 0] = true := by decide +kernel
theorem subd11_0_87 : subd11_0 [-3, 3, 1] = true := by decide +kernel
theorem subd11_0_88 : subd11_0 [-3, 3, 2] = true := by decide +kernel
theorem subd11_0_89 : subd11_0 [-3, 3, 3] = true := by decide +kernel
theorem subd11_0_90 : subd11_0 [-3, 3, 4] = true := by decide +kernel
theorem subd11_0_91 : subd11_0 [-3, 3, 5] = true := by decide +kernel
theorem subd11_0_92 : subd11_0 [-3, 3, 6] = true := by decide +kernel
theorem subd11_0_93 : subd11_0 [-3, 3, 7] = true := by decide +kernel
theorem subd11_0_94 : subd11_0 [-3, 4] = true := by decide +kernel
theorem subd11_0_95 : subd11_0 [-3, 5] = true := by decide +kernel
theorem sbd11_0_2 : ∀ q ∈ blkd11_0_2, subd11_0 q = true := by
  unfold blkd11_0_2
  exact List.forall_mem_cons.2 ⟨subd11_0_64, List.forall_mem_cons.2 ⟨subd11_0_65, List.forall_mem_cons.2 ⟨subd11_0_66, List.forall_mem_cons.2 ⟨subd11_0_67, List.forall_mem_cons.2 ⟨subd11_0_68, List.forall_mem_cons.2 ⟨subd11_0_69, List.forall_mem_cons.2 ⟨subd11_0_70, List.forall_mem_cons.2 ⟨subd11_0_71, List.forall_mem_cons.2 ⟨subd11_0_72, List.forall_mem_cons.2 ⟨subd11_0_73, List.forall_mem_cons.2 ⟨subd11_0_74, List.forall_mem_cons.2 ⟨subd11_0_75, List.forall_mem_cons.2 ⟨subd11_0_76, List.forall_mem_cons.2 ⟨subd11_0_77, List.forall_mem_cons.2 ⟨subd11_0_78, List.forall_mem_cons.2 ⟨subd11_0_79, List.forall_mem_cons.2 ⟨subd11_0_80, List.forall_mem_cons.2 ⟨subd11_0_81, List.forall_mem_cons.2 ⟨subd11_0_82, List.forall_mem_cons.2 ⟨subd11_0_83, List.forall_mem_cons.2 ⟨subd11_0_84, List.forall_mem_cons.2 ⟨subd11_0_85, List.forall_mem_cons.2 ⟨subd11_0_86, List.forall_mem_cons.2 ⟨subd11_0_87, List.forall_mem_cons.2 ⟨subd11_0_88, List.forall_mem_cons.2 ⟨subd11_0_89, List.forall_mem_cons.2 ⟨subd11_0_90, List.forall_mem_cons.2 ⟨subd11_0_91, List.forall_mem_cons.2 ⟨subd11_0_92, List.forall_mem_cons.2 ⟨subd11_0_93, List.forall_mem_cons.2 ⟨subd11_0_94, List.forall_mem_cons.2 ⟨subd11_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_96 : subd11_0 [-3, 6] = true := by decide +kernel
theorem subd11_0_97 : subd11_0 [-2, -6] = true := by decide +kernel
theorem subd11_0_98 : subd11_0 [-2, -5] = true := by decide +kernel
theorem subd11_0_99 : subd11_0 [-2, -4] = true := by decide +kernel
theorem subd11_0_100 : subd11_0 [-2, -3] = true := by decide +kernel
theorem subd11_0_101 : subd11_0 [-2, -2, -8] = true := by decide +kernel
theorem subd11_0_102 : subd11_0 [-2, -2, -7] = true := by decide +kernel
theorem subd11_0_103 : subd11_0 [-2, -2, -6] = true := by decide +kernel
theorem subd11_0_104 : subd11_0 [-2, -2, -5] = true := by decide +kernel
theorem subd11_0_105 : subd11_0 [-2, -2, -4] = true := by decide +kernel
theorem subd11_0_106 : subd11_0 [-2, -2, -3] = true := by decide +kernel
theorem subd11_0_107 : subd11_0 [-2, -2, -2] = true := by decide +kernel
theorem subd11_0_108 : subd11_0 [-2, -2, -1] = true := by decide +kernel
theorem subd11_0_109 : subd11_0 [-2, -2, 0] = true := by decide +kernel
theorem subd11_0_110 : subd11_0 [-2, -2, 1] = true := by decide +kernel
theorem subd11_0_111 : subd11_0 [-2, -2, 2] = true := by decide +kernel
theorem subd11_0_112 : subd11_0 [-2, -2, 3] = true := by decide +kernel
theorem subd11_0_113 : subd11_0 [-2, -2, 4] = true := by decide +kernel
theorem subd11_0_114 : subd11_0 [-2, -2, 5] = true := by decide +kernel
theorem subd11_0_115 : subd11_0 [-2, -1, -8] = true := by decide +kernel
theorem subd11_0_116 : subd11_0 [-2, -1, -7] = true := by decide +kernel
theorem subd11_0_117 : subd11_0 [-2, -1, -6] = true := by decide +kernel
theorem subd11_0_118 : subd11_0 [-2, -1, -5] = true := by decide +kernel
theorem subd11_0_119 : subd11_0 [-2, -1, -4] = true := by decide +kernel
theorem subd11_0_120 : subd11_0 [-2, -1, -3] = true := by decide +kernel
theorem subd11_0_121 : subd11_0 [-2, -1, -2] = true := by decide +kernel
theorem subd11_0_122 : subd11_0 [-2, -1, -1] = true := by decide +kernel
theorem subd11_0_123 : subd11_0 [-2, -1, 0] = true := by decide +kernel
theorem subd11_0_124 : subd11_0 [-2, -1, 1] = true := by decide +kernel
theorem subd11_0_125 : subd11_0 [-2, -1, 2] = true := by decide +kernel
theorem subd11_0_126 : subd11_0 [-2, -1, 3] = true := by decide +kernel
theorem subd11_0_127 : subd11_0 [-2, -1, 4] = true := by decide +kernel
theorem sbd11_0_3 : ∀ q ∈ blkd11_0_3, subd11_0 q = true := by
  unfold blkd11_0_3
  exact List.forall_mem_cons.2 ⟨subd11_0_96, List.forall_mem_cons.2 ⟨subd11_0_97, List.forall_mem_cons.2 ⟨subd11_0_98, List.forall_mem_cons.2 ⟨subd11_0_99, List.forall_mem_cons.2 ⟨subd11_0_100, List.forall_mem_cons.2 ⟨subd11_0_101, List.forall_mem_cons.2 ⟨subd11_0_102, List.forall_mem_cons.2 ⟨subd11_0_103, List.forall_mem_cons.2 ⟨subd11_0_104, List.forall_mem_cons.2 ⟨subd11_0_105, List.forall_mem_cons.2 ⟨subd11_0_106, List.forall_mem_cons.2 ⟨subd11_0_107, List.forall_mem_cons.2 ⟨subd11_0_108, List.forall_mem_cons.2 ⟨subd11_0_109, List.forall_mem_cons.2 ⟨subd11_0_110, List.forall_mem_cons.2 ⟨subd11_0_111, List.forall_mem_cons.2 ⟨subd11_0_112, List.forall_mem_cons.2 ⟨subd11_0_113, List.forall_mem_cons.2 ⟨subd11_0_114, List.forall_mem_cons.2 ⟨subd11_0_115, List.forall_mem_cons.2 ⟨subd11_0_116, List.forall_mem_cons.2 ⟨subd11_0_117, List.forall_mem_cons.2 ⟨subd11_0_118, List.forall_mem_cons.2 ⟨subd11_0_119, List.forall_mem_cons.2 ⟨subd11_0_120, List.forall_mem_cons.2 ⟨subd11_0_121, List.forall_mem_cons.2 ⟨subd11_0_122, List.forall_mem_cons.2 ⟨subd11_0_123, List.forall_mem_cons.2 ⟨subd11_0_124, List.forall_mem_cons.2 ⟨subd11_0_125, List.forall_mem_cons.2 ⟨subd11_0_126, List.forall_mem_cons.2 ⟨subd11_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_128 : subd11_0 [-2, -1, 5] = true := by decide +kernel
theorem subd11_0_129 : subd11_0 [-2, -1, 6] = true := by decide +kernel
theorem subd11_0_130 : subd11_0 [-2, 0, -8] = true := by decide +kernel
theorem subd11_0_131 : subd11_0 [-2, 0, -7] = true := by decide +kernel
theorem subd11_0_132 : subd11_0 [-2, 0, -6] = true := by decide +kernel
theorem subd11_0_133 : subd11_0 [-2, 0, -5] = true := by decide +kernel
theorem subd11_0_134 : subd11_0 [-2, 0, -4] = true := by decide +kernel
theorem subd11_0_135 : subd11_0 [-2, 0, -3] = true := by decide +kernel
theorem subd11_0_136 : subd11_0 [-2, 0, -2] = true := by decide +kernel
theorem subd11_0_137 : subd11_0 [-2, 0, -1] = true := by decide +kernel
theorem subd11_0_138 : subd11_0 [-2, 0, 0] = true := by decide +kernel
theorem subd11_0_139 : subd11_0 [-2, 0, 1] = true := by decide +kernel
theorem subd11_0_140 : subd11_0 [-2, 0, 2] = true := by decide +kernel
theorem subd11_0_141 : subd11_0 [-2, 0, 3] = true := by decide +kernel
theorem subd11_0_142 : subd11_0 [-2, 0, 4] = true := by decide +kernel
theorem subd11_0_143 : subd11_0 [-2, 0, 5] = true := by decide +kernel
theorem subd11_0_144 : subd11_0 [-2, 0, 6] = true := by decide +kernel
theorem subd11_0_145 : subd11_0 [-2, 0, 7] = true := by decide +kernel
theorem subd11_0_146 : subd11_0 [-2, 1, -8] = true := by decide +kernel
theorem subd11_0_147 : subd11_0 [-2, 1, -7] = true := by decide +kernel
theorem subd11_0_148 : subd11_0 [-2, 1, -6] = true := by decide +kernel
theorem subd11_0_149 : subd11_0 [-2, 1, -5] = true := by decide +kernel
theorem subd11_0_150 : subd11_0 [-2, 1, -4] = true := by decide +kernel
theorem subd11_0_151 : subd11_0 [-2, 1, -3] = true := by decide +kernel
theorem subd11_0_152 : subd11_0 [-2, 1, -2] = true := by decide +kernel
theorem subd11_0_153 : subd11_0 [-2, 1, -1] = true := by decide +kernel
theorem subd11_0_154 : subd11_0 [-2, 1, 0] = true := by decide +kernel
theorem subd11_0_155 : subd11_0 [-2, 1, 1] = true := by decide +kernel
theorem subd11_0_156 : subd11_0 [-2, 1, 2] = true := by decide +kernel
theorem subd11_0_157 : subd11_0 [-2, 1, 3] = true := by decide +kernel
theorem subd11_0_158 : subd11_0 [-2, 1, 4] = true := by decide +kernel
theorem subd11_0_159 : subd11_0 [-2, 1, 5] = true := by decide +kernel
theorem sbd11_0_4 : ∀ q ∈ blkd11_0_4, subd11_0 q = true := by
  unfold blkd11_0_4
  exact List.forall_mem_cons.2 ⟨subd11_0_128, List.forall_mem_cons.2 ⟨subd11_0_129, List.forall_mem_cons.2 ⟨subd11_0_130, List.forall_mem_cons.2 ⟨subd11_0_131, List.forall_mem_cons.2 ⟨subd11_0_132, List.forall_mem_cons.2 ⟨subd11_0_133, List.forall_mem_cons.2 ⟨subd11_0_134, List.forall_mem_cons.2 ⟨subd11_0_135, List.forall_mem_cons.2 ⟨subd11_0_136, List.forall_mem_cons.2 ⟨subd11_0_137, List.forall_mem_cons.2 ⟨subd11_0_138, List.forall_mem_cons.2 ⟨subd11_0_139, List.forall_mem_cons.2 ⟨subd11_0_140, List.forall_mem_cons.2 ⟨subd11_0_141, List.forall_mem_cons.2 ⟨subd11_0_142, List.forall_mem_cons.2 ⟨subd11_0_143, List.forall_mem_cons.2 ⟨subd11_0_144, List.forall_mem_cons.2 ⟨subd11_0_145, List.forall_mem_cons.2 ⟨subd11_0_146, List.forall_mem_cons.2 ⟨subd11_0_147, List.forall_mem_cons.2 ⟨subd11_0_148, List.forall_mem_cons.2 ⟨subd11_0_149, List.forall_mem_cons.2 ⟨subd11_0_150, List.forall_mem_cons.2 ⟨subd11_0_151, List.forall_mem_cons.2 ⟨subd11_0_152, List.forall_mem_cons.2 ⟨subd11_0_153, List.forall_mem_cons.2 ⟨subd11_0_154, List.forall_mem_cons.2 ⟨subd11_0_155, List.forall_mem_cons.2 ⟨subd11_0_156, List.forall_mem_cons.2 ⟨subd11_0_157, List.forall_mem_cons.2 ⟨subd11_0_158, List.forall_mem_cons.2 ⟨subd11_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_160 : subd11_0 [-2, 1, 6] = true := by decide +kernel
theorem subd11_0_161 : subd11_0 [-2, 1, 7] = true := by decide +kernel
theorem subd11_0_162 : subd11_0 [-2, 2, -7] = true := by decide +kernel
theorem subd11_0_163 : subd11_0 [-2, 2, -6] = true := by decide +kernel
theorem subd11_0_164 : subd11_0 [-2, 2, -5] = true := by decide +kernel
theorem subd11_0_165 : subd11_0 [-2, 2, -4] = true := by decide +kernel
theorem subd11_0_166 : subd11_0 [-2, 2, -3] = true := by decide +kernel
theorem subd11_0_167 : subd11_0 [-2, 2, -2] = true := by decide +kernel
theorem subd11_0_168 : subd11_0 [-2, 2, -1] = true := by decide +kernel
theorem subd11_0_169 : subd11_0 [-2, 2, 0] = true := by decide +kernel
theorem subd11_0_170 : subd11_0 [-2, 2, 1] = true := by decide +kernel
theorem subd11_0_171 : subd11_0 [-2, 2, 2] = true := by decide +kernel
theorem subd11_0_172 : subd11_0 [-2, 2, 3] = true := by decide +kernel
theorem subd11_0_173 : subd11_0 [-2, 2, 4] = true := by decide +kernel
theorem subd11_0_174 : subd11_0 [-2, 2, 5] = true := by decide +kernel
theorem subd11_0_175 : subd11_0 [-2, 2, 6] = true := by decide +kernel
theorem subd11_0_176 : subd11_0 [-2, 2, 7] = true := by decide +kernel
theorem subd11_0_177 : subd11_0 [-2, 3, -6] = true := by decide +kernel
theorem subd11_0_178 : subd11_0 [-2, 3, -5] = true := by decide +kernel
theorem subd11_0_179 : subd11_0 [-2, 3, -4] = true := by decide +kernel
theorem subd11_0_180 : subd11_0 [-2, 3, -3] = true := by decide +kernel
theorem subd11_0_181 : subd11_0 [-2, 3, -2] = true := by decide +kernel
theorem subd11_0_182 : subd11_0 [-2, 3, -1] = true := by decide +kernel
theorem subd11_0_183 : subd11_0 [-2, 3, 0] = true := by decide +kernel
theorem subd11_0_184 : subd11_0 [-2, 3, 1] = true := by decide +kernel
theorem subd11_0_185 : subd11_0 [-2, 3, 2] = true := by decide +kernel
theorem subd11_0_186 : subd11_0 [-2, 3, 3] = true := by decide +kernel
theorem subd11_0_187 : subd11_0 [-2, 3, 4] = true := by decide +kernel
theorem subd11_0_188 : subd11_0 [-2, 3, 5] = true := by decide +kernel
theorem subd11_0_189 : subd11_0 [-2, 3, 6] = true := by decide +kernel
theorem subd11_0_190 : subd11_0 [-2, 3, 7] = true := by decide +kernel
theorem subd11_0_191 : subd11_0 [-2, 3, 8] = true := by decide +kernel
theorem sbd11_0_5 : ∀ q ∈ blkd11_0_5, subd11_0 q = true := by
  unfold blkd11_0_5
  exact List.forall_mem_cons.2 ⟨subd11_0_160, List.forall_mem_cons.2 ⟨subd11_0_161, List.forall_mem_cons.2 ⟨subd11_0_162, List.forall_mem_cons.2 ⟨subd11_0_163, List.forall_mem_cons.2 ⟨subd11_0_164, List.forall_mem_cons.2 ⟨subd11_0_165, List.forall_mem_cons.2 ⟨subd11_0_166, List.forall_mem_cons.2 ⟨subd11_0_167, List.forall_mem_cons.2 ⟨subd11_0_168, List.forall_mem_cons.2 ⟨subd11_0_169, List.forall_mem_cons.2 ⟨subd11_0_170, List.forall_mem_cons.2 ⟨subd11_0_171, List.forall_mem_cons.2 ⟨subd11_0_172, List.forall_mem_cons.2 ⟨subd11_0_173, List.forall_mem_cons.2 ⟨subd11_0_174, List.forall_mem_cons.2 ⟨subd11_0_175, List.forall_mem_cons.2 ⟨subd11_0_176, List.forall_mem_cons.2 ⟨subd11_0_177, List.forall_mem_cons.2 ⟨subd11_0_178, List.forall_mem_cons.2 ⟨subd11_0_179, List.forall_mem_cons.2 ⟨subd11_0_180, List.forall_mem_cons.2 ⟨subd11_0_181, List.forall_mem_cons.2 ⟨subd11_0_182, List.forall_mem_cons.2 ⟨subd11_0_183, List.forall_mem_cons.2 ⟨subd11_0_184, List.forall_mem_cons.2 ⟨subd11_0_185, List.forall_mem_cons.2 ⟨subd11_0_186, List.forall_mem_cons.2 ⟨subd11_0_187, List.forall_mem_cons.2 ⟨subd11_0_188, List.forall_mem_cons.2 ⟨subd11_0_189, List.forall_mem_cons.2 ⟨subd11_0_190, List.forall_mem_cons.2 ⟨subd11_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
