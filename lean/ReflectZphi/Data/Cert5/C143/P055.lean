import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd18_0_384 : subd18_0 [1, -2, -5] = true := by decide +kernel
theorem subd18_0_385 : subd18_0 [1, -2, -4] = true := by decide +kernel
theorem subd18_0_386 : subd18_0 [1, -2, -3] = true := by decide +kernel
theorem subd18_0_387 : subd18_0 [1, -2, -2] = true := by decide +kernel
theorem subd18_0_388 : subd18_0 [1, -2, -1] = true := by decide +kernel
theorem subd18_0_389 : subd18_0 [1, -2, 0] = true := by decide +kernel
theorem subd18_0_390 : subd18_0 [1, -2, 1] = true := by decide +kernel
theorem subd18_0_391 : subd18_0 [1, -2, 2] = true := by decide +kernel
theorem subd18_0_392 : subd18_0 [1, -2, 3] = true := by decide +kernel
theorem subd18_0_393 : subd18_0 [1, -2, 4] = true := by decide +kernel
theorem subd18_0_394 : subd18_0 [1, -2, 5] = true := by decide +kernel
theorem subd18_0_395 : subd18_0 [1, -2, 6] = true := by decide +kernel
theorem subd18_0_396 : subd18_0 [1, -2, 7] = true := by decide +kernel
theorem subd18_0_397 : subd18_0 [1, -2, 8] = true := by decide +kernel
theorem subd18_0_398 : subd18_0 [1, -2, 9] = true := by decide +kernel
theorem subd18_0_399 : subd18_0 [1, -1, -11] = true := by decide +kernel
theorem subd18_0_400 : subd18_0 [1, -1, -10] = true := by decide +kernel
theorem subd18_0_401 : subd18_0 [1, -1, -9] = true := by decide +kernel
theorem subd18_0_402 : subd18_0 [1, -1, -8] = true := by decide +kernel
theorem subd18_0_403 : subd18_0 [1, -1, -7] = true := by decide +kernel
theorem subd18_0_404 : subd18_0 [1, -1, -6] = true := by decide +kernel
theorem subd18_0_405 : subd18_0 [1, -1, -5] = true := by decide +kernel
theorem subd18_0_406 : subd18_0 [1, -1, -4] = true := by decide +kernel
theorem subd18_0_407 : subd18_0 [1, -1, -3] = true := by decide +kernel
theorem subd18_0_408 : subd18_0 [1, -1, -2] = true := by decide +kernel
theorem subd18_0_409 : subd18_0 [1, -1, -1] = true := by decide +kernel
theorem subd18_0_410 : subd18_0 [1, -1, 0] = true := by decide +kernel
theorem subd18_0_411 : subd18_0 [1, -1, 1] = true := by decide +kernel
theorem subd18_0_412 : subd18_0 [1, -1, 2] = true := by decide +kernel
theorem subd18_0_413 : subd18_0 [1, -1, 3] = true := by decide +kernel
theorem subd18_0_414 : subd18_0 [1, -1, 4] = true := by decide +kernel
theorem subd18_0_415 : subd18_0 [1, -1, 5] = true := by decide +kernel
theorem sbd18_0_12 : ∀ q ∈ blkd18_0_12, subd18_0 q = true := by
  unfold blkd18_0_12
  exact List.forall_mem_cons.2 ⟨subd18_0_384, List.forall_mem_cons.2 ⟨subd18_0_385, List.forall_mem_cons.2 ⟨subd18_0_386, List.forall_mem_cons.2 ⟨subd18_0_387, List.forall_mem_cons.2 ⟨subd18_0_388, List.forall_mem_cons.2 ⟨subd18_0_389, List.forall_mem_cons.2 ⟨subd18_0_390, List.forall_mem_cons.2 ⟨subd18_0_391, List.forall_mem_cons.2 ⟨subd18_0_392, List.forall_mem_cons.2 ⟨subd18_0_393, List.forall_mem_cons.2 ⟨subd18_0_394, List.forall_mem_cons.2 ⟨subd18_0_395, List.forall_mem_cons.2 ⟨subd18_0_396, List.forall_mem_cons.2 ⟨subd18_0_397, List.forall_mem_cons.2 ⟨subd18_0_398, List.forall_mem_cons.2 ⟨subd18_0_399, List.forall_mem_cons.2 ⟨subd18_0_400, List.forall_mem_cons.2 ⟨subd18_0_401, List.forall_mem_cons.2 ⟨subd18_0_402, List.forall_mem_cons.2 ⟨subd18_0_403, List.forall_mem_cons.2 ⟨subd18_0_404, List.forall_mem_cons.2 ⟨subd18_0_405, List.forall_mem_cons.2 ⟨subd18_0_406, List.forall_mem_cons.2 ⟨subd18_0_407, List.forall_mem_cons.2 ⟨subd18_0_408, List.forall_mem_cons.2 ⟨subd18_0_409, List.forall_mem_cons.2 ⟨subd18_0_410, List.forall_mem_cons.2 ⟨subd18_0_411, List.forall_mem_cons.2 ⟨subd18_0_412, List.forall_mem_cons.2 ⟨subd18_0_413, List.forall_mem_cons.2 ⟨subd18_0_414, List.forall_mem_cons.2 ⟨subd18_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_416 : subd18_0 [1, -1, 6] = true := by decide +kernel
theorem subd18_0_417 : subd18_0 [1, -1, 7] = true := by decide +kernel
theorem subd18_0_418 : subd18_0 [1, -1, 8] = true := by decide +kernel
theorem subd18_0_419 : subd18_0 [1, -1, 9] = true := by decide +kernel
theorem subd18_0_420 : subd18_0 [1, -1, 10] = true := by decide +kernel
theorem subd18_0_421 : subd18_0 [1, -1, 11] = true := by decide +kernel
theorem subd18_0_422 : subd18_0 [1, -1, 12] = true := by decide +kernel
theorem subd18_0_423 : subd18_0 [1, 0, -13] = true := by decide +kernel
theorem subd18_0_424 : subd18_0 [1, 0, -12] = true := by decide +kernel
theorem subd18_0_425 : subd18_0 [1, 0, -11] = true := by decide +kernel
theorem subd18_0_426 : subd18_0 [1, 0, -10] = true := by decide +kernel
theorem subd18_0_427 : subd18_0 [1, 0, -9] = true := by decide +kernel
theorem subd18_0_428 : subd18_0 [1, 0, -8] = true := by decide +kernel
theorem subd18_0_429 : subd18_0 [1, 0, -7] = true := by decide +kernel
theorem subd18_0_430 : subd18_0 [1, 0, -6] = true := by decide +kernel
theorem subd18_0_431 : subd18_0 [1, 0, -5] = true := by decide +kernel
theorem subd18_0_432 : subd18_0 [1, 0, -4] = true := by decide +kernel
theorem subd18_0_433 : subd18_0 [1, 0, -3] = true := by decide +kernel
theorem subd18_0_434 : subd18_0 [1, 0, -2] = true := by decide +kernel
theorem subd18_0_435 : subd18_0 [1, 0, -1] = true := by decide +kernel
theorem subd18_0_436 : subd18_0 [1, 0, 0] = true := by decide +kernel
theorem subd18_0_437 : subd18_0 [1, 0, 1] = true := by decide +kernel
theorem subd18_0_438 : subd18_0 [1, 0, 2] = true := by decide +kernel
theorem subd18_0_439 : subd18_0 [1, 0, 3] = true := by decide +kernel
theorem subd18_0_440 : subd18_0 [1, 0, 4] = true := by decide +kernel
theorem subd18_0_441 : subd18_0 [1, 0, 5] = true := by decide +kernel
theorem subd18_0_442 : subd18_0 [1, 0, 6] = true := by decide +kernel
theorem subd18_0_443 : subd18_0 [1, 0, 7] = true := by decide +kernel
theorem subd18_0_444 : subd18_0 [1, 0, 8] = true := by decide +kernel
theorem subd18_0_445 : subd18_0 [1, 0, 9] = true := by decide +kernel
theorem subd18_0_446 : subd18_0 [1, 0, 10] = true := by decide +kernel
theorem subd18_0_447 : subd18_0 [1, 0, 11] = true := by decide +kernel
theorem sbd18_0_13 : ∀ q ∈ blkd18_0_13, subd18_0 q = true := by
  unfold blkd18_0_13
  exact List.forall_mem_cons.2 ⟨subd18_0_416, List.forall_mem_cons.2 ⟨subd18_0_417, List.forall_mem_cons.2 ⟨subd18_0_418, List.forall_mem_cons.2 ⟨subd18_0_419, List.forall_mem_cons.2 ⟨subd18_0_420, List.forall_mem_cons.2 ⟨subd18_0_421, List.forall_mem_cons.2 ⟨subd18_0_422, List.forall_mem_cons.2 ⟨subd18_0_423, List.forall_mem_cons.2 ⟨subd18_0_424, List.forall_mem_cons.2 ⟨subd18_0_425, List.forall_mem_cons.2 ⟨subd18_0_426, List.forall_mem_cons.2 ⟨subd18_0_427, List.forall_mem_cons.2 ⟨subd18_0_428, List.forall_mem_cons.2 ⟨subd18_0_429, List.forall_mem_cons.2 ⟨subd18_0_430, List.forall_mem_cons.2 ⟨subd18_0_431, List.forall_mem_cons.2 ⟨subd18_0_432, List.forall_mem_cons.2 ⟨subd18_0_433, List.forall_mem_cons.2 ⟨subd18_0_434, List.forall_mem_cons.2 ⟨subd18_0_435, List.forall_mem_cons.2 ⟨subd18_0_436, List.forall_mem_cons.2 ⟨subd18_0_437, List.forall_mem_cons.2 ⟨subd18_0_438, List.forall_mem_cons.2 ⟨subd18_0_439, List.forall_mem_cons.2 ⟨subd18_0_440, List.forall_mem_cons.2 ⟨subd18_0_441, List.forall_mem_cons.2 ⟨subd18_0_442, List.forall_mem_cons.2 ⟨subd18_0_443, List.forall_mem_cons.2 ⟨subd18_0_444, List.forall_mem_cons.2 ⟨subd18_0_445, List.forall_mem_cons.2 ⟨subd18_0_446, List.forall_mem_cons.2 ⟨subd18_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_448 : subd18_0 [1, 0, 12] = true := by decide +kernel
theorem subd18_0_449 : subd18_0 [1, 1, -13] = true := by decide +kernel
theorem subd18_0_450 : subd18_0 [1, 1, -12] = true := by decide +kernel
theorem subd18_0_451 : subd18_0 [1, 1, -11] = true := by decide +kernel
theorem subd18_0_452 : subd18_0 [1, 1, -10] = true := by decide +kernel
theorem subd18_0_453 : subd18_0 [1, 1, -9] = true := by decide +kernel
theorem subd18_0_454 : subd18_0 [1, 1, -8] = true := by decide +kernel
theorem subd18_0_455 : subd18_0 [1, 1, -7] = true := by decide +kernel
theorem subd18_0_456 : subd18_0 [1, 1, -6] = true := by decide +kernel
theorem subd18_0_457 : subd18_0 [1, 1, -5] = true := by decide +kernel
theorem subd18_0_458 : subd18_0 [1, 1, -4] = true := by decide +kernel
theorem subd18_0_459 : subd18_0 [1, 1, -3] = true := by decide +kernel
theorem subd18_0_460 : subd18_0 [1, 1, -2] = true := by decide +kernel
theorem subd18_0_461 : subd18_0 [1, 1, -1] = true := by decide +kernel
theorem subd18_0_462 : subd18_0 [1, 1, 0] = true := by decide +kernel
theorem subd18_0_463 : subd18_0 [1, 1, 1] = true := by decide +kernel
theorem subd18_0_464 : subd18_0 [1, 1, 2] = true := by decide +kernel
theorem subd18_0_465 : subd18_0 [1, 1, 3] = true := by decide +kernel
theorem subd18_0_466 : subd18_0 [1, 1, 4] = true := by decide +kernel
theorem subd18_0_467 : subd18_0 [1, 1, 5] = true := by decide +kernel
theorem subd18_0_468 : subd18_0 [1, 1, 6] = true := by decide +kernel
theorem subd18_0_469 : subd18_0 [1, 1, 7] = true := by decide +kernel
theorem subd18_0_470 : subd18_0 [1, 1, 8] = true := by decide +kernel
theorem subd18_0_471 : subd18_0 [1, 1, 9] = true := by decide +kernel
theorem subd18_0_472 : subd18_0 [1, 1, 10] = true := by decide +kernel
theorem subd18_0_473 : subd18_0 [1, 1, 11] = true := by decide +kernel
theorem subd18_0_474 : subd18_0 [1, 1, 12] = true := by decide +kernel
theorem subd18_0_475 : subd18_0 [1, 2, -11] = true := by decide +kernel
theorem subd18_0_476 : subd18_0 [1, 2, -10] = true := by decide +kernel
theorem subd18_0_477 : subd18_0 [1, 2, -9] = true := by decide +kernel
theorem subd18_0_478 : subd18_0 [1, 2, -8] = true := by decide +kernel
theorem subd18_0_479 : subd18_0 [1, 2, -7] = true := by decide +kernel
theorem sbd18_0_14 : ∀ q ∈ blkd18_0_14, subd18_0 q = true := by
  unfold blkd18_0_14
  exact List.forall_mem_cons.2 ⟨subd18_0_448, List.forall_mem_cons.2 ⟨subd18_0_449, List.forall_mem_cons.2 ⟨subd18_0_450, List.forall_mem_cons.2 ⟨subd18_0_451, List.forall_mem_cons.2 ⟨subd18_0_452, List.forall_mem_cons.2 ⟨subd18_0_453, List.forall_mem_cons.2 ⟨subd18_0_454, List.forall_mem_cons.2 ⟨subd18_0_455, List.forall_mem_cons.2 ⟨subd18_0_456, List.forall_mem_cons.2 ⟨subd18_0_457, List.forall_mem_cons.2 ⟨subd18_0_458, List.forall_mem_cons.2 ⟨subd18_0_459, List.forall_mem_cons.2 ⟨subd18_0_460, List.forall_mem_cons.2 ⟨subd18_0_461, List.forall_mem_cons.2 ⟨subd18_0_462, List.forall_mem_cons.2 ⟨subd18_0_463, List.forall_mem_cons.2 ⟨subd18_0_464, List.forall_mem_cons.2 ⟨subd18_0_465, List.forall_mem_cons.2 ⟨subd18_0_466, List.forall_mem_cons.2 ⟨subd18_0_467, List.forall_mem_cons.2 ⟨subd18_0_468, List.forall_mem_cons.2 ⟨subd18_0_469, List.forall_mem_cons.2 ⟨subd18_0_470, List.forall_mem_cons.2 ⟨subd18_0_471, List.forall_mem_cons.2 ⟨subd18_0_472, List.forall_mem_cons.2 ⟨subd18_0_473, List.forall_mem_cons.2 ⟨subd18_0_474, List.forall_mem_cons.2 ⟨subd18_0_475, List.forall_mem_cons.2 ⟨subd18_0_476, List.forall_mem_cons.2 ⟨subd18_0_477, List.forall_mem_cons.2 ⟨subd18_0_478, List.forall_mem_cons.2 ⟨subd18_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_480 : subd18_0 [1, 2, -6] = true := by decide +kernel
theorem subd18_0_481 : subd18_0 [1, 2, -5] = true := by decide +kernel
theorem subd18_0_482 : subd18_0 [1, 2, -4] = true := by decide +kernel
theorem subd18_0_483 : subd18_0 [1, 2, -3] = true := by decide +kernel
theorem subd18_0_484 : subd18_0 [1, 2, -2] = true := by decide +kernel
theorem subd18_0_485 : subd18_0 [1, 2, -1] = true := by decide +kernel
theorem subd18_0_486 : subd18_0 [1, 2, 0] = true := by decide +kernel
theorem subd18_0_487 : subd18_0 [1, 2, 1] = true := by decide +kernel
theorem subd18_0_488 : subd18_0 [1, 2, 2] = true := by decide +kernel
theorem subd18_0_489 : subd18_0 [1, 2, 3] = true := by decide +kernel
theorem subd18_0_490 : subd18_0 [1, 2, 4] = true := by decide +kernel
theorem subd18_0_491 : subd18_0 [1, 2, 5] = true := by decide +kernel
theorem subd18_0_492 : subd18_0 [1, 2, 6] = true := by decide +kernel
theorem subd18_0_493 : subd18_0 [1, 2, 7] = true := by decide +kernel
theorem subd18_0_494 : subd18_0 [1, 2, 8] = true := by decide +kernel
theorem subd18_0_495 : subd18_0 [1, 2, 9] = true := by decide +kernel
theorem subd18_0_496 : subd18_0 [1, 2, 10] = true := by decide +kernel
theorem subd18_0_497 : subd18_0 [1, 3, -8] = true := by decide +kernel
theorem subd18_0_498 : subd18_0 [1, 3, -7] = true := by decide +kernel
theorem subd18_0_499 : subd18_0 [1, 3, -6] = true := by decide +kernel
theorem subd18_0_500 : subd18_0 [1, 3, -5] = true := by decide +kernel
theorem subd18_0_501 : subd18_0 [1, 3, -4] = true := by decide +kernel
theorem subd18_0_502 : subd18_0 [1, 3, -3] = true := by decide +kernel
theorem subd18_0_503 : subd18_0 [1, 3, -2] = true := by decide +kernel
theorem subd18_0_504 : subd18_0 [1, 3, -1] = true := by decide +kernel
theorem subd18_0_505 : subd18_0 [1, 3, 0] = true := by decide +kernel
theorem subd18_0_506 : subd18_0 [1, 3, 1] = true := by decide +kernel
theorem subd18_0_507 : subd18_0 [1, 3, 2] = true := by decide +kernel
theorem subd18_0_508 : subd18_0 [1, 3, 3] = true := by decide +kernel
theorem subd18_0_509 : subd18_0 [1, 3, 4] = true := by decide +kernel
theorem subd18_0_510 : subd18_0 [1, 3, 5] = true := by decide +kernel
theorem subd18_0_511 : subd18_0 [1, 3, 6] = true := by decide +kernel
theorem sbd18_0_15 : ∀ q ∈ blkd18_0_15, subd18_0 q = true := by
  unfold blkd18_0_15
  exact List.forall_mem_cons.2 ⟨subd18_0_480, List.forall_mem_cons.2 ⟨subd18_0_481, List.forall_mem_cons.2 ⟨subd18_0_482, List.forall_mem_cons.2 ⟨subd18_0_483, List.forall_mem_cons.2 ⟨subd18_0_484, List.forall_mem_cons.2 ⟨subd18_0_485, List.forall_mem_cons.2 ⟨subd18_0_486, List.forall_mem_cons.2 ⟨subd18_0_487, List.forall_mem_cons.2 ⟨subd18_0_488, List.forall_mem_cons.2 ⟨subd18_0_489, List.forall_mem_cons.2 ⟨subd18_0_490, List.forall_mem_cons.2 ⟨subd18_0_491, List.forall_mem_cons.2 ⟨subd18_0_492, List.forall_mem_cons.2 ⟨subd18_0_493, List.forall_mem_cons.2 ⟨subd18_0_494, List.forall_mem_cons.2 ⟨subd18_0_495, List.forall_mem_cons.2 ⟨subd18_0_496, List.forall_mem_cons.2 ⟨subd18_0_497, List.forall_mem_cons.2 ⟨subd18_0_498, List.forall_mem_cons.2 ⟨subd18_0_499, List.forall_mem_cons.2 ⟨subd18_0_500, List.forall_mem_cons.2 ⟨subd18_0_501, List.forall_mem_cons.2 ⟨subd18_0_502, List.forall_mem_cons.2 ⟨subd18_0_503, List.forall_mem_cons.2 ⟨subd18_0_504, List.forall_mem_cons.2 ⟨subd18_0_505, List.forall_mem_cons.2 ⟨subd18_0_506, List.forall_mem_cons.2 ⟨subd18_0_507, List.forall_mem_cons.2 ⟨subd18_0_508, List.forall_mem_cons.2 ⟨subd18_0_509, List.forall_mem_cons.2 ⟨subd18_0_510, List.forall_mem_cons.2 ⟨subd18_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_512 : subd18_0 [1, 3, 7] = true := by decide +kernel
theorem subd18_0_513 : subd18_0 [2, -3] = true := by decide +kernel
theorem subd18_0_514 : subd18_0 [2, -2] = true := by decide +kernel
theorem subd18_0_515 : subd18_0 [2, -1, -8] = true := by decide +kernel
theorem subd18_0_516 : subd18_0 [2, -1, -7] = true := by decide +kernel
theorem subd18_0_517 : subd18_0 [2, -1, -6] = true := by decide +kernel
theorem subd18_0_518 : subd18_0 [2, -1, -5] = true := by decide +kernel
theorem subd18_0_519 : subd18_0 [2, -1, -4] = true := by decide +kernel
theorem subd18_0_520 : subd18_0 [2, -1, -3] = true := by decide +kernel
theorem subd18_0_521 : subd18_0 [2, -1, -2] = true := by decide +kernel
theorem subd18_0_522 : subd18_0 [2, -1, -1] = true := by decide +kernel
theorem subd18_0_523 : subd18_0 [2, -1, 0] = true := by decide +kernel
theorem subd18_0_524 : subd18_0 [2, -1, 1] = true := by decide +kernel
theorem subd18_0_525 : subd18_0 [2, -1, 2] = true := by decide +kernel
theorem subd18_0_526 : subd18_0 [2, -1, 3] = true := by decide +kernel
theorem subd18_0_527 : subd18_0 [2, -1, 4] = true := by decide +kernel
theorem subd18_0_528 : subd18_0 [2, -1, 5] = true := by decide +kernel
theorem subd18_0_529 : subd18_0 [2, -1, 6] = true := by decide +kernel
theorem subd18_0_530 : subd18_0 [2, -1, 7] = true := by decide +kernel
theorem subd18_0_531 : subd18_0 [2, -1, 8] = true := by decide +kernel
theorem subd18_0_532 : subd18_0 [2, -1, 9] = true := by decide +kernel
theorem subd18_0_533 : subd18_0 [2, 0, -10] = true := by decide +kernel
theorem subd18_0_534 : subd18_0 [2, 0, -9] = true := by decide +kernel
theorem subd18_0_535 : subd18_0 [2, 0, -8] = true := by decide +kernel
theorem subd18_0_536 : subd18_0 [2, 0, -7] = true := by decide +kernel
theorem subd18_0_537 : subd18_0 [2, 0, -6] = true := by decide +kernel
theorem subd18_0_538 : subd18_0 [2, 0, -5] = true := by decide +kernel
theorem subd18_0_539 : subd18_0 [2, 0, -4] = true := by decide +kernel
theorem subd18_0_540 : subd18_0 [2, 0, -3] = true := by decide +kernel
theorem subd18_0_541 : subd18_0 [2, 0, -2] = true := by decide +kernel
theorem subd18_0_542 : subd18_0 [2, 0, -1] = true := by decide +kernel
theorem subd18_0_543 : subd18_0 [2, 0, 0] = true := by decide +kernel
theorem sbd18_0_16 : ∀ q ∈ blkd18_0_16, subd18_0 q = true := by
  unfold blkd18_0_16
  exact List.forall_mem_cons.2 ⟨subd18_0_512, List.forall_mem_cons.2 ⟨subd18_0_513, List.forall_mem_cons.2 ⟨subd18_0_514, List.forall_mem_cons.2 ⟨subd18_0_515, List.forall_mem_cons.2 ⟨subd18_0_516, List.forall_mem_cons.2 ⟨subd18_0_517, List.forall_mem_cons.2 ⟨subd18_0_518, List.forall_mem_cons.2 ⟨subd18_0_519, List.forall_mem_cons.2 ⟨subd18_0_520, List.forall_mem_cons.2 ⟨subd18_0_521, List.forall_mem_cons.2 ⟨subd18_0_522, List.forall_mem_cons.2 ⟨subd18_0_523, List.forall_mem_cons.2 ⟨subd18_0_524, List.forall_mem_cons.2 ⟨subd18_0_525, List.forall_mem_cons.2 ⟨subd18_0_526, List.forall_mem_cons.2 ⟨subd18_0_527, List.forall_mem_cons.2 ⟨subd18_0_528, List.forall_mem_cons.2 ⟨subd18_0_529, List.forall_mem_cons.2 ⟨subd18_0_530, List.forall_mem_cons.2 ⟨subd18_0_531, List.forall_mem_cons.2 ⟨subd18_0_532, List.forall_mem_cons.2 ⟨subd18_0_533, List.forall_mem_cons.2 ⟨subd18_0_534, List.forall_mem_cons.2 ⟨subd18_0_535, List.forall_mem_cons.2 ⟨subd18_0_536, List.forall_mem_cons.2 ⟨subd18_0_537, List.forall_mem_cons.2 ⟨subd18_0_538, List.forall_mem_cons.2 ⟨subd18_0_539, List.forall_mem_cons.2 ⟨subd18_0_540, List.forall_mem_cons.2 ⟨subd18_0_541, List.forall_mem_cons.2 ⟨subd18_0_542, List.forall_mem_cons.2 ⟨subd18_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_544 : subd18_0 [2, 0, 1] = true := by decide +kernel
theorem subd18_0_545 : subd18_0 [2, 0, 2] = true := by decide +kernel
theorem subd18_0_546 : subd18_0 [2, 0, 3] = true := by decide +kernel
theorem subd18_0_547 : subd18_0 [2, 0, 4] = true := by decide +kernel
theorem subd18_0_548 : subd18_0 [2, 0, 5] = true := by decide +kernel
theorem subd18_0_549 : subd18_0 [2, 0, 6] = true := by decide +kernel
theorem subd18_0_550 : subd18_0 [2, 0, 7] = true := by decide +kernel
theorem subd18_0_551 : subd18_0 [2, 0, 8] = true := by decide +kernel
theorem subd18_0_552 : subd18_0 [2, 0, 9] = true := by decide +kernel
theorem subd18_0_553 : subd18_0 [2, 0, 10] = true := by decide +kernel
theorem subd18_0_554 : subd18_0 [2, 1, -10] = true := by decide +kernel
theorem subd18_0_555 : subd18_0 [2, 1, -9] = true := by decide +kernel
theorem subd18_0_556 : subd18_0 [2, 1, -8] = true := by decide +kernel
theorem subd18_0_557 : subd18_0 [2, 1, -7] = true := by decide +kernel
theorem subd18_0_558 : subd18_0 [2, 1, -6] = true := by decide +kernel
theorem subd18_0_559 : subd18_0 [2, 1, -5] = true := by decide +kernel
theorem subd18_0_560 : subd18_0 [2, 1, -4] = true := by decide +kernel
theorem subd18_0_561 : subd18_0 [2, 1, -3] = true := by decide +kernel
theorem subd18_0_562 : subd18_0 [2, 1, -2] = true := by decide +kernel
theorem subd18_0_563 : subd18_0 [2, 1, -1] = true := by decide +kernel
theorem subd18_0_564 : subd18_0 [2, 1, 0] = true := by decide +kernel
theorem subd18_0_565 : subd18_0 [2, 1, 1] = true := by decide +kernel
theorem subd18_0_566 : subd18_0 [2, 1, 2] = true := by decide +kernel
theorem subd18_0_567 : subd18_0 [2, 1, 3] = true := by decide +kernel
theorem subd18_0_568 : subd18_0 [2, 1, 4] = true := by decide +kernel
theorem subd18_0_569 : subd18_0 [2, 1, 5] = true := by decide +kernel
theorem subd18_0_570 : subd18_0 [2, 1, 6] = true := by decide +kernel
theorem subd18_0_571 : subd18_0 [2, 1, 7] = true := by decide +kernel
theorem subd18_0_572 : subd18_0 [2, 1, 8] = true := by decide +kernel
theorem subd18_0_573 : subd18_0 [2, 1, 9] = true := by decide +kernel
theorem subd18_0_574 : subd18_0 [2, 1, 10] = true := by decide +kernel
theorem subd18_0_575 : subd18_0 [2, 2, -9] = true := by decide +kernel
theorem sbd18_0_17 : ∀ q ∈ blkd18_0_17, subd18_0 q = true := by
  unfold blkd18_0_17
  exact List.forall_mem_cons.2 ⟨subd18_0_544, List.forall_mem_cons.2 ⟨subd18_0_545, List.forall_mem_cons.2 ⟨subd18_0_546, List.forall_mem_cons.2 ⟨subd18_0_547, List.forall_mem_cons.2 ⟨subd18_0_548, List.forall_mem_cons.2 ⟨subd18_0_549, List.forall_mem_cons.2 ⟨subd18_0_550, List.forall_mem_cons.2 ⟨subd18_0_551, List.forall_mem_cons.2 ⟨subd18_0_552, List.forall_mem_cons.2 ⟨subd18_0_553, List.forall_mem_cons.2 ⟨subd18_0_554, List.forall_mem_cons.2 ⟨subd18_0_555, List.forall_mem_cons.2 ⟨subd18_0_556, List.forall_mem_cons.2 ⟨subd18_0_557, List.forall_mem_cons.2 ⟨subd18_0_558, List.forall_mem_cons.2 ⟨subd18_0_559, List.forall_mem_cons.2 ⟨subd18_0_560, List.forall_mem_cons.2 ⟨subd18_0_561, List.forall_mem_cons.2 ⟨subd18_0_562, List.forall_mem_cons.2 ⟨subd18_0_563, List.forall_mem_cons.2 ⟨subd18_0_564, List.forall_mem_cons.2 ⟨subd18_0_565, List.forall_mem_cons.2 ⟨subd18_0_566, List.forall_mem_cons.2 ⟨subd18_0_567, List.forall_mem_cons.2 ⟨subd18_0_568, List.forall_mem_cons.2 ⟨subd18_0_569, List.forall_mem_cons.2 ⟨subd18_0_570, List.forall_mem_cons.2 ⟨subd18_0_571, List.forall_mem_cons.2 ⟨subd18_0_572, List.forall_mem_cons.2 ⟨subd18_0_573, List.forall_mem_cons.2 ⟨subd18_0_574, List.forall_mem_cons.2 ⟨subd18_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_576 : subd18_0 [2, 2, -8] = true := by decide +kernel
theorem subd18_0_577 : subd18_0 [2, 2, -7] = true := by decide +kernel
theorem subd18_0_578 : subd18_0 [2, 2, -6] = true := by decide +kernel
theorem subd18_0_579 : subd18_0 [2, 2, -5] = true := by decide +kernel
theorem subd18_0_580 : subd18_0 [2, 2, -4] = true := by decide +kernel
theorem subd18_0_581 : subd18_0 [2, 2, -3] = true := by decide +kernel
theorem subd18_0_582 : subd18_0 [2, 2, -2] = true := by decide +kernel
theorem subd18_0_583 : subd18_0 [2, 2, -1] = true := by decide +kernel
theorem subd18_0_584 : subd18_0 [2, 2, 0] = true := by decide +kernel
theorem subd18_0_585 : subd18_0 [2, 2, 1] = true := by decide +kernel
theorem subd18_0_586 : subd18_0 [2, 2, 2] = true := by decide +kernel
theorem subd18_0_587 : subd18_0 [2, 2, 3] = true := by decide +kernel
theorem subd18_0_588 : subd18_0 [2, 2, 4] = true := by decide +kernel
theorem subd18_0_589 : subd18_0 [2, 2, 5] = true := by decide +kernel
theorem subd18_0_590 : subd18_0 [2, 2, 6] = true := by decide +kernel
theorem subd18_0_591 : subd18_0 [2, 2, 7] = true := by decide +kernel
theorem subd18_0_592 : subd18_0 [2, 2, 8] = true := by decide +kernel
theorem subd18_0_593 : subd18_0 [2, 2, 9] = true := by decide +kernel
theorem subd18_0_594 : subd18_0 [2, 3] = true := by decide +kernel
theorem subd18_0_595 : subd18_0 [3, -1] = true := by decide +kernel
theorem subd18_0_596 : subd18_0 [3, 0] = true := by decide +kernel
theorem subd18_0_597 : subd18_0 [3, 1] = true := by decide +kernel
theorem subd18_0_598 : subd18_0 [3, 2] = true := by decide +kernel
theorem sbd18_0_18 : ∀ q ∈ blkd18_0_18, subd18_0 q = true := by
  unfold blkd18_0_18
  exact List.forall_mem_cons.2 ⟨subd18_0_576, List.forall_mem_cons.2 ⟨subd18_0_577, List.forall_mem_cons.2 ⟨subd18_0_578, List.forall_mem_cons.2 ⟨subd18_0_579, List.forall_mem_cons.2 ⟨subd18_0_580, List.forall_mem_cons.2 ⟨subd18_0_581, List.forall_mem_cons.2 ⟨subd18_0_582, List.forall_mem_cons.2 ⟨subd18_0_583, List.forall_mem_cons.2 ⟨subd18_0_584, List.forall_mem_cons.2 ⟨subd18_0_585, List.forall_mem_cons.2 ⟨subd18_0_586, List.forall_mem_cons.2 ⟨subd18_0_587, List.forall_mem_cons.2 ⟨subd18_0_588, List.forall_mem_cons.2 ⟨subd18_0_589, List.forall_mem_cons.2 ⟨subd18_0_590, List.forall_mem_cons.2 ⟨subd18_0_591, List.forall_mem_cons.2 ⟨subd18_0_592, List.forall_mem_cons.2 ⟨subd18_0_593, List.forall_mem_cons.2 ⟨subd18_0_594, List.forall_mem_cons.2 ⟨subd18_0_595, List.forall_mem_cons.2 ⟨subd18_0_596, List.forall_mem_cons.2 ⟨subd18_0_597, List.forall_mem_cons.2 ⟨subd18_0_598, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd18_1 : ldCheck G d18_1.U d18_1.ms ldd18_1 = true := by decide +kernel
theorem pre_okd18_1 : subPre G cell18 d18_1 = true := by decide +kernel
theorem subd18_1_0 : subd18_1 [-6] = true := by decide +kernel
theorem subd18_1_1 : subd18_1 [-5, -7] = true := by decide +kernel
theorem subd18_1_2 : subd18_1 [-5, -6] = true := by decide +kernel
theorem subd18_1_3 : subd18_1 [-5, -5] = true := by decide +kernel
theorem subd18_1_4 : subd18_1 [-5, -4] = true := by decide +kernel
theorem subd18_1_5 : subd18_1 [-5, -3] = true := by decide +kernel
theorem subd18_1_6 : subd18_1 [-5, -2] = true := by decide +kernel
theorem subd18_1_7 : subd18_1 [-5, -1] = true := by decide +kernel
theorem subd18_1_8 : subd18_1 [-5, 0] = true := by decide +kernel
theorem subd18_1_9 : subd18_1 [-5, 1] = true := by decide +kernel
theorem subd18_1_10 : subd18_1 [-5, 2] = true := by decide +kernel
theorem subd18_1_11 : subd18_1 [-4, -7] = true := by decide +kernel
theorem subd18_1_12 : subd18_1 [-4, -6] = true := by decide +kernel
theorem subd18_1_13 : subd18_1 [-4, -5] = true := by decide +kernel
theorem subd18_1_14 : subd18_1 [-4, -4] = true := by decide +kernel
theorem subd18_1_15 : subd18_1 [-4, -3] = true := by decide +kernel
theorem subd18_1_16 : subd18_1 [-4, -2] = true := by decide +kernel
theorem subd18_1_17 : subd18_1 [-4, -1] = true := by decide +kernel
theorem subd18_1_18 : subd18_1 [-4, 0] = true := by decide +kernel
theorem subd18_1_19 : subd18_1 [-4, 1] = true := by decide +kernel
theorem subd18_1_20 : subd18_1 [-4, 2] = true := by decide +kernel
theorem subd18_1_21 : subd18_1 [-4, 3] = true := by decide +kernel
theorem subd18_1_22 : subd18_1 [-4, 4] = true := by decide +kernel
theorem subd18_1_23 : subd18_1 [-3, -8] = true := by decide +kernel
theorem subd18_1_24 : subd18_1 [-3, -7] = true := by decide +kernel
theorem subd18_1_25 : subd18_1 [-3, -6] = true := by decide +kernel
theorem subd18_1_26 : subd18_1 [-3, -5] = true := by decide +kernel
theorem subd18_1_27 : subd18_1 [-3, -4] = true := by decide +kernel
theorem subd18_1_28 : subd18_1 [-3, -3, -7] = true := by decide +kernel
theorem subd18_1_29 : subd18_1 [-3, -3, -6] = true := by decide +kernel
theorem subd18_1_30 : subd18_1 [-3, -3, -5] = true := by decide +kernel
theorem subd18_1_31 : subd18_1 [-3, -3, -4] = true := by decide +kernel
theorem sbd18_1_0 : ∀ q ∈ blkd18_1_0, subd18_1 q = true := by
  unfold blkd18_1_0
  exact List.forall_mem_cons.2 ⟨subd18_1_0, List.forall_mem_cons.2 ⟨subd18_1_1, List.forall_mem_cons.2 ⟨subd18_1_2, List.forall_mem_cons.2 ⟨subd18_1_3, List.forall_mem_cons.2 ⟨subd18_1_4, List.forall_mem_cons.2 ⟨subd18_1_5, List.forall_mem_cons.2 ⟨subd18_1_6, List.forall_mem_cons.2 ⟨subd18_1_7, List.forall_mem_cons.2 ⟨subd18_1_8, List.forall_mem_cons.2 ⟨subd18_1_9, List.forall_mem_cons.2 ⟨subd18_1_10, List.forall_mem_cons.2 ⟨subd18_1_11, List.forall_mem_cons.2 ⟨subd18_1_12, List.forall_mem_cons.2 ⟨subd18_1_13, List.forall_mem_cons.2 ⟨subd18_1_14, List.forall_mem_cons.2 ⟨subd18_1_15, List.forall_mem_cons.2 ⟨subd18_1_16, List.forall_mem_cons.2 ⟨subd18_1_17, List.forall_mem_cons.2 ⟨subd18_1_18, List.forall_mem_cons.2 ⟨subd18_1_19, List.forall_mem_cons.2 ⟨subd18_1_20, List.forall_mem_cons.2 ⟨subd18_1_21, List.forall_mem_cons.2 ⟨subd18_1_22, List.forall_mem_cons.2 ⟨subd18_1_23, List.forall_mem_cons.2 ⟨subd18_1_24, List.forall_mem_cons.2 ⟨subd18_1_25, List.forall_mem_cons.2 ⟨subd18_1_26, List.forall_mem_cons.2 ⟨subd18_1_27, List.forall_mem_cons.2 ⟨subd18_1_28, List.forall_mem_cons.2 ⟨subd18_1_29, List.forall_mem_cons.2 ⟨subd18_1_30, List.forall_mem_cons.2 ⟨subd18_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_32 : subd18_1 [-3, -3, -3] = true := by decide +kernel
theorem subd18_1_33 : subd18_1 [-3, -3, -2] = true := by decide +kernel
theorem subd18_1_34 : subd18_1 [-3, -3, -1] = true := by decide +kernel
theorem subd18_1_35 : subd18_1 [-3, -3, 0] = true := by decide +kernel
theorem subd18_1_36 : subd18_1 [-3, -3, 1] = true := by decide +kernel
theorem subd18_1_37 : subd18_1 [-3, -3, 2] = true := by decide +kernel
theorem subd18_1_38 : subd18_1 [-3, -3, 3] = true := by decide +kernel
theorem subd18_1_39 : subd18_1 [-3, -3, 4] = true := by decide +kernel
theorem subd18_1_40 : subd18_1 [-3, -3, 5] = true := by decide +kernel
theorem subd18_1_41 : subd18_1 [-3, -3, 6] = true := by decide +kernel
theorem subd18_1_42 : subd18_1 [-3, -2, -8] = true := by decide +kernel
theorem subd18_1_43 : subd18_1 [-3, -2, -7] = true := by decide +kernel
theorem subd18_1_44 : subd18_1 [-3, -2, -6] = true := by decide +kernel
theorem subd18_1_45 : subd18_1 [-3, -2, -5] = true := by decide +kernel
theorem subd18_1_46 : subd18_1 [-3, -2, -4] = true := by decide +kernel
theorem subd18_1_47 : subd18_1 [-3, -2, -3] = true := by decide +kernel
theorem subd18_1_48 : subd18_1 [-3, -2, -2] = true := by decide +kernel
theorem subd18_1_49 : subd18_1 [-3, -2, -1] = true := by decide +kernel
theorem subd18_1_50 : subd18_1 [-3, -2, 0] = true := by decide +kernel
theorem subd18_1_51 : subd18_1 [-3, -2, 1] = true := by decide +kernel
theorem subd18_1_52 : subd18_1 [-3, -2, 2] = true := by decide +kernel
theorem subd18_1_53 : subd18_1 [-3, -2, 3] = true := by decide +kernel
theorem subd18_1_54 : subd18_1 [-3, -2, 4] = true := by decide +kernel
theorem subd18_1_55 : subd18_1 [-3, -2, 5] = true := by decide +kernel
theorem subd18_1_56 : subd18_1 [-3, -2, 6] = true := by decide +kernel
theorem subd18_1_57 : subd18_1 [-3, -1, -8] = true := by decide +kernel
theorem subd18_1_58 : subd18_1 [-3, -1, -7] = true := by decide +kernel
theorem subd18_1_59 : subd18_1 [-3, -1, -6] = true := by decide +kernel
theorem subd18_1_60 : subd18_1 [-3, -1, -5] = true := by decide +kernel
theorem subd18_1_61 : subd18_1 [-3, -1, -4] = true := by decide +kernel
theorem subd18_1_62 : subd18_1 [-3, -1, -3] = true := by decide +kernel
theorem subd18_1_63 : subd18_1 [-3, -1, -2] = true := by decide +kernel
theorem sbd18_1_1 : ∀ q ∈ blkd18_1_1, subd18_1 q = true := by
  unfold blkd18_1_1
  exact List.forall_mem_cons.2 ⟨subd18_1_32, List.forall_mem_cons.2 ⟨subd18_1_33, List.forall_mem_cons.2 ⟨subd18_1_34, List.forall_mem_cons.2 ⟨subd18_1_35, List.forall_mem_cons.2 ⟨subd18_1_36, List.forall_mem_cons.2 ⟨subd18_1_37, List.forall_mem_cons.2 ⟨subd18_1_38, List.forall_mem_cons.2 ⟨subd18_1_39, List.forall_mem_cons.2 ⟨subd18_1_40, List.forall_mem_cons.2 ⟨subd18_1_41, List.forall_mem_cons.2 ⟨subd18_1_42, List.forall_mem_cons.2 ⟨subd18_1_43, List.forall_mem_cons.2 ⟨subd18_1_44, List.forall_mem_cons.2 ⟨subd18_1_45, List.forall_mem_cons.2 ⟨subd18_1_46, List.forall_mem_cons.2 ⟨subd18_1_47, List.forall_mem_cons.2 ⟨subd18_1_48, List.forall_mem_cons.2 ⟨subd18_1_49, List.forall_mem_cons.2 ⟨subd18_1_50, List.forall_mem_cons.2 ⟨subd18_1_51, List.forall_mem_cons.2 ⟨subd18_1_52, List.forall_mem_cons.2 ⟨subd18_1_53, List.forall_mem_cons.2 ⟨subd18_1_54, List.forall_mem_cons.2 ⟨subd18_1_55, List.forall_mem_cons.2 ⟨subd18_1_56, List.forall_mem_cons.2 ⟨subd18_1_57, List.forall_mem_cons.2 ⟨subd18_1_58, List.forall_mem_cons.2 ⟨subd18_1_59, List.forall_mem_cons.2 ⟨subd18_1_60, List.forall_mem_cons.2 ⟨subd18_1_61, List.forall_mem_cons.2 ⟨subd18_1_62, List.forall_mem_cons.2 ⟨subd18_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_64 : subd18_1 [-3, -1, -1] = true := by decide +kernel
theorem subd18_1_65 : subd18_1 [-3, -1, 0] = true := by decide +kernel
theorem subd18_1_66 : subd18_1 [-3, -1, 1] = true := by decide +kernel
theorem subd18_1_67 : subd18_1 [-3, -1, 2] = true := by decide +kernel
theorem subd18_1_68 : subd18_1 [-3, -1, 3] = true := by decide +kernel
theorem subd18_1_69 : subd18_1 [-3, -1, 4] = true := by decide +kernel
theorem subd18_1_70 : subd18_1 [-3, -1, 5] = true := by decide +kernel
theorem subd18_1_71 : subd18_1 [-3, -1, 6] = true := by decide +kernel
theorem subd18_1_72 : subd18_1 [-3, 0, -9] = true := by decide +kernel
theorem subd18_1_73 : subd18_1 [-3, 0, -8] = true := by decide +kernel
theorem subd18_1_74 : subd18_1 [-3, 0, -7] = true := by decide +kernel
theorem subd18_1_75 : subd18_1 [-3, 0, -6] = true := by decide +kernel
theorem subd18_1_76 : subd18_1 [-3, 0, -5] = true := by decide +kernel
theorem subd18_1_77 : subd18_1 [-3, 0, -4] = true := by decide +kernel
theorem subd18_1_78 : subd18_1 [-3, 0, -3] = true := by decide +kernel
theorem subd18_1_79 : subd18_1 [-3, 0, -2] = true := by decide +kernel
theorem subd18_1_80 : subd18_1 [-3, 0, -1] = true := by decide +kernel
theorem subd18_1_81 : subd18_1 [-3, 0, 0] = true := by decide +kernel
theorem subd18_1_82 : subd18_1 [-3, 0, 1] = true := by decide +kernel
theorem subd18_1_83 : subd18_1 [-3, 0, 2] = true := by decide +kernel
theorem subd18_1_84 : subd18_1 [-3, 0, 3] = true := by decide +kernel
theorem subd18_1_85 : subd18_1 [-3, 0, 4] = true := by decide +kernel
theorem subd18_1_86 : subd18_1 [-3, 0, 5] = true := by decide +kernel
theorem subd18_1_87 : subd18_1 [-3, 1, -9] = true := by decide +kernel
theorem subd18_1_88 : subd18_1 [-3, 1, -8] = true := by decide +kernel
theorem subd18_1_89 : subd18_1 [-3, 1, -7] = true := by decide +kernel
theorem subd18_1_90 : subd18_1 [-3, 1, -6] = true := by decide +kernel
theorem subd18_1_91 : subd18_1 [-3, 1, -5] = true := by decide +kernel
theorem subd18_1_92 : subd18_1 [-3, 1, -4] = true := by decide +kernel
theorem subd18_1_93 : subd18_1 [-3, 1, -3] = true := by decide +kernel
theorem subd18_1_94 : subd18_1 [-3, 1, -2] = true := by decide +kernel
theorem subd18_1_95 : subd18_1 [-3, 1, -1] = true := by decide +kernel
theorem sbd18_1_2 : ∀ q ∈ blkd18_1_2, subd18_1 q = true := by
  unfold blkd18_1_2
  exact List.forall_mem_cons.2 ⟨subd18_1_64, List.forall_mem_cons.2 ⟨subd18_1_65, List.forall_mem_cons.2 ⟨subd18_1_66, List.forall_mem_cons.2 ⟨subd18_1_67, List.forall_mem_cons.2 ⟨subd18_1_68, List.forall_mem_cons.2 ⟨subd18_1_69, List.forall_mem_cons.2 ⟨subd18_1_70, List.forall_mem_cons.2 ⟨subd18_1_71, List.forall_mem_cons.2 ⟨subd18_1_72, List.forall_mem_cons.2 ⟨subd18_1_73, List.forall_mem_cons.2 ⟨subd18_1_74, List.forall_mem_cons.2 ⟨subd18_1_75, List.forall_mem_cons.2 ⟨subd18_1_76, List.forall_mem_cons.2 ⟨subd18_1_77, List.forall_mem_cons.2 ⟨subd18_1_78, List.forall_mem_cons.2 ⟨subd18_1_79, List.forall_mem_cons.2 ⟨subd18_1_80, List.forall_mem_cons.2 ⟨subd18_1_81, List.forall_mem_cons.2 ⟨subd18_1_82, List.forall_mem_cons.2 ⟨subd18_1_83, List.forall_mem_cons.2 ⟨subd18_1_84, List.forall_mem_cons.2 ⟨subd18_1_85, List.forall_mem_cons.2 ⟨subd18_1_86, List.forall_mem_cons.2 ⟨subd18_1_87, List.forall_mem_cons.2 ⟨subd18_1_88, List.forall_mem_cons.2 ⟨subd18_1_89, List.forall_mem_cons.2 ⟨subd18_1_90, List.forall_mem_cons.2 ⟨subd18_1_91, List.forall_mem_cons.2 ⟨subd18_1_92, List.forall_mem_cons.2 ⟨subd18_1_93, List.forall_mem_cons.2 ⟨subd18_1_94, List.forall_mem_cons.2 ⟨subd18_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
