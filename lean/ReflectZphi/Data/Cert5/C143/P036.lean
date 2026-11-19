import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_3_384 : subd15_3 [0, 0, -9] = true := by decide +kernel
theorem subd15_3_385 : subd15_3 [0, 0, -8] = true := by decide +kernel
theorem subd15_3_386 : subd15_3 [0, 0, -7] = true := by decide +kernel
theorem subd15_3_387 : subd15_3 [0, 0, -6] = true := by decide +kernel
theorem subd15_3_388 : subd15_3 [0, 0, -5] = true := by decide +kernel
theorem subd15_3_389 : subd15_3 [0, 0, -4] = true := by decide +kernel
theorem subd15_3_390 : subd15_3 [0, 0, -3] = true := by decide +kernel
theorem subd15_3_391 : subd15_3 [0, 0, -2] = true := by decide +kernel
theorem subd15_3_392 : subd15_3 [0, 0, -1] = true := by decide +kernel
theorem subd15_3_393 : subd15_3 [0, 0, 0] = true := by decide +kernel
theorem subd15_3_394 : subd15_3 [0, 0, 1] = true := by decide +kernel
theorem subd15_3_395 : subd15_3 [0, 0, 2] = true := by decide +kernel
theorem subd15_3_396 : subd15_3 [0, 0, 3] = true := by decide +kernel
theorem subd15_3_397 : subd15_3 [0, 0, 4] = true := by decide +kernel
theorem subd15_3_398 : subd15_3 [0, 0, 5] = true := by decide +kernel
theorem subd15_3_399 : subd15_3 [0, 0, 6] = true := by decide +kernel
theorem subd15_3_400 : subd15_3 [0, 0, 7] = true := by decide +kernel
theorem subd15_3_401 : subd15_3 [0, 0, 8] = true := by decide +kernel
theorem subd15_3_402 : subd15_3 [0, 1, -9] = true := by decide +kernel
theorem subd15_3_403 : subd15_3 [0, 1, -8] = true := by decide +kernel
theorem subd15_3_404 : subd15_3 [0, 1, -7] = true := by decide +kernel
theorem subd15_3_405 : subd15_3 [0, 1, -6] = true := by decide +kernel
theorem subd15_3_406 : subd15_3 [0, 1, -5] = true := by decide +kernel
theorem subd15_3_407 : subd15_3 [0, 1, -4] = true := by decide +kernel
theorem subd15_3_408 : subd15_3 [0, 1, -3] = true := by decide +kernel
theorem subd15_3_409 : subd15_3 [0, 1, -2] = true := by decide +kernel
theorem subd15_3_410 : subd15_3 [0, 1, -1] = true := by decide +kernel
theorem subd15_3_411 : subd15_3 [0, 1, 0] = true := by decide +kernel
theorem subd15_3_412 : subd15_3 [0, 1, 1] = true := by decide +kernel
theorem subd15_3_413 : subd15_3 [0, 1, 2] = true := by decide +kernel
theorem subd15_3_414 : subd15_3 [0, 1, 3] = true := by decide +kernel
theorem subd15_3_415 : subd15_3 [0, 1, 4] = true := by decide +kernel
theorem sbd15_3_12 : ∀ q ∈ blkd15_3_12, subd15_3 q = true := by
  unfold blkd15_3_12
  exact List.forall_mem_cons.2 ⟨subd15_3_384, List.forall_mem_cons.2 ⟨subd15_3_385, List.forall_mem_cons.2 ⟨subd15_3_386, List.forall_mem_cons.2 ⟨subd15_3_387, List.forall_mem_cons.2 ⟨subd15_3_388, List.forall_mem_cons.2 ⟨subd15_3_389, List.forall_mem_cons.2 ⟨subd15_3_390, List.forall_mem_cons.2 ⟨subd15_3_391, List.forall_mem_cons.2 ⟨subd15_3_392, List.forall_mem_cons.2 ⟨subd15_3_393, List.forall_mem_cons.2 ⟨subd15_3_394, List.forall_mem_cons.2 ⟨subd15_3_395, List.forall_mem_cons.2 ⟨subd15_3_396, List.forall_mem_cons.2 ⟨subd15_3_397, List.forall_mem_cons.2 ⟨subd15_3_398, List.forall_mem_cons.2 ⟨subd15_3_399, List.forall_mem_cons.2 ⟨subd15_3_400, List.forall_mem_cons.2 ⟨subd15_3_401, List.forall_mem_cons.2 ⟨subd15_3_402, List.forall_mem_cons.2 ⟨subd15_3_403, List.forall_mem_cons.2 ⟨subd15_3_404, List.forall_mem_cons.2 ⟨subd15_3_405, List.forall_mem_cons.2 ⟨subd15_3_406, List.forall_mem_cons.2 ⟨subd15_3_407, List.forall_mem_cons.2 ⟨subd15_3_408, List.forall_mem_cons.2 ⟨subd15_3_409, List.forall_mem_cons.2 ⟨subd15_3_410, List.forall_mem_cons.2 ⟨subd15_3_411, List.forall_mem_cons.2 ⟨subd15_3_412, List.forall_mem_cons.2 ⟨subd15_3_413, List.forall_mem_cons.2 ⟨subd15_3_414, List.forall_mem_cons.2 ⟨subd15_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_416 : subd15_3 [0, 1, 5] = true := by decide +kernel
theorem subd15_3_417 : subd15_3 [0, 1, 6] = true := by decide +kernel
theorem subd15_3_418 : subd15_3 [0, 1, 7] = true := by decide +kernel
theorem subd15_3_419 : subd15_3 [0, 1, 8] = true := by decide +kernel
theorem subd15_3_420 : subd15_3 [0, 2, -9] = true := by decide +kernel
theorem subd15_3_421 : subd15_3 [0, 2, -8] = true := by decide +kernel
theorem subd15_3_422 : subd15_3 [0, 2, -7] = true := by decide +kernel
theorem subd15_3_423 : subd15_3 [0, 2, -6] = true := by decide +kernel
theorem subd15_3_424 : subd15_3 [0, 2, -5] = true := by decide +kernel
theorem subd15_3_425 : subd15_3 [0, 2, -4] = true := by decide +kernel
theorem subd15_3_426 : subd15_3 [0, 2, -3] = true := by decide +kernel
theorem subd15_3_427 : subd15_3 [0, 2, -2] = true := by decide +kernel
theorem subd15_3_428 : subd15_3 [0, 2, -1] = true := by decide +kernel
theorem subd15_3_429 : subd15_3 [0, 2, 0] = true := by decide +kernel
theorem subd15_3_430 : subd15_3 [0, 2, 1] = true := by decide +kernel
theorem subd15_3_431 : subd15_3 [0, 2, 2] = true := by decide +kernel
theorem subd15_3_432 : subd15_3 [0, 2, 3] = true := by decide +kernel
theorem subd15_3_433 : subd15_3 [0, 2, 4] = true := by decide +kernel
theorem subd15_3_434 : subd15_3 [0, 2, 5] = true := by decide +kernel
theorem subd15_3_435 : subd15_3 [0, 2, 6] = true := by decide +kernel
theorem subd15_3_436 : subd15_3 [0, 2, 7] = true := by decide +kernel
theorem subd15_3_437 : subd15_3 [0, 3, -9] = true := by decide +kernel
theorem subd15_3_438 : subd15_3 [0, 3, -8] = true := by decide +kernel
theorem subd15_3_439 : subd15_3 [0, 3, -7] = true := by decide +kernel
theorem subd15_3_440 : subd15_3 [0, 3, -6] = true := by decide +kernel
theorem subd15_3_441 : subd15_3 [0, 3, -5] = true := by decide +kernel
theorem subd15_3_442 : subd15_3 [0, 3, -4] = true := by decide +kernel
theorem subd15_3_443 : subd15_3 [0, 3, -3] = true := by decide +kernel
theorem subd15_3_444 : subd15_3 [0, 3, -2] = true := by decide +kernel
theorem subd15_3_445 : subd15_3 [0, 3, -1] = true := by decide +kernel
theorem subd15_3_446 : subd15_3 [0, 3, 0] = true := by decide +kernel
theorem subd15_3_447 : subd15_3 [0, 3, 1] = true := by decide +kernel
theorem sbd15_3_13 : ∀ q ∈ blkd15_3_13, subd15_3 q = true := by
  unfold blkd15_3_13
  exact List.forall_mem_cons.2 ⟨subd15_3_416, List.forall_mem_cons.2 ⟨subd15_3_417, List.forall_mem_cons.2 ⟨subd15_3_418, List.forall_mem_cons.2 ⟨subd15_3_419, List.forall_mem_cons.2 ⟨subd15_3_420, List.forall_mem_cons.2 ⟨subd15_3_421, List.forall_mem_cons.2 ⟨subd15_3_422, List.forall_mem_cons.2 ⟨subd15_3_423, List.forall_mem_cons.2 ⟨subd15_3_424, List.forall_mem_cons.2 ⟨subd15_3_425, List.forall_mem_cons.2 ⟨subd15_3_426, List.forall_mem_cons.2 ⟨subd15_3_427, List.forall_mem_cons.2 ⟨subd15_3_428, List.forall_mem_cons.2 ⟨subd15_3_429, List.forall_mem_cons.2 ⟨subd15_3_430, List.forall_mem_cons.2 ⟨subd15_3_431, List.forall_mem_cons.2 ⟨subd15_3_432, List.forall_mem_cons.2 ⟨subd15_3_433, List.forall_mem_cons.2 ⟨subd15_3_434, List.forall_mem_cons.2 ⟨subd15_3_435, List.forall_mem_cons.2 ⟨subd15_3_436, List.forall_mem_cons.2 ⟨subd15_3_437, List.forall_mem_cons.2 ⟨subd15_3_438, List.forall_mem_cons.2 ⟨subd15_3_439, List.forall_mem_cons.2 ⟨subd15_3_440, List.forall_mem_cons.2 ⟨subd15_3_441, List.forall_mem_cons.2 ⟨subd15_3_442, List.forall_mem_cons.2 ⟨subd15_3_443, List.forall_mem_cons.2 ⟨subd15_3_444, List.forall_mem_cons.2 ⟨subd15_3_445, List.forall_mem_cons.2 ⟨subd15_3_446, List.forall_mem_cons.2 ⟨subd15_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_448 : subd15_3 [0, 3, 2] = true := by decide +kernel
theorem subd15_3_449 : subd15_3 [0, 3, 3] = true := by decide +kernel
theorem subd15_3_450 : subd15_3 [0, 3, 4] = true := by decide +kernel
theorem subd15_3_451 : subd15_3 [0, 3, 5] = true := by decide +kernel
theorem subd15_3_452 : subd15_3 [0, 3, 6] = true := by decide +kernel
theorem subd15_3_453 : subd15_3 [0, 4, -8] = true := by decide +kernel
theorem subd15_3_454 : subd15_3 [0, 4, -7] = true := by decide +kernel
theorem subd15_3_455 : subd15_3 [0, 4, -6] = true := by decide +kernel
theorem subd15_3_456 : subd15_3 [0, 4, -5] = true := by decide +kernel
theorem subd15_3_457 : subd15_3 [0, 4, -4] = true := by decide +kernel
theorem subd15_3_458 : subd15_3 [0, 4, -3] = true := by decide +kernel
theorem subd15_3_459 : subd15_3 [0, 4, -2] = true := by decide +kernel
theorem subd15_3_460 : subd15_3 [0, 4, -1] = true := by decide +kernel
theorem subd15_3_461 : subd15_3 [0, 4, 0] = true := by decide +kernel
theorem subd15_3_462 : subd15_3 [0, 4, 1] = true := by decide +kernel
theorem subd15_3_463 : subd15_3 [0, 4, 2] = true := by decide +kernel
theorem subd15_3_464 : subd15_3 [0, 4, 3] = true := by decide +kernel
theorem subd15_3_465 : subd15_3 [0, 4, 4] = true := by decide +kernel
theorem subd15_3_466 : subd15_3 [0, 5] = true := by decide +kernel
theorem subd15_3_467 : subd15_3 [1, -6] = true := by decide +kernel
theorem subd15_3_468 : subd15_3 [1, -5] = true := by decide +kernel
theorem subd15_3_469 : subd15_3 [1, -4] = true := by decide +kernel
theorem subd15_3_470 : subd15_3 [1, -3, -6] = true := by decide +kernel
theorem subd15_3_471 : subd15_3 [1, -3, -5] = true := by decide +kernel
theorem subd15_3_472 : subd15_3 [1, -3, -4] = true := by decide +kernel
theorem subd15_3_473 : subd15_3 [1, -3, -3] = true := by decide +kernel
theorem subd15_3_474 : subd15_3 [1, -3, -2] = true := by decide +kernel
theorem subd15_3_475 : subd15_3 [1, -3, -1] = true := by decide +kernel
theorem subd15_3_476 : subd15_3 [1, -3, 0] = true := by decide +kernel
theorem subd15_3_477 : subd15_3 [1, -3, 1] = true := by decide +kernel
theorem subd15_3_478 : subd15_3 [1, -3, 2] = true := by decide +kernel
theorem subd15_3_479 : subd15_3 [1, -3, 3] = true := by decide +kernel
theorem sbd15_3_14 : ∀ q ∈ blkd15_3_14, subd15_3 q = true := by
  unfold blkd15_3_14
  exact List.forall_mem_cons.2 ⟨subd15_3_448, List.forall_mem_cons.2 ⟨subd15_3_449, List.forall_mem_cons.2 ⟨subd15_3_450, List.forall_mem_cons.2 ⟨subd15_3_451, List.forall_mem_cons.2 ⟨subd15_3_452, List.forall_mem_cons.2 ⟨subd15_3_453, List.forall_mem_cons.2 ⟨subd15_3_454, List.forall_mem_cons.2 ⟨subd15_3_455, List.forall_mem_cons.2 ⟨subd15_3_456, List.forall_mem_cons.2 ⟨subd15_3_457, List.forall_mem_cons.2 ⟨subd15_3_458, List.forall_mem_cons.2 ⟨subd15_3_459, List.forall_mem_cons.2 ⟨subd15_3_460, List.forall_mem_cons.2 ⟨subd15_3_461, List.forall_mem_cons.2 ⟨subd15_3_462, List.forall_mem_cons.2 ⟨subd15_3_463, List.forall_mem_cons.2 ⟨subd15_3_464, List.forall_mem_cons.2 ⟨subd15_3_465, List.forall_mem_cons.2 ⟨subd15_3_466, List.forall_mem_cons.2 ⟨subd15_3_467, List.forall_mem_cons.2 ⟨subd15_3_468, List.forall_mem_cons.2 ⟨subd15_3_469, List.forall_mem_cons.2 ⟨subd15_3_470, List.forall_mem_cons.2 ⟨subd15_3_471, List.forall_mem_cons.2 ⟨subd15_3_472, List.forall_mem_cons.2 ⟨subd15_3_473, List.forall_mem_cons.2 ⟨subd15_3_474, List.forall_mem_cons.2 ⟨subd15_3_475, List.forall_mem_cons.2 ⟨subd15_3_476, List.forall_mem_cons.2 ⟨subd15_3_477, List.forall_mem_cons.2 ⟨subd15_3_478, List.forall_mem_cons.2 ⟨subd15_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_480 : subd15_3 [1, -3, 4] = true := by decide +kernel
theorem subd15_3_481 : subd15_3 [1, -3, 5] = true := by decide +kernel
theorem subd15_3_482 : subd15_3 [1, -3, 6] = true := by decide +kernel
theorem subd15_3_483 : subd15_3 [1, -3, 7] = true := by decide +kernel
theorem subd15_3_484 : subd15_3 [1, -3, 8] = true := by decide +kernel
theorem subd15_3_485 : subd15_3 [1, -2, -7] = true := by decide +kernel
theorem subd15_3_486 : subd15_3 [1, -2, -6] = true := by decide +kernel
theorem subd15_3_487 : subd15_3 [1, -2, -5] = true := by decide +kernel
theorem subd15_3_488 : subd15_3 [1, -2, -4] = true := by decide +kernel
theorem subd15_3_489 : subd15_3 [1, -2, -3] = true := by decide +kernel
theorem subd15_3_490 : subd15_3 [1, -2, -2] = true := by decide +kernel
theorem subd15_3_491 : subd15_3 [1, -2, -1] = true := by decide +kernel
theorem subd15_3_492 : subd15_3 [1, -2, 0] = true := by decide +kernel
theorem subd15_3_493 : subd15_3 [1, -2, 1] = true := by decide +kernel
theorem subd15_3_494 : subd15_3 [1, -2, 2] = true := by decide +kernel
theorem subd15_3_495 : subd15_3 [1, -2, 3] = true := by decide +kernel
theorem subd15_3_496 : subd15_3 [1, -2, 4] = true := by decide +kernel
theorem subd15_3_497 : subd15_3 [1, -2, 5] = true := by decide +kernel
theorem subd15_3_498 : subd15_3 [1, -2, 6] = true := by decide +kernel
theorem subd15_3_499 : subd15_3 [1, -2, 7] = true := by decide +kernel
theorem subd15_3_500 : subd15_3 [1, -2, 8] = true := by decide +kernel
theorem subd15_3_501 : subd15_3 [1, -1, -8] = true := by decide +kernel
theorem subd15_3_502 : subd15_3 [1, -1, -7] = true := by decide +kernel
theorem subd15_3_503 : subd15_3 [1, -1, -6] = true := by decide +kernel
theorem subd15_3_504 : subd15_3 [1, -1, -5] = true := by decide +kernel
theorem subd15_3_505 : subd15_3 [1, -1, -4] = true := by decide +kernel
theorem subd15_3_506 : subd15_3 [1, -1, -3] = true := by decide +kernel
theorem subd15_3_507 : subd15_3 [1, -1, -2] = true := by decide +kernel
theorem subd15_3_508 : subd15_3 [1, -1, -1] = true := by decide +kernel
theorem subd15_3_509 : subd15_3 [1, -1, 0] = true := by decide +kernel
theorem subd15_3_510 : subd15_3 [1, -1, 1] = true := by decide +kernel
theorem subd15_3_511 : subd15_3 [1, -1, 2] = true := by decide +kernel
theorem sbd15_3_15 : ∀ q ∈ blkd15_3_15, subd15_3 q = true := by
  unfold blkd15_3_15
  exact List.forall_mem_cons.2 ⟨subd15_3_480, List.forall_mem_cons.2 ⟨subd15_3_481, List.forall_mem_cons.2 ⟨subd15_3_482, List.forall_mem_cons.2 ⟨subd15_3_483, List.forall_mem_cons.2 ⟨subd15_3_484, List.forall_mem_cons.2 ⟨subd15_3_485, List.forall_mem_cons.2 ⟨subd15_3_486, List.forall_mem_cons.2 ⟨subd15_3_487, List.forall_mem_cons.2 ⟨subd15_3_488, List.forall_mem_cons.2 ⟨subd15_3_489, List.forall_mem_cons.2 ⟨subd15_3_490, List.forall_mem_cons.2 ⟨subd15_3_491, List.forall_mem_cons.2 ⟨subd15_3_492, List.forall_mem_cons.2 ⟨subd15_3_493, List.forall_mem_cons.2 ⟨subd15_3_494, List.forall_mem_cons.2 ⟨subd15_3_495, List.forall_mem_cons.2 ⟨subd15_3_496, List.forall_mem_cons.2 ⟨subd15_3_497, List.forall_mem_cons.2 ⟨subd15_3_498, List.forall_mem_cons.2 ⟨subd15_3_499, List.forall_mem_cons.2 ⟨subd15_3_500, List.forall_mem_cons.2 ⟨subd15_3_501, List.forall_mem_cons.2 ⟨subd15_3_502, List.forall_mem_cons.2 ⟨subd15_3_503, List.forall_mem_cons.2 ⟨subd15_3_504, List.forall_mem_cons.2 ⟨subd15_3_505, List.forall_mem_cons.2 ⟨subd15_3_506, List.forall_mem_cons.2 ⟨subd15_3_507, List.forall_mem_cons.2 ⟨subd15_3_508, List.forall_mem_cons.2 ⟨subd15_3_509, List.forall_mem_cons.2 ⟨subd15_3_510, List.forall_mem_cons.2 ⟨subd15_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_512 : subd15_3 [1, -1, 3] = true := by decide +kernel
theorem subd15_3_513 : subd15_3 [1, -1, 4] = true := by decide +kernel
theorem subd15_3_514 : subd15_3 [1, -1, 5] = true := by decide +kernel
theorem subd15_3_515 : subd15_3 [1, -1, 6] = true := by decide +kernel
theorem subd15_3_516 : subd15_3 [1, -1, 7] = true := by decide +kernel
theorem subd15_3_517 : subd15_3 [1, -1, 8] = true := by decide +kernel
theorem subd15_3_518 : subd15_3 [1, 0, -8] = true := by decide +kernel
theorem subd15_3_519 : subd15_3 [1, 0, -7] = true := by decide +kernel
theorem subd15_3_520 : subd15_3 [1, 0, -6] = true := by decide +kernel
theorem subd15_3_521 : subd15_3 [1, 0, -5] = true := by decide +kernel
theorem subd15_3_522 : subd15_3 [1, 0, -4] = true := by decide +kernel
theorem subd15_3_523 : subd15_3 [1, 0, -3] = true := by decide +kernel
theorem subd15_3_524 : subd15_3 [1, 0, -2] = true := by decide +kernel
theorem subd15_3_525 : subd15_3 [1, 0, -1] = true := by decide +kernel
theorem subd15_3_526 : subd15_3 [1, 0, 0] = true := by decide +kernel
theorem subd15_3_527 : subd15_3 [1, 0, 1] = true := by decide +kernel
theorem subd15_3_528 : subd15_3 [1, 0, 2] = true := by decide +kernel
theorem subd15_3_529 : subd15_3 [1, 0, 3] = true := by decide +kernel
theorem subd15_3_530 : subd15_3 [1, 0, 4] = true := by decide +kernel
theorem subd15_3_531 : subd15_3 [1, 0, 5] = true := by decide +kernel
theorem subd15_3_532 : subd15_3 [1, 0, 6] = true := by decide +kernel
theorem subd15_3_533 : subd15_3 [1, 0, 7] = true := by decide +kernel
theorem subd15_3_534 : subd15_3 [1, 0, 8] = true := by decide +kernel
theorem subd15_3_535 : subd15_3 [1, 1, -9] = true := by decide +kernel
theorem subd15_3_536 : subd15_3 [1, 1, -8] = true := by decide +kernel
theorem subd15_3_537 : subd15_3 [1, 1, -7] = true := by decide +kernel
theorem subd15_3_538 : subd15_3 [1, 1, -6] = true := by decide +kernel
theorem subd15_3_539 : subd15_3 [1, 1, -5] = true := by decide +kernel
theorem subd15_3_540 : subd15_3 [1, 1, -4] = true := by decide +kernel
theorem subd15_3_541 : subd15_3 [1, 1, -3] = true := by decide +kernel
theorem subd15_3_542 : subd15_3 [1, 1, -2] = true := by decide +kernel
theorem subd15_3_543 : subd15_3 [1, 1, -1] = true := by decide +kernel
theorem sbd15_3_16 : ∀ q ∈ blkd15_3_16, subd15_3 q = true := by
  unfold blkd15_3_16
  exact List.forall_mem_cons.2 ⟨subd15_3_512, List.forall_mem_cons.2 ⟨subd15_3_513, List.forall_mem_cons.2 ⟨subd15_3_514, List.forall_mem_cons.2 ⟨subd15_3_515, List.forall_mem_cons.2 ⟨subd15_3_516, List.forall_mem_cons.2 ⟨subd15_3_517, List.forall_mem_cons.2 ⟨subd15_3_518, List.forall_mem_cons.2 ⟨subd15_3_519, List.forall_mem_cons.2 ⟨subd15_3_520, List.forall_mem_cons.2 ⟨subd15_3_521, List.forall_mem_cons.2 ⟨subd15_3_522, List.forall_mem_cons.2 ⟨subd15_3_523, List.forall_mem_cons.2 ⟨subd15_3_524, List.forall_mem_cons.2 ⟨subd15_3_525, List.forall_mem_cons.2 ⟨subd15_3_526, List.forall_mem_cons.2 ⟨subd15_3_527, List.forall_mem_cons.2 ⟨subd15_3_528, List.forall_mem_cons.2 ⟨subd15_3_529, List.forall_mem_cons.2 ⟨subd15_3_530, List.forall_mem_cons.2 ⟨subd15_3_531, List.forall_mem_cons.2 ⟨subd15_3_532, List.forall_mem_cons.2 ⟨subd15_3_533, List.forall_mem_cons.2 ⟨subd15_3_534, List.forall_mem_cons.2 ⟨subd15_3_535, List.forall_mem_cons.2 ⟨subd15_3_536, List.forall_mem_cons.2 ⟨subd15_3_537, List.forall_mem_cons.2 ⟨subd15_3_538, List.forall_mem_cons.2 ⟨subd15_3_539, List.forall_mem_cons.2 ⟨subd15_3_540, List.forall_mem_cons.2 ⟨subd15_3_541, List.forall_mem_cons.2 ⟨subd15_3_542, List.forall_mem_cons.2 ⟨subd15_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_544 : subd15_3 [1, 1, 0] = true := by decide +kernel
theorem subd15_3_545 : subd15_3 [1, 1, 1] = true := by decide +kernel
theorem subd15_3_546 : subd15_3 [1, 1, 2] = true := by decide +kernel
theorem subd15_3_547 : subd15_3 [1, 1, 3] = true := by decide +kernel
theorem subd15_3_548 : subd15_3 [1, 1, 4] = true := by decide +kernel
theorem subd15_3_549 : subd15_3 [1, 1, 5] = true := by decide +kernel
theorem subd15_3_550 : subd15_3 [1, 1, 6] = true := by decide +kernel
theorem subd15_3_551 : subd15_3 [1, 1, 7] = true := by decide +kernel
theorem subd15_3_552 : subd15_3 [1, 1, 8] = true := by decide +kernel
theorem subd15_3_553 : subd15_3 [1, 2, -9] = true := by decide +kernel
theorem subd15_3_554 : subd15_3 [1, 2, -8] = true := by decide +kernel
theorem subd15_3_555 : subd15_3 [1, 2, -7] = true := by decide +kernel
theorem subd15_3_556 : subd15_3 [1, 2, -6] = true := by decide +kernel
theorem subd15_3_557 : subd15_3 [1, 2, -5] = true := by decide +kernel
theorem subd15_3_558 : subd15_3 [1, 2, -4] = true := by decide +kernel
theorem subd15_3_559 : subd15_3 [1, 2, -3] = true := by decide +kernel
theorem subd15_3_560 : subd15_3 [1, 2, -2] = true := by decide +kernel
theorem subd15_3_561 : subd15_3 [1, 2, -1] = true := by decide +kernel
theorem subd15_3_562 : subd15_3 [1, 2, 0] = true := by decide +kernel
theorem subd15_3_563 : subd15_3 [1, 2, 1] = true := by decide +kernel
theorem subd15_3_564 : subd15_3 [1, 2, 2] = true := by decide +kernel
theorem subd15_3_565 : subd15_3 [1, 2, 3] = true := by decide +kernel
theorem subd15_3_566 : subd15_3 [1, 2, 4] = true := by decide +kernel
theorem subd15_3_567 : subd15_3 [1, 2, 5] = true := by decide +kernel
theorem subd15_3_568 : subd15_3 [1, 2, 6] = true := by decide +kernel
theorem subd15_3_569 : subd15_3 [1, 2, 7] = true := by decide +kernel
theorem subd15_3_570 : subd15_3 [1, 3, -8] = true := by decide +kernel
theorem subd15_3_571 : subd15_3 [1, 3, -7] = true := by decide +kernel
theorem subd15_3_572 : subd15_3 [1, 3, -6] = true := by decide +kernel
theorem subd15_3_573 : subd15_3 [1, 3, -5] = true := by decide +kernel
theorem subd15_3_574 : subd15_3 [1, 3, -4] = true := by decide +kernel
theorem subd15_3_575 : subd15_3 [1, 3, -3] = true := by decide +kernel
theorem sbd15_3_17 : ∀ q ∈ blkd15_3_17, subd15_3 q = true := by
  unfold blkd15_3_17
  exact List.forall_mem_cons.2 ⟨subd15_3_544, List.forall_mem_cons.2 ⟨subd15_3_545, List.forall_mem_cons.2 ⟨subd15_3_546, List.forall_mem_cons.2 ⟨subd15_3_547, List.forall_mem_cons.2 ⟨subd15_3_548, List.forall_mem_cons.2 ⟨subd15_3_549, List.forall_mem_cons.2 ⟨subd15_3_550, List.forall_mem_cons.2 ⟨subd15_3_551, List.forall_mem_cons.2 ⟨subd15_3_552, List.forall_mem_cons.2 ⟨subd15_3_553, List.forall_mem_cons.2 ⟨subd15_3_554, List.forall_mem_cons.2 ⟨subd15_3_555, List.forall_mem_cons.2 ⟨subd15_3_556, List.forall_mem_cons.2 ⟨subd15_3_557, List.forall_mem_cons.2 ⟨subd15_3_558, List.forall_mem_cons.2 ⟨subd15_3_559, List.forall_mem_cons.2 ⟨subd15_3_560, List.forall_mem_cons.2 ⟨subd15_3_561, List.forall_mem_cons.2 ⟨subd15_3_562, List.forall_mem_cons.2 ⟨subd15_3_563, List.forall_mem_cons.2 ⟨subd15_3_564, List.forall_mem_cons.2 ⟨subd15_3_565, List.forall_mem_cons.2 ⟨subd15_3_566, List.forall_mem_cons.2 ⟨subd15_3_567, List.forall_mem_cons.2 ⟨subd15_3_568, List.forall_mem_cons.2 ⟨subd15_3_569, List.forall_mem_cons.2 ⟨subd15_3_570, List.forall_mem_cons.2 ⟨subd15_3_571, List.forall_mem_cons.2 ⟨subd15_3_572, List.forall_mem_cons.2 ⟨subd15_3_573, List.forall_mem_cons.2 ⟨subd15_3_574, List.forall_mem_cons.2 ⟨subd15_3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_576 : subd15_3 [1, 3, -2] = true := by decide +kernel
theorem subd15_3_577 : subd15_3 [1, 3, -1] = true := by decide +kernel
theorem subd15_3_578 : subd15_3 [1, 3, 0] = true := by decide +kernel
theorem subd15_3_579 : subd15_3 [1, 3, 1] = true := by decide +kernel
theorem subd15_3_580 : subd15_3 [1, 3, 2] = true := by decide +kernel
theorem subd15_3_581 : subd15_3 [1, 3, 3] = true := by decide +kernel
theorem subd15_3_582 : subd15_3 [1, 3, 4] = true := by decide +kernel
theorem subd15_3_583 : subd15_3 [1, 3, 5] = true := by decide +kernel
theorem subd15_3_584 : subd15_3 [1, 3, 6] = true := by decide +kernel
theorem subd15_3_585 : subd15_3 [1, 4, -8] = true := by decide +kernel
theorem subd15_3_586 : subd15_3 [1, 4, -7] = true := by decide +kernel
theorem subd15_3_587 : subd15_3 [1, 4, -6] = true := by decide +kernel
theorem subd15_3_588 : subd15_3 [1, 4, -5] = true := by decide +kernel
theorem subd15_3_589 : subd15_3 [1, 4, -4] = true := by decide +kernel
theorem subd15_3_590 : subd15_3 [1, 4, -3] = true := by decide +kernel
theorem subd15_3_591 : subd15_3 [1, 4, -2] = true := by decide +kernel
theorem subd15_3_592 : subd15_3 [1, 4, -1] = true := by decide +kernel
theorem subd15_3_593 : subd15_3 [1, 4, 0] = true := by decide +kernel
theorem subd15_3_594 : subd15_3 [1, 4, 1] = true := by decide +kernel
theorem subd15_3_595 : subd15_3 [1, 4, 2] = true := by decide +kernel
theorem subd15_3_596 : subd15_3 [1, 4, 3] = true := by decide +kernel
theorem subd15_3_597 : subd15_3 [1, 4, 4] = true := by decide +kernel
theorem subd15_3_598 : subd15_3 [1, 4, 5] = true := by decide +kernel
theorem subd15_3_599 : subd15_3 [1, 5] = true := by decide +kernel
theorem subd15_3_600 : subd15_3 [2, -5] = true := by decide +kernel
theorem subd15_3_601 : subd15_3 [2, -4] = true := by decide +kernel
theorem subd15_3_602 : subd15_3 [2, -3] = true := by decide +kernel
theorem subd15_3_603 : subd15_3 [2, -2, -6] = true := by decide +kernel
theorem subd15_3_604 : subd15_3 [2, -2, -5] = true := by decide +kernel
theorem subd15_3_605 : subd15_3 [2, -2, -4] = true := by decide +kernel
theorem subd15_3_606 : subd15_3 [2, -2, -3] = true := by decide +kernel
theorem subd15_3_607 : subd15_3 [2, -2, -2] = true := by decide +kernel
theorem sbd15_3_18 : ∀ q ∈ blkd15_3_18, subd15_3 q = true := by
  unfold blkd15_3_18
  exact List.forall_mem_cons.2 ⟨subd15_3_576, List.forall_mem_cons.2 ⟨subd15_3_577, List.forall_mem_cons.2 ⟨subd15_3_578, List.forall_mem_cons.2 ⟨subd15_3_579, List.forall_mem_cons.2 ⟨subd15_3_580, List.forall_mem_cons.2 ⟨subd15_3_581, List.forall_mem_cons.2 ⟨subd15_3_582, List.forall_mem_cons.2 ⟨subd15_3_583, List.forall_mem_cons.2 ⟨subd15_3_584, List.forall_mem_cons.2 ⟨subd15_3_585, List.forall_mem_cons.2 ⟨subd15_3_586, List.forall_mem_cons.2 ⟨subd15_3_587, List.forall_mem_cons.2 ⟨subd15_3_588, List.forall_mem_cons.2 ⟨subd15_3_589, List.forall_mem_cons.2 ⟨subd15_3_590, List.forall_mem_cons.2 ⟨subd15_3_591, List.forall_mem_cons.2 ⟨subd15_3_592, List.forall_mem_cons.2 ⟨subd15_3_593, List.forall_mem_cons.2 ⟨subd15_3_594, List.forall_mem_cons.2 ⟨subd15_3_595, List.forall_mem_cons.2 ⟨subd15_3_596, List.forall_mem_cons.2 ⟨subd15_3_597, List.forall_mem_cons.2 ⟨subd15_3_598, List.forall_mem_cons.2 ⟨subd15_3_599, List.forall_mem_cons.2 ⟨subd15_3_600, List.forall_mem_cons.2 ⟨subd15_3_601, List.forall_mem_cons.2 ⟨subd15_3_602, List.forall_mem_cons.2 ⟨subd15_3_603, List.forall_mem_cons.2 ⟨subd15_3_604, List.forall_mem_cons.2 ⟨subd15_3_605, List.forall_mem_cons.2 ⟨subd15_3_606, List.forall_mem_cons.2 ⟨subd15_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_608 : subd15_3 [2, -2, -1] = true := by decide +kernel
theorem subd15_3_609 : subd15_3 [2, -2, 0] = true := by decide +kernel
theorem subd15_3_610 : subd15_3 [2, -2, 1] = true := by decide +kernel
theorem subd15_3_611 : subd15_3 [2, -2, 2] = true := by decide +kernel
theorem subd15_3_612 : subd15_3 [2, -2, 3] = true := by decide +kernel
theorem subd15_3_613 : subd15_3 [2, -2, 4] = true := by decide +kernel
theorem subd15_3_614 : subd15_3 [2, -2, 5] = true := by decide +kernel
theorem subd15_3_615 : subd15_3 [2, -2, 6] = true := by decide +kernel
theorem subd15_3_616 : subd15_3 [2, -2, 7] = true := by decide +kernel
theorem subd15_3_617 : subd15_3 [2, -2, 8] = true := by decide +kernel
theorem subd15_3_618 : subd15_3 [2, -1, -7] = true := by decide +kernel
theorem subd15_3_619 : subd15_3 [2, -1, -6] = true := by decide +kernel
theorem subd15_3_620 : subd15_3 [2, -1, -5] = true := by decide +kernel
theorem subd15_3_621 : subd15_3 [2, -1, -4] = true := by decide +kernel
theorem subd15_3_622 : subd15_3 [2, -1, -3] = true := by decide +kernel
theorem subd15_3_623 : subd15_3 [2, -1, -2] = true := by decide +kernel
theorem subd15_3_624 : subd15_3 [2, -1, -1] = true := by decide +kernel
theorem subd15_3_625 : subd15_3 [2, -1, 0] = true := by decide +kernel
theorem subd15_3_626 : subd15_3 [2, -1, 1] = true := by decide +kernel
theorem subd15_3_627 : subd15_3 [2, -1, 2] = true := by decide +kernel
theorem subd15_3_628 : subd15_3 [2, -1, 3] = true := by decide +kernel
theorem subd15_3_629 : subd15_3 [2, -1, 4] = true := by decide +kernel
theorem subd15_3_630 : subd15_3 [2, -1, 5] = true := by decide +kernel
theorem subd15_3_631 : subd15_3 [2, -1, 6] = true := by decide +kernel
theorem subd15_3_632 : subd15_3 [2, -1, 7] = true := by decide +kernel
theorem subd15_3_633 : subd15_3 [2, -1, 8] = true := by decide +kernel
theorem subd15_3_634 : subd15_3 [2, 0, -7] = true := by decide +kernel
theorem subd15_3_635 : subd15_3 [2, 0, -6] = true := by decide +kernel
theorem subd15_3_636 : subd15_3 [2, 0, -5] = true := by decide +kernel
theorem subd15_3_637 : subd15_3 [2, 0, -4] = true := by decide +kernel
theorem subd15_3_638 : subd15_3 [2, 0, -3] = true := by decide +kernel
theorem subd15_3_639 : subd15_3 [2, 0, -2] = true := by decide +kernel
theorem sbd15_3_19 : ∀ q ∈ blkd15_3_19, subd15_3 q = true := by
  unfold blkd15_3_19
  exact List.forall_mem_cons.2 ⟨subd15_3_608, List.forall_mem_cons.2 ⟨subd15_3_609, List.forall_mem_cons.2 ⟨subd15_3_610, List.forall_mem_cons.2 ⟨subd15_3_611, List.forall_mem_cons.2 ⟨subd15_3_612, List.forall_mem_cons.2 ⟨subd15_3_613, List.forall_mem_cons.2 ⟨subd15_3_614, List.forall_mem_cons.2 ⟨subd15_3_615, List.forall_mem_cons.2 ⟨subd15_3_616, List.forall_mem_cons.2 ⟨subd15_3_617, List.forall_mem_cons.2 ⟨subd15_3_618, List.forall_mem_cons.2 ⟨subd15_3_619, List.forall_mem_cons.2 ⟨subd15_3_620, List.forall_mem_cons.2 ⟨subd15_3_621, List.forall_mem_cons.2 ⟨subd15_3_622, List.forall_mem_cons.2 ⟨subd15_3_623, List.forall_mem_cons.2 ⟨subd15_3_624, List.forall_mem_cons.2 ⟨subd15_3_625, List.forall_mem_cons.2 ⟨subd15_3_626, List.forall_mem_cons.2 ⟨subd15_3_627, List.forall_mem_cons.2 ⟨subd15_3_628, List.forall_mem_cons.2 ⟨subd15_3_629, List.forall_mem_cons.2 ⟨subd15_3_630, List.forall_mem_cons.2 ⟨subd15_3_631, List.forall_mem_cons.2 ⟨subd15_3_632, List.forall_mem_cons.2 ⟨subd15_3_633, List.forall_mem_cons.2 ⟨subd15_3_634, List.forall_mem_cons.2 ⟨subd15_3_635, List.forall_mem_cons.2 ⟨subd15_3_636, List.forall_mem_cons.2 ⟨subd15_3_637, List.forall_mem_cons.2 ⟨subd15_3_638, List.forall_mem_cons.2 ⟨subd15_3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_640 : subd15_3 [2, 0, -1] = true := by decide +kernel
theorem subd15_3_641 : subd15_3 [2, 0, 0] = true := by decide +kernel
theorem subd15_3_642 : subd15_3 [2, 0, 1] = true := by decide +kernel
theorem subd15_3_643 : subd15_3 [2, 0, 2] = true := by decide +kernel
theorem subd15_3_644 : subd15_3 [2, 0, 3] = true := by decide +kernel
theorem subd15_3_645 : subd15_3 [2, 0, 4] = true := by decide +kernel
theorem subd15_3_646 : subd15_3 [2, 0, 5] = true := by decide +kernel
theorem subd15_3_647 : subd15_3 [2, 0, 6] = true := by decide +kernel
theorem subd15_3_648 : subd15_3 [2, 0, 7] = true := by decide +kernel
theorem subd15_3_649 : subd15_3 [2, 0, 8] = true := by decide +kernel
theorem subd15_3_650 : subd15_3 [2, 1, -8] = true := by decide +kernel
theorem subd15_3_651 : subd15_3 [2, 1, -7] = true := by decide +kernel
theorem subd15_3_652 : subd15_3 [2, 1, -6] = true := by decide +kernel
theorem subd15_3_653 : subd15_3 [2, 1, -5] = true := by decide +kernel
theorem subd15_3_654 : subd15_3 [2, 1, -4] = true := by decide +kernel
theorem subd15_3_655 : subd15_3 [2, 1, -3] = true := by decide +kernel
theorem subd15_3_656 : subd15_3 [2, 1, -2] = true := by decide +kernel
theorem subd15_3_657 : subd15_3 [2, 1, -1] = true := by decide +kernel
theorem subd15_3_658 : subd15_3 [2, 1, 0] = true := by decide +kernel
theorem subd15_3_659 : subd15_3 [2, 1, 1] = true := by decide +kernel
theorem subd15_3_660 : subd15_3 [2, 1, 2] = true := by decide +kernel
theorem subd15_3_661 : subd15_3 [2, 1, 3] = true := by decide +kernel
theorem subd15_3_662 : subd15_3 [2, 1, 4] = true := by decide +kernel
theorem subd15_3_663 : subd15_3 [2, 1, 5] = true := by decide +kernel
theorem subd15_3_664 : subd15_3 [2, 1, 6] = true := by decide +kernel
theorem subd15_3_665 : subd15_3 [2, 1, 7] = true := by decide +kernel
theorem subd15_3_666 : subd15_3 [2, 1, 8] = true := by decide +kernel
theorem subd15_3_667 : subd15_3 [2, 2, -8] = true := by decide +kernel
theorem subd15_3_668 : subd15_3 [2, 2, -7] = true := by decide +kernel
theorem subd15_3_669 : subd15_3 [2, 2, -6] = true := by decide +kernel
theorem subd15_3_670 : subd15_3 [2, 2, -5] = true := by decide +kernel
theorem subd15_3_671 : subd15_3 [2, 2, -4] = true := by decide +kernel
theorem sbd15_3_20 : ∀ q ∈ blkd15_3_20, subd15_3 q = true := by
  unfold blkd15_3_20
  exact List.forall_mem_cons.2 ⟨subd15_3_640, List.forall_mem_cons.2 ⟨subd15_3_641, List.forall_mem_cons.2 ⟨subd15_3_642, List.forall_mem_cons.2 ⟨subd15_3_643, List.forall_mem_cons.2 ⟨subd15_3_644, List.forall_mem_cons.2 ⟨subd15_3_645, List.forall_mem_cons.2 ⟨subd15_3_646, List.forall_mem_cons.2 ⟨subd15_3_647, List.forall_mem_cons.2 ⟨subd15_3_648, List.forall_mem_cons.2 ⟨subd15_3_649, List.forall_mem_cons.2 ⟨subd15_3_650, List.forall_mem_cons.2 ⟨subd15_3_651, List.forall_mem_cons.2 ⟨subd15_3_652, List.forall_mem_cons.2 ⟨subd15_3_653, List.forall_mem_cons.2 ⟨subd15_3_654, List.forall_mem_cons.2 ⟨subd15_3_655, List.forall_mem_cons.2 ⟨subd15_3_656, List.forall_mem_cons.2 ⟨subd15_3_657, List.forall_mem_cons.2 ⟨subd15_3_658, List.forall_mem_cons.2 ⟨subd15_3_659, List.forall_mem_cons.2 ⟨subd15_3_660, List.forall_mem_cons.2 ⟨subd15_3_661, List.forall_mem_cons.2 ⟨subd15_3_662, List.forall_mem_cons.2 ⟨subd15_3_663, List.forall_mem_cons.2 ⟨subd15_3_664, List.forall_mem_cons.2 ⟨subd15_3_665, List.forall_mem_cons.2 ⟨subd15_3_666, List.forall_mem_cons.2 ⟨subd15_3_667, List.forall_mem_cons.2 ⟨subd15_3_668, List.forall_mem_cons.2 ⟨subd15_3_669, List.forall_mem_cons.2 ⟨subd15_3_670, List.forall_mem_cons.2 ⟨subd15_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_672 : subd15_3 [2, 2, -3] = true := by decide +kernel
theorem subd15_3_673 : subd15_3 [2, 2, -2] = true := by decide +kernel
theorem subd15_3_674 : subd15_3 [2, 2, -1] = true := by decide +kernel
theorem subd15_3_675 : subd15_3 [2, 2, 0] = true := by decide +kernel
theorem subd15_3_676 : subd15_3 [2, 2, 1] = true := by decide +kernel
theorem subd15_3_677 : subd15_3 [2, 2, 2] = true := by decide +kernel
theorem subd15_3_678 : subd15_3 [2, 2, 3] = true := by decide +kernel
theorem subd15_3_679 : subd15_3 [2, 2, 4] = true := by decide +kernel
theorem subd15_3_680 : subd15_3 [2, 2, 5] = true := by decide +kernel
theorem subd15_3_681 : subd15_3 [2, 2, 6] = true := by decide +kernel
theorem subd15_3_682 : subd15_3 [2, 2, 7] = true := by decide +kernel
theorem subd15_3_683 : subd15_3 [2, 3, -7] = true := by decide +kernel
theorem subd15_3_684 : subd15_3 [2, 3, -6] = true := by decide +kernel
theorem subd15_3_685 : subd15_3 [2, 3, -5] = true := by decide +kernel
theorem subd15_3_686 : subd15_3 [2, 3, -4] = true := by decide +kernel
theorem subd15_3_687 : subd15_3 [2, 3, -3] = true := by decide +kernel
theorem subd15_3_688 : subd15_3 [2, 3, -2] = true := by decide +kernel
theorem subd15_3_689 : subd15_3 [2, 3, -1] = true := by decide +kernel
theorem subd15_3_690 : subd15_3 [2, 3, 0] = true := by decide +kernel
theorem subd15_3_691 : subd15_3 [2, 3, 1] = true := by decide +kernel
theorem subd15_3_692 : subd15_3 [2, 3, 2] = true := by decide +kernel
theorem subd15_3_693 : subd15_3 [2, 3, 3] = true := by decide +kernel
theorem subd15_3_694 : subd15_3 [2, 3, 4] = true := by decide +kernel
theorem subd15_3_695 : subd15_3 [2, 3, 5] = true := by decide +kernel
theorem subd15_3_696 : subd15_3 [2, 3, 6] = true := by decide +kernel
theorem subd15_3_697 : subd15_3 [2, 4] = true := by decide +kernel
theorem subd15_3_698 : subd15_3 [2, 5] = true := by decide +kernel
theorem subd15_3_699 : subd15_3 [3, -5] = true := by decide +kernel
theorem subd15_3_700 : subd15_3 [3, -4] = true := by decide +kernel
theorem subd15_3_701 : subd15_3 [3, -3] = true := by decide +kernel
theorem subd15_3_702 : subd15_3 [3, -2] = true := by decide +kernel
theorem subd15_3_703 : subd15_3 [3, -1, -5] = true := by decide +kernel
theorem sbd15_3_21 : ∀ q ∈ blkd15_3_21, subd15_3 q = true := by
  unfold blkd15_3_21
  exact List.forall_mem_cons.2 ⟨subd15_3_672, List.forall_mem_cons.2 ⟨subd15_3_673, List.forall_mem_cons.2 ⟨subd15_3_674, List.forall_mem_cons.2 ⟨subd15_3_675, List.forall_mem_cons.2 ⟨subd15_3_676, List.forall_mem_cons.2 ⟨subd15_3_677, List.forall_mem_cons.2 ⟨subd15_3_678, List.forall_mem_cons.2 ⟨subd15_3_679, List.forall_mem_cons.2 ⟨subd15_3_680, List.forall_mem_cons.2 ⟨subd15_3_681, List.forall_mem_cons.2 ⟨subd15_3_682, List.forall_mem_cons.2 ⟨subd15_3_683, List.forall_mem_cons.2 ⟨subd15_3_684, List.forall_mem_cons.2 ⟨subd15_3_685, List.forall_mem_cons.2 ⟨subd15_3_686, List.forall_mem_cons.2 ⟨subd15_3_687, List.forall_mem_cons.2 ⟨subd15_3_688, List.forall_mem_cons.2 ⟨subd15_3_689, List.forall_mem_cons.2 ⟨subd15_3_690, List.forall_mem_cons.2 ⟨subd15_3_691, List.forall_mem_cons.2 ⟨subd15_3_692, List.forall_mem_cons.2 ⟨subd15_3_693, List.forall_mem_cons.2 ⟨subd15_3_694, List.forall_mem_cons.2 ⟨subd15_3_695, List.forall_mem_cons.2 ⟨subd15_3_696, List.forall_mem_cons.2 ⟨subd15_3_697, List.forall_mem_cons.2 ⟨subd15_3_698, List.forall_mem_cons.2 ⟨subd15_3_699, List.forall_mem_cons.2 ⟨subd15_3_700, List.forall_mem_cons.2 ⟨subd15_3_701, List.forall_mem_cons.2 ⟨subd15_3_702, List.forall_mem_cons.2 ⟨subd15_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_704 : subd15_3 [3, -1, -4] = true := by decide +kernel
theorem subd15_3_705 : subd15_3 [3, -1, -3] = true := by decide +kernel
theorem subd15_3_706 : subd15_3 [3, -1, -2] = true := by decide +kernel
theorem subd15_3_707 : subd15_3 [3, -1, -1] = true := by decide +kernel
theorem subd15_3_708 : subd15_3 [3, -1, 0] = true := by decide +kernel
theorem subd15_3_709 : subd15_3 [3, -1, 1] = true := by decide +kernel
theorem subd15_3_710 : subd15_3 [3, -1, 2] = true := by decide +kernel
theorem subd15_3_711 : subd15_3 [3, -1, 3] = true := by decide +kernel
theorem subd15_3_712 : subd15_3 [3, -1, 4] = true := by decide +kernel
theorem subd15_3_713 : subd15_3 [3, -1, 5] = true := by decide +kernel
theorem subd15_3_714 : subd15_3 [3, -1, 6] = true := by decide +kernel
theorem subd15_3_715 : subd15_3 [3, -1, 7] = true := by decide +kernel
theorem subd15_3_716 : subd15_3 [3, -1, 8] = true := by decide +kernel
theorem subd15_3_717 : subd15_3 [3, 0, -6] = true := by decide +kernel
theorem subd15_3_718 : subd15_3 [3, 0, -5] = true := by decide +kernel
theorem subd15_3_719 : subd15_3 [3, 0, -4] = true := by decide +kernel
theorem subd15_3_720 : subd15_3 [3, 0, -3] = true := by decide +kernel
theorem subd15_3_721 : subd15_3 [3, 0, -2] = true := by decide +kernel
theorem subd15_3_722 : subd15_3 [3, 0, -1] = true := by decide +kernel
theorem subd15_3_723 : subd15_3 [3, 0, 0] = true := by decide +kernel
theorem subd15_3_724 : subd15_3 [3, 0, 1] = true := by decide +kernel
theorem subd15_3_725 : subd15_3 [3, 0, 2] = true := by decide +kernel
theorem subd15_3_726 : subd15_3 [3, 0, 3] = true := by decide +kernel
theorem subd15_3_727 : subd15_3 [3, 0, 4] = true := by decide +kernel
theorem subd15_3_728 : subd15_3 [3, 0, 5] = true := by decide +kernel
theorem subd15_3_729 : subd15_3 [3, 0, 6] = true := by decide +kernel
theorem subd15_3_730 : subd15_3 [3, 0, 7] = true := by decide +kernel
theorem subd15_3_731 : subd15_3 [3, 0, 8] = true := by decide +kernel
theorem subd15_3_732 : subd15_3 [3, 1, -6] = true := by decide +kernel
theorem subd15_3_733 : subd15_3 [3, 1, -5] = true := by decide +kernel
theorem subd15_3_734 : subd15_3 [3, 1, -4] = true := by decide +kernel
theorem subd15_3_735 : subd15_3 [3, 1, -3] = true := by decide +kernel
theorem sbd15_3_22 : ∀ q ∈ blkd15_3_22, subd15_3 q = true := by
  unfold blkd15_3_22
  exact List.forall_mem_cons.2 ⟨subd15_3_704, List.forall_mem_cons.2 ⟨subd15_3_705, List.forall_mem_cons.2 ⟨subd15_3_706, List.forall_mem_cons.2 ⟨subd15_3_707, List.forall_mem_cons.2 ⟨subd15_3_708, List.forall_mem_cons.2 ⟨subd15_3_709, List.forall_mem_cons.2 ⟨subd15_3_710, List.forall_mem_cons.2 ⟨subd15_3_711, List.forall_mem_cons.2 ⟨subd15_3_712, List.forall_mem_cons.2 ⟨subd15_3_713, List.forall_mem_cons.2 ⟨subd15_3_714, List.forall_mem_cons.2 ⟨subd15_3_715, List.forall_mem_cons.2 ⟨subd15_3_716, List.forall_mem_cons.2 ⟨subd15_3_717, List.forall_mem_cons.2 ⟨subd15_3_718, List.forall_mem_cons.2 ⟨subd15_3_719, List.forall_mem_cons.2 ⟨subd15_3_720, List.forall_mem_cons.2 ⟨subd15_3_721, List.forall_mem_cons.2 ⟨subd15_3_722, List.forall_mem_cons.2 ⟨subd15_3_723, List.forall_mem_cons.2 ⟨subd15_3_724, List.forall_mem_cons.2 ⟨subd15_3_725, List.forall_mem_cons.2 ⟨subd15_3_726, List.forall_mem_cons.2 ⟨subd15_3_727, List.forall_mem_cons.2 ⟨subd15_3_728, List.forall_mem_cons.2 ⟨subd15_3_729, List.forall_mem_cons.2 ⟨subd15_3_730, List.forall_mem_cons.2 ⟨subd15_3_731, List.forall_mem_cons.2 ⟨subd15_3_732, List.forall_mem_cons.2 ⟨subd15_3_733, List.forall_mem_cons.2 ⟨subd15_3_734, List.forall_mem_cons.2 ⟨subd15_3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_736 : subd15_3 [3, 1, -2] = true := by decide +kernel
theorem subd15_3_737 : subd15_3 [3, 1, -1] = true := by decide +kernel
theorem subd15_3_738 : subd15_3 [3, 1, 0] = true := by decide +kernel
theorem subd15_3_739 : subd15_3 [3, 1, 1] = true := by decide +kernel
theorem subd15_3_740 : subd15_3 [3, 1, 2] = true := by decide +kernel
theorem subd15_3_741 : subd15_3 [3, 1, 3] = true := by decide +kernel
theorem subd15_3_742 : subd15_3 [3, 1, 4] = true := by decide +kernel
theorem subd15_3_743 : subd15_3 [3, 1, 5] = true := by decide +kernel
theorem subd15_3_744 : subd15_3 [3, 1, 6] = true := by decide +kernel
theorem subd15_3_745 : subd15_3 [3, 1, 7] = true := by decide +kernel
theorem subd15_3_746 : subd15_3 [3, 1, 8] = true := by decide +kernel
theorem subd15_3_747 : subd15_3 [3, 2, -6] = true := by decide +kernel
theorem subd15_3_748 : subd15_3 [3, 2, -5] = true := by decide +kernel
theorem subd15_3_749 : subd15_3 [3, 2, -4] = true := by decide +kernel
theorem subd15_3_750 : subd15_3 [3, 2, -3] = true := by decide +kernel
theorem subd15_3_751 : subd15_3 [3, 2, -2] = true := by decide +kernel
theorem subd15_3_752 : subd15_3 [3, 2, -1] = true := by decide +kernel
theorem subd15_3_753 : subd15_3 [3, 2, 0] = true := by decide +kernel
theorem subd15_3_754 : subd15_3 [3, 2, 1] = true := by decide +kernel
theorem subd15_3_755 : subd15_3 [3, 2, 2] = true := by decide +kernel
theorem subd15_3_756 : subd15_3 [3, 2, 3] = true := by decide +kernel
theorem subd15_3_757 : subd15_3 [3, 2, 4] = true := by decide +kernel
theorem subd15_3_758 : subd15_3 [3, 2, 5] = true := by decide +kernel
theorem subd15_3_759 : subd15_3 [3, 2, 6] = true := by decide +kernel
theorem subd15_3_760 : subd15_3 [3, 2, 7] = true := by decide +kernel
theorem subd15_3_761 : subd15_3 [3, 3, -6] = true := by decide +kernel
theorem subd15_3_762 : subd15_3 [3, 3, -5] = true := by decide +kernel
theorem subd15_3_763 : subd15_3 [3, 3, -4] = true := by decide +kernel
theorem subd15_3_764 : subd15_3 [3, 3, -3] = true := by decide +kernel
theorem subd15_3_765 : subd15_3 [3, 3, -2] = true := by decide +kernel
theorem subd15_3_766 : subd15_3 [3, 3, -1] = true := by decide +kernel
theorem subd15_3_767 : subd15_3 [3, 3, 0] = true := by decide +kernel
theorem sbd15_3_23 : ∀ q ∈ blkd15_3_23, subd15_3 q = true := by
  unfold blkd15_3_23
  exact List.forall_mem_cons.2 ⟨subd15_3_736, List.forall_mem_cons.2 ⟨subd15_3_737, List.forall_mem_cons.2 ⟨subd15_3_738, List.forall_mem_cons.2 ⟨subd15_3_739, List.forall_mem_cons.2 ⟨subd15_3_740, List.forall_mem_cons.2 ⟨subd15_3_741, List.forall_mem_cons.2 ⟨subd15_3_742, List.forall_mem_cons.2 ⟨subd15_3_743, List.forall_mem_cons.2 ⟨subd15_3_744, List.forall_mem_cons.2 ⟨subd15_3_745, List.forall_mem_cons.2 ⟨subd15_3_746, List.forall_mem_cons.2 ⟨subd15_3_747, List.forall_mem_cons.2 ⟨subd15_3_748, List.forall_mem_cons.2 ⟨subd15_3_749, List.forall_mem_cons.2 ⟨subd15_3_750, List.forall_mem_cons.2 ⟨subd15_3_751, List.forall_mem_cons.2 ⟨subd15_3_752, List.forall_mem_cons.2 ⟨subd15_3_753, List.forall_mem_cons.2 ⟨subd15_3_754, List.forall_mem_cons.2 ⟨subd15_3_755, List.forall_mem_cons.2 ⟨subd15_3_756, List.forall_mem_cons.2 ⟨subd15_3_757, List.forall_mem_cons.2 ⟨subd15_3_758, List.forall_mem_cons.2 ⟨subd15_3_759, List.forall_mem_cons.2 ⟨subd15_3_760, List.forall_mem_cons.2 ⟨subd15_3_761, List.forall_mem_cons.2 ⟨subd15_3_762, List.forall_mem_cons.2 ⟨subd15_3_763, List.forall_mem_cons.2 ⟨subd15_3_764, List.forall_mem_cons.2 ⟨subd15_3_765, List.forall_mem_cons.2 ⟨subd15_3_766, List.forall_mem_cons.2 ⟨subd15_3_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_768 : subd15_3 [3, 3, 1] = true := by decide +kernel
theorem subd15_3_769 : subd15_3 [3, 3, 2] = true := by decide +kernel
theorem subd15_3_770 : subd15_3 [3, 3, 3] = true := by decide +kernel
theorem subd15_3_771 : subd15_3 [3, 3, 4] = true := by decide +kernel
theorem subd15_3_772 : subd15_3 [3, 3, 5] = true := by decide +kernel
theorem subd15_3_773 : subd15_3 [3, 3, 6] = true := by decide +kernel
theorem subd15_3_774 : subd15_3 [3, 4] = true := by decide +kernel
theorem subd15_3_775 : subd15_3 [3, 5] = true := by decide +kernel
theorem subd15_3_776 : subd15_3 [4, -3] = true := by decide +kernel
theorem subd15_3_777 : subd15_3 [4, -2] = true := by decide +kernel
theorem subd15_3_778 : subd15_3 [4, -1] = true := by decide +kernel
theorem subd15_3_779 : subd15_3 [4, 0] = true := by decide +kernel
theorem subd15_3_780 : subd15_3 [4, 1] = true := by decide +kernel
theorem subd15_3_781 : subd15_3 [4, 2] = true := by decide +kernel
theorem subd15_3_782 : subd15_3 [4, 3] = true := by decide +kernel
theorem subd15_3_783 : subd15_3 [4, 4] = true := by decide +kernel
theorem subd15_3_784 : subd15_3 [5] = true := by decide +kernel
theorem sbd15_3_24 : ∀ q ∈ blkd15_3_24, subd15_3 q = true := by
  unfold blkd15_3_24
  exact List.forall_mem_cons.2 ⟨subd15_3_768, List.forall_mem_cons.2 ⟨subd15_3_769, List.forall_mem_cons.2 ⟨subd15_3_770, List.forall_mem_cons.2 ⟨subd15_3_771, List.forall_mem_cons.2 ⟨subd15_3_772, List.forall_mem_cons.2 ⟨subd15_3_773, List.forall_mem_cons.2 ⟨subd15_3_774, List.forall_mem_cons.2 ⟨subd15_3_775, List.forall_mem_cons.2 ⟨subd15_3_776, List.forall_mem_cons.2 ⟨subd15_3_777, List.forall_mem_cons.2 ⟨subd15_3_778, List.forall_mem_cons.2 ⟨subd15_3_779, List.forall_mem_cons.2 ⟨subd15_3_780, List.forall_mem_cons.2 ⟨subd15_3_781, List.forall_mem_cons.2 ⟨subd15_3_782, List.forall_mem_cons.2 ⟨subd15_3_783, List.forall_mem_cons.2 ⟨subd15_3_784, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
