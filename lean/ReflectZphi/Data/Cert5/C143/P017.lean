import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_1_384 : subd13_1 [1, -3, 5] = true := by decide +kernel
theorem subd13_1_385 : subd13_1 [1, -3, 6] = true := by decide +kernel
theorem subd13_1_386 : subd13_1 [1, -2, -7] = true := by decide +kernel
theorem subd13_1_387 : subd13_1 [1, -2, -6] = true := by decide +kernel
theorem subd13_1_388 : subd13_1 [1, -2, -5] = true := by decide +kernel
theorem subd13_1_389 : subd13_1 [1, -2, -4] = true := by decide +kernel
theorem subd13_1_390 : subd13_1 [1, -2, -3] = true := by decide +kernel
theorem subd13_1_391 : subd13_1 [1, -2, -2] = true := by decide +kernel
theorem subd13_1_392 : subd13_1 [1, -2, -1] = true := by decide +kernel
theorem subd13_1_393 : subd13_1 [1, -2, 0] = true := by decide +kernel
theorem subd13_1_394 : subd13_1 [1, -2, 1] = true := by decide +kernel
theorem subd13_1_395 : subd13_1 [1, -2, 2] = true := by decide +kernel
theorem subd13_1_396 : subd13_1 [1, -2, 3] = true := by decide +kernel
theorem subd13_1_397 : subd13_1 [1, -2, 4] = true := by decide +kernel
theorem subd13_1_398 : subd13_1 [1, -2, 5] = true := by decide +kernel
theorem subd13_1_399 : subd13_1 [1, -2, 6] = true := by decide +kernel
theorem subd13_1_400 : subd13_1 [1, -2, 7] = true := by decide +kernel
theorem subd13_1_401 : subd13_1 [1, -1, -8] = true := by decide +kernel
theorem subd13_1_402 : subd13_1 [1, -1, -7] = true := by decide +kernel
theorem subd13_1_403 : subd13_1 [1, -1, -6] = true := by decide +kernel
theorem subd13_1_404 : subd13_1 [1, -1, -5] = true := by decide +kernel
theorem subd13_1_405 : subd13_1 [1, -1, -4] = true := by decide +kernel
theorem subd13_1_406 : subd13_1 [1, -1, -3] = true := by decide +kernel
theorem subd13_1_407 : subd13_1 [1, -1, -2] = true := by decide +kernel
theorem subd13_1_408 : subd13_1 [1, -1, -1] = true := by decide +kernel
theorem subd13_1_409 : subd13_1 [1, -1, 0] = true := by decide +kernel
theorem subd13_1_410 : subd13_1 [1, -1, 1] = true := by decide +kernel
theorem subd13_1_411 : subd13_1 [1, -1, 2] = true := by decide +kernel
theorem subd13_1_412 : subd13_1 [1, -1, 3] = true := by decide +kernel
theorem subd13_1_413 : subd13_1 [1, -1, 4] = true := by decide +kernel
theorem subd13_1_414 : subd13_1 [1, -1, 5] = true := by decide +kernel
theorem subd13_1_415 : subd13_1 [1, -1, 6] = true := by decide +kernel
theorem sbd13_1_12 : ∀ q ∈ blkd13_1_12, subd13_1 q = true := by
  unfold blkd13_1_12
  exact List.forall_mem_cons.2 ⟨subd13_1_384, List.forall_mem_cons.2 ⟨subd13_1_385, List.forall_mem_cons.2 ⟨subd13_1_386, List.forall_mem_cons.2 ⟨subd13_1_387, List.forall_mem_cons.2 ⟨subd13_1_388, List.forall_mem_cons.2 ⟨subd13_1_389, List.forall_mem_cons.2 ⟨subd13_1_390, List.forall_mem_cons.2 ⟨subd13_1_391, List.forall_mem_cons.2 ⟨subd13_1_392, List.forall_mem_cons.2 ⟨subd13_1_393, List.forall_mem_cons.2 ⟨subd13_1_394, List.forall_mem_cons.2 ⟨subd13_1_395, List.forall_mem_cons.2 ⟨subd13_1_396, List.forall_mem_cons.2 ⟨subd13_1_397, List.forall_mem_cons.2 ⟨subd13_1_398, List.forall_mem_cons.2 ⟨subd13_1_399, List.forall_mem_cons.2 ⟨subd13_1_400, List.forall_mem_cons.2 ⟨subd13_1_401, List.forall_mem_cons.2 ⟨subd13_1_402, List.forall_mem_cons.2 ⟨subd13_1_403, List.forall_mem_cons.2 ⟨subd13_1_404, List.forall_mem_cons.2 ⟨subd13_1_405, List.forall_mem_cons.2 ⟨subd13_1_406, List.forall_mem_cons.2 ⟨subd13_1_407, List.forall_mem_cons.2 ⟨subd13_1_408, List.forall_mem_cons.2 ⟨subd13_1_409, List.forall_mem_cons.2 ⟨subd13_1_410, List.forall_mem_cons.2 ⟨subd13_1_411, List.forall_mem_cons.2 ⟨subd13_1_412, List.forall_mem_cons.2 ⟨subd13_1_413, List.forall_mem_cons.2 ⟨subd13_1_414, List.forall_mem_cons.2 ⟨subd13_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_416 : subd13_1 [1, -1, 7] = true := by decide +kernel
theorem subd13_1_417 : subd13_1 [1, 0, -8] = true := by decide +kernel
theorem subd13_1_418 : subd13_1 [1, 0, -7] = true := by decide +kernel
theorem subd13_1_419 : subd13_1 [1, 0, -6] = true := by decide +kernel
theorem subd13_1_420 : subd13_1 [1, 0, -5] = true := by decide +kernel
theorem subd13_1_421 : subd13_1 [1, 0, -4] = true := by decide +kernel
theorem subd13_1_422 : subd13_1 [1, 0, -3] = true := by decide +kernel
theorem subd13_1_423 : subd13_1 [1, 0, -2] = true := by decide +kernel
theorem subd13_1_424 : subd13_1 [1, 0, -1] = true := by decide +kernel
theorem subd13_1_425 : subd13_1 [1, 0, 0] = true := by decide +kernel
theorem subd13_1_426 : subd13_1 [1, 0, 1] = true := by decide +kernel
theorem subd13_1_427 : subd13_1 [1, 0, 2] = true := by decide +kernel
theorem subd13_1_428 : subd13_1 [1, 0, 3] = true := by decide +kernel
theorem subd13_1_429 : subd13_1 [1, 0, 4] = true := by decide +kernel
theorem subd13_1_430 : subd13_1 [1, 0, 5] = true := by decide +kernel
theorem subd13_1_431 : subd13_1 [1, 0, 6] = true := by decide +kernel
theorem subd13_1_432 : subd13_1 [1, 0, 7] = true := by decide +kernel
theorem subd13_1_433 : subd13_1 [1, 0, 8] = true := by decide +kernel
theorem subd13_1_434 : subd13_1 [1, 1, -8] = true := by decide +kernel
theorem subd13_1_435 : subd13_1 [1, 1, -7] = true := by decide +kernel
theorem subd13_1_436 : subd13_1 [1, 1, -6] = true := by decide +kernel
theorem subd13_1_437 : subd13_1 [1, 1, -5] = true := by decide +kernel
theorem subd13_1_438 : subd13_1 [1, 1, -4] = true := by decide +kernel
theorem subd13_1_439 : subd13_1 [1, 1, -3] = true := by decide +kernel
theorem subd13_1_440 : subd13_1 [1, 1, -2] = true := by decide +kernel
theorem subd13_1_441 : subd13_1 [1, 1, -1] = true := by decide +kernel
theorem subd13_1_442 : subd13_1 [1, 1, 0] = true := by decide +kernel
theorem subd13_1_443 : subd13_1 [1, 1, 1] = true := by decide +kernel
theorem subd13_1_444 : subd13_1 [1, 1, 2] = true := by decide +kernel
theorem subd13_1_445 : subd13_1 [1, 1, 3] = true := by decide +kernel
theorem subd13_1_446 : subd13_1 [1, 1, 4] = true := by decide +kernel
theorem subd13_1_447 : subd13_1 [1, 1, 5] = true := by decide +kernel
theorem sbd13_1_13 : ∀ q ∈ blkd13_1_13, subd13_1 q = true := by
  unfold blkd13_1_13
  exact List.forall_mem_cons.2 ⟨subd13_1_416, List.forall_mem_cons.2 ⟨subd13_1_417, List.forall_mem_cons.2 ⟨subd13_1_418, List.forall_mem_cons.2 ⟨subd13_1_419, List.forall_mem_cons.2 ⟨subd13_1_420, List.forall_mem_cons.2 ⟨subd13_1_421, List.forall_mem_cons.2 ⟨subd13_1_422, List.forall_mem_cons.2 ⟨subd13_1_423, List.forall_mem_cons.2 ⟨subd13_1_424, List.forall_mem_cons.2 ⟨subd13_1_425, List.forall_mem_cons.2 ⟨subd13_1_426, List.forall_mem_cons.2 ⟨subd13_1_427, List.forall_mem_cons.2 ⟨subd13_1_428, List.forall_mem_cons.2 ⟨subd13_1_429, List.forall_mem_cons.2 ⟨subd13_1_430, List.forall_mem_cons.2 ⟨subd13_1_431, List.forall_mem_cons.2 ⟨subd13_1_432, List.forall_mem_cons.2 ⟨subd13_1_433, List.forall_mem_cons.2 ⟨subd13_1_434, List.forall_mem_cons.2 ⟨subd13_1_435, List.forall_mem_cons.2 ⟨subd13_1_436, List.forall_mem_cons.2 ⟨subd13_1_437, List.forall_mem_cons.2 ⟨subd13_1_438, List.forall_mem_cons.2 ⟨subd13_1_439, List.forall_mem_cons.2 ⟨subd13_1_440, List.forall_mem_cons.2 ⟨subd13_1_441, List.forall_mem_cons.2 ⟨subd13_1_442, List.forall_mem_cons.2 ⟨subd13_1_443, List.forall_mem_cons.2 ⟨subd13_1_444, List.forall_mem_cons.2 ⟨subd13_1_445, List.forall_mem_cons.2 ⟨subd13_1_446, List.forall_mem_cons.2 ⟨subd13_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_448 : subd13_1 [1, 1, 6] = true := by decide +kernel
theorem subd13_1_449 : subd13_1 [1, 1, 7] = true := by decide +kernel
theorem subd13_1_450 : subd13_1 [1, 2, -7] = true := by decide +kernel
theorem subd13_1_451 : subd13_1 [1, 2, -6] = true := by decide +kernel
theorem subd13_1_452 : subd13_1 [1, 2, -5] = true := by decide +kernel
theorem subd13_1_453 : subd13_1 [1, 2, -4] = true := by decide +kernel
theorem subd13_1_454 : subd13_1 [1, 2, -3] = true := by decide +kernel
theorem subd13_1_455 : subd13_1 [1, 2, -2] = true := by decide +kernel
theorem subd13_1_456 : subd13_1 [1, 2, -1] = true := by decide +kernel
theorem subd13_1_457 : subd13_1 [1, 2, 0] = true := by decide +kernel
theorem subd13_1_458 : subd13_1 [1, 2, 1] = true := by decide +kernel
theorem subd13_1_459 : subd13_1 [1, 2, 2] = true := by decide +kernel
theorem subd13_1_460 : subd13_1 [1, 2, 3] = true := by decide +kernel
theorem subd13_1_461 : subd13_1 [1, 2, 4] = true := by decide +kernel
theorem subd13_1_462 : subd13_1 [1, 2, 5] = true := by decide +kernel
theorem subd13_1_463 : subd13_1 [1, 2, 6] = true := by decide +kernel
theorem subd13_1_464 : subd13_1 [1, 2, 7] = true := by decide +kernel
theorem subd13_1_465 : subd13_1 [1, 3, -7] = true := by decide +kernel
theorem subd13_1_466 : subd13_1 [1, 3, -6] = true := by decide +kernel
theorem subd13_1_467 : subd13_1 [1, 3, -5] = true := by decide +kernel
theorem subd13_1_468 : subd13_1 [1, 3, -4] = true := by decide +kernel
theorem subd13_1_469 : subd13_1 [1, 3, -3] = true := by decide +kernel
theorem subd13_1_470 : subd13_1 [1, 3, -2] = true := by decide +kernel
theorem subd13_1_471 : subd13_1 [1, 3, -1] = true := by decide +kernel
theorem subd13_1_472 : subd13_1 [1, 3, 0] = true := by decide +kernel
theorem subd13_1_473 : subd13_1 [1, 3, 1] = true := by decide +kernel
theorem subd13_1_474 : subd13_1 [1, 3, 2] = true := by decide +kernel
theorem subd13_1_475 : subd13_1 [1, 3, 3] = true := by decide +kernel
theorem subd13_1_476 : subd13_1 [1, 3, 4] = true := by decide +kernel
theorem subd13_1_477 : subd13_1 [1, 3, 5] = true := by decide +kernel
theorem subd13_1_478 : subd13_1 [1, 3, 6] = true := by decide +kernel
theorem subd13_1_479 : subd13_1 [1, 4] = true := by decide +kernel
theorem sbd13_1_14 : ∀ q ∈ blkd13_1_14, subd13_1 q = true := by
  unfold blkd13_1_14
  exact List.forall_mem_cons.2 ⟨subd13_1_448, List.forall_mem_cons.2 ⟨subd13_1_449, List.forall_mem_cons.2 ⟨subd13_1_450, List.forall_mem_cons.2 ⟨subd13_1_451, List.forall_mem_cons.2 ⟨subd13_1_452, List.forall_mem_cons.2 ⟨subd13_1_453, List.forall_mem_cons.2 ⟨subd13_1_454, List.forall_mem_cons.2 ⟨subd13_1_455, List.forall_mem_cons.2 ⟨subd13_1_456, List.forall_mem_cons.2 ⟨subd13_1_457, List.forall_mem_cons.2 ⟨subd13_1_458, List.forall_mem_cons.2 ⟨subd13_1_459, List.forall_mem_cons.2 ⟨subd13_1_460, List.forall_mem_cons.2 ⟨subd13_1_461, List.forall_mem_cons.2 ⟨subd13_1_462, List.forall_mem_cons.2 ⟨subd13_1_463, List.forall_mem_cons.2 ⟨subd13_1_464, List.forall_mem_cons.2 ⟨subd13_1_465, List.forall_mem_cons.2 ⟨subd13_1_466, List.forall_mem_cons.2 ⟨subd13_1_467, List.forall_mem_cons.2 ⟨subd13_1_468, List.forall_mem_cons.2 ⟨subd13_1_469, List.forall_mem_cons.2 ⟨subd13_1_470, List.forall_mem_cons.2 ⟨subd13_1_471, List.forall_mem_cons.2 ⟨subd13_1_472, List.forall_mem_cons.2 ⟨subd13_1_473, List.forall_mem_cons.2 ⟨subd13_1_474, List.forall_mem_cons.2 ⟨subd13_1_475, List.forall_mem_cons.2 ⟨subd13_1_476, List.forall_mem_cons.2 ⟨subd13_1_477, List.forall_mem_cons.2 ⟨subd13_1_478, List.forall_mem_cons.2 ⟨subd13_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_480 : subd13_1 [1, 5] = true := by decide +kernel
theorem subd13_1_481 : subd13_1 [2, -5] = true := by decide +kernel
theorem subd13_1_482 : subd13_1 [2, -4] = true := by decide +kernel
theorem subd13_1_483 : subd13_1 [2, -3] = true := by decide +kernel
theorem subd13_1_484 : subd13_1 [2, -2, -7] = true := by decide +kernel
theorem subd13_1_485 : subd13_1 [2, -2, -6] = true := by decide +kernel
theorem subd13_1_486 : subd13_1 [2, -2, -5] = true := by decide +kernel
theorem subd13_1_487 : subd13_1 [2, -2, -4] = true := by decide +kernel
theorem subd13_1_488 : subd13_1 [2, -2, -3] = true := by decide +kernel
theorem subd13_1_489 : subd13_1 [2, -2, -2] = true := by decide +kernel
theorem subd13_1_490 : subd13_1 [2, -2, -1] = true := by decide +kernel
theorem subd13_1_491 : subd13_1 [2, -2, 0] = true := by decide +kernel
theorem subd13_1_492 : subd13_1 [2, -2, 1] = true := by decide +kernel
theorem subd13_1_493 : subd13_1 [2, -2, 2] = true := by decide +kernel
theorem subd13_1_494 : subd13_1 [2, -2, 3] = true := by decide +kernel
theorem subd13_1_495 : subd13_1 [2, -2, 4] = true := by decide +kernel
theorem subd13_1_496 : subd13_1 [2, -2, 5] = true := by decide +kernel
theorem subd13_1_497 : subd13_1 [2, -2, 6] = true := by decide +kernel
theorem subd13_1_498 : subd13_1 [2, -2, 7] = true := by decide +kernel
theorem subd13_1_499 : subd13_1 [2, -1, -7] = true := by decide +kernel
theorem subd13_1_500 : subd13_1 [2, -1, -6] = true := by decide +kernel
theorem subd13_1_501 : subd13_1 [2, -1, -5] = true := by decide +kernel
theorem subd13_1_502 : subd13_1 [2, -1, -4] = true := by decide +kernel
theorem subd13_1_503 : subd13_1 [2, -1, -3] = true := by decide +kernel
theorem subd13_1_504 : subd13_1 [2, -1, -2] = true := by decide +kernel
theorem subd13_1_505 : subd13_1 [2, -1, -1] = true := by decide +kernel
theorem subd13_1_506 : subd13_1 [2, -1, 0] = true := by decide +kernel
theorem subd13_1_507 : subd13_1 [2, -1, 1] = true := by decide +kernel
theorem subd13_1_508 : subd13_1 [2, -1, 2] = true := by decide +kernel
theorem subd13_1_509 : subd13_1 [2, -1, 3] = true := by decide +kernel
theorem subd13_1_510 : subd13_1 [2, -1, 4] = true := by decide +kernel
theorem subd13_1_511 : subd13_1 [2, -1, 5] = true := by decide +kernel
theorem sbd13_1_15 : ∀ q ∈ blkd13_1_15, subd13_1 q = true := by
  unfold blkd13_1_15
  exact List.forall_mem_cons.2 ⟨subd13_1_480, List.forall_mem_cons.2 ⟨subd13_1_481, List.forall_mem_cons.2 ⟨subd13_1_482, List.forall_mem_cons.2 ⟨subd13_1_483, List.forall_mem_cons.2 ⟨subd13_1_484, List.forall_mem_cons.2 ⟨subd13_1_485, List.forall_mem_cons.2 ⟨subd13_1_486, List.forall_mem_cons.2 ⟨subd13_1_487, List.forall_mem_cons.2 ⟨subd13_1_488, List.forall_mem_cons.2 ⟨subd13_1_489, List.forall_mem_cons.2 ⟨subd13_1_490, List.forall_mem_cons.2 ⟨subd13_1_491, List.forall_mem_cons.2 ⟨subd13_1_492, List.forall_mem_cons.2 ⟨subd13_1_493, List.forall_mem_cons.2 ⟨subd13_1_494, List.forall_mem_cons.2 ⟨subd13_1_495, List.forall_mem_cons.2 ⟨subd13_1_496, List.forall_mem_cons.2 ⟨subd13_1_497, List.forall_mem_cons.2 ⟨subd13_1_498, List.forall_mem_cons.2 ⟨subd13_1_499, List.forall_mem_cons.2 ⟨subd13_1_500, List.forall_mem_cons.2 ⟨subd13_1_501, List.forall_mem_cons.2 ⟨subd13_1_502, List.forall_mem_cons.2 ⟨subd13_1_503, List.forall_mem_cons.2 ⟨subd13_1_504, List.forall_mem_cons.2 ⟨subd13_1_505, List.forall_mem_cons.2 ⟨subd13_1_506, List.forall_mem_cons.2 ⟨subd13_1_507, List.forall_mem_cons.2 ⟨subd13_1_508, List.forall_mem_cons.2 ⟨subd13_1_509, List.forall_mem_cons.2 ⟨subd13_1_510, List.forall_mem_cons.2 ⟨subd13_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_512 : subd13_1 [2, -1, 6] = true := by decide +kernel
theorem subd13_1_513 : subd13_1 [2, -1, 7] = true := by decide +kernel
theorem subd13_1_514 : subd13_1 [2, 0, -7] = true := by decide +kernel
theorem subd13_1_515 : subd13_1 [2, 0, -6] = true := by decide +kernel
theorem subd13_1_516 : subd13_1 [2, 0, -5] = true := by decide +kernel
theorem subd13_1_517 : subd13_1 [2, 0, -4] = true := by decide +kernel
theorem subd13_1_518 : subd13_1 [2, 0, -3] = true := by decide +kernel
theorem subd13_1_519 : subd13_1 [2, 0, -2] = true := by decide +kernel
theorem subd13_1_520 : subd13_1 [2, 0, -1] = true := by decide +kernel
theorem subd13_1_521 : subd13_1 [2, 0, 0] = true := by decide +kernel
theorem subd13_1_522 : subd13_1 [2, 0, 1] = true := by decide +kernel
theorem subd13_1_523 : subd13_1 [2, 0, 2] = true := by decide +kernel
theorem subd13_1_524 : subd13_1 [2, 0, 3] = true := by decide +kernel
theorem subd13_1_525 : subd13_1 [2, 0, 4] = true := by decide +kernel
theorem subd13_1_526 : subd13_1 [2, 0, 5] = true := by decide +kernel
theorem subd13_1_527 : subd13_1 [2, 0, 6] = true := by decide +kernel
theorem subd13_1_528 : subd13_1 [2, 0, 7] = true := by decide +kernel
theorem subd13_1_529 : subd13_1 [2, 1, -7] = true := by decide +kernel
theorem subd13_1_530 : subd13_1 [2, 1, -6] = true := by decide +kernel
theorem subd13_1_531 : subd13_1 [2, 1, -5] = true := by decide +kernel
theorem subd13_1_532 : subd13_1 [2, 1, -4] = true := by decide +kernel
theorem subd13_1_533 : subd13_1 [2, 1, -3] = true := by decide +kernel
theorem subd13_1_534 : subd13_1 [2, 1, -2] = true := by decide +kernel
theorem subd13_1_535 : subd13_1 [2, 1, -1] = true := by decide +kernel
theorem subd13_1_536 : subd13_1 [2, 1, 0] = true := by decide +kernel
theorem subd13_1_537 : subd13_1 [2, 1, 1] = true := by decide +kernel
theorem subd13_1_538 : subd13_1 [2, 1, 2] = true := by decide +kernel
theorem subd13_1_539 : subd13_1 [2, 1, 3] = true := by decide +kernel
theorem subd13_1_540 : subd13_1 [2, 1, 4] = true := by decide +kernel
theorem subd13_1_541 : subd13_1 [2, 1, 5] = true := by decide +kernel
theorem subd13_1_542 : subd13_1 [2, 1, 6] = true := by decide +kernel
theorem subd13_1_543 : subd13_1 [2, 1, 7] = true := by decide +kernel
theorem sbd13_1_16 : ∀ q ∈ blkd13_1_16, subd13_1 q = true := by
  unfold blkd13_1_16
  exact List.forall_mem_cons.2 ⟨subd13_1_512, List.forall_mem_cons.2 ⟨subd13_1_513, List.forall_mem_cons.2 ⟨subd13_1_514, List.forall_mem_cons.2 ⟨subd13_1_515, List.forall_mem_cons.2 ⟨subd13_1_516, List.forall_mem_cons.2 ⟨subd13_1_517, List.forall_mem_cons.2 ⟨subd13_1_518, List.forall_mem_cons.2 ⟨subd13_1_519, List.forall_mem_cons.2 ⟨subd13_1_520, List.forall_mem_cons.2 ⟨subd13_1_521, List.forall_mem_cons.2 ⟨subd13_1_522, List.forall_mem_cons.2 ⟨subd13_1_523, List.forall_mem_cons.2 ⟨subd13_1_524, List.forall_mem_cons.2 ⟨subd13_1_525, List.forall_mem_cons.2 ⟨subd13_1_526, List.forall_mem_cons.2 ⟨subd13_1_527, List.forall_mem_cons.2 ⟨subd13_1_528, List.forall_mem_cons.2 ⟨subd13_1_529, List.forall_mem_cons.2 ⟨subd13_1_530, List.forall_mem_cons.2 ⟨subd13_1_531, List.forall_mem_cons.2 ⟨subd13_1_532, List.forall_mem_cons.2 ⟨subd13_1_533, List.forall_mem_cons.2 ⟨subd13_1_534, List.forall_mem_cons.2 ⟨subd13_1_535, List.forall_mem_cons.2 ⟨subd13_1_536, List.forall_mem_cons.2 ⟨subd13_1_537, List.forall_mem_cons.2 ⟨subd13_1_538, List.forall_mem_cons.2 ⟨subd13_1_539, List.forall_mem_cons.2 ⟨subd13_1_540, List.forall_mem_cons.2 ⟨subd13_1_541, List.forall_mem_cons.2 ⟨subd13_1_542, List.forall_mem_cons.2 ⟨subd13_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_544 : subd13_1 [2, 2, -7] = true := by decide +kernel
theorem subd13_1_545 : subd13_1 [2, 2, -6] = true := by decide +kernel
theorem subd13_1_546 : subd13_1 [2, 2, -5] = true := by decide +kernel
theorem subd13_1_547 : subd13_1 [2, 2, -4] = true := by decide +kernel
theorem subd13_1_548 : subd13_1 [2, 2, -3] = true := by decide +kernel
theorem subd13_1_549 : subd13_1 [2, 2, -2] = true := by decide +kernel
theorem subd13_1_550 : subd13_1 [2, 2, -1] = true := by decide +kernel
theorem subd13_1_551 : subd13_1 [2, 2, 0] = true := by decide +kernel
theorem subd13_1_552 : subd13_1 [2, 2, 1] = true := by decide +kernel
theorem subd13_1_553 : subd13_1 [2, 2, 2] = true := by decide +kernel
theorem subd13_1_554 : subd13_1 [2, 2, 3] = true := by decide +kernel
theorem subd13_1_555 : subd13_1 [2, 2, 4] = true := by decide +kernel
theorem subd13_1_556 : subd13_1 [2, 2, 5] = true := by decide +kernel
theorem subd13_1_557 : subd13_1 [2, 2, 6] = true := by decide +kernel
theorem subd13_1_558 : subd13_1 [2, 2, 7] = true := by decide +kernel
theorem subd13_1_559 : subd13_1 [2, 3] = true := by decide +kernel
theorem subd13_1_560 : subd13_1 [2, 4] = true := by decide +kernel
theorem subd13_1_561 : subd13_1 [2, 5] = true := by decide +kernel
theorem subd13_1_562 : subd13_1 [3, -5] = true := by decide +kernel
theorem subd13_1_563 : subd13_1 [3, -4] = true := by decide +kernel
theorem subd13_1_564 : subd13_1 [3, -3] = true := by decide +kernel
theorem subd13_1_565 : subd13_1 [3, -2] = true := by decide +kernel
theorem subd13_1_566 : subd13_1 [3, -1, -6] = true := by decide +kernel
theorem subd13_1_567 : subd13_1 [3, -1, -5] = true := by decide +kernel
theorem subd13_1_568 : subd13_1 [3, -1, -4] = true := by decide +kernel
theorem subd13_1_569 : subd13_1 [3, -1, -3] = true := by decide +kernel
theorem subd13_1_570 : subd13_1 [3, -1, -2] = true := by decide +kernel
theorem subd13_1_571 : subd13_1 [3, -1, -1] = true := by decide +kernel
theorem subd13_1_572 : subd13_1 [3, -1, 0] = true := by decide +kernel
theorem subd13_1_573 : subd13_1 [3, -1, 1] = true := by decide +kernel
theorem subd13_1_574 : subd13_1 [3, -1, 2] = true := by decide +kernel
theorem subd13_1_575 : subd13_1 [3, -1, 3] = true := by decide +kernel
theorem sbd13_1_17 : ∀ q ∈ blkd13_1_17, subd13_1 q = true := by
  unfold blkd13_1_17
  exact List.forall_mem_cons.2 ⟨subd13_1_544, List.forall_mem_cons.2 ⟨subd13_1_545, List.forall_mem_cons.2 ⟨subd13_1_546, List.forall_mem_cons.2 ⟨subd13_1_547, List.forall_mem_cons.2 ⟨subd13_1_548, List.forall_mem_cons.2 ⟨subd13_1_549, List.forall_mem_cons.2 ⟨subd13_1_550, List.forall_mem_cons.2 ⟨subd13_1_551, List.forall_mem_cons.2 ⟨subd13_1_552, List.forall_mem_cons.2 ⟨subd13_1_553, List.forall_mem_cons.2 ⟨subd13_1_554, List.forall_mem_cons.2 ⟨subd13_1_555, List.forall_mem_cons.2 ⟨subd13_1_556, List.forall_mem_cons.2 ⟨subd13_1_557, List.forall_mem_cons.2 ⟨subd13_1_558, List.forall_mem_cons.2 ⟨subd13_1_559, List.forall_mem_cons.2 ⟨subd13_1_560, List.forall_mem_cons.2 ⟨subd13_1_561, List.forall_mem_cons.2 ⟨subd13_1_562, List.forall_mem_cons.2 ⟨subd13_1_563, List.forall_mem_cons.2 ⟨subd13_1_564, List.forall_mem_cons.2 ⟨subd13_1_565, List.forall_mem_cons.2 ⟨subd13_1_566, List.forall_mem_cons.2 ⟨subd13_1_567, List.forall_mem_cons.2 ⟨subd13_1_568, List.forall_mem_cons.2 ⟨subd13_1_569, List.forall_mem_cons.2 ⟨subd13_1_570, List.forall_mem_cons.2 ⟨subd13_1_571, List.forall_mem_cons.2 ⟨subd13_1_572, List.forall_mem_cons.2 ⟨subd13_1_573, List.forall_mem_cons.2 ⟨subd13_1_574, List.forall_mem_cons.2 ⟨subd13_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_576 : subd13_1 [3, -1, 4] = true := by decide +kernel
theorem subd13_1_577 : subd13_1 [3, -1, 5] = true := by decide +kernel
theorem subd13_1_578 : subd13_1 [3, -1, 6] = true := by decide +kernel
theorem subd13_1_579 : subd13_1 [3, -1, 7] = true := by decide +kernel
theorem subd13_1_580 : subd13_1 [3, 0, -6] = true := by decide +kernel
theorem subd13_1_581 : subd13_1 [3, 0, -5] = true := by decide +kernel
theorem subd13_1_582 : subd13_1 [3, 0, -4] = true := by decide +kernel
theorem subd13_1_583 : subd13_1 [3, 0, -3] = true := by decide +kernel
theorem subd13_1_584 : subd13_1 [3, 0, -2] = true := by decide +kernel
theorem subd13_1_585 : subd13_1 [3, 0, -1] = true := by decide +kernel
theorem subd13_1_586 : subd13_1 [3, 0, 0] = true := by decide +kernel
theorem subd13_1_587 : subd13_1 [3, 0, 1] = true := by decide +kernel
theorem subd13_1_588 : subd13_1 [3, 0, 2] = true := by decide +kernel
theorem subd13_1_589 : subd13_1 [3, 0, 3] = true := by decide +kernel
theorem subd13_1_590 : subd13_1 [3, 0, 4] = true := by decide +kernel
theorem subd13_1_591 : subd13_1 [3, 0, 5] = true := by decide +kernel
theorem subd13_1_592 : subd13_1 [3, 0, 6] = true := by decide +kernel
theorem subd13_1_593 : subd13_1 [3, 0, 7] = true := by decide +kernel
theorem subd13_1_594 : subd13_1 [3, 1, -6] = true := by decide +kernel
theorem subd13_1_595 : subd13_1 [3, 1, -5] = true := by decide +kernel
theorem subd13_1_596 : subd13_1 [3, 1, -4] = true := by decide +kernel
theorem subd13_1_597 : subd13_1 [3, 1, -3] = true := by decide +kernel
theorem subd13_1_598 : subd13_1 [3, 1, -2] = true := by decide +kernel
theorem subd13_1_599 : subd13_1 [3, 1, -1] = true := by decide +kernel
theorem subd13_1_600 : subd13_1 [3, 1, 0] = true := by decide +kernel
theorem subd13_1_601 : subd13_1 [3, 1, 1] = true := by decide +kernel
theorem subd13_1_602 : subd13_1 [3, 1, 2] = true := by decide +kernel
theorem subd13_1_603 : subd13_1 [3, 1, 3] = true := by decide +kernel
theorem subd13_1_604 : subd13_1 [3, 1, 4] = true := by decide +kernel
theorem subd13_1_605 : subd13_1 [3, 1, 5] = true := by decide +kernel
theorem subd13_1_606 : subd13_1 [3, 1, 6] = true := by decide +kernel
theorem subd13_1_607 : subd13_1 [3, 1, 7] = true := by decide +kernel
theorem sbd13_1_18 : ∀ q ∈ blkd13_1_18, subd13_1 q = true := by
  unfold blkd13_1_18
  exact List.forall_mem_cons.2 ⟨subd13_1_576, List.forall_mem_cons.2 ⟨subd13_1_577, List.forall_mem_cons.2 ⟨subd13_1_578, List.forall_mem_cons.2 ⟨subd13_1_579, List.forall_mem_cons.2 ⟨subd13_1_580, List.forall_mem_cons.2 ⟨subd13_1_581, List.forall_mem_cons.2 ⟨subd13_1_582, List.forall_mem_cons.2 ⟨subd13_1_583, List.forall_mem_cons.2 ⟨subd13_1_584, List.forall_mem_cons.2 ⟨subd13_1_585, List.forall_mem_cons.2 ⟨subd13_1_586, List.forall_mem_cons.2 ⟨subd13_1_587, List.forall_mem_cons.2 ⟨subd13_1_588, List.forall_mem_cons.2 ⟨subd13_1_589, List.forall_mem_cons.2 ⟨subd13_1_590, List.forall_mem_cons.2 ⟨subd13_1_591, List.forall_mem_cons.2 ⟨subd13_1_592, List.forall_mem_cons.2 ⟨subd13_1_593, List.forall_mem_cons.2 ⟨subd13_1_594, List.forall_mem_cons.2 ⟨subd13_1_595, List.forall_mem_cons.2 ⟨subd13_1_596, List.forall_mem_cons.2 ⟨subd13_1_597, List.forall_mem_cons.2 ⟨subd13_1_598, List.forall_mem_cons.2 ⟨subd13_1_599, List.forall_mem_cons.2 ⟨subd13_1_600, List.forall_mem_cons.2 ⟨subd13_1_601, List.forall_mem_cons.2 ⟨subd13_1_602, List.forall_mem_cons.2 ⟨subd13_1_603, List.forall_mem_cons.2 ⟨subd13_1_604, List.forall_mem_cons.2 ⟨subd13_1_605, List.forall_mem_cons.2 ⟨subd13_1_606, List.forall_mem_cons.2 ⟨subd13_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_608 : subd13_1 [3, 2] = true := by decide +kernel
theorem subd13_1_609 : subd13_1 [3, 3] = true := by decide +kernel
theorem subd13_1_610 : subd13_1 [3, 4] = true := by decide +kernel
theorem subd13_1_611 : subd13_1 [4, -4] = true := by decide +kernel
theorem subd13_1_612 : subd13_1 [4, -3] = true := by decide +kernel
theorem subd13_1_613 : subd13_1 [4, -2] = true := by decide +kernel
theorem subd13_1_614 : subd13_1 [4, -1] = true := by decide +kernel
theorem subd13_1_615 : subd13_1 [4, 0] = true := by decide +kernel
theorem subd13_1_616 : subd13_1 [4, 1] = true := by decide +kernel
theorem subd13_1_617 : subd13_1 [4, 2] = true := by decide +kernel
theorem subd13_1_618 : subd13_1 [4, 3] = true := by decide +kernel
theorem subd13_1_619 : subd13_1 [5, -3] = true := by decide +kernel
theorem subd13_1_620 : subd13_1 [5, -2] = true := by decide +kernel
theorem subd13_1_621 : subd13_1 [5, -1] = true := by decide +kernel
theorem subd13_1_622 : subd13_1 [5, 0] = true := by decide +kernel
theorem subd13_1_623 : subd13_1 [5, 1] = true := by decide +kernel
theorem subd13_1_624 : subd13_1 [5, 2] = true := by decide +kernel
theorem sbd13_1_19 : ∀ q ∈ blkd13_1_19, subd13_1 q = true := by
  unfold blkd13_1_19
  exact List.forall_mem_cons.2 ⟨subd13_1_608, List.forall_mem_cons.2 ⟨subd13_1_609, List.forall_mem_cons.2 ⟨subd13_1_610, List.forall_mem_cons.2 ⟨subd13_1_611, List.forall_mem_cons.2 ⟨subd13_1_612, List.forall_mem_cons.2 ⟨subd13_1_613, List.forall_mem_cons.2 ⟨subd13_1_614, List.forall_mem_cons.2 ⟨subd13_1_615, List.forall_mem_cons.2 ⟨subd13_1_616, List.forall_mem_cons.2 ⟨subd13_1_617, List.forall_mem_cons.2 ⟨subd13_1_618, List.forall_mem_cons.2 ⟨subd13_1_619, List.forall_mem_cons.2 ⟨subd13_1_620, List.forall_mem_cons.2 ⟨subd13_1_621, List.forall_mem_cons.2 ⟨subd13_1_622, List.forall_mem_cons.2 ⟨subd13_1_623, List.forall_mem_cons.2 ⟨subd13_1_624, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [-5] = true := by decide +kernel
theorem subd13_2_1 : subd13_2 [-4, -4] = true := by decide +kernel
theorem subd13_2_2 : subd13_2 [-4, -3] = true := by decide +kernel
theorem subd13_2_3 : subd13_2 [-4, -2] = true := by decide +kernel
theorem subd13_2_4 : subd13_2 [-4, -1] = true := by decide +kernel
theorem subd13_2_5 : subd13_2 [-4, 0] = true := by decide +kernel
theorem subd13_2_6 : subd13_2 [-4, 1] = true := by decide +kernel
theorem subd13_2_7 : subd13_2 [-4, 2] = true := by decide +kernel
theorem subd13_2_8 : subd13_2 [-4, 3] = true := by decide +kernel
theorem subd13_2_9 : subd13_2 [-3, -5] = true := by decide +kernel
theorem subd13_2_10 : subd13_2 [-3, -4] = true := by decide +kernel
theorem subd13_2_11 : subd13_2 [-3, -3] = true := by decide +kernel
theorem subd13_2_12 : subd13_2 [-3, -2] = true := by decide +kernel
theorem subd13_2_13 : subd13_2 [-3, -1] = true := by decide +kernel
theorem subd13_2_14 : subd13_2 [-3, 0] = true := by decide +kernel
theorem subd13_2_15 : subd13_2 [-3, 1] = true := by decide +kernel
theorem subd13_2_16 : subd13_2 [-3, 2] = true := by decide +kernel
theorem subd13_2_17 : subd13_2 [-3, 3] = true := by decide +kernel
theorem subd13_2_18 : subd13_2 [-3, 4] = true := by decide +kernel
theorem subd13_2_19 : subd13_2 [-2, -5] = true := by decide +kernel
theorem subd13_2_20 : subd13_2 [-2, -4] = true := by decide +kernel
theorem subd13_2_21 : subd13_2 [-2, -3] = true := by decide +kernel
theorem subd13_2_22 : subd13_2 [-2, -2] = true := by decide +kernel
theorem subd13_2_23 : subd13_2 [-2, -1] = true := by decide +kernel
theorem subd13_2_24 : subd13_2 [-2, 0, -6] = true := by decide +kernel
theorem subd13_2_25 : subd13_2 [-2, 0, -5] = true := by decide +kernel
theorem subd13_2_26 : subd13_2 [-2, 0, -4] = true := by decide +kernel
theorem subd13_2_27 : subd13_2 [-2, 0, -3] = true := by decide +kernel
theorem subd13_2_28 : subd13_2 [-2, 0, -2] = true := by decide +kernel
theorem subd13_2_29 : subd13_2 [-2, 0, -1] = true := by decide +kernel
theorem subd13_2_30 : subd13_2 [-2, 0, 0] = true := by decide +kernel
theorem subd13_2_31 : subd13_2 [-2, 0, 1] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_cons.2 ⟨subd13_2_1, List.forall_mem_cons.2 ⟨subd13_2_2, List.forall_mem_cons.2 ⟨subd13_2_3, List.forall_mem_cons.2 ⟨subd13_2_4, List.forall_mem_cons.2 ⟨subd13_2_5, List.forall_mem_cons.2 ⟨subd13_2_6, List.forall_mem_cons.2 ⟨subd13_2_7, List.forall_mem_cons.2 ⟨subd13_2_8, List.forall_mem_cons.2 ⟨subd13_2_9, List.forall_mem_cons.2 ⟨subd13_2_10, List.forall_mem_cons.2 ⟨subd13_2_11, List.forall_mem_cons.2 ⟨subd13_2_12, List.forall_mem_cons.2 ⟨subd13_2_13, List.forall_mem_cons.2 ⟨subd13_2_14, List.forall_mem_cons.2 ⟨subd13_2_15, List.forall_mem_cons.2 ⟨subd13_2_16, List.forall_mem_cons.2 ⟨subd13_2_17, List.forall_mem_cons.2 ⟨subd13_2_18, List.forall_mem_cons.2 ⟨subd13_2_19, List.forall_mem_cons.2 ⟨subd13_2_20, List.forall_mem_cons.2 ⟨subd13_2_21, List.forall_mem_cons.2 ⟨subd13_2_22, List.forall_mem_cons.2 ⟨subd13_2_23, List.forall_mem_cons.2 ⟨subd13_2_24, List.forall_mem_cons.2 ⟨subd13_2_25, List.forall_mem_cons.2 ⟨subd13_2_26, List.forall_mem_cons.2 ⟨subd13_2_27, List.forall_mem_cons.2 ⟨subd13_2_28, List.forall_mem_cons.2 ⟨subd13_2_29, List.forall_mem_cons.2 ⟨subd13_2_30, List.forall_mem_cons.2 ⟨subd13_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
