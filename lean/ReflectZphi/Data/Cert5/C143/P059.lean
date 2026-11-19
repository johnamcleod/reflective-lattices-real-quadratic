import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd18_2_384 : subd18_2 [1, 2, 3] = true := by decide +kernel
theorem subd18_2_385 : subd18_2 [1, 2, 4] = true := by decide +kernel
theorem subd18_2_386 : subd18_2 [1, 2, 5] = true := by decide +kernel
theorem subd18_2_387 : subd18_2 [1, 2, 6] = true := by decide +kernel
theorem subd18_2_388 : subd18_2 [1, 2, 7] = true := by decide +kernel
theorem subd18_2_389 : subd18_2 [1, 3, -6] = true := by decide +kernel
theorem subd18_2_390 : subd18_2 [1, 3, -5] = true := by decide +kernel
theorem subd18_2_391 : subd18_2 [1, 3, -4] = true := by decide +kernel
theorem subd18_2_392 : subd18_2 [1, 3, -3] = true := by decide +kernel
theorem subd18_2_393 : subd18_2 [1, 3, -2] = true := by decide +kernel
theorem subd18_2_394 : subd18_2 [1, 3, -1] = true := by decide +kernel
theorem subd18_2_395 : subd18_2 [1, 3, 0] = true := by decide +kernel
theorem subd18_2_396 : subd18_2 [1, 3, 1] = true := by decide +kernel
theorem subd18_2_397 : subd18_2 [1, 3, 2] = true := by decide +kernel
theorem subd18_2_398 : subd18_2 [1, 3, 3] = true := by decide +kernel
theorem subd18_2_399 : subd18_2 [1, 3, 4] = true := by decide +kernel
theorem subd18_2_400 : subd18_2 [1, 3, 5] = true := by decide +kernel
theorem subd18_2_401 : subd18_2 [1, 3, 6] = true := by decide +kernel
theorem subd18_2_402 : subd18_2 [1, 3, 7] = true := by decide +kernel
theorem subd18_2_403 : subd18_2 [1, 4] = true := by decide +kernel
theorem subd18_2_404 : subd18_2 [1, 5] = true := by decide +kernel
theorem subd18_2_405 : subd18_2 [2, -5] = true := by decide +kernel
theorem subd18_2_406 : subd18_2 [2, -4] = true := by decide +kernel
theorem subd18_2_407 : subd18_2 [2, -3] = true := by decide +kernel
theorem subd18_2_408 : subd18_2 [2, -2] = true := by decide +kernel
theorem subd18_2_409 : subd18_2 [2, -1, -7] = true := by decide +kernel
theorem subd18_2_410 : subd18_2 [2, -1, -6] = true := by decide +kernel
theorem subd18_2_411 : subd18_2 [2, -1, -5] = true := by decide +kernel
theorem subd18_2_412 : subd18_2 [2, -1, -4] = true := by decide +kernel
theorem subd18_2_413 : subd18_2 [2, -1, -3] = true := by decide +kernel
theorem subd18_2_414 : subd18_2 [2, -1, -2] = true := by decide +kernel
theorem subd18_2_415 : subd18_2 [2, -1, -1] = true := by decide +kernel
theorem sbd18_2_12 : ∀ q ∈ blkd18_2_12, subd18_2 q = true := by
  unfold blkd18_2_12
  exact List.forall_mem_cons.2 ⟨subd18_2_384, List.forall_mem_cons.2 ⟨subd18_2_385, List.forall_mem_cons.2 ⟨subd18_2_386, List.forall_mem_cons.2 ⟨subd18_2_387, List.forall_mem_cons.2 ⟨subd18_2_388, List.forall_mem_cons.2 ⟨subd18_2_389, List.forall_mem_cons.2 ⟨subd18_2_390, List.forall_mem_cons.2 ⟨subd18_2_391, List.forall_mem_cons.2 ⟨subd18_2_392, List.forall_mem_cons.2 ⟨subd18_2_393, List.forall_mem_cons.2 ⟨subd18_2_394, List.forall_mem_cons.2 ⟨subd18_2_395, List.forall_mem_cons.2 ⟨subd18_2_396, List.forall_mem_cons.2 ⟨subd18_2_397, List.forall_mem_cons.2 ⟨subd18_2_398, List.forall_mem_cons.2 ⟨subd18_2_399, List.forall_mem_cons.2 ⟨subd18_2_400, List.forall_mem_cons.2 ⟨subd18_2_401, List.forall_mem_cons.2 ⟨subd18_2_402, List.forall_mem_cons.2 ⟨subd18_2_403, List.forall_mem_cons.2 ⟨subd18_2_404, List.forall_mem_cons.2 ⟨subd18_2_405, List.forall_mem_cons.2 ⟨subd18_2_406, List.forall_mem_cons.2 ⟨subd18_2_407, List.forall_mem_cons.2 ⟨subd18_2_408, List.forall_mem_cons.2 ⟨subd18_2_409, List.forall_mem_cons.2 ⟨subd18_2_410, List.forall_mem_cons.2 ⟨subd18_2_411, List.forall_mem_cons.2 ⟨subd18_2_412, List.forall_mem_cons.2 ⟨subd18_2_413, List.forall_mem_cons.2 ⟨subd18_2_414, List.forall_mem_cons.2 ⟨subd18_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_416 : subd18_2 [2, -1, 0] = true := by decide +kernel
theorem subd18_2_417 : subd18_2 [2, -1, 1] = true := by decide +kernel
theorem subd18_2_418 : subd18_2 [2, -1, 2] = true := by decide +kernel
theorem subd18_2_419 : subd18_2 [2, -1, 3] = true := by decide +kernel
theorem subd18_2_420 : subd18_2 [2, -1, 4] = true := by decide +kernel
theorem subd18_2_421 : subd18_2 [2, -1, 5] = true := by decide +kernel
theorem subd18_2_422 : subd18_2 [2, -1, 6] = true := by decide +kernel
theorem subd18_2_423 : subd18_2 [2, 0, -8] = true := by decide +kernel
theorem subd18_2_424 : subd18_2 [2, 0, -7] = true := by decide +kernel
theorem subd18_2_425 : subd18_2 [2, 0, -6] = true := by decide +kernel
theorem subd18_2_426 : subd18_2 [2, 0, -5] = true := by decide +kernel
theorem subd18_2_427 : subd18_2 [2, 0, -4] = true := by decide +kernel
theorem subd18_2_428 : subd18_2 [2, 0, -3] = true := by decide +kernel
theorem subd18_2_429 : subd18_2 [2, 0, -2] = true := by decide +kernel
theorem subd18_2_430 : subd18_2 [2, 0, -1] = true := by decide +kernel
theorem subd18_2_431 : subd18_2 [2, 0, 0] = true := by decide +kernel
theorem subd18_2_432 : subd18_2 [2, 0, 1] = true := by decide +kernel
theorem subd18_2_433 : subd18_2 [2, 0, 2] = true := by decide +kernel
theorem subd18_2_434 : subd18_2 [2, 0, 3] = true := by decide +kernel
theorem subd18_2_435 : subd18_2 [2, 0, 4] = true := by decide +kernel
theorem subd18_2_436 : subd18_2 [2, 0, 5] = true := by decide +kernel
theorem subd18_2_437 : subd18_2 [2, 0, 6] = true := by decide +kernel
theorem subd18_2_438 : subd18_2 [2, 0, 7] = true := by decide +kernel
theorem subd18_2_439 : subd18_2 [2, 1, -7] = true := by decide +kernel
theorem subd18_2_440 : subd18_2 [2, 1, -6] = true := by decide +kernel
theorem subd18_2_441 : subd18_2 [2, 1, -5] = true := by decide +kernel
theorem subd18_2_442 : subd18_2 [2, 1, -4] = true := by decide +kernel
theorem subd18_2_443 : subd18_2 [2, 1, -3] = true := by decide +kernel
theorem subd18_2_444 : subd18_2 [2, 1, -2] = true := by decide +kernel
theorem subd18_2_445 : subd18_2 [2, 1, -1] = true := by decide +kernel
theorem subd18_2_446 : subd18_2 [2, 1, 0] = true := by decide +kernel
theorem subd18_2_447 : subd18_2 [2, 1, 1] = true := by decide +kernel
theorem sbd18_2_13 : ∀ q ∈ blkd18_2_13, subd18_2 q = true := by
  unfold blkd18_2_13
  exact List.forall_mem_cons.2 ⟨subd18_2_416, List.forall_mem_cons.2 ⟨subd18_2_417, List.forall_mem_cons.2 ⟨subd18_2_418, List.forall_mem_cons.2 ⟨subd18_2_419, List.forall_mem_cons.2 ⟨subd18_2_420, List.forall_mem_cons.2 ⟨subd18_2_421, List.forall_mem_cons.2 ⟨subd18_2_422, List.forall_mem_cons.2 ⟨subd18_2_423, List.forall_mem_cons.2 ⟨subd18_2_424, List.forall_mem_cons.2 ⟨subd18_2_425, List.forall_mem_cons.2 ⟨subd18_2_426, List.forall_mem_cons.2 ⟨subd18_2_427, List.forall_mem_cons.2 ⟨subd18_2_428, List.forall_mem_cons.2 ⟨subd18_2_429, List.forall_mem_cons.2 ⟨subd18_2_430, List.forall_mem_cons.2 ⟨subd18_2_431, List.forall_mem_cons.2 ⟨subd18_2_432, List.forall_mem_cons.2 ⟨subd18_2_433, List.forall_mem_cons.2 ⟨subd18_2_434, List.forall_mem_cons.2 ⟨subd18_2_435, List.forall_mem_cons.2 ⟨subd18_2_436, List.forall_mem_cons.2 ⟨subd18_2_437, List.forall_mem_cons.2 ⟨subd18_2_438, List.forall_mem_cons.2 ⟨subd18_2_439, List.forall_mem_cons.2 ⟨subd18_2_440, List.forall_mem_cons.2 ⟨subd18_2_441, List.forall_mem_cons.2 ⟨subd18_2_442, List.forall_mem_cons.2 ⟨subd18_2_443, List.forall_mem_cons.2 ⟨subd18_2_444, List.forall_mem_cons.2 ⟨subd18_2_445, List.forall_mem_cons.2 ⟨subd18_2_446, List.forall_mem_cons.2 ⟨subd18_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_448 : subd18_2 [2, 1, 2] = true := by decide +kernel
theorem subd18_2_449 : subd18_2 [2, 1, 3] = true := by decide +kernel
theorem subd18_2_450 : subd18_2 [2, 1, 4] = true := by decide +kernel
theorem subd18_2_451 : subd18_2 [2, 1, 5] = true := by decide +kernel
theorem subd18_2_452 : subd18_2 [2, 1, 6] = true := by decide +kernel
theorem subd18_2_453 : subd18_2 [2, 1, 7] = true := by decide +kernel
theorem subd18_2_454 : subd18_2 [2, 2, -7] = true := by decide +kernel
theorem subd18_2_455 : subd18_2 [2, 2, -6] = true := by decide +kernel
theorem subd18_2_456 : subd18_2 [2, 2, -5] = true := by decide +kernel
theorem subd18_2_457 : subd18_2 [2, 2, -4] = true := by decide +kernel
theorem subd18_2_458 : subd18_2 [2, 2, -3] = true := by decide +kernel
theorem subd18_2_459 : subd18_2 [2, 2, -2] = true := by decide +kernel
theorem subd18_2_460 : subd18_2 [2, 2, -1] = true := by decide +kernel
theorem subd18_2_461 : subd18_2 [2, 2, 0] = true := by decide +kernel
theorem subd18_2_462 : subd18_2 [2, 2, 1] = true := by decide +kernel
theorem subd18_2_463 : subd18_2 [2, 2, 2] = true := by decide +kernel
theorem subd18_2_464 : subd18_2 [2, 2, 3] = true := by decide +kernel
theorem subd18_2_465 : subd18_2 [2, 2, 4] = true := by decide +kernel
theorem subd18_2_466 : subd18_2 [2, 2, 5] = true := by decide +kernel
theorem subd18_2_467 : subd18_2 [2, 2, 6] = true := by decide +kernel
theorem subd18_2_468 : subd18_2 [2, 2, 7] = true := by decide +kernel
theorem subd18_2_469 : subd18_2 [2, 3] = true := by decide +kernel
theorem subd18_2_470 : subd18_2 [2, 4] = true := by decide +kernel
theorem subd18_2_471 : subd18_2 [2, 5] = true := by decide +kernel
theorem subd18_2_472 : subd18_2 [3, -5] = true := by decide +kernel
theorem subd18_2_473 : subd18_2 [3, -4] = true := by decide +kernel
theorem subd18_2_474 : subd18_2 [3, -3] = true := by decide +kernel
theorem subd18_2_475 : subd18_2 [3, -2] = true := by decide +kernel
theorem subd18_2_476 : subd18_2 [3, -1] = true := by decide +kernel
theorem subd18_2_477 : subd18_2 [3, 0, -7] = true := by decide +kernel
theorem subd18_2_478 : subd18_2 [3, 0, -6] = true := by decide +kernel
theorem subd18_2_479 : subd18_2 [3, 0, -5] = true := by decide +kernel
theorem sbd18_2_14 : ∀ q ∈ blkd18_2_14, subd18_2 q = true := by
  unfold blkd18_2_14
  exact List.forall_mem_cons.2 ⟨subd18_2_448, List.forall_mem_cons.2 ⟨subd18_2_449, List.forall_mem_cons.2 ⟨subd18_2_450, List.forall_mem_cons.2 ⟨subd18_2_451, List.forall_mem_cons.2 ⟨subd18_2_452, List.forall_mem_cons.2 ⟨subd18_2_453, List.forall_mem_cons.2 ⟨subd18_2_454, List.forall_mem_cons.2 ⟨subd18_2_455, List.forall_mem_cons.2 ⟨subd18_2_456, List.forall_mem_cons.2 ⟨subd18_2_457, List.forall_mem_cons.2 ⟨subd18_2_458, List.forall_mem_cons.2 ⟨subd18_2_459, List.forall_mem_cons.2 ⟨subd18_2_460, List.forall_mem_cons.2 ⟨subd18_2_461, List.forall_mem_cons.2 ⟨subd18_2_462, List.forall_mem_cons.2 ⟨subd18_2_463, List.forall_mem_cons.2 ⟨subd18_2_464, List.forall_mem_cons.2 ⟨subd18_2_465, List.forall_mem_cons.2 ⟨subd18_2_466, List.forall_mem_cons.2 ⟨subd18_2_467, List.forall_mem_cons.2 ⟨subd18_2_468, List.forall_mem_cons.2 ⟨subd18_2_469, List.forall_mem_cons.2 ⟨subd18_2_470, List.forall_mem_cons.2 ⟨subd18_2_471, List.forall_mem_cons.2 ⟨subd18_2_472, List.forall_mem_cons.2 ⟨subd18_2_473, List.forall_mem_cons.2 ⟨subd18_2_474, List.forall_mem_cons.2 ⟨subd18_2_475, List.forall_mem_cons.2 ⟨subd18_2_476, List.forall_mem_cons.2 ⟨subd18_2_477, List.forall_mem_cons.2 ⟨subd18_2_478, List.forall_mem_cons.2 ⟨subd18_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_480 : subd18_2 [3, 0, -4] = true := by decide +kernel
theorem subd18_2_481 : subd18_2 [3, 0, -3] = true := by decide +kernel
theorem subd18_2_482 : subd18_2 [3, 0, -2] = true := by decide +kernel
theorem subd18_2_483 : subd18_2 [3, 0, -1] = true := by decide +kernel
theorem subd18_2_484 : subd18_2 [3, 0, 0] = true := by decide +kernel
theorem subd18_2_485 : subd18_2 [3, 0, 1] = true := by decide +kernel
theorem subd18_2_486 : subd18_2 [3, 0, 2] = true := by decide +kernel
theorem subd18_2_487 : subd18_2 [3, 0, 3] = true := by decide +kernel
theorem subd18_2_488 : subd18_2 [3, 0, 4] = true := by decide +kernel
theorem subd18_2_489 : subd18_2 [3, 0, 5] = true := by decide +kernel
theorem subd18_2_490 : subd18_2 [3, 0, 6] = true := by decide +kernel
theorem subd18_2_491 : subd18_2 [3, 1, -7] = true := by decide +kernel
theorem subd18_2_492 : subd18_2 [3, 1, -6] = true := by decide +kernel
theorem subd18_2_493 : subd18_2 [3, 1, -5] = true := by decide +kernel
theorem subd18_2_494 : subd18_2 [3, 1, -4] = true := by decide +kernel
theorem subd18_2_495 : subd18_2 [3, 1, -3] = true := by decide +kernel
theorem subd18_2_496 : subd18_2 [3, 1, -2] = true := by decide +kernel
theorem subd18_2_497 : subd18_2 [3, 1, -1] = true := by decide +kernel
theorem subd18_2_498 : subd18_2 [3, 1, 0] = true := by decide +kernel
theorem subd18_2_499 : subd18_2 [3, 1, 1] = true := by decide +kernel
theorem subd18_2_500 : subd18_2 [3, 1, 2] = true := by decide +kernel
theorem subd18_2_501 : subd18_2 [3, 1, 3] = true := by decide +kernel
theorem subd18_2_502 : subd18_2 [3, 1, 4] = true := by decide +kernel
theorem subd18_2_503 : subd18_2 [3, 1, 5] = true := by decide +kernel
theorem subd18_2_504 : subd18_2 [3, 1, 6] = true := by decide +kernel
theorem subd18_2_505 : subd18_2 [3, 1, 7] = true := by decide +kernel
theorem subd18_2_506 : subd18_2 [3, 2] = true := by decide +kernel
theorem subd18_2_507 : subd18_2 [3, 3] = true := by decide +kernel
theorem subd18_2_508 : subd18_2 [3, 4] = true := by decide +kernel
theorem subd18_2_509 : subd18_2 [3, 5] = true := by decide +kernel
theorem subd18_2_510 : subd18_2 [4, -4] = true := by decide +kernel
theorem subd18_2_511 : subd18_2 [4, -3] = true := by decide +kernel
theorem sbd18_2_15 : ∀ q ∈ blkd18_2_15, subd18_2 q = true := by
  unfold blkd18_2_15
  exact List.forall_mem_cons.2 ⟨subd18_2_480, List.forall_mem_cons.2 ⟨subd18_2_481, List.forall_mem_cons.2 ⟨subd18_2_482, List.forall_mem_cons.2 ⟨subd18_2_483, List.forall_mem_cons.2 ⟨subd18_2_484, List.forall_mem_cons.2 ⟨subd18_2_485, List.forall_mem_cons.2 ⟨subd18_2_486, List.forall_mem_cons.2 ⟨subd18_2_487, List.forall_mem_cons.2 ⟨subd18_2_488, List.forall_mem_cons.2 ⟨subd18_2_489, List.forall_mem_cons.2 ⟨subd18_2_490, List.forall_mem_cons.2 ⟨subd18_2_491, List.forall_mem_cons.2 ⟨subd18_2_492, List.forall_mem_cons.2 ⟨subd18_2_493, List.forall_mem_cons.2 ⟨subd18_2_494, List.forall_mem_cons.2 ⟨subd18_2_495, List.forall_mem_cons.2 ⟨subd18_2_496, List.forall_mem_cons.2 ⟨subd18_2_497, List.forall_mem_cons.2 ⟨subd18_2_498, List.forall_mem_cons.2 ⟨subd18_2_499, List.forall_mem_cons.2 ⟨subd18_2_500, List.forall_mem_cons.2 ⟨subd18_2_501, List.forall_mem_cons.2 ⟨subd18_2_502, List.forall_mem_cons.2 ⟨subd18_2_503, List.forall_mem_cons.2 ⟨subd18_2_504, List.forall_mem_cons.2 ⟨subd18_2_505, List.forall_mem_cons.2 ⟨subd18_2_506, List.forall_mem_cons.2 ⟨subd18_2_507, List.forall_mem_cons.2 ⟨subd18_2_508, List.forall_mem_cons.2 ⟨subd18_2_509, List.forall_mem_cons.2 ⟨subd18_2_510, List.forall_mem_cons.2 ⟨subd18_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_512 : subd18_2 [4, -2] = true := by decide +kernel
theorem subd18_2_513 : subd18_2 [4, -1] = true := by decide +kernel
theorem subd18_2_514 : subd18_2 [4, 0] = true := by decide +kernel
theorem subd18_2_515 : subd18_2 [4, 1] = true := by decide +kernel
theorem subd18_2_516 : subd18_2 [4, 2] = true := by decide +kernel
theorem subd18_2_517 : subd18_2 [4, 3] = true := by decide +kernel
theorem subd18_2_518 : subd18_2 [4, 4] = true := by decide +kernel
theorem subd18_2_519 : subd18_2 [4, 5] = true := by decide +kernel
theorem subd18_2_520 : subd18_2 [5, -3] = true := by decide +kernel
theorem subd18_2_521 : subd18_2 [5, -2] = true := by decide +kernel
theorem subd18_2_522 : subd18_2 [5, -1] = true := by decide +kernel
theorem subd18_2_523 : subd18_2 [5, 0] = true := by decide +kernel
theorem subd18_2_524 : subd18_2 [5, 1] = true := by decide +kernel
theorem subd18_2_525 : subd18_2 [5, 2] = true := by decide +kernel
theorem subd18_2_526 : subd18_2 [5, 3] = true := by decide +kernel
theorem subd18_2_527 : subd18_2 [5, 4] = true := by decide +kernel
theorem subd18_2_528 : subd18_2 [6] = true := by decide +kernel
theorem sbd18_2_16 : ∀ q ∈ blkd18_2_16, subd18_2 q = true := by
  unfold blkd18_2_16
  exact List.forall_mem_cons.2 ⟨subd18_2_512, List.forall_mem_cons.2 ⟨subd18_2_513, List.forall_mem_cons.2 ⟨subd18_2_514, List.forall_mem_cons.2 ⟨subd18_2_515, List.forall_mem_cons.2 ⟨subd18_2_516, List.forall_mem_cons.2 ⟨subd18_2_517, List.forall_mem_cons.2 ⟨subd18_2_518, List.forall_mem_cons.2 ⟨subd18_2_519, List.forall_mem_cons.2 ⟨subd18_2_520, List.forall_mem_cons.2 ⟨subd18_2_521, List.forall_mem_cons.2 ⟨subd18_2_522, List.forall_mem_cons.2 ⟨subd18_2_523, List.forall_mem_cons.2 ⟨subd18_2_524, List.forall_mem_cons.2 ⟨subd18_2_525, List.forall_mem_cons.2 ⟨subd18_2_526, List.forall_mem_cons.2 ⟨subd18_2_527, List.forall_mem_cons.2 ⟨subd18_2_528, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd18_3 : ldCheck G d18_3.U d18_3.ms ldd18_3 = true := by decide +kernel
theorem pre_okd18_3 : subPre G cell18 d18_3 = true := by decide +kernel
theorem subd18_3_0 : subd18_3 [-7] = true := by decide +kernel
theorem subd18_3_1 : subd18_3 [-6, -5] = true := by decide +kernel
theorem subd18_3_2 : subd18_3 [-6, -4] = true := by decide +kernel
theorem subd18_3_3 : subd18_3 [-6, -3] = true := by decide +kernel
theorem subd18_3_4 : subd18_3 [-6, -2] = true := by decide +kernel
theorem subd18_3_5 : subd18_3 [-6, -1] = true := by decide +kernel
theorem subd18_3_6 : subd18_3 [-6, 0] = true := by decide +kernel
theorem subd18_3_7 : subd18_3 [-6, 1] = true := by decide +kernel
theorem subd18_3_8 : subd18_3 [-6, 2] = true := by decide +kernel
theorem subd18_3_9 : subd18_3 [-6, 3] = true := by decide +kernel
theorem subd18_3_10 : subd18_3 [-6, 4] = true := by decide +kernel
theorem subd18_3_11 : subd18_3 [-5, -6] = true := by decide +kernel
theorem subd18_3_12 : subd18_3 [-5, -5] = true := by decide +kernel
theorem subd18_3_13 : subd18_3 [-5, -4] = true := by decide +kernel
theorem subd18_3_14 : subd18_3 [-5, -3] = true := by decide +kernel
theorem subd18_3_15 : subd18_3 [-5, -2] = true := by decide +kernel
theorem subd18_3_16 : subd18_3 [-5, -1] = true := by decide +kernel
theorem subd18_3_17 : subd18_3 [-5, 0] = true := by decide +kernel
theorem subd18_3_18 : subd18_3 [-5, 1] = true := by decide +kernel
theorem subd18_3_19 : subd18_3 [-5, 2] = true := by decide +kernel
theorem subd18_3_20 : subd18_3 [-5, 3] = true := by decide +kernel
theorem subd18_3_21 : subd18_3 [-5, 4] = true := by decide +kernel
theorem subd18_3_22 : subd18_3 [-5, 5] = true := by decide +kernel
theorem subd18_3_23 : subd18_3 [-4, -7] = true := by decide +kernel
theorem subd18_3_24 : subd18_3 [-4, -6] = true := by decide +kernel
theorem subd18_3_25 : subd18_3 [-4, -5] = true := by decide +kernel
theorem subd18_3_26 : subd18_3 [-4, -4] = true := by decide +kernel
theorem subd18_3_27 : subd18_3 [-4, -3] = true := by decide +kernel
theorem subd18_3_28 : subd18_3 [-4, -2] = true := by decide +kernel
theorem subd18_3_29 : subd18_3 [-4, -1] = true := by decide +kernel
theorem subd18_3_30 : subd18_3 [-4, 0] = true := by decide +kernel
theorem subd18_3_31 : subd18_3 [-4, 1] = true := by decide +kernel
theorem sbd18_3_0 : ∀ q ∈ blkd18_3_0, subd18_3 q = true := by
  unfold blkd18_3_0
  exact List.forall_mem_cons.2 ⟨subd18_3_0, List.forall_mem_cons.2 ⟨subd18_3_1, List.forall_mem_cons.2 ⟨subd18_3_2, List.forall_mem_cons.2 ⟨subd18_3_3, List.forall_mem_cons.2 ⟨subd18_3_4, List.forall_mem_cons.2 ⟨subd18_3_5, List.forall_mem_cons.2 ⟨subd18_3_6, List.forall_mem_cons.2 ⟨subd18_3_7, List.forall_mem_cons.2 ⟨subd18_3_8, List.forall_mem_cons.2 ⟨subd18_3_9, List.forall_mem_cons.2 ⟨subd18_3_10, List.forall_mem_cons.2 ⟨subd18_3_11, List.forall_mem_cons.2 ⟨subd18_3_12, List.forall_mem_cons.2 ⟨subd18_3_13, List.forall_mem_cons.2 ⟨subd18_3_14, List.forall_mem_cons.2 ⟨subd18_3_15, List.forall_mem_cons.2 ⟨subd18_3_16, List.forall_mem_cons.2 ⟨subd18_3_17, List.forall_mem_cons.2 ⟨subd18_3_18, List.forall_mem_cons.2 ⟨subd18_3_19, List.forall_mem_cons.2 ⟨subd18_3_20, List.forall_mem_cons.2 ⟨subd18_3_21, List.forall_mem_cons.2 ⟨subd18_3_22, List.forall_mem_cons.2 ⟨subd18_3_23, List.forall_mem_cons.2 ⟨subd18_3_24, List.forall_mem_cons.2 ⟨subd18_3_25, List.forall_mem_cons.2 ⟨subd18_3_26, List.forall_mem_cons.2 ⟨subd18_3_27, List.forall_mem_cons.2 ⟨subd18_3_28, List.forall_mem_cons.2 ⟨subd18_3_29, List.forall_mem_cons.2 ⟨subd18_3_30, List.forall_mem_cons.2 ⟨subd18_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
