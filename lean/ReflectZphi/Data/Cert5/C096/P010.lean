import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_1_384 : subd7_1 [0, 3, -6] = true := by decide +kernel
theorem subd7_1_385 : subd7_1 [0, 3, -5] = true := by decide +kernel
theorem subd7_1_386 : subd7_1 [0, 3, -4] = true := by decide +kernel
theorem subd7_1_387 : subd7_1 [0, 3, -3] = true := by decide +kernel
theorem subd7_1_388 : subd7_1 [0, 3, -2] = true := by decide +kernel
theorem subd7_1_389 : subd7_1 [0, 3, -1] = true := by decide +kernel
theorem subd7_1_390 : subd7_1 [0, 3, 0] = true := by decide +kernel
theorem subd7_1_391 : subd7_1 [0, 3, 1] = true := by decide +kernel
theorem subd7_1_392 : subd7_1 [0, 3, 2] = true := by decide +kernel
theorem subd7_1_393 : subd7_1 [0, 3, 3] = true := by decide +kernel
theorem subd7_1_394 : subd7_1 [0, 3, 4] = true := by decide +kernel
theorem subd7_1_395 : subd7_1 [0, 3, 5] = true := by decide +kernel
theorem subd7_1_396 : subd7_1 [0, 4] = true := by decide +kernel
theorem subd7_1_397 : subd7_1 [0, 5] = true := by decide +kernel
theorem subd7_1_398 : subd7_1 [1, -7] = true := by decide +kernel
theorem subd7_1_399 : subd7_1 [1, -6] = true := by decide +kernel
theorem subd7_1_400 : subd7_1 [1, -5] = true := by decide +kernel
theorem subd7_1_401 : subd7_1 [1, -4] = true := by decide +kernel
theorem subd7_1_402 : subd7_1 [1, -3, -6] = true := by decide +kernel
theorem subd7_1_403 : subd7_1 [1, -3, -5] = true := by decide +kernel
theorem subd7_1_404 : subd7_1 [1, -3, -4] = true := by decide +kernel
theorem subd7_1_405 : subd7_1 [1, -3, -3] = true := by decide +kernel
theorem subd7_1_406 : subd7_1 [1, -3, -2] = true := by decide +kernel
theorem subd7_1_407 : subd7_1 [1, -3, -1] = true := by decide +kernel
theorem subd7_1_408 : subd7_1 [1, -3, 0] = true := by decide +kernel
theorem subd7_1_409 : subd7_1 [1, -3, 1] = true := by decide +kernel
theorem subd7_1_410 : subd7_1 [1, -3, 2] = true := by decide +kernel
theorem subd7_1_411 : subd7_1 [1, -3, 3] = true := by decide +kernel
theorem subd7_1_412 : subd7_1 [1, -3, 4] = true := by decide +kernel
theorem subd7_1_413 : subd7_1 [1, -3, 5] = true := by decide +kernel
theorem subd7_1_414 : subd7_1 [1, -3, 6] = true := by decide +kernel
theorem subd7_1_415 : subd7_1 [1, -3, 7] = true := by decide +kernel
theorem sbd7_1_12 : ∀ q ∈ blkd7_1_12, subd7_1 q = true := by
  unfold blkd7_1_12
  exact List.forall_mem_cons.2 ⟨subd7_1_384, List.forall_mem_cons.2 ⟨subd7_1_385, List.forall_mem_cons.2 ⟨subd7_1_386, List.forall_mem_cons.2 ⟨subd7_1_387, List.forall_mem_cons.2 ⟨subd7_1_388, List.forall_mem_cons.2 ⟨subd7_1_389, List.forall_mem_cons.2 ⟨subd7_1_390, List.forall_mem_cons.2 ⟨subd7_1_391, List.forall_mem_cons.2 ⟨subd7_1_392, List.forall_mem_cons.2 ⟨subd7_1_393, List.forall_mem_cons.2 ⟨subd7_1_394, List.forall_mem_cons.2 ⟨subd7_1_395, List.forall_mem_cons.2 ⟨subd7_1_396, List.forall_mem_cons.2 ⟨subd7_1_397, List.forall_mem_cons.2 ⟨subd7_1_398, List.forall_mem_cons.2 ⟨subd7_1_399, List.forall_mem_cons.2 ⟨subd7_1_400, List.forall_mem_cons.2 ⟨subd7_1_401, List.forall_mem_cons.2 ⟨subd7_1_402, List.forall_mem_cons.2 ⟨subd7_1_403, List.forall_mem_cons.2 ⟨subd7_1_404, List.forall_mem_cons.2 ⟨subd7_1_405, List.forall_mem_cons.2 ⟨subd7_1_406, List.forall_mem_cons.2 ⟨subd7_1_407, List.forall_mem_cons.2 ⟨subd7_1_408, List.forall_mem_cons.2 ⟨subd7_1_409, List.forall_mem_cons.2 ⟨subd7_1_410, List.forall_mem_cons.2 ⟨subd7_1_411, List.forall_mem_cons.2 ⟨subd7_1_412, List.forall_mem_cons.2 ⟨subd7_1_413, List.forall_mem_cons.2 ⟨subd7_1_414, List.forall_mem_cons.2 ⟨subd7_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_416 : subd7_1 [1, -2, -7] = true := by decide +kernel
theorem subd7_1_417 : subd7_1 [1, -2, -6] = true := by decide +kernel
theorem subd7_1_418 : subd7_1 [1, -2, -5] = true := by decide +kernel
theorem subd7_1_419 : subd7_1 [1, -2, -4] = true := by decide +kernel
theorem subd7_1_420 : subd7_1 [1, -2, -3] = true := by decide +kernel
theorem subd7_1_421 : subd7_1 [1, -2, -2] = true := by decide +kernel
theorem subd7_1_422 : subd7_1 [1, -2, -1] = true := by decide +kernel
theorem subd7_1_423 : subd7_1 [1, -2, 0] = true := by decide +kernel
theorem subd7_1_424 : subd7_1 [1, -2, 1] = true := by decide +kernel
theorem subd7_1_425 : subd7_1 [1, -2, 2] = true := by decide +kernel
theorem subd7_1_426 : subd7_1 [1, -2, 3] = true := by decide +kernel
theorem subd7_1_427 : subd7_1 [1, -2, 4] = true := by decide +kernel
theorem subd7_1_428 : subd7_1 [1, -2, 5] = true := by decide +kernel
theorem subd7_1_429 : subd7_1 [1, -2, 6] = true := by decide +kernel
theorem subd7_1_430 : subd7_1 [1, -2, 7] = true := by decide +kernel
theorem subd7_1_431 : subd7_1 [1, -1, -8] = true := by decide +kernel
theorem subd7_1_432 : subd7_1 [1, -1, -7] = true := by decide +kernel
theorem subd7_1_433 : subd7_1 [1, -1, -6] = true := by decide +kernel
theorem subd7_1_434 : subd7_1 [1, -1, -5] = true := by decide +kernel
theorem subd7_1_435 : subd7_1 [1, -1, -4] = true := by decide +kernel
theorem subd7_1_436 : subd7_1 [1, -1, -3] = true := by decide +kernel
theorem subd7_1_437 : subd7_1 [1, -1, -2] = true := by decide +kernel
theorem subd7_1_438 : subd7_1 [1, -1, -1] = true := by decide +kernel
theorem subd7_1_439 : subd7_1 [1, -1, 0] = true := by decide +kernel
theorem subd7_1_440 : subd7_1 [1, -1, 1] = true := by decide +kernel
theorem subd7_1_441 : subd7_1 [1, -1, 2] = true := by decide +kernel
theorem subd7_1_442 : subd7_1 [1, -1, 3] = true := by decide +kernel
theorem subd7_1_443 : subd7_1 [1, -1, 4] = true := by decide +kernel
theorem subd7_1_444 : subd7_1 [1, -1, 5] = true := by decide +kernel
theorem subd7_1_445 : subd7_1 [1, -1, 6] = true := by decide +kernel
theorem subd7_1_446 : subd7_1 [1, -1, 7] = true := by decide +kernel
theorem subd7_1_447 : subd7_1 [1, 0, -8] = true := by decide +kernel
theorem sbd7_1_13 : ∀ q ∈ blkd7_1_13, subd7_1 q = true := by
  unfold blkd7_1_13
  exact List.forall_mem_cons.2 ⟨subd7_1_416, List.forall_mem_cons.2 ⟨subd7_1_417, List.forall_mem_cons.2 ⟨subd7_1_418, List.forall_mem_cons.2 ⟨subd7_1_419, List.forall_mem_cons.2 ⟨subd7_1_420, List.forall_mem_cons.2 ⟨subd7_1_421, List.forall_mem_cons.2 ⟨subd7_1_422, List.forall_mem_cons.2 ⟨subd7_1_423, List.forall_mem_cons.2 ⟨subd7_1_424, List.forall_mem_cons.2 ⟨subd7_1_425, List.forall_mem_cons.2 ⟨subd7_1_426, List.forall_mem_cons.2 ⟨subd7_1_427, List.forall_mem_cons.2 ⟨subd7_1_428, List.forall_mem_cons.2 ⟨subd7_1_429, List.forall_mem_cons.2 ⟨subd7_1_430, List.forall_mem_cons.2 ⟨subd7_1_431, List.forall_mem_cons.2 ⟨subd7_1_432, List.forall_mem_cons.2 ⟨subd7_1_433, List.forall_mem_cons.2 ⟨subd7_1_434, List.forall_mem_cons.2 ⟨subd7_1_435, List.forall_mem_cons.2 ⟨subd7_1_436, List.forall_mem_cons.2 ⟨subd7_1_437, List.forall_mem_cons.2 ⟨subd7_1_438, List.forall_mem_cons.2 ⟨subd7_1_439, List.forall_mem_cons.2 ⟨subd7_1_440, List.forall_mem_cons.2 ⟨subd7_1_441, List.forall_mem_cons.2 ⟨subd7_1_442, List.forall_mem_cons.2 ⟨subd7_1_443, List.forall_mem_cons.2 ⟨subd7_1_444, List.forall_mem_cons.2 ⟨subd7_1_445, List.forall_mem_cons.2 ⟨subd7_1_446, List.forall_mem_cons.2 ⟨subd7_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_448 : subd7_1 [1, 0, -7] = true := by decide +kernel
theorem subd7_1_449 : subd7_1 [1, 0, -6] = true := by decide +kernel
theorem subd7_1_450 : subd7_1 [1, 0, -5] = true := by decide +kernel
theorem subd7_1_451 : subd7_1 [1, 0, -4] = true := by decide +kernel
theorem subd7_1_452 : subd7_1 [1, 0, -3] = true := by decide +kernel
theorem subd7_1_453 : subd7_1 [1, 0, -2] = true := by decide +kernel
theorem subd7_1_454 : subd7_1 [1, 0, -1] = true := by decide +kernel
theorem subd7_1_455 : subd7_1 [1, 0, 0] = true := by decide +kernel
theorem subd7_1_456 : subd7_1 [1, 0, 1] = true := by decide +kernel
theorem subd7_1_457 : subd7_1 [1, 0, 2] = true := by decide +kernel
theorem subd7_1_458 : subd7_1 [1, 0, 3] = true := by decide +kernel
theorem subd7_1_459 : subd7_1 [1, 0, 4] = true := by decide +kernel
theorem subd7_1_460 : subd7_1 [1, 0, 5] = true := by decide +kernel
theorem subd7_1_461 : subd7_1 [1, 0, 6] = true := by decide +kernel
theorem subd7_1_462 : subd7_1 [1, 0, 7] = true := by decide +kernel
theorem subd7_1_463 : subd7_1 [1, 1, -8] = true := by decide +kernel
theorem subd7_1_464 : subd7_1 [1, 1, -7] = true := by decide +kernel
theorem subd7_1_465 : subd7_1 [1, 1, -6] = true := by decide +kernel
theorem subd7_1_466 : subd7_1 [1, 1, -5] = true := by decide +kernel
theorem subd7_1_467 : subd7_1 [1, 1, -4] = true := by decide +kernel
theorem subd7_1_468 : subd7_1 [1, 1, -3] = true := by decide +kernel
theorem subd7_1_469 : subd7_1 [1, 1, -2] = true := by decide +kernel
theorem subd7_1_470 : subd7_1 [1, 1, -1] = true := by decide +kernel
theorem subd7_1_471 : subd7_1 [1, 1, 0] = true := by decide +kernel
theorem subd7_1_472 : subd7_1 [1, 1, 1] = true := by decide +kernel
theorem subd7_1_473 : subd7_1 [1, 1, 2] = true := by decide +kernel
theorem subd7_1_474 : subd7_1 [1, 1, 3] = true := by decide +kernel
theorem subd7_1_475 : subd7_1 [1, 1, 4] = true := by decide +kernel
theorem subd7_1_476 : subd7_1 [1, 1, 5] = true := by decide +kernel
theorem subd7_1_477 : subd7_1 [1, 1, 6] = true := by decide +kernel
theorem subd7_1_478 : subd7_1 [1, 2, -8] = true := by decide +kernel
theorem subd7_1_479 : subd7_1 [1, 2, -7] = true := by decide +kernel
theorem sbd7_1_14 : ∀ q ∈ blkd7_1_14, subd7_1 q = true := by
  unfold blkd7_1_14
  exact List.forall_mem_cons.2 ⟨subd7_1_448, List.forall_mem_cons.2 ⟨subd7_1_449, List.forall_mem_cons.2 ⟨subd7_1_450, List.forall_mem_cons.2 ⟨subd7_1_451, List.forall_mem_cons.2 ⟨subd7_1_452, List.forall_mem_cons.2 ⟨subd7_1_453, List.forall_mem_cons.2 ⟨subd7_1_454, List.forall_mem_cons.2 ⟨subd7_1_455, List.forall_mem_cons.2 ⟨subd7_1_456, List.forall_mem_cons.2 ⟨subd7_1_457, List.forall_mem_cons.2 ⟨subd7_1_458, List.forall_mem_cons.2 ⟨subd7_1_459, List.forall_mem_cons.2 ⟨subd7_1_460, List.forall_mem_cons.2 ⟨subd7_1_461, List.forall_mem_cons.2 ⟨subd7_1_462, List.forall_mem_cons.2 ⟨subd7_1_463, List.forall_mem_cons.2 ⟨subd7_1_464, List.forall_mem_cons.2 ⟨subd7_1_465, List.forall_mem_cons.2 ⟨subd7_1_466, List.forall_mem_cons.2 ⟨subd7_1_467, List.forall_mem_cons.2 ⟨subd7_1_468, List.forall_mem_cons.2 ⟨subd7_1_469, List.forall_mem_cons.2 ⟨subd7_1_470, List.forall_mem_cons.2 ⟨subd7_1_471, List.forall_mem_cons.2 ⟨subd7_1_472, List.forall_mem_cons.2 ⟨subd7_1_473, List.forall_mem_cons.2 ⟨subd7_1_474, List.forall_mem_cons.2 ⟨subd7_1_475, List.forall_mem_cons.2 ⟨subd7_1_476, List.forall_mem_cons.2 ⟨subd7_1_477, List.forall_mem_cons.2 ⟨subd7_1_478, List.forall_mem_cons.2 ⟨subd7_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_480 : subd7_1 [1, 2, -6] = true := by decide +kernel
theorem subd7_1_481 : subd7_1 [1, 2, -5] = true := by decide +kernel
theorem subd7_1_482 : subd7_1 [1, 2, -4] = true := by decide +kernel
theorem subd7_1_483 : subd7_1 [1, 2, -3] = true := by decide +kernel
theorem subd7_1_484 : subd7_1 [1, 2, -2] = true := by decide +kernel
theorem subd7_1_485 : subd7_1 [1, 2, -1] = true := by decide +kernel
theorem subd7_1_486 : subd7_1 [1, 2, 0] = true := by decide +kernel
theorem subd7_1_487 : subd7_1 [1, 2, 1] = true := by decide +kernel
theorem subd7_1_488 : subd7_1 [1, 2, 2] = true := by decide +kernel
theorem subd7_1_489 : subd7_1 [1, 2, 3] = true := by decide +kernel
theorem subd7_1_490 : subd7_1 [1, 2, 4] = true := by decide +kernel
theorem subd7_1_491 : subd7_1 [1, 2, 5] = true := by decide +kernel
theorem subd7_1_492 : subd7_1 [1, 2, 6] = true := by decide +kernel
theorem subd7_1_493 : subd7_1 [1, 3, -8] = true := by decide +kernel
theorem subd7_1_494 : subd7_1 [1, 3, -7] = true := by decide +kernel
theorem subd7_1_495 : subd7_1 [1, 3, -6] = true := by decide +kernel
theorem subd7_1_496 : subd7_1 [1, 3, -5] = true := by decide +kernel
theorem subd7_1_497 : subd7_1 [1, 3, -4] = true := by decide +kernel
theorem subd7_1_498 : subd7_1 [1, 3, -3] = true := by decide +kernel
theorem subd7_1_499 : subd7_1 [1, 3, -2] = true := by decide +kernel
theorem subd7_1_500 : subd7_1 [1, 3, -1] = true := by decide +kernel
theorem subd7_1_501 : subd7_1 [1, 3, 0] = true := by decide +kernel
theorem subd7_1_502 : subd7_1 [1, 3, 1] = true := by decide +kernel
theorem subd7_1_503 : subd7_1 [1, 3, 2] = true := by decide +kernel
theorem subd7_1_504 : subd7_1 [1, 3, 3] = true := by decide +kernel
theorem subd7_1_505 : subd7_1 [1, 3, 4] = true := by decide +kernel
theorem subd7_1_506 : subd7_1 [1, 4] = true := by decide +kernel
theorem subd7_1_507 : subd7_1 [1, 5] = true := by decide +kernel
theorem subd7_1_508 : subd7_1 [2, -6] = true := by decide +kernel
theorem subd7_1_509 : subd7_1 [2, -5] = true := by decide +kernel
theorem subd7_1_510 : subd7_1 [2, -4] = true := by decide +kernel
theorem subd7_1_511 : subd7_1 [2, -3, -6] = true := by decide +kernel
theorem sbd7_1_15 : ∀ q ∈ blkd7_1_15, subd7_1 q = true := by
  unfold blkd7_1_15
  exact List.forall_mem_cons.2 ⟨subd7_1_480, List.forall_mem_cons.2 ⟨subd7_1_481, List.forall_mem_cons.2 ⟨subd7_1_482, List.forall_mem_cons.2 ⟨subd7_1_483, List.forall_mem_cons.2 ⟨subd7_1_484, List.forall_mem_cons.2 ⟨subd7_1_485, List.forall_mem_cons.2 ⟨subd7_1_486, List.forall_mem_cons.2 ⟨subd7_1_487, List.forall_mem_cons.2 ⟨subd7_1_488, List.forall_mem_cons.2 ⟨subd7_1_489, List.forall_mem_cons.2 ⟨subd7_1_490, List.forall_mem_cons.2 ⟨subd7_1_491, List.forall_mem_cons.2 ⟨subd7_1_492, List.forall_mem_cons.2 ⟨subd7_1_493, List.forall_mem_cons.2 ⟨subd7_1_494, List.forall_mem_cons.2 ⟨subd7_1_495, List.forall_mem_cons.2 ⟨subd7_1_496, List.forall_mem_cons.2 ⟨subd7_1_497, List.forall_mem_cons.2 ⟨subd7_1_498, List.forall_mem_cons.2 ⟨subd7_1_499, List.forall_mem_cons.2 ⟨subd7_1_500, List.forall_mem_cons.2 ⟨subd7_1_501, List.forall_mem_cons.2 ⟨subd7_1_502, List.forall_mem_cons.2 ⟨subd7_1_503, List.forall_mem_cons.2 ⟨subd7_1_504, List.forall_mem_cons.2 ⟨subd7_1_505, List.forall_mem_cons.2 ⟨subd7_1_506, List.forall_mem_cons.2 ⟨subd7_1_507, List.forall_mem_cons.2 ⟨subd7_1_508, List.forall_mem_cons.2 ⟨subd7_1_509, List.forall_mem_cons.2 ⟨subd7_1_510, List.forall_mem_cons.2 ⟨subd7_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_512 : subd7_1 [2, -3, -5] = true := by decide +kernel
theorem subd7_1_513 : subd7_1 [2, -3, -4] = true := by decide +kernel
theorem subd7_1_514 : subd7_1 [2, -3, -3] = true := by decide +kernel
theorem subd7_1_515 : subd7_1 [2, -3, -2] = true := by decide +kernel
theorem subd7_1_516 : subd7_1 [2, -3, -1] = true := by decide +kernel
theorem subd7_1_517 : subd7_1 [2, -3, 0] = true := by decide +kernel
theorem subd7_1_518 : subd7_1 [2, -3, 1] = true := by decide +kernel
theorem subd7_1_519 : subd7_1 [2, -3, 2] = true := by decide +kernel
theorem subd7_1_520 : subd7_1 [2, -3, 3] = true := by decide +kernel
theorem subd7_1_521 : subd7_1 [2, -3, 4] = true := by decide +kernel
theorem subd7_1_522 : subd7_1 [2, -3, 5] = true := by decide +kernel
theorem subd7_1_523 : subd7_1 [2, -3, 6] = true := by decide +kernel
theorem subd7_1_524 : subd7_1 [2, -3, 7] = true := by decide +kernel
theorem subd7_1_525 : subd7_1 [2, -2, -7] = true := by decide +kernel
theorem subd7_1_526 : subd7_1 [2, -2, -6] = true := by decide +kernel
theorem subd7_1_527 : subd7_1 [2, -2, -5] = true := by decide +kernel
theorem subd7_1_528 : subd7_1 [2, -2, -4] = true := by decide +kernel
theorem subd7_1_529 : subd7_1 [2, -2, -3] = true := by decide +kernel
theorem subd7_1_530 : subd7_1 [2, -2, -2] = true := by decide +kernel
theorem subd7_1_531 : subd7_1 [2, -2, -1] = true := by decide +kernel
theorem subd7_1_532 : subd7_1 [2, -2, 0] = true := by decide +kernel
theorem subd7_1_533 : subd7_1 [2, -2, 1] = true := by decide +kernel
theorem subd7_1_534 : subd7_1 [2, -2, 2] = true := by decide +kernel
theorem subd7_1_535 : subd7_1 [2, -2, 3] = true := by decide +kernel
theorem subd7_1_536 : subd7_1 [2, -2, 4] = true := by decide +kernel
theorem subd7_1_537 : subd7_1 [2, -2, 5] = true := by decide +kernel
theorem subd7_1_538 : subd7_1 [2, -2, 6] = true := by decide +kernel
theorem subd7_1_539 : subd7_1 [2, -2, 7] = true := by decide +kernel
theorem subd7_1_540 : subd7_1 [2, -1, -7] = true := by decide +kernel
theorem subd7_1_541 : subd7_1 [2, -1, -6] = true := by decide +kernel
theorem subd7_1_542 : subd7_1 [2, -1, -5] = true := by decide +kernel
theorem subd7_1_543 : subd7_1 [2, -1, -4] = true := by decide +kernel
theorem sbd7_1_16 : ∀ q ∈ blkd7_1_16, subd7_1 q = true := by
  unfold blkd7_1_16
  exact List.forall_mem_cons.2 ⟨subd7_1_512, List.forall_mem_cons.2 ⟨subd7_1_513, List.forall_mem_cons.2 ⟨subd7_1_514, List.forall_mem_cons.2 ⟨subd7_1_515, List.forall_mem_cons.2 ⟨subd7_1_516, List.forall_mem_cons.2 ⟨subd7_1_517, List.forall_mem_cons.2 ⟨subd7_1_518, List.forall_mem_cons.2 ⟨subd7_1_519, List.forall_mem_cons.2 ⟨subd7_1_520, List.forall_mem_cons.2 ⟨subd7_1_521, List.forall_mem_cons.2 ⟨subd7_1_522, List.forall_mem_cons.2 ⟨subd7_1_523, List.forall_mem_cons.2 ⟨subd7_1_524, List.forall_mem_cons.2 ⟨subd7_1_525, List.forall_mem_cons.2 ⟨subd7_1_526, List.forall_mem_cons.2 ⟨subd7_1_527, List.forall_mem_cons.2 ⟨subd7_1_528, List.forall_mem_cons.2 ⟨subd7_1_529, List.forall_mem_cons.2 ⟨subd7_1_530, List.forall_mem_cons.2 ⟨subd7_1_531, List.forall_mem_cons.2 ⟨subd7_1_532, List.forall_mem_cons.2 ⟨subd7_1_533, List.forall_mem_cons.2 ⟨subd7_1_534, List.forall_mem_cons.2 ⟨subd7_1_535, List.forall_mem_cons.2 ⟨subd7_1_536, List.forall_mem_cons.2 ⟨subd7_1_537, List.forall_mem_cons.2 ⟨subd7_1_538, List.forall_mem_cons.2 ⟨subd7_1_539, List.forall_mem_cons.2 ⟨subd7_1_540, List.forall_mem_cons.2 ⟨subd7_1_541, List.forall_mem_cons.2 ⟨subd7_1_542, List.forall_mem_cons.2 ⟨subd7_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_544 : subd7_1 [2, -1, -3] = true := by decide +kernel
theorem subd7_1_545 : subd7_1 [2, -1, -2] = true := by decide +kernel
theorem subd7_1_546 : subd7_1 [2, -1, -1] = true := by decide +kernel
theorem subd7_1_547 : subd7_1 [2, -1, 0] = true := by decide +kernel
theorem subd7_1_548 : subd7_1 [2, -1, 1] = true := by decide +kernel
theorem subd7_1_549 : subd7_1 [2, -1, 2] = true := by decide +kernel
theorem subd7_1_550 : subd7_1 [2, -1, 3] = true := by decide +kernel
theorem subd7_1_551 : subd7_1 [2, -1, 4] = true := by decide +kernel
theorem subd7_1_552 : subd7_1 [2, -1, 5] = true := by decide +kernel
theorem subd7_1_553 : subd7_1 [2, -1, 6] = true := by decide +kernel
theorem subd7_1_554 : subd7_1 [2, -1, 7] = true := by decide +kernel
theorem subd7_1_555 : subd7_1 [2, 0, -8] = true := by decide +kernel
theorem subd7_1_556 : subd7_1 [2, 0, -7] = true := by decide +kernel
theorem subd7_1_557 : subd7_1 [2, 0, -6] = true := by decide +kernel
theorem subd7_1_558 : subd7_1 [2, 0, -5] = true := by decide +kernel
theorem subd7_1_559 : subd7_1 [2, 0, -4] = true := by decide +kernel
theorem subd7_1_560 : subd7_1 [2, 0, -3] = true := by decide +kernel
theorem subd7_1_561 : subd7_1 [2, 0, -2] = true := by decide +kernel
theorem subd7_1_562 : subd7_1 [2, 0, -1] = true := by decide +kernel
theorem subd7_1_563 : subd7_1 [2, 0, 0] = true := by decide +kernel
theorem subd7_1_564 : subd7_1 [2, 0, 1] = true := by decide +kernel
theorem subd7_1_565 : subd7_1 [2, 0, 2] = true := by decide +kernel
theorem subd7_1_566 : subd7_1 [2, 0, 3] = true := by decide +kernel
theorem subd7_1_567 : subd7_1 [2, 0, 4] = true := by decide +kernel
theorem subd7_1_568 : subd7_1 [2, 0, 5] = true := by decide +kernel
theorem subd7_1_569 : subd7_1 [2, 0, 6] = true := by decide +kernel
theorem subd7_1_570 : subd7_1 [2, 1, -8] = true := by decide +kernel
theorem subd7_1_571 : subd7_1 [2, 1, -7] = true := by decide +kernel
theorem subd7_1_572 : subd7_1 [2, 1, -6] = true := by decide +kernel
theorem subd7_1_573 : subd7_1 [2, 1, -5] = true := by decide +kernel
theorem subd7_1_574 : subd7_1 [2, 1, -4] = true := by decide +kernel
theorem subd7_1_575 : subd7_1 [2, 1, -3] = true := by decide +kernel
theorem sbd7_1_17 : ∀ q ∈ blkd7_1_17, subd7_1 q = true := by
  unfold blkd7_1_17
  exact List.forall_mem_cons.2 ⟨subd7_1_544, List.forall_mem_cons.2 ⟨subd7_1_545, List.forall_mem_cons.2 ⟨subd7_1_546, List.forall_mem_cons.2 ⟨subd7_1_547, List.forall_mem_cons.2 ⟨subd7_1_548, List.forall_mem_cons.2 ⟨subd7_1_549, List.forall_mem_cons.2 ⟨subd7_1_550, List.forall_mem_cons.2 ⟨subd7_1_551, List.forall_mem_cons.2 ⟨subd7_1_552, List.forall_mem_cons.2 ⟨subd7_1_553, List.forall_mem_cons.2 ⟨subd7_1_554, List.forall_mem_cons.2 ⟨subd7_1_555, List.forall_mem_cons.2 ⟨subd7_1_556, List.forall_mem_cons.2 ⟨subd7_1_557, List.forall_mem_cons.2 ⟨subd7_1_558, List.forall_mem_cons.2 ⟨subd7_1_559, List.forall_mem_cons.2 ⟨subd7_1_560, List.forall_mem_cons.2 ⟨subd7_1_561, List.forall_mem_cons.2 ⟨subd7_1_562, List.forall_mem_cons.2 ⟨subd7_1_563, List.forall_mem_cons.2 ⟨subd7_1_564, List.forall_mem_cons.2 ⟨subd7_1_565, List.forall_mem_cons.2 ⟨subd7_1_566, List.forall_mem_cons.2 ⟨subd7_1_567, List.forall_mem_cons.2 ⟨subd7_1_568, List.forall_mem_cons.2 ⟨subd7_1_569, List.forall_mem_cons.2 ⟨subd7_1_570, List.forall_mem_cons.2 ⟨subd7_1_571, List.forall_mem_cons.2 ⟨subd7_1_572, List.forall_mem_cons.2 ⟨subd7_1_573, List.forall_mem_cons.2 ⟨subd7_1_574, List.forall_mem_cons.2 ⟨subd7_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_576 : subd7_1 [2, 1, -2] = true := by decide +kernel
theorem subd7_1_577 : subd7_1 [2, 1, -1] = true := by decide +kernel
theorem subd7_1_578 : subd7_1 [2, 1, 0] = true := by decide +kernel
theorem subd7_1_579 : subd7_1 [2, 1, 1] = true := by decide +kernel
theorem subd7_1_580 : subd7_1 [2, 1, 2] = true := by decide +kernel
theorem subd7_1_581 : subd7_1 [2, 1, 3] = true := by decide +kernel
theorem subd7_1_582 : subd7_1 [2, 1, 4] = true := by decide +kernel
theorem subd7_1_583 : subd7_1 [2, 1, 5] = true := by decide +kernel
theorem subd7_1_584 : subd7_1 [2, 1, 6] = true := by decide +kernel
theorem subd7_1_585 : subd7_1 [2, 2, -8] = true := by decide +kernel
theorem subd7_1_586 : subd7_1 [2, 2, -7] = true := by decide +kernel
theorem subd7_1_587 : subd7_1 [2, 2, -6] = true := by decide +kernel
theorem subd7_1_588 : subd7_1 [2, 2, -5] = true := by decide +kernel
theorem subd7_1_589 : subd7_1 [2, 2, -4] = true := by decide +kernel
theorem subd7_1_590 : subd7_1 [2, 2, -3] = true := by decide +kernel
theorem subd7_1_591 : subd7_1 [2, 2, -2] = true := by decide +kernel
theorem subd7_1_592 : subd7_1 [2, 2, -1] = true := by decide +kernel
theorem subd7_1_593 : subd7_1 [2, 2, 0] = true := by decide +kernel
theorem subd7_1_594 : subd7_1 [2, 2, 1] = true := by decide +kernel
theorem subd7_1_595 : subd7_1 [2, 2, 2] = true := by decide +kernel
theorem subd7_1_596 : subd7_1 [2, 2, 3] = true := by decide +kernel
theorem subd7_1_597 : subd7_1 [2, 2, 4] = true := by decide +kernel
theorem subd7_1_598 : subd7_1 [2, 2, 5] = true := by decide +kernel
theorem subd7_1_599 : subd7_1 [2, 3] = true := by decide +kernel
theorem subd7_1_600 : subd7_1 [2, 4] = true := by decide +kernel
theorem subd7_1_601 : subd7_1 [2, 5] = true := by decide +kernel
theorem subd7_1_602 : subd7_1 [3, -6] = true := by decide +kernel
theorem subd7_1_603 : subd7_1 [3, -5] = true := by decide +kernel
theorem subd7_1_604 : subd7_1 [3, -4] = true := by decide +kernel
theorem subd7_1_605 : subd7_1 [3, -3] = true := by decide +kernel
theorem subd7_1_606 : subd7_1 [3, -2, -6] = true := by decide +kernel
theorem subd7_1_607 : subd7_1 [3, -2, -5] = true := by decide +kernel
theorem sbd7_1_18 : ∀ q ∈ blkd7_1_18, subd7_1 q = true := by
  unfold blkd7_1_18
  exact List.forall_mem_cons.2 ⟨subd7_1_576, List.forall_mem_cons.2 ⟨subd7_1_577, List.forall_mem_cons.2 ⟨subd7_1_578, List.forall_mem_cons.2 ⟨subd7_1_579, List.forall_mem_cons.2 ⟨subd7_1_580, List.forall_mem_cons.2 ⟨subd7_1_581, List.forall_mem_cons.2 ⟨subd7_1_582, List.forall_mem_cons.2 ⟨subd7_1_583, List.forall_mem_cons.2 ⟨subd7_1_584, List.forall_mem_cons.2 ⟨subd7_1_585, List.forall_mem_cons.2 ⟨subd7_1_586, List.forall_mem_cons.2 ⟨subd7_1_587, List.forall_mem_cons.2 ⟨subd7_1_588, List.forall_mem_cons.2 ⟨subd7_1_589, List.forall_mem_cons.2 ⟨subd7_1_590, List.forall_mem_cons.2 ⟨subd7_1_591, List.forall_mem_cons.2 ⟨subd7_1_592, List.forall_mem_cons.2 ⟨subd7_1_593, List.forall_mem_cons.2 ⟨subd7_1_594, List.forall_mem_cons.2 ⟨subd7_1_595, List.forall_mem_cons.2 ⟨subd7_1_596, List.forall_mem_cons.2 ⟨subd7_1_597, List.forall_mem_cons.2 ⟨subd7_1_598, List.forall_mem_cons.2 ⟨subd7_1_599, List.forall_mem_cons.2 ⟨subd7_1_600, List.forall_mem_cons.2 ⟨subd7_1_601, List.forall_mem_cons.2 ⟨subd7_1_602, List.forall_mem_cons.2 ⟨subd7_1_603, List.forall_mem_cons.2 ⟨subd7_1_604, List.forall_mem_cons.2 ⟨subd7_1_605, List.forall_mem_cons.2 ⟨subd7_1_606, List.forall_mem_cons.2 ⟨subd7_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_608 : subd7_1 [3, -2, -4] = true := by decide +kernel
theorem subd7_1_609 : subd7_1 [3, -2, -3] = true := by decide +kernel
theorem subd7_1_610 : subd7_1 [3, -2, -2] = true := by decide +kernel
theorem subd7_1_611 : subd7_1 [3, -2, -1] = true := by decide +kernel
theorem subd7_1_612 : subd7_1 [3, -2, 0] = true := by decide +kernel
theorem subd7_1_613 : subd7_1 [3, -2, 1] = true := by decide +kernel
theorem subd7_1_614 : subd7_1 [3, -2, 2] = true := by decide +kernel
theorem subd7_1_615 : subd7_1 [3, -2, 3] = true := by decide +kernel
theorem subd7_1_616 : subd7_1 [3, -2, 4] = true := by decide +kernel
theorem subd7_1_617 : subd7_1 [3, -2, 5] = true := by decide +kernel
theorem subd7_1_618 : subd7_1 [3, -2, 6] = true := by decide +kernel
theorem subd7_1_619 : subd7_1 [3, -1, -7] = true := by decide +kernel
theorem subd7_1_620 : subd7_1 [3, -1, -6] = true := by decide +kernel
theorem subd7_1_621 : subd7_1 [3, -1, -5] = true := by decide +kernel
theorem subd7_1_622 : subd7_1 [3, -1, -4] = true := by decide +kernel
theorem subd7_1_623 : subd7_1 [3, -1, -3] = true := by decide +kernel
theorem subd7_1_624 : subd7_1 [3, -1, -2] = true := by decide +kernel
theorem subd7_1_625 : subd7_1 [3, -1, -1] = true := by decide +kernel
theorem subd7_1_626 : subd7_1 [3, -1, 0] = true := by decide +kernel
theorem subd7_1_627 : subd7_1 [3, -1, 1] = true := by decide +kernel
theorem subd7_1_628 : subd7_1 [3, -1, 2] = true := by decide +kernel
theorem subd7_1_629 : subd7_1 [3, -1, 3] = true := by decide +kernel
theorem subd7_1_630 : subd7_1 [3, -1, 4] = true := by decide +kernel
theorem subd7_1_631 : subd7_1 [3, -1, 5] = true := by decide +kernel
theorem subd7_1_632 : subd7_1 [3, -1, 6] = true := by decide +kernel
theorem subd7_1_633 : subd7_1 [3, 0, -7] = true := by decide +kernel
theorem subd7_1_634 : subd7_1 [3, 0, -6] = true := by decide +kernel
theorem subd7_1_635 : subd7_1 [3, 0, -5] = true := by decide +kernel
theorem subd7_1_636 : subd7_1 [3, 0, -4] = true := by decide +kernel
theorem subd7_1_637 : subd7_1 [3, 0, -3] = true := by decide +kernel
theorem subd7_1_638 : subd7_1 [3, 0, -2] = true := by decide +kernel
theorem subd7_1_639 : subd7_1 [3, 0, -1] = true := by decide +kernel
theorem sbd7_1_19 : ∀ q ∈ blkd7_1_19, subd7_1 q = true := by
  unfold blkd7_1_19
  exact List.forall_mem_cons.2 ⟨subd7_1_608, List.forall_mem_cons.2 ⟨subd7_1_609, List.forall_mem_cons.2 ⟨subd7_1_610, List.forall_mem_cons.2 ⟨subd7_1_611, List.forall_mem_cons.2 ⟨subd7_1_612, List.forall_mem_cons.2 ⟨subd7_1_613, List.forall_mem_cons.2 ⟨subd7_1_614, List.forall_mem_cons.2 ⟨subd7_1_615, List.forall_mem_cons.2 ⟨subd7_1_616, List.forall_mem_cons.2 ⟨subd7_1_617, List.forall_mem_cons.2 ⟨subd7_1_618, List.forall_mem_cons.2 ⟨subd7_1_619, List.forall_mem_cons.2 ⟨subd7_1_620, List.forall_mem_cons.2 ⟨subd7_1_621, List.forall_mem_cons.2 ⟨subd7_1_622, List.forall_mem_cons.2 ⟨subd7_1_623, List.forall_mem_cons.2 ⟨subd7_1_624, List.forall_mem_cons.2 ⟨subd7_1_625, List.forall_mem_cons.2 ⟨subd7_1_626, List.forall_mem_cons.2 ⟨subd7_1_627, List.forall_mem_cons.2 ⟨subd7_1_628, List.forall_mem_cons.2 ⟨subd7_1_629, List.forall_mem_cons.2 ⟨subd7_1_630, List.forall_mem_cons.2 ⟨subd7_1_631, List.forall_mem_cons.2 ⟨subd7_1_632, List.forall_mem_cons.2 ⟨subd7_1_633, List.forall_mem_cons.2 ⟨subd7_1_634, List.forall_mem_cons.2 ⟨subd7_1_635, List.forall_mem_cons.2 ⟨subd7_1_636, List.forall_mem_cons.2 ⟨subd7_1_637, List.forall_mem_cons.2 ⟨subd7_1_638, List.forall_mem_cons.2 ⟨subd7_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_640 : subd7_1 [3, 0, 0] = true := by decide +kernel
theorem subd7_1_641 : subd7_1 [3, 0, 1] = true := by decide +kernel
theorem subd7_1_642 : subd7_1 [3, 0, 2] = true := by decide +kernel
theorem subd7_1_643 : subd7_1 [3, 0, 3] = true := by decide +kernel
theorem subd7_1_644 : subd7_1 [3, 0, 4] = true := by decide +kernel
theorem subd7_1_645 : subd7_1 [3, 0, 5] = true := by decide +kernel
theorem subd7_1_646 : subd7_1 [3, 0, 6] = true := by decide +kernel
theorem subd7_1_647 : subd7_1 [3, 1, -8] = true := by decide +kernel
theorem subd7_1_648 : subd7_1 [3, 1, -7] = true := by decide +kernel
theorem subd7_1_649 : subd7_1 [3, 1, -6] = true := by decide +kernel
theorem subd7_1_650 : subd7_1 [3, 1, -5] = true := by decide +kernel
theorem subd7_1_651 : subd7_1 [3, 1, -4] = true := by decide +kernel
theorem subd7_1_652 : subd7_1 [3, 1, -3] = true := by decide +kernel
theorem subd7_1_653 : subd7_1 [3, 1, -2] = true := by decide +kernel
theorem subd7_1_654 : subd7_1 [3, 1, -1] = true := by decide +kernel
theorem subd7_1_655 : subd7_1 [3, 1, 0] = true := by decide +kernel
theorem subd7_1_656 : subd7_1 [3, 1, 1] = true := by decide +kernel
theorem subd7_1_657 : subd7_1 [3, 1, 2] = true := by decide +kernel
theorem subd7_1_658 : subd7_1 [3, 1, 3] = true := by decide +kernel
theorem subd7_1_659 : subd7_1 [3, 1, 4] = true := by decide +kernel
theorem subd7_1_660 : subd7_1 [3, 1, 5] = true := by decide +kernel
theorem subd7_1_661 : subd7_1 [3, 2] = true := by decide +kernel
theorem subd7_1_662 : subd7_1 [3, 3] = true := by decide +kernel
theorem subd7_1_663 : subd7_1 [3, 4] = true := by decide +kernel
theorem subd7_1_664 : subd7_1 [4, -6] = true := by decide +kernel
theorem subd7_1_665 : subd7_1 [4, -5] = true := by decide +kernel
theorem subd7_1_666 : subd7_1 [4, -4] = true := by decide +kernel
theorem subd7_1_667 : subd7_1 [4, -3] = true := by decide +kernel
theorem subd7_1_668 : subd7_1 [4, -2] = true := by decide +kernel
theorem subd7_1_669 : subd7_1 [4, -1] = true := by decide +kernel
theorem subd7_1_670 : subd7_1 [4, 0] = true := by decide +kernel
theorem subd7_1_671 : subd7_1 [4, 1] = true := by decide +kernel
theorem sbd7_1_20 : ∀ q ∈ blkd7_1_20, subd7_1 q = true := by
  unfold blkd7_1_20
  exact List.forall_mem_cons.2 ⟨subd7_1_640, List.forall_mem_cons.2 ⟨subd7_1_641, List.forall_mem_cons.2 ⟨subd7_1_642, List.forall_mem_cons.2 ⟨subd7_1_643, List.forall_mem_cons.2 ⟨subd7_1_644, List.forall_mem_cons.2 ⟨subd7_1_645, List.forall_mem_cons.2 ⟨subd7_1_646, List.forall_mem_cons.2 ⟨subd7_1_647, List.forall_mem_cons.2 ⟨subd7_1_648, List.forall_mem_cons.2 ⟨subd7_1_649, List.forall_mem_cons.2 ⟨subd7_1_650, List.forall_mem_cons.2 ⟨subd7_1_651, List.forall_mem_cons.2 ⟨subd7_1_652, List.forall_mem_cons.2 ⟨subd7_1_653, List.forall_mem_cons.2 ⟨subd7_1_654, List.forall_mem_cons.2 ⟨subd7_1_655, List.forall_mem_cons.2 ⟨subd7_1_656, List.forall_mem_cons.2 ⟨subd7_1_657, List.forall_mem_cons.2 ⟨subd7_1_658, List.forall_mem_cons.2 ⟨subd7_1_659, List.forall_mem_cons.2 ⟨subd7_1_660, List.forall_mem_cons.2 ⟨subd7_1_661, List.forall_mem_cons.2 ⟨subd7_1_662, List.forall_mem_cons.2 ⟨subd7_1_663, List.forall_mem_cons.2 ⟨subd7_1_664, List.forall_mem_cons.2 ⟨subd7_1_665, List.forall_mem_cons.2 ⟨subd7_1_666, List.forall_mem_cons.2 ⟨subd7_1_667, List.forall_mem_cons.2 ⟨subd7_1_668, List.forall_mem_cons.2 ⟨subd7_1_669, List.forall_mem_cons.2 ⟨subd7_1_670, List.forall_mem_cons.2 ⟨subd7_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_672 : subd7_1 [4, 2] = true := by decide +kernel
theorem subd7_1_673 : subd7_1 [4, 3] = true := by decide +kernel
theorem subd7_1_674 : subd7_1 [4, 4] = true := by decide +kernel
theorem subd7_1_675 : subd7_1 [5, -5] = true := by decide +kernel
theorem subd7_1_676 : subd7_1 [5, -4] = true := by decide +kernel
theorem subd7_1_677 : subd7_1 [5, -3] = true := by decide +kernel
theorem subd7_1_678 : subd7_1 [5, -2] = true := by decide +kernel
theorem subd7_1_679 : subd7_1 [5, -1] = true := by decide +kernel
theorem subd7_1_680 : subd7_1 [5, 0] = true := by decide +kernel
theorem subd7_1_681 : subd7_1 [5, 1] = true := by decide +kernel
theorem subd7_1_682 : subd7_1 [5, 2] = true := by decide +kernel
theorem subd7_1_683 : subd7_1 [5, 3] = true := by decide +kernel
theorem subd7_1_684 : subd7_1 [6] = true := by decide +kernel
theorem sbd7_1_21 : ∀ q ∈ blkd7_1_21, subd7_1 q = true := by
  unfold blkd7_1_21
  exact List.forall_mem_cons.2 ⟨subd7_1_672, List.forall_mem_cons.2 ⟨subd7_1_673, List.forall_mem_cons.2 ⟨subd7_1_674, List.forall_mem_cons.2 ⟨subd7_1_675, List.forall_mem_cons.2 ⟨subd7_1_676, List.forall_mem_cons.2 ⟨subd7_1_677, List.forall_mem_cons.2 ⟨subd7_1_678, List.forall_mem_cons.2 ⟨subd7_1_679, List.forall_mem_cons.2 ⟨subd7_1_680, List.forall_mem_cons.2 ⟨subd7_1_681, List.forall_mem_cons.2 ⟨subd7_1_682, List.forall_mem_cons.2 ⟨subd7_1_683, List.forall_mem_cons.2 ⟨subd7_1_684, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [-4, 0] = true := by decide +kernel
theorem subd7_2_1 : subd7_2 [-4, 1] = true := by decide +kernel
theorem subd7_2_2 : subd7_2 [-4, 2] = true := by decide +kernel
theorem subd7_2_3 : subd7_2 [-4, 3] = true := by decide +kernel
theorem subd7_2_4 : subd7_2 [-3, -2] = true := by decide +kernel
theorem subd7_2_5 : subd7_2 [-3, -1, -8] = true := by decide +kernel
theorem subd7_2_6 : subd7_2 [-3, -1, -7] = true := by decide +kernel
theorem subd7_2_7 : subd7_2 [-3, -1, -6] = true := by decide +kernel
theorem subd7_2_8 : subd7_2 [-3, -1, -5] = true := by decide +kernel
theorem subd7_2_9 : subd7_2 [-3, -1, -4] = true := by decide +kernel
theorem subd7_2_10 : subd7_2 [-3, -1, -3] = true := by decide +kernel
theorem subd7_2_11 : subd7_2 [-3, -1, -2] = true := by decide +kernel
theorem subd7_2_12 : subd7_2 [-3, -1, -1] = true := by decide +kernel
theorem subd7_2_13 : subd7_2 [-3, -1, 0] = true := by decide +kernel
theorem subd7_2_14 : subd7_2 [-3, -1, 1] = true := by decide +kernel
theorem subd7_2_15 : subd7_2 [-3, -1, 2] = true := by decide +kernel
theorem subd7_2_16 : subd7_2 [-3, -1, 3] = true := by decide +kernel
theorem subd7_2_17 : subd7_2 [-3, -1, 4] = true := by decide +kernel
theorem subd7_2_18 : subd7_2 [-3, -1, 5] = true := by decide +kernel
theorem subd7_2_19 : subd7_2 [-3, -1, 6] = true := by decide +kernel
theorem subd7_2_20 : subd7_2 [-3, -1, 7] = true := by decide +kernel
theorem subd7_2_21 : subd7_2 [-3, -1, 8] = true := by decide +kernel
theorem subd7_2_22 : subd7_2 [-3, -1, 9] = true := by decide +kernel
theorem subd7_2_23 : subd7_2 [-3, 0, -10] = true := by decide +kernel
theorem subd7_2_24 : subd7_2 [-3, 0, -9] = true := by decide +kernel
theorem subd7_2_25 : subd7_2 [-3, 0, -8] = true := by decide +kernel
theorem subd7_2_26 : subd7_2 [-3, 0, -7] = true := by decide +kernel
theorem subd7_2_27 : subd7_2 [-3, 0, -6] = true := by decide +kernel
theorem subd7_2_28 : subd7_2 [-3, 0, -5] = true := by decide +kernel
theorem subd7_2_29 : subd7_2 [-3, 0, -4] = true := by decide +kernel
theorem subd7_2_30 : subd7_2 [-3, 0, -3] = true := by decide +kernel
theorem subd7_2_31 : subd7_2 [-3, 0, -2] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_cons.2 ⟨subd7_2_1, List.forall_mem_cons.2 ⟨subd7_2_2, List.forall_mem_cons.2 ⟨subd7_2_3, List.forall_mem_cons.2 ⟨subd7_2_4, List.forall_mem_cons.2 ⟨subd7_2_5, List.forall_mem_cons.2 ⟨subd7_2_6, List.forall_mem_cons.2 ⟨subd7_2_7, List.forall_mem_cons.2 ⟨subd7_2_8, List.forall_mem_cons.2 ⟨subd7_2_9, List.forall_mem_cons.2 ⟨subd7_2_10, List.forall_mem_cons.2 ⟨subd7_2_11, List.forall_mem_cons.2 ⟨subd7_2_12, List.forall_mem_cons.2 ⟨subd7_2_13, List.forall_mem_cons.2 ⟨subd7_2_14, List.forall_mem_cons.2 ⟨subd7_2_15, List.forall_mem_cons.2 ⟨subd7_2_16, List.forall_mem_cons.2 ⟨subd7_2_17, List.forall_mem_cons.2 ⟨subd7_2_18, List.forall_mem_cons.2 ⟨subd7_2_19, List.forall_mem_cons.2 ⟨subd7_2_20, List.forall_mem_cons.2 ⟨subd7_2_21, List.forall_mem_cons.2 ⟨subd7_2_22, List.forall_mem_cons.2 ⟨subd7_2_23, List.forall_mem_cons.2 ⟨subd7_2_24, List.forall_mem_cons.2 ⟨subd7_2_25, List.forall_mem_cons.2 ⟨subd7_2_26, List.forall_mem_cons.2 ⟨subd7_2_27, List.forall_mem_cons.2 ⟨subd7_2_28, List.forall_mem_cons.2 ⟨subd7_2_29, List.forall_mem_cons.2 ⟨subd7_2_30, List.forall_mem_cons.2 ⟨subd7_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
