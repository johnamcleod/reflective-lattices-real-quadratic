import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_3_384 : subd7_3 [-1, 0, -6] = true := by decide +kernel
theorem subd7_3_385 : subd7_3 [-1, 0, -5] = true := by decide +kernel
theorem subd7_3_386 : subd7_3 [-1, 0, -4] = true := by decide +kernel
theorem subd7_3_387 : subd7_3 [-1, 0, -3] = true := by decide +kernel
theorem subd7_3_388 : subd7_3 [-1, 0, -2] = true := by decide +kernel
theorem subd7_3_389 : subd7_3 [-1, 0, -1] = true := by decide +kernel
theorem subd7_3_390 : subd7_3 [-1, 0, 0] = true := by decide +kernel
theorem subd7_3_391 : subd7_3 [-1, 0, 1] = true := by decide +kernel
theorem subd7_3_392 : subd7_3 [-1, 0, 2] = true := by decide +kernel
theorem subd7_3_393 : subd7_3 [-1, 0, 3] = true := by decide +kernel
theorem subd7_3_394 : subd7_3 [-1, 0, 4] = true := by decide +kernel
theorem subd7_3_395 : subd7_3 [-1, 0, 5] = true := by decide +kernel
theorem subd7_3_396 : subd7_3 [-1, 0, 6] = true := by decide +kernel
theorem subd7_3_397 : subd7_3 [-1, 0, 7] = true := by decide +kernel
theorem subd7_3_398 : subd7_3 [-1, 1, -9] = true := by decide +kernel
theorem subd7_3_399 : subd7_3 [-1, 1, -8] = true := by decide +kernel
theorem subd7_3_400 : subd7_3 [-1, 1, -7] = true := by decide +kernel
theorem subd7_3_401 : subd7_3 [-1, 1, -6] = true := by decide +kernel
theorem subd7_3_402 : subd7_3 [-1, 1, -5] = true := by decide +kernel
theorem subd7_3_403 : subd7_3 [-1, 1, -4] = true := by decide +kernel
theorem subd7_3_404 : subd7_3 [-1, 1, -3] = true := by decide +kernel
theorem subd7_3_405 : subd7_3 [-1, 1, -2] = true := by decide +kernel
theorem subd7_3_406 : subd7_3 [-1, 1, -1] = true := by decide +kernel
theorem subd7_3_407 : subd7_3 [-1, 1, 0] = true := by decide +kernel
theorem subd7_3_408 : subd7_3 [-1, 1, 1] = true := by decide +kernel
theorem subd7_3_409 : subd7_3 [-1, 1, 2] = true := by decide +kernel
theorem subd7_3_410 : subd7_3 [-1, 1, 3] = true := by decide +kernel
theorem subd7_3_411 : subd7_3 [-1, 1, 4] = true := by decide +kernel
theorem subd7_3_412 : subd7_3 [-1, 1, 5] = true := by decide +kernel
theorem subd7_3_413 : subd7_3 [-1, 1, 6] = true := by decide +kernel
theorem subd7_3_414 : subd7_3 [-1, 1, 7] = true := by decide +kernel
theorem subd7_3_415 : subd7_3 [-1, 2, -9] = true := by decide +kernel
theorem sbd7_3_12 : ∀ q ∈ blkd7_3_12, subd7_3 q = true := by
  unfold blkd7_3_12
  exact List.forall_mem_cons.2 ⟨subd7_3_384, List.forall_mem_cons.2 ⟨subd7_3_385, List.forall_mem_cons.2 ⟨subd7_3_386, List.forall_mem_cons.2 ⟨subd7_3_387, List.forall_mem_cons.2 ⟨subd7_3_388, List.forall_mem_cons.2 ⟨subd7_3_389, List.forall_mem_cons.2 ⟨subd7_3_390, List.forall_mem_cons.2 ⟨subd7_3_391, List.forall_mem_cons.2 ⟨subd7_3_392, List.forall_mem_cons.2 ⟨subd7_3_393, List.forall_mem_cons.2 ⟨subd7_3_394, List.forall_mem_cons.2 ⟨subd7_3_395, List.forall_mem_cons.2 ⟨subd7_3_396, List.forall_mem_cons.2 ⟨subd7_3_397, List.forall_mem_cons.2 ⟨subd7_3_398, List.forall_mem_cons.2 ⟨subd7_3_399, List.forall_mem_cons.2 ⟨subd7_3_400, List.forall_mem_cons.2 ⟨subd7_3_401, List.forall_mem_cons.2 ⟨subd7_3_402, List.forall_mem_cons.2 ⟨subd7_3_403, List.forall_mem_cons.2 ⟨subd7_3_404, List.forall_mem_cons.2 ⟨subd7_3_405, List.forall_mem_cons.2 ⟨subd7_3_406, List.forall_mem_cons.2 ⟨subd7_3_407, List.forall_mem_cons.2 ⟨subd7_3_408, List.forall_mem_cons.2 ⟨subd7_3_409, List.forall_mem_cons.2 ⟨subd7_3_410, List.forall_mem_cons.2 ⟨subd7_3_411, List.forall_mem_cons.2 ⟨subd7_3_412, List.forall_mem_cons.2 ⟨subd7_3_413, List.forall_mem_cons.2 ⟨subd7_3_414, List.forall_mem_cons.2 ⟨subd7_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_416 : subd7_3 [-1, 2, -8] = true := by decide +kernel
theorem subd7_3_417 : subd7_3 [-1, 2, -7] = true := by decide +kernel
theorem subd7_3_418 : subd7_3 [-1, 2, -6] = true := by decide +kernel
theorem subd7_3_419 : subd7_3 [-1, 2, -5] = true := by decide +kernel
theorem subd7_3_420 : subd7_3 [-1, 2, -4] = true := by decide +kernel
theorem subd7_3_421 : subd7_3 [-1, 2, -3] = true := by decide +kernel
theorem subd7_3_422 : subd7_3 [-1, 2, -2] = true := by decide +kernel
theorem subd7_3_423 : subd7_3 [-1, 2, -1] = true := by decide +kernel
theorem subd7_3_424 : subd7_3 [-1, 2, 0] = true := by decide +kernel
theorem subd7_3_425 : subd7_3 [-1, 2, 1] = true := by decide +kernel
theorem subd7_3_426 : subd7_3 [-1, 2, 2] = true := by decide +kernel
theorem subd7_3_427 : subd7_3 [-1, 2, 3] = true := by decide +kernel
theorem subd7_3_428 : subd7_3 [-1, 2, 4] = true := by decide +kernel
theorem subd7_3_429 : subd7_3 [-1, 2, 5] = true := by decide +kernel
theorem subd7_3_430 : subd7_3 [-1, 2, 6] = true := by decide +kernel
theorem subd7_3_431 : subd7_3 [-1, 2, 7] = true := by decide +kernel
theorem subd7_3_432 : subd7_3 [-1, 3, -8] = true := by decide +kernel
theorem subd7_3_433 : subd7_3 [-1, 3, -7] = true := by decide +kernel
theorem subd7_3_434 : subd7_3 [-1, 3, -6] = true := by decide +kernel
theorem subd7_3_435 : subd7_3 [-1, 3, -5] = true := by decide +kernel
theorem subd7_3_436 : subd7_3 [-1, 3, -4] = true := by decide +kernel
theorem subd7_3_437 : subd7_3 [-1, 3, -3] = true := by decide +kernel
theorem subd7_3_438 : subd7_3 [-1, 3, -2] = true := by decide +kernel
theorem subd7_3_439 : subd7_3 [-1, 3, -1] = true := by decide +kernel
theorem subd7_3_440 : subd7_3 [-1, 3, 0] = true := by decide +kernel
theorem subd7_3_441 : subd7_3 [-1, 3, 1] = true := by decide +kernel
theorem subd7_3_442 : subd7_3 [-1, 3, 2] = true := by decide +kernel
theorem subd7_3_443 : subd7_3 [-1, 3, 3] = true := by decide +kernel
theorem subd7_3_444 : subd7_3 [-1, 3, 4] = true := by decide +kernel
theorem subd7_3_445 : subd7_3 [-1, 3, 5] = true := by decide +kernel
theorem subd7_3_446 : subd7_3 [-1, 3, 6] = true := by decide +kernel
theorem subd7_3_447 : subd7_3 [-1, 4, -7] = true := by decide +kernel
theorem sbd7_3_13 : ∀ q ∈ blkd7_3_13, subd7_3 q = true := by
  unfold blkd7_3_13
  exact List.forall_mem_cons.2 ⟨subd7_3_416, List.forall_mem_cons.2 ⟨subd7_3_417, List.forall_mem_cons.2 ⟨subd7_3_418, List.forall_mem_cons.2 ⟨subd7_3_419, List.forall_mem_cons.2 ⟨subd7_3_420, List.forall_mem_cons.2 ⟨subd7_3_421, List.forall_mem_cons.2 ⟨subd7_3_422, List.forall_mem_cons.2 ⟨subd7_3_423, List.forall_mem_cons.2 ⟨subd7_3_424, List.forall_mem_cons.2 ⟨subd7_3_425, List.forall_mem_cons.2 ⟨subd7_3_426, List.forall_mem_cons.2 ⟨subd7_3_427, List.forall_mem_cons.2 ⟨subd7_3_428, List.forall_mem_cons.2 ⟨subd7_3_429, List.forall_mem_cons.2 ⟨subd7_3_430, List.forall_mem_cons.2 ⟨subd7_3_431, List.forall_mem_cons.2 ⟨subd7_3_432, List.forall_mem_cons.2 ⟨subd7_3_433, List.forall_mem_cons.2 ⟨subd7_3_434, List.forall_mem_cons.2 ⟨subd7_3_435, List.forall_mem_cons.2 ⟨subd7_3_436, List.forall_mem_cons.2 ⟨subd7_3_437, List.forall_mem_cons.2 ⟨subd7_3_438, List.forall_mem_cons.2 ⟨subd7_3_439, List.forall_mem_cons.2 ⟨subd7_3_440, List.forall_mem_cons.2 ⟨subd7_3_441, List.forall_mem_cons.2 ⟨subd7_3_442, List.forall_mem_cons.2 ⟨subd7_3_443, List.forall_mem_cons.2 ⟨subd7_3_444, List.forall_mem_cons.2 ⟨subd7_3_445, List.forall_mem_cons.2 ⟨subd7_3_446, List.forall_mem_cons.2 ⟨subd7_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_448 : subd7_3 [-1, 4, -6] = true := by decide +kernel
theorem subd7_3_449 : subd7_3 [-1, 4, -5] = true := by decide +kernel
theorem subd7_3_450 : subd7_3 [-1, 4, -4] = true := by decide +kernel
theorem subd7_3_451 : subd7_3 [-1, 4, -3] = true := by decide +kernel
theorem subd7_3_452 : subd7_3 [-1, 4, -2] = true := by decide +kernel
theorem subd7_3_453 : subd7_3 [-1, 4, -1] = true := by decide +kernel
theorem subd7_3_454 : subd7_3 [-1, 4, 0] = true := by decide +kernel
theorem subd7_3_455 : subd7_3 [-1, 4, 1] = true := by decide +kernel
theorem subd7_3_456 : subd7_3 [-1, 4, 2] = true := by decide +kernel
theorem subd7_3_457 : subd7_3 [-1, 4, 3] = true := by decide +kernel
theorem subd7_3_458 : subd7_3 [-1, 4, 4] = true := by decide +kernel
theorem subd7_3_459 : subd7_3 [-1, 4, 5] = true := by decide +kernel
theorem subd7_3_460 : subd7_3 [-1, 4, 6] = true := by decide +kernel
theorem subd7_3_461 : subd7_3 [-1, 5] = true := by decide +kernel
theorem subd7_3_462 : subd7_3 [-1, 6] = true := by decide +kernel
theorem subd7_3_463 : subd7_3 [0, -8] = true := by decide +kernel
theorem subd7_3_464 : subd7_3 [0, -7] = true := by decide +kernel
theorem subd7_3_465 : subd7_3 [0, -6] = true := by decide +kernel
theorem subd7_3_466 : subd7_3 [0, -5] = true := by decide +kernel
theorem subd7_3_467 : subd7_3 [0, -4, -7] = true := by decide +kernel
theorem subd7_3_468 : subd7_3 [0, -4, -6] = true := by decide +kernel
theorem subd7_3_469 : subd7_3 [0, -4, -5] = true := by decide +kernel
theorem subd7_3_470 : subd7_3 [0, -4, -4] = true := by decide +kernel
theorem subd7_3_471 : subd7_3 [0, -4, -3] = true := by decide +kernel
theorem subd7_3_472 : subd7_3 [0, -4, -2] = true := by decide +kernel
theorem subd7_3_473 : subd7_3 [0, -4, -1] = true := by decide +kernel
theorem subd7_3_474 : subd7_3 [0, -4, 0] = true := by decide +kernel
theorem subd7_3_475 : subd7_3 [0, -4, 1] = true := by decide +kernel
theorem subd7_3_476 : subd7_3 [0, -4, 2] = true := by decide +kernel
theorem subd7_3_477 : subd7_3 [0, -4, 3] = true := by decide +kernel
theorem subd7_3_478 : subd7_3 [0, -4, 4] = true := by decide +kernel
theorem subd7_3_479 : subd7_3 [0, -4, 5] = true := by decide +kernel
theorem sbd7_3_14 : ∀ q ∈ blkd7_3_14, subd7_3 q = true := by
  unfold blkd7_3_14
  exact List.forall_mem_cons.2 ⟨subd7_3_448, List.forall_mem_cons.2 ⟨subd7_3_449, List.forall_mem_cons.2 ⟨subd7_3_450, List.forall_mem_cons.2 ⟨subd7_3_451, List.forall_mem_cons.2 ⟨subd7_3_452, List.forall_mem_cons.2 ⟨subd7_3_453, List.forall_mem_cons.2 ⟨subd7_3_454, List.forall_mem_cons.2 ⟨subd7_3_455, List.forall_mem_cons.2 ⟨subd7_3_456, List.forall_mem_cons.2 ⟨subd7_3_457, List.forall_mem_cons.2 ⟨subd7_3_458, List.forall_mem_cons.2 ⟨subd7_3_459, List.forall_mem_cons.2 ⟨subd7_3_460, List.forall_mem_cons.2 ⟨subd7_3_461, List.forall_mem_cons.2 ⟨subd7_3_462, List.forall_mem_cons.2 ⟨subd7_3_463, List.forall_mem_cons.2 ⟨subd7_3_464, List.forall_mem_cons.2 ⟨subd7_3_465, List.forall_mem_cons.2 ⟨subd7_3_466, List.forall_mem_cons.2 ⟨subd7_3_467, List.forall_mem_cons.2 ⟨subd7_3_468, List.forall_mem_cons.2 ⟨subd7_3_469, List.forall_mem_cons.2 ⟨subd7_3_470, List.forall_mem_cons.2 ⟨subd7_3_471, List.forall_mem_cons.2 ⟨subd7_3_472, List.forall_mem_cons.2 ⟨subd7_3_473, List.forall_mem_cons.2 ⟨subd7_3_474, List.forall_mem_cons.2 ⟨subd7_3_475, List.forall_mem_cons.2 ⟨subd7_3_476, List.forall_mem_cons.2 ⟨subd7_3_477, List.forall_mem_cons.2 ⟨subd7_3_478, List.forall_mem_cons.2 ⟨subd7_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_480 : subd7_3 [0, -4, 6] = true := by decide +kernel
theorem subd7_3_481 : subd7_3 [0, -3, -8] = true := by decide +kernel
theorem subd7_3_482 : subd7_3 [0, -3, -7] = true := by decide +kernel
theorem subd7_3_483 : subd7_3 [0, -3, -6] = true := by decide +kernel
theorem subd7_3_484 : subd7_3 [0, -3, -5] = true := by decide +kernel
theorem subd7_3_485 : subd7_3 [0, -3, -4] = true := by decide +kernel
theorem subd7_3_486 : subd7_3 [0, -3, -3] = true := by decide +kernel
theorem subd7_3_487 : subd7_3 [0, -3, -2] = true := by decide +kernel
theorem subd7_3_488 : subd7_3 [0, -3, -1] = true := by decide +kernel
theorem subd7_3_489 : subd7_3 [0, -3, 0] = true := by decide +kernel
theorem subd7_3_490 : subd7_3 [0, -3, 1] = true := by decide +kernel
theorem subd7_3_491 : subd7_3 [0, -3, 2] = true := by decide +kernel
theorem subd7_3_492 : subd7_3 [0, -3, 3] = true := by decide +kernel
theorem subd7_3_493 : subd7_3 [0, -3, 4] = true := by decide +kernel
theorem subd7_3_494 : subd7_3 [0, -3, 5] = true := by decide +kernel
theorem subd7_3_495 : subd7_3 [0, -3, 6] = true := by decide +kernel
theorem subd7_3_496 : subd7_3 [0, -3, 7] = true := by decide +kernel
theorem subd7_3_497 : subd7_3 [0, -2, -8] = true := by decide +kernel
theorem subd7_3_498 : subd7_3 [0, -2, -7] = true := by decide +kernel
theorem subd7_3_499 : subd7_3 [0, -2, -6] = true := by decide +kernel
theorem subd7_3_500 : subd7_3 [0, -2, -5] = true := by decide +kernel
theorem subd7_3_501 : subd7_3 [0, -2, -4] = true := by decide +kernel
theorem subd7_3_502 : subd7_3 [0, -2, -3] = true := by decide +kernel
theorem subd7_3_503 : subd7_3 [0, -2, -2] = true := by decide +kernel
theorem subd7_3_504 : subd7_3 [0, -2, -1] = true := by decide +kernel
theorem subd7_3_505 : subd7_3 [0, -2, 0] = true := by decide +kernel
theorem subd7_3_506 : subd7_3 [0, -2, 1] = true := by decide +kernel
theorem subd7_3_507 : subd7_3 [0, -2, 2] = true := by decide +kernel
theorem subd7_3_508 : subd7_3 [0, -2, 3] = true := by decide +kernel
theorem subd7_3_509 : subd7_3 [0, -2, 4] = true := by decide +kernel
theorem subd7_3_510 : subd7_3 [0, -2, 5] = true := by decide +kernel
theorem subd7_3_511 : subd7_3 [0, -2, 6] = true := by decide +kernel
theorem sbd7_3_15 : ∀ q ∈ blkd7_3_15, subd7_3 q = true := by
  unfold blkd7_3_15
  exact List.forall_mem_cons.2 ⟨subd7_3_480, List.forall_mem_cons.2 ⟨subd7_3_481, List.forall_mem_cons.2 ⟨subd7_3_482, List.forall_mem_cons.2 ⟨subd7_3_483, List.forall_mem_cons.2 ⟨subd7_3_484, List.forall_mem_cons.2 ⟨subd7_3_485, List.forall_mem_cons.2 ⟨subd7_3_486, List.forall_mem_cons.2 ⟨subd7_3_487, List.forall_mem_cons.2 ⟨subd7_3_488, List.forall_mem_cons.2 ⟨subd7_3_489, List.forall_mem_cons.2 ⟨subd7_3_490, List.forall_mem_cons.2 ⟨subd7_3_491, List.forall_mem_cons.2 ⟨subd7_3_492, List.forall_mem_cons.2 ⟨subd7_3_493, List.forall_mem_cons.2 ⟨subd7_3_494, List.forall_mem_cons.2 ⟨subd7_3_495, List.forall_mem_cons.2 ⟨subd7_3_496, List.forall_mem_cons.2 ⟨subd7_3_497, List.forall_mem_cons.2 ⟨subd7_3_498, List.forall_mem_cons.2 ⟨subd7_3_499, List.forall_mem_cons.2 ⟨subd7_3_500, List.forall_mem_cons.2 ⟨subd7_3_501, List.forall_mem_cons.2 ⟨subd7_3_502, List.forall_mem_cons.2 ⟨subd7_3_503, List.forall_mem_cons.2 ⟨subd7_3_504, List.forall_mem_cons.2 ⟨subd7_3_505, List.forall_mem_cons.2 ⟨subd7_3_506, List.forall_mem_cons.2 ⟨subd7_3_507, List.forall_mem_cons.2 ⟨subd7_3_508, List.forall_mem_cons.2 ⟨subd7_3_509, List.forall_mem_cons.2 ⟨subd7_3_510, List.forall_mem_cons.2 ⟨subd7_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_512 : subd7_3 [0, -2, 7] = true := by decide +kernel
theorem subd7_3_513 : subd7_3 [0, -1, -9] = true := by decide +kernel
theorem subd7_3_514 : subd7_3 [0, -1, -8] = true := by decide +kernel
theorem subd7_3_515 : subd7_3 [0, -1, -7] = true := by decide +kernel
theorem subd7_3_516 : subd7_3 [0, -1, -6] = true := by decide +kernel
theorem subd7_3_517 : subd7_3 [0, -1, -5] = true := by decide +kernel
theorem subd7_3_518 : subd7_3 [0, -1, -4] = true := by decide +kernel
theorem subd7_3_519 : subd7_3 [0, -1, -3] = true := by decide +kernel
theorem subd7_3_520 : subd7_3 [0, -1, -2] = true := by decide +kernel
theorem subd7_3_521 : subd7_3 [0, -1, -1] = true := by decide +kernel
theorem subd7_3_522 : subd7_3 [0, -1, 0] = true := by decide +kernel
theorem subd7_3_523 : subd7_3 [0, -1, 1] = true := by decide +kernel
theorem subd7_3_524 : subd7_3 [0, -1, 2] = true := by decide +kernel
theorem subd7_3_525 : subd7_3 [0, -1, 3] = true := by decide +kernel
theorem subd7_3_526 : subd7_3 [0, -1, 4] = true := by decide +kernel
theorem subd7_3_527 : subd7_3 [0, -1, 5] = true := by decide +kernel
theorem subd7_3_528 : subd7_3 [0, -1, 6] = true := by decide +kernel
theorem subd7_3_529 : subd7_3 [0, -1, 7] = true := by decide +kernel
theorem subd7_3_530 : subd7_3 [0, -1, 8] = true := by decide +kernel
theorem subd7_3_531 : subd7_3 [0, 0, -9] = true := by decide +kernel
theorem subd7_3_532 : subd7_3 [0, 0, -8] = true := by decide +kernel
theorem subd7_3_533 : subd7_3 [0, 0, -7] = true := by decide +kernel
theorem subd7_3_534 : subd7_3 [0, 0, -6] = true := by decide +kernel
theorem subd7_3_535 : subd7_3 [0, 0, -5] = true := by decide +kernel
theorem subd7_3_536 : subd7_3 [0, 0, -4] = true := by decide +kernel
theorem subd7_3_537 : subd7_3 [0, 0, -3] = true := by decide +kernel
theorem subd7_3_538 : subd7_3 [0, 0, -2] = true := by decide +kernel
theorem subd7_3_539 : subd7_3 [0, 0, -1] = true := by decide +kernel
theorem subd7_3_540 : subd7_3 [0, 0, 0] = true := by decide +kernel
theorem subd7_3_541 : subd7_3 [0, 0, 1] = true := by decide +kernel
theorem subd7_3_542 : subd7_3 [0, 0, 2] = true := by decide +kernel
theorem subd7_3_543 : subd7_3 [0, 0, 3] = true := by decide +kernel
theorem sbd7_3_16 : ∀ q ∈ blkd7_3_16, subd7_3 q = true := by
  unfold blkd7_3_16
  exact List.forall_mem_cons.2 ⟨subd7_3_512, List.forall_mem_cons.2 ⟨subd7_3_513, List.forall_mem_cons.2 ⟨subd7_3_514, List.forall_mem_cons.2 ⟨subd7_3_515, List.forall_mem_cons.2 ⟨subd7_3_516, List.forall_mem_cons.2 ⟨subd7_3_517, List.forall_mem_cons.2 ⟨subd7_3_518, List.forall_mem_cons.2 ⟨subd7_3_519, List.forall_mem_cons.2 ⟨subd7_3_520, List.forall_mem_cons.2 ⟨subd7_3_521, List.forall_mem_cons.2 ⟨subd7_3_522, List.forall_mem_cons.2 ⟨subd7_3_523, List.forall_mem_cons.2 ⟨subd7_3_524, List.forall_mem_cons.2 ⟨subd7_3_525, List.forall_mem_cons.2 ⟨subd7_3_526, List.forall_mem_cons.2 ⟨subd7_3_527, List.forall_mem_cons.2 ⟨subd7_3_528, List.forall_mem_cons.2 ⟨subd7_3_529, List.forall_mem_cons.2 ⟨subd7_3_530, List.forall_mem_cons.2 ⟨subd7_3_531, List.forall_mem_cons.2 ⟨subd7_3_532, List.forall_mem_cons.2 ⟨subd7_3_533, List.forall_mem_cons.2 ⟨subd7_3_534, List.forall_mem_cons.2 ⟨subd7_3_535, List.forall_mem_cons.2 ⟨subd7_3_536, List.forall_mem_cons.2 ⟨subd7_3_537, List.forall_mem_cons.2 ⟨subd7_3_538, List.forall_mem_cons.2 ⟨subd7_3_539, List.forall_mem_cons.2 ⟨subd7_3_540, List.forall_mem_cons.2 ⟨subd7_3_541, List.forall_mem_cons.2 ⟨subd7_3_542, List.forall_mem_cons.2 ⟨subd7_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_544 : subd7_3 [0, 0, 4] = true := by decide +kernel
theorem subd7_3_545 : subd7_3 [0, 0, 5] = true := by decide +kernel
theorem subd7_3_546 : subd7_3 [0, 0, 6] = true := by decide +kernel
theorem subd7_3_547 : subd7_3 [0, 0, 7] = true := by decide +kernel
theorem subd7_3_548 : subd7_3 [0, 0, 8] = true := by decide +kernel
theorem subd7_3_549 : subd7_3 [0, 1, -9] = true := by decide +kernel
theorem subd7_3_550 : subd7_3 [0, 1, -8] = true := by decide +kernel
theorem subd7_3_551 : subd7_3 [0, 1, -7] = true := by decide +kernel
theorem subd7_3_552 : subd7_3 [0, 1, -6] = true := by decide +kernel
theorem subd7_3_553 : subd7_3 [0, 1, -5] = true := by decide +kernel
theorem subd7_3_554 : subd7_3 [0, 1, -4] = true := by decide +kernel
theorem subd7_3_555 : subd7_3 [0, 1, -3] = true := by decide +kernel
theorem subd7_3_556 : subd7_3 [0, 1, -2] = true := by decide +kernel
theorem subd7_3_557 : subd7_3 [0, 1, -1] = true := by decide +kernel
theorem subd7_3_558 : subd7_3 [0, 1, 0] = true := by decide +kernel
theorem subd7_3_559 : subd7_3 [0, 1, 1] = true := by decide +kernel
theorem subd7_3_560 : subd7_3 [0, 1, 2] = true := by decide +kernel
theorem subd7_3_561 : subd7_3 [0, 1, 3] = true := by decide +kernel
theorem subd7_3_562 : subd7_3 [0, 1, 4] = true := by decide +kernel
theorem subd7_3_563 : subd7_3 [0, 1, 5] = true := by decide +kernel
theorem subd7_3_564 : subd7_3 [0, 1, 6] = true := by decide +kernel
theorem subd7_3_565 : subd7_3 [0, 1, 7] = true := by decide +kernel
theorem subd7_3_566 : subd7_3 [0, 1, 8] = true := by decide +kernel
theorem subd7_3_567 : subd7_3 [0, 2, -8] = true := by decide +kernel
theorem subd7_3_568 : subd7_3 [0, 2, -7] = true := by decide +kernel
theorem subd7_3_569 : subd7_3 [0, 2, -6] = true := by decide +kernel
theorem subd7_3_570 : subd7_3 [0, 2, -5] = true := by decide +kernel
theorem subd7_3_571 : subd7_3 [0, 2, -4] = true := by decide +kernel
theorem subd7_3_572 : subd7_3 [0, 2, -3] = true := by decide +kernel
theorem subd7_3_573 : subd7_3 [0, 2, -2] = true := by decide +kernel
theorem subd7_3_574 : subd7_3 [0, 2, -1] = true := by decide +kernel
theorem subd7_3_575 : subd7_3 [0, 2, 0] = true := by decide +kernel
theorem sbd7_3_17 : ∀ q ∈ blkd7_3_17, subd7_3 q = true := by
  unfold blkd7_3_17
  exact List.forall_mem_cons.2 ⟨subd7_3_544, List.forall_mem_cons.2 ⟨subd7_3_545, List.forall_mem_cons.2 ⟨subd7_3_546, List.forall_mem_cons.2 ⟨subd7_3_547, List.forall_mem_cons.2 ⟨subd7_3_548, List.forall_mem_cons.2 ⟨subd7_3_549, List.forall_mem_cons.2 ⟨subd7_3_550, List.forall_mem_cons.2 ⟨subd7_3_551, List.forall_mem_cons.2 ⟨subd7_3_552, List.forall_mem_cons.2 ⟨subd7_3_553, List.forall_mem_cons.2 ⟨subd7_3_554, List.forall_mem_cons.2 ⟨subd7_3_555, List.forall_mem_cons.2 ⟨subd7_3_556, List.forall_mem_cons.2 ⟨subd7_3_557, List.forall_mem_cons.2 ⟨subd7_3_558, List.forall_mem_cons.2 ⟨subd7_3_559, List.forall_mem_cons.2 ⟨subd7_3_560, List.forall_mem_cons.2 ⟨subd7_3_561, List.forall_mem_cons.2 ⟨subd7_3_562, List.forall_mem_cons.2 ⟨subd7_3_563, List.forall_mem_cons.2 ⟨subd7_3_564, List.forall_mem_cons.2 ⟨subd7_3_565, List.forall_mem_cons.2 ⟨subd7_3_566, List.forall_mem_cons.2 ⟨subd7_3_567, List.forall_mem_cons.2 ⟨subd7_3_568, List.forall_mem_cons.2 ⟨subd7_3_569, List.forall_mem_cons.2 ⟨subd7_3_570, List.forall_mem_cons.2 ⟨subd7_3_571, List.forall_mem_cons.2 ⟨subd7_3_572, List.forall_mem_cons.2 ⟨subd7_3_573, List.forall_mem_cons.2 ⟨subd7_3_574, List.forall_mem_cons.2 ⟨subd7_3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_576 : subd7_3 [0, 2, 1] = true := by decide +kernel
theorem subd7_3_577 : subd7_3 [0, 2, 2] = true := by decide +kernel
theorem subd7_3_578 : subd7_3 [0, 2, 3] = true := by decide +kernel
theorem subd7_3_579 : subd7_3 [0, 2, 4] = true := by decide +kernel
theorem subd7_3_580 : subd7_3 [0, 2, 5] = true := by decide +kernel
theorem subd7_3_581 : subd7_3 [0, 2, 6] = true := by decide +kernel
theorem subd7_3_582 : subd7_3 [0, 2, 7] = true := by decide +kernel
theorem subd7_3_583 : subd7_3 [0, 3, -8] = true := by decide +kernel
theorem subd7_3_584 : subd7_3 [0, 3, -7] = true := by decide +kernel
theorem subd7_3_585 : subd7_3 [0, 3, -6] = true := by decide +kernel
theorem subd7_3_586 : subd7_3 [0, 3, -5] = true := by decide +kernel
theorem subd7_3_587 : subd7_3 [0, 3, -4] = true := by decide +kernel
theorem subd7_3_588 : subd7_3 [0, 3, -3] = true := by decide +kernel
theorem subd7_3_589 : subd7_3 [0, 3, -2] = true := by decide +kernel
theorem subd7_3_590 : subd7_3 [0, 3, -1] = true := by decide +kernel
theorem subd7_3_591 : subd7_3 [0, 3, 0] = true := by decide +kernel
theorem subd7_3_592 : subd7_3 [0, 3, 1] = true := by decide +kernel
theorem subd7_3_593 : subd7_3 [0, 3, 2] = true := by decide +kernel
theorem subd7_3_594 : subd7_3 [0, 3, 3] = true := by decide +kernel
theorem subd7_3_595 : subd7_3 [0, 3, 4] = true := by decide +kernel
theorem subd7_3_596 : subd7_3 [0, 3, 5] = true := by decide +kernel
theorem subd7_3_597 : subd7_3 [0, 3, 6] = true := by decide +kernel
theorem subd7_3_598 : subd7_3 [0, 3, 7] = true := by decide +kernel
theorem subd7_3_599 : subd7_3 [0, 4, -7] = true := by decide +kernel
theorem subd7_3_600 : subd7_3 [0, 4, -6] = true := by decide +kernel
theorem subd7_3_601 : subd7_3 [0, 4, -5] = true := by decide +kernel
theorem subd7_3_602 : subd7_3 [0, 4, -4] = true := by decide +kernel
theorem subd7_3_603 : subd7_3 [0, 4, -3] = true := by decide +kernel
theorem subd7_3_604 : subd7_3 [0, 4, -2] = true := by decide +kernel
theorem subd7_3_605 : subd7_3 [0, 4, -1] = true := by decide +kernel
theorem subd7_3_606 : subd7_3 [0, 4, 0] = true := by decide +kernel
theorem subd7_3_607 : subd7_3 [0, 4, 1] = true := by decide +kernel
theorem sbd7_3_18 : ∀ q ∈ blkd7_3_18, subd7_3 q = true := by
  unfold blkd7_3_18
  exact List.forall_mem_cons.2 ⟨subd7_3_576, List.forall_mem_cons.2 ⟨subd7_3_577, List.forall_mem_cons.2 ⟨subd7_3_578, List.forall_mem_cons.2 ⟨subd7_3_579, List.forall_mem_cons.2 ⟨subd7_3_580, List.forall_mem_cons.2 ⟨subd7_3_581, List.forall_mem_cons.2 ⟨subd7_3_582, List.forall_mem_cons.2 ⟨subd7_3_583, List.forall_mem_cons.2 ⟨subd7_3_584, List.forall_mem_cons.2 ⟨subd7_3_585, List.forall_mem_cons.2 ⟨subd7_3_586, List.forall_mem_cons.2 ⟨subd7_3_587, List.forall_mem_cons.2 ⟨subd7_3_588, List.forall_mem_cons.2 ⟨subd7_3_589, List.forall_mem_cons.2 ⟨subd7_3_590, List.forall_mem_cons.2 ⟨subd7_3_591, List.forall_mem_cons.2 ⟨subd7_3_592, List.forall_mem_cons.2 ⟨subd7_3_593, List.forall_mem_cons.2 ⟨subd7_3_594, List.forall_mem_cons.2 ⟨subd7_3_595, List.forall_mem_cons.2 ⟨subd7_3_596, List.forall_mem_cons.2 ⟨subd7_3_597, List.forall_mem_cons.2 ⟨subd7_3_598, List.forall_mem_cons.2 ⟨subd7_3_599, List.forall_mem_cons.2 ⟨subd7_3_600, List.forall_mem_cons.2 ⟨subd7_3_601, List.forall_mem_cons.2 ⟨subd7_3_602, List.forall_mem_cons.2 ⟨subd7_3_603, List.forall_mem_cons.2 ⟨subd7_3_604, List.forall_mem_cons.2 ⟨subd7_3_605, List.forall_mem_cons.2 ⟨subd7_3_606, List.forall_mem_cons.2 ⟨subd7_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_608 : subd7_3 [0, 4, 2] = true := by decide +kernel
theorem subd7_3_609 : subd7_3 [0, 4, 3] = true := by decide +kernel
theorem subd7_3_610 : subd7_3 [0, 4, 4] = true := by decide +kernel
theorem subd7_3_611 : subd7_3 [0, 4, 5] = true := by decide +kernel
theorem subd7_3_612 : subd7_3 [0, 4, 6] = true := by decide +kernel
theorem subd7_3_613 : subd7_3 [0, 5] = true := by decide +kernel
theorem subd7_3_614 : subd7_3 [0, 6] = true := by decide +kernel
theorem subd7_3_615 : subd7_3 [0, 7] = true := by decide +kernel
theorem subd7_3_616 : subd7_3 [1, -7] = true := by decide +kernel
theorem subd7_3_617 : subd7_3 [1, -6] = true := by decide +kernel
theorem subd7_3_618 : subd7_3 [1, -5] = true := by decide +kernel
theorem subd7_3_619 : subd7_3 [1, -4, -7] = true := by decide +kernel
theorem subd7_3_620 : subd7_3 [1, -4, -6] = true := by decide +kernel
theorem subd7_3_621 : subd7_3 [1, -4, -5] = true := by decide +kernel
theorem subd7_3_622 : subd7_3 [1, -4, -4] = true := by decide +kernel
theorem subd7_3_623 : subd7_3 [1, -4, -3] = true := by decide +kernel
theorem subd7_3_624 : subd7_3 [1, -4, -2] = true := by decide +kernel
theorem subd7_3_625 : subd7_3 [1, -4, -1] = true := by decide +kernel
theorem subd7_3_626 : subd7_3 [1, -4, 0] = true := by decide +kernel
theorem subd7_3_627 : subd7_3 [1, -4, 1] = true := by decide +kernel
theorem subd7_3_628 : subd7_3 [1, -4, 2] = true := by decide +kernel
theorem subd7_3_629 : subd7_3 [1, -4, 3] = true := by decide +kernel
theorem subd7_3_630 : subd7_3 [1, -4, 4] = true := by decide +kernel
theorem subd7_3_631 : subd7_3 [1, -4, 5] = true := by decide +kernel
theorem subd7_3_632 : subd7_3 [1, -4, 6] = true := by decide +kernel
theorem subd7_3_633 : subd7_3 [1, -3, -7] = true := by decide +kernel
theorem subd7_3_634 : subd7_3 [1, -3, -6] = true := by decide +kernel
theorem subd7_3_635 : subd7_3 [1, -3, -5] = true := by decide +kernel
theorem subd7_3_636 : subd7_3 [1, -3, -4] = true := by decide +kernel
theorem subd7_3_637 : subd7_3 [1, -3, -3] = true := by decide +kernel
theorem subd7_3_638 : subd7_3 [1, -3, -2] = true := by decide +kernel
theorem subd7_3_639 : subd7_3 [1, -3, -1] = true := by decide +kernel
theorem sbd7_3_19 : ∀ q ∈ blkd7_3_19, subd7_3 q = true := by
  unfold blkd7_3_19
  exact List.forall_mem_cons.2 ⟨subd7_3_608, List.forall_mem_cons.2 ⟨subd7_3_609, List.forall_mem_cons.2 ⟨subd7_3_610, List.forall_mem_cons.2 ⟨subd7_3_611, List.forall_mem_cons.2 ⟨subd7_3_612, List.forall_mem_cons.2 ⟨subd7_3_613, List.forall_mem_cons.2 ⟨subd7_3_614, List.forall_mem_cons.2 ⟨subd7_3_615, List.forall_mem_cons.2 ⟨subd7_3_616, List.forall_mem_cons.2 ⟨subd7_3_617, List.forall_mem_cons.2 ⟨subd7_3_618, List.forall_mem_cons.2 ⟨subd7_3_619, List.forall_mem_cons.2 ⟨subd7_3_620, List.forall_mem_cons.2 ⟨subd7_3_621, List.forall_mem_cons.2 ⟨subd7_3_622, List.forall_mem_cons.2 ⟨subd7_3_623, List.forall_mem_cons.2 ⟨subd7_3_624, List.forall_mem_cons.2 ⟨subd7_3_625, List.forall_mem_cons.2 ⟨subd7_3_626, List.forall_mem_cons.2 ⟨subd7_3_627, List.forall_mem_cons.2 ⟨subd7_3_628, List.forall_mem_cons.2 ⟨subd7_3_629, List.forall_mem_cons.2 ⟨subd7_3_630, List.forall_mem_cons.2 ⟨subd7_3_631, List.forall_mem_cons.2 ⟨subd7_3_632, List.forall_mem_cons.2 ⟨subd7_3_633, List.forall_mem_cons.2 ⟨subd7_3_634, List.forall_mem_cons.2 ⟨subd7_3_635, List.forall_mem_cons.2 ⟨subd7_3_636, List.forall_mem_cons.2 ⟨subd7_3_637, List.forall_mem_cons.2 ⟨subd7_3_638, List.forall_mem_cons.2 ⟨subd7_3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_640 : subd7_3 [1, -3, 0] = true := by decide +kernel
theorem subd7_3_641 : subd7_3 [1, -3, 1] = true := by decide +kernel
theorem subd7_3_642 : subd7_3 [1, -3, 2] = true := by decide +kernel
theorem subd7_3_643 : subd7_3 [1, -3, 3] = true := by decide +kernel
theorem subd7_3_644 : subd7_3 [1, -3, 4] = true := by decide +kernel
theorem subd7_3_645 : subd7_3 [1, -3, 5] = true := by decide +kernel
theorem subd7_3_646 : subd7_3 [1, -3, 6] = true := by decide +kernel
theorem subd7_3_647 : subd7_3 [1, -3, 7] = true := by decide +kernel
theorem subd7_3_648 : subd7_3 [1, -2, -8] = true := by decide +kernel
theorem subd7_3_649 : subd7_3 [1, -2, -7] = true := by decide +kernel
theorem subd7_3_650 : subd7_3 [1, -2, -6] = true := by decide +kernel
theorem subd7_3_651 : subd7_3 [1, -2, -5] = true := by decide +kernel
theorem subd7_3_652 : subd7_3 [1, -2, -4] = true := by decide +kernel
theorem subd7_3_653 : subd7_3 [1, -2, -3] = true := by decide +kernel
theorem subd7_3_654 : subd7_3 [1, -2, -2] = true := by decide +kernel
theorem subd7_3_655 : subd7_3 [1, -2, -1] = true := by decide +kernel
theorem subd7_3_656 : subd7_3 [1, -2, 0] = true := by decide +kernel
theorem subd7_3_657 : subd7_3 [1, -2, 1] = true := by decide +kernel
theorem subd7_3_658 : subd7_3 [1, -2, 2] = true := by decide +kernel
theorem subd7_3_659 : subd7_3 [1, -2, 3] = true := by decide +kernel
theorem subd7_3_660 : subd7_3 [1, -2, 4] = true := by decide +kernel
theorem subd7_3_661 : subd7_3 [1, -2, 5] = true := by decide +kernel
theorem subd7_3_662 : subd7_3 [1, -2, 6] = true := by decide +kernel
theorem subd7_3_663 : subd7_3 [1, -2, 7] = true := by decide +kernel
theorem subd7_3_664 : subd7_3 [1, -2, 8] = true := by decide +kernel
theorem subd7_3_665 : subd7_3 [1, -1, -8] = true := by decide +kernel
theorem subd7_3_666 : subd7_3 [1, -1, -7] = true := by decide +kernel
theorem subd7_3_667 : subd7_3 [1, -1, -6] = true := by decide +kernel
theorem subd7_3_668 : subd7_3 [1, -1, -5] = true := by decide +kernel
theorem subd7_3_669 : subd7_3 [1, -1, -4] = true := by decide +kernel
theorem subd7_3_670 : subd7_3 [1, -1, -3] = true := by decide +kernel
theorem subd7_3_671 : subd7_3 [1, -1, -2] = true := by decide +kernel
theorem sbd7_3_20 : ∀ q ∈ blkd7_3_20, subd7_3 q = true := by
  unfold blkd7_3_20
  exact List.forall_mem_cons.2 ⟨subd7_3_640, List.forall_mem_cons.2 ⟨subd7_3_641, List.forall_mem_cons.2 ⟨subd7_3_642, List.forall_mem_cons.2 ⟨subd7_3_643, List.forall_mem_cons.2 ⟨subd7_3_644, List.forall_mem_cons.2 ⟨subd7_3_645, List.forall_mem_cons.2 ⟨subd7_3_646, List.forall_mem_cons.2 ⟨subd7_3_647, List.forall_mem_cons.2 ⟨subd7_3_648, List.forall_mem_cons.2 ⟨subd7_3_649, List.forall_mem_cons.2 ⟨subd7_3_650, List.forall_mem_cons.2 ⟨subd7_3_651, List.forall_mem_cons.2 ⟨subd7_3_652, List.forall_mem_cons.2 ⟨subd7_3_653, List.forall_mem_cons.2 ⟨subd7_3_654, List.forall_mem_cons.2 ⟨subd7_3_655, List.forall_mem_cons.2 ⟨subd7_3_656, List.forall_mem_cons.2 ⟨subd7_3_657, List.forall_mem_cons.2 ⟨subd7_3_658, List.forall_mem_cons.2 ⟨subd7_3_659, List.forall_mem_cons.2 ⟨subd7_3_660, List.forall_mem_cons.2 ⟨subd7_3_661, List.forall_mem_cons.2 ⟨subd7_3_662, List.forall_mem_cons.2 ⟨subd7_3_663, List.forall_mem_cons.2 ⟨subd7_3_664, List.forall_mem_cons.2 ⟨subd7_3_665, List.forall_mem_cons.2 ⟨subd7_3_666, List.forall_mem_cons.2 ⟨subd7_3_667, List.forall_mem_cons.2 ⟨subd7_3_668, List.forall_mem_cons.2 ⟨subd7_3_669, List.forall_mem_cons.2 ⟨subd7_3_670, List.forall_mem_cons.2 ⟨subd7_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_672 : subd7_3 [1, -1, -1] = true := by decide +kernel
theorem subd7_3_673 : subd7_3 [1, -1, 0] = true := by decide +kernel
theorem subd7_3_674 : subd7_3 [1, -1, 1] = true := by decide +kernel
theorem subd7_3_675 : subd7_3 [1, -1, 2] = true := by decide +kernel
theorem subd7_3_676 : subd7_3 [1, -1, 3] = true := by decide +kernel
theorem subd7_3_677 : subd7_3 [1, -1, 4] = true := by decide +kernel
theorem subd7_3_678 : subd7_3 [1, -1, 5] = true := by decide +kernel
theorem subd7_3_679 : subd7_3 [1, -1, 6] = true := by decide +kernel
theorem subd7_3_680 : subd7_3 [1, -1, 7] = true := by decide +kernel
theorem subd7_3_681 : subd7_3 [1, -1, 8] = true := by decide +kernel
theorem subd7_3_682 : subd7_3 [1, 0, -8] = true := by decide +kernel
theorem subd7_3_683 : subd7_3 [1, 0, -7] = true := by decide +kernel
theorem subd7_3_684 : subd7_3 [1, 0, -6] = true := by decide +kernel
theorem subd7_3_685 : subd7_3 [1, 0, -5] = true := by decide +kernel
theorem subd7_3_686 : subd7_3 [1, 0, -4] = true := by decide +kernel
theorem subd7_3_687 : subd7_3 [1, 0, -3] = true := by decide +kernel
theorem subd7_3_688 : subd7_3 [1, 0, -2] = true := by decide +kernel
theorem subd7_3_689 : subd7_3 [1, 0, -1] = true := by decide +kernel
theorem subd7_3_690 : subd7_3 [1, 0, 0] = true := by decide +kernel
theorem subd7_3_691 : subd7_3 [1, 0, 1] = true := by decide +kernel
theorem subd7_3_692 : subd7_3 [1, 0, 2] = true := by decide +kernel
theorem subd7_3_693 : subd7_3 [1, 0, 3] = true := by decide +kernel
theorem subd7_3_694 : subd7_3 [1, 0, 4] = true := by decide +kernel
theorem subd7_3_695 : subd7_3 [1, 0, 5] = true := by decide +kernel
theorem subd7_3_696 : subd7_3 [1, 0, 6] = true := by decide +kernel
theorem subd7_3_697 : subd7_3 [1, 0, 7] = true := by decide +kernel
theorem subd7_3_698 : subd7_3 [1, 0, 8] = true := by decide +kernel
theorem subd7_3_699 : subd7_3 [1, 1, -8] = true := by decide +kernel
theorem subd7_3_700 : subd7_3 [1, 1, -7] = true := by decide +kernel
theorem subd7_3_701 : subd7_3 [1, 1, -6] = true := by decide +kernel
theorem subd7_3_702 : subd7_3 [1, 1, -5] = true := by decide +kernel
theorem subd7_3_703 : subd7_3 [1, 1, -4] = true := by decide +kernel
theorem sbd7_3_21 : ∀ q ∈ blkd7_3_21, subd7_3 q = true := by
  unfold blkd7_3_21
  exact List.forall_mem_cons.2 ⟨subd7_3_672, List.forall_mem_cons.2 ⟨subd7_3_673, List.forall_mem_cons.2 ⟨subd7_3_674, List.forall_mem_cons.2 ⟨subd7_3_675, List.forall_mem_cons.2 ⟨subd7_3_676, List.forall_mem_cons.2 ⟨subd7_3_677, List.forall_mem_cons.2 ⟨subd7_3_678, List.forall_mem_cons.2 ⟨subd7_3_679, List.forall_mem_cons.2 ⟨subd7_3_680, List.forall_mem_cons.2 ⟨subd7_3_681, List.forall_mem_cons.2 ⟨subd7_3_682, List.forall_mem_cons.2 ⟨subd7_3_683, List.forall_mem_cons.2 ⟨subd7_3_684, List.forall_mem_cons.2 ⟨subd7_3_685, List.forall_mem_cons.2 ⟨subd7_3_686, List.forall_mem_cons.2 ⟨subd7_3_687, List.forall_mem_cons.2 ⟨subd7_3_688, List.forall_mem_cons.2 ⟨subd7_3_689, List.forall_mem_cons.2 ⟨subd7_3_690, List.forall_mem_cons.2 ⟨subd7_3_691, List.forall_mem_cons.2 ⟨subd7_3_692, List.forall_mem_cons.2 ⟨subd7_3_693, List.forall_mem_cons.2 ⟨subd7_3_694, List.forall_mem_cons.2 ⟨subd7_3_695, List.forall_mem_cons.2 ⟨subd7_3_696, List.forall_mem_cons.2 ⟨subd7_3_697, List.forall_mem_cons.2 ⟨subd7_3_698, List.forall_mem_cons.2 ⟨subd7_3_699, List.forall_mem_cons.2 ⟨subd7_3_700, List.forall_mem_cons.2 ⟨subd7_3_701, List.forall_mem_cons.2 ⟨subd7_3_702, List.forall_mem_cons.2 ⟨subd7_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_704 : subd7_3 [1, 1, -3] = true := by decide +kernel
theorem subd7_3_705 : subd7_3 [1, 1, -2] = true := by decide +kernel
theorem subd7_3_706 : subd7_3 [1, 1, -1] = true := by decide +kernel
theorem subd7_3_707 : subd7_3 [1, 1, 0] = true := by decide +kernel
theorem subd7_3_708 : subd7_3 [1, 1, 1] = true := by decide +kernel
theorem subd7_3_709 : subd7_3 [1, 1, 2] = true := by decide +kernel
theorem subd7_3_710 : subd7_3 [1, 1, 3] = true := by decide +kernel
theorem subd7_3_711 : subd7_3 [1, 1, 4] = true := by decide +kernel
theorem subd7_3_712 : subd7_3 [1, 1, 5] = true := by decide +kernel
theorem subd7_3_713 : subd7_3 [1, 1, 6] = true := by decide +kernel
theorem subd7_3_714 : subd7_3 [1, 1, 7] = true := by decide +kernel
theorem subd7_3_715 : subd7_3 [1, 1, 8] = true := by decide +kernel
theorem subd7_3_716 : subd7_3 [1, 2, -8] = true := by decide +kernel
theorem subd7_3_717 : subd7_3 [1, 2, -7] = true := by decide +kernel
theorem subd7_3_718 : subd7_3 [1, 2, -6] = true := by decide +kernel
theorem subd7_3_719 : subd7_3 [1, 2, -5] = true := by decide +kernel
theorem subd7_3_720 : subd7_3 [1, 2, -4] = true := by decide +kernel
theorem subd7_3_721 : subd7_3 [1, 2, -3] = true := by decide +kernel
theorem subd7_3_722 : subd7_3 [1, 2, -2] = true := by decide +kernel
theorem subd7_3_723 : subd7_3 [1, 2, -1] = true := by decide +kernel
theorem subd7_3_724 : subd7_3 [1, 2, 0] = true := by decide +kernel
theorem subd7_3_725 : subd7_3 [1, 2, 1] = true := by decide +kernel
theorem subd7_3_726 : subd7_3 [1, 2, 2] = true := by decide +kernel
theorem subd7_3_727 : subd7_3 [1, 2, 3] = true := by decide +kernel
theorem subd7_3_728 : subd7_3 [1, 2, 4] = true := by decide +kernel
theorem subd7_3_729 : subd7_3 [1, 2, 5] = true := by decide +kernel
theorem subd7_3_730 : subd7_3 [1, 2, 6] = true := by decide +kernel
theorem subd7_3_731 : subd7_3 [1, 2, 7] = true := by decide +kernel
theorem subd7_3_732 : subd7_3 [1, 2, 8] = true := by decide +kernel
theorem subd7_3_733 : subd7_3 [1, 3, -7] = true := by decide +kernel
theorem subd7_3_734 : subd7_3 [1, 3, -6] = true := by decide +kernel
theorem subd7_3_735 : subd7_3 [1, 3, -5] = true := by decide +kernel
theorem sbd7_3_22 : ∀ q ∈ blkd7_3_22, subd7_3 q = true := by
  unfold blkd7_3_22
  exact List.forall_mem_cons.2 ⟨subd7_3_704, List.forall_mem_cons.2 ⟨subd7_3_705, List.forall_mem_cons.2 ⟨subd7_3_706, List.forall_mem_cons.2 ⟨subd7_3_707, List.forall_mem_cons.2 ⟨subd7_3_708, List.forall_mem_cons.2 ⟨subd7_3_709, List.forall_mem_cons.2 ⟨subd7_3_710, List.forall_mem_cons.2 ⟨subd7_3_711, List.forall_mem_cons.2 ⟨subd7_3_712, List.forall_mem_cons.2 ⟨subd7_3_713, List.forall_mem_cons.2 ⟨subd7_3_714, List.forall_mem_cons.2 ⟨subd7_3_715, List.forall_mem_cons.2 ⟨subd7_3_716, List.forall_mem_cons.2 ⟨subd7_3_717, List.forall_mem_cons.2 ⟨subd7_3_718, List.forall_mem_cons.2 ⟨subd7_3_719, List.forall_mem_cons.2 ⟨subd7_3_720, List.forall_mem_cons.2 ⟨subd7_3_721, List.forall_mem_cons.2 ⟨subd7_3_722, List.forall_mem_cons.2 ⟨subd7_3_723, List.forall_mem_cons.2 ⟨subd7_3_724, List.forall_mem_cons.2 ⟨subd7_3_725, List.forall_mem_cons.2 ⟨subd7_3_726, List.forall_mem_cons.2 ⟨subd7_3_727, List.forall_mem_cons.2 ⟨subd7_3_728, List.forall_mem_cons.2 ⟨subd7_3_729, List.forall_mem_cons.2 ⟨subd7_3_730, List.forall_mem_cons.2 ⟨subd7_3_731, List.forall_mem_cons.2 ⟨subd7_3_732, List.forall_mem_cons.2 ⟨subd7_3_733, List.forall_mem_cons.2 ⟨subd7_3_734, List.forall_mem_cons.2 ⟨subd7_3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_736 : subd7_3 [1, 3, -4] = true := by decide +kernel
theorem subd7_3_737 : subd7_3 [1, 3, -3] = true := by decide +kernel
theorem subd7_3_738 : subd7_3 [1, 3, -2] = true := by decide +kernel
theorem subd7_3_739 : subd7_3 [1, 3, -1] = true := by decide +kernel
theorem subd7_3_740 : subd7_3 [1, 3, 0] = true := by decide +kernel
theorem subd7_3_741 : subd7_3 [1, 3, 1] = true := by decide +kernel
theorem subd7_3_742 : subd7_3 [1, 3, 2] = true := by decide +kernel
theorem subd7_3_743 : subd7_3 [1, 3, 3] = true := by decide +kernel
theorem subd7_3_744 : subd7_3 [1, 3, 4] = true := by decide +kernel
theorem subd7_3_745 : subd7_3 [1, 3, 5] = true := by decide +kernel
theorem subd7_3_746 : subd7_3 [1, 3, 6] = true := by decide +kernel
theorem subd7_3_747 : subd7_3 [1, 3, 7] = true := by decide +kernel
theorem subd7_3_748 : subd7_3 [1, 4, -7] = true := by decide +kernel
theorem subd7_3_749 : subd7_3 [1, 4, -6] = true := by decide +kernel
theorem subd7_3_750 : subd7_3 [1, 4, -5] = true := by decide +kernel
theorem subd7_3_751 : subd7_3 [1, 4, -4] = true := by decide +kernel
theorem subd7_3_752 : subd7_3 [1, 4, -3] = true := by decide +kernel
theorem subd7_3_753 : subd7_3 [1, 4, -2] = true := by decide +kernel
theorem subd7_3_754 : subd7_3 [1, 4, -1] = true := by decide +kernel
theorem subd7_3_755 : subd7_3 [1, 4, 0] = true := by decide +kernel
theorem subd7_3_756 : subd7_3 [1, 4, 1] = true := by decide +kernel
theorem subd7_3_757 : subd7_3 [1, 4, 2] = true := by decide +kernel
theorem subd7_3_758 : subd7_3 [1, 4, 3] = true := by decide +kernel
theorem subd7_3_759 : subd7_3 [1, 4, 4] = true := by decide +kernel
theorem subd7_3_760 : subd7_3 [1, 4, 5] = true := by decide +kernel
theorem subd7_3_761 : subd7_3 [1, 4, 6] = true := by decide +kernel
theorem subd7_3_762 : subd7_3 [1, 4, 7] = true := by decide +kernel
theorem subd7_3_763 : subd7_3 [1, 5] = true := by decide +kernel
theorem subd7_3_764 : subd7_3 [1, 6] = true := by decide +kernel
theorem subd7_3_765 : subd7_3 [1, 7] = true := by decide +kernel
theorem subd7_3_766 : subd7_3 [2, -7] = true := by decide +kernel
theorem subd7_3_767 : subd7_3 [2, -6] = true := by decide +kernel
theorem sbd7_3_23 : ∀ q ∈ blkd7_3_23, subd7_3 q = true := by
  unfold blkd7_3_23
  exact List.forall_mem_cons.2 ⟨subd7_3_736, List.forall_mem_cons.2 ⟨subd7_3_737, List.forall_mem_cons.2 ⟨subd7_3_738, List.forall_mem_cons.2 ⟨subd7_3_739, List.forall_mem_cons.2 ⟨subd7_3_740, List.forall_mem_cons.2 ⟨subd7_3_741, List.forall_mem_cons.2 ⟨subd7_3_742, List.forall_mem_cons.2 ⟨subd7_3_743, List.forall_mem_cons.2 ⟨subd7_3_744, List.forall_mem_cons.2 ⟨subd7_3_745, List.forall_mem_cons.2 ⟨subd7_3_746, List.forall_mem_cons.2 ⟨subd7_3_747, List.forall_mem_cons.2 ⟨subd7_3_748, List.forall_mem_cons.2 ⟨subd7_3_749, List.forall_mem_cons.2 ⟨subd7_3_750, List.forall_mem_cons.2 ⟨subd7_3_751, List.forall_mem_cons.2 ⟨subd7_3_752, List.forall_mem_cons.2 ⟨subd7_3_753, List.forall_mem_cons.2 ⟨subd7_3_754, List.forall_mem_cons.2 ⟨subd7_3_755, List.forall_mem_cons.2 ⟨subd7_3_756, List.forall_mem_cons.2 ⟨subd7_3_757, List.forall_mem_cons.2 ⟨subd7_3_758, List.forall_mem_cons.2 ⟨subd7_3_759, List.forall_mem_cons.2 ⟨subd7_3_760, List.forall_mem_cons.2 ⟨subd7_3_761, List.forall_mem_cons.2 ⟨subd7_3_762, List.forall_mem_cons.2 ⟨subd7_3_763, List.forall_mem_cons.2 ⟨subd7_3_764, List.forall_mem_cons.2 ⟨subd7_3_765, List.forall_mem_cons.2 ⟨subd7_3_766, List.forall_mem_cons.2 ⟨subd7_3_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_768 : subd7_3 [2, -5] = true := by decide +kernel
theorem subd7_3_769 : subd7_3 [2, -4] = true := by decide +kernel
theorem subd7_3_770 : subd7_3 [2, -3, -7] = true := by decide +kernel
theorem subd7_3_771 : subd7_3 [2, -3, -6] = true := by decide +kernel
theorem subd7_3_772 : subd7_3 [2, -3, -5] = true := by decide +kernel
theorem subd7_3_773 : subd7_3 [2, -3, -4] = true := by decide +kernel
theorem subd7_3_774 : subd7_3 [2, -3, -3] = true := by decide +kernel
theorem subd7_3_775 : subd7_3 [2, -3, -2] = true := by decide +kernel
theorem subd7_3_776 : subd7_3 [2, -3, -1] = true := by decide +kernel
theorem subd7_3_777 : subd7_3 [2, -3, 0] = true := by decide +kernel
theorem subd7_3_778 : subd7_3 [2, -3, 1] = true := by decide +kernel
theorem subd7_3_779 : subd7_3 [2, -3, 2] = true := by decide +kernel
theorem subd7_3_780 : subd7_3 [2, -3, 3] = true := by decide +kernel
theorem subd7_3_781 : subd7_3 [2, -3, 4] = true := by decide +kernel
theorem subd7_3_782 : subd7_3 [2, -3, 5] = true := by decide +kernel
theorem subd7_3_783 : subd7_3 [2, -3, 6] = true := by decide +kernel
theorem subd7_3_784 : subd7_3 [2, -3, 7] = true := by decide +kernel
theorem subd7_3_785 : subd7_3 [2, -2, -7] = true := by decide +kernel
theorem subd7_3_786 : subd7_3 [2, -2, -6] = true := by decide +kernel
theorem subd7_3_787 : subd7_3 [2, -2, -5] = true := by decide +kernel
theorem subd7_3_788 : subd7_3 [2, -2, -4] = true := by decide +kernel
theorem subd7_3_789 : subd7_3 [2, -2, -3] = true := by decide +kernel
theorem subd7_3_790 : subd7_3 [2, -2, -2] = true := by decide +kernel
theorem subd7_3_791 : subd7_3 [2, -2, -1] = true := by decide +kernel
theorem subd7_3_792 : subd7_3 [2, -2, 0] = true := by decide +kernel
theorem subd7_3_793 : subd7_3 [2, -2, 1] = true := by decide +kernel
theorem subd7_3_794 : subd7_3 [2, -2, 2] = true := by decide +kernel
theorem subd7_3_795 : subd7_3 [2, -2, 3] = true := by decide +kernel
theorem subd7_3_796 : subd7_3 [2, -2, 4] = true := by decide +kernel
theorem subd7_3_797 : subd7_3 [2, -2, 5] = true := by decide +kernel
theorem subd7_3_798 : subd7_3 [2, -2, 6] = true := by decide +kernel
theorem subd7_3_799 : subd7_3 [2, -2, 7] = true := by decide +kernel
theorem sbd7_3_24 : ∀ q ∈ blkd7_3_24, subd7_3 q = true := by
  unfold blkd7_3_24
  exact List.forall_mem_cons.2 ⟨subd7_3_768, List.forall_mem_cons.2 ⟨subd7_3_769, List.forall_mem_cons.2 ⟨subd7_3_770, List.forall_mem_cons.2 ⟨subd7_3_771, List.forall_mem_cons.2 ⟨subd7_3_772, List.forall_mem_cons.2 ⟨subd7_3_773, List.forall_mem_cons.2 ⟨subd7_3_774, List.forall_mem_cons.2 ⟨subd7_3_775, List.forall_mem_cons.2 ⟨subd7_3_776, List.forall_mem_cons.2 ⟨subd7_3_777, List.forall_mem_cons.2 ⟨subd7_3_778, List.forall_mem_cons.2 ⟨subd7_3_779, List.forall_mem_cons.2 ⟨subd7_3_780, List.forall_mem_cons.2 ⟨subd7_3_781, List.forall_mem_cons.2 ⟨subd7_3_782, List.forall_mem_cons.2 ⟨subd7_3_783, List.forall_mem_cons.2 ⟨subd7_3_784, List.forall_mem_cons.2 ⟨subd7_3_785, List.forall_mem_cons.2 ⟨subd7_3_786, List.forall_mem_cons.2 ⟨subd7_3_787, List.forall_mem_cons.2 ⟨subd7_3_788, List.forall_mem_cons.2 ⟨subd7_3_789, List.forall_mem_cons.2 ⟨subd7_3_790, List.forall_mem_cons.2 ⟨subd7_3_791, List.forall_mem_cons.2 ⟨subd7_3_792, List.forall_mem_cons.2 ⟨subd7_3_793, List.forall_mem_cons.2 ⟨subd7_3_794, List.forall_mem_cons.2 ⟨subd7_3_795, List.forall_mem_cons.2 ⟨subd7_3_796, List.forall_mem_cons.2 ⟨subd7_3_797, List.forall_mem_cons.2 ⟨subd7_3_798, List.forall_mem_cons.2 ⟨subd7_3_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_800 : subd7_3 [2, -2, 8] = true := by decide +kernel
theorem subd7_3_801 : subd7_3 [2, -1, -7] = true := by decide +kernel
theorem subd7_3_802 : subd7_3 [2, -1, -6] = true := by decide +kernel
theorem subd7_3_803 : subd7_3 [2, -1, -5] = true := by decide +kernel
theorem subd7_3_804 : subd7_3 [2, -1, -4] = true := by decide +kernel
theorem subd7_3_805 : subd7_3 [2, -1, -3] = true := by decide +kernel
theorem subd7_3_806 : subd7_3 [2, -1, -2] = true := by decide +kernel
theorem subd7_3_807 : subd7_3 [2, -1, -1] = true := by decide +kernel
theorem subd7_3_808 : subd7_3 [2, -1, 0] = true := by decide +kernel
theorem subd7_3_809 : subd7_3 [2, -1, 1] = true := by decide +kernel
theorem subd7_3_810 : subd7_3 [2, -1, 2] = true := by decide +kernel
theorem subd7_3_811 : subd7_3 [2, -1, 3] = true := by decide +kernel
theorem subd7_3_812 : subd7_3 [2, -1, 4] = true := by decide +kernel
theorem subd7_3_813 : subd7_3 [2, -1, 5] = true := by decide +kernel
theorem subd7_3_814 : subd7_3 [2, -1, 6] = true := by decide +kernel
theorem subd7_3_815 : subd7_3 [2, -1, 7] = true := by decide +kernel
theorem subd7_3_816 : subd7_3 [2, -1, 8] = true := by decide +kernel
theorem subd7_3_817 : subd7_3 [2, 0, -8] = true := by decide +kernel
theorem subd7_3_818 : subd7_3 [2, 0, -7] = true := by decide +kernel
theorem subd7_3_819 : subd7_3 [2, 0, -6] = true := by decide +kernel
theorem subd7_3_820 : subd7_3 [2, 0, -5] = true := by decide +kernel
theorem subd7_3_821 : subd7_3 [2, 0, -4] = true := by decide +kernel
theorem subd7_3_822 : subd7_3 [2, 0, -3] = true := by decide +kernel
theorem subd7_3_823 : subd7_3 [2, 0, -2] = true := by decide +kernel
theorem subd7_3_824 : subd7_3 [2, 0, -1] = true := by decide +kernel
theorem subd7_3_825 : subd7_3 [2, 0, 0] = true := by decide +kernel
theorem subd7_3_826 : subd7_3 [2, 0, 1] = true := by decide +kernel
theorem subd7_3_827 : subd7_3 [2, 0, 2] = true := by decide +kernel
theorem subd7_3_828 : subd7_3 [2, 0, 3] = true := by decide +kernel
theorem subd7_3_829 : subd7_3 [2, 0, 4] = true := by decide +kernel
theorem subd7_3_830 : subd7_3 [2, 0, 5] = true := by decide +kernel
theorem subd7_3_831 : subd7_3 [2, 0, 6] = true := by decide +kernel
theorem sbd7_3_25 : ∀ q ∈ blkd7_3_25, subd7_3 q = true := by
  unfold blkd7_3_25
  exact List.forall_mem_cons.2 ⟨subd7_3_800, List.forall_mem_cons.2 ⟨subd7_3_801, List.forall_mem_cons.2 ⟨subd7_3_802, List.forall_mem_cons.2 ⟨subd7_3_803, List.forall_mem_cons.2 ⟨subd7_3_804, List.forall_mem_cons.2 ⟨subd7_3_805, List.forall_mem_cons.2 ⟨subd7_3_806, List.forall_mem_cons.2 ⟨subd7_3_807, List.forall_mem_cons.2 ⟨subd7_3_808, List.forall_mem_cons.2 ⟨subd7_3_809, List.forall_mem_cons.2 ⟨subd7_3_810, List.forall_mem_cons.2 ⟨subd7_3_811, List.forall_mem_cons.2 ⟨subd7_3_812, List.forall_mem_cons.2 ⟨subd7_3_813, List.forall_mem_cons.2 ⟨subd7_3_814, List.forall_mem_cons.2 ⟨subd7_3_815, List.forall_mem_cons.2 ⟨subd7_3_816, List.forall_mem_cons.2 ⟨subd7_3_817, List.forall_mem_cons.2 ⟨subd7_3_818, List.forall_mem_cons.2 ⟨subd7_3_819, List.forall_mem_cons.2 ⟨subd7_3_820, List.forall_mem_cons.2 ⟨subd7_3_821, List.forall_mem_cons.2 ⟨subd7_3_822, List.forall_mem_cons.2 ⟨subd7_3_823, List.forall_mem_cons.2 ⟨subd7_3_824, List.forall_mem_cons.2 ⟨subd7_3_825, List.forall_mem_cons.2 ⟨subd7_3_826, List.forall_mem_cons.2 ⟨subd7_3_827, List.forall_mem_cons.2 ⟨subd7_3_828, List.forall_mem_cons.2 ⟨subd7_3_829, List.forall_mem_cons.2 ⟨subd7_3_830, List.forall_mem_cons.2 ⟨subd7_3_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
