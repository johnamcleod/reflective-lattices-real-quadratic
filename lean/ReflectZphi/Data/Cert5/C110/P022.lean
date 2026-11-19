import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_4_384 : subd8_4 [-1, 3, 2] = true := by decide +kernel
theorem subd8_4_385 : subd8_4 [-1, 3, 3] = true := by decide +kernel
theorem subd8_4_386 : subd8_4 [-1, 3, 4] = true := by decide +kernel
theorem subd8_4_387 : subd8_4 [-1, 3, 5] = true := by decide +kernel
theorem subd8_4_388 : subd8_4 [-1, 3, 6] = true := by decide +kernel
theorem subd8_4_389 : subd8_4 [-1, 3, 7] = true := by decide +kernel
theorem subd8_4_390 : subd8_4 [-1, 4, -5] = true := by decide +kernel
theorem subd8_4_391 : subd8_4 [-1, 4, -4] = true := by decide +kernel
theorem subd8_4_392 : subd8_4 [-1, 4, -3] = true := by decide +kernel
theorem subd8_4_393 : subd8_4 [-1, 4, -2] = true := by decide +kernel
theorem subd8_4_394 : subd8_4 [-1, 4, -1] = true := by decide +kernel
theorem subd8_4_395 : subd8_4 [-1, 4, 0] = true := by decide +kernel
theorem subd8_4_396 : subd8_4 [-1, 4, 1] = true := by decide +kernel
theorem subd8_4_397 : subd8_4 [-1, 4, 2] = true := by decide +kernel
theorem subd8_4_398 : subd8_4 [-1, 4, 3] = true := by decide +kernel
theorem subd8_4_399 : subd8_4 [-1, 4, 4] = true := by decide +kernel
theorem subd8_4_400 : subd8_4 [-1, 4, 5] = true := by decide +kernel
theorem subd8_4_401 : subd8_4 [-1, 4, 6] = true := by decide +kernel
theorem subd8_4_402 : subd8_4 [-1, 4, 7] = true := by decide +kernel
theorem subd8_4_403 : subd8_4 [-1, 5] = true := by decide +kernel
theorem subd8_4_404 : subd8_4 [-1, 6] = true := by decide +kernel
theorem subd8_4_405 : subd8_4 [-1, 7] = true := by decide +kernel
theorem subd8_4_406 : subd8_4 [0, -8] = true := by decide +kernel
theorem subd8_4_407 : subd8_4 [0, -7] = true := by decide +kernel
theorem subd8_4_408 : subd8_4 [0, -6] = true := by decide +kernel
theorem subd8_4_409 : subd8_4 [0, -5] = true := by decide +kernel
theorem subd8_4_410 : subd8_4 [0, -4, -9] = true := by decide +kernel
theorem subd8_4_411 : subd8_4 [0, -4, -8] = true := by decide +kernel
theorem subd8_4_412 : subd8_4 [0, -4, -7] = true := by decide +kernel
theorem subd8_4_413 : subd8_4 [0, -4, -6] = true := by decide +kernel
theorem subd8_4_414 : subd8_4 [0, -4, -5] = true := by decide +kernel
theorem subd8_4_415 : subd8_4 [0, -4, -4] = true := by decide +kernel
theorem sbd8_4_12 : ∀ q ∈ blkd8_4_12, subd8_4 q = true := by
  unfold blkd8_4_12
  exact List.forall_mem_cons.2 ⟨subd8_4_384, List.forall_mem_cons.2 ⟨subd8_4_385, List.forall_mem_cons.2 ⟨subd8_4_386, List.forall_mem_cons.2 ⟨subd8_4_387, List.forall_mem_cons.2 ⟨subd8_4_388, List.forall_mem_cons.2 ⟨subd8_4_389, List.forall_mem_cons.2 ⟨subd8_4_390, List.forall_mem_cons.2 ⟨subd8_4_391, List.forall_mem_cons.2 ⟨subd8_4_392, List.forall_mem_cons.2 ⟨subd8_4_393, List.forall_mem_cons.2 ⟨subd8_4_394, List.forall_mem_cons.2 ⟨subd8_4_395, List.forall_mem_cons.2 ⟨subd8_4_396, List.forall_mem_cons.2 ⟨subd8_4_397, List.forall_mem_cons.2 ⟨subd8_4_398, List.forall_mem_cons.2 ⟨subd8_4_399, List.forall_mem_cons.2 ⟨subd8_4_400, List.forall_mem_cons.2 ⟨subd8_4_401, List.forall_mem_cons.2 ⟨subd8_4_402, List.forall_mem_cons.2 ⟨subd8_4_403, List.forall_mem_cons.2 ⟨subd8_4_404, List.forall_mem_cons.2 ⟨subd8_4_405, List.forall_mem_cons.2 ⟨subd8_4_406, List.forall_mem_cons.2 ⟨subd8_4_407, List.forall_mem_cons.2 ⟨subd8_4_408, List.forall_mem_cons.2 ⟨subd8_4_409, List.forall_mem_cons.2 ⟨subd8_4_410, List.forall_mem_cons.2 ⟨subd8_4_411, List.forall_mem_cons.2 ⟨subd8_4_412, List.forall_mem_cons.2 ⟨subd8_4_413, List.forall_mem_cons.2 ⟨subd8_4_414, List.forall_mem_cons.2 ⟨subd8_4_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_416 : subd8_4 [0, -4, -3] = true := by decide +kernel
theorem subd8_4_417 : subd8_4 [0, -4, -2] = true := by decide +kernel
theorem subd8_4_418 : subd8_4 [0, -4, -1] = true := by decide +kernel
theorem subd8_4_419 : subd8_4 [0, -4, 0] = true := by decide +kernel
theorem subd8_4_420 : subd8_4 [0, -4, 1] = true := by decide +kernel
theorem subd8_4_421 : subd8_4 [0, -4, 2] = true := by decide +kernel
theorem subd8_4_422 : subd8_4 [0, -4, 3] = true := by decide +kernel
theorem subd8_4_423 : subd8_4 [0, -4, 4] = true := by decide +kernel
theorem subd8_4_424 : subd8_4 [0, -3, -9] = true := by decide +kernel
theorem subd8_4_425 : subd8_4 [0, -3, -8] = true := by decide +kernel
theorem subd8_4_426 : subd8_4 [0, -3, -7] = true := by decide +kernel
theorem subd8_4_427 : subd8_4 [0, -3, -6] = true := by decide +kernel
theorem subd8_4_428 : subd8_4 [0, -3, -5] = true := by decide +kernel
theorem subd8_4_429 : subd8_4 [0, -3, -4] = true := by decide +kernel
theorem subd8_4_430 : subd8_4 [0, -3, -3] = true := by decide +kernel
theorem subd8_4_431 : subd8_4 [0, -3, -2] = true := by decide +kernel
theorem subd8_4_432 : subd8_4 [0, -3, -1] = true := by decide +kernel
theorem subd8_4_433 : subd8_4 [0, -3, 0] = true := by decide +kernel
theorem subd8_4_434 : subd8_4 [0, -3, 1] = true := by decide +kernel
theorem subd8_4_435 : subd8_4 [0, -3, 2] = true := by decide +kernel
theorem subd8_4_436 : subd8_4 [0, -3, 3] = true := by decide +kernel
theorem subd8_4_437 : subd8_4 [0, -3, 4] = true := by decide +kernel
theorem subd8_4_438 : subd8_4 [0, -3, 5] = true := by decide +kernel
theorem subd8_4_439 : subd8_4 [0, -2, -9] = true := by decide +kernel
theorem subd8_4_440 : subd8_4 [0, -2, -8] = true := by decide +kernel
theorem subd8_4_441 : subd8_4 [0, -2, -7] = true := by decide +kernel
theorem subd8_4_442 : subd8_4 [0, -2, -6] = true := by decide +kernel
theorem subd8_4_443 : subd8_4 [0, -2, -5] = true := by decide +kernel
theorem subd8_4_444 : subd8_4 [0, -2, -4] = true := by decide +kernel
theorem subd8_4_445 : subd8_4 [0, -2, -3] = true := by decide +kernel
theorem subd8_4_446 : subd8_4 [0, -2, -2] = true := by decide +kernel
theorem subd8_4_447 : subd8_4 [0, -2, -1] = true := by decide +kernel
theorem sbd8_4_13 : ∀ q ∈ blkd8_4_13, subd8_4 q = true := by
  unfold blkd8_4_13
  exact List.forall_mem_cons.2 ⟨subd8_4_416, List.forall_mem_cons.2 ⟨subd8_4_417, List.forall_mem_cons.2 ⟨subd8_4_418, List.forall_mem_cons.2 ⟨subd8_4_419, List.forall_mem_cons.2 ⟨subd8_4_420, List.forall_mem_cons.2 ⟨subd8_4_421, List.forall_mem_cons.2 ⟨subd8_4_422, List.forall_mem_cons.2 ⟨subd8_4_423, List.forall_mem_cons.2 ⟨subd8_4_424, List.forall_mem_cons.2 ⟨subd8_4_425, List.forall_mem_cons.2 ⟨subd8_4_426, List.forall_mem_cons.2 ⟨subd8_4_427, List.forall_mem_cons.2 ⟨subd8_4_428, List.forall_mem_cons.2 ⟨subd8_4_429, List.forall_mem_cons.2 ⟨subd8_4_430, List.forall_mem_cons.2 ⟨subd8_4_431, List.forall_mem_cons.2 ⟨subd8_4_432, List.forall_mem_cons.2 ⟨subd8_4_433, List.forall_mem_cons.2 ⟨subd8_4_434, List.forall_mem_cons.2 ⟨subd8_4_435, List.forall_mem_cons.2 ⟨subd8_4_436, List.forall_mem_cons.2 ⟨subd8_4_437, List.forall_mem_cons.2 ⟨subd8_4_438, List.forall_mem_cons.2 ⟨subd8_4_439, List.forall_mem_cons.2 ⟨subd8_4_440, List.forall_mem_cons.2 ⟨subd8_4_441, List.forall_mem_cons.2 ⟨subd8_4_442, List.forall_mem_cons.2 ⟨subd8_4_443, List.forall_mem_cons.2 ⟨subd8_4_444, List.forall_mem_cons.2 ⟨subd8_4_445, List.forall_mem_cons.2 ⟨subd8_4_446, List.forall_mem_cons.2 ⟨subd8_4_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_448 : subd8_4 [0, -2, 0] = true := by decide +kernel
theorem subd8_4_449 : subd8_4 [0, -2, 1] = true := by decide +kernel
theorem subd8_4_450 : subd8_4 [0, -2, 2] = true := by decide +kernel
theorem subd8_4_451 : subd8_4 [0, -2, 3] = true := by decide +kernel
theorem subd8_4_452 : subd8_4 [0, -2, 4] = true := by decide +kernel
theorem subd8_4_453 : subd8_4 [0, -2, 5] = true := by decide +kernel
theorem subd8_4_454 : subd8_4 [0, -2, 6] = true := by decide +kernel
theorem subd8_4_455 : subd8_4 [0, -1, -9] = true := by decide +kernel
theorem subd8_4_456 : subd8_4 [0, -1, -8] = true := by decide +kernel
theorem subd8_4_457 : subd8_4 [0, -1, -7] = true := by decide +kernel
theorem subd8_4_458 : subd8_4 [0, -1, -6] = true := by decide +kernel
theorem subd8_4_459 : subd8_4 [0, -1, -5] = true := by decide +kernel
theorem subd8_4_460 : subd8_4 [0, -1, -4] = true := by decide +kernel
theorem subd8_4_461 : subd8_4 [0, -1, -3] = true := by decide +kernel
theorem subd8_4_462 : subd8_4 [0, -1, -2] = true := by decide +kernel
theorem subd8_4_463 : subd8_4 [0, -1, -1] = true := by decide +kernel
theorem subd8_4_464 : subd8_4 [0, -1, 0] = true := by decide +kernel
theorem subd8_4_465 : subd8_4 [0, -1, 1] = true := by decide +kernel
theorem subd8_4_466 : subd8_4 [0, -1, 2] = true := by decide +kernel
theorem subd8_4_467 : subd8_4 [0, -1, 3] = true := by decide +kernel
theorem subd8_4_468 : subd8_4 [0, -1, 4] = true := by decide +kernel
theorem subd8_4_469 : subd8_4 [0, -1, 5] = true := by decide +kernel
theorem subd8_4_470 : subd8_4 [0, -1, 6] = true := by decide +kernel
theorem subd8_4_471 : subd8_4 [0, -1, 7] = true := by decide +kernel
theorem subd8_4_472 : subd8_4 [0, 0, -8] = true := by decide +kernel
theorem subd8_4_473 : subd8_4 [0, 0, -7] = true := by decide +kernel
theorem subd8_4_474 : subd8_4 [0, 0, -6] = true := by decide +kernel
theorem subd8_4_475 : subd8_4 [0, 0, -5] = true := by decide +kernel
theorem subd8_4_476 : subd8_4 [0, 0, -4] = true := by decide +kernel
theorem subd8_4_477 : subd8_4 [0, 0, -3] = true := by decide +kernel
theorem subd8_4_478 : subd8_4 [0, 0, -2] = true := by decide +kernel
theorem subd8_4_479 : subd8_4 [0, 0, -1] = true := by decide +kernel
theorem sbd8_4_14 : ∀ q ∈ blkd8_4_14, subd8_4 q = true := by
  unfold blkd8_4_14
  exact List.forall_mem_cons.2 ⟨subd8_4_448, List.forall_mem_cons.2 ⟨subd8_4_449, List.forall_mem_cons.2 ⟨subd8_4_450, List.forall_mem_cons.2 ⟨subd8_4_451, List.forall_mem_cons.2 ⟨subd8_4_452, List.forall_mem_cons.2 ⟨subd8_4_453, List.forall_mem_cons.2 ⟨subd8_4_454, List.forall_mem_cons.2 ⟨subd8_4_455, List.forall_mem_cons.2 ⟨subd8_4_456, List.forall_mem_cons.2 ⟨subd8_4_457, List.forall_mem_cons.2 ⟨subd8_4_458, List.forall_mem_cons.2 ⟨subd8_4_459, List.forall_mem_cons.2 ⟨subd8_4_460, List.forall_mem_cons.2 ⟨subd8_4_461, List.forall_mem_cons.2 ⟨subd8_4_462, List.forall_mem_cons.2 ⟨subd8_4_463, List.forall_mem_cons.2 ⟨subd8_4_464, List.forall_mem_cons.2 ⟨subd8_4_465, List.forall_mem_cons.2 ⟨subd8_4_466, List.forall_mem_cons.2 ⟨subd8_4_467, List.forall_mem_cons.2 ⟨subd8_4_468, List.forall_mem_cons.2 ⟨subd8_4_469, List.forall_mem_cons.2 ⟨subd8_4_470, List.forall_mem_cons.2 ⟨subd8_4_471, List.forall_mem_cons.2 ⟨subd8_4_472, List.forall_mem_cons.2 ⟨subd8_4_473, List.forall_mem_cons.2 ⟨subd8_4_474, List.forall_mem_cons.2 ⟨subd8_4_475, List.forall_mem_cons.2 ⟨subd8_4_476, List.forall_mem_cons.2 ⟨subd8_4_477, List.forall_mem_cons.2 ⟨subd8_4_478, List.forall_mem_cons.2 ⟨subd8_4_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_480 : subd8_4 [0, 0, 0] = true := by decide +kernel
theorem subd8_4_481 : subd8_4 [0, 0, 1] = true := by decide +kernel
theorem subd8_4_482 : subd8_4 [0, 0, 2] = true := by decide +kernel
theorem subd8_4_483 : subd8_4 [0, 0, 3] = true := by decide +kernel
theorem subd8_4_484 : subd8_4 [0, 0, 4] = true := by decide +kernel
theorem subd8_4_485 : subd8_4 [0, 0, 5] = true := by decide +kernel
theorem subd8_4_486 : subd8_4 [0, 0, 6] = true := by decide +kernel
theorem subd8_4_487 : subd8_4 [0, 0, 7] = true := by decide +kernel
theorem subd8_4_488 : subd8_4 [0, 1, -8] = true := by decide +kernel
theorem subd8_4_489 : subd8_4 [0, 1, -7] = true := by decide +kernel
theorem subd8_4_490 : subd8_4 [0, 1, -6] = true := by decide +kernel
theorem subd8_4_491 : subd8_4 [0, 1, -5] = true := by decide +kernel
theorem subd8_4_492 : subd8_4 [0, 1, -4] = true := by decide +kernel
theorem subd8_4_493 : subd8_4 [0, 1, -3] = true := by decide +kernel
theorem subd8_4_494 : subd8_4 [0, 1, -2] = true := by decide +kernel
theorem subd8_4_495 : subd8_4 [0, 1, -1] = true := by decide +kernel
theorem subd8_4_496 : subd8_4 [0, 1, 0] = true := by decide +kernel
theorem subd8_4_497 : subd8_4 [0, 1, 1] = true := by decide +kernel
theorem subd8_4_498 : subd8_4 [0, 1, 2] = true := by decide +kernel
theorem subd8_4_499 : subd8_4 [0, 1, 3] = true := by decide +kernel
theorem subd8_4_500 : subd8_4 [0, 1, 4] = true := by decide +kernel
theorem subd8_4_501 : subd8_4 [0, 1, 5] = true := by decide +kernel
theorem subd8_4_502 : subd8_4 [0, 1, 6] = true := by decide +kernel
theorem subd8_4_503 : subd8_4 [0, 1, 7] = true := by decide +kernel
theorem subd8_4_504 : subd8_4 [0, 1, 8] = true := by decide +kernel
theorem subd8_4_505 : subd8_4 [0, 2, -7] = true := by decide +kernel
theorem subd8_4_506 : subd8_4 [0, 2, -6] = true := by decide +kernel
theorem subd8_4_507 : subd8_4 [0, 2, -5] = true := by decide +kernel
theorem subd8_4_508 : subd8_4 [0, 2, -4] = true := by decide +kernel
theorem subd8_4_509 : subd8_4 [0, 2, -3] = true := by decide +kernel
theorem subd8_4_510 : subd8_4 [0, 2, -2] = true := by decide +kernel
theorem subd8_4_511 : subd8_4 [0, 2, -1] = true := by decide +kernel
theorem sbd8_4_15 : ∀ q ∈ blkd8_4_15, subd8_4 q = true := by
  unfold blkd8_4_15
  exact List.forall_mem_cons.2 ⟨subd8_4_480, List.forall_mem_cons.2 ⟨subd8_4_481, List.forall_mem_cons.2 ⟨subd8_4_482, List.forall_mem_cons.2 ⟨subd8_4_483, List.forall_mem_cons.2 ⟨subd8_4_484, List.forall_mem_cons.2 ⟨subd8_4_485, List.forall_mem_cons.2 ⟨subd8_4_486, List.forall_mem_cons.2 ⟨subd8_4_487, List.forall_mem_cons.2 ⟨subd8_4_488, List.forall_mem_cons.2 ⟨subd8_4_489, List.forall_mem_cons.2 ⟨subd8_4_490, List.forall_mem_cons.2 ⟨subd8_4_491, List.forall_mem_cons.2 ⟨subd8_4_492, List.forall_mem_cons.2 ⟨subd8_4_493, List.forall_mem_cons.2 ⟨subd8_4_494, List.forall_mem_cons.2 ⟨subd8_4_495, List.forall_mem_cons.2 ⟨subd8_4_496, List.forall_mem_cons.2 ⟨subd8_4_497, List.forall_mem_cons.2 ⟨subd8_4_498, List.forall_mem_cons.2 ⟨subd8_4_499, List.forall_mem_cons.2 ⟨subd8_4_500, List.forall_mem_cons.2 ⟨subd8_4_501, List.forall_mem_cons.2 ⟨subd8_4_502, List.forall_mem_cons.2 ⟨subd8_4_503, List.forall_mem_cons.2 ⟨subd8_4_504, List.forall_mem_cons.2 ⟨subd8_4_505, List.forall_mem_cons.2 ⟨subd8_4_506, List.forall_mem_cons.2 ⟨subd8_4_507, List.forall_mem_cons.2 ⟨subd8_4_508, List.forall_mem_cons.2 ⟨subd8_4_509, List.forall_mem_cons.2 ⟨subd8_4_510, List.forall_mem_cons.2 ⟨subd8_4_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_512 : subd8_4 [0, 2, 0] = true := by decide +kernel
theorem subd8_4_513 : subd8_4 [0, 2, 1] = true := by decide +kernel
theorem subd8_4_514 : subd8_4 [0, 2, 2] = true := by decide +kernel
theorem subd8_4_515 : subd8_4 [0, 2, 3] = true := by decide +kernel
theorem subd8_4_516 : subd8_4 [0, 2, 4] = true := by decide +kernel
theorem subd8_4_517 : subd8_4 [0, 2, 5] = true := by decide +kernel
theorem subd8_4_518 : subd8_4 [0, 2, 6] = true := by decide +kernel
theorem subd8_4_519 : subd8_4 [0, 2, 7] = true := by decide +kernel
theorem subd8_4_520 : subd8_4 [0, 2, 8] = true := by decide +kernel
theorem subd8_4_521 : subd8_4 [0, 3, -6] = true := by decide +kernel
theorem subd8_4_522 : subd8_4 [0, 3, -5] = true := by decide +kernel
theorem subd8_4_523 : subd8_4 [0, 3, -4] = true := by decide +kernel
theorem subd8_4_524 : subd8_4 [0, 3, -3] = true := by decide +kernel
theorem subd8_4_525 : subd8_4 [0, 3, -2] = true := by decide +kernel
theorem subd8_4_526 : subd8_4 [0, 3, -1] = true := by decide +kernel
theorem subd8_4_527 : subd8_4 [0, 3, 0] = true := by decide +kernel
theorem subd8_4_528 : subd8_4 [0, 3, 1] = true := by decide +kernel
theorem subd8_4_529 : subd8_4 [0, 3, 2] = true := by decide +kernel
theorem subd8_4_530 : subd8_4 [0, 3, 3] = true := by decide +kernel
theorem subd8_4_531 : subd8_4 [0, 3, 4] = true := by decide +kernel
theorem subd8_4_532 : subd8_4 [0, 3, 5] = true := by decide +kernel
theorem subd8_4_533 : subd8_4 [0, 3, 6] = true := by decide +kernel
theorem subd8_4_534 : subd8_4 [0, 3, 7] = true := by decide +kernel
theorem subd8_4_535 : subd8_4 [0, 3, 8] = true := by decide +kernel
theorem subd8_4_536 : subd8_4 [0, 4, -5] = true := by decide +kernel
theorem subd8_4_537 : subd8_4 [0, 4, -4] = true := by decide +kernel
theorem subd8_4_538 : subd8_4 [0, 4, -3] = true := by decide +kernel
theorem subd8_4_539 : subd8_4 [0, 4, -2] = true := by decide +kernel
theorem subd8_4_540 : subd8_4 [0, 4, -1] = true := by decide +kernel
theorem subd8_4_541 : subd8_4 [0, 4, 0] = true := by decide +kernel
theorem subd8_4_542 : subd8_4 [0, 4, 1] = true := by decide +kernel
theorem subd8_4_543 : subd8_4 [0, 4, 2] = true := by decide +kernel
theorem sbd8_4_16 : ∀ q ∈ blkd8_4_16, subd8_4 q = true := by
  unfold blkd8_4_16
  exact List.forall_mem_cons.2 ⟨subd8_4_512, List.forall_mem_cons.2 ⟨subd8_4_513, List.forall_mem_cons.2 ⟨subd8_4_514, List.forall_mem_cons.2 ⟨subd8_4_515, List.forall_mem_cons.2 ⟨subd8_4_516, List.forall_mem_cons.2 ⟨subd8_4_517, List.forall_mem_cons.2 ⟨subd8_4_518, List.forall_mem_cons.2 ⟨subd8_4_519, List.forall_mem_cons.2 ⟨subd8_4_520, List.forall_mem_cons.2 ⟨subd8_4_521, List.forall_mem_cons.2 ⟨subd8_4_522, List.forall_mem_cons.2 ⟨subd8_4_523, List.forall_mem_cons.2 ⟨subd8_4_524, List.forall_mem_cons.2 ⟨subd8_4_525, List.forall_mem_cons.2 ⟨subd8_4_526, List.forall_mem_cons.2 ⟨subd8_4_527, List.forall_mem_cons.2 ⟨subd8_4_528, List.forall_mem_cons.2 ⟨subd8_4_529, List.forall_mem_cons.2 ⟨subd8_4_530, List.forall_mem_cons.2 ⟨subd8_4_531, List.forall_mem_cons.2 ⟨subd8_4_532, List.forall_mem_cons.2 ⟨subd8_4_533, List.forall_mem_cons.2 ⟨subd8_4_534, List.forall_mem_cons.2 ⟨subd8_4_535, List.forall_mem_cons.2 ⟨subd8_4_536, List.forall_mem_cons.2 ⟨subd8_4_537, List.forall_mem_cons.2 ⟨subd8_4_538, List.forall_mem_cons.2 ⟨subd8_4_539, List.forall_mem_cons.2 ⟨subd8_4_540, List.forall_mem_cons.2 ⟨subd8_4_541, List.forall_mem_cons.2 ⟨subd8_4_542, List.forall_mem_cons.2 ⟨subd8_4_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_544 : subd8_4 [0, 4, 3] = true := by decide +kernel
theorem subd8_4_545 : subd8_4 [0, 4, 4] = true := by decide +kernel
theorem subd8_4_546 : subd8_4 [0, 4, 5] = true := by decide +kernel
theorem subd8_4_547 : subd8_4 [0, 4, 6] = true := by decide +kernel
theorem subd8_4_548 : subd8_4 [0, 4, 7] = true := by decide +kernel
theorem subd8_4_549 : subd8_4 [0, 4, 8] = true := by decide +kernel
theorem subd8_4_550 : subd8_4 [0, 5] = true := by decide +kernel
theorem subd8_4_551 : subd8_4 [0, 6] = true := by decide +kernel
theorem subd8_4_552 : subd8_4 [0, 7] = true := by decide +kernel
theorem subd8_4_553 : subd8_4 [1, -8] = true := by decide +kernel
theorem subd8_4_554 : subd8_4 [1, -7] = true := by decide +kernel
theorem subd8_4_555 : subd8_4 [1, -6] = true := by decide +kernel
theorem subd8_4_556 : subd8_4 [1, -5] = true := by decide +kernel
theorem subd8_4_557 : subd8_4 [1, -4, -8] = true := by decide +kernel
theorem subd8_4_558 : subd8_4 [1, -4, -7] = true := by decide +kernel
theorem subd8_4_559 : subd8_4 [1, -4, -6] = true := by decide +kernel
theorem subd8_4_560 : subd8_4 [1, -4, -5] = true := by decide +kernel
theorem subd8_4_561 : subd8_4 [1, -4, -4] = true := by decide +kernel
theorem subd8_4_562 : subd8_4 [1, -4, -3] = true := by decide +kernel
theorem subd8_4_563 : subd8_4 [1, -4, -2] = true := by decide +kernel
theorem subd8_4_564 : subd8_4 [1, -4, -1] = true := by decide +kernel
theorem subd8_4_565 : subd8_4 [1, -4, 0] = true := by decide +kernel
theorem subd8_4_566 : subd8_4 [1, -4, 1] = true := by decide +kernel
theorem subd8_4_567 : subd8_4 [1, -4, 2] = true := by decide +kernel
theorem subd8_4_568 : subd8_4 [1, -4, 3] = true := by decide +kernel
theorem subd8_4_569 : subd8_4 [1, -4, 4] = true := by decide +kernel
theorem subd8_4_570 : subd8_4 [1, -3, -8] = true := by decide +kernel
theorem subd8_4_571 : subd8_4 [1, -3, -7] = true := by decide +kernel
theorem subd8_4_572 : subd8_4 [1, -3, -6] = true := by decide +kernel
theorem subd8_4_573 : subd8_4 [1, -3, -5] = true := by decide +kernel
theorem subd8_4_574 : subd8_4 [1, -3, -4] = true := by decide +kernel
theorem subd8_4_575 : subd8_4 [1, -3, -3] = true := by decide +kernel
theorem sbd8_4_17 : ∀ q ∈ blkd8_4_17, subd8_4 q = true := by
  unfold blkd8_4_17
  exact List.forall_mem_cons.2 ⟨subd8_4_544, List.forall_mem_cons.2 ⟨subd8_4_545, List.forall_mem_cons.2 ⟨subd8_4_546, List.forall_mem_cons.2 ⟨subd8_4_547, List.forall_mem_cons.2 ⟨subd8_4_548, List.forall_mem_cons.2 ⟨subd8_4_549, List.forall_mem_cons.2 ⟨subd8_4_550, List.forall_mem_cons.2 ⟨subd8_4_551, List.forall_mem_cons.2 ⟨subd8_4_552, List.forall_mem_cons.2 ⟨subd8_4_553, List.forall_mem_cons.2 ⟨subd8_4_554, List.forall_mem_cons.2 ⟨subd8_4_555, List.forall_mem_cons.2 ⟨subd8_4_556, List.forall_mem_cons.2 ⟨subd8_4_557, List.forall_mem_cons.2 ⟨subd8_4_558, List.forall_mem_cons.2 ⟨subd8_4_559, List.forall_mem_cons.2 ⟨subd8_4_560, List.forall_mem_cons.2 ⟨subd8_4_561, List.forall_mem_cons.2 ⟨subd8_4_562, List.forall_mem_cons.2 ⟨subd8_4_563, List.forall_mem_cons.2 ⟨subd8_4_564, List.forall_mem_cons.2 ⟨subd8_4_565, List.forall_mem_cons.2 ⟨subd8_4_566, List.forall_mem_cons.2 ⟨subd8_4_567, List.forall_mem_cons.2 ⟨subd8_4_568, List.forall_mem_cons.2 ⟨subd8_4_569, List.forall_mem_cons.2 ⟨subd8_4_570, List.forall_mem_cons.2 ⟨subd8_4_571, List.forall_mem_cons.2 ⟨subd8_4_572, List.forall_mem_cons.2 ⟨subd8_4_573, List.forall_mem_cons.2 ⟨subd8_4_574, List.forall_mem_cons.2 ⟨subd8_4_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_576 : subd8_4 [1, -3, -2] = true := by decide +kernel
theorem subd8_4_577 : subd8_4 [1, -3, -1] = true := by decide +kernel
theorem subd8_4_578 : subd8_4 [1, -3, 0] = true := by decide +kernel
theorem subd8_4_579 : subd8_4 [1, -3, 1] = true := by decide +kernel
theorem subd8_4_580 : subd8_4 [1, -3, 2] = true := by decide +kernel
theorem subd8_4_581 : subd8_4 [1, -3, 3] = true := by decide +kernel
theorem subd8_4_582 : subd8_4 [1, -3, 4] = true := by decide +kernel
theorem subd8_4_583 : subd8_4 [1, -3, 5] = true := by decide +kernel
theorem subd8_4_584 : subd8_4 [1, -2, -8] = true := by decide +kernel
theorem subd8_4_585 : subd8_4 [1, -2, -7] = true := by decide +kernel
theorem subd8_4_586 : subd8_4 [1, -2, -6] = true := by decide +kernel
theorem subd8_4_587 : subd8_4 [1, -2, -5] = true := by decide +kernel
theorem subd8_4_588 : subd8_4 [1, -2, -4] = true := by decide +kernel
theorem subd8_4_589 : subd8_4 [1, -2, -3] = true := by decide +kernel
theorem subd8_4_590 : subd8_4 [1, -2, -2] = true := by decide +kernel
theorem subd8_4_591 : subd8_4 [1, -2, -1] = true := by decide +kernel
theorem subd8_4_592 : subd8_4 [1, -2, 0] = true := by decide +kernel
theorem subd8_4_593 : subd8_4 [1, -2, 1] = true := by decide +kernel
theorem subd8_4_594 : subd8_4 [1, -2, 2] = true := by decide +kernel
theorem subd8_4_595 : subd8_4 [1, -2, 3] = true := by decide +kernel
theorem subd8_4_596 : subd8_4 [1, -2, 4] = true := by decide +kernel
theorem subd8_4_597 : subd8_4 [1, -2, 5] = true := by decide +kernel
theorem subd8_4_598 : subd8_4 [1, -2, 6] = true := by decide +kernel
theorem subd8_4_599 : subd8_4 [1, -1, -8] = true := by decide +kernel
theorem subd8_4_600 : subd8_4 [1, -1, -7] = true := by decide +kernel
theorem subd8_4_601 : subd8_4 [1, -1, -6] = true := by decide +kernel
theorem subd8_4_602 : subd8_4 [1, -1, -5] = true := by decide +kernel
theorem subd8_4_603 : subd8_4 [1, -1, -4] = true := by decide +kernel
theorem subd8_4_604 : subd8_4 [1, -1, -3] = true := by decide +kernel
theorem subd8_4_605 : subd8_4 [1, -1, -2] = true := by decide +kernel
theorem subd8_4_606 : subd8_4 [1, -1, -1] = true := by decide +kernel
theorem subd8_4_607 : subd8_4 [1, -1, 0] = true := by decide +kernel
theorem sbd8_4_18 : ∀ q ∈ blkd8_4_18, subd8_4 q = true := by
  unfold blkd8_4_18
  exact List.forall_mem_cons.2 ⟨subd8_4_576, List.forall_mem_cons.2 ⟨subd8_4_577, List.forall_mem_cons.2 ⟨subd8_4_578, List.forall_mem_cons.2 ⟨subd8_4_579, List.forall_mem_cons.2 ⟨subd8_4_580, List.forall_mem_cons.2 ⟨subd8_4_581, List.forall_mem_cons.2 ⟨subd8_4_582, List.forall_mem_cons.2 ⟨subd8_4_583, List.forall_mem_cons.2 ⟨subd8_4_584, List.forall_mem_cons.2 ⟨subd8_4_585, List.forall_mem_cons.2 ⟨subd8_4_586, List.forall_mem_cons.2 ⟨subd8_4_587, List.forall_mem_cons.2 ⟨subd8_4_588, List.forall_mem_cons.2 ⟨subd8_4_589, List.forall_mem_cons.2 ⟨subd8_4_590, List.forall_mem_cons.2 ⟨subd8_4_591, List.forall_mem_cons.2 ⟨subd8_4_592, List.forall_mem_cons.2 ⟨subd8_4_593, List.forall_mem_cons.2 ⟨subd8_4_594, List.forall_mem_cons.2 ⟨subd8_4_595, List.forall_mem_cons.2 ⟨subd8_4_596, List.forall_mem_cons.2 ⟨subd8_4_597, List.forall_mem_cons.2 ⟨subd8_4_598, List.forall_mem_cons.2 ⟨subd8_4_599, List.forall_mem_cons.2 ⟨subd8_4_600, List.forall_mem_cons.2 ⟨subd8_4_601, List.forall_mem_cons.2 ⟨subd8_4_602, List.forall_mem_cons.2 ⟨subd8_4_603, List.forall_mem_cons.2 ⟨subd8_4_604, List.forall_mem_cons.2 ⟨subd8_4_605, List.forall_mem_cons.2 ⟨subd8_4_606, List.forall_mem_cons.2 ⟨subd8_4_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_608 : subd8_4 [1, -1, 1] = true := by decide +kernel
theorem subd8_4_609 : subd8_4 [1, -1, 2] = true := by decide +kernel
theorem subd8_4_610 : subd8_4 [1, -1, 3] = true := by decide +kernel
theorem subd8_4_611 : subd8_4 [1, -1, 4] = true := by decide +kernel
theorem subd8_4_612 : subd8_4 [1, -1, 5] = true := by decide +kernel
theorem subd8_4_613 : subd8_4 [1, -1, 6] = true := by decide +kernel
theorem subd8_4_614 : subd8_4 [1, -1, 7] = true := by decide +kernel
theorem subd8_4_615 : subd8_4 [1, 0, -8] = true := by decide +kernel
theorem subd8_4_616 : subd8_4 [1, 0, -7] = true := by decide +kernel
theorem subd8_4_617 : subd8_4 [1, 0, -6] = true := by decide +kernel
theorem subd8_4_618 : subd8_4 [1, 0, -5] = true := by decide +kernel
theorem subd8_4_619 : subd8_4 [1, 0, -4] = true := by decide +kernel
theorem subd8_4_620 : subd8_4 [1, 0, -3] = true := by decide +kernel
theorem subd8_4_621 : subd8_4 [1, 0, -2] = true := by decide +kernel
theorem subd8_4_622 : subd8_4 [1, 0, -1] = true := by decide +kernel
theorem subd8_4_623 : subd8_4 [1, 0, 0] = true := by decide +kernel
theorem subd8_4_624 : subd8_4 [1, 0, 1] = true := by decide +kernel
theorem subd8_4_625 : subd8_4 [1, 0, 2] = true := by decide +kernel
theorem subd8_4_626 : subd8_4 [1, 0, 3] = true := by decide +kernel
theorem subd8_4_627 : subd8_4 [1, 0, 4] = true := by decide +kernel
theorem subd8_4_628 : subd8_4 [1, 0, 5] = true := by decide +kernel
theorem subd8_4_629 : subd8_4 [1, 0, 6] = true := by decide +kernel
theorem subd8_4_630 : subd8_4 [1, 0, 7] = true := by decide +kernel
theorem subd8_4_631 : subd8_4 [1, 1, -7] = true := by decide +kernel
theorem subd8_4_632 : subd8_4 [1, 1, -6] = true := by decide +kernel
theorem subd8_4_633 : subd8_4 [1, 1, -5] = true := by decide +kernel
theorem subd8_4_634 : subd8_4 [1, 1, -4] = true := by decide +kernel
theorem subd8_4_635 : subd8_4 [1, 1, -3] = true := by decide +kernel
theorem subd8_4_636 : subd8_4 [1, 1, -2] = true := by decide +kernel
theorem subd8_4_637 : subd8_4 [1, 1, -1] = true := by decide +kernel
theorem subd8_4_638 : subd8_4 [1, 1, 0] = true := by decide +kernel
theorem subd8_4_639 : subd8_4 [1, 1, 1] = true := by decide +kernel
theorem sbd8_4_19 : ∀ q ∈ blkd8_4_19, subd8_4 q = true := by
  unfold blkd8_4_19
  exact List.forall_mem_cons.2 ⟨subd8_4_608, List.forall_mem_cons.2 ⟨subd8_4_609, List.forall_mem_cons.2 ⟨subd8_4_610, List.forall_mem_cons.2 ⟨subd8_4_611, List.forall_mem_cons.2 ⟨subd8_4_612, List.forall_mem_cons.2 ⟨subd8_4_613, List.forall_mem_cons.2 ⟨subd8_4_614, List.forall_mem_cons.2 ⟨subd8_4_615, List.forall_mem_cons.2 ⟨subd8_4_616, List.forall_mem_cons.2 ⟨subd8_4_617, List.forall_mem_cons.2 ⟨subd8_4_618, List.forall_mem_cons.2 ⟨subd8_4_619, List.forall_mem_cons.2 ⟨subd8_4_620, List.forall_mem_cons.2 ⟨subd8_4_621, List.forall_mem_cons.2 ⟨subd8_4_622, List.forall_mem_cons.2 ⟨subd8_4_623, List.forall_mem_cons.2 ⟨subd8_4_624, List.forall_mem_cons.2 ⟨subd8_4_625, List.forall_mem_cons.2 ⟨subd8_4_626, List.forall_mem_cons.2 ⟨subd8_4_627, List.forall_mem_cons.2 ⟨subd8_4_628, List.forall_mem_cons.2 ⟨subd8_4_629, List.forall_mem_cons.2 ⟨subd8_4_630, List.forall_mem_cons.2 ⟨subd8_4_631, List.forall_mem_cons.2 ⟨subd8_4_632, List.forall_mem_cons.2 ⟨subd8_4_633, List.forall_mem_cons.2 ⟨subd8_4_634, List.forall_mem_cons.2 ⟨subd8_4_635, List.forall_mem_cons.2 ⟨subd8_4_636, List.forall_mem_cons.2 ⟨subd8_4_637, List.forall_mem_cons.2 ⟨subd8_4_638, List.forall_mem_cons.2 ⟨subd8_4_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_640 : subd8_4 [1, 1, 2] = true := by decide +kernel
theorem subd8_4_641 : subd8_4 [1, 1, 3] = true := by decide +kernel
theorem subd8_4_642 : subd8_4 [1, 1, 4] = true := by decide +kernel
theorem subd8_4_643 : subd8_4 [1, 1, 5] = true := by decide +kernel
theorem subd8_4_644 : subd8_4 [1, 1, 6] = true := by decide +kernel
theorem subd8_4_645 : subd8_4 [1, 1, 7] = true := by decide +kernel
theorem subd8_4_646 : subd8_4 [1, 1, 8] = true := by decide +kernel
theorem subd8_4_647 : subd8_4 [1, 2, -6] = true := by decide +kernel
theorem subd8_4_648 : subd8_4 [1, 2, -5] = true := by decide +kernel
theorem subd8_4_649 : subd8_4 [1, 2, -4] = true := by decide +kernel
theorem subd8_4_650 : subd8_4 [1, 2, -3] = true := by decide +kernel
theorem subd8_4_651 : subd8_4 [1, 2, -2] = true := by decide +kernel
theorem subd8_4_652 : subd8_4 [1, 2, -1] = true := by decide +kernel
theorem subd8_4_653 : subd8_4 [1, 2, 0] = true := by decide +kernel
theorem subd8_4_654 : subd8_4 [1, 2, 1] = true := by decide +kernel
theorem subd8_4_655 : subd8_4 [1, 2, 2] = true := by decide +kernel
theorem subd8_4_656 : subd8_4 [1, 2, 3] = true := by decide +kernel
theorem subd8_4_657 : subd8_4 [1, 2, 4] = true := by decide +kernel
theorem subd8_4_658 : subd8_4 [1, 2, 5] = true := by decide +kernel
theorem subd8_4_659 : subd8_4 [1, 2, 6] = true := by decide +kernel
theorem subd8_4_660 : subd8_4 [1, 2, 7] = true := by decide +kernel
theorem subd8_4_661 : subd8_4 [1, 2, 8] = true := by decide +kernel
theorem subd8_4_662 : subd8_4 [1, 3, -6] = true := by decide +kernel
theorem subd8_4_663 : subd8_4 [1, 3, -5] = true := by decide +kernel
theorem subd8_4_664 : subd8_4 [1, 3, -4] = true := by decide +kernel
theorem subd8_4_665 : subd8_4 [1, 3, -3] = true := by decide +kernel
theorem subd8_4_666 : subd8_4 [1, 3, -2] = true := by decide +kernel
theorem subd8_4_667 : subd8_4 [1, 3, -1] = true := by decide +kernel
theorem subd8_4_668 : subd8_4 [1, 3, 0] = true := by decide +kernel
theorem subd8_4_669 : subd8_4 [1, 3, 1] = true := by decide +kernel
theorem subd8_4_670 : subd8_4 [1, 3, 2] = true := by decide +kernel
theorem subd8_4_671 : subd8_4 [1, 3, 3] = true := by decide +kernel
theorem sbd8_4_20 : ∀ q ∈ blkd8_4_20, subd8_4 q = true := by
  unfold blkd8_4_20
  exact List.forall_mem_cons.2 ⟨subd8_4_640, List.forall_mem_cons.2 ⟨subd8_4_641, List.forall_mem_cons.2 ⟨subd8_4_642, List.forall_mem_cons.2 ⟨subd8_4_643, List.forall_mem_cons.2 ⟨subd8_4_644, List.forall_mem_cons.2 ⟨subd8_4_645, List.forall_mem_cons.2 ⟨subd8_4_646, List.forall_mem_cons.2 ⟨subd8_4_647, List.forall_mem_cons.2 ⟨subd8_4_648, List.forall_mem_cons.2 ⟨subd8_4_649, List.forall_mem_cons.2 ⟨subd8_4_650, List.forall_mem_cons.2 ⟨subd8_4_651, List.forall_mem_cons.2 ⟨subd8_4_652, List.forall_mem_cons.2 ⟨subd8_4_653, List.forall_mem_cons.2 ⟨subd8_4_654, List.forall_mem_cons.2 ⟨subd8_4_655, List.forall_mem_cons.2 ⟨subd8_4_656, List.forall_mem_cons.2 ⟨subd8_4_657, List.forall_mem_cons.2 ⟨subd8_4_658, List.forall_mem_cons.2 ⟨subd8_4_659, List.forall_mem_cons.2 ⟨subd8_4_660, List.forall_mem_cons.2 ⟨subd8_4_661, List.forall_mem_cons.2 ⟨subd8_4_662, List.forall_mem_cons.2 ⟨subd8_4_663, List.forall_mem_cons.2 ⟨subd8_4_664, List.forall_mem_cons.2 ⟨subd8_4_665, List.forall_mem_cons.2 ⟨subd8_4_666, List.forall_mem_cons.2 ⟨subd8_4_667, List.forall_mem_cons.2 ⟨subd8_4_668, List.forall_mem_cons.2 ⟨subd8_4_669, List.forall_mem_cons.2 ⟨subd8_4_670, List.forall_mem_cons.2 ⟨subd8_4_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_672 : subd8_4 [1, 3, 4] = true := by decide +kernel
theorem subd8_4_673 : subd8_4 [1, 3, 5] = true := by decide +kernel
theorem subd8_4_674 : subd8_4 [1, 3, 6] = true := by decide +kernel
theorem subd8_4_675 : subd8_4 [1, 3, 7] = true := by decide +kernel
theorem subd8_4_676 : subd8_4 [1, 3, 8] = true := by decide +kernel
theorem subd8_4_677 : subd8_4 [1, 4] = true := by decide +kernel
theorem subd8_4_678 : subd8_4 [1, 5] = true := by decide +kernel
theorem subd8_4_679 : subd8_4 [1, 6] = true := by decide +kernel
theorem subd8_4_680 : subd8_4 [1, 7] = true := by decide +kernel
theorem subd8_4_681 : subd8_4 [2, -8] = true := by decide +kernel
theorem subd8_4_682 : subd8_4 [2, -7] = true := by decide +kernel
theorem subd8_4_683 : subd8_4 [2, -6] = true := by decide +kernel
theorem subd8_4_684 : subd8_4 [2, -5] = true := by decide +kernel
theorem subd8_4_685 : subd8_4 [2, -4, -8] = true := by decide +kernel
theorem subd8_4_686 : subd8_4 [2, -4, -7] = true := by decide +kernel
theorem subd8_4_687 : subd8_4 [2, -4, -6] = true := by decide +kernel
theorem subd8_4_688 : subd8_4 [2, -4, -5] = true := by decide +kernel
theorem subd8_4_689 : subd8_4 [2, -4, -4] = true := by decide +kernel
theorem subd8_4_690 : subd8_4 [2, -4, -3] = true := by decide +kernel
theorem subd8_4_691 : subd8_4 [2, -4, -2] = true := by decide +kernel
theorem subd8_4_692 : subd8_4 [2, -4, -1] = true := by decide +kernel
theorem subd8_4_693 : subd8_4 [2, -4, 0] = true := by decide +kernel
theorem subd8_4_694 : subd8_4 [2, -4, 1] = true := by decide +kernel
theorem subd8_4_695 : subd8_4 [2, -4, 2] = true := by decide +kernel
theorem subd8_4_696 : subd8_4 [2, -4, 3] = true := by decide +kernel
theorem subd8_4_697 : subd8_4 [2, -4, 4] = true := by decide +kernel
theorem subd8_4_698 : subd8_4 [2, -4, 5] = true := by decide +kernel
theorem subd8_4_699 : subd8_4 [2, -3, -8] = true := by decide +kernel
theorem subd8_4_700 : subd8_4 [2, -3, -7] = true := by decide +kernel
theorem subd8_4_701 : subd8_4 [2, -3, -6] = true := by decide +kernel
theorem subd8_4_702 : subd8_4 [2, -3, -5] = true := by decide +kernel
theorem subd8_4_703 : subd8_4 [2, -3, -4] = true := by decide +kernel
theorem sbd8_4_21 : ∀ q ∈ blkd8_4_21, subd8_4 q = true := by
  unfold blkd8_4_21
  exact List.forall_mem_cons.2 ⟨subd8_4_672, List.forall_mem_cons.2 ⟨subd8_4_673, List.forall_mem_cons.2 ⟨subd8_4_674, List.forall_mem_cons.2 ⟨subd8_4_675, List.forall_mem_cons.2 ⟨subd8_4_676, List.forall_mem_cons.2 ⟨subd8_4_677, List.forall_mem_cons.2 ⟨subd8_4_678, List.forall_mem_cons.2 ⟨subd8_4_679, List.forall_mem_cons.2 ⟨subd8_4_680, List.forall_mem_cons.2 ⟨subd8_4_681, List.forall_mem_cons.2 ⟨subd8_4_682, List.forall_mem_cons.2 ⟨subd8_4_683, List.forall_mem_cons.2 ⟨subd8_4_684, List.forall_mem_cons.2 ⟨subd8_4_685, List.forall_mem_cons.2 ⟨subd8_4_686, List.forall_mem_cons.2 ⟨subd8_4_687, List.forall_mem_cons.2 ⟨subd8_4_688, List.forall_mem_cons.2 ⟨subd8_4_689, List.forall_mem_cons.2 ⟨subd8_4_690, List.forall_mem_cons.2 ⟨subd8_4_691, List.forall_mem_cons.2 ⟨subd8_4_692, List.forall_mem_cons.2 ⟨subd8_4_693, List.forall_mem_cons.2 ⟨subd8_4_694, List.forall_mem_cons.2 ⟨subd8_4_695, List.forall_mem_cons.2 ⟨subd8_4_696, List.forall_mem_cons.2 ⟨subd8_4_697, List.forall_mem_cons.2 ⟨subd8_4_698, List.forall_mem_cons.2 ⟨subd8_4_699, List.forall_mem_cons.2 ⟨subd8_4_700, List.forall_mem_cons.2 ⟨subd8_4_701, List.forall_mem_cons.2 ⟨subd8_4_702, List.forall_mem_cons.2 ⟨subd8_4_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_704 : subd8_4 [2, -3, -3] = true := by decide +kernel
theorem subd8_4_705 : subd8_4 [2, -3, -2] = true := by decide +kernel
theorem subd8_4_706 : subd8_4 [2, -3, -1] = true := by decide +kernel
theorem subd8_4_707 : subd8_4 [2, -3, 0] = true := by decide +kernel
theorem subd8_4_708 : subd8_4 [2, -3, 1] = true := by decide +kernel
theorem subd8_4_709 : subd8_4 [2, -3, 2] = true := by decide +kernel
theorem subd8_4_710 : subd8_4 [2, -3, 3] = true := by decide +kernel
theorem subd8_4_711 : subd8_4 [2, -3, 4] = true := by decide +kernel
theorem subd8_4_712 : subd8_4 [2, -3, 5] = true := by decide +kernel
theorem subd8_4_713 : subd8_4 [2, -3, 6] = true := by decide +kernel
theorem subd8_4_714 : subd8_4 [2, -2, -8] = true := by decide +kernel
theorem subd8_4_715 : subd8_4 [2, -2, -7] = true := by decide +kernel
theorem subd8_4_716 : subd8_4 [2, -2, -6] = true := by decide +kernel
theorem subd8_4_717 : subd8_4 [2, -2, -5] = true := by decide +kernel
theorem subd8_4_718 : subd8_4 [2, -2, -4] = true := by decide +kernel
theorem subd8_4_719 : subd8_4 [2, -2, -3] = true := by decide +kernel
theorem subd8_4_720 : subd8_4 [2, -2, -2] = true := by decide +kernel
theorem subd8_4_721 : subd8_4 [2, -2, -1] = true := by decide +kernel
theorem subd8_4_722 : subd8_4 [2, -2, 0] = true := by decide +kernel
theorem subd8_4_723 : subd8_4 [2, -2, 1] = true := by decide +kernel
theorem subd8_4_724 : subd8_4 [2, -2, 2] = true := by decide +kernel
theorem subd8_4_725 : subd8_4 [2, -2, 3] = true := by decide +kernel
theorem subd8_4_726 : subd8_4 [2, -2, 4] = true := by decide +kernel
theorem subd8_4_727 : subd8_4 [2, -2, 5] = true := by decide +kernel
theorem subd8_4_728 : subd8_4 [2, -2, 6] = true := by decide +kernel
theorem subd8_4_729 : subd8_4 [2, -1, -7] = true := by decide +kernel
theorem subd8_4_730 : subd8_4 [2, -1, -6] = true := by decide +kernel
theorem subd8_4_731 : subd8_4 [2, -1, -5] = true := by decide +kernel
theorem subd8_4_732 : subd8_4 [2, -1, -4] = true := by decide +kernel
theorem subd8_4_733 : subd8_4 [2, -1, -3] = true := by decide +kernel
theorem subd8_4_734 : subd8_4 [2, -1, -2] = true := by decide +kernel
theorem subd8_4_735 : subd8_4 [2, -1, -1] = true := by decide +kernel
theorem sbd8_4_22 : ∀ q ∈ blkd8_4_22, subd8_4 q = true := by
  unfold blkd8_4_22
  exact List.forall_mem_cons.2 ⟨subd8_4_704, List.forall_mem_cons.2 ⟨subd8_4_705, List.forall_mem_cons.2 ⟨subd8_4_706, List.forall_mem_cons.2 ⟨subd8_4_707, List.forall_mem_cons.2 ⟨subd8_4_708, List.forall_mem_cons.2 ⟨subd8_4_709, List.forall_mem_cons.2 ⟨subd8_4_710, List.forall_mem_cons.2 ⟨subd8_4_711, List.forall_mem_cons.2 ⟨subd8_4_712, List.forall_mem_cons.2 ⟨subd8_4_713, List.forall_mem_cons.2 ⟨subd8_4_714, List.forall_mem_cons.2 ⟨subd8_4_715, List.forall_mem_cons.2 ⟨subd8_4_716, List.forall_mem_cons.2 ⟨subd8_4_717, List.forall_mem_cons.2 ⟨subd8_4_718, List.forall_mem_cons.2 ⟨subd8_4_719, List.forall_mem_cons.2 ⟨subd8_4_720, List.forall_mem_cons.2 ⟨subd8_4_721, List.forall_mem_cons.2 ⟨subd8_4_722, List.forall_mem_cons.2 ⟨subd8_4_723, List.forall_mem_cons.2 ⟨subd8_4_724, List.forall_mem_cons.2 ⟨subd8_4_725, List.forall_mem_cons.2 ⟨subd8_4_726, List.forall_mem_cons.2 ⟨subd8_4_727, List.forall_mem_cons.2 ⟨subd8_4_728, List.forall_mem_cons.2 ⟨subd8_4_729, List.forall_mem_cons.2 ⟨subd8_4_730, List.forall_mem_cons.2 ⟨subd8_4_731, List.forall_mem_cons.2 ⟨subd8_4_732, List.forall_mem_cons.2 ⟨subd8_4_733, List.forall_mem_cons.2 ⟨subd8_4_734, List.forall_mem_cons.2 ⟨subd8_4_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_736 : subd8_4 [2, -1, 0] = true := by decide +kernel
theorem subd8_4_737 : subd8_4 [2, -1, 1] = true := by decide +kernel
theorem subd8_4_738 : subd8_4 [2, -1, 2] = true := by decide +kernel
theorem subd8_4_739 : subd8_4 [2, -1, 3] = true := by decide +kernel
theorem subd8_4_740 : subd8_4 [2, -1, 4] = true := by decide +kernel
theorem subd8_4_741 : subd8_4 [2, -1, 5] = true := by decide +kernel
theorem subd8_4_742 : subd8_4 [2, -1, 6] = true := by decide +kernel
theorem subd8_4_743 : subd8_4 [2, -1, 7] = true := by decide +kernel
theorem subd8_4_744 : subd8_4 [2, 0, -7] = true := by decide +kernel
theorem subd8_4_745 : subd8_4 [2, 0, -6] = true := by decide +kernel
theorem subd8_4_746 : subd8_4 [2, 0, -5] = true := by decide +kernel
theorem subd8_4_747 : subd8_4 [2, 0, -4] = true := by decide +kernel
theorem subd8_4_748 : subd8_4 [2, 0, -3] = true := by decide +kernel
theorem subd8_4_749 : subd8_4 [2, 0, -2] = true := by decide +kernel
theorem subd8_4_750 : subd8_4 [2, 0, -1] = true := by decide +kernel
theorem subd8_4_751 : subd8_4 [2, 0, 0] = true := by decide +kernel
theorem subd8_4_752 : subd8_4 [2, 0, 1] = true := by decide +kernel
theorem subd8_4_753 : subd8_4 [2, 0, 2] = true := by decide +kernel
theorem subd8_4_754 : subd8_4 [2, 0, 3] = true := by decide +kernel
theorem subd8_4_755 : subd8_4 [2, 0, 4] = true := by decide +kernel
theorem subd8_4_756 : subd8_4 [2, 0, 5] = true := by decide +kernel
theorem subd8_4_757 : subd8_4 [2, 0, 6] = true := by decide +kernel
theorem subd8_4_758 : subd8_4 [2, 0, 7] = true := by decide +kernel
theorem subd8_4_759 : subd8_4 [2, 0, 8] = true := by decide +kernel
theorem subd8_4_760 : subd8_4 [2, 1, -6] = true := by decide +kernel
theorem subd8_4_761 : subd8_4 [2, 1, -5] = true := by decide +kernel
theorem subd8_4_762 : subd8_4 [2, 1, -4] = true := by decide +kernel
theorem subd8_4_763 : subd8_4 [2, 1, -3] = true := by decide +kernel
theorem subd8_4_764 : subd8_4 [2, 1, -2] = true := by decide +kernel
theorem subd8_4_765 : subd8_4 [2, 1, -1] = true := by decide +kernel
theorem subd8_4_766 : subd8_4 [2, 1, 0] = true := by decide +kernel
theorem subd8_4_767 : subd8_4 [2, 1, 1] = true := by decide +kernel
theorem sbd8_4_23 : ∀ q ∈ blkd8_4_23, subd8_4 q = true := by
  unfold blkd8_4_23
  exact List.forall_mem_cons.2 ⟨subd8_4_736, List.forall_mem_cons.2 ⟨subd8_4_737, List.forall_mem_cons.2 ⟨subd8_4_738, List.forall_mem_cons.2 ⟨subd8_4_739, List.forall_mem_cons.2 ⟨subd8_4_740, List.forall_mem_cons.2 ⟨subd8_4_741, List.forall_mem_cons.2 ⟨subd8_4_742, List.forall_mem_cons.2 ⟨subd8_4_743, List.forall_mem_cons.2 ⟨subd8_4_744, List.forall_mem_cons.2 ⟨subd8_4_745, List.forall_mem_cons.2 ⟨subd8_4_746, List.forall_mem_cons.2 ⟨subd8_4_747, List.forall_mem_cons.2 ⟨subd8_4_748, List.forall_mem_cons.2 ⟨subd8_4_749, List.forall_mem_cons.2 ⟨subd8_4_750, List.forall_mem_cons.2 ⟨subd8_4_751, List.forall_mem_cons.2 ⟨subd8_4_752, List.forall_mem_cons.2 ⟨subd8_4_753, List.forall_mem_cons.2 ⟨subd8_4_754, List.forall_mem_cons.2 ⟨subd8_4_755, List.forall_mem_cons.2 ⟨subd8_4_756, List.forall_mem_cons.2 ⟨subd8_4_757, List.forall_mem_cons.2 ⟨subd8_4_758, List.forall_mem_cons.2 ⟨subd8_4_759, List.forall_mem_cons.2 ⟨subd8_4_760, List.forall_mem_cons.2 ⟨subd8_4_761, List.forall_mem_cons.2 ⟨subd8_4_762, List.forall_mem_cons.2 ⟨subd8_4_763, List.forall_mem_cons.2 ⟨subd8_4_764, List.forall_mem_cons.2 ⟨subd8_4_765, List.forall_mem_cons.2 ⟨subd8_4_766, List.forall_mem_cons.2 ⟨subd8_4_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_768 : subd8_4 [2, 1, 2] = true := by decide +kernel
theorem subd8_4_769 : subd8_4 [2, 1, 3] = true := by decide +kernel
theorem subd8_4_770 : subd8_4 [2, 1, 4] = true := by decide +kernel
theorem subd8_4_771 : subd8_4 [2, 1, 5] = true := by decide +kernel
theorem subd8_4_772 : subd8_4 [2, 1, 6] = true := by decide +kernel
theorem subd8_4_773 : subd8_4 [2, 1, 7] = true := by decide +kernel
theorem subd8_4_774 : subd8_4 [2, 1, 8] = true := by decide +kernel
theorem subd8_4_775 : subd8_4 [2, 2, -6] = true := by decide +kernel
theorem subd8_4_776 : subd8_4 [2, 2, -5] = true := by decide +kernel
theorem subd8_4_777 : subd8_4 [2, 2, -4] = true := by decide +kernel
theorem subd8_4_778 : subd8_4 [2, 2, -3] = true := by decide +kernel
theorem subd8_4_779 : subd8_4 [2, 2, -2] = true := by decide +kernel
theorem subd8_4_780 : subd8_4 [2, 2, -1] = true := by decide +kernel
theorem subd8_4_781 : subd8_4 [2, 2, 0] = true := by decide +kernel
theorem subd8_4_782 : subd8_4 [2, 2, 1] = true := by decide +kernel
theorem subd8_4_783 : subd8_4 [2, 2, 2] = true := by decide +kernel
theorem subd8_4_784 : subd8_4 [2, 2, 3] = true := by decide +kernel
theorem subd8_4_785 : subd8_4 [2, 2, 4] = true := by decide +kernel
theorem subd8_4_786 : subd8_4 [2, 2, 5] = true := by decide +kernel
theorem subd8_4_787 : subd8_4 [2, 2, 6] = true := by decide +kernel
theorem subd8_4_788 : subd8_4 [2, 2, 7] = true := by decide +kernel
theorem subd8_4_789 : subd8_4 [2, 2, 8] = true := by decide +kernel
theorem subd8_4_790 : subd8_4 [2, 3, -5] = true := by decide +kernel
theorem subd8_4_791 : subd8_4 [2, 3, -4] = true := by decide +kernel
theorem subd8_4_792 : subd8_4 [2, 3, -3] = true := by decide +kernel
theorem subd8_4_793 : subd8_4 [2, 3, -2] = true := by decide +kernel
theorem subd8_4_794 : subd8_4 [2, 3, -1] = true := by decide +kernel
theorem subd8_4_795 : subd8_4 [2, 3, 0] = true := by decide +kernel
theorem subd8_4_796 : subd8_4 [2, 3, 1] = true := by decide +kernel
theorem subd8_4_797 : subd8_4 [2, 3, 2] = true := by decide +kernel
theorem subd8_4_798 : subd8_4 [2, 3, 3] = true := by decide +kernel
theorem subd8_4_799 : subd8_4 [2, 3, 4] = true := by decide +kernel
theorem sbd8_4_24 : ∀ q ∈ blkd8_4_24, subd8_4 q = true := by
  unfold blkd8_4_24
  exact List.forall_mem_cons.2 ⟨subd8_4_768, List.forall_mem_cons.2 ⟨subd8_4_769, List.forall_mem_cons.2 ⟨subd8_4_770, List.forall_mem_cons.2 ⟨subd8_4_771, List.forall_mem_cons.2 ⟨subd8_4_772, List.forall_mem_cons.2 ⟨subd8_4_773, List.forall_mem_cons.2 ⟨subd8_4_774, List.forall_mem_cons.2 ⟨subd8_4_775, List.forall_mem_cons.2 ⟨subd8_4_776, List.forall_mem_cons.2 ⟨subd8_4_777, List.forall_mem_cons.2 ⟨subd8_4_778, List.forall_mem_cons.2 ⟨subd8_4_779, List.forall_mem_cons.2 ⟨subd8_4_780, List.forall_mem_cons.2 ⟨subd8_4_781, List.forall_mem_cons.2 ⟨subd8_4_782, List.forall_mem_cons.2 ⟨subd8_4_783, List.forall_mem_cons.2 ⟨subd8_4_784, List.forall_mem_cons.2 ⟨subd8_4_785, List.forall_mem_cons.2 ⟨subd8_4_786, List.forall_mem_cons.2 ⟨subd8_4_787, List.forall_mem_cons.2 ⟨subd8_4_788, List.forall_mem_cons.2 ⟨subd8_4_789, List.forall_mem_cons.2 ⟨subd8_4_790, List.forall_mem_cons.2 ⟨subd8_4_791, List.forall_mem_cons.2 ⟨subd8_4_792, List.forall_mem_cons.2 ⟨subd8_4_793, List.forall_mem_cons.2 ⟨subd8_4_794, List.forall_mem_cons.2 ⟨subd8_4_795, List.forall_mem_cons.2 ⟨subd8_4_796, List.forall_mem_cons.2 ⟨subd8_4_797, List.forall_mem_cons.2 ⟨subd8_4_798, List.forall_mem_cons.2 ⟨subd8_4_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_800 : subd8_4 [2, 3, 5] = true := by decide +kernel
theorem subd8_4_801 : subd8_4 [2, 3, 6] = true := by decide +kernel
theorem subd8_4_802 : subd8_4 [2, 3, 7] = true := by decide +kernel
theorem subd8_4_803 : subd8_4 [2, 3, 8] = true := by decide +kernel
theorem subd8_4_804 : subd8_4 [2, 4] = true := by decide +kernel
theorem subd8_4_805 : subd8_4 [2, 5] = true := by decide +kernel
theorem subd8_4_806 : subd8_4 [2, 6] = true := by decide +kernel
theorem subd8_4_807 : subd8_4 [3, -7] = true := by decide +kernel
theorem subd8_4_808 : subd8_4 [3, -6] = true := by decide +kernel
theorem subd8_4_809 : subd8_4 [3, -5] = true := by decide +kernel
theorem subd8_4_810 : subd8_4 [3, -4] = true := by decide +kernel
theorem subd8_4_811 : subd8_4 [3, -3, -7] = true := by decide +kernel
theorem subd8_4_812 : subd8_4 [3, -3, -6] = true := by decide +kernel
theorem subd8_4_813 : subd8_4 [3, -3, -5] = true := by decide +kernel
theorem subd8_4_814 : subd8_4 [3, -3, -4] = true := by decide +kernel
theorem subd8_4_815 : subd8_4 [3, -3, -3] = true := by decide +kernel
theorem subd8_4_816 : subd8_4 [3, -3, -2] = true := by decide +kernel
theorem subd8_4_817 : subd8_4 [3, -3, -1] = true := by decide +kernel
theorem subd8_4_818 : subd8_4 [3, -3, 0] = true := by decide +kernel
theorem subd8_4_819 : subd8_4 [3, -3, 1] = true := by decide +kernel
theorem subd8_4_820 : subd8_4 [3, -3, 2] = true := by decide +kernel
theorem subd8_4_821 : subd8_4 [3, -3, 3] = true := by decide +kernel
theorem subd8_4_822 : subd8_4 [3, -3, 4] = true := by decide +kernel
theorem subd8_4_823 : subd8_4 [3, -3, 5] = true := by decide +kernel
theorem subd8_4_824 : subd8_4 [3, -3, 6] = true := by decide +kernel
theorem subd8_4_825 : subd8_4 [3, -2, -7] = true := by decide +kernel
theorem subd8_4_826 : subd8_4 [3, -2, -6] = true := by decide +kernel
theorem subd8_4_827 : subd8_4 [3, -2, -5] = true := by decide +kernel
theorem subd8_4_828 : subd8_4 [3, -2, -4] = true := by decide +kernel
theorem subd8_4_829 : subd8_4 [3, -2, -3] = true := by decide +kernel
theorem subd8_4_830 : subd8_4 [3, -2, -2] = true := by decide +kernel
theorem subd8_4_831 : subd8_4 [3, -2, -1] = true := by decide +kernel
theorem sbd8_4_25 : ∀ q ∈ blkd8_4_25, subd8_4 q = true := by
  unfold blkd8_4_25
  exact List.forall_mem_cons.2 ⟨subd8_4_800, List.forall_mem_cons.2 ⟨subd8_4_801, List.forall_mem_cons.2 ⟨subd8_4_802, List.forall_mem_cons.2 ⟨subd8_4_803, List.forall_mem_cons.2 ⟨subd8_4_804, List.forall_mem_cons.2 ⟨subd8_4_805, List.forall_mem_cons.2 ⟨subd8_4_806, List.forall_mem_cons.2 ⟨subd8_4_807, List.forall_mem_cons.2 ⟨subd8_4_808, List.forall_mem_cons.2 ⟨subd8_4_809, List.forall_mem_cons.2 ⟨subd8_4_810, List.forall_mem_cons.2 ⟨subd8_4_811, List.forall_mem_cons.2 ⟨subd8_4_812, List.forall_mem_cons.2 ⟨subd8_4_813, List.forall_mem_cons.2 ⟨subd8_4_814, List.forall_mem_cons.2 ⟨subd8_4_815, List.forall_mem_cons.2 ⟨subd8_4_816, List.forall_mem_cons.2 ⟨subd8_4_817, List.forall_mem_cons.2 ⟨subd8_4_818, List.forall_mem_cons.2 ⟨subd8_4_819, List.forall_mem_cons.2 ⟨subd8_4_820, List.forall_mem_cons.2 ⟨subd8_4_821, List.forall_mem_cons.2 ⟨subd8_4_822, List.forall_mem_cons.2 ⟨subd8_4_823, List.forall_mem_cons.2 ⟨subd8_4_824, List.forall_mem_cons.2 ⟨subd8_4_825, List.forall_mem_cons.2 ⟨subd8_4_826, List.forall_mem_cons.2 ⟨subd8_4_827, List.forall_mem_cons.2 ⟨subd8_4_828, List.forall_mem_cons.2 ⟨subd8_4_829, List.forall_mem_cons.2 ⟨subd8_4_830, List.forall_mem_cons.2 ⟨subd8_4_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C110
