import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_3_384 : subd19_3 [-3, 3, 7] = true := by decide +kernel
theorem subd19_3_385 : subd19_3 [-3, 4, -8] = true := by decide +kernel
theorem subd19_3_386 : subd19_3 [-3, 4, -7] = true := by decide +kernel
theorem subd19_3_387 : subd19_3 [-3, 4, -6] = true := by decide +kernel
theorem subd19_3_388 : subd19_3 [-3, 4, -5] = true := by decide +kernel
theorem subd19_3_389 : subd19_3 [-3, 4, -4] = true := by decide +kernel
theorem subd19_3_390 : subd19_3 [-3, 4, -3] = true := by decide +kernel
theorem subd19_3_391 : subd19_3 [-3, 4, -2] = true := by decide +kernel
theorem subd19_3_392 : subd19_3 [-3, 4, -1] = true := by decide +kernel
theorem subd19_3_393 : subd19_3 [-3, 4, 0] = true := by decide +kernel
theorem subd19_3_394 : subd19_3 [-3, 4, 1] = true := by decide +kernel
theorem subd19_3_395 : subd19_3 [-3, 4, 2] = true := by decide +kernel
theorem subd19_3_396 : subd19_3 [-3, 4, 3] = true := by decide +kernel
theorem subd19_3_397 : subd19_3 [-3, 4, 4] = true := by decide +kernel
theorem subd19_3_398 : subd19_3 [-3, 4, 5] = true := by decide +kernel
theorem subd19_3_399 : subd19_3 [-3, 4, 6] = true := by decide +kernel
theorem subd19_3_400 : subd19_3 [-3, 5] = true := by decide +kernel
theorem subd19_3_401 : subd19_3 [-3, 6] = true := by decide +kernel
theorem subd19_3_402 : subd19_3 [-3, 7] = true := by decide +kernel
theorem subd19_3_403 : subd19_3 [-2, -8] = true := by decide +kernel
theorem subd19_3_404 : subd19_3 [-2, -7] = true := by decide +kernel
theorem subd19_3_405 : subd19_3 [-2, -6] = true := by decide +kernel
theorem subd19_3_406 : subd19_3 [-2, -5] = true := by decide +kernel
theorem subd19_3_407 : subd19_3 [-2, -4, -5] = true := by decide +kernel
theorem subd19_3_408 : subd19_3 [-2, -4, -4] = true := by decide +kernel
theorem subd19_3_409 : subd19_3 [-2, -4, -3] = true := by decide +kernel
theorem subd19_3_410 : subd19_3 [-2, -4, -2] = true := by decide +kernel
theorem subd19_3_411 : subd19_3 [-2, -4, -1] = true := by decide +kernel
theorem subd19_3_412 : subd19_3 [-2, -4, 0] = true := by decide +kernel
theorem subd19_3_413 : subd19_3 [-2, -4, 1] = true := by decide +kernel
theorem subd19_3_414 : subd19_3 [-2, -4, 2] = true := by decide +kernel
theorem subd19_3_415 : subd19_3 [-2, -4, 3] = true := by decide +kernel
theorem sbd19_3_12 : ∀ q ∈ blkd19_3_12, subd19_3 q = true := by
  unfold blkd19_3_12
  exact List.forall_mem_cons.2 ⟨subd19_3_384, List.forall_mem_cons.2 ⟨subd19_3_385, List.forall_mem_cons.2 ⟨subd19_3_386, List.forall_mem_cons.2 ⟨subd19_3_387, List.forall_mem_cons.2 ⟨subd19_3_388, List.forall_mem_cons.2 ⟨subd19_3_389, List.forall_mem_cons.2 ⟨subd19_3_390, List.forall_mem_cons.2 ⟨subd19_3_391, List.forall_mem_cons.2 ⟨subd19_3_392, List.forall_mem_cons.2 ⟨subd19_3_393, List.forall_mem_cons.2 ⟨subd19_3_394, List.forall_mem_cons.2 ⟨subd19_3_395, List.forall_mem_cons.2 ⟨subd19_3_396, List.forall_mem_cons.2 ⟨subd19_3_397, List.forall_mem_cons.2 ⟨subd19_3_398, List.forall_mem_cons.2 ⟨subd19_3_399, List.forall_mem_cons.2 ⟨subd19_3_400, List.forall_mem_cons.2 ⟨subd19_3_401, List.forall_mem_cons.2 ⟨subd19_3_402, List.forall_mem_cons.2 ⟨subd19_3_403, List.forall_mem_cons.2 ⟨subd19_3_404, List.forall_mem_cons.2 ⟨subd19_3_405, List.forall_mem_cons.2 ⟨subd19_3_406, List.forall_mem_cons.2 ⟨subd19_3_407, List.forall_mem_cons.2 ⟨subd19_3_408, List.forall_mem_cons.2 ⟨subd19_3_409, List.forall_mem_cons.2 ⟨subd19_3_410, List.forall_mem_cons.2 ⟨subd19_3_411, List.forall_mem_cons.2 ⟨subd19_3_412, List.forall_mem_cons.2 ⟨subd19_3_413, List.forall_mem_cons.2 ⟨subd19_3_414, List.forall_mem_cons.2 ⟨subd19_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_416 : subd19_3 [-2, -4, 4] = true := by decide +kernel
theorem subd19_3_417 : subd19_3 [-2, -4, 5] = true := by decide +kernel
theorem subd19_3_418 : subd19_3 [-2, -4, 6] = true := by decide +kernel
theorem subd19_3_419 : subd19_3 [-2, -4, 7] = true := by decide +kernel
theorem subd19_3_420 : subd19_3 [-2, -4, 8] = true := by decide +kernel
theorem subd19_3_421 : subd19_3 [-2, -4, 9] = true := by decide +kernel
theorem subd19_3_422 : subd19_3 [-2, -3, -6] = true := by decide +kernel
theorem subd19_3_423 : subd19_3 [-2, -3, -5] = true := by decide +kernel
theorem subd19_3_424 : subd19_3 [-2, -3, -4] = true := by decide +kernel
theorem subd19_3_425 : subd19_3 [-2, -3, -3] = true := by decide +kernel
theorem subd19_3_426 : subd19_3 [-2, -3, -2] = true := by decide +kernel
theorem subd19_3_427 : subd19_3 [-2, -3, -1] = true := by decide +kernel
theorem subd19_3_428 : subd19_3 [-2, -3, 0] = true := by decide +kernel
theorem subd19_3_429 : subd19_3 [-2, -3, 1] = true := by decide +kernel
theorem subd19_3_430 : subd19_3 [-2, -3, 2] = true := by decide +kernel
theorem subd19_3_431 : subd19_3 [-2, -3, 3] = true := by decide +kernel
theorem subd19_3_432 : subd19_3 [-2, -3, 4] = true := by decide +kernel
theorem subd19_3_433 : subd19_3 [-2, -3, 5] = true := by decide +kernel
theorem subd19_3_434 : subd19_3 [-2, -3, 6] = true := by decide +kernel
theorem subd19_3_435 : subd19_3 [-2, -3, 7] = true := by decide +kernel
theorem subd19_3_436 : subd19_3 [-2, -3, 8] = true := by decide +kernel
theorem subd19_3_437 : subd19_3 [-2, -3, 9] = true := by decide +kernel
theorem subd19_3_438 : subd19_3 [-2, -2, -7] = true := by decide +kernel
theorem subd19_3_439 : subd19_3 [-2, -2, -6] = true := by decide +kernel
theorem subd19_3_440 : subd19_3 [-2, -2, -5] = true := by decide +kernel
theorem subd19_3_441 : subd19_3 [-2, -2, -4] = true := by decide +kernel
theorem subd19_3_442 : subd19_3 [-2, -2, -3] = true := by decide +kernel
theorem subd19_3_443 : subd19_3 [-2, -2, -2] = true := by decide +kernel
theorem subd19_3_444 : subd19_3 [-2, -2, -1] = true := by decide +kernel
theorem subd19_3_445 : subd19_3 [-2, -2, 0] = true := by decide +kernel
theorem subd19_3_446 : subd19_3 [-2, -2, 1] = true := by decide +kernel
theorem subd19_3_447 : subd19_3 [-2, -2, 2] = true := by decide +kernel
theorem sbd19_3_13 : ∀ q ∈ blkd19_3_13, subd19_3 q = true := by
  unfold blkd19_3_13
  exact List.forall_mem_cons.2 ⟨subd19_3_416, List.forall_mem_cons.2 ⟨subd19_3_417, List.forall_mem_cons.2 ⟨subd19_3_418, List.forall_mem_cons.2 ⟨subd19_3_419, List.forall_mem_cons.2 ⟨subd19_3_420, List.forall_mem_cons.2 ⟨subd19_3_421, List.forall_mem_cons.2 ⟨subd19_3_422, List.forall_mem_cons.2 ⟨subd19_3_423, List.forall_mem_cons.2 ⟨subd19_3_424, List.forall_mem_cons.2 ⟨subd19_3_425, List.forall_mem_cons.2 ⟨subd19_3_426, List.forall_mem_cons.2 ⟨subd19_3_427, List.forall_mem_cons.2 ⟨subd19_3_428, List.forall_mem_cons.2 ⟨subd19_3_429, List.forall_mem_cons.2 ⟨subd19_3_430, List.forall_mem_cons.2 ⟨subd19_3_431, List.forall_mem_cons.2 ⟨subd19_3_432, List.forall_mem_cons.2 ⟨subd19_3_433, List.forall_mem_cons.2 ⟨subd19_3_434, List.forall_mem_cons.2 ⟨subd19_3_435, List.forall_mem_cons.2 ⟨subd19_3_436, List.forall_mem_cons.2 ⟨subd19_3_437, List.forall_mem_cons.2 ⟨subd19_3_438, List.forall_mem_cons.2 ⟨subd19_3_439, List.forall_mem_cons.2 ⟨subd19_3_440, List.forall_mem_cons.2 ⟨subd19_3_441, List.forall_mem_cons.2 ⟨subd19_3_442, List.forall_mem_cons.2 ⟨subd19_3_443, List.forall_mem_cons.2 ⟨subd19_3_444, List.forall_mem_cons.2 ⟨subd19_3_445, List.forall_mem_cons.2 ⟨subd19_3_446, List.forall_mem_cons.2 ⟨subd19_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_448 : subd19_3 [-2, -2, 3] = true := by decide +kernel
theorem subd19_3_449 : subd19_3 [-2, -2, 4] = true := by decide +kernel
theorem subd19_3_450 : subd19_3 [-2, -2, 5] = true := by decide +kernel
theorem subd19_3_451 : subd19_3 [-2, -2, 6] = true := by decide +kernel
theorem subd19_3_452 : subd19_3 [-2, -2, 7] = true := by decide +kernel
theorem subd19_3_453 : subd19_3 [-2, -2, 8] = true := by decide +kernel
theorem subd19_3_454 : subd19_3 [-2, -2, 9] = true := by decide +kernel
theorem subd19_3_455 : subd19_3 [-2, -1, -8] = true := by decide +kernel
theorem subd19_3_456 : subd19_3 [-2, -1, -7] = true := by decide +kernel
theorem subd19_3_457 : subd19_3 [-2, -1, -6] = true := by decide +kernel
theorem subd19_3_458 : subd19_3 [-2, -1, -5] = true := by decide +kernel
theorem subd19_3_459 : subd19_3 [-2, -1, -4] = true := by decide +kernel
theorem subd19_3_460 : subd19_3 [-2, -1, -3] = true := by decide +kernel
theorem subd19_3_461 : subd19_3 [-2, -1, -2] = true := by decide +kernel
theorem subd19_3_462 : subd19_3 [-2, -1, -1] = true := by decide +kernel
theorem subd19_3_463 : subd19_3 [-2, -1, 0] = true := by decide +kernel
theorem subd19_3_464 : subd19_3 [-2, -1, 1] = true := by decide +kernel
theorem subd19_3_465 : subd19_3 [-2, -1, 2] = true := by decide +kernel
theorem subd19_3_466 : subd19_3 [-2, -1, 3] = true := by decide +kernel
theorem subd19_3_467 : subd19_3 [-2, -1, 4] = true := by decide +kernel
theorem subd19_3_468 : subd19_3 [-2, -1, 5] = true := by decide +kernel
theorem subd19_3_469 : subd19_3 [-2, -1, 6] = true := by decide +kernel
theorem subd19_3_470 : subd19_3 [-2, -1, 7] = true := by decide +kernel
theorem subd19_3_471 : subd19_3 [-2, -1, 8] = true := by decide +kernel
theorem subd19_3_472 : subd19_3 [-2, -1, 9] = true := by decide +kernel
theorem subd19_3_473 : subd19_3 [-2, 0, -8] = true := by decide +kernel
theorem subd19_3_474 : subd19_3 [-2, 0, -7] = true := by decide +kernel
theorem subd19_3_475 : subd19_3 [-2, 0, -6] = true := by decide +kernel
theorem subd19_3_476 : subd19_3 [-2, 0, -5] = true := by decide +kernel
theorem subd19_3_477 : subd19_3 [-2, 0, -4] = true := by decide +kernel
theorem subd19_3_478 : subd19_3 [-2, 0, -3] = true := by decide +kernel
theorem subd19_3_479 : subd19_3 [-2, 0, -2] = true := by decide +kernel
theorem sbd19_3_14 : ∀ q ∈ blkd19_3_14, subd19_3 q = true := by
  unfold blkd19_3_14
  exact List.forall_mem_cons.2 ⟨subd19_3_448, List.forall_mem_cons.2 ⟨subd19_3_449, List.forall_mem_cons.2 ⟨subd19_3_450, List.forall_mem_cons.2 ⟨subd19_3_451, List.forall_mem_cons.2 ⟨subd19_3_452, List.forall_mem_cons.2 ⟨subd19_3_453, List.forall_mem_cons.2 ⟨subd19_3_454, List.forall_mem_cons.2 ⟨subd19_3_455, List.forall_mem_cons.2 ⟨subd19_3_456, List.forall_mem_cons.2 ⟨subd19_3_457, List.forall_mem_cons.2 ⟨subd19_3_458, List.forall_mem_cons.2 ⟨subd19_3_459, List.forall_mem_cons.2 ⟨subd19_3_460, List.forall_mem_cons.2 ⟨subd19_3_461, List.forall_mem_cons.2 ⟨subd19_3_462, List.forall_mem_cons.2 ⟨subd19_3_463, List.forall_mem_cons.2 ⟨subd19_3_464, List.forall_mem_cons.2 ⟨subd19_3_465, List.forall_mem_cons.2 ⟨subd19_3_466, List.forall_mem_cons.2 ⟨subd19_3_467, List.forall_mem_cons.2 ⟨subd19_3_468, List.forall_mem_cons.2 ⟨subd19_3_469, List.forall_mem_cons.2 ⟨subd19_3_470, List.forall_mem_cons.2 ⟨subd19_3_471, List.forall_mem_cons.2 ⟨subd19_3_472, List.forall_mem_cons.2 ⟨subd19_3_473, List.forall_mem_cons.2 ⟨subd19_3_474, List.forall_mem_cons.2 ⟨subd19_3_475, List.forall_mem_cons.2 ⟨subd19_3_476, List.forall_mem_cons.2 ⟨subd19_3_477, List.forall_mem_cons.2 ⟨subd19_3_478, List.forall_mem_cons.2 ⟨subd19_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_480 : subd19_3 [-2, 0, -1] = true := by decide +kernel
theorem subd19_3_481 : subd19_3 [-2, 0, 0] = true := by decide +kernel
theorem subd19_3_482 : subd19_3 [-2, 0, 1] = true := by decide +kernel
theorem subd19_3_483 : subd19_3 [-2, 0, 2] = true := by decide +kernel
theorem subd19_3_484 : subd19_3 [-2, 0, 3] = true := by decide +kernel
theorem subd19_3_485 : subd19_3 [-2, 0, 4] = true := by decide +kernel
theorem subd19_3_486 : subd19_3 [-2, 0, 5] = true := by decide +kernel
theorem subd19_3_487 : subd19_3 [-2, 0, 6] = true := by decide +kernel
theorem subd19_3_488 : subd19_3 [-2, 0, 7] = true := by decide +kernel
theorem subd19_3_489 : subd19_3 [-2, 0, 8] = true := by decide +kernel
theorem subd19_3_490 : subd19_3 [-2, 0, 9] = true := by decide +kernel
theorem subd19_3_491 : subd19_3 [-2, 1, -9] = true := by decide +kernel
theorem subd19_3_492 : subd19_3 [-2, 1, -8] = true := by decide +kernel
theorem subd19_3_493 : subd19_3 [-2, 1, -7] = true := by decide +kernel
theorem subd19_3_494 : subd19_3 [-2, 1, -6] = true := by decide +kernel
theorem subd19_3_495 : subd19_3 [-2, 1, -5] = true := by decide +kernel
theorem subd19_3_496 : subd19_3 [-2, 1, -4] = true := by decide +kernel
theorem subd19_3_497 : subd19_3 [-2, 1, -3] = true := by decide +kernel
theorem subd19_3_498 : subd19_3 [-2, 1, -2] = true := by decide +kernel
theorem subd19_3_499 : subd19_3 [-2, 1, -1] = true := by decide +kernel
theorem subd19_3_500 : subd19_3 [-2, 1, 0] = true := by decide +kernel
theorem subd19_3_501 : subd19_3 [-2, 1, 1] = true := by decide +kernel
theorem subd19_3_502 : subd19_3 [-2, 1, 2] = true := by decide +kernel
theorem subd19_3_503 : subd19_3 [-2, 1, 3] = true := by decide +kernel
theorem subd19_3_504 : subd19_3 [-2, 1, 4] = true := by decide +kernel
theorem subd19_3_505 : subd19_3 [-2, 1, 5] = true := by decide +kernel
theorem subd19_3_506 : subd19_3 [-2, 1, 6] = true := by decide +kernel
theorem subd19_3_507 : subd19_3 [-2, 1, 7] = true := by decide +kernel
theorem subd19_3_508 : subd19_3 [-2, 1, 8] = true := by decide +kernel
theorem subd19_3_509 : subd19_3 [-2, 2, -9] = true := by decide +kernel
theorem subd19_3_510 : subd19_3 [-2, 2, -8] = true := by decide +kernel
theorem subd19_3_511 : subd19_3 [-2, 2, -7] = true := by decide +kernel
theorem sbd19_3_15 : ∀ q ∈ blkd19_3_15, subd19_3 q = true := by
  unfold blkd19_3_15
  exact List.forall_mem_cons.2 ⟨subd19_3_480, List.forall_mem_cons.2 ⟨subd19_3_481, List.forall_mem_cons.2 ⟨subd19_3_482, List.forall_mem_cons.2 ⟨subd19_3_483, List.forall_mem_cons.2 ⟨subd19_3_484, List.forall_mem_cons.2 ⟨subd19_3_485, List.forall_mem_cons.2 ⟨subd19_3_486, List.forall_mem_cons.2 ⟨subd19_3_487, List.forall_mem_cons.2 ⟨subd19_3_488, List.forall_mem_cons.2 ⟨subd19_3_489, List.forall_mem_cons.2 ⟨subd19_3_490, List.forall_mem_cons.2 ⟨subd19_3_491, List.forall_mem_cons.2 ⟨subd19_3_492, List.forall_mem_cons.2 ⟨subd19_3_493, List.forall_mem_cons.2 ⟨subd19_3_494, List.forall_mem_cons.2 ⟨subd19_3_495, List.forall_mem_cons.2 ⟨subd19_3_496, List.forall_mem_cons.2 ⟨subd19_3_497, List.forall_mem_cons.2 ⟨subd19_3_498, List.forall_mem_cons.2 ⟨subd19_3_499, List.forall_mem_cons.2 ⟨subd19_3_500, List.forall_mem_cons.2 ⟨subd19_3_501, List.forall_mem_cons.2 ⟨subd19_3_502, List.forall_mem_cons.2 ⟨subd19_3_503, List.forall_mem_cons.2 ⟨subd19_3_504, List.forall_mem_cons.2 ⟨subd19_3_505, List.forall_mem_cons.2 ⟨subd19_3_506, List.forall_mem_cons.2 ⟨subd19_3_507, List.forall_mem_cons.2 ⟨subd19_3_508, List.forall_mem_cons.2 ⟨subd19_3_509, List.forall_mem_cons.2 ⟨subd19_3_510, List.forall_mem_cons.2 ⟨subd19_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_512 : subd19_3 [-2, 2, -6] = true := by decide +kernel
theorem subd19_3_513 : subd19_3 [-2, 2, -5] = true := by decide +kernel
theorem subd19_3_514 : subd19_3 [-2, 2, -4] = true := by decide +kernel
theorem subd19_3_515 : subd19_3 [-2, 2, -3] = true := by decide +kernel
theorem subd19_3_516 : subd19_3 [-2, 2, -2] = true := by decide +kernel
theorem subd19_3_517 : subd19_3 [-2, 2, -1] = true := by decide +kernel
theorem subd19_3_518 : subd19_3 [-2, 2, 0] = true := by decide +kernel
theorem subd19_3_519 : subd19_3 [-2, 2, 1] = true := by decide +kernel
theorem subd19_3_520 : subd19_3 [-2, 2, 2] = true := by decide +kernel
theorem subd19_3_521 : subd19_3 [-2, 2, 3] = true := by decide +kernel
theorem subd19_3_522 : subd19_3 [-2, 2, 4] = true := by decide +kernel
theorem subd19_3_523 : subd19_3 [-2, 2, 5] = true := by decide +kernel
theorem subd19_3_524 : subd19_3 [-2, 2, 6] = true := by decide +kernel
theorem subd19_3_525 : subd19_3 [-2, 2, 7] = true := by decide +kernel
theorem subd19_3_526 : subd19_3 [-2, 2, 8] = true := by decide +kernel
theorem subd19_3_527 : subd19_3 [-2, 3, -9] = true := by decide +kernel
theorem subd19_3_528 : subd19_3 [-2, 3, -8] = true := by decide +kernel
theorem subd19_3_529 : subd19_3 [-2, 3, -7] = true := by decide +kernel
theorem subd19_3_530 : subd19_3 [-2, 3, -6] = true := by decide +kernel
theorem subd19_3_531 : subd19_3 [-2, 3, -5] = true := by decide +kernel
theorem subd19_3_532 : subd19_3 [-2, 3, -4] = true := by decide +kernel
theorem subd19_3_533 : subd19_3 [-2, 3, -3] = true := by decide +kernel
theorem subd19_3_534 : subd19_3 [-2, 3, -2] = true := by decide +kernel
theorem subd19_3_535 : subd19_3 [-2, 3, -1] = true := by decide +kernel
theorem subd19_3_536 : subd19_3 [-2, 3, 0] = true := by decide +kernel
theorem subd19_3_537 : subd19_3 [-2, 3, 1] = true := by decide +kernel
theorem subd19_3_538 : subd19_3 [-2, 3, 2] = true := by decide +kernel
theorem subd19_3_539 : subd19_3 [-2, 3, 3] = true := by decide +kernel
theorem subd19_3_540 : subd19_3 [-2, 3, 4] = true := by decide +kernel
theorem subd19_3_541 : subd19_3 [-2, 3, 5] = true := by decide +kernel
theorem subd19_3_542 : subd19_3 [-2, 3, 6] = true := by decide +kernel
theorem subd19_3_543 : subd19_3 [-2, 3, 7] = true := by decide +kernel
theorem sbd19_3_16 : ∀ q ∈ blkd19_3_16, subd19_3 q = true := by
  unfold blkd19_3_16
  exact List.forall_mem_cons.2 ⟨subd19_3_512, List.forall_mem_cons.2 ⟨subd19_3_513, List.forall_mem_cons.2 ⟨subd19_3_514, List.forall_mem_cons.2 ⟨subd19_3_515, List.forall_mem_cons.2 ⟨subd19_3_516, List.forall_mem_cons.2 ⟨subd19_3_517, List.forall_mem_cons.2 ⟨subd19_3_518, List.forall_mem_cons.2 ⟨subd19_3_519, List.forall_mem_cons.2 ⟨subd19_3_520, List.forall_mem_cons.2 ⟨subd19_3_521, List.forall_mem_cons.2 ⟨subd19_3_522, List.forall_mem_cons.2 ⟨subd19_3_523, List.forall_mem_cons.2 ⟨subd19_3_524, List.forall_mem_cons.2 ⟨subd19_3_525, List.forall_mem_cons.2 ⟨subd19_3_526, List.forall_mem_cons.2 ⟨subd19_3_527, List.forall_mem_cons.2 ⟨subd19_3_528, List.forall_mem_cons.2 ⟨subd19_3_529, List.forall_mem_cons.2 ⟨subd19_3_530, List.forall_mem_cons.2 ⟨subd19_3_531, List.forall_mem_cons.2 ⟨subd19_3_532, List.forall_mem_cons.2 ⟨subd19_3_533, List.forall_mem_cons.2 ⟨subd19_3_534, List.forall_mem_cons.2 ⟨subd19_3_535, List.forall_mem_cons.2 ⟨subd19_3_536, List.forall_mem_cons.2 ⟨subd19_3_537, List.forall_mem_cons.2 ⟨subd19_3_538, List.forall_mem_cons.2 ⟨subd19_3_539, List.forall_mem_cons.2 ⟨subd19_3_540, List.forall_mem_cons.2 ⟨subd19_3_541, List.forall_mem_cons.2 ⟨subd19_3_542, List.forall_mem_cons.2 ⟨subd19_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_544 : subd19_3 [-2, 4, -9] = true := by decide +kernel
theorem subd19_3_545 : subd19_3 [-2, 4, -8] = true := by decide +kernel
theorem subd19_3_546 : subd19_3 [-2, 4, -7] = true := by decide +kernel
theorem subd19_3_547 : subd19_3 [-2, 4, -6] = true := by decide +kernel
theorem subd19_3_548 : subd19_3 [-2, 4, -5] = true := by decide +kernel
theorem subd19_3_549 : subd19_3 [-2, 4, -4] = true := by decide +kernel
theorem subd19_3_550 : subd19_3 [-2, 4, -3] = true := by decide +kernel
theorem subd19_3_551 : subd19_3 [-2, 4, -2] = true := by decide +kernel
theorem subd19_3_552 : subd19_3 [-2, 4, -1] = true := by decide +kernel
theorem subd19_3_553 : subd19_3 [-2, 4, 0] = true := by decide +kernel
theorem subd19_3_554 : subd19_3 [-2, 4, 1] = true := by decide +kernel
theorem subd19_3_555 : subd19_3 [-2, 4, 2] = true := by decide +kernel
theorem subd19_3_556 : subd19_3 [-2, 4, 3] = true := by decide +kernel
theorem subd19_3_557 : subd19_3 [-2, 4, 4] = true := by decide +kernel
theorem subd19_3_558 : subd19_3 [-2, 4, 5] = true := by decide +kernel
theorem subd19_3_559 : subd19_3 [-2, 4, 6] = true := by decide +kernel
theorem subd19_3_560 : subd19_3 [-2, 5, -9] = true := by decide +kernel
theorem subd19_3_561 : subd19_3 [-2, 5, -8] = true := by decide +kernel
theorem subd19_3_562 : subd19_3 [-2, 5, -7] = true := by decide +kernel
theorem subd19_3_563 : subd19_3 [-2, 5, -6] = true := by decide +kernel
theorem subd19_3_564 : subd19_3 [-2, 5, -5] = true := by decide +kernel
theorem subd19_3_565 : subd19_3 [-2, 5, -4] = true := by decide +kernel
theorem subd19_3_566 : subd19_3 [-2, 5, -3] = true := by decide +kernel
theorem subd19_3_567 : subd19_3 [-2, 5, -2] = true := by decide +kernel
theorem subd19_3_568 : subd19_3 [-2, 5, -1] = true := by decide +kernel
theorem subd19_3_569 : subd19_3 [-2, 5, 0] = true := by decide +kernel
theorem subd19_3_570 : subd19_3 [-2, 5, 1] = true := by decide +kernel
theorem subd19_3_571 : subd19_3 [-2, 5, 2] = true := by decide +kernel
theorem subd19_3_572 : subd19_3 [-2, 5, 3] = true := by decide +kernel
theorem subd19_3_573 : subd19_3 [-2, 5, 4] = true := by decide +kernel
theorem subd19_3_574 : subd19_3 [-2, 5, 5] = true := by decide +kernel
theorem subd19_3_575 : subd19_3 [-2, 6] = true := by decide +kernel
theorem sbd19_3_17 : ∀ q ∈ blkd19_3_17, subd19_3 q = true := by
  unfold blkd19_3_17
  exact List.forall_mem_cons.2 ⟨subd19_3_544, List.forall_mem_cons.2 ⟨subd19_3_545, List.forall_mem_cons.2 ⟨subd19_3_546, List.forall_mem_cons.2 ⟨subd19_3_547, List.forall_mem_cons.2 ⟨subd19_3_548, List.forall_mem_cons.2 ⟨subd19_3_549, List.forall_mem_cons.2 ⟨subd19_3_550, List.forall_mem_cons.2 ⟨subd19_3_551, List.forall_mem_cons.2 ⟨subd19_3_552, List.forall_mem_cons.2 ⟨subd19_3_553, List.forall_mem_cons.2 ⟨subd19_3_554, List.forall_mem_cons.2 ⟨subd19_3_555, List.forall_mem_cons.2 ⟨subd19_3_556, List.forall_mem_cons.2 ⟨subd19_3_557, List.forall_mem_cons.2 ⟨subd19_3_558, List.forall_mem_cons.2 ⟨subd19_3_559, List.forall_mem_cons.2 ⟨subd19_3_560, List.forall_mem_cons.2 ⟨subd19_3_561, List.forall_mem_cons.2 ⟨subd19_3_562, List.forall_mem_cons.2 ⟨subd19_3_563, List.forall_mem_cons.2 ⟨subd19_3_564, List.forall_mem_cons.2 ⟨subd19_3_565, List.forall_mem_cons.2 ⟨subd19_3_566, List.forall_mem_cons.2 ⟨subd19_3_567, List.forall_mem_cons.2 ⟨subd19_3_568, List.forall_mem_cons.2 ⟨subd19_3_569, List.forall_mem_cons.2 ⟨subd19_3_570, List.forall_mem_cons.2 ⟨subd19_3_571, List.forall_mem_cons.2 ⟨subd19_3_572, List.forall_mem_cons.2 ⟨subd19_3_573, List.forall_mem_cons.2 ⟨subd19_3_574, List.forall_mem_cons.2 ⟨subd19_3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_576 : subd19_3 [-2, 7] = true := by decide +kernel
theorem subd19_3_577 : subd19_3 [-1, -8] = true := by decide +kernel
theorem subd19_3_578 : subd19_3 [-1, -7] = true := by decide +kernel
theorem subd19_3_579 : subd19_3 [-1, -6] = true := by decide +kernel
theorem subd19_3_580 : subd19_3 [-1, -5, -5] = true := by decide +kernel
theorem subd19_3_581 : subd19_3 [-1, -5, -4] = true := by decide +kernel
theorem subd19_3_582 : subd19_3 [-1, -5, -3] = true := by decide +kernel
theorem subd19_3_583 : subd19_3 [-1, -5, -2] = true := by decide +kernel
theorem subd19_3_584 : subd19_3 [-1, -5, -1] = true := by decide +kernel
theorem subd19_3_585 : subd19_3 [-1, -5, 0] = true := by decide +kernel
theorem subd19_3_586 : subd19_3 [-1, -5, 1] = true := by decide +kernel
theorem subd19_3_587 : subd19_3 [-1, -5, 2] = true := by decide +kernel
theorem subd19_3_588 : subd19_3 [-1, -5, 3] = true := by decide +kernel
theorem subd19_3_589 : subd19_3 [-1, -5, 4] = true := by decide +kernel
theorem subd19_3_590 : subd19_3 [-1, -5, 5] = true := by decide +kernel
theorem subd19_3_591 : subd19_3 [-1, -5, 6] = true := by decide +kernel
theorem subd19_3_592 : subd19_3 [-1, -5, 7] = true := by decide +kernel
theorem subd19_3_593 : subd19_3 [-1, -5, 8] = true := by decide +kernel
theorem subd19_3_594 : subd19_3 [-1, -5, 9] = true := by decide +kernel
theorem subd19_3_595 : subd19_3 [-1, -4, -6] = true := by decide +kernel
theorem subd19_3_596 : subd19_3 [-1, -4, -5] = true := by decide +kernel
theorem subd19_3_597 : subd19_3 [-1, -4, -4] = true := by decide +kernel
theorem subd19_3_598 : subd19_3 [-1, -4, -3] = true := by decide +kernel
theorem subd19_3_599 : subd19_3 [-1, -4, -2] = true := by decide +kernel
theorem subd19_3_600 : subd19_3 [-1, -4, -1] = true := by decide +kernel
theorem subd19_3_601 : subd19_3 [-1, -4, 0] = true := by decide +kernel
theorem subd19_3_602 : subd19_3 [-1, -4, 1] = true := by decide +kernel
theorem subd19_3_603 : subd19_3 [-1, -4, 2] = true := by decide +kernel
theorem subd19_3_604 : subd19_3 [-1, -4, 3] = true := by decide +kernel
theorem subd19_3_605 : subd19_3 [-1, -4, 4] = true := by decide +kernel
theorem subd19_3_606 : subd19_3 [-1, -4, 5] = true := by decide +kernel
theorem subd19_3_607 : subd19_3 [-1, -4, 6] = true := by decide +kernel
theorem sbd19_3_18 : ∀ q ∈ blkd19_3_18, subd19_3 q = true := by
  unfold blkd19_3_18
  exact List.forall_mem_cons.2 ⟨subd19_3_576, List.forall_mem_cons.2 ⟨subd19_3_577, List.forall_mem_cons.2 ⟨subd19_3_578, List.forall_mem_cons.2 ⟨subd19_3_579, List.forall_mem_cons.2 ⟨subd19_3_580, List.forall_mem_cons.2 ⟨subd19_3_581, List.forall_mem_cons.2 ⟨subd19_3_582, List.forall_mem_cons.2 ⟨subd19_3_583, List.forall_mem_cons.2 ⟨subd19_3_584, List.forall_mem_cons.2 ⟨subd19_3_585, List.forall_mem_cons.2 ⟨subd19_3_586, List.forall_mem_cons.2 ⟨subd19_3_587, List.forall_mem_cons.2 ⟨subd19_3_588, List.forall_mem_cons.2 ⟨subd19_3_589, List.forall_mem_cons.2 ⟨subd19_3_590, List.forall_mem_cons.2 ⟨subd19_3_591, List.forall_mem_cons.2 ⟨subd19_3_592, List.forall_mem_cons.2 ⟨subd19_3_593, List.forall_mem_cons.2 ⟨subd19_3_594, List.forall_mem_cons.2 ⟨subd19_3_595, List.forall_mem_cons.2 ⟨subd19_3_596, List.forall_mem_cons.2 ⟨subd19_3_597, List.forall_mem_cons.2 ⟨subd19_3_598, List.forall_mem_cons.2 ⟨subd19_3_599, List.forall_mem_cons.2 ⟨subd19_3_600, List.forall_mem_cons.2 ⟨subd19_3_601, List.forall_mem_cons.2 ⟨subd19_3_602, List.forall_mem_cons.2 ⟨subd19_3_603, List.forall_mem_cons.2 ⟨subd19_3_604, List.forall_mem_cons.2 ⟨subd19_3_605, List.forall_mem_cons.2 ⟨subd19_3_606, List.forall_mem_cons.2 ⟨subd19_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_608 : subd19_3 [-1, -4, 7] = true := by decide +kernel
theorem subd19_3_609 : subd19_3 [-1, -4, 8] = true := by decide +kernel
theorem subd19_3_610 : subd19_3 [-1, -4, 9] = true := by decide +kernel
theorem subd19_3_611 : subd19_3 [-1, -3, -7] = true := by decide +kernel
theorem subd19_3_612 : subd19_3 [-1, -3, -6] = true := by decide +kernel
theorem subd19_3_613 : subd19_3 [-1, -3, -5] = true := by decide +kernel
theorem subd19_3_614 : subd19_3 [-1, -3, -4] = true := by decide +kernel
theorem subd19_3_615 : subd19_3 [-1, -3, -3] = true := by decide +kernel
theorem subd19_3_616 : subd19_3 [-1, -3, -2] = true := by decide +kernel
theorem subd19_3_617 : subd19_3 [-1, -3, -1] = true := by decide +kernel
theorem subd19_3_618 : subd19_3 [-1, -3, 0] = true := by decide +kernel
theorem subd19_3_619 : subd19_3 [-1, -3, 1] = true := by decide +kernel
theorem subd19_3_620 : subd19_3 [-1, -3, 2] = true := by decide +kernel
theorem subd19_3_621 : subd19_3 [-1, -3, 3] = true := by decide +kernel
theorem subd19_3_622 : subd19_3 [-1, -3, 4] = true := by decide +kernel
theorem subd19_3_623 : subd19_3 [-1, -3, 5] = true := by decide +kernel
theorem subd19_3_624 : subd19_3 [-1, -3, 6] = true := by decide +kernel
theorem subd19_3_625 : subd19_3 [-1, -3, 7] = true := by decide +kernel
theorem subd19_3_626 : subd19_3 [-1, -3, 8] = true := by decide +kernel
theorem subd19_3_627 : subd19_3 [-1, -3, 9] = true := by decide +kernel
theorem subd19_3_628 : subd19_3 [-1, -2, -8] = true := by decide +kernel
theorem subd19_3_629 : subd19_3 [-1, -2, -7] = true := by decide +kernel
theorem subd19_3_630 : subd19_3 [-1, -2, -6] = true := by decide +kernel
theorem subd19_3_631 : subd19_3 [-1, -2, -5] = true := by decide +kernel
theorem subd19_3_632 : subd19_3 [-1, -2, -4] = true := by decide +kernel
theorem subd19_3_633 : subd19_3 [-1, -2, -3] = true := by decide +kernel
theorem subd19_3_634 : subd19_3 [-1, -2, -2] = true := by decide +kernel
theorem subd19_3_635 : subd19_3 [-1, -2, -1] = true := by decide +kernel
theorem subd19_3_636 : subd19_3 [-1, -2, 0] = true := by decide +kernel
theorem subd19_3_637 : subd19_3 [-1, -2, 1] = true := by decide +kernel
theorem subd19_3_638 : subd19_3 [-1, -2, 2] = true := by decide +kernel
theorem subd19_3_639 : subd19_3 [-1, -2, 3] = true := by decide +kernel
theorem sbd19_3_19 : ∀ q ∈ blkd19_3_19, subd19_3 q = true := by
  unfold blkd19_3_19
  exact List.forall_mem_cons.2 ⟨subd19_3_608, List.forall_mem_cons.2 ⟨subd19_3_609, List.forall_mem_cons.2 ⟨subd19_3_610, List.forall_mem_cons.2 ⟨subd19_3_611, List.forall_mem_cons.2 ⟨subd19_3_612, List.forall_mem_cons.2 ⟨subd19_3_613, List.forall_mem_cons.2 ⟨subd19_3_614, List.forall_mem_cons.2 ⟨subd19_3_615, List.forall_mem_cons.2 ⟨subd19_3_616, List.forall_mem_cons.2 ⟨subd19_3_617, List.forall_mem_cons.2 ⟨subd19_3_618, List.forall_mem_cons.2 ⟨subd19_3_619, List.forall_mem_cons.2 ⟨subd19_3_620, List.forall_mem_cons.2 ⟨subd19_3_621, List.forall_mem_cons.2 ⟨subd19_3_622, List.forall_mem_cons.2 ⟨subd19_3_623, List.forall_mem_cons.2 ⟨subd19_3_624, List.forall_mem_cons.2 ⟨subd19_3_625, List.forall_mem_cons.2 ⟨subd19_3_626, List.forall_mem_cons.2 ⟨subd19_3_627, List.forall_mem_cons.2 ⟨subd19_3_628, List.forall_mem_cons.2 ⟨subd19_3_629, List.forall_mem_cons.2 ⟨subd19_3_630, List.forall_mem_cons.2 ⟨subd19_3_631, List.forall_mem_cons.2 ⟨subd19_3_632, List.forall_mem_cons.2 ⟨subd19_3_633, List.forall_mem_cons.2 ⟨subd19_3_634, List.forall_mem_cons.2 ⟨subd19_3_635, List.forall_mem_cons.2 ⟨subd19_3_636, List.forall_mem_cons.2 ⟨subd19_3_637, List.forall_mem_cons.2 ⟨subd19_3_638, List.forall_mem_cons.2 ⟨subd19_3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_640 : subd19_3 [-1, -2, 4] = true := by decide +kernel
theorem subd19_3_641 : subd19_3 [-1, -2, 5] = true := by decide +kernel
theorem subd19_3_642 : subd19_3 [-1, -2, 6] = true := by decide +kernel
theorem subd19_3_643 : subd19_3 [-1, -2, 7] = true := by decide +kernel
theorem subd19_3_644 : subd19_3 [-1, -2, 8] = true := by decide +kernel
theorem subd19_3_645 : subd19_3 [-1, -2, 9] = true := by decide +kernel
theorem subd19_3_646 : subd19_3 [-1, -1, -8] = true := by decide +kernel
theorem subd19_3_647 : subd19_3 [-1, -1, -7] = true := by decide +kernel
theorem subd19_3_648 : subd19_3 [-1, -1, -6] = true := by decide +kernel
theorem subd19_3_649 : subd19_3 [-1, -1, -5] = true := by decide +kernel
theorem subd19_3_650 : subd19_3 [-1, -1, -4] = true := by decide +kernel
theorem subd19_3_651 : subd19_3 [-1, -1, -3] = true := by decide +kernel
theorem subd19_3_652 : subd19_3 [-1, -1, -2] = true := by decide +kernel
theorem subd19_3_653 : subd19_3 [-1, -1, -1] = true := by decide +kernel
theorem subd19_3_654 : subd19_3 [-1, -1, 0] = true := by decide +kernel
theorem subd19_3_655 : subd19_3 [-1, -1, 1] = true := by decide +kernel
theorem subd19_3_656 : subd19_3 [-1, -1, 2] = true := by decide +kernel
theorem subd19_3_657 : subd19_3 [-1, -1, 3] = true := by decide +kernel
theorem subd19_3_658 : subd19_3 [-1, -1, 4] = true := by decide +kernel
theorem subd19_3_659 : subd19_3 [-1, -1, 5] = true := by decide +kernel
theorem subd19_3_660 : subd19_3 [-1, -1, 6] = true := by decide +kernel
theorem subd19_3_661 : subd19_3 [-1, -1, 7] = true := by decide +kernel
theorem subd19_3_662 : subd19_3 [-1, -1, 8] = true := by decide +kernel
theorem subd19_3_663 : subd19_3 [-1, -1, 9] = true := by decide +kernel
theorem subd19_3_664 : subd19_3 [-1, 0, -9] = true := by decide +kernel
theorem subd19_3_665 : subd19_3 [-1, 0, -8] = true := by decide +kernel
theorem subd19_3_666 : subd19_3 [-1, 0, -7] = true := by decide +kernel
theorem subd19_3_667 : subd19_3 [-1, 0, -6] = true := by decide +kernel
theorem subd19_3_668 : subd19_3 [-1, 0, -5] = true := by decide +kernel
theorem subd19_3_669 : subd19_3 [-1, 0, -4] = true := by decide +kernel
theorem subd19_3_670 : subd19_3 [-1, 0, -3] = true := by decide +kernel
theorem subd19_3_671 : subd19_3 [-1, 0, -2] = true := by decide +kernel
theorem sbd19_3_20 : ∀ q ∈ blkd19_3_20, subd19_3 q = true := by
  unfold blkd19_3_20
  exact List.forall_mem_cons.2 ⟨subd19_3_640, List.forall_mem_cons.2 ⟨subd19_3_641, List.forall_mem_cons.2 ⟨subd19_3_642, List.forall_mem_cons.2 ⟨subd19_3_643, List.forall_mem_cons.2 ⟨subd19_3_644, List.forall_mem_cons.2 ⟨subd19_3_645, List.forall_mem_cons.2 ⟨subd19_3_646, List.forall_mem_cons.2 ⟨subd19_3_647, List.forall_mem_cons.2 ⟨subd19_3_648, List.forall_mem_cons.2 ⟨subd19_3_649, List.forall_mem_cons.2 ⟨subd19_3_650, List.forall_mem_cons.2 ⟨subd19_3_651, List.forall_mem_cons.2 ⟨subd19_3_652, List.forall_mem_cons.2 ⟨subd19_3_653, List.forall_mem_cons.2 ⟨subd19_3_654, List.forall_mem_cons.2 ⟨subd19_3_655, List.forall_mem_cons.2 ⟨subd19_3_656, List.forall_mem_cons.2 ⟨subd19_3_657, List.forall_mem_cons.2 ⟨subd19_3_658, List.forall_mem_cons.2 ⟨subd19_3_659, List.forall_mem_cons.2 ⟨subd19_3_660, List.forall_mem_cons.2 ⟨subd19_3_661, List.forall_mem_cons.2 ⟨subd19_3_662, List.forall_mem_cons.2 ⟨subd19_3_663, List.forall_mem_cons.2 ⟨subd19_3_664, List.forall_mem_cons.2 ⟨subd19_3_665, List.forall_mem_cons.2 ⟨subd19_3_666, List.forall_mem_cons.2 ⟨subd19_3_667, List.forall_mem_cons.2 ⟨subd19_3_668, List.forall_mem_cons.2 ⟨subd19_3_669, List.forall_mem_cons.2 ⟨subd19_3_670, List.forall_mem_cons.2 ⟨subd19_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_672 : subd19_3 [-1, 0, -1] = true := by decide +kernel
theorem subd19_3_673 : subd19_3 [-1, 0, 0] = true := by decide +kernel
theorem subd19_3_674 : subd19_3 [-1, 0, 1] = true := by decide +kernel
theorem subd19_3_675 : subd19_3 [-1, 0, 2] = true := by decide +kernel
theorem subd19_3_676 : subd19_3 [-1, 0, 3] = true := by decide +kernel
theorem subd19_3_677 : subd19_3 [-1, 0, 4] = true := by decide +kernel
theorem subd19_3_678 : subd19_3 [-1, 0, 5] = true := by decide +kernel
theorem subd19_3_679 : subd19_3 [-1, 0, 6] = true := by decide +kernel
theorem subd19_3_680 : subd19_3 [-1, 0, 7] = true := by decide +kernel
theorem subd19_3_681 : subd19_3 [-1, 0, 8] = true := by decide +kernel
theorem subd19_3_682 : subd19_3 [-1, 0, 9] = true := by decide +kernel
theorem subd19_3_683 : subd19_3 [-1, 1, -9] = true := by decide +kernel
theorem subd19_3_684 : subd19_3 [-1, 1, -8] = true := by decide +kernel
theorem subd19_3_685 : subd19_3 [-1, 1, -7] = true := by decide +kernel
theorem subd19_3_686 : subd19_3 [-1, 1, -6] = true := by decide +kernel
theorem subd19_3_687 : subd19_3 [-1, 1, -5] = true := by decide +kernel
theorem subd19_3_688 : subd19_3 [-1, 1, -4] = true := by decide +kernel
theorem subd19_3_689 : subd19_3 [-1, 1, -3] = true := by decide +kernel
theorem subd19_3_690 : subd19_3 [-1, 1, -2] = true := by decide +kernel
theorem subd19_3_691 : subd19_3 [-1, 1, -1] = true := by decide +kernel
theorem subd19_3_692 : subd19_3 [-1, 1, 0] = true := by decide +kernel
theorem subd19_3_693 : subd19_3 [-1, 1, 1] = true := by decide +kernel
theorem subd19_3_694 : subd19_3 [-1, 1, 2] = true := by decide +kernel
theorem subd19_3_695 : subd19_3 [-1, 1, 3] = true := by decide +kernel
theorem subd19_3_696 : subd19_3 [-1, 1, 4] = true := by decide +kernel
theorem subd19_3_697 : subd19_3 [-1, 1, 5] = true := by decide +kernel
theorem subd19_3_698 : subd19_3 [-1, 1, 6] = true := by decide +kernel
theorem subd19_3_699 : subd19_3 [-1, 1, 7] = true := by decide +kernel
theorem subd19_3_700 : subd19_3 [-1, 1, 8] = true := by decide +kernel
theorem subd19_3_701 : subd19_3 [-1, 2, -10] = true := by decide +kernel
theorem subd19_3_702 : subd19_3 [-1, 2, -9] = true := by decide +kernel
theorem subd19_3_703 : subd19_3 [-1, 2, -8] = true := by decide +kernel
theorem sbd19_3_21 : ∀ q ∈ blkd19_3_21, subd19_3 q = true := by
  unfold blkd19_3_21
  exact List.forall_mem_cons.2 ⟨subd19_3_672, List.forall_mem_cons.2 ⟨subd19_3_673, List.forall_mem_cons.2 ⟨subd19_3_674, List.forall_mem_cons.2 ⟨subd19_3_675, List.forall_mem_cons.2 ⟨subd19_3_676, List.forall_mem_cons.2 ⟨subd19_3_677, List.forall_mem_cons.2 ⟨subd19_3_678, List.forall_mem_cons.2 ⟨subd19_3_679, List.forall_mem_cons.2 ⟨subd19_3_680, List.forall_mem_cons.2 ⟨subd19_3_681, List.forall_mem_cons.2 ⟨subd19_3_682, List.forall_mem_cons.2 ⟨subd19_3_683, List.forall_mem_cons.2 ⟨subd19_3_684, List.forall_mem_cons.2 ⟨subd19_3_685, List.forall_mem_cons.2 ⟨subd19_3_686, List.forall_mem_cons.2 ⟨subd19_3_687, List.forall_mem_cons.2 ⟨subd19_3_688, List.forall_mem_cons.2 ⟨subd19_3_689, List.forall_mem_cons.2 ⟨subd19_3_690, List.forall_mem_cons.2 ⟨subd19_3_691, List.forall_mem_cons.2 ⟨subd19_3_692, List.forall_mem_cons.2 ⟨subd19_3_693, List.forall_mem_cons.2 ⟨subd19_3_694, List.forall_mem_cons.2 ⟨subd19_3_695, List.forall_mem_cons.2 ⟨subd19_3_696, List.forall_mem_cons.2 ⟨subd19_3_697, List.forall_mem_cons.2 ⟨subd19_3_698, List.forall_mem_cons.2 ⟨subd19_3_699, List.forall_mem_cons.2 ⟨subd19_3_700, List.forall_mem_cons.2 ⟨subd19_3_701, List.forall_mem_cons.2 ⟨subd19_3_702, List.forall_mem_cons.2 ⟨subd19_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_704 : subd19_3 [-1, 2, -7] = true := by decide +kernel
theorem subd19_3_705 : subd19_3 [-1, 2, -6] = true := by decide +kernel
theorem subd19_3_706 : subd19_3 [-1, 2, -5] = true := by decide +kernel
theorem subd19_3_707 : subd19_3 [-1, 2, -4] = true := by decide +kernel
theorem subd19_3_708 : subd19_3 [-1, 2, -3] = true := by decide +kernel
theorem subd19_3_709 : subd19_3 [-1, 2, -2] = true := by decide +kernel
theorem subd19_3_710 : subd19_3 [-1, 2, -1] = true := by decide +kernel
theorem subd19_3_711 : subd19_3 [-1, 2, 0] = true := by decide +kernel
theorem subd19_3_712 : subd19_3 [-1, 2, 1] = true := by decide +kernel
theorem subd19_3_713 : subd19_3 [-1, 2, 2] = true := by decide +kernel
theorem subd19_3_714 : subd19_3 [-1, 2, 3] = true := by decide +kernel
theorem subd19_3_715 : subd19_3 [-1, 2, 4] = true := by decide +kernel
theorem subd19_3_716 : subd19_3 [-1, 2, 5] = true := by decide +kernel
theorem subd19_3_717 : subd19_3 [-1, 2, 6] = true := by decide +kernel
theorem subd19_3_718 : subd19_3 [-1, 2, 7] = true := by decide +kernel
theorem subd19_3_719 : subd19_3 [-1, 3, -10] = true := by decide +kernel
theorem subd19_3_720 : subd19_3 [-1, 3, -9] = true := by decide +kernel
theorem subd19_3_721 : subd19_3 [-1, 3, -8] = true := by decide +kernel
theorem subd19_3_722 : subd19_3 [-1, 3, -7] = true := by decide +kernel
theorem subd19_3_723 : subd19_3 [-1, 3, -6] = true := by decide +kernel
theorem subd19_3_724 : subd19_3 [-1, 3, -5] = true := by decide +kernel
theorem subd19_3_725 : subd19_3 [-1, 3, -4] = true := by decide +kernel
theorem subd19_3_726 : subd19_3 [-1, 3, -3] = true := by decide +kernel
theorem subd19_3_727 : subd19_3 [-1, 3, -2] = true := by decide +kernel
theorem subd19_3_728 : subd19_3 [-1, 3, -1] = true := by decide +kernel
theorem subd19_3_729 : subd19_3 [-1, 3, 0] = true := by decide +kernel
theorem subd19_3_730 : subd19_3 [-1, 3, 1] = true := by decide +kernel
theorem subd19_3_731 : subd19_3 [-1, 3, 2] = true := by decide +kernel
theorem subd19_3_732 : subd19_3 [-1, 3, 3] = true := by decide +kernel
theorem subd19_3_733 : subd19_3 [-1, 3, 4] = true := by decide +kernel
theorem subd19_3_734 : subd19_3 [-1, 3, 5] = true := by decide +kernel
theorem subd19_3_735 : subd19_3 [-1, 3, 6] = true := by decide +kernel
theorem sbd19_3_22 : ∀ q ∈ blkd19_3_22, subd19_3 q = true := by
  unfold blkd19_3_22
  exact List.forall_mem_cons.2 ⟨subd19_3_704, List.forall_mem_cons.2 ⟨subd19_3_705, List.forall_mem_cons.2 ⟨subd19_3_706, List.forall_mem_cons.2 ⟨subd19_3_707, List.forall_mem_cons.2 ⟨subd19_3_708, List.forall_mem_cons.2 ⟨subd19_3_709, List.forall_mem_cons.2 ⟨subd19_3_710, List.forall_mem_cons.2 ⟨subd19_3_711, List.forall_mem_cons.2 ⟨subd19_3_712, List.forall_mem_cons.2 ⟨subd19_3_713, List.forall_mem_cons.2 ⟨subd19_3_714, List.forall_mem_cons.2 ⟨subd19_3_715, List.forall_mem_cons.2 ⟨subd19_3_716, List.forall_mem_cons.2 ⟨subd19_3_717, List.forall_mem_cons.2 ⟨subd19_3_718, List.forall_mem_cons.2 ⟨subd19_3_719, List.forall_mem_cons.2 ⟨subd19_3_720, List.forall_mem_cons.2 ⟨subd19_3_721, List.forall_mem_cons.2 ⟨subd19_3_722, List.forall_mem_cons.2 ⟨subd19_3_723, List.forall_mem_cons.2 ⟨subd19_3_724, List.forall_mem_cons.2 ⟨subd19_3_725, List.forall_mem_cons.2 ⟨subd19_3_726, List.forall_mem_cons.2 ⟨subd19_3_727, List.forall_mem_cons.2 ⟨subd19_3_728, List.forall_mem_cons.2 ⟨subd19_3_729, List.forall_mem_cons.2 ⟨subd19_3_730, List.forall_mem_cons.2 ⟨subd19_3_731, List.forall_mem_cons.2 ⟨subd19_3_732, List.forall_mem_cons.2 ⟨subd19_3_733, List.forall_mem_cons.2 ⟨subd19_3_734, List.forall_mem_cons.2 ⟨subd19_3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_736 : subd19_3 [-1, 3, 7] = true := by decide +kernel
theorem subd19_3_737 : subd19_3 [-1, 4, -10] = true := by decide +kernel
theorem subd19_3_738 : subd19_3 [-1, 4, -9] = true := by decide +kernel
theorem subd19_3_739 : subd19_3 [-1, 4, -8] = true := by decide +kernel
theorem subd19_3_740 : subd19_3 [-1, 4, -7] = true := by decide +kernel
theorem subd19_3_741 : subd19_3 [-1, 4, -6] = true := by decide +kernel
theorem subd19_3_742 : subd19_3 [-1, 4, -5] = true := by decide +kernel
theorem subd19_3_743 : subd19_3 [-1, 4, -4] = true := by decide +kernel
theorem subd19_3_744 : subd19_3 [-1, 4, -3] = true := by decide +kernel
theorem subd19_3_745 : subd19_3 [-1, 4, -2] = true := by decide +kernel
theorem subd19_3_746 : subd19_3 [-1, 4, -1] = true := by decide +kernel
theorem subd19_3_747 : subd19_3 [-1, 4, 0] = true := by decide +kernel
theorem subd19_3_748 : subd19_3 [-1, 4, 1] = true := by decide +kernel
theorem subd19_3_749 : subd19_3 [-1, 4, 2] = true := by decide +kernel
theorem subd19_3_750 : subd19_3 [-1, 4, 3] = true := by decide +kernel
theorem subd19_3_751 : subd19_3 [-1, 4, 4] = true := by decide +kernel
theorem subd19_3_752 : subd19_3 [-1, 4, 5] = true := by decide +kernel
theorem subd19_3_753 : subd19_3 [-1, 4, 6] = true := by decide +kernel
theorem subd19_3_754 : subd19_3 [-1, 5, -9] = true := by decide +kernel
theorem subd19_3_755 : subd19_3 [-1, 5, -8] = true := by decide +kernel
theorem subd19_3_756 : subd19_3 [-1, 5, -7] = true := by decide +kernel
theorem subd19_3_757 : subd19_3 [-1, 5, -6] = true := by decide +kernel
theorem subd19_3_758 : subd19_3 [-1, 5, -5] = true := by decide +kernel
theorem subd19_3_759 : subd19_3 [-1, 5, -4] = true := by decide +kernel
theorem subd19_3_760 : subd19_3 [-1, 5, -3] = true := by decide +kernel
theorem subd19_3_761 : subd19_3 [-1, 5, -2] = true := by decide +kernel
theorem subd19_3_762 : subd19_3 [-1, 5, -1] = true := by decide +kernel
theorem subd19_3_763 : subd19_3 [-1, 5, 0] = true := by decide +kernel
theorem subd19_3_764 : subd19_3 [-1, 5, 1] = true := by decide +kernel
theorem subd19_3_765 : subd19_3 [-1, 5, 2] = true := by decide +kernel
theorem subd19_3_766 : subd19_3 [-1, 5, 3] = true := by decide +kernel
theorem subd19_3_767 : subd19_3 [-1, 5, 4] = true := by decide +kernel
theorem sbd19_3_23 : ∀ q ∈ blkd19_3_23, subd19_3 q = true := by
  unfold blkd19_3_23
  exact List.forall_mem_cons.2 ⟨subd19_3_736, List.forall_mem_cons.2 ⟨subd19_3_737, List.forall_mem_cons.2 ⟨subd19_3_738, List.forall_mem_cons.2 ⟨subd19_3_739, List.forall_mem_cons.2 ⟨subd19_3_740, List.forall_mem_cons.2 ⟨subd19_3_741, List.forall_mem_cons.2 ⟨subd19_3_742, List.forall_mem_cons.2 ⟨subd19_3_743, List.forall_mem_cons.2 ⟨subd19_3_744, List.forall_mem_cons.2 ⟨subd19_3_745, List.forall_mem_cons.2 ⟨subd19_3_746, List.forall_mem_cons.2 ⟨subd19_3_747, List.forall_mem_cons.2 ⟨subd19_3_748, List.forall_mem_cons.2 ⟨subd19_3_749, List.forall_mem_cons.2 ⟨subd19_3_750, List.forall_mem_cons.2 ⟨subd19_3_751, List.forall_mem_cons.2 ⟨subd19_3_752, List.forall_mem_cons.2 ⟨subd19_3_753, List.forall_mem_cons.2 ⟨subd19_3_754, List.forall_mem_cons.2 ⟨subd19_3_755, List.forall_mem_cons.2 ⟨subd19_3_756, List.forall_mem_cons.2 ⟨subd19_3_757, List.forall_mem_cons.2 ⟨subd19_3_758, List.forall_mem_cons.2 ⟨subd19_3_759, List.forall_mem_cons.2 ⟨subd19_3_760, List.forall_mem_cons.2 ⟨subd19_3_761, List.forall_mem_cons.2 ⟨subd19_3_762, List.forall_mem_cons.2 ⟨subd19_3_763, List.forall_mem_cons.2 ⟨subd19_3_764, List.forall_mem_cons.2 ⟨subd19_3_765, List.forall_mem_cons.2 ⟨subd19_3_766, List.forall_mem_cons.2 ⟨subd19_3_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_768 : subd19_3 [-1, 6] = true := by decide +kernel
theorem subd19_3_769 : subd19_3 [-1, 7] = true := by decide +kernel
theorem subd19_3_770 : subd19_3 [-1, 8] = true := by decide +kernel
theorem subd19_3_771 : subd19_3 [0, -9] = true := by decide +kernel
theorem subd19_3_772 : subd19_3 [0, -8] = true := by decide +kernel
theorem subd19_3_773 : subd19_3 [0, -7] = true := by decide +kernel
theorem subd19_3_774 : subd19_3 [0, -6] = true := by decide +kernel
theorem subd19_3_775 : subd19_3 [0, -5, -5] = true := by decide +kernel
theorem subd19_3_776 : subd19_3 [0, -5, -4] = true := by decide +kernel
theorem subd19_3_777 : subd19_3 [0, -5, -3] = true := by decide +kernel
theorem subd19_3_778 : subd19_3 [0, -5, -2] = true := by decide +kernel
theorem subd19_3_779 : subd19_3 [0, -5, -1] = true := by decide +kernel
theorem subd19_3_780 : subd19_3 [0, -5, 0] = true := by decide +kernel
theorem subd19_3_781 : subd19_3 [0, -5, 1] = true := by decide +kernel
theorem subd19_3_782 : subd19_3 [0, -5, 2] = true := by decide +kernel
theorem subd19_3_783 : subd19_3 [0, -5, 3] = true := by decide +kernel
theorem subd19_3_784 : subd19_3 [0, -5, 4] = true := by decide +kernel
theorem subd19_3_785 : subd19_3 [0, -5, 5] = true := by decide +kernel
theorem subd19_3_786 : subd19_3 [0, -5, 6] = true := by decide +kernel
theorem subd19_3_787 : subd19_3 [0, -5, 7] = true := by decide +kernel
theorem subd19_3_788 : subd19_3 [0, -5, 8] = true := by decide +kernel
theorem subd19_3_789 : subd19_3 [0, -5, 9] = true := by decide +kernel
theorem subd19_3_790 : subd19_3 [0, -4, -6] = true := by decide +kernel
theorem subd19_3_791 : subd19_3 [0, -4, -5] = true := by decide +kernel
theorem subd19_3_792 : subd19_3 [0, -4, -4] = true := by decide +kernel
theorem subd19_3_793 : subd19_3 [0, -4, -3] = true := by decide +kernel
theorem subd19_3_794 : subd19_3 [0, -4, -2] = true := by decide +kernel
theorem subd19_3_795 : subd19_3 [0, -4, -1] = true := by decide +kernel
theorem subd19_3_796 : subd19_3 [0, -4, 0] = true := by decide +kernel
theorem subd19_3_797 : subd19_3 [0, -4, 1] = true := by decide +kernel
theorem subd19_3_798 : subd19_3 [0, -4, 2] = true := by decide +kernel
theorem subd19_3_799 : subd19_3 [0, -4, 3] = true := by decide +kernel
theorem sbd19_3_24 : ∀ q ∈ blkd19_3_24, subd19_3 q = true := by
  unfold blkd19_3_24
  exact List.forall_mem_cons.2 ⟨subd19_3_768, List.forall_mem_cons.2 ⟨subd19_3_769, List.forall_mem_cons.2 ⟨subd19_3_770, List.forall_mem_cons.2 ⟨subd19_3_771, List.forall_mem_cons.2 ⟨subd19_3_772, List.forall_mem_cons.2 ⟨subd19_3_773, List.forall_mem_cons.2 ⟨subd19_3_774, List.forall_mem_cons.2 ⟨subd19_3_775, List.forall_mem_cons.2 ⟨subd19_3_776, List.forall_mem_cons.2 ⟨subd19_3_777, List.forall_mem_cons.2 ⟨subd19_3_778, List.forall_mem_cons.2 ⟨subd19_3_779, List.forall_mem_cons.2 ⟨subd19_3_780, List.forall_mem_cons.2 ⟨subd19_3_781, List.forall_mem_cons.2 ⟨subd19_3_782, List.forall_mem_cons.2 ⟨subd19_3_783, List.forall_mem_cons.2 ⟨subd19_3_784, List.forall_mem_cons.2 ⟨subd19_3_785, List.forall_mem_cons.2 ⟨subd19_3_786, List.forall_mem_cons.2 ⟨subd19_3_787, List.forall_mem_cons.2 ⟨subd19_3_788, List.forall_mem_cons.2 ⟨subd19_3_789, List.forall_mem_cons.2 ⟨subd19_3_790, List.forall_mem_cons.2 ⟨subd19_3_791, List.forall_mem_cons.2 ⟨subd19_3_792, List.forall_mem_cons.2 ⟨subd19_3_793, List.forall_mem_cons.2 ⟨subd19_3_794, List.forall_mem_cons.2 ⟨subd19_3_795, List.forall_mem_cons.2 ⟨subd19_3_796, List.forall_mem_cons.2 ⟨subd19_3_797, List.forall_mem_cons.2 ⟨subd19_3_798, List.forall_mem_cons.2 ⟨subd19_3_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_800 : subd19_3 [0, -4, 4] = true := by decide +kernel
theorem subd19_3_801 : subd19_3 [0, -4, 5] = true := by decide +kernel
theorem subd19_3_802 : subd19_3 [0, -4, 6] = true := by decide +kernel
theorem subd19_3_803 : subd19_3 [0, -4, 7] = true := by decide +kernel
theorem subd19_3_804 : subd19_3 [0, -4, 8] = true := by decide +kernel
theorem subd19_3_805 : subd19_3 [0, -4, 9] = true := by decide +kernel
theorem subd19_3_806 : subd19_3 [0, -3, -7] = true := by decide +kernel
theorem subd19_3_807 : subd19_3 [0, -3, -6] = true := by decide +kernel
theorem subd19_3_808 : subd19_3 [0, -3, -5] = true := by decide +kernel
theorem subd19_3_809 : subd19_3 [0, -3, -4] = true := by decide +kernel
theorem subd19_3_810 : subd19_3 [0, -3, -3] = true := by decide +kernel
theorem subd19_3_811 : subd19_3 [0, -3, -2] = true := by decide +kernel
theorem subd19_3_812 : subd19_3 [0, -3, -1] = true := by decide +kernel
theorem subd19_3_813 : subd19_3 [0, -3, 0] = true := by decide +kernel
theorem subd19_3_814 : subd19_3 [0, -3, 1] = true := by decide +kernel
theorem subd19_3_815 : subd19_3 [0, -3, 2] = true := by decide +kernel
theorem subd19_3_816 : subd19_3 [0, -3, 3] = true := by decide +kernel
theorem subd19_3_817 : subd19_3 [0, -3, 4] = true := by decide +kernel
theorem subd19_3_818 : subd19_3 [0, -3, 5] = true := by decide +kernel
theorem subd19_3_819 : subd19_3 [0, -3, 6] = true := by decide +kernel
theorem subd19_3_820 : subd19_3 [0, -3, 7] = true := by decide +kernel
theorem subd19_3_821 : subd19_3 [0, -3, 8] = true := by decide +kernel
theorem subd19_3_822 : subd19_3 [0, -3, 9] = true := by decide +kernel
theorem subd19_3_823 : subd19_3 [0, -2, -8] = true := by decide +kernel
theorem subd19_3_824 : subd19_3 [0, -2, -7] = true := by decide +kernel
theorem subd19_3_825 : subd19_3 [0, -2, -6] = true := by decide +kernel
theorem subd19_3_826 : subd19_3 [0, -2, -5] = true := by decide +kernel
theorem subd19_3_827 : subd19_3 [0, -2, -4] = true := by decide +kernel
theorem subd19_3_828 : subd19_3 [0, -2, -3] = true := by decide +kernel
theorem subd19_3_829 : subd19_3 [0, -2, -2] = true := by decide +kernel
theorem subd19_3_830 : subd19_3 [0, -2, -1] = true := by decide +kernel
theorem subd19_3_831 : subd19_3 [0, -2, 0] = true := by decide +kernel
theorem sbd19_3_25 : ∀ q ∈ blkd19_3_25, subd19_3 q = true := by
  unfold blkd19_3_25
  exact List.forall_mem_cons.2 ⟨subd19_3_800, List.forall_mem_cons.2 ⟨subd19_3_801, List.forall_mem_cons.2 ⟨subd19_3_802, List.forall_mem_cons.2 ⟨subd19_3_803, List.forall_mem_cons.2 ⟨subd19_3_804, List.forall_mem_cons.2 ⟨subd19_3_805, List.forall_mem_cons.2 ⟨subd19_3_806, List.forall_mem_cons.2 ⟨subd19_3_807, List.forall_mem_cons.2 ⟨subd19_3_808, List.forall_mem_cons.2 ⟨subd19_3_809, List.forall_mem_cons.2 ⟨subd19_3_810, List.forall_mem_cons.2 ⟨subd19_3_811, List.forall_mem_cons.2 ⟨subd19_3_812, List.forall_mem_cons.2 ⟨subd19_3_813, List.forall_mem_cons.2 ⟨subd19_3_814, List.forall_mem_cons.2 ⟨subd19_3_815, List.forall_mem_cons.2 ⟨subd19_3_816, List.forall_mem_cons.2 ⟨subd19_3_817, List.forall_mem_cons.2 ⟨subd19_3_818, List.forall_mem_cons.2 ⟨subd19_3_819, List.forall_mem_cons.2 ⟨subd19_3_820, List.forall_mem_cons.2 ⟨subd19_3_821, List.forall_mem_cons.2 ⟨subd19_3_822, List.forall_mem_cons.2 ⟨subd19_3_823, List.forall_mem_cons.2 ⟨subd19_3_824, List.forall_mem_cons.2 ⟨subd19_3_825, List.forall_mem_cons.2 ⟨subd19_3_826, List.forall_mem_cons.2 ⟨subd19_3_827, List.forall_mem_cons.2 ⟨subd19_3_828, List.forall_mem_cons.2 ⟨subd19_3_829, List.forall_mem_cons.2 ⟨subd19_3_830, List.forall_mem_cons.2 ⟨subd19_3_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_832 : subd19_3 [0, -2, 1] = true := by decide +kernel
theorem subd19_3_833 : subd19_3 [0, -2, 2] = true := by decide +kernel
theorem subd19_3_834 : subd19_3 [0, -2, 3] = true := by decide +kernel
theorem subd19_3_835 : subd19_3 [0, -2, 4] = true := by decide +kernel
theorem subd19_3_836 : subd19_3 [0, -2, 5] = true := by decide +kernel
theorem subd19_3_837 : subd19_3 [0, -2, 6] = true := by decide +kernel
theorem subd19_3_838 : subd19_3 [0, -2, 7] = true := by decide +kernel
theorem subd19_3_839 : subd19_3 [0, -2, 8] = true := by decide +kernel
theorem subd19_3_840 : subd19_3 [0, -2, 9] = true := by decide +kernel
theorem subd19_3_841 : subd19_3 [0, -1, -9] = true := by decide +kernel
theorem subd19_3_842 : subd19_3 [0, -1, -8] = true := by decide +kernel
theorem subd19_3_843 : subd19_3 [0, -1, -7] = true := by decide +kernel
theorem subd19_3_844 : subd19_3 [0, -1, -6] = true := by decide +kernel
theorem subd19_3_845 : subd19_3 [0, -1, -5] = true := by decide +kernel
theorem subd19_3_846 : subd19_3 [0, -1, -4] = true := by decide +kernel
theorem subd19_3_847 : subd19_3 [0, -1, -3] = true := by decide +kernel
theorem subd19_3_848 : subd19_3 [0, -1, -2] = true := by decide +kernel
theorem subd19_3_849 : subd19_3 [0, -1, -1] = true := by decide +kernel
theorem subd19_3_850 : subd19_3 [0, -1, 0] = true := by decide +kernel
theorem subd19_3_851 : subd19_3 [0, -1, 1] = true := by decide +kernel
theorem subd19_3_852 : subd19_3 [0, -1, 2] = true := by decide +kernel
theorem subd19_3_853 : subd19_3 [0, -1, 3] = true := by decide +kernel
theorem subd19_3_854 : subd19_3 [0, -1, 4] = true := by decide +kernel
theorem subd19_3_855 : subd19_3 [0, -1, 5] = true := by decide +kernel
theorem subd19_3_856 : subd19_3 [0, -1, 6] = true := by decide +kernel
theorem subd19_3_857 : subd19_3 [0, -1, 7] = true := by decide +kernel
theorem subd19_3_858 : subd19_3 [0, -1, 8] = true := by decide +kernel
theorem subd19_3_859 : subd19_3 [0, -1, 9] = true := by decide +kernel
theorem subd19_3_860 : subd19_3 [0, 0, -9] = true := by decide +kernel
theorem subd19_3_861 : subd19_3 [0, 0, -8] = true := by decide +kernel
theorem subd19_3_862 : subd19_3 [0, 0, -7] = true := by decide +kernel
theorem subd19_3_863 : subd19_3 [0, 0, -6] = true := by decide +kernel
theorem sbd19_3_26 : ∀ q ∈ blkd19_3_26, subd19_3 q = true := by
  unfold blkd19_3_26
  exact List.forall_mem_cons.2 ⟨subd19_3_832, List.forall_mem_cons.2 ⟨subd19_3_833, List.forall_mem_cons.2 ⟨subd19_3_834, List.forall_mem_cons.2 ⟨subd19_3_835, List.forall_mem_cons.2 ⟨subd19_3_836, List.forall_mem_cons.2 ⟨subd19_3_837, List.forall_mem_cons.2 ⟨subd19_3_838, List.forall_mem_cons.2 ⟨subd19_3_839, List.forall_mem_cons.2 ⟨subd19_3_840, List.forall_mem_cons.2 ⟨subd19_3_841, List.forall_mem_cons.2 ⟨subd19_3_842, List.forall_mem_cons.2 ⟨subd19_3_843, List.forall_mem_cons.2 ⟨subd19_3_844, List.forall_mem_cons.2 ⟨subd19_3_845, List.forall_mem_cons.2 ⟨subd19_3_846, List.forall_mem_cons.2 ⟨subd19_3_847, List.forall_mem_cons.2 ⟨subd19_3_848, List.forall_mem_cons.2 ⟨subd19_3_849, List.forall_mem_cons.2 ⟨subd19_3_850, List.forall_mem_cons.2 ⟨subd19_3_851, List.forall_mem_cons.2 ⟨subd19_3_852, List.forall_mem_cons.2 ⟨subd19_3_853, List.forall_mem_cons.2 ⟨subd19_3_854, List.forall_mem_cons.2 ⟨subd19_3_855, List.forall_mem_cons.2 ⟨subd19_3_856, List.forall_mem_cons.2 ⟨subd19_3_857, List.forall_mem_cons.2 ⟨subd19_3_858, List.forall_mem_cons.2 ⟨subd19_3_859, List.forall_mem_cons.2 ⟨subd19_3_860, List.forall_mem_cons.2 ⟨subd19_3_861, List.forall_mem_cons.2 ⟨subd19_3_862, List.forall_mem_cons.2 ⟨subd19_3_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_864 : subd19_3 [0, 0, -5] = true := by decide +kernel
theorem subd19_3_865 : subd19_3 [0, 0, -4] = true := by decide +kernel
theorem subd19_3_866 : subd19_3 [0, 0, -3] = true := by decide +kernel
theorem subd19_3_867 : subd19_3 [0, 0, -2] = true := by decide +kernel
theorem subd19_3_868 : subd19_3 [0, 0, -1] = true := by decide +kernel
theorem subd19_3_869 : subd19_3 [0, 0, 0] = true := by decide +kernel
theorem subd19_3_870 : subd19_3 [0, 0, 1] = true := by decide +kernel
theorem subd19_3_871 : subd19_3 [0, 0, 2] = true := by decide +kernel
theorem subd19_3_872 : subd19_3 [0, 0, 3] = true := by decide +kernel
theorem subd19_3_873 : subd19_3 [0, 0, 4] = true := by decide +kernel
theorem subd19_3_874 : subd19_3 [0, 0, 5] = true := by decide +kernel
theorem subd19_3_875 : subd19_3 [0, 0, 6] = true := by decide +kernel
theorem subd19_3_876 : subd19_3 [0, 0, 7] = true := by decide +kernel
theorem subd19_3_877 : subd19_3 [0, 0, 8] = true := by decide +kernel
theorem subd19_3_878 : subd19_3 [0, 1, -10] = true := by decide +kernel
theorem subd19_3_879 : subd19_3 [0, 1, -9] = true := by decide +kernel
theorem subd19_3_880 : subd19_3 [0, 1, -8] = true := by decide +kernel
theorem subd19_3_881 : subd19_3 [0, 1, -7] = true := by decide +kernel
theorem subd19_3_882 : subd19_3 [0, 1, -6] = true := by decide +kernel
theorem subd19_3_883 : subd19_3 [0, 1, -5] = true := by decide +kernel
theorem subd19_3_884 : subd19_3 [0, 1, -4] = true := by decide +kernel
theorem subd19_3_885 : subd19_3 [0, 1, -3] = true := by decide +kernel
theorem subd19_3_886 : subd19_3 [0, 1, -2] = true := by decide +kernel
theorem subd19_3_887 : subd19_3 [0, 1, -1] = true := by decide +kernel
theorem subd19_3_888 : subd19_3 [0, 1, 0] = true := by decide +kernel
theorem subd19_3_889 : subd19_3 [0, 1, 1] = true := by decide +kernel
theorem subd19_3_890 : subd19_3 [0, 1, 2] = true := by decide +kernel
theorem subd19_3_891 : subd19_3 [0, 1, 3] = true := by decide +kernel
theorem subd19_3_892 : subd19_3 [0, 1, 4] = true := by decide +kernel
theorem subd19_3_893 : subd19_3 [0, 1, 5] = true := by decide +kernel
theorem subd19_3_894 : subd19_3 [0, 1, 6] = true := by decide +kernel
theorem subd19_3_895 : subd19_3 [0, 1, 7] = true := by decide +kernel
theorem sbd19_3_27 : ∀ q ∈ blkd19_3_27, subd19_3 q = true := by
  unfold blkd19_3_27
  exact List.forall_mem_cons.2 ⟨subd19_3_864, List.forall_mem_cons.2 ⟨subd19_3_865, List.forall_mem_cons.2 ⟨subd19_3_866, List.forall_mem_cons.2 ⟨subd19_3_867, List.forall_mem_cons.2 ⟨subd19_3_868, List.forall_mem_cons.2 ⟨subd19_3_869, List.forall_mem_cons.2 ⟨subd19_3_870, List.forall_mem_cons.2 ⟨subd19_3_871, List.forall_mem_cons.2 ⟨subd19_3_872, List.forall_mem_cons.2 ⟨subd19_3_873, List.forall_mem_cons.2 ⟨subd19_3_874, List.forall_mem_cons.2 ⟨subd19_3_875, List.forall_mem_cons.2 ⟨subd19_3_876, List.forall_mem_cons.2 ⟨subd19_3_877, List.forall_mem_cons.2 ⟨subd19_3_878, List.forall_mem_cons.2 ⟨subd19_3_879, List.forall_mem_cons.2 ⟨subd19_3_880, List.forall_mem_cons.2 ⟨subd19_3_881, List.forall_mem_cons.2 ⟨subd19_3_882, List.forall_mem_cons.2 ⟨subd19_3_883, List.forall_mem_cons.2 ⟨subd19_3_884, List.forall_mem_cons.2 ⟨subd19_3_885, List.forall_mem_cons.2 ⟨subd19_3_886, List.forall_mem_cons.2 ⟨subd19_3_887, List.forall_mem_cons.2 ⟨subd19_3_888, List.forall_mem_cons.2 ⟨subd19_3_889, List.forall_mem_cons.2 ⟨subd19_3_890, List.forall_mem_cons.2 ⟨subd19_3_891, List.forall_mem_cons.2 ⟨subd19_3_892, List.forall_mem_cons.2 ⟨subd19_3_893, List.forall_mem_cons.2 ⟨subd19_3_894, List.forall_mem_cons.2 ⟨subd19_3_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
