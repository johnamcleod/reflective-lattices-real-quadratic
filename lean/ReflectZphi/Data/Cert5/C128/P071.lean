import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_6_384 : subd9_6 [0, -2, -3] = true := by decide +kernel
theorem subd9_6_385 : subd9_6 [0, -2, -2] = true := by decide +kernel
theorem subd9_6_386 : subd9_6 [0, -2, -1] = true := by decide +kernel
theorem subd9_6_387 : subd9_6 [0, -2, 0] = true := by decide +kernel
theorem subd9_6_388 : subd9_6 [0, -2, 1] = true := by decide +kernel
theorem subd9_6_389 : subd9_6 [0, -2, 2] = true := by decide +kernel
theorem subd9_6_390 : subd9_6 [0, -2, 3] = true := by decide +kernel
theorem subd9_6_391 : subd9_6 [0, -2, 4] = true := by decide +kernel
theorem subd9_6_392 : subd9_6 [0, -2, 5] = true := by decide +kernel
theorem subd9_6_393 : subd9_6 [0, -2, 6] = true := by decide +kernel
theorem subd9_6_394 : subd9_6 [0, -2, 7] = true := by decide +kernel
theorem subd9_6_395 : subd9_6 [0, -2, 8] = true := by decide +kernel
theorem subd9_6_396 : subd9_6 [0, -1, -8] = true := by decide +kernel
theorem subd9_6_397 : subd9_6 [0, -1, -7] = true := by decide +kernel
theorem subd9_6_398 : subd9_6 [0, -1, -6] = true := by decide +kernel
theorem subd9_6_399 : subd9_6 [0, -1, -5] = true := by decide +kernel
theorem subd9_6_400 : subd9_6 [0, -1, -4] = true := by decide +kernel
theorem subd9_6_401 : subd9_6 [0, -1, -3] = true := by decide +kernel
theorem subd9_6_402 : subd9_6 [0, -1, -2] = true := by decide +kernel
theorem subd9_6_403 : subd9_6 [0, -1, -1] = true := by decide +kernel
theorem subd9_6_404 : subd9_6 [0, -1, 0] = true := by decide +kernel
theorem subd9_6_405 : subd9_6 [0, -1, 1] = true := by decide +kernel
theorem subd9_6_406 : subd9_6 [0, -1, 2] = true := by decide +kernel
theorem subd9_6_407 : subd9_6 [0, -1, 3] = true := by decide +kernel
theorem subd9_6_408 : subd9_6 [0, -1, 4] = true := by decide +kernel
theorem subd9_6_409 : subd9_6 [0, -1, 5] = true := by decide +kernel
theorem subd9_6_410 : subd9_6 [0, -1, 6] = true := by decide +kernel
theorem subd9_6_411 : subd9_6 [0, -1, 7] = true := by decide +kernel
theorem subd9_6_412 : subd9_6 [0, -1, 8] = true := by decide +kernel
theorem subd9_6_413 : subd9_6 [0, 0, -9] = true := by decide +kernel
theorem subd9_6_414 : subd9_6 [0, 0, -8] = true := by decide +kernel
theorem subd9_6_415 : subd9_6 [0, 0, -7] = true := by decide +kernel
theorem sbd9_6_12 : ∀ q ∈ blkd9_6_12, subd9_6 q = true := by
  unfold blkd9_6_12
  exact List.forall_mem_cons.2 ⟨subd9_6_384, List.forall_mem_cons.2 ⟨subd9_6_385, List.forall_mem_cons.2 ⟨subd9_6_386, List.forall_mem_cons.2 ⟨subd9_6_387, List.forall_mem_cons.2 ⟨subd9_6_388, List.forall_mem_cons.2 ⟨subd9_6_389, List.forall_mem_cons.2 ⟨subd9_6_390, List.forall_mem_cons.2 ⟨subd9_6_391, List.forall_mem_cons.2 ⟨subd9_6_392, List.forall_mem_cons.2 ⟨subd9_6_393, List.forall_mem_cons.2 ⟨subd9_6_394, List.forall_mem_cons.2 ⟨subd9_6_395, List.forall_mem_cons.2 ⟨subd9_6_396, List.forall_mem_cons.2 ⟨subd9_6_397, List.forall_mem_cons.2 ⟨subd9_6_398, List.forall_mem_cons.2 ⟨subd9_6_399, List.forall_mem_cons.2 ⟨subd9_6_400, List.forall_mem_cons.2 ⟨subd9_6_401, List.forall_mem_cons.2 ⟨subd9_6_402, List.forall_mem_cons.2 ⟨subd9_6_403, List.forall_mem_cons.2 ⟨subd9_6_404, List.forall_mem_cons.2 ⟨subd9_6_405, List.forall_mem_cons.2 ⟨subd9_6_406, List.forall_mem_cons.2 ⟨subd9_6_407, List.forall_mem_cons.2 ⟨subd9_6_408, List.forall_mem_cons.2 ⟨subd9_6_409, List.forall_mem_cons.2 ⟨subd9_6_410, List.forall_mem_cons.2 ⟨subd9_6_411, List.forall_mem_cons.2 ⟨subd9_6_412, List.forall_mem_cons.2 ⟨subd9_6_413, List.forall_mem_cons.2 ⟨subd9_6_414, List.forall_mem_cons.2 ⟨subd9_6_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_416 : subd9_6 [0, 0, -6] = true := by decide +kernel
theorem subd9_6_417 : subd9_6 [0, 0, -5] = true := by decide +kernel
theorem subd9_6_418 : subd9_6 [0, 0, -4] = true := by decide +kernel
theorem subd9_6_419 : subd9_6 [0, 0, -3] = true := by decide +kernel
theorem subd9_6_420 : subd9_6 [0, 0, -2] = true := by decide +kernel
theorem subd9_6_421 : subd9_6 [0, 0, -1] = true := by decide +kernel
theorem subd9_6_422 : subd9_6 [0, 0, 0] = true := by decide +kernel
theorem subd9_6_423 : subd9_6 [0, 0, 1] = true := by decide +kernel
theorem subd9_6_424 : subd9_6 [0, 0, 2] = true := by decide +kernel
theorem subd9_6_425 : subd9_6 [0, 0, 3] = true := by decide +kernel
theorem subd9_6_426 : subd9_6 [0, 0, 4] = true := by decide +kernel
theorem subd9_6_427 : subd9_6 [0, 0, 5] = true := by decide +kernel
theorem subd9_6_428 : subd9_6 [0, 0, 6] = true := by decide +kernel
theorem subd9_6_429 : subd9_6 [0, 0, 7] = true := by decide +kernel
theorem subd9_6_430 : subd9_6 [0, 0, 8] = true := by decide +kernel
theorem subd9_6_431 : subd9_6 [0, 1, -9] = true := by decide +kernel
theorem subd9_6_432 : subd9_6 [0, 1, -8] = true := by decide +kernel
theorem subd9_6_433 : subd9_6 [0, 1, -7] = true := by decide +kernel
theorem subd9_6_434 : subd9_6 [0, 1, -6] = true := by decide +kernel
theorem subd9_6_435 : subd9_6 [0, 1, -5] = true := by decide +kernel
theorem subd9_6_436 : subd9_6 [0, 1, -4] = true := by decide +kernel
theorem subd9_6_437 : subd9_6 [0, 1, -3] = true := by decide +kernel
theorem subd9_6_438 : subd9_6 [0, 1, -2] = true := by decide +kernel
theorem subd9_6_439 : subd9_6 [0, 1, -1] = true := by decide +kernel
theorem subd9_6_440 : subd9_6 [0, 1, 0] = true := by decide +kernel
theorem subd9_6_441 : subd9_6 [0, 1, 1] = true := by decide +kernel
theorem subd9_6_442 : subd9_6 [0, 1, 2] = true := by decide +kernel
theorem subd9_6_443 : subd9_6 [0, 1, 3] = true := by decide +kernel
theorem subd9_6_444 : subd9_6 [0, 1, 4] = true := by decide +kernel
theorem subd9_6_445 : subd9_6 [0, 1, 5] = true := by decide +kernel
theorem subd9_6_446 : subd9_6 [0, 1, 6] = true := by decide +kernel
theorem subd9_6_447 : subd9_6 [0, 1, 7] = true := by decide +kernel
theorem sbd9_6_13 : ∀ q ∈ blkd9_6_13, subd9_6 q = true := by
  unfold blkd9_6_13
  exact List.forall_mem_cons.2 ⟨subd9_6_416, List.forall_mem_cons.2 ⟨subd9_6_417, List.forall_mem_cons.2 ⟨subd9_6_418, List.forall_mem_cons.2 ⟨subd9_6_419, List.forall_mem_cons.2 ⟨subd9_6_420, List.forall_mem_cons.2 ⟨subd9_6_421, List.forall_mem_cons.2 ⟨subd9_6_422, List.forall_mem_cons.2 ⟨subd9_6_423, List.forall_mem_cons.2 ⟨subd9_6_424, List.forall_mem_cons.2 ⟨subd9_6_425, List.forall_mem_cons.2 ⟨subd9_6_426, List.forall_mem_cons.2 ⟨subd9_6_427, List.forall_mem_cons.2 ⟨subd9_6_428, List.forall_mem_cons.2 ⟨subd9_6_429, List.forall_mem_cons.2 ⟨subd9_6_430, List.forall_mem_cons.2 ⟨subd9_6_431, List.forall_mem_cons.2 ⟨subd9_6_432, List.forall_mem_cons.2 ⟨subd9_6_433, List.forall_mem_cons.2 ⟨subd9_6_434, List.forall_mem_cons.2 ⟨subd9_6_435, List.forall_mem_cons.2 ⟨subd9_6_436, List.forall_mem_cons.2 ⟨subd9_6_437, List.forall_mem_cons.2 ⟨subd9_6_438, List.forall_mem_cons.2 ⟨subd9_6_439, List.forall_mem_cons.2 ⟨subd9_6_440, List.forall_mem_cons.2 ⟨subd9_6_441, List.forall_mem_cons.2 ⟨subd9_6_442, List.forall_mem_cons.2 ⟨subd9_6_443, List.forall_mem_cons.2 ⟨subd9_6_444, List.forall_mem_cons.2 ⟨subd9_6_445, List.forall_mem_cons.2 ⟨subd9_6_446, List.forall_mem_cons.2 ⟨subd9_6_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_448 : subd9_6 [0, 2, -9] = true := by decide +kernel
theorem subd9_6_449 : subd9_6 [0, 2, -8] = true := by decide +kernel
theorem subd9_6_450 : subd9_6 [0, 2, -7] = true := by decide +kernel
theorem subd9_6_451 : subd9_6 [0, 2, -6] = true := by decide +kernel
theorem subd9_6_452 : subd9_6 [0, 2, -5] = true := by decide +kernel
theorem subd9_6_453 : subd9_6 [0, 2, -4] = true := by decide +kernel
theorem subd9_6_454 : subd9_6 [0, 2, -3] = true := by decide +kernel
theorem subd9_6_455 : subd9_6 [0, 2, -2] = true := by decide +kernel
theorem subd9_6_456 : subd9_6 [0, 2, -1] = true := by decide +kernel
theorem subd9_6_457 : subd9_6 [0, 2, 0] = true := by decide +kernel
theorem subd9_6_458 : subd9_6 [0, 2, 1] = true := by decide +kernel
theorem subd9_6_459 : subd9_6 [0, 2, 2] = true := by decide +kernel
theorem subd9_6_460 : subd9_6 [0, 2, 3] = true := by decide +kernel
theorem subd9_6_461 : subd9_6 [0, 2, 4] = true := by decide +kernel
theorem subd9_6_462 : subd9_6 [0, 2, 5] = true := by decide +kernel
theorem subd9_6_463 : subd9_6 [0, 2, 6] = true := by decide +kernel
theorem subd9_6_464 : subd9_6 [0, 2, 7] = true := by decide +kernel
theorem subd9_6_465 : subd9_6 [0, 3, -8] = true := by decide +kernel
theorem subd9_6_466 : subd9_6 [0, 3, -7] = true := by decide +kernel
theorem subd9_6_467 : subd9_6 [0, 3, -6] = true := by decide +kernel
theorem subd9_6_468 : subd9_6 [0, 3, -5] = true := by decide +kernel
theorem subd9_6_469 : subd9_6 [0, 3, -4] = true := by decide +kernel
theorem subd9_6_470 : subd9_6 [0, 3, -3] = true := by decide +kernel
theorem subd9_6_471 : subd9_6 [0, 3, -2] = true := by decide +kernel
theorem subd9_6_472 : subd9_6 [0, 3, -1] = true := by decide +kernel
theorem subd9_6_473 : subd9_6 [0, 3, 0] = true := by decide +kernel
theorem subd9_6_474 : subd9_6 [0, 3, 1] = true := by decide +kernel
theorem subd9_6_475 : subd9_6 [0, 3, 2] = true := by decide +kernel
theorem subd9_6_476 : subd9_6 [0, 3, 3] = true := by decide +kernel
theorem subd9_6_477 : subd9_6 [0, 3, 4] = true := by decide +kernel
theorem subd9_6_478 : subd9_6 [0, 3, 5] = true := by decide +kernel
theorem subd9_6_479 : subd9_6 [0, 3, 6] = true := by decide +kernel
theorem sbd9_6_14 : ∀ q ∈ blkd9_6_14, subd9_6 q = true := by
  unfold blkd9_6_14
  exact List.forall_mem_cons.2 ⟨subd9_6_448, List.forall_mem_cons.2 ⟨subd9_6_449, List.forall_mem_cons.2 ⟨subd9_6_450, List.forall_mem_cons.2 ⟨subd9_6_451, List.forall_mem_cons.2 ⟨subd9_6_452, List.forall_mem_cons.2 ⟨subd9_6_453, List.forall_mem_cons.2 ⟨subd9_6_454, List.forall_mem_cons.2 ⟨subd9_6_455, List.forall_mem_cons.2 ⟨subd9_6_456, List.forall_mem_cons.2 ⟨subd9_6_457, List.forall_mem_cons.2 ⟨subd9_6_458, List.forall_mem_cons.2 ⟨subd9_6_459, List.forall_mem_cons.2 ⟨subd9_6_460, List.forall_mem_cons.2 ⟨subd9_6_461, List.forall_mem_cons.2 ⟨subd9_6_462, List.forall_mem_cons.2 ⟨subd9_6_463, List.forall_mem_cons.2 ⟨subd9_6_464, List.forall_mem_cons.2 ⟨subd9_6_465, List.forall_mem_cons.2 ⟨subd9_6_466, List.forall_mem_cons.2 ⟨subd9_6_467, List.forall_mem_cons.2 ⟨subd9_6_468, List.forall_mem_cons.2 ⟨subd9_6_469, List.forall_mem_cons.2 ⟨subd9_6_470, List.forall_mem_cons.2 ⟨subd9_6_471, List.forall_mem_cons.2 ⟨subd9_6_472, List.forall_mem_cons.2 ⟨subd9_6_473, List.forall_mem_cons.2 ⟨subd9_6_474, List.forall_mem_cons.2 ⟨subd9_6_475, List.forall_mem_cons.2 ⟨subd9_6_476, List.forall_mem_cons.2 ⟨subd9_6_477, List.forall_mem_cons.2 ⟨subd9_6_478, List.forall_mem_cons.2 ⟨subd9_6_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_480 : subd9_6 [0, 4, -8] = true := by decide +kernel
theorem subd9_6_481 : subd9_6 [0, 4, -7] = true := by decide +kernel
theorem subd9_6_482 : subd9_6 [0, 4, -6] = true := by decide +kernel
theorem subd9_6_483 : subd9_6 [0, 4, -5] = true := by decide +kernel
theorem subd9_6_484 : subd9_6 [0, 4, -4] = true := by decide +kernel
theorem subd9_6_485 : subd9_6 [0, 4, -3] = true := by decide +kernel
theorem subd9_6_486 : subd9_6 [0, 4, -2] = true := by decide +kernel
theorem subd9_6_487 : subd9_6 [0, 4, -1] = true := by decide +kernel
theorem subd9_6_488 : subd9_6 [0, 4, 0] = true := by decide +kernel
theorem subd9_6_489 : subd9_6 [0, 4, 1] = true := by decide +kernel
theorem subd9_6_490 : subd9_6 [0, 4, 2] = true := by decide +kernel
theorem subd9_6_491 : subd9_6 [0, 4, 3] = true := by decide +kernel
theorem subd9_6_492 : subd9_6 [0, 4, 4] = true := by decide +kernel
theorem subd9_6_493 : subd9_6 [0, 4, 5] = true := by decide +kernel
theorem subd9_6_494 : subd9_6 [0, 5] = true := by decide +kernel
theorem subd9_6_495 : subd9_6 [0, 6] = true := by decide +kernel
theorem subd9_6_496 : subd9_6 [1, -7] = true := by decide +kernel
theorem subd9_6_497 : subd9_6 [1, -6] = true := by decide +kernel
theorem subd9_6_498 : subd9_6 [1, -5] = true := by decide +kernel
theorem subd9_6_499 : subd9_6 [1, -4] = true := by decide +kernel
theorem subd9_6_500 : subd9_6 [1, -3, -6] = true := by decide +kernel
theorem subd9_6_501 : subd9_6 [1, -3, -5] = true := by decide +kernel
theorem subd9_6_502 : subd9_6 [1, -3, -4] = true := by decide +kernel
theorem subd9_6_503 : subd9_6 [1, -3, -3] = true := by decide +kernel
theorem subd9_6_504 : subd9_6 [1, -3, -2] = true := by decide +kernel
theorem subd9_6_505 : subd9_6 [1, -3, -1] = true := by decide +kernel
theorem subd9_6_506 : subd9_6 [1, -3, 0] = true := by decide +kernel
theorem subd9_6_507 : subd9_6 [1, -3, 1] = true := by decide +kernel
theorem subd9_6_508 : subd9_6 [1, -3, 2] = true := by decide +kernel
theorem subd9_6_509 : subd9_6 [1, -3, 3] = true := by decide +kernel
theorem subd9_6_510 : subd9_6 [1, -3, 4] = true := by decide +kernel
theorem subd9_6_511 : subd9_6 [1, -3, 5] = true := by decide +kernel
theorem sbd9_6_15 : ∀ q ∈ blkd9_6_15, subd9_6 q = true := by
  unfold blkd9_6_15
  exact List.forall_mem_cons.2 ⟨subd9_6_480, List.forall_mem_cons.2 ⟨subd9_6_481, List.forall_mem_cons.2 ⟨subd9_6_482, List.forall_mem_cons.2 ⟨subd9_6_483, List.forall_mem_cons.2 ⟨subd9_6_484, List.forall_mem_cons.2 ⟨subd9_6_485, List.forall_mem_cons.2 ⟨subd9_6_486, List.forall_mem_cons.2 ⟨subd9_6_487, List.forall_mem_cons.2 ⟨subd9_6_488, List.forall_mem_cons.2 ⟨subd9_6_489, List.forall_mem_cons.2 ⟨subd9_6_490, List.forall_mem_cons.2 ⟨subd9_6_491, List.forall_mem_cons.2 ⟨subd9_6_492, List.forall_mem_cons.2 ⟨subd9_6_493, List.forall_mem_cons.2 ⟨subd9_6_494, List.forall_mem_cons.2 ⟨subd9_6_495, List.forall_mem_cons.2 ⟨subd9_6_496, List.forall_mem_cons.2 ⟨subd9_6_497, List.forall_mem_cons.2 ⟨subd9_6_498, List.forall_mem_cons.2 ⟨subd9_6_499, List.forall_mem_cons.2 ⟨subd9_6_500, List.forall_mem_cons.2 ⟨subd9_6_501, List.forall_mem_cons.2 ⟨subd9_6_502, List.forall_mem_cons.2 ⟨subd9_6_503, List.forall_mem_cons.2 ⟨subd9_6_504, List.forall_mem_cons.2 ⟨subd9_6_505, List.forall_mem_cons.2 ⟨subd9_6_506, List.forall_mem_cons.2 ⟨subd9_6_507, List.forall_mem_cons.2 ⟨subd9_6_508, List.forall_mem_cons.2 ⟨subd9_6_509, List.forall_mem_cons.2 ⟨subd9_6_510, List.forall_mem_cons.2 ⟨subd9_6_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_512 : subd9_6 [1, -3, 6] = true := by decide +kernel
theorem subd9_6_513 : subd9_6 [1, -3, 7] = true := by decide +kernel
theorem subd9_6_514 : subd9_6 [1, -2, -7] = true := by decide +kernel
theorem subd9_6_515 : subd9_6 [1, -2, -6] = true := by decide +kernel
theorem subd9_6_516 : subd9_6 [1, -2, -5] = true := by decide +kernel
theorem subd9_6_517 : subd9_6 [1, -2, -4] = true := by decide +kernel
theorem subd9_6_518 : subd9_6 [1, -2, -3] = true := by decide +kernel
theorem subd9_6_519 : subd9_6 [1, -2, -2] = true := by decide +kernel
theorem subd9_6_520 : subd9_6 [1, -2, -1] = true := by decide +kernel
theorem subd9_6_521 : subd9_6 [1, -2, 0] = true := by decide +kernel
theorem subd9_6_522 : subd9_6 [1, -2, 1] = true := by decide +kernel
theorem subd9_6_523 : subd9_6 [1, -2, 2] = true := by decide +kernel
theorem subd9_6_524 : subd9_6 [1, -2, 3] = true := by decide +kernel
theorem subd9_6_525 : subd9_6 [1, -2, 4] = true := by decide +kernel
theorem subd9_6_526 : subd9_6 [1, -2, 5] = true := by decide +kernel
theorem subd9_6_527 : subd9_6 [1, -2, 6] = true := by decide +kernel
theorem subd9_6_528 : subd9_6 [1, -2, 7] = true := by decide +kernel
theorem subd9_6_529 : subd9_6 [1, -2, 8] = true := by decide +kernel
theorem subd9_6_530 : subd9_6 [1, -1, -8] = true := by decide +kernel
theorem subd9_6_531 : subd9_6 [1, -1, -7] = true := by decide +kernel
theorem subd9_6_532 : subd9_6 [1, -1, -6] = true := by decide +kernel
theorem subd9_6_533 : subd9_6 [1, -1, -5] = true := by decide +kernel
theorem subd9_6_534 : subd9_6 [1, -1, -4] = true := by decide +kernel
theorem subd9_6_535 : subd9_6 [1, -1, -3] = true := by decide +kernel
theorem subd9_6_536 : subd9_6 [1, -1, -2] = true := by decide +kernel
theorem subd9_6_537 : subd9_6 [1, -1, -1] = true := by decide +kernel
theorem subd9_6_538 : subd9_6 [1, -1, 0] = true := by decide +kernel
theorem subd9_6_539 : subd9_6 [1, -1, 1] = true := by decide +kernel
theorem subd9_6_540 : subd9_6 [1, -1, 2] = true := by decide +kernel
theorem subd9_6_541 : subd9_6 [1, -1, 3] = true := by decide +kernel
theorem subd9_6_542 : subd9_6 [1, -1, 4] = true := by decide +kernel
theorem subd9_6_543 : subd9_6 [1, -1, 5] = true := by decide +kernel
theorem sbd9_6_16 : ∀ q ∈ blkd9_6_16, subd9_6 q = true := by
  unfold blkd9_6_16
  exact List.forall_mem_cons.2 ⟨subd9_6_512, List.forall_mem_cons.2 ⟨subd9_6_513, List.forall_mem_cons.2 ⟨subd9_6_514, List.forall_mem_cons.2 ⟨subd9_6_515, List.forall_mem_cons.2 ⟨subd9_6_516, List.forall_mem_cons.2 ⟨subd9_6_517, List.forall_mem_cons.2 ⟨subd9_6_518, List.forall_mem_cons.2 ⟨subd9_6_519, List.forall_mem_cons.2 ⟨subd9_6_520, List.forall_mem_cons.2 ⟨subd9_6_521, List.forall_mem_cons.2 ⟨subd9_6_522, List.forall_mem_cons.2 ⟨subd9_6_523, List.forall_mem_cons.2 ⟨subd9_6_524, List.forall_mem_cons.2 ⟨subd9_6_525, List.forall_mem_cons.2 ⟨subd9_6_526, List.forall_mem_cons.2 ⟨subd9_6_527, List.forall_mem_cons.2 ⟨subd9_6_528, List.forall_mem_cons.2 ⟨subd9_6_529, List.forall_mem_cons.2 ⟨subd9_6_530, List.forall_mem_cons.2 ⟨subd9_6_531, List.forall_mem_cons.2 ⟨subd9_6_532, List.forall_mem_cons.2 ⟨subd9_6_533, List.forall_mem_cons.2 ⟨subd9_6_534, List.forall_mem_cons.2 ⟨subd9_6_535, List.forall_mem_cons.2 ⟨subd9_6_536, List.forall_mem_cons.2 ⟨subd9_6_537, List.forall_mem_cons.2 ⟨subd9_6_538, List.forall_mem_cons.2 ⟨subd9_6_539, List.forall_mem_cons.2 ⟨subd9_6_540, List.forall_mem_cons.2 ⟨subd9_6_541, List.forall_mem_cons.2 ⟨subd9_6_542, List.forall_mem_cons.2 ⟨subd9_6_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_544 : subd9_6 [1, -1, 6] = true := by decide +kernel
theorem subd9_6_545 : subd9_6 [1, -1, 7] = true := by decide +kernel
theorem subd9_6_546 : subd9_6 [1, -1, 8] = true := by decide +kernel
theorem subd9_6_547 : subd9_6 [1, 0, -8] = true := by decide +kernel
theorem subd9_6_548 : subd9_6 [1, 0, -7] = true := by decide +kernel
theorem subd9_6_549 : subd9_6 [1, 0, -6] = true := by decide +kernel
theorem subd9_6_550 : subd9_6 [1, 0, -5] = true := by decide +kernel
theorem subd9_6_551 : subd9_6 [1, 0, -4] = true := by decide +kernel
theorem subd9_6_552 : subd9_6 [1, 0, -3] = true := by decide +kernel
theorem subd9_6_553 : subd9_6 [1, 0, -2] = true := by decide +kernel
theorem subd9_6_554 : subd9_6 [1, 0, -1] = true := by decide +kernel
theorem subd9_6_555 : subd9_6 [1, 0, 0] = true := by decide +kernel
theorem subd9_6_556 : subd9_6 [1, 0, 1] = true := by decide +kernel
theorem subd9_6_557 : subd9_6 [1, 0, 2] = true := by decide +kernel
theorem subd9_6_558 : subd9_6 [1, 0, 3] = true := by decide +kernel
theorem subd9_6_559 : subd9_6 [1, 0, 4] = true := by decide +kernel
theorem subd9_6_560 : subd9_6 [1, 0, 5] = true := by decide +kernel
theorem subd9_6_561 : subd9_6 [1, 0, 6] = true := by decide +kernel
theorem subd9_6_562 : subd9_6 [1, 0, 7] = true := by decide +kernel
theorem subd9_6_563 : subd9_6 [1, 0, 8] = true := by decide +kernel
theorem subd9_6_564 : subd9_6 [1, 1, -8] = true := by decide +kernel
theorem subd9_6_565 : subd9_6 [1, 1, -7] = true := by decide +kernel
theorem subd9_6_566 : subd9_6 [1, 1, -6] = true := by decide +kernel
theorem subd9_6_567 : subd9_6 [1, 1, -5] = true := by decide +kernel
theorem subd9_6_568 : subd9_6 [1, 1, -4] = true := by decide +kernel
theorem subd9_6_569 : subd9_6 [1, 1, -3] = true := by decide +kernel
theorem subd9_6_570 : subd9_6 [1, 1, -2] = true := by decide +kernel
theorem subd9_6_571 : subd9_6 [1, 1, -1] = true := by decide +kernel
theorem subd9_6_572 : subd9_6 [1, 1, 0] = true := by decide +kernel
theorem subd9_6_573 : subd9_6 [1, 1, 1] = true := by decide +kernel
theorem subd9_6_574 : subd9_6 [1, 1, 2] = true := by decide +kernel
theorem subd9_6_575 : subd9_6 [1, 1, 3] = true := by decide +kernel
theorem sbd9_6_17 : ∀ q ∈ blkd9_6_17, subd9_6 q = true := by
  unfold blkd9_6_17
  exact List.forall_mem_cons.2 ⟨subd9_6_544, List.forall_mem_cons.2 ⟨subd9_6_545, List.forall_mem_cons.2 ⟨subd9_6_546, List.forall_mem_cons.2 ⟨subd9_6_547, List.forall_mem_cons.2 ⟨subd9_6_548, List.forall_mem_cons.2 ⟨subd9_6_549, List.forall_mem_cons.2 ⟨subd9_6_550, List.forall_mem_cons.2 ⟨subd9_6_551, List.forall_mem_cons.2 ⟨subd9_6_552, List.forall_mem_cons.2 ⟨subd9_6_553, List.forall_mem_cons.2 ⟨subd9_6_554, List.forall_mem_cons.2 ⟨subd9_6_555, List.forall_mem_cons.2 ⟨subd9_6_556, List.forall_mem_cons.2 ⟨subd9_6_557, List.forall_mem_cons.2 ⟨subd9_6_558, List.forall_mem_cons.2 ⟨subd9_6_559, List.forall_mem_cons.2 ⟨subd9_6_560, List.forall_mem_cons.2 ⟨subd9_6_561, List.forall_mem_cons.2 ⟨subd9_6_562, List.forall_mem_cons.2 ⟨subd9_6_563, List.forall_mem_cons.2 ⟨subd9_6_564, List.forall_mem_cons.2 ⟨subd9_6_565, List.forall_mem_cons.2 ⟨subd9_6_566, List.forall_mem_cons.2 ⟨subd9_6_567, List.forall_mem_cons.2 ⟨subd9_6_568, List.forall_mem_cons.2 ⟨subd9_6_569, List.forall_mem_cons.2 ⟨subd9_6_570, List.forall_mem_cons.2 ⟨subd9_6_571, List.forall_mem_cons.2 ⟨subd9_6_572, List.forall_mem_cons.2 ⟨subd9_6_573, List.forall_mem_cons.2 ⟨subd9_6_574, List.forall_mem_cons.2 ⟨subd9_6_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_576 : subd9_6 [1, 1, 4] = true := by decide +kernel
theorem subd9_6_577 : subd9_6 [1, 1, 5] = true := by decide +kernel
theorem subd9_6_578 : subd9_6 [1, 1, 6] = true := by decide +kernel
theorem subd9_6_579 : subd9_6 [1, 1, 7] = true := by decide +kernel
theorem subd9_6_580 : subd9_6 [1, 1, 8] = true := by decide +kernel
theorem subd9_6_581 : subd9_6 [1, 2, -8] = true := by decide +kernel
theorem subd9_6_582 : subd9_6 [1, 2, -7] = true := by decide +kernel
theorem subd9_6_583 : subd9_6 [1, 2, -6] = true := by decide +kernel
theorem subd9_6_584 : subd9_6 [1, 2, -5] = true := by decide +kernel
theorem subd9_6_585 : subd9_6 [1, 2, -4] = true := by decide +kernel
theorem subd9_6_586 : subd9_6 [1, 2, -3] = true := by decide +kernel
theorem subd9_6_587 : subd9_6 [1, 2, -2] = true := by decide +kernel
theorem subd9_6_588 : subd9_6 [1, 2, -1] = true := by decide +kernel
theorem subd9_6_589 : subd9_6 [1, 2, 0] = true := by decide +kernel
theorem subd9_6_590 : subd9_6 [1, 2, 1] = true := by decide +kernel
theorem subd9_6_591 : subd9_6 [1, 2, 2] = true := by decide +kernel
theorem subd9_6_592 : subd9_6 [1, 2, 3] = true := by decide +kernel
theorem subd9_6_593 : subd9_6 [1, 2, 4] = true := by decide +kernel
theorem subd9_6_594 : subd9_6 [1, 2, 5] = true := by decide +kernel
theorem subd9_6_595 : subd9_6 [1, 2, 6] = true := by decide +kernel
theorem subd9_6_596 : subd9_6 [1, 2, 7] = true := by decide +kernel
theorem subd9_6_597 : subd9_6 [1, 3, -8] = true := by decide +kernel
theorem subd9_6_598 : subd9_6 [1, 3, -7] = true := by decide +kernel
theorem subd9_6_599 : subd9_6 [1, 3, -6] = true := by decide +kernel
theorem subd9_6_600 : subd9_6 [1, 3, -5] = true := by decide +kernel
theorem subd9_6_601 : subd9_6 [1, 3, -4] = true := by decide +kernel
theorem subd9_6_602 : subd9_6 [1, 3, -3] = true := by decide +kernel
theorem subd9_6_603 : subd9_6 [1, 3, -2] = true := by decide +kernel
theorem subd9_6_604 : subd9_6 [1, 3, -1] = true := by decide +kernel
theorem subd9_6_605 : subd9_6 [1, 3, 0] = true := by decide +kernel
theorem subd9_6_606 : subd9_6 [1, 3, 1] = true := by decide +kernel
theorem subd9_6_607 : subd9_6 [1, 3, 2] = true := by decide +kernel
theorem sbd9_6_18 : ∀ q ∈ blkd9_6_18, subd9_6 q = true := by
  unfold blkd9_6_18
  exact List.forall_mem_cons.2 ⟨subd9_6_576, List.forall_mem_cons.2 ⟨subd9_6_577, List.forall_mem_cons.2 ⟨subd9_6_578, List.forall_mem_cons.2 ⟨subd9_6_579, List.forall_mem_cons.2 ⟨subd9_6_580, List.forall_mem_cons.2 ⟨subd9_6_581, List.forall_mem_cons.2 ⟨subd9_6_582, List.forall_mem_cons.2 ⟨subd9_6_583, List.forall_mem_cons.2 ⟨subd9_6_584, List.forall_mem_cons.2 ⟨subd9_6_585, List.forall_mem_cons.2 ⟨subd9_6_586, List.forall_mem_cons.2 ⟨subd9_6_587, List.forall_mem_cons.2 ⟨subd9_6_588, List.forall_mem_cons.2 ⟨subd9_6_589, List.forall_mem_cons.2 ⟨subd9_6_590, List.forall_mem_cons.2 ⟨subd9_6_591, List.forall_mem_cons.2 ⟨subd9_6_592, List.forall_mem_cons.2 ⟨subd9_6_593, List.forall_mem_cons.2 ⟨subd9_6_594, List.forall_mem_cons.2 ⟨subd9_6_595, List.forall_mem_cons.2 ⟨subd9_6_596, List.forall_mem_cons.2 ⟨subd9_6_597, List.forall_mem_cons.2 ⟨subd9_6_598, List.forall_mem_cons.2 ⟨subd9_6_599, List.forall_mem_cons.2 ⟨subd9_6_600, List.forall_mem_cons.2 ⟨subd9_6_601, List.forall_mem_cons.2 ⟨subd9_6_602, List.forall_mem_cons.2 ⟨subd9_6_603, List.forall_mem_cons.2 ⟨subd9_6_604, List.forall_mem_cons.2 ⟨subd9_6_605, List.forall_mem_cons.2 ⟨subd9_6_606, List.forall_mem_cons.2 ⟨subd9_6_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_608 : subd9_6 [1, 3, 3] = true := by decide +kernel
theorem subd9_6_609 : subd9_6 [1, 3, 4] = true := by decide +kernel
theorem subd9_6_610 : subd9_6 [1, 3, 5] = true := by decide +kernel
theorem subd9_6_611 : subd9_6 [1, 3, 6] = true := by decide +kernel
theorem subd9_6_612 : subd9_6 [1, 4, -8] = true := by decide +kernel
theorem subd9_6_613 : subd9_6 [1, 4, -7] = true := by decide +kernel
theorem subd9_6_614 : subd9_6 [1, 4, -6] = true := by decide +kernel
theorem subd9_6_615 : subd9_6 [1, 4, -5] = true := by decide +kernel
theorem subd9_6_616 : subd9_6 [1, 4, -4] = true := by decide +kernel
theorem subd9_6_617 : subd9_6 [1, 4, -3] = true := by decide +kernel
theorem subd9_6_618 : subd9_6 [1, 4, -2] = true := by decide +kernel
theorem subd9_6_619 : subd9_6 [1, 4, -1] = true := by decide +kernel
theorem subd9_6_620 : subd9_6 [1, 4, 0] = true := by decide +kernel
theorem subd9_6_621 : subd9_6 [1, 4, 1] = true := by decide +kernel
theorem subd9_6_622 : subd9_6 [1, 4, 2] = true := by decide +kernel
theorem subd9_6_623 : subd9_6 [1, 4, 3] = true := by decide +kernel
theorem subd9_6_624 : subd9_6 [1, 4, 4] = true := by decide +kernel
theorem subd9_6_625 : subd9_6 [1, 4, 5] = true := by decide +kernel
theorem subd9_6_626 : subd9_6 [1, 5] = true := by decide +kernel
theorem subd9_6_627 : subd9_6 [1, 6] = true := by decide +kernel
theorem subd9_6_628 : subd9_6 [2, -6] = true := by decide +kernel
theorem subd9_6_629 : subd9_6 [2, -5] = true := by decide +kernel
theorem subd9_6_630 : subd9_6 [2, -4] = true := by decide +kernel
theorem subd9_6_631 : subd9_6 [2, -3, -6] = true := by decide +kernel
theorem subd9_6_632 : subd9_6 [2, -3, -5] = true := by decide +kernel
theorem subd9_6_633 : subd9_6 [2, -3, -4] = true := by decide +kernel
theorem subd9_6_634 : subd9_6 [2, -3, -3] = true := by decide +kernel
theorem subd9_6_635 : subd9_6 [2, -3, -2] = true := by decide +kernel
theorem subd9_6_636 : subd9_6 [2, -3, -1] = true := by decide +kernel
theorem subd9_6_637 : subd9_6 [2, -3, 0] = true := by decide +kernel
theorem subd9_6_638 : subd9_6 [2, -3, 1] = true := by decide +kernel
theorem subd9_6_639 : subd9_6 [2, -3, 2] = true := by decide +kernel
theorem sbd9_6_19 : ∀ q ∈ blkd9_6_19, subd9_6 q = true := by
  unfold blkd9_6_19
  exact List.forall_mem_cons.2 ⟨subd9_6_608, List.forall_mem_cons.2 ⟨subd9_6_609, List.forall_mem_cons.2 ⟨subd9_6_610, List.forall_mem_cons.2 ⟨subd9_6_611, List.forall_mem_cons.2 ⟨subd9_6_612, List.forall_mem_cons.2 ⟨subd9_6_613, List.forall_mem_cons.2 ⟨subd9_6_614, List.forall_mem_cons.2 ⟨subd9_6_615, List.forall_mem_cons.2 ⟨subd9_6_616, List.forall_mem_cons.2 ⟨subd9_6_617, List.forall_mem_cons.2 ⟨subd9_6_618, List.forall_mem_cons.2 ⟨subd9_6_619, List.forall_mem_cons.2 ⟨subd9_6_620, List.forall_mem_cons.2 ⟨subd9_6_621, List.forall_mem_cons.2 ⟨subd9_6_622, List.forall_mem_cons.2 ⟨subd9_6_623, List.forall_mem_cons.2 ⟨subd9_6_624, List.forall_mem_cons.2 ⟨subd9_6_625, List.forall_mem_cons.2 ⟨subd9_6_626, List.forall_mem_cons.2 ⟨subd9_6_627, List.forall_mem_cons.2 ⟨subd9_6_628, List.forall_mem_cons.2 ⟨subd9_6_629, List.forall_mem_cons.2 ⟨subd9_6_630, List.forall_mem_cons.2 ⟨subd9_6_631, List.forall_mem_cons.2 ⟨subd9_6_632, List.forall_mem_cons.2 ⟨subd9_6_633, List.forall_mem_cons.2 ⟨subd9_6_634, List.forall_mem_cons.2 ⟨subd9_6_635, List.forall_mem_cons.2 ⟨subd9_6_636, List.forall_mem_cons.2 ⟨subd9_6_637, List.forall_mem_cons.2 ⟨subd9_6_638, List.forall_mem_cons.2 ⟨subd9_6_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_640 : subd9_6 [2, -3, 3] = true := by decide +kernel
theorem subd9_6_641 : subd9_6 [2, -3, 4] = true := by decide +kernel
theorem subd9_6_642 : subd9_6 [2, -3, 5] = true := by decide +kernel
theorem subd9_6_643 : subd9_6 [2, -3, 6] = true := by decide +kernel
theorem subd9_6_644 : subd9_6 [2, -3, 7] = true := by decide +kernel
theorem subd9_6_645 : subd9_6 [2, -2, -7] = true := by decide +kernel
theorem subd9_6_646 : subd9_6 [2, -2, -6] = true := by decide +kernel
theorem subd9_6_647 : subd9_6 [2, -2, -5] = true := by decide +kernel
theorem subd9_6_648 : subd9_6 [2, -2, -4] = true := by decide +kernel
theorem subd9_6_649 : subd9_6 [2, -2, -3] = true := by decide +kernel
theorem subd9_6_650 : subd9_6 [2, -2, -2] = true := by decide +kernel
theorem subd9_6_651 : subd9_6 [2, -2, -1] = true := by decide +kernel
theorem subd9_6_652 : subd9_6 [2, -2, 0] = true := by decide +kernel
theorem subd9_6_653 : subd9_6 [2, -2, 1] = true := by decide +kernel
theorem subd9_6_654 : subd9_6 [2, -2, 2] = true := by decide +kernel
theorem subd9_6_655 : subd9_6 [2, -2, 3] = true := by decide +kernel
theorem subd9_6_656 : subd9_6 [2, -2, 4] = true := by decide +kernel
theorem subd9_6_657 : subd9_6 [2, -2, 5] = true := by decide +kernel
theorem subd9_6_658 : subd9_6 [2, -2, 6] = true := by decide +kernel
theorem subd9_6_659 : subd9_6 [2, -2, 7] = true := by decide +kernel
theorem subd9_6_660 : subd9_6 [2, -2, 8] = true := by decide +kernel
theorem subd9_6_661 : subd9_6 [2, -1, -7] = true := by decide +kernel
theorem subd9_6_662 : subd9_6 [2, -1, -6] = true := by decide +kernel
theorem subd9_6_663 : subd9_6 [2, -1, -5] = true := by decide +kernel
theorem subd9_6_664 : subd9_6 [2, -1, -4] = true := by decide +kernel
theorem subd9_6_665 : subd9_6 [2, -1, -3] = true := by decide +kernel
theorem subd9_6_666 : subd9_6 [2, -1, -2] = true := by decide +kernel
theorem subd9_6_667 : subd9_6 [2, -1, -1] = true := by decide +kernel
theorem subd9_6_668 : subd9_6 [2, -1, 0] = true := by decide +kernel
theorem subd9_6_669 : subd9_6 [2, -1, 1] = true := by decide +kernel
theorem subd9_6_670 : subd9_6 [2, -1, 2] = true := by decide +kernel
theorem subd9_6_671 : subd9_6 [2, -1, 3] = true := by decide +kernel
theorem sbd9_6_20 : ∀ q ∈ blkd9_6_20, subd9_6 q = true := by
  unfold blkd9_6_20
  exact List.forall_mem_cons.2 ⟨subd9_6_640, List.forall_mem_cons.2 ⟨subd9_6_641, List.forall_mem_cons.2 ⟨subd9_6_642, List.forall_mem_cons.2 ⟨subd9_6_643, List.forall_mem_cons.2 ⟨subd9_6_644, List.forall_mem_cons.2 ⟨subd9_6_645, List.forall_mem_cons.2 ⟨subd9_6_646, List.forall_mem_cons.2 ⟨subd9_6_647, List.forall_mem_cons.2 ⟨subd9_6_648, List.forall_mem_cons.2 ⟨subd9_6_649, List.forall_mem_cons.2 ⟨subd9_6_650, List.forall_mem_cons.2 ⟨subd9_6_651, List.forall_mem_cons.2 ⟨subd9_6_652, List.forall_mem_cons.2 ⟨subd9_6_653, List.forall_mem_cons.2 ⟨subd9_6_654, List.forall_mem_cons.2 ⟨subd9_6_655, List.forall_mem_cons.2 ⟨subd9_6_656, List.forall_mem_cons.2 ⟨subd9_6_657, List.forall_mem_cons.2 ⟨subd9_6_658, List.forall_mem_cons.2 ⟨subd9_6_659, List.forall_mem_cons.2 ⟨subd9_6_660, List.forall_mem_cons.2 ⟨subd9_6_661, List.forall_mem_cons.2 ⟨subd9_6_662, List.forall_mem_cons.2 ⟨subd9_6_663, List.forall_mem_cons.2 ⟨subd9_6_664, List.forall_mem_cons.2 ⟨subd9_6_665, List.forall_mem_cons.2 ⟨subd9_6_666, List.forall_mem_cons.2 ⟨subd9_6_667, List.forall_mem_cons.2 ⟨subd9_6_668, List.forall_mem_cons.2 ⟨subd9_6_669, List.forall_mem_cons.2 ⟨subd9_6_670, List.forall_mem_cons.2 ⟨subd9_6_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_672 : subd9_6 [2, -1, 4] = true := by decide +kernel
theorem subd9_6_673 : subd9_6 [2, -1, 5] = true := by decide +kernel
theorem subd9_6_674 : subd9_6 [2, -1, 6] = true := by decide +kernel
theorem subd9_6_675 : subd9_6 [2, -1, 7] = true := by decide +kernel
theorem subd9_6_676 : subd9_6 [2, -1, 8] = true := by decide +kernel
theorem subd9_6_677 : subd9_6 [2, 0, -8] = true := by decide +kernel
theorem subd9_6_678 : subd9_6 [2, 0, -7] = true := by decide +kernel
theorem subd9_6_679 : subd9_6 [2, 0, -6] = true := by decide +kernel
theorem subd9_6_680 : subd9_6 [2, 0, -5] = true := by decide +kernel
theorem subd9_6_681 : subd9_6 [2, 0, -4] = true := by decide +kernel
theorem subd9_6_682 : subd9_6 [2, 0, -3] = true := by decide +kernel
theorem subd9_6_683 : subd9_6 [2, 0, -2] = true := by decide +kernel
theorem subd9_6_684 : subd9_6 [2, 0, -1] = true := by decide +kernel
theorem subd9_6_685 : subd9_6 [2, 0, 0] = true := by decide +kernel
theorem subd9_6_686 : subd9_6 [2, 0, 1] = true := by decide +kernel
theorem subd9_6_687 : subd9_6 [2, 0, 2] = true := by decide +kernel
theorem subd9_6_688 : subd9_6 [2, 0, 3] = true := by decide +kernel
theorem subd9_6_689 : subd9_6 [2, 0, 4] = true := by decide +kernel
theorem subd9_6_690 : subd9_6 [2, 0, 5] = true := by decide +kernel
theorem subd9_6_691 : subd9_6 [2, 0, 6] = true := by decide +kernel
theorem subd9_6_692 : subd9_6 [2, 0, 7] = true := by decide +kernel
theorem subd9_6_693 : subd9_6 [2, 0, 8] = true := by decide +kernel
theorem subd9_6_694 : subd9_6 [2, 1, -8] = true := by decide +kernel
theorem subd9_6_695 : subd9_6 [2, 1, -7] = true := by decide +kernel
theorem subd9_6_696 : subd9_6 [2, 1, -6] = true := by decide +kernel
theorem subd9_6_697 : subd9_6 [2, 1, -5] = true := by decide +kernel
theorem subd9_6_698 : subd9_6 [2, 1, -4] = true := by decide +kernel
theorem subd9_6_699 : subd9_6 [2, 1, -3] = true := by decide +kernel
theorem subd9_6_700 : subd9_6 [2, 1, -2] = true := by decide +kernel
theorem subd9_6_701 : subd9_6 [2, 1, -1] = true := by decide +kernel
theorem subd9_6_702 : subd9_6 [2, 1, 0] = true := by decide +kernel
theorem subd9_6_703 : subd9_6 [2, 1, 1] = true := by decide +kernel
theorem sbd9_6_21 : ∀ q ∈ blkd9_6_21, subd9_6 q = true := by
  unfold blkd9_6_21
  exact List.forall_mem_cons.2 ⟨subd9_6_672, List.forall_mem_cons.2 ⟨subd9_6_673, List.forall_mem_cons.2 ⟨subd9_6_674, List.forall_mem_cons.2 ⟨subd9_6_675, List.forall_mem_cons.2 ⟨subd9_6_676, List.forall_mem_cons.2 ⟨subd9_6_677, List.forall_mem_cons.2 ⟨subd9_6_678, List.forall_mem_cons.2 ⟨subd9_6_679, List.forall_mem_cons.2 ⟨subd9_6_680, List.forall_mem_cons.2 ⟨subd9_6_681, List.forall_mem_cons.2 ⟨subd9_6_682, List.forall_mem_cons.2 ⟨subd9_6_683, List.forall_mem_cons.2 ⟨subd9_6_684, List.forall_mem_cons.2 ⟨subd9_6_685, List.forall_mem_cons.2 ⟨subd9_6_686, List.forall_mem_cons.2 ⟨subd9_6_687, List.forall_mem_cons.2 ⟨subd9_6_688, List.forall_mem_cons.2 ⟨subd9_6_689, List.forall_mem_cons.2 ⟨subd9_6_690, List.forall_mem_cons.2 ⟨subd9_6_691, List.forall_mem_cons.2 ⟨subd9_6_692, List.forall_mem_cons.2 ⟨subd9_6_693, List.forall_mem_cons.2 ⟨subd9_6_694, List.forall_mem_cons.2 ⟨subd9_6_695, List.forall_mem_cons.2 ⟨subd9_6_696, List.forall_mem_cons.2 ⟨subd9_6_697, List.forall_mem_cons.2 ⟨subd9_6_698, List.forall_mem_cons.2 ⟨subd9_6_699, List.forall_mem_cons.2 ⟨subd9_6_700, List.forall_mem_cons.2 ⟨subd9_6_701, List.forall_mem_cons.2 ⟨subd9_6_702, List.forall_mem_cons.2 ⟨subd9_6_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_704 : subd9_6 [2, 1, 2] = true := by decide +kernel
theorem subd9_6_705 : subd9_6 [2, 1, 3] = true := by decide +kernel
theorem subd9_6_706 : subd9_6 [2, 1, 4] = true := by decide +kernel
theorem subd9_6_707 : subd9_6 [2, 1, 5] = true := by decide +kernel
theorem subd9_6_708 : subd9_6 [2, 1, 6] = true := by decide +kernel
theorem subd9_6_709 : subd9_6 [2, 1, 7] = true := by decide +kernel
theorem subd9_6_710 : subd9_6 [2, 2, -8] = true := by decide +kernel
theorem subd9_6_711 : subd9_6 [2, 2, -7] = true := by decide +kernel
theorem subd9_6_712 : subd9_6 [2, 2, -6] = true := by decide +kernel
theorem subd9_6_713 : subd9_6 [2, 2, -5] = true := by decide +kernel
theorem subd9_6_714 : subd9_6 [2, 2, -4] = true := by decide +kernel
theorem subd9_6_715 : subd9_6 [2, 2, -3] = true := by decide +kernel
theorem subd9_6_716 : subd9_6 [2, 2, -2] = true := by decide +kernel
theorem subd9_6_717 : subd9_6 [2, 2, -1] = true := by decide +kernel
theorem subd9_6_718 : subd9_6 [2, 2, 0] = true := by decide +kernel
theorem subd9_6_719 : subd9_6 [2, 2, 1] = true := by decide +kernel
theorem subd9_6_720 : subd9_6 [2, 2, 2] = true := by decide +kernel
theorem subd9_6_721 : subd9_6 [2, 2, 3] = true := by decide +kernel
theorem subd9_6_722 : subd9_6 [2, 2, 4] = true := by decide +kernel
theorem subd9_6_723 : subd9_6 [2, 2, 5] = true := by decide +kernel
theorem subd9_6_724 : subd9_6 [2, 2, 6] = true := by decide +kernel
theorem subd9_6_725 : subd9_6 [2, 2, 7] = true := by decide +kernel
theorem subd9_6_726 : subd9_6 [2, 3, -8] = true := by decide +kernel
theorem subd9_6_727 : subd9_6 [2, 3, -7] = true := by decide +kernel
theorem subd9_6_728 : subd9_6 [2, 3, -6] = true := by decide +kernel
theorem subd9_6_729 : subd9_6 [2, 3, -5] = true := by decide +kernel
theorem subd9_6_730 : subd9_6 [2, 3, -4] = true := by decide +kernel
theorem subd9_6_731 : subd9_6 [2, 3, -3] = true := by decide +kernel
theorem subd9_6_732 : subd9_6 [2, 3, -2] = true := by decide +kernel
theorem subd9_6_733 : subd9_6 [2, 3, -1] = true := by decide +kernel
theorem subd9_6_734 : subd9_6 [2, 3, 0] = true := by decide +kernel
theorem subd9_6_735 : subd9_6 [2, 3, 1] = true := by decide +kernel
theorem sbd9_6_22 : ∀ q ∈ blkd9_6_22, subd9_6 q = true := by
  unfold blkd9_6_22
  exact List.forall_mem_cons.2 ⟨subd9_6_704, List.forall_mem_cons.2 ⟨subd9_6_705, List.forall_mem_cons.2 ⟨subd9_6_706, List.forall_mem_cons.2 ⟨subd9_6_707, List.forall_mem_cons.2 ⟨subd9_6_708, List.forall_mem_cons.2 ⟨subd9_6_709, List.forall_mem_cons.2 ⟨subd9_6_710, List.forall_mem_cons.2 ⟨subd9_6_711, List.forall_mem_cons.2 ⟨subd9_6_712, List.forall_mem_cons.2 ⟨subd9_6_713, List.forall_mem_cons.2 ⟨subd9_6_714, List.forall_mem_cons.2 ⟨subd9_6_715, List.forall_mem_cons.2 ⟨subd9_6_716, List.forall_mem_cons.2 ⟨subd9_6_717, List.forall_mem_cons.2 ⟨subd9_6_718, List.forall_mem_cons.2 ⟨subd9_6_719, List.forall_mem_cons.2 ⟨subd9_6_720, List.forall_mem_cons.2 ⟨subd9_6_721, List.forall_mem_cons.2 ⟨subd9_6_722, List.forall_mem_cons.2 ⟨subd9_6_723, List.forall_mem_cons.2 ⟨subd9_6_724, List.forall_mem_cons.2 ⟨subd9_6_725, List.forall_mem_cons.2 ⟨subd9_6_726, List.forall_mem_cons.2 ⟨subd9_6_727, List.forall_mem_cons.2 ⟨subd9_6_728, List.forall_mem_cons.2 ⟨subd9_6_729, List.forall_mem_cons.2 ⟨subd9_6_730, List.forall_mem_cons.2 ⟨subd9_6_731, List.forall_mem_cons.2 ⟨subd9_6_732, List.forall_mem_cons.2 ⟨subd9_6_733, List.forall_mem_cons.2 ⟨subd9_6_734, List.forall_mem_cons.2 ⟨subd9_6_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_736 : subd9_6 [2, 3, 2] = true := by decide +kernel
theorem subd9_6_737 : subd9_6 [2, 3, 3] = true := by decide +kernel
theorem subd9_6_738 : subd9_6 [2, 3, 4] = true := by decide +kernel
theorem subd9_6_739 : subd9_6 [2, 3, 5] = true := by decide +kernel
theorem subd9_6_740 : subd9_6 [2, 3, 6] = true := by decide +kernel
theorem subd9_6_741 : subd9_6 [2, 4] = true := by decide +kernel
theorem subd9_6_742 : subd9_6 [2, 5] = true := by decide +kernel
theorem subd9_6_743 : subd9_6 [2, 6] = true := by decide +kernel
theorem subd9_6_744 : subd9_6 [3, -5] = true := by decide +kernel
theorem subd9_6_745 : subd9_6 [3, -4] = true := by decide +kernel
theorem subd9_6_746 : subd9_6 [3, -3] = true := by decide +kernel
theorem subd9_6_747 : subd9_6 [3, -2] = true := by decide +kernel
theorem subd9_6_748 : subd9_6 [3, -1, -6] = true := by decide +kernel
theorem subd9_6_749 : subd9_6 [3, -1, -5] = true := by decide +kernel
theorem subd9_6_750 : subd9_6 [3, -1, -4] = true := by decide +kernel
theorem subd9_6_751 : subd9_6 [3, -1, -3] = true := by decide +kernel
theorem subd9_6_752 : subd9_6 [3, -1, -2] = true := by decide +kernel
theorem subd9_6_753 : subd9_6 [3, -1, -1] = true := by decide +kernel
theorem subd9_6_754 : subd9_6 [3, -1, 0] = true := by decide +kernel
theorem subd9_6_755 : subd9_6 [3, -1, 1] = true := by decide +kernel
theorem subd9_6_756 : subd9_6 [3, -1, 2] = true := by decide +kernel
theorem subd9_6_757 : subd9_6 [3, -1, 3] = true := by decide +kernel
theorem subd9_6_758 : subd9_6 [3, -1, 4] = true := by decide +kernel
theorem subd9_6_759 : subd9_6 [3, -1, 5] = true := by decide +kernel
theorem subd9_6_760 : subd9_6 [3, -1, 6] = true := by decide +kernel
theorem subd9_6_761 : subd9_6 [3, -1, 7] = true := by decide +kernel
theorem subd9_6_762 : subd9_6 [3, 0, -7] = true := by decide +kernel
theorem subd9_6_763 : subd9_6 [3, 0, -6] = true := by decide +kernel
theorem subd9_6_764 : subd9_6 [3, 0, -5] = true := by decide +kernel
theorem subd9_6_765 : subd9_6 [3, 0, -4] = true := by decide +kernel
theorem subd9_6_766 : subd9_6 [3, 0, -3] = true := by decide +kernel
theorem subd9_6_767 : subd9_6 [3, 0, -2] = true := by decide +kernel
theorem sbd9_6_23 : ∀ q ∈ blkd9_6_23, subd9_6 q = true := by
  unfold blkd9_6_23
  exact List.forall_mem_cons.2 ⟨subd9_6_736, List.forall_mem_cons.2 ⟨subd9_6_737, List.forall_mem_cons.2 ⟨subd9_6_738, List.forall_mem_cons.2 ⟨subd9_6_739, List.forall_mem_cons.2 ⟨subd9_6_740, List.forall_mem_cons.2 ⟨subd9_6_741, List.forall_mem_cons.2 ⟨subd9_6_742, List.forall_mem_cons.2 ⟨subd9_6_743, List.forall_mem_cons.2 ⟨subd9_6_744, List.forall_mem_cons.2 ⟨subd9_6_745, List.forall_mem_cons.2 ⟨subd9_6_746, List.forall_mem_cons.2 ⟨subd9_6_747, List.forall_mem_cons.2 ⟨subd9_6_748, List.forall_mem_cons.2 ⟨subd9_6_749, List.forall_mem_cons.2 ⟨subd9_6_750, List.forall_mem_cons.2 ⟨subd9_6_751, List.forall_mem_cons.2 ⟨subd9_6_752, List.forall_mem_cons.2 ⟨subd9_6_753, List.forall_mem_cons.2 ⟨subd9_6_754, List.forall_mem_cons.2 ⟨subd9_6_755, List.forall_mem_cons.2 ⟨subd9_6_756, List.forall_mem_cons.2 ⟨subd9_6_757, List.forall_mem_cons.2 ⟨subd9_6_758, List.forall_mem_cons.2 ⟨subd9_6_759, List.forall_mem_cons.2 ⟨subd9_6_760, List.forall_mem_cons.2 ⟨subd9_6_761, List.forall_mem_cons.2 ⟨subd9_6_762, List.forall_mem_cons.2 ⟨subd9_6_763, List.forall_mem_cons.2 ⟨subd9_6_764, List.forall_mem_cons.2 ⟨subd9_6_765, List.forall_mem_cons.2 ⟨subd9_6_766, List.forall_mem_cons.2 ⟨subd9_6_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_768 : subd9_6 [3, 0, -1] = true := by decide +kernel
theorem subd9_6_769 : subd9_6 [3, 0, 0] = true := by decide +kernel
theorem subd9_6_770 : subd9_6 [3, 0, 1] = true := by decide +kernel
theorem subd9_6_771 : subd9_6 [3, 0, 2] = true := by decide +kernel
theorem subd9_6_772 : subd9_6 [3, 0, 3] = true := by decide +kernel
theorem subd9_6_773 : subd9_6 [3, 0, 4] = true := by decide +kernel
theorem subd9_6_774 : subd9_6 [3, 0, 5] = true := by decide +kernel
theorem subd9_6_775 : subd9_6 [3, 0, 6] = true := by decide +kernel
theorem subd9_6_776 : subd9_6 [3, 0, 7] = true := by decide +kernel
theorem subd9_6_777 : subd9_6 [3, 1, -7] = true := by decide +kernel
theorem subd9_6_778 : subd9_6 [3, 1, -6] = true := by decide +kernel
theorem subd9_6_779 : subd9_6 [3, 1, -5] = true := by decide +kernel
theorem subd9_6_780 : subd9_6 [3, 1, -4] = true := by decide +kernel
theorem subd9_6_781 : subd9_6 [3, 1, -3] = true := by decide +kernel
theorem subd9_6_782 : subd9_6 [3, 1, -2] = true := by decide +kernel
theorem subd9_6_783 : subd9_6 [3, 1, -1] = true := by decide +kernel
theorem subd9_6_784 : subd9_6 [3, 1, 0] = true := by decide +kernel
theorem subd9_6_785 : subd9_6 [3, 1, 1] = true := by decide +kernel
theorem subd9_6_786 : subd9_6 [3, 1, 2] = true := by decide +kernel
theorem subd9_6_787 : subd9_6 [3, 1, 3] = true := by decide +kernel
theorem subd9_6_788 : subd9_6 [3, 1, 4] = true := by decide +kernel
theorem subd9_6_789 : subd9_6 [3, 1, 5] = true := by decide +kernel
theorem subd9_6_790 : subd9_6 [3, 1, 6] = true := by decide +kernel
theorem subd9_6_791 : subd9_6 [3, 1, 7] = true := by decide +kernel
theorem subd9_6_792 : subd9_6 [3, 2, -7] = true := by decide +kernel
theorem subd9_6_793 : subd9_6 [3, 2, -6] = true := by decide +kernel
theorem subd9_6_794 : subd9_6 [3, 2, -5] = true := by decide +kernel
theorem subd9_6_795 : subd9_6 [3, 2, -4] = true := by decide +kernel
theorem subd9_6_796 : subd9_6 [3, 2, -3] = true := by decide +kernel
theorem subd9_6_797 : subd9_6 [3, 2, -2] = true := by decide +kernel
theorem subd9_6_798 : subd9_6 [3, 2, -1] = true := by decide +kernel
theorem subd9_6_799 : subd9_6 [3, 2, 0] = true := by decide +kernel
theorem sbd9_6_24 : ∀ q ∈ blkd9_6_24, subd9_6 q = true := by
  unfold blkd9_6_24
  exact List.forall_mem_cons.2 ⟨subd9_6_768, List.forall_mem_cons.2 ⟨subd9_6_769, List.forall_mem_cons.2 ⟨subd9_6_770, List.forall_mem_cons.2 ⟨subd9_6_771, List.forall_mem_cons.2 ⟨subd9_6_772, List.forall_mem_cons.2 ⟨subd9_6_773, List.forall_mem_cons.2 ⟨subd9_6_774, List.forall_mem_cons.2 ⟨subd9_6_775, List.forall_mem_cons.2 ⟨subd9_6_776, List.forall_mem_cons.2 ⟨subd9_6_777, List.forall_mem_cons.2 ⟨subd9_6_778, List.forall_mem_cons.2 ⟨subd9_6_779, List.forall_mem_cons.2 ⟨subd9_6_780, List.forall_mem_cons.2 ⟨subd9_6_781, List.forall_mem_cons.2 ⟨subd9_6_782, List.forall_mem_cons.2 ⟨subd9_6_783, List.forall_mem_cons.2 ⟨subd9_6_784, List.forall_mem_cons.2 ⟨subd9_6_785, List.forall_mem_cons.2 ⟨subd9_6_786, List.forall_mem_cons.2 ⟨subd9_6_787, List.forall_mem_cons.2 ⟨subd9_6_788, List.forall_mem_cons.2 ⟨subd9_6_789, List.forall_mem_cons.2 ⟨subd9_6_790, List.forall_mem_cons.2 ⟨subd9_6_791, List.forall_mem_cons.2 ⟨subd9_6_792, List.forall_mem_cons.2 ⟨subd9_6_793, List.forall_mem_cons.2 ⟨subd9_6_794, List.forall_mem_cons.2 ⟨subd9_6_795, List.forall_mem_cons.2 ⟨subd9_6_796, List.forall_mem_cons.2 ⟨subd9_6_797, List.forall_mem_cons.2 ⟨subd9_6_798, List.forall_mem_cons.2 ⟨subd9_6_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
