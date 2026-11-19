import ReflectZphi.Data.Cert5.C081.Base

namespace ReflectZphi.Data.Cert5.C081
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_384 : sub4 [1, -1, 0] = true := by decide +kernel
theorem sub4_385 : sub4 [1, -1, 1] = true := by decide +kernel
theorem sub4_386 : sub4 [1, -1, 2] = true := by decide +kernel
theorem sub4_387 : sub4 [1, -1, 3] = true := by decide +kernel
theorem sub4_388 : sub4 [1, -1, 4] = true := by decide +kernel
theorem sub4_389 : sub4 [1, -1, 5] = true := by decide +kernel
theorem sub4_390 : sub4 [1, -1, 6] = true := by decide +kernel
theorem sub4_391 : sub4 [1, -1, 7] = true := by decide +kernel
theorem sub4_392 : sub4 [1, -1, 8] = true := by decide +kernel
theorem sub4_393 : sub4 [1, -1, 9] = true := by decide +kernel
theorem sub4_394 : sub4 [1, 0, -10] = true := by decide +kernel
theorem sub4_395 : sub4 [1, 0, -9] = true := by decide +kernel
theorem sub4_396 : sub4 [1, 0, -8] = true := by decide +kernel
theorem sub4_397 : sub4 [1, 0, -7] = true := by decide +kernel
theorem sub4_398 : sub4 [1, 0, -6] = true := by decide +kernel
theorem sub4_399 : sub4 [1, 0, -5] = true := by decide +kernel
theorem sub4_400 : sub4 [1, 0, -4] = true := by decide +kernel
theorem sub4_401 : sub4 [1, 0, -3] = true := by decide +kernel
theorem sub4_402 : sub4 [1, 0, -2] = true := by decide +kernel
theorem sub4_403 : sub4 [1, 0, -1] = true := by decide +kernel
theorem sub4_404 : sub4 [1, 0, 0] = true := by decide +kernel
theorem sub4_405 : sub4 [1, 0, 1] = true := by decide +kernel
theorem sub4_406 : sub4 [1, 0, 2] = true := by decide +kernel
theorem sub4_407 : sub4 [1, 0, 3] = true := by decide +kernel
theorem sub4_408 : sub4 [1, 0, 4] = true := by decide +kernel
theorem sub4_409 : sub4 [1, 0, 5] = true := by decide +kernel
theorem sub4_410 : sub4 [1, 0, 6] = true := by decide +kernel
theorem sub4_411 : sub4 [1, 0, 7] = true := by decide +kernel
theorem sub4_412 : sub4 [1, 0, 8] = true := by decide +kernel
theorem sub4_413 : sub4 [1, 0, 9] = true := by decide +kernel
theorem sub4_414 : sub4 [1, 1, -10] = true := by decide +kernel
theorem sub4_415 : sub4 [1, 1, -9] = true := by decide +kernel
theorem sb4_12 : ∀ q ∈ blk4_12, sub4 q = true := by
  unfold blk4_12
  exact List.forall_mem_cons.2 ⟨sub4_384, List.forall_mem_cons.2 ⟨sub4_385, List.forall_mem_cons.2 ⟨sub4_386, List.forall_mem_cons.2 ⟨sub4_387, List.forall_mem_cons.2 ⟨sub4_388, List.forall_mem_cons.2 ⟨sub4_389, List.forall_mem_cons.2 ⟨sub4_390, List.forall_mem_cons.2 ⟨sub4_391, List.forall_mem_cons.2 ⟨sub4_392, List.forall_mem_cons.2 ⟨sub4_393, List.forall_mem_cons.2 ⟨sub4_394, List.forall_mem_cons.2 ⟨sub4_395, List.forall_mem_cons.2 ⟨sub4_396, List.forall_mem_cons.2 ⟨sub4_397, List.forall_mem_cons.2 ⟨sub4_398, List.forall_mem_cons.2 ⟨sub4_399, List.forall_mem_cons.2 ⟨sub4_400, List.forall_mem_cons.2 ⟨sub4_401, List.forall_mem_cons.2 ⟨sub4_402, List.forall_mem_cons.2 ⟨sub4_403, List.forall_mem_cons.2 ⟨sub4_404, List.forall_mem_cons.2 ⟨sub4_405, List.forall_mem_cons.2 ⟨sub4_406, List.forall_mem_cons.2 ⟨sub4_407, List.forall_mem_cons.2 ⟨sub4_408, List.forall_mem_cons.2 ⟨sub4_409, List.forall_mem_cons.2 ⟨sub4_410, List.forall_mem_cons.2 ⟨sub4_411, List.forall_mem_cons.2 ⟨sub4_412, List.forall_mem_cons.2 ⟨sub4_413, List.forall_mem_cons.2 ⟨sub4_414, List.forall_mem_cons.2 ⟨sub4_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_416 : sub4 [1, 1, -8] = true := by decide +kernel
theorem sub4_417 : sub4 [1, 1, -7] = true := by decide +kernel
theorem sub4_418 : sub4 [1, 1, -6] = true := by decide +kernel
theorem sub4_419 : sub4 [1, 1, -5] = true := by decide +kernel
theorem sub4_420 : sub4 [1, 1, -4] = true := by decide +kernel
theorem sub4_421 : sub4 [1, 1, -3] = true := by decide +kernel
theorem sub4_422 : sub4 [1, 1, -2] = true := by decide +kernel
theorem sub4_423 : sub4 [1, 1, -1] = true := by decide +kernel
theorem sub4_424 : sub4 [1, 1, 0] = true := by decide +kernel
theorem sub4_425 : sub4 [1, 1, 1] = true := by decide +kernel
theorem sub4_426 : sub4 [1, 1, 2] = true := by decide +kernel
theorem sub4_427 : sub4 [1, 1, 3] = true := by decide +kernel
theorem sub4_428 : sub4 [1, 1, 4] = true := by decide +kernel
theorem sub4_429 : sub4 [1, 1, 5] = true := by decide +kernel
theorem sub4_430 : sub4 [1, 1, 6] = true := by decide +kernel
theorem sub4_431 : sub4 [1, 1, 7] = true := by decide +kernel
theorem sub4_432 : sub4 [1, 1, 8] = true := by decide +kernel
theorem sub4_433 : sub4 [1, 1, 9] = true := by decide +kernel
theorem sub4_434 : sub4 [1, 2, -9] = true := by decide +kernel
theorem sub4_435 : sub4 [1, 2, -8] = true := by decide +kernel
theorem sub4_436 : sub4 [1, 2, -7] = true := by decide +kernel
theorem sub4_437 : sub4 [1, 2, -6] = true := by decide +kernel
theorem sub4_438 : sub4 [1, 2, -5] = true := by decide +kernel
theorem sub4_439 : sub4 [1, 2, -4] = true := by decide +kernel
theorem sub4_440 : sub4 [1, 2, -3] = true := by decide +kernel
theorem sub4_441 : sub4 [1, 2, -2] = true := by decide +kernel
theorem sub4_442 : sub4 [1, 2, -1] = true := by decide +kernel
theorem sub4_443 : sub4 [1, 2, 0] = true := by decide +kernel
theorem sub4_444 : sub4 [1, 2, 1] = true := by decide +kernel
theorem sub4_445 : sub4 [1, 2, 2] = true := by decide +kernel
theorem sub4_446 : sub4 [1, 2, 3] = true := by decide +kernel
theorem sub4_447 : sub4 [1, 2, 4] = true := by decide +kernel
theorem sb4_13 : ∀ q ∈ blk4_13, sub4 q = true := by
  unfold blk4_13
  exact List.forall_mem_cons.2 ⟨sub4_416, List.forall_mem_cons.2 ⟨sub4_417, List.forall_mem_cons.2 ⟨sub4_418, List.forall_mem_cons.2 ⟨sub4_419, List.forall_mem_cons.2 ⟨sub4_420, List.forall_mem_cons.2 ⟨sub4_421, List.forall_mem_cons.2 ⟨sub4_422, List.forall_mem_cons.2 ⟨sub4_423, List.forall_mem_cons.2 ⟨sub4_424, List.forall_mem_cons.2 ⟨sub4_425, List.forall_mem_cons.2 ⟨sub4_426, List.forall_mem_cons.2 ⟨sub4_427, List.forall_mem_cons.2 ⟨sub4_428, List.forall_mem_cons.2 ⟨sub4_429, List.forall_mem_cons.2 ⟨sub4_430, List.forall_mem_cons.2 ⟨sub4_431, List.forall_mem_cons.2 ⟨sub4_432, List.forall_mem_cons.2 ⟨sub4_433, List.forall_mem_cons.2 ⟨sub4_434, List.forall_mem_cons.2 ⟨sub4_435, List.forall_mem_cons.2 ⟨sub4_436, List.forall_mem_cons.2 ⟨sub4_437, List.forall_mem_cons.2 ⟨sub4_438, List.forall_mem_cons.2 ⟨sub4_439, List.forall_mem_cons.2 ⟨sub4_440, List.forall_mem_cons.2 ⟨sub4_441, List.forall_mem_cons.2 ⟨sub4_442, List.forall_mem_cons.2 ⟨sub4_443, List.forall_mem_cons.2 ⟨sub4_444, List.forall_mem_cons.2 ⟨sub4_445, List.forall_mem_cons.2 ⟨sub4_446, List.forall_mem_cons.2 ⟨sub4_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_448 : sub4 [1, 2, 5] = true := by decide +kernel
theorem sub4_449 : sub4 [1, 2, 6] = true := by decide +kernel
theorem sub4_450 : sub4 [1, 2, 7] = true := by decide +kernel
theorem sub4_451 : sub4 [1, 3, -8] = true := by decide +kernel
theorem sub4_452 : sub4 [1, 3, -7] = true := by decide +kernel
theorem sub4_453 : sub4 [1, 3, -6] = true := by decide +kernel
theorem sub4_454 : sub4 [1, 3, -5] = true := by decide +kernel
theorem sub4_455 : sub4 [1, 3, -4] = true := by decide +kernel
theorem sub4_456 : sub4 [1, 3, -3] = true := by decide +kernel
theorem sub4_457 : sub4 [1, 3, -2] = true := by decide +kernel
theorem sub4_458 : sub4 [1, 3, -1] = true := by decide +kernel
theorem sub4_459 : sub4 [1, 3, 0] = true := by decide +kernel
theorem sub4_460 : sub4 [1, 3, 1] = true := by decide +kernel
theorem sub4_461 : sub4 [1, 3, 2] = true := by decide +kernel
theorem sub4_462 : sub4 [1, 3, 3] = true := by decide +kernel
theorem sub4_463 : sub4 [1, 3, 4] = true := by decide +kernel
theorem sub4_464 : sub4 [1, 3, 5] = true := by decide +kernel
theorem sub4_465 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_466 : sub4 [2, -3] = true := by decide +kernel
theorem sub4_467 : sub4 [2, -2, -6] = true := by decide +kernel
theorem sub4_468 : sub4 [2, -2, -5] = true := by decide +kernel
theorem sub4_469 : sub4 [2, -2, -4] = true := by decide +kernel
theorem sub4_470 : sub4 [2, -2, -3] = true := by decide +kernel
theorem sub4_471 : sub4 [2, -2, -2] = true := by decide +kernel
theorem sub4_472 : sub4 [2, -2, -1] = true := by decide +kernel
theorem sub4_473 : sub4 [2, -2, 0] = true := by decide +kernel
theorem sub4_474 : sub4 [2, -2, 1] = true := by decide +kernel
theorem sub4_475 : sub4 [2, -2, 2] = true := by decide +kernel
theorem sub4_476 : sub4 [2, -2, 3] = true := by decide +kernel
theorem sub4_477 : sub4 [2, -2, 4] = true := by decide +kernel
theorem sub4_478 : sub4 [2, -2, 5] = true := by decide +kernel
theorem sub4_479 : sub4 [2, -2, 6] = true := by decide +kernel
theorem sb4_14 : ∀ q ∈ blk4_14, sub4 q = true := by
  unfold blk4_14
  exact List.forall_mem_cons.2 ⟨sub4_448, List.forall_mem_cons.2 ⟨sub4_449, List.forall_mem_cons.2 ⟨sub4_450, List.forall_mem_cons.2 ⟨sub4_451, List.forall_mem_cons.2 ⟨sub4_452, List.forall_mem_cons.2 ⟨sub4_453, List.forall_mem_cons.2 ⟨sub4_454, List.forall_mem_cons.2 ⟨sub4_455, List.forall_mem_cons.2 ⟨sub4_456, List.forall_mem_cons.2 ⟨sub4_457, List.forall_mem_cons.2 ⟨sub4_458, List.forall_mem_cons.2 ⟨sub4_459, List.forall_mem_cons.2 ⟨sub4_460, List.forall_mem_cons.2 ⟨sub4_461, List.forall_mem_cons.2 ⟨sub4_462, List.forall_mem_cons.2 ⟨sub4_463, List.forall_mem_cons.2 ⟨sub4_464, List.forall_mem_cons.2 ⟨sub4_465, List.forall_mem_cons.2 ⟨sub4_466, List.forall_mem_cons.2 ⟨sub4_467, List.forall_mem_cons.2 ⟨sub4_468, List.forall_mem_cons.2 ⟨sub4_469, List.forall_mem_cons.2 ⟨sub4_470, List.forall_mem_cons.2 ⟨sub4_471, List.forall_mem_cons.2 ⟨sub4_472, List.forall_mem_cons.2 ⟨sub4_473, List.forall_mem_cons.2 ⟨sub4_474, List.forall_mem_cons.2 ⟨sub4_475, List.forall_mem_cons.2 ⟨sub4_476, List.forall_mem_cons.2 ⟨sub4_477, List.forall_mem_cons.2 ⟨sub4_478, List.forall_mem_cons.2 ⟨sub4_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_480 : sub4 [2, -2, 7] = true := by decide +kernel
theorem sub4_481 : sub4 [2, -2, 8] = true := by decide +kernel
theorem sub4_482 : sub4 [2, -1, -7] = true := by decide +kernel
theorem sub4_483 : sub4 [2, -1, -6] = true := by decide +kernel
theorem sub4_484 : sub4 [2, -1, -5] = true := by decide +kernel
theorem sub4_485 : sub4 [2, -1, -4] = true := by decide +kernel
theorem sub4_486 : sub4 [2, -1, -3] = true := by decide +kernel
theorem sub4_487 : sub4 [2, -1, -2] = true := by decide +kernel
theorem sub4_488 : sub4 [2, -1, -1] = true := by decide +kernel
theorem sub4_489 : sub4 [2, -1, 0] = true := by decide +kernel
theorem sub4_490 : sub4 [2, -1, 1] = true := by decide +kernel
theorem sub4_491 : sub4 [2, -1, 2] = true := by decide +kernel
theorem sub4_492 : sub4 [2, -1, 3] = true := by decide +kernel
theorem sub4_493 : sub4 [2, -1, 4] = true := by decide +kernel
theorem sub4_494 : sub4 [2, -1, 5] = true := by decide +kernel
theorem sub4_495 : sub4 [2, -1, 6] = true := by decide +kernel
theorem sub4_496 : sub4 [2, -1, 7] = true := by decide +kernel
theorem sub4_497 : sub4 [2, -1, 8] = true := by decide +kernel
theorem sub4_498 : sub4 [2, -1, 9] = true := by decide +kernel
theorem sub4_499 : sub4 [2, 0, -8] = true := by decide +kernel
theorem sub4_500 : sub4 [2, 0, -7] = true := by decide +kernel
theorem sub4_501 : sub4 [2, 0, -6] = true := by decide +kernel
theorem sub4_502 : sub4 [2, 0, -5] = true := by decide +kernel
theorem sub4_503 : sub4 [2, 0, -4] = true := by decide +kernel
theorem sub4_504 : sub4 [2, 0, -3] = true := by decide +kernel
theorem sub4_505 : sub4 [2, 0, -2] = true := by decide +kernel
theorem sub4_506 : sub4 [2, 0, -1] = true := by decide +kernel
theorem sub4_507 : sub4 [2, 0, 0] = true := by decide +kernel
theorem sub4_508 : sub4 [2, 0, 1] = true := by decide +kernel
theorem sub4_509 : sub4 [2, 0, 2] = true := by decide +kernel
theorem sub4_510 : sub4 [2, 0, 3] = true := by decide +kernel
theorem sub4_511 : sub4 [2, 0, 4] = true := by decide +kernel
theorem sb4_15 : ∀ q ∈ blk4_15, sub4 q = true := by
  unfold blk4_15
  exact List.forall_mem_cons.2 ⟨sub4_480, List.forall_mem_cons.2 ⟨sub4_481, List.forall_mem_cons.2 ⟨sub4_482, List.forall_mem_cons.2 ⟨sub4_483, List.forall_mem_cons.2 ⟨sub4_484, List.forall_mem_cons.2 ⟨sub4_485, List.forall_mem_cons.2 ⟨sub4_486, List.forall_mem_cons.2 ⟨sub4_487, List.forall_mem_cons.2 ⟨sub4_488, List.forall_mem_cons.2 ⟨sub4_489, List.forall_mem_cons.2 ⟨sub4_490, List.forall_mem_cons.2 ⟨sub4_491, List.forall_mem_cons.2 ⟨sub4_492, List.forall_mem_cons.2 ⟨sub4_493, List.forall_mem_cons.2 ⟨sub4_494, List.forall_mem_cons.2 ⟨sub4_495, List.forall_mem_cons.2 ⟨sub4_496, List.forall_mem_cons.2 ⟨sub4_497, List.forall_mem_cons.2 ⟨sub4_498, List.forall_mem_cons.2 ⟨sub4_499, List.forall_mem_cons.2 ⟨sub4_500, List.forall_mem_cons.2 ⟨sub4_501, List.forall_mem_cons.2 ⟨sub4_502, List.forall_mem_cons.2 ⟨sub4_503, List.forall_mem_cons.2 ⟨sub4_504, List.forall_mem_cons.2 ⟨sub4_505, List.forall_mem_cons.2 ⟨sub4_506, List.forall_mem_cons.2 ⟨sub4_507, List.forall_mem_cons.2 ⟨sub4_508, List.forall_mem_cons.2 ⟨sub4_509, List.forall_mem_cons.2 ⟨sub4_510, List.forall_mem_cons.2 ⟨sub4_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_512 : sub4 [2, 0, 5] = true := by decide +kernel
theorem sub4_513 : sub4 [2, 0, 6] = true := by decide +kernel
theorem sub4_514 : sub4 [2, 0, 7] = true := by decide +kernel
theorem sub4_515 : sub4 [2, 0, 8] = true := by decide +kernel
theorem sub4_516 : sub4 [2, 0, 9] = true := by decide +kernel
theorem sub4_517 : sub4 [2, 1, -9] = true := by decide +kernel
theorem sub4_518 : sub4 [2, 1, -8] = true := by decide +kernel
theorem sub4_519 : sub4 [2, 1, -7] = true := by decide +kernel
theorem sub4_520 : sub4 [2, 1, -6] = true := by decide +kernel
theorem sub4_521 : sub4 [2, 1, -5] = true := by decide +kernel
theorem sub4_522 : sub4 [2, 1, -4] = true := by decide +kernel
theorem sub4_523 : sub4 [2, 1, -3] = true := by decide +kernel
theorem sub4_524 : sub4 [2, 1, -2] = true := by decide +kernel
theorem sub4_525 : sub4 [2, 1, -1] = true := by decide +kernel
theorem sub4_526 : sub4 [2, 1, 0] = true := by decide +kernel
theorem sub4_527 : sub4 [2, 1, 1] = true := by decide +kernel
theorem sub4_528 : sub4 [2, 1, 2] = true := by decide +kernel
theorem sub4_529 : sub4 [2, 1, 3] = true := by decide +kernel
theorem sub4_530 : sub4 [2, 1, 4] = true := by decide +kernel
theorem sub4_531 : sub4 [2, 1, 5] = true := by decide +kernel
theorem sub4_532 : sub4 [2, 1, 6] = true := by decide +kernel
theorem sub4_533 : sub4 [2, 1, 7] = true := by decide +kernel
theorem sub4_534 : sub4 [2, 1, 8] = true := by decide +kernel
theorem sub4_535 : sub4 [2, 2, -8] = true := by decide +kernel
theorem sub4_536 : sub4 [2, 2, -7] = true := by decide +kernel
theorem sub4_537 : sub4 [2, 2, -6] = true := by decide +kernel
theorem sub4_538 : sub4 [2, 2, -5] = true := by decide +kernel
theorem sub4_539 : sub4 [2, 2, -4] = true := by decide +kernel
theorem sub4_540 : sub4 [2, 2, -3] = true := by decide +kernel
theorem sub4_541 : sub4 [2, 2, -2] = true := by decide +kernel
theorem sub4_542 : sub4 [2, 2, -1] = true := by decide +kernel
theorem sub4_543 : sub4 [2, 2, 0] = true := by decide +kernel
theorem sb4_16 : ∀ q ∈ blk4_16, sub4 q = true := by
  unfold blk4_16
  exact List.forall_mem_cons.2 ⟨sub4_512, List.forall_mem_cons.2 ⟨sub4_513, List.forall_mem_cons.2 ⟨sub4_514, List.forall_mem_cons.2 ⟨sub4_515, List.forall_mem_cons.2 ⟨sub4_516, List.forall_mem_cons.2 ⟨sub4_517, List.forall_mem_cons.2 ⟨sub4_518, List.forall_mem_cons.2 ⟨sub4_519, List.forall_mem_cons.2 ⟨sub4_520, List.forall_mem_cons.2 ⟨sub4_521, List.forall_mem_cons.2 ⟨sub4_522, List.forall_mem_cons.2 ⟨sub4_523, List.forall_mem_cons.2 ⟨sub4_524, List.forall_mem_cons.2 ⟨sub4_525, List.forall_mem_cons.2 ⟨sub4_526, List.forall_mem_cons.2 ⟨sub4_527, List.forall_mem_cons.2 ⟨sub4_528, List.forall_mem_cons.2 ⟨sub4_529, List.forall_mem_cons.2 ⟨sub4_530, List.forall_mem_cons.2 ⟨sub4_531, List.forall_mem_cons.2 ⟨sub4_532, List.forall_mem_cons.2 ⟨sub4_533, List.forall_mem_cons.2 ⟨sub4_534, List.forall_mem_cons.2 ⟨sub4_535, List.forall_mem_cons.2 ⟨sub4_536, List.forall_mem_cons.2 ⟨sub4_537, List.forall_mem_cons.2 ⟨sub4_538, List.forall_mem_cons.2 ⟨sub4_539, List.forall_mem_cons.2 ⟨sub4_540, List.forall_mem_cons.2 ⟨sub4_541, List.forall_mem_cons.2 ⟨sub4_542, List.forall_mem_cons.2 ⟨sub4_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_544 : sub4 [2, 2, 1] = true := by decide +kernel
theorem sub4_545 : sub4 [2, 2, 2] = true := by decide +kernel
theorem sub4_546 : sub4 [2, 2, 3] = true := by decide +kernel
theorem sub4_547 : sub4 [2, 2, 4] = true := by decide +kernel
theorem sub4_548 : sub4 [2, 2, 5] = true := by decide +kernel
theorem sub4_549 : sub4 [2, 2, 6] = true := by decide +kernel
theorem sub4_550 : sub4 [2, 2, 7] = true := by decide +kernel
theorem sub4_551 : sub4 [2, 3] = true := by decide +kernel
theorem sub4_552 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_553 : sub4 [3, -2] = true := by decide +kernel
theorem sub4_554 : sub4 [3, -1] = true := by decide +kernel
theorem sub4_555 : sub4 [3, 0, -6] = true := by decide +kernel
theorem sub4_556 : sub4 [3, 0, -5] = true := by decide +kernel
theorem sub4_557 : sub4 [3, 0, -4] = true := by decide +kernel
theorem sub4_558 : sub4 [3, 0, -3] = true := by decide +kernel
theorem sub4_559 : sub4 [3, 0, -2] = true := by decide +kernel
theorem sub4_560 : sub4 [3, 0, -1] = true := by decide +kernel
theorem sub4_561 : sub4 [3, 0, 0] = true := by decide +kernel
theorem sub4_562 : sub4 [3, 0, 1] = true := by decide +kernel
theorem sub4_563 : sub4 [3, 0, 2] = true := by decide +kernel
theorem sub4_564 : sub4 [3, 0, 3] = true := by decide +kernel
theorem sub4_565 : sub4 [3, 0, 4] = true := by decide +kernel
theorem sub4_566 : sub4 [3, 0, 5] = true := by decide +kernel
theorem sub4_567 : sub4 [3, 0, 6] = true := by decide +kernel
theorem sub4_568 : sub4 [3, 0, 7] = true := by decide +kernel
theorem sub4_569 : sub4 [3, 1, -7] = true := by decide +kernel
theorem sub4_570 : sub4 [3, 1, -6] = true := by decide +kernel
theorem sub4_571 : sub4 [3, 1, -5] = true := by decide +kernel
theorem sub4_572 : sub4 [3, 1, -4] = true := by decide +kernel
theorem sub4_573 : sub4 [3, 1, -3] = true := by decide +kernel
theorem sub4_574 : sub4 [3, 1, -2] = true := by decide +kernel
theorem sub4_575 : sub4 [3, 1, -1] = true := by decide +kernel
theorem sb4_17 : ∀ q ∈ blk4_17, sub4 q = true := by
  unfold blk4_17
  exact List.forall_mem_cons.2 ⟨sub4_544, List.forall_mem_cons.2 ⟨sub4_545, List.forall_mem_cons.2 ⟨sub4_546, List.forall_mem_cons.2 ⟨sub4_547, List.forall_mem_cons.2 ⟨sub4_548, List.forall_mem_cons.2 ⟨sub4_549, List.forall_mem_cons.2 ⟨sub4_550, List.forall_mem_cons.2 ⟨sub4_551, List.forall_mem_cons.2 ⟨sub4_552, List.forall_mem_cons.2 ⟨sub4_553, List.forall_mem_cons.2 ⟨sub4_554, List.forall_mem_cons.2 ⟨sub4_555, List.forall_mem_cons.2 ⟨sub4_556, List.forall_mem_cons.2 ⟨sub4_557, List.forall_mem_cons.2 ⟨sub4_558, List.forall_mem_cons.2 ⟨sub4_559, List.forall_mem_cons.2 ⟨sub4_560, List.forall_mem_cons.2 ⟨sub4_561, List.forall_mem_cons.2 ⟨sub4_562, List.forall_mem_cons.2 ⟨sub4_563, List.forall_mem_cons.2 ⟨sub4_564, List.forall_mem_cons.2 ⟨sub4_565, List.forall_mem_cons.2 ⟨sub4_566, List.forall_mem_cons.2 ⟨sub4_567, List.forall_mem_cons.2 ⟨sub4_568, List.forall_mem_cons.2 ⟨sub4_569, List.forall_mem_cons.2 ⟨sub4_570, List.forall_mem_cons.2 ⟨sub4_571, List.forall_mem_cons.2 ⟨sub4_572, List.forall_mem_cons.2 ⟨sub4_573, List.forall_mem_cons.2 ⟨sub4_574, List.forall_mem_cons.2 ⟨sub4_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_576 : sub4 [3, 1, 0] = true := by decide +kernel
theorem sub4_577 : sub4 [3, 1, 1] = true := by decide +kernel
theorem sub4_578 : sub4 [3, 1, 2] = true := by decide +kernel
theorem sub4_579 : sub4 [3, 1, 3] = true := by decide +kernel
theorem sub4_580 : sub4 [3, 1, 4] = true := by decide +kernel
theorem sub4_581 : sub4 [3, 1, 5] = true := by decide +kernel
theorem sub4_582 : sub4 [3, 1, 6] = true := by decide +kernel
theorem sub4_583 : sub4 [3, 1, 7] = true := by decide +kernel
theorem sub4_584 : sub4 [3, 2] = true := by decide +kernel
theorem sub4_585 : sub4 [3, 3] = true := by decide +kernel
theorem sub4_586 : sub4 [4] = true := by decide +kernel
theorem sb4_18 : ∀ q ∈ blk4_18, sub4 q = true := by
  unfold blk4_18
  exact List.forall_mem_cons.2 ⟨sub4_576, List.forall_mem_cons.2 ⟨sub4_577, List.forall_mem_cons.2 ⟨sub4_578, List.forall_mem_cons.2 ⟨sub4_579, List.forall_mem_cons.2 ⟨sub4_580, List.forall_mem_cons.2 ⟨sub4_581, List.forall_mem_cons.2 ⟨sub4_582, List.forall_mem_cons.2 ⟨sub4_583, List.forall_mem_cons.2 ⟨sub4_584, List.forall_mem_cons.2 ⟨sub4_585, List.forall_mem_cons.2 ⟨sub4_586, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_0 : sub5 [-4] = true := by decide +kernel
theorem sub5_1 : sub5 [-3, -3] = true := by decide +kernel
theorem sub5_2 : sub5 [-3, -2] = true := by decide +kernel
theorem sub5_3 : sub5 [-3, -1] = true := by decide +kernel
theorem sub5_4 : sub5 [-3, 0] = true := by decide +kernel
theorem sub5_5 : sub5 [-3, 1] = true := by decide +kernel
theorem sub5_6 : sub5 [-3, 2] = true := by decide +kernel
theorem sub5_7 : sub5 [-2, -4] = true := by decide +kernel
theorem sub5_8 : sub5 [-2, -3] = true := by decide +kernel
theorem sub5_9 : sub5 [-2, -2] = true := by decide +kernel
theorem sub5_10 : sub5 [-2, -1] = true := by decide +kernel
theorem sub5_11 : sub5 [-2, 0] = true := by decide +kernel
theorem sub5_12 : sub5 [-2, 1] = true := by decide +kernel
theorem sub5_13 : sub5 [-2, 2] = true := by decide +kernel
theorem sub5_14 : sub5 [-2, 3] = true := by decide +kernel
theorem sub5_15 : sub5 [-1, -4] = true := by decide +kernel
theorem sub5_16 : sub5 [-1, -3] = true := by decide +kernel
theorem sub5_17 : sub5 [-1, -2] = true := by decide +kernel
theorem sub5_18 : sub5 [-1, -1] = true := by decide +kernel
theorem sub5_19 : sub5 [-1, 0] = true := by decide +kernel
theorem sub5_20 : sub5 [-1, 1] = true := by decide +kernel
theorem sub5_21 : sub5 [-1, 2] = true := by decide +kernel
theorem sub5_22 : sub5 [-1, 3] = true := by decide +kernel
theorem sub5_23 : sub5 [0, -4] = true := by decide +kernel
theorem sub5_24 : sub5 [0, -3] = true := by decide +kernel
theorem sub5_25 : sub5 [0, -2] = true := by decide +kernel
theorem sub5_26 : sub5 [0, -1] = true := by decide +kernel
theorem sub5_27 : sub5 [0, 0, -7] = true := by decide +kernel
theorem sub5_28 : sub5 [0, 0, -6] = true := by decide +kernel
theorem sub5_29 : sub5 [0, 0, -5] = true := by decide +kernel
theorem sub5_30 : sub5 [0, 0, -4] = true := by decide +kernel
theorem sub5_31 : sub5 [0, 0, -3] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [0, 0, -2] = true := by decide +kernel
theorem sub5_33 : sub5 [0, 0, -1] = true := by decide +kernel
theorem sub5_34 : sub5 [0, 0, 0] = true := by decide +kernel
theorem sub5_35 : sub5 [0, 0, 1] = true := by decide +kernel
theorem sub5_36 : sub5 [0, 0, 2] = true := by decide +kernel
theorem sub5_37 : sub5 [0, 0, 3] = true := by decide +kernel
theorem sub5_38 : sub5 [0, 0, 4] = true := by decide +kernel
theorem sub5_39 : sub5 [0, 0, 5] = true := by decide +kernel
theorem sub5_40 : sub5 [0, 0, 6] = true := by decide +kernel
theorem sub5_41 : sub5 [0, 1] = true := by decide +kernel
theorem sub5_42 : sub5 [0, 2] = true := by decide +kernel
theorem sub5_43 : sub5 [0, 3] = true := by decide +kernel
theorem sub5_44 : sub5 [1, -4] = true := by decide +kernel
theorem sub5_45 : sub5 [1, -3] = true := by decide +kernel
theorem sub5_46 : sub5 [1, -2] = true := by decide +kernel
theorem sub5_47 : sub5 [1, -1] = true := by decide +kernel
theorem sub5_48 : sub5 [1, 0] = true := by decide +kernel
theorem sub5_49 : sub5 [1, 1] = true := by decide +kernel
theorem sub5_50 : sub5 [1, 2] = true := by decide +kernel
theorem sub5_51 : sub5 [1, 3] = true := by decide +kernel
theorem sub5_52 : sub5 [2, -4] = true := by decide +kernel
theorem sub5_53 : sub5 [2, -3] = true := by decide +kernel
theorem sub5_54 : sub5 [2, -2] = true := by decide +kernel
theorem sub5_55 : sub5 [2, -1] = true := by decide +kernel
theorem sub5_56 : sub5 [2, 0] = true := by decide +kernel
theorem sub5_57 : sub5 [2, 1] = true := by decide +kernel
theorem sub5_58 : sub5 [2, 2] = true := by decide +kernel
theorem sub5_59 : sub5 [2, 3] = true := by decide +kernel
theorem sub5_60 : sub5 [3, -3] = true := by decide +kernel
theorem sub5_61 : sub5 [3, -2] = true := by decide +kernel
theorem sub5_62 : sub5 [3, -1] = true := by decide +kernel
theorem sub5_63 : sub5 [3, 0] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_64 : sub5 [3, 1] = true := by decide +kernel
theorem sub5_65 : sub5 [3, 2] = true := by decide +kernel
theorem sub5_66 : sub5 [4] = true := by decide +kernel
theorem sb5_2 : ∀ q ∈ blk5_2, sub5 q = true := by
  unfold blk5_2
  exact List.forall_mem_cons.2 ⟨sub5_64, List.forall_mem_cons.2 ⟨sub5_65, List.forall_mem_cons.2 ⟨sub5_66, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C081
