import ReflectZphi.Data.Cert5.C102.Base

namespace ReflectZphi.Data.Cert5.C102
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_416 : sub8 [-3, 3, 6] = true := by decide +kernel
theorem sub8_417 : sub8 [-3, 3, 7] = true := by decide +kernel
theorem sub8_418 : sub8 [-3, 3, 8] = true := by decide +kernel
theorem sub8_419 : sub8 [-3, 4, -7] = true := by decide +kernel
theorem sub8_420 : sub8 [-3, 4, -6] = true := by decide +kernel
theorem sub8_421 : sub8 [-3, 4, -5] = true := by decide +kernel
theorem sub8_422 : sub8 [-3, 4, -4] = true := by decide +kernel
theorem sub8_423 : sub8 [-3, 4, -3] = true := by decide +kernel
theorem sub8_424 : sub8 [-3, 4, -2] = true := by decide +kernel
theorem sub8_425 : sub8 [-3, 4, -1] = true := by decide +kernel
theorem sub8_426 : sub8 [-3, 4, 0] = true := by decide +kernel
theorem sub8_427 : sub8 [-3, 4, 1] = true := by decide +kernel
theorem sub8_428 : sub8 [-3, 4, 2] = true := by decide +kernel
theorem sub8_429 : sub8 [-3, 4, 3] = true := by decide +kernel
theorem sub8_430 : sub8 [-3, 4, 4] = true := by decide +kernel
theorem sub8_431 : sub8 [-3, 4, 5] = true := by decide +kernel
theorem sub8_432 : sub8 [-3, 4, 6] = true := by decide +kernel
theorem sub8_433 : sub8 [-3, 4, 7] = true := by decide +kernel
theorem sub8_434 : sub8 [-3, 4, 8] = true := by decide +kernel
theorem sub8_435 : sub8 [-3, 5, -6] = true := by decide +kernel
theorem sub8_436 : sub8 [-3, 5, -5] = true := by decide +kernel
theorem sub8_437 : sub8 [-3, 5, -4] = true := by decide +kernel
theorem sub8_438 : sub8 [-3, 5, -3] = true := by decide +kernel
theorem sub8_439 : sub8 [-3, 5, -2] = true := by decide +kernel
theorem sub8_440 : sub8 [-3, 5, -1] = true := by decide +kernel
theorem sub8_441 : sub8 [-3, 5, 0] = true := by decide +kernel
theorem sub8_442 : sub8 [-3, 5, 1] = true := by decide +kernel
theorem sub8_443 : sub8 [-3, 5, 2] = true := by decide +kernel
theorem sub8_444 : sub8 [-3, 5, 3] = true := by decide +kernel
theorem sub8_445 : sub8 [-3, 5, 4] = true := by decide +kernel
theorem sub8_446 : sub8 [-3, 5, 5] = true := by decide +kernel
theorem sub8_447 : sub8 [-3, 5, 6] = true := by decide +kernel
theorem sb8_13 : ∀ q ∈ blk8_13, sub8 q = true := by
  unfold blk8_13
  exact List.forall_mem_cons.2 ⟨sub8_416, List.forall_mem_cons.2 ⟨sub8_417, List.forall_mem_cons.2 ⟨sub8_418, List.forall_mem_cons.2 ⟨sub8_419, List.forall_mem_cons.2 ⟨sub8_420, List.forall_mem_cons.2 ⟨sub8_421, List.forall_mem_cons.2 ⟨sub8_422, List.forall_mem_cons.2 ⟨sub8_423, List.forall_mem_cons.2 ⟨sub8_424, List.forall_mem_cons.2 ⟨sub8_425, List.forall_mem_cons.2 ⟨sub8_426, List.forall_mem_cons.2 ⟨sub8_427, List.forall_mem_cons.2 ⟨sub8_428, List.forall_mem_cons.2 ⟨sub8_429, List.forall_mem_cons.2 ⟨sub8_430, List.forall_mem_cons.2 ⟨sub8_431, List.forall_mem_cons.2 ⟨sub8_432, List.forall_mem_cons.2 ⟨sub8_433, List.forall_mem_cons.2 ⟨sub8_434, List.forall_mem_cons.2 ⟨sub8_435, List.forall_mem_cons.2 ⟨sub8_436, List.forall_mem_cons.2 ⟨sub8_437, List.forall_mem_cons.2 ⟨sub8_438, List.forall_mem_cons.2 ⟨sub8_439, List.forall_mem_cons.2 ⟨sub8_440, List.forall_mem_cons.2 ⟨sub8_441, List.forall_mem_cons.2 ⟨sub8_442, List.forall_mem_cons.2 ⟨sub8_443, List.forall_mem_cons.2 ⟨sub8_444, List.forall_mem_cons.2 ⟨sub8_445, List.forall_mem_cons.2 ⟨sub8_446, List.forall_mem_cons.2 ⟨sub8_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_448 : sub8 [-3, 5, 7] = true := by decide +kernel
theorem sub8_449 : sub8 [-3, 6] = true := by decide +kernel
theorem sub8_450 : sub8 [-3, 7] = true := by decide +kernel
theorem sub8_451 : sub8 [-3, 8] = true := by decide +kernel
theorem sub8_452 : sub8 [-2, -7] = true := by decide +kernel
theorem sub8_453 : sub8 [-2, -6] = true := by decide +kernel
theorem sub8_454 : sub8 [-2, -5] = true := by decide +kernel
theorem sub8_455 : sub8 [-2, -4] = true := by decide +kernel
theorem sub8_456 : sub8 [-2, -3, -8] = true := by decide +kernel
theorem sub8_457 : sub8 [-2, -3, -7] = true := by decide +kernel
theorem sub8_458 : sub8 [-2, -3, -6] = true := by decide +kernel
theorem sub8_459 : sub8 [-2, -3, -5] = true := by decide +kernel
theorem sub8_460 : sub8 [-2, -3, -4] = true := by decide +kernel
theorem sub8_461 : sub8 [-2, -3, -3] = true := by decide +kernel
theorem sub8_462 : sub8 [-2, -3, -2] = true := by decide +kernel
theorem sub8_463 : sub8 [-2, -3, -1] = true := by decide +kernel
theorem sub8_464 : sub8 [-2, -3, 0] = true := by decide +kernel
theorem sub8_465 : sub8 [-2, -3, 1] = true := by decide +kernel
theorem sub8_466 : sub8 [-2, -3, 2] = true := by decide +kernel
theorem sub8_467 : sub8 [-2, -3, 3] = true := by decide +kernel
theorem sub8_468 : sub8 [-2, -3, 4] = true := by decide +kernel
theorem sub8_469 : sub8 [-2, -3, 5] = true := by decide +kernel
theorem sub8_470 : sub8 [-2, -3, 6] = true := by decide +kernel
theorem sub8_471 : sub8 [-2, -2, -8] = true := by decide +kernel
theorem sub8_472 : sub8 [-2, -2, -7] = true := by decide +kernel
theorem sub8_473 : sub8 [-2, -2, -6] = true := by decide +kernel
theorem sub8_474 : sub8 [-2, -2, -5] = true := by decide +kernel
theorem sub8_475 : sub8 [-2, -2, -4] = true := by decide +kernel
theorem sub8_476 : sub8 [-2, -2, -3] = true := by decide +kernel
theorem sub8_477 : sub8 [-2, -2, -2] = true := by decide +kernel
theorem sub8_478 : sub8 [-2, -2, -1] = true := by decide +kernel
theorem sub8_479 : sub8 [-2, -2, 0] = true := by decide +kernel
theorem sb8_14 : ∀ q ∈ blk8_14, sub8 q = true := by
  unfold blk8_14
  exact List.forall_mem_cons.2 ⟨sub8_448, List.forall_mem_cons.2 ⟨sub8_449, List.forall_mem_cons.2 ⟨sub8_450, List.forall_mem_cons.2 ⟨sub8_451, List.forall_mem_cons.2 ⟨sub8_452, List.forall_mem_cons.2 ⟨sub8_453, List.forall_mem_cons.2 ⟨sub8_454, List.forall_mem_cons.2 ⟨sub8_455, List.forall_mem_cons.2 ⟨sub8_456, List.forall_mem_cons.2 ⟨sub8_457, List.forall_mem_cons.2 ⟨sub8_458, List.forall_mem_cons.2 ⟨sub8_459, List.forall_mem_cons.2 ⟨sub8_460, List.forall_mem_cons.2 ⟨sub8_461, List.forall_mem_cons.2 ⟨sub8_462, List.forall_mem_cons.2 ⟨sub8_463, List.forall_mem_cons.2 ⟨sub8_464, List.forall_mem_cons.2 ⟨sub8_465, List.forall_mem_cons.2 ⟨sub8_466, List.forall_mem_cons.2 ⟨sub8_467, List.forall_mem_cons.2 ⟨sub8_468, List.forall_mem_cons.2 ⟨sub8_469, List.forall_mem_cons.2 ⟨sub8_470, List.forall_mem_cons.2 ⟨sub8_471, List.forall_mem_cons.2 ⟨sub8_472, List.forall_mem_cons.2 ⟨sub8_473, List.forall_mem_cons.2 ⟨sub8_474, List.forall_mem_cons.2 ⟨sub8_475, List.forall_mem_cons.2 ⟨sub8_476, List.forall_mem_cons.2 ⟨sub8_477, List.forall_mem_cons.2 ⟨sub8_478, List.forall_mem_cons.2 ⟨sub8_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_480 : sub8 [-2, -2, 1] = true := by decide +kernel
theorem sub8_481 : sub8 [-2, -2, 2] = true := by decide +kernel
theorem sub8_482 : sub8 [-2, -2, 3] = true := by decide +kernel
theorem sub8_483 : sub8 [-2, -2, 4] = true := by decide +kernel
theorem sub8_484 : sub8 [-2, -2, 5] = true := by decide +kernel
theorem sub8_485 : sub8 [-2, -2, 6] = true := by decide +kernel
theorem sub8_486 : sub8 [-2, -2, 7] = true := by decide +kernel
theorem sub8_487 : sub8 [-2, -1, -9] = true := by decide +kernel
theorem sub8_488 : sub8 [-2, -1, -8] = true := by decide +kernel
theorem sub8_489 : sub8 [-2, -1, -7] = true := by decide +kernel
theorem sub8_490 : sub8 [-2, -1, -6] = true := by decide +kernel
theorem sub8_491 : sub8 [-2, -1, -5] = true := by decide +kernel
theorem sub8_492 : sub8 [-2, -1, -4] = true := by decide +kernel
theorem sub8_493 : sub8 [-2, -1, -3] = true := by decide +kernel
theorem sub8_494 : sub8 [-2, -1, -2] = true := by decide +kernel
theorem sub8_495 : sub8 [-2, -1, -1] = true := by decide +kernel
theorem sub8_496 : sub8 [-2, -1, 0] = true := by decide +kernel
theorem sub8_497 : sub8 [-2, -1, 1] = true := by decide +kernel
theorem sub8_498 : sub8 [-2, -1, 2] = true := by decide +kernel
theorem sub8_499 : sub8 [-2, -1, 3] = true := by decide +kernel
theorem sub8_500 : sub8 [-2, -1, 4] = true := by decide +kernel
theorem sub8_501 : sub8 [-2, -1, 5] = true := by decide +kernel
theorem sub8_502 : sub8 [-2, -1, 6] = true := by decide +kernel
theorem sub8_503 : sub8 [-2, -1, 7] = true := by decide +kernel
theorem sub8_504 : sub8 [-2, -1, 8] = true := by decide +kernel
theorem sub8_505 : sub8 [-2, 0, -9] = true := by decide +kernel
theorem sub8_506 : sub8 [-2, 0, -8] = true := by decide +kernel
theorem sub8_507 : sub8 [-2, 0, -7] = true := by decide +kernel
theorem sub8_508 : sub8 [-2, 0, -6] = true := by decide +kernel
theorem sub8_509 : sub8 [-2, 0, -5] = true := by decide +kernel
theorem sub8_510 : sub8 [-2, 0, -4] = true := by decide +kernel
theorem sub8_511 : sub8 [-2, 0, -3] = true := by decide +kernel
theorem sb8_15 : ∀ q ∈ blk8_15, sub8 q = true := by
  unfold blk8_15
  exact List.forall_mem_cons.2 ⟨sub8_480, List.forall_mem_cons.2 ⟨sub8_481, List.forall_mem_cons.2 ⟨sub8_482, List.forall_mem_cons.2 ⟨sub8_483, List.forall_mem_cons.2 ⟨sub8_484, List.forall_mem_cons.2 ⟨sub8_485, List.forall_mem_cons.2 ⟨sub8_486, List.forall_mem_cons.2 ⟨sub8_487, List.forall_mem_cons.2 ⟨sub8_488, List.forall_mem_cons.2 ⟨sub8_489, List.forall_mem_cons.2 ⟨sub8_490, List.forall_mem_cons.2 ⟨sub8_491, List.forall_mem_cons.2 ⟨sub8_492, List.forall_mem_cons.2 ⟨sub8_493, List.forall_mem_cons.2 ⟨sub8_494, List.forall_mem_cons.2 ⟨sub8_495, List.forall_mem_cons.2 ⟨sub8_496, List.forall_mem_cons.2 ⟨sub8_497, List.forall_mem_cons.2 ⟨sub8_498, List.forall_mem_cons.2 ⟨sub8_499, List.forall_mem_cons.2 ⟨sub8_500, List.forall_mem_cons.2 ⟨sub8_501, List.forall_mem_cons.2 ⟨sub8_502, List.forall_mem_cons.2 ⟨sub8_503, List.forall_mem_cons.2 ⟨sub8_504, List.forall_mem_cons.2 ⟨sub8_505, List.forall_mem_cons.2 ⟨sub8_506, List.forall_mem_cons.2 ⟨sub8_507, List.forall_mem_cons.2 ⟨sub8_508, List.forall_mem_cons.2 ⟨sub8_509, List.forall_mem_cons.2 ⟨sub8_510, List.forall_mem_cons.2 ⟨sub8_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_512 : sub8 [-2, 0, -2] = true := by decide +kernel
theorem sub8_513 : sub8 [-2, 0, -1] = true := by decide +kernel
theorem sub8_514 : sub8 [-2, 0, 0] = true := by decide +kernel
theorem sub8_515 : sub8 [-2, 0, 1] = true := by decide +kernel
theorem sub8_516 : sub8 [-2, 0, 2] = true := by decide +kernel
theorem sub8_517 : sub8 [-2, 0, 3] = true := by decide +kernel
theorem sub8_518 : sub8 [-2, 0, 4] = true := by decide +kernel
theorem sub8_519 : sub8 [-2, 0, 5] = true := by decide +kernel
theorem sub8_520 : sub8 [-2, 0, 6] = true := by decide +kernel
theorem sub8_521 : sub8 [-2, 0, 7] = true := by decide +kernel
theorem sub8_522 : sub8 [-2, 0, 8] = true := by decide +kernel
theorem sub8_523 : sub8 [-2, 1, -9] = true := by decide +kernel
theorem sub8_524 : sub8 [-2, 1, -8] = true := by decide +kernel
theorem sub8_525 : sub8 [-2, 1, -7] = true := by decide +kernel
theorem sub8_526 : sub8 [-2, 1, -6] = true := by decide +kernel
theorem sub8_527 : sub8 [-2, 1, -5] = true := by decide +kernel
theorem sub8_528 : sub8 [-2, 1, -4] = true := by decide +kernel
theorem sub8_529 : sub8 [-2, 1, -3] = true := by decide +kernel
theorem sub8_530 : sub8 [-2, 1, -2] = true := by decide +kernel
theorem sub8_531 : sub8 [-2, 1, -1] = true := by decide +kernel
theorem sub8_532 : sub8 [-2, 1, 0] = true := by decide +kernel
theorem sub8_533 : sub8 [-2, 1, 1] = true := by decide +kernel
theorem sub8_534 : sub8 [-2, 1, 2] = true := by decide +kernel
theorem sub8_535 : sub8 [-2, 1, 3] = true := by decide +kernel
theorem sub8_536 : sub8 [-2, 1, 4] = true := by decide +kernel
theorem sub8_537 : sub8 [-2, 1, 5] = true := by decide +kernel
theorem sub8_538 : sub8 [-2, 1, 6] = true := by decide +kernel
theorem sub8_539 : sub8 [-2, 1, 7] = true := by decide +kernel
theorem sub8_540 : sub8 [-2, 1, 8] = true := by decide +kernel
theorem sub8_541 : sub8 [-2, 2, -8] = true := by decide +kernel
theorem sub8_542 : sub8 [-2, 2, -7] = true := by decide +kernel
theorem sub8_543 : sub8 [-2, 2, -6] = true := by decide +kernel
theorem sb8_16 : ∀ q ∈ blk8_16, sub8 q = true := by
  unfold blk8_16
  exact List.forall_mem_cons.2 ⟨sub8_512, List.forall_mem_cons.2 ⟨sub8_513, List.forall_mem_cons.2 ⟨sub8_514, List.forall_mem_cons.2 ⟨sub8_515, List.forall_mem_cons.2 ⟨sub8_516, List.forall_mem_cons.2 ⟨sub8_517, List.forall_mem_cons.2 ⟨sub8_518, List.forall_mem_cons.2 ⟨sub8_519, List.forall_mem_cons.2 ⟨sub8_520, List.forall_mem_cons.2 ⟨sub8_521, List.forall_mem_cons.2 ⟨sub8_522, List.forall_mem_cons.2 ⟨sub8_523, List.forall_mem_cons.2 ⟨sub8_524, List.forall_mem_cons.2 ⟨sub8_525, List.forall_mem_cons.2 ⟨sub8_526, List.forall_mem_cons.2 ⟨sub8_527, List.forall_mem_cons.2 ⟨sub8_528, List.forall_mem_cons.2 ⟨sub8_529, List.forall_mem_cons.2 ⟨sub8_530, List.forall_mem_cons.2 ⟨sub8_531, List.forall_mem_cons.2 ⟨sub8_532, List.forall_mem_cons.2 ⟨sub8_533, List.forall_mem_cons.2 ⟨sub8_534, List.forall_mem_cons.2 ⟨sub8_535, List.forall_mem_cons.2 ⟨sub8_536, List.forall_mem_cons.2 ⟨sub8_537, List.forall_mem_cons.2 ⟨sub8_538, List.forall_mem_cons.2 ⟨sub8_539, List.forall_mem_cons.2 ⟨sub8_540, List.forall_mem_cons.2 ⟨sub8_541, List.forall_mem_cons.2 ⟨sub8_542, List.forall_mem_cons.2 ⟨sub8_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_544 : sub8 [-2, 2, -5] = true := by decide +kernel
theorem sub8_545 : sub8 [-2, 2, -4] = true := by decide +kernel
theorem sub8_546 : sub8 [-2, 2, -3] = true := by decide +kernel
theorem sub8_547 : sub8 [-2, 2, -2] = true := by decide +kernel
theorem sub8_548 : sub8 [-2, 2, -1] = true := by decide +kernel
theorem sub8_549 : sub8 [-2, 2, 0] = true := by decide +kernel
theorem sub8_550 : sub8 [-2, 2, 1] = true := by decide +kernel
theorem sub8_551 : sub8 [-2, 2, 2] = true := by decide +kernel
theorem sub8_552 : sub8 [-2, 2, 3] = true := by decide +kernel
theorem sub8_553 : sub8 [-2, 2, 4] = true := by decide +kernel
theorem sub8_554 : sub8 [-2, 2, 5] = true := by decide +kernel
theorem sub8_555 : sub8 [-2, 2, 6] = true := by decide +kernel
theorem sub8_556 : sub8 [-2, 2, 7] = true := by decide +kernel
theorem sub8_557 : sub8 [-2, 2, 8] = true := by decide +kernel
theorem sub8_558 : sub8 [-2, 3, -8] = true := by decide +kernel
theorem sub8_559 : sub8 [-2, 3, -7] = true := by decide +kernel
theorem sub8_560 : sub8 [-2, 3, -6] = true := by decide +kernel
theorem sub8_561 : sub8 [-2, 3, -5] = true := by decide +kernel
theorem sub8_562 : sub8 [-2, 3, -4] = true := by decide +kernel
theorem sub8_563 : sub8 [-2, 3, -3] = true := by decide +kernel
theorem sub8_564 : sub8 [-2, 3, -2] = true := by decide +kernel
theorem sub8_565 : sub8 [-2, 3, -1] = true := by decide +kernel
theorem sub8_566 : sub8 [-2, 3, 0] = true := by decide +kernel
theorem sub8_567 : sub8 [-2, 3, 1] = true := by decide +kernel
theorem sub8_568 : sub8 [-2, 3, 2] = true := by decide +kernel
theorem sub8_569 : sub8 [-2, 3, 3] = true := by decide +kernel
theorem sub8_570 : sub8 [-2, 3, 4] = true := by decide +kernel
theorem sub8_571 : sub8 [-2, 3, 5] = true := by decide +kernel
theorem sub8_572 : sub8 [-2, 3, 6] = true := by decide +kernel
theorem sub8_573 : sub8 [-2, 3, 7] = true := by decide +kernel
theorem sub8_574 : sub8 [-2, 3, 8] = true := by decide +kernel
theorem sub8_575 : sub8 [-2, 4, -7] = true := by decide +kernel
theorem sb8_17 : ∀ q ∈ blk8_17, sub8 q = true := by
  unfold blk8_17
  exact List.forall_mem_cons.2 ⟨sub8_544, List.forall_mem_cons.2 ⟨sub8_545, List.forall_mem_cons.2 ⟨sub8_546, List.forall_mem_cons.2 ⟨sub8_547, List.forall_mem_cons.2 ⟨sub8_548, List.forall_mem_cons.2 ⟨sub8_549, List.forall_mem_cons.2 ⟨sub8_550, List.forall_mem_cons.2 ⟨sub8_551, List.forall_mem_cons.2 ⟨sub8_552, List.forall_mem_cons.2 ⟨sub8_553, List.forall_mem_cons.2 ⟨sub8_554, List.forall_mem_cons.2 ⟨sub8_555, List.forall_mem_cons.2 ⟨sub8_556, List.forall_mem_cons.2 ⟨sub8_557, List.forall_mem_cons.2 ⟨sub8_558, List.forall_mem_cons.2 ⟨sub8_559, List.forall_mem_cons.2 ⟨sub8_560, List.forall_mem_cons.2 ⟨sub8_561, List.forall_mem_cons.2 ⟨sub8_562, List.forall_mem_cons.2 ⟨sub8_563, List.forall_mem_cons.2 ⟨sub8_564, List.forall_mem_cons.2 ⟨sub8_565, List.forall_mem_cons.2 ⟨sub8_566, List.forall_mem_cons.2 ⟨sub8_567, List.forall_mem_cons.2 ⟨sub8_568, List.forall_mem_cons.2 ⟨sub8_569, List.forall_mem_cons.2 ⟨sub8_570, List.forall_mem_cons.2 ⟨sub8_571, List.forall_mem_cons.2 ⟨sub8_572, List.forall_mem_cons.2 ⟨sub8_573, List.forall_mem_cons.2 ⟨sub8_574, List.forall_mem_cons.2 ⟨sub8_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_576 : sub8 [-2, 4, -6] = true := by decide +kernel
theorem sub8_577 : sub8 [-2, 4, -5] = true := by decide +kernel
theorem sub8_578 : sub8 [-2, 4, -4] = true := by decide +kernel
theorem sub8_579 : sub8 [-2, 4, -3] = true := by decide +kernel
theorem sub8_580 : sub8 [-2, 4, -2] = true := by decide +kernel
theorem sub8_581 : sub8 [-2, 4, -1] = true := by decide +kernel
theorem sub8_582 : sub8 [-2, 4, 0] = true := by decide +kernel
theorem sub8_583 : sub8 [-2, 4, 1] = true := by decide +kernel
theorem sub8_584 : sub8 [-2, 4, 2] = true := by decide +kernel
theorem sub8_585 : sub8 [-2, 4, 3] = true := by decide +kernel
theorem sub8_586 : sub8 [-2, 4, 4] = true := by decide +kernel
theorem sub8_587 : sub8 [-2, 4, 5] = true := by decide +kernel
theorem sub8_588 : sub8 [-2, 4, 6] = true := by decide +kernel
theorem sub8_589 : sub8 [-2, 4, 7] = true := by decide +kernel
theorem sub8_590 : sub8 [-2, 4, 8] = true := by decide +kernel
theorem sub8_591 : sub8 [-2, 5, -6] = true := by decide +kernel
theorem sub8_592 : sub8 [-2, 5, -5] = true := by decide +kernel
theorem sub8_593 : sub8 [-2, 5, -4] = true := by decide +kernel
theorem sub8_594 : sub8 [-2, 5, -3] = true := by decide +kernel
theorem sub8_595 : sub8 [-2, 5, -2] = true := by decide +kernel
theorem sub8_596 : sub8 [-2, 5, -1] = true := by decide +kernel
theorem sub8_597 : sub8 [-2, 5, 0] = true := by decide +kernel
theorem sub8_598 : sub8 [-2, 5, 1] = true := by decide +kernel
theorem sub8_599 : sub8 [-2, 5, 2] = true := by decide +kernel
theorem sub8_600 : sub8 [-2, 5, 3] = true := by decide +kernel
theorem sub8_601 : sub8 [-2, 5, 4] = true := by decide +kernel
theorem sub8_602 : sub8 [-2, 5, 5] = true := by decide +kernel
theorem sub8_603 : sub8 [-2, 5, 6] = true := by decide +kernel
theorem sub8_604 : sub8 [-2, 5, 7] = true := by decide +kernel
theorem sub8_605 : sub8 [-2, 6] = true := by decide +kernel
theorem sub8_606 : sub8 [-2, 7] = true := by decide +kernel
theorem sub8_607 : sub8 [-1, -7] = true := by decide +kernel
theorem sb8_18 : ∀ q ∈ blk8_18, sub8 q = true := by
  unfold blk8_18
  exact List.forall_mem_cons.2 ⟨sub8_576, List.forall_mem_cons.2 ⟨sub8_577, List.forall_mem_cons.2 ⟨sub8_578, List.forall_mem_cons.2 ⟨sub8_579, List.forall_mem_cons.2 ⟨sub8_580, List.forall_mem_cons.2 ⟨sub8_581, List.forall_mem_cons.2 ⟨sub8_582, List.forall_mem_cons.2 ⟨sub8_583, List.forall_mem_cons.2 ⟨sub8_584, List.forall_mem_cons.2 ⟨sub8_585, List.forall_mem_cons.2 ⟨sub8_586, List.forall_mem_cons.2 ⟨sub8_587, List.forall_mem_cons.2 ⟨sub8_588, List.forall_mem_cons.2 ⟨sub8_589, List.forall_mem_cons.2 ⟨sub8_590, List.forall_mem_cons.2 ⟨sub8_591, List.forall_mem_cons.2 ⟨sub8_592, List.forall_mem_cons.2 ⟨sub8_593, List.forall_mem_cons.2 ⟨sub8_594, List.forall_mem_cons.2 ⟨sub8_595, List.forall_mem_cons.2 ⟨sub8_596, List.forall_mem_cons.2 ⟨sub8_597, List.forall_mem_cons.2 ⟨sub8_598, List.forall_mem_cons.2 ⟨sub8_599, List.forall_mem_cons.2 ⟨sub8_600, List.forall_mem_cons.2 ⟨sub8_601, List.forall_mem_cons.2 ⟨sub8_602, List.forall_mem_cons.2 ⟨sub8_603, List.forall_mem_cons.2 ⟨sub8_604, List.forall_mem_cons.2 ⟨sub8_605, List.forall_mem_cons.2 ⟨sub8_606, List.forall_mem_cons.2 ⟨sub8_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_608 : sub8 [-1, -6] = true := by decide +kernel
theorem sub8_609 : sub8 [-1, -5] = true := by decide +kernel
theorem sub8_610 : sub8 [-1, -4, -8] = true := by decide +kernel
theorem sub8_611 : sub8 [-1, -4, -7] = true := by decide +kernel
theorem sub8_612 : sub8 [-1, -4, -6] = true := by decide +kernel
theorem sub8_613 : sub8 [-1, -4, -5] = true := by decide +kernel
theorem sub8_614 : sub8 [-1, -4, -4] = true := by decide +kernel
theorem sub8_615 : sub8 [-1, -4, -3] = true := by decide +kernel
theorem sub8_616 : sub8 [-1, -4, -2] = true := by decide +kernel
theorem sub8_617 : sub8 [-1, -4, -1] = true := by decide +kernel
theorem sub8_618 : sub8 [-1, -4, 0] = true := by decide +kernel
theorem sub8_619 : sub8 [-1, -4, 1] = true := by decide +kernel
theorem sub8_620 : sub8 [-1, -4, 2] = true := by decide +kernel
theorem sub8_621 : sub8 [-1, -4, 3] = true := by decide +kernel
theorem sub8_622 : sub8 [-1, -4, 4] = true := by decide +kernel
theorem sub8_623 : sub8 [-1, -4, 5] = true := by decide +kernel
theorem sub8_624 : sub8 [-1, -4, 6] = true := by decide +kernel
theorem sub8_625 : sub8 [-1, -3, -8] = true := by decide +kernel
theorem sub8_626 : sub8 [-1, -3, -7] = true := by decide +kernel
theorem sub8_627 : sub8 [-1, -3, -6] = true := by decide +kernel
theorem sub8_628 : sub8 [-1, -3, -5] = true := by decide +kernel
theorem sub8_629 : sub8 [-1, -3, -4] = true := by decide +kernel
theorem sub8_630 : sub8 [-1, -3, -3] = true := by decide +kernel
theorem sub8_631 : sub8 [-1, -3, -2] = true := by decide +kernel
theorem sub8_632 : sub8 [-1, -3, -1] = true := by decide +kernel
theorem sub8_633 : sub8 [-1, -3, 0] = true := by decide +kernel
theorem sub8_634 : sub8 [-1, -3, 1] = true := by decide +kernel
theorem sub8_635 : sub8 [-1, -3, 2] = true := by decide +kernel
theorem sub8_636 : sub8 [-1, -3, 3] = true := by decide +kernel
theorem sub8_637 : sub8 [-1, -3, 4] = true := by decide +kernel
theorem sub8_638 : sub8 [-1, -3, 5] = true := by decide +kernel
theorem sub8_639 : sub8 [-1, -3, 6] = true := by decide +kernel
theorem sb8_19 : ∀ q ∈ blk8_19, sub8 q = true := by
  unfold blk8_19
  exact List.forall_mem_cons.2 ⟨sub8_608, List.forall_mem_cons.2 ⟨sub8_609, List.forall_mem_cons.2 ⟨sub8_610, List.forall_mem_cons.2 ⟨sub8_611, List.forall_mem_cons.2 ⟨sub8_612, List.forall_mem_cons.2 ⟨sub8_613, List.forall_mem_cons.2 ⟨sub8_614, List.forall_mem_cons.2 ⟨sub8_615, List.forall_mem_cons.2 ⟨sub8_616, List.forall_mem_cons.2 ⟨sub8_617, List.forall_mem_cons.2 ⟨sub8_618, List.forall_mem_cons.2 ⟨sub8_619, List.forall_mem_cons.2 ⟨sub8_620, List.forall_mem_cons.2 ⟨sub8_621, List.forall_mem_cons.2 ⟨sub8_622, List.forall_mem_cons.2 ⟨sub8_623, List.forall_mem_cons.2 ⟨sub8_624, List.forall_mem_cons.2 ⟨sub8_625, List.forall_mem_cons.2 ⟨sub8_626, List.forall_mem_cons.2 ⟨sub8_627, List.forall_mem_cons.2 ⟨sub8_628, List.forall_mem_cons.2 ⟨sub8_629, List.forall_mem_cons.2 ⟨sub8_630, List.forall_mem_cons.2 ⟨sub8_631, List.forall_mem_cons.2 ⟨sub8_632, List.forall_mem_cons.2 ⟨sub8_633, List.forall_mem_cons.2 ⟨sub8_634, List.forall_mem_cons.2 ⟨sub8_635, List.forall_mem_cons.2 ⟨sub8_636, List.forall_mem_cons.2 ⟨sub8_637, List.forall_mem_cons.2 ⟨sub8_638, List.forall_mem_cons.2 ⟨sub8_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_640 : sub8 [-1, -3, 7] = true := by decide +kernel
theorem sub8_641 : sub8 [-1, -2, -9] = true := by decide +kernel
theorem sub8_642 : sub8 [-1, -2, -8] = true := by decide +kernel
theorem sub8_643 : sub8 [-1, -2, -7] = true := by decide +kernel
theorem sub8_644 : sub8 [-1, -2, -6] = true := by decide +kernel
theorem sub8_645 : sub8 [-1, -2, -5] = true := by decide +kernel
theorem sub8_646 : sub8 [-1, -2, -4] = true := by decide +kernel
theorem sub8_647 : sub8 [-1, -2, -3] = true := by decide +kernel
theorem sub8_648 : sub8 [-1, -2, -2] = true := by decide +kernel
theorem sub8_649 : sub8 [-1, -2, -1] = true := by decide +kernel
theorem sub8_650 : sub8 [-1, -2, 0] = true := by decide +kernel
theorem sub8_651 : sub8 [-1, -2, 1] = true := by decide +kernel
theorem sub8_652 : sub8 [-1, -2, 2] = true := by decide +kernel
theorem sub8_653 : sub8 [-1, -2, 3] = true := by decide +kernel
theorem sub8_654 : sub8 [-1, -2, 4] = true := by decide +kernel
theorem sub8_655 : sub8 [-1, -2, 5] = true := by decide +kernel
theorem sub8_656 : sub8 [-1, -2, 6] = true := by decide +kernel
theorem sub8_657 : sub8 [-1, -2, 7] = true := by decide +kernel
theorem sub8_658 : sub8 [-1, -2, 8] = true := by decide +kernel
theorem sub8_659 : sub8 [-1, -1, -9] = true := by decide +kernel
theorem sub8_660 : sub8 [-1, -1, -8] = true := by decide +kernel
theorem sub8_661 : sub8 [-1, -1, -7] = true := by decide +kernel
theorem sub8_662 : sub8 [-1, -1, -6] = true := by decide +kernel
theorem sub8_663 : sub8 [-1, -1, -5] = true := by decide +kernel
theorem sub8_664 : sub8 [-1, -1, -4] = true := by decide +kernel
theorem sub8_665 : sub8 [-1, -1, -3] = true := by decide +kernel
theorem sub8_666 : sub8 [-1, -1, -2] = true := by decide +kernel
theorem sub8_667 : sub8 [-1, -1, -1] = true := by decide +kernel
theorem sub8_668 : sub8 [-1, -1, 0] = true := by decide +kernel
theorem sub8_669 : sub8 [-1, -1, 1] = true := by decide +kernel
theorem sub8_670 : sub8 [-1, -1, 2] = true := by decide +kernel
theorem sub8_671 : sub8 [-1, -1, 3] = true := by decide +kernel
theorem sb8_20 : ∀ q ∈ blk8_20, sub8 q = true := by
  unfold blk8_20
  exact List.forall_mem_cons.2 ⟨sub8_640, List.forall_mem_cons.2 ⟨sub8_641, List.forall_mem_cons.2 ⟨sub8_642, List.forall_mem_cons.2 ⟨sub8_643, List.forall_mem_cons.2 ⟨sub8_644, List.forall_mem_cons.2 ⟨sub8_645, List.forall_mem_cons.2 ⟨sub8_646, List.forall_mem_cons.2 ⟨sub8_647, List.forall_mem_cons.2 ⟨sub8_648, List.forall_mem_cons.2 ⟨sub8_649, List.forall_mem_cons.2 ⟨sub8_650, List.forall_mem_cons.2 ⟨sub8_651, List.forall_mem_cons.2 ⟨sub8_652, List.forall_mem_cons.2 ⟨sub8_653, List.forall_mem_cons.2 ⟨sub8_654, List.forall_mem_cons.2 ⟨sub8_655, List.forall_mem_cons.2 ⟨sub8_656, List.forall_mem_cons.2 ⟨sub8_657, List.forall_mem_cons.2 ⟨sub8_658, List.forall_mem_cons.2 ⟨sub8_659, List.forall_mem_cons.2 ⟨sub8_660, List.forall_mem_cons.2 ⟨sub8_661, List.forall_mem_cons.2 ⟨sub8_662, List.forall_mem_cons.2 ⟨sub8_663, List.forall_mem_cons.2 ⟨sub8_664, List.forall_mem_cons.2 ⟨sub8_665, List.forall_mem_cons.2 ⟨sub8_666, List.forall_mem_cons.2 ⟨sub8_667, List.forall_mem_cons.2 ⟨sub8_668, List.forall_mem_cons.2 ⟨sub8_669, List.forall_mem_cons.2 ⟨sub8_670, List.forall_mem_cons.2 ⟨sub8_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_672 : sub8 [-1, -1, 4] = true := by decide +kernel
theorem sub8_673 : sub8 [-1, -1, 5] = true := by decide +kernel
theorem sub8_674 : sub8 [-1, -1, 6] = true := by decide +kernel
theorem sub8_675 : sub8 [-1, -1, 7] = true := by decide +kernel
theorem sub8_676 : sub8 [-1, -1, 8] = true := by decide +kernel
theorem sub8_677 : sub8 [-1, 0, -9] = true := by decide +kernel
theorem sub8_678 : sub8 [-1, 0, -8] = true := by decide +kernel
theorem sub8_679 : sub8 [-1, 0, -7] = true := by decide +kernel
theorem sub8_680 : sub8 [-1, 0, -6] = true := by decide +kernel
theorem sub8_681 : sub8 [-1, 0, -5] = true := by decide +kernel
theorem sub8_682 : sub8 [-1, 0, -4] = true := by decide +kernel
theorem sub8_683 : sub8 [-1, 0, -3] = true := by decide +kernel
theorem sub8_684 : sub8 [-1, 0, -2] = true := by decide +kernel
theorem sub8_685 : sub8 [-1, 0, -1] = true := by decide +kernel
theorem sub8_686 : sub8 [-1, 0, 0] = true := by decide +kernel
theorem sub8_687 : sub8 [-1, 0, 1] = true := by decide +kernel
theorem sub8_688 : sub8 [-1, 0, 2] = true := by decide +kernel
theorem sub8_689 : sub8 [-1, 0, 3] = true := by decide +kernel
theorem sub8_690 : sub8 [-1, 0, 4] = true := by decide +kernel
theorem sub8_691 : sub8 [-1, 0, 5] = true := by decide +kernel
theorem sub8_692 : sub8 [-1, 0, 6] = true := by decide +kernel
theorem sub8_693 : sub8 [-1, 0, 7] = true := by decide +kernel
theorem sub8_694 : sub8 [-1, 0, 8] = true := by decide +kernel
theorem sub8_695 : sub8 [-1, 1, -9] = true := by decide +kernel
theorem sub8_696 : sub8 [-1, 1, -8] = true := by decide +kernel
theorem sub8_697 : sub8 [-1, 1, -7] = true := by decide +kernel
theorem sub8_698 : sub8 [-1, 1, -6] = true := by decide +kernel
theorem sub8_699 : sub8 [-1, 1, -5] = true := by decide +kernel
theorem sub8_700 : sub8 [-1, 1, -4] = true := by decide +kernel
theorem sub8_701 : sub8 [-1, 1, -3] = true := by decide +kernel
theorem sub8_702 : sub8 [-1, 1, -2] = true := by decide +kernel
theorem sub8_703 : sub8 [-1, 1, -1] = true := by decide +kernel
theorem sb8_21 : ∀ q ∈ blk8_21, sub8 q = true := by
  unfold blk8_21
  exact List.forall_mem_cons.2 ⟨sub8_672, List.forall_mem_cons.2 ⟨sub8_673, List.forall_mem_cons.2 ⟨sub8_674, List.forall_mem_cons.2 ⟨sub8_675, List.forall_mem_cons.2 ⟨sub8_676, List.forall_mem_cons.2 ⟨sub8_677, List.forall_mem_cons.2 ⟨sub8_678, List.forall_mem_cons.2 ⟨sub8_679, List.forall_mem_cons.2 ⟨sub8_680, List.forall_mem_cons.2 ⟨sub8_681, List.forall_mem_cons.2 ⟨sub8_682, List.forall_mem_cons.2 ⟨sub8_683, List.forall_mem_cons.2 ⟨sub8_684, List.forall_mem_cons.2 ⟨sub8_685, List.forall_mem_cons.2 ⟨sub8_686, List.forall_mem_cons.2 ⟨sub8_687, List.forall_mem_cons.2 ⟨sub8_688, List.forall_mem_cons.2 ⟨sub8_689, List.forall_mem_cons.2 ⟨sub8_690, List.forall_mem_cons.2 ⟨sub8_691, List.forall_mem_cons.2 ⟨sub8_692, List.forall_mem_cons.2 ⟨sub8_693, List.forall_mem_cons.2 ⟨sub8_694, List.forall_mem_cons.2 ⟨sub8_695, List.forall_mem_cons.2 ⟨sub8_696, List.forall_mem_cons.2 ⟨sub8_697, List.forall_mem_cons.2 ⟨sub8_698, List.forall_mem_cons.2 ⟨sub8_699, List.forall_mem_cons.2 ⟨sub8_700, List.forall_mem_cons.2 ⟨sub8_701, List.forall_mem_cons.2 ⟨sub8_702, List.forall_mem_cons.2 ⟨sub8_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_704 : sub8 [-1, 1, 0] = true := by decide +kernel
theorem sub8_705 : sub8 [-1, 1, 1] = true := by decide +kernel
theorem sub8_706 : sub8 [-1, 1, 2] = true := by decide +kernel
theorem sub8_707 : sub8 [-1, 1, 3] = true := by decide +kernel
theorem sub8_708 : sub8 [-1, 1, 4] = true := by decide +kernel
theorem sub8_709 : sub8 [-1, 1, 5] = true := by decide +kernel
theorem sub8_710 : sub8 [-1, 1, 6] = true := by decide +kernel
theorem sub8_711 : sub8 [-1, 1, 7] = true := by decide +kernel
theorem sub8_712 : sub8 [-1, 1, 8] = true := by decide +kernel
theorem sub8_713 : sub8 [-1, 2, -9] = true := by decide +kernel
theorem sub8_714 : sub8 [-1, 2, -8] = true := by decide +kernel
theorem sub8_715 : sub8 [-1, 2, -7] = true := by decide +kernel
theorem sub8_716 : sub8 [-1, 2, -6] = true := by decide +kernel
theorem sub8_717 : sub8 [-1, 2, -5] = true := by decide +kernel
theorem sub8_718 : sub8 [-1, 2, -4] = true := by decide +kernel
theorem sub8_719 : sub8 [-1, 2, -3] = true := by decide +kernel
theorem sub8_720 : sub8 [-1, 2, -2] = true := by decide +kernel
theorem sub8_721 : sub8 [-1, 2, -1] = true := by decide +kernel
theorem sub8_722 : sub8 [-1, 2, 0] = true := by decide +kernel
theorem sub8_723 : sub8 [-1, 2, 1] = true := by decide +kernel
theorem sub8_724 : sub8 [-1, 2, 2] = true := by decide +kernel
theorem sub8_725 : sub8 [-1, 2, 3] = true := by decide +kernel
theorem sub8_726 : sub8 [-1, 2, 4] = true := by decide +kernel
theorem sub8_727 : sub8 [-1, 2, 5] = true := by decide +kernel
theorem sub8_728 : sub8 [-1, 2, 6] = true := by decide +kernel
theorem sub8_729 : sub8 [-1, 2, 7] = true := by decide +kernel
theorem sub8_730 : sub8 [-1, 2, 8] = true := by decide +kernel
theorem sub8_731 : sub8 [-1, 3, -8] = true := by decide +kernel
theorem sub8_732 : sub8 [-1, 3, -7] = true := by decide +kernel
theorem sub8_733 : sub8 [-1, 3, -6] = true := by decide +kernel
theorem sub8_734 : sub8 [-1, 3, -5] = true := by decide +kernel
theorem sub8_735 : sub8 [-1, 3, -4] = true := by decide +kernel
theorem sb8_22 : ∀ q ∈ blk8_22, sub8 q = true := by
  unfold blk8_22
  exact List.forall_mem_cons.2 ⟨sub8_704, List.forall_mem_cons.2 ⟨sub8_705, List.forall_mem_cons.2 ⟨sub8_706, List.forall_mem_cons.2 ⟨sub8_707, List.forall_mem_cons.2 ⟨sub8_708, List.forall_mem_cons.2 ⟨sub8_709, List.forall_mem_cons.2 ⟨sub8_710, List.forall_mem_cons.2 ⟨sub8_711, List.forall_mem_cons.2 ⟨sub8_712, List.forall_mem_cons.2 ⟨sub8_713, List.forall_mem_cons.2 ⟨sub8_714, List.forall_mem_cons.2 ⟨sub8_715, List.forall_mem_cons.2 ⟨sub8_716, List.forall_mem_cons.2 ⟨sub8_717, List.forall_mem_cons.2 ⟨sub8_718, List.forall_mem_cons.2 ⟨sub8_719, List.forall_mem_cons.2 ⟨sub8_720, List.forall_mem_cons.2 ⟨sub8_721, List.forall_mem_cons.2 ⟨sub8_722, List.forall_mem_cons.2 ⟨sub8_723, List.forall_mem_cons.2 ⟨sub8_724, List.forall_mem_cons.2 ⟨sub8_725, List.forall_mem_cons.2 ⟨sub8_726, List.forall_mem_cons.2 ⟨sub8_727, List.forall_mem_cons.2 ⟨sub8_728, List.forall_mem_cons.2 ⟨sub8_729, List.forall_mem_cons.2 ⟨sub8_730, List.forall_mem_cons.2 ⟨sub8_731, List.forall_mem_cons.2 ⟨sub8_732, List.forall_mem_cons.2 ⟨sub8_733, List.forall_mem_cons.2 ⟨sub8_734, List.forall_mem_cons.2 ⟨sub8_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_736 : sub8 [-1, 3, -3] = true := by decide +kernel
theorem sub8_737 : sub8 [-1, 3, -2] = true := by decide +kernel
theorem sub8_738 : sub8 [-1, 3, -1] = true := by decide +kernel
theorem sub8_739 : sub8 [-1, 3, 0] = true := by decide +kernel
theorem sub8_740 : sub8 [-1, 3, 1] = true := by decide +kernel
theorem sub8_741 : sub8 [-1, 3, 2] = true := by decide +kernel
theorem sub8_742 : sub8 [-1, 3, 3] = true := by decide +kernel
theorem sub8_743 : sub8 [-1, 3, 4] = true := by decide +kernel
theorem sub8_744 : sub8 [-1, 3, 5] = true := by decide +kernel
theorem sub8_745 : sub8 [-1, 3, 6] = true := by decide +kernel
theorem sub8_746 : sub8 [-1, 3, 7] = true := by decide +kernel
theorem sub8_747 : sub8 [-1, 3, 8] = true := by decide +kernel
theorem sub8_748 : sub8 [-1, 4, -7] = true := by decide +kernel
theorem sub8_749 : sub8 [-1, 4, -6] = true := by decide +kernel
theorem sub8_750 : sub8 [-1, 4, -5] = true := by decide +kernel
theorem sub8_751 : sub8 [-1, 4, -4] = true := by decide +kernel
theorem sub8_752 : sub8 [-1, 4, -3] = true := by decide +kernel
theorem sub8_753 : sub8 [-1, 4, -2] = true := by decide +kernel
theorem sub8_754 : sub8 [-1, 4, -1] = true := by decide +kernel
theorem sub8_755 : sub8 [-1, 4, 0] = true := by decide +kernel
theorem sub8_756 : sub8 [-1, 4, 1] = true := by decide +kernel
theorem sub8_757 : sub8 [-1, 4, 2] = true := by decide +kernel
theorem sub8_758 : sub8 [-1, 4, 3] = true := by decide +kernel
theorem sub8_759 : sub8 [-1, 4, 4] = true := by decide +kernel
theorem sub8_760 : sub8 [-1, 4, 5] = true := by decide +kernel
theorem sub8_761 : sub8 [-1, 4, 6] = true := by decide +kernel
theorem sub8_762 : sub8 [-1, 4, 7] = true := by decide +kernel
theorem sub8_763 : sub8 [-1, 4, 8] = true := by decide +kernel
theorem sub8_764 : sub8 [-1, 5, -6] = true := by decide +kernel
theorem sub8_765 : sub8 [-1, 5, -5] = true := by decide +kernel
theorem sub8_766 : sub8 [-1, 5, -4] = true := by decide +kernel
theorem sub8_767 : sub8 [-1, 5, -3] = true := by decide +kernel
theorem sb8_23 : ∀ q ∈ blk8_23, sub8 q = true := by
  unfold blk8_23
  exact List.forall_mem_cons.2 ⟨sub8_736, List.forall_mem_cons.2 ⟨sub8_737, List.forall_mem_cons.2 ⟨sub8_738, List.forall_mem_cons.2 ⟨sub8_739, List.forall_mem_cons.2 ⟨sub8_740, List.forall_mem_cons.2 ⟨sub8_741, List.forall_mem_cons.2 ⟨sub8_742, List.forall_mem_cons.2 ⟨sub8_743, List.forall_mem_cons.2 ⟨sub8_744, List.forall_mem_cons.2 ⟨sub8_745, List.forall_mem_cons.2 ⟨sub8_746, List.forall_mem_cons.2 ⟨sub8_747, List.forall_mem_cons.2 ⟨sub8_748, List.forall_mem_cons.2 ⟨sub8_749, List.forall_mem_cons.2 ⟨sub8_750, List.forall_mem_cons.2 ⟨sub8_751, List.forall_mem_cons.2 ⟨sub8_752, List.forall_mem_cons.2 ⟨sub8_753, List.forall_mem_cons.2 ⟨sub8_754, List.forall_mem_cons.2 ⟨sub8_755, List.forall_mem_cons.2 ⟨sub8_756, List.forall_mem_cons.2 ⟨sub8_757, List.forall_mem_cons.2 ⟨sub8_758, List.forall_mem_cons.2 ⟨sub8_759, List.forall_mem_cons.2 ⟨sub8_760, List.forall_mem_cons.2 ⟨sub8_761, List.forall_mem_cons.2 ⟨sub8_762, List.forall_mem_cons.2 ⟨sub8_763, List.forall_mem_cons.2 ⟨sub8_764, List.forall_mem_cons.2 ⟨sub8_765, List.forall_mem_cons.2 ⟨sub8_766, List.forall_mem_cons.2 ⟨sub8_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_768 : sub8 [-1, 5, -2] = true := by decide +kernel
theorem sub8_769 : sub8 [-1, 5, -1] = true := by decide +kernel
theorem sub8_770 : sub8 [-1, 5, 0] = true := by decide +kernel
theorem sub8_771 : sub8 [-1, 5, 1] = true := by decide +kernel
theorem sub8_772 : sub8 [-1, 5, 2] = true := by decide +kernel
theorem sub8_773 : sub8 [-1, 5, 3] = true := by decide +kernel
theorem sub8_774 : sub8 [-1, 5, 4] = true := by decide +kernel
theorem sub8_775 : sub8 [-1, 5, 5] = true := by decide +kernel
theorem sub8_776 : sub8 [-1, 5, 6] = true := by decide +kernel
theorem sub8_777 : sub8 [-1, 5, 7] = true := by decide +kernel
theorem sub8_778 : sub8 [-1, 6] = true := by decide +kernel
theorem sub8_779 : sub8 [-1, 7] = true := by decide +kernel
theorem sub8_780 : sub8 [0, -8] = true := by decide +kernel
theorem sub8_781 : sub8 [0, -7] = true := by decide +kernel
theorem sub8_782 : sub8 [0, -6] = true := by decide +kernel
theorem sub8_783 : sub8 [0, -5] = true := by decide +kernel
theorem sub8_784 : sub8 [0, -4, -8] = true := by decide +kernel
theorem sub8_785 : sub8 [0, -4, -7] = true := by decide +kernel
theorem sub8_786 : sub8 [0, -4, -6] = true := by decide +kernel
theorem sub8_787 : sub8 [0, -4, -5] = true := by decide +kernel
theorem sub8_788 : sub8 [0, -4, -4] = true := by decide +kernel
theorem sub8_789 : sub8 [0, -4, -3] = true := by decide +kernel
theorem sub8_790 : sub8 [0, -4, -2] = true := by decide +kernel
theorem sub8_791 : sub8 [0, -4, -1] = true := by decide +kernel
theorem sub8_792 : sub8 [0, -4, 0] = true := by decide +kernel
theorem sub8_793 : sub8 [0, -4, 1] = true := by decide +kernel
theorem sub8_794 : sub8 [0, -4, 2] = true := by decide +kernel
theorem sub8_795 : sub8 [0, -4, 3] = true := by decide +kernel
theorem sub8_796 : sub8 [0, -4, 4] = true := by decide +kernel
theorem sub8_797 : sub8 [0, -4, 5] = true := by decide +kernel
theorem sub8_798 : sub8 [0, -4, 6] = true := by decide +kernel
theorem sub8_799 : sub8 [0, -3, -9] = true := by decide +kernel
theorem sb8_24 : ∀ q ∈ blk8_24, sub8 q = true := by
  unfold blk8_24
  exact List.forall_mem_cons.2 ⟨sub8_768, List.forall_mem_cons.2 ⟨sub8_769, List.forall_mem_cons.2 ⟨sub8_770, List.forall_mem_cons.2 ⟨sub8_771, List.forall_mem_cons.2 ⟨sub8_772, List.forall_mem_cons.2 ⟨sub8_773, List.forall_mem_cons.2 ⟨sub8_774, List.forall_mem_cons.2 ⟨sub8_775, List.forall_mem_cons.2 ⟨sub8_776, List.forall_mem_cons.2 ⟨sub8_777, List.forall_mem_cons.2 ⟨sub8_778, List.forall_mem_cons.2 ⟨sub8_779, List.forall_mem_cons.2 ⟨sub8_780, List.forall_mem_cons.2 ⟨sub8_781, List.forall_mem_cons.2 ⟨sub8_782, List.forall_mem_cons.2 ⟨sub8_783, List.forall_mem_cons.2 ⟨sub8_784, List.forall_mem_cons.2 ⟨sub8_785, List.forall_mem_cons.2 ⟨sub8_786, List.forall_mem_cons.2 ⟨sub8_787, List.forall_mem_cons.2 ⟨sub8_788, List.forall_mem_cons.2 ⟨sub8_789, List.forall_mem_cons.2 ⟨sub8_790, List.forall_mem_cons.2 ⟨sub8_791, List.forall_mem_cons.2 ⟨sub8_792, List.forall_mem_cons.2 ⟨sub8_793, List.forall_mem_cons.2 ⟨sub8_794, List.forall_mem_cons.2 ⟨sub8_795, List.forall_mem_cons.2 ⟨sub8_796, List.forall_mem_cons.2 ⟨sub8_797, List.forall_mem_cons.2 ⟨sub8_798, List.forall_mem_cons.2 ⟨sub8_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_800 : sub8 [0, -3, -8] = true := by decide +kernel
theorem sub8_801 : sub8 [0, -3, -7] = true := by decide +kernel
theorem sub8_802 : sub8 [0, -3, -6] = true := by decide +kernel
theorem sub8_803 : sub8 [0, -3, -5] = true := by decide +kernel
theorem sub8_804 : sub8 [0, -3, -4] = true := by decide +kernel
theorem sub8_805 : sub8 [0, -3, -3] = true := by decide +kernel
theorem sub8_806 : sub8 [0, -3, -2] = true := by decide +kernel
theorem sub8_807 : sub8 [0, -3, -1] = true := by decide +kernel
theorem sub8_808 : sub8 [0, -3, 0] = true := by decide +kernel
theorem sub8_809 : sub8 [0, -3, 1] = true := by decide +kernel
theorem sub8_810 : sub8 [0, -3, 2] = true := by decide +kernel
theorem sub8_811 : sub8 [0, -3, 3] = true := by decide +kernel
theorem sub8_812 : sub8 [0, -3, 4] = true := by decide +kernel
theorem sub8_813 : sub8 [0, -3, 5] = true := by decide +kernel
theorem sub8_814 : sub8 [0, -3, 6] = true := by decide +kernel
theorem sub8_815 : sub8 [0, -3, 7] = true := by decide +kernel
theorem sub8_816 : sub8 [0, -2, -9] = true := by decide +kernel
theorem sub8_817 : sub8 [0, -2, -8] = true := by decide +kernel
theorem sub8_818 : sub8 [0, -2, -7] = true := by decide +kernel
theorem sub8_819 : sub8 [0, -2, -6] = true := by decide +kernel
theorem sub8_820 : sub8 [0, -2, -5] = true := by decide +kernel
theorem sub8_821 : sub8 [0, -2, -4] = true := by decide +kernel
theorem sub8_822 : sub8 [0, -2, -3] = true := by decide +kernel
theorem sub8_823 : sub8 [0, -2, -2] = true := by decide +kernel
theorem sub8_824 : sub8 [0, -2, -1] = true := by decide +kernel
theorem sub8_825 : sub8 [0, -2, 0] = true := by decide +kernel
theorem sub8_826 : sub8 [0, -2, 1] = true := by decide +kernel
theorem sub8_827 : sub8 [0, -2, 2] = true := by decide +kernel
theorem sub8_828 : sub8 [0, -2, 3] = true := by decide +kernel
theorem sub8_829 : sub8 [0, -2, 4] = true := by decide +kernel
theorem sub8_830 : sub8 [0, -2, 5] = true := by decide +kernel
theorem sub8_831 : sub8 [0, -2, 6] = true := by decide +kernel
theorem sb8_25 : ∀ q ∈ blk8_25, sub8 q = true := by
  unfold blk8_25
  exact List.forall_mem_cons.2 ⟨sub8_800, List.forall_mem_cons.2 ⟨sub8_801, List.forall_mem_cons.2 ⟨sub8_802, List.forall_mem_cons.2 ⟨sub8_803, List.forall_mem_cons.2 ⟨sub8_804, List.forall_mem_cons.2 ⟨sub8_805, List.forall_mem_cons.2 ⟨sub8_806, List.forall_mem_cons.2 ⟨sub8_807, List.forall_mem_cons.2 ⟨sub8_808, List.forall_mem_cons.2 ⟨sub8_809, List.forall_mem_cons.2 ⟨sub8_810, List.forall_mem_cons.2 ⟨sub8_811, List.forall_mem_cons.2 ⟨sub8_812, List.forall_mem_cons.2 ⟨sub8_813, List.forall_mem_cons.2 ⟨sub8_814, List.forall_mem_cons.2 ⟨sub8_815, List.forall_mem_cons.2 ⟨sub8_816, List.forall_mem_cons.2 ⟨sub8_817, List.forall_mem_cons.2 ⟨sub8_818, List.forall_mem_cons.2 ⟨sub8_819, List.forall_mem_cons.2 ⟨sub8_820, List.forall_mem_cons.2 ⟨sub8_821, List.forall_mem_cons.2 ⟨sub8_822, List.forall_mem_cons.2 ⟨sub8_823, List.forall_mem_cons.2 ⟨sub8_824, List.forall_mem_cons.2 ⟨sub8_825, List.forall_mem_cons.2 ⟨sub8_826, List.forall_mem_cons.2 ⟨sub8_827, List.forall_mem_cons.2 ⟨sub8_828, List.forall_mem_cons.2 ⟨sub8_829, List.forall_mem_cons.2 ⟨sub8_830, List.forall_mem_cons.2 ⟨sub8_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_832 : sub8 [0, -2, 7] = true := by decide +kernel
theorem sub8_833 : sub8 [0, -2, 8] = true := by decide +kernel
theorem sub8_834 : sub8 [0, -1, -9] = true := by decide +kernel
theorem sub8_835 : sub8 [0, -1, -8] = true := by decide +kernel
theorem sub8_836 : sub8 [0, -1, -7] = true := by decide +kernel
theorem sub8_837 : sub8 [0, -1, -6] = true := by decide +kernel
theorem sub8_838 : sub8 [0, -1, -5] = true := by decide +kernel
theorem sub8_839 : sub8 [0, -1, -4] = true := by decide +kernel
theorem sub8_840 : sub8 [0, -1, -3] = true := by decide +kernel
theorem sub8_841 : sub8 [0, -1, -2] = true := by decide +kernel
theorem sub8_842 : sub8 [0, -1, -1] = true := by decide +kernel
theorem sub8_843 : sub8 [0, -1, 0] = true := by decide +kernel
theorem sub8_844 : sub8 [0, -1, 1] = true := by decide +kernel
theorem sub8_845 : sub8 [0, -1, 2] = true := by decide +kernel
theorem sub8_846 : sub8 [0, -1, 3] = true := by decide +kernel
theorem sub8_847 : sub8 [0, -1, 4] = true := by decide +kernel
theorem sub8_848 : sub8 [0, -1, 5] = true := by decide +kernel
theorem sub8_849 : sub8 [0, -1, 6] = true := by decide +kernel
theorem sub8_850 : sub8 [0, -1, 7] = true := by decide +kernel
theorem sub8_851 : sub8 [0, -1, 8] = true := by decide +kernel
theorem sub8_852 : sub8 [0, 0, -9] = true := by decide +kernel
theorem sub8_853 : sub8 [0, 0, -8] = true := by decide +kernel
theorem sub8_854 : sub8 [0, 0, -7] = true := by decide +kernel
theorem sub8_855 : sub8 [0, 0, -6] = true := by decide +kernel
theorem sub8_856 : sub8 [0, 0, -5] = true := by decide +kernel
theorem sub8_857 : sub8 [0, 0, -4] = true := by decide +kernel
theorem sub8_858 : sub8 [0, 0, -3] = true := by decide +kernel
theorem sub8_859 : sub8 [0, 0, -2] = true := by decide +kernel
theorem sub8_860 : sub8 [0, 0, -1] = true := by decide +kernel
theorem sub8_861 : sub8 [0, 0, 0] = true := by decide +kernel
theorem sub8_862 : sub8 [0, 0, 1] = true := by decide +kernel
theorem sub8_863 : sub8 [0, 0, 2] = true := by decide +kernel
theorem sb8_26 : ∀ q ∈ blk8_26, sub8 q = true := by
  unfold blk8_26
  exact List.forall_mem_cons.2 ⟨sub8_832, List.forall_mem_cons.2 ⟨sub8_833, List.forall_mem_cons.2 ⟨sub8_834, List.forall_mem_cons.2 ⟨sub8_835, List.forall_mem_cons.2 ⟨sub8_836, List.forall_mem_cons.2 ⟨sub8_837, List.forall_mem_cons.2 ⟨sub8_838, List.forall_mem_cons.2 ⟨sub8_839, List.forall_mem_cons.2 ⟨sub8_840, List.forall_mem_cons.2 ⟨sub8_841, List.forall_mem_cons.2 ⟨sub8_842, List.forall_mem_cons.2 ⟨sub8_843, List.forall_mem_cons.2 ⟨sub8_844, List.forall_mem_cons.2 ⟨sub8_845, List.forall_mem_cons.2 ⟨sub8_846, List.forall_mem_cons.2 ⟨sub8_847, List.forall_mem_cons.2 ⟨sub8_848, List.forall_mem_cons.2 ⟨sub8_849, List.forall_mem_cons.2 ⟨sub8_850, List.forall_mem_cons.2 ⟨sub8_851, List.forall_mem_cons.2 ⟨sub8_852, List.forall_mem_cons.2 ⟨sub8_853, List.forall_mem_cons.2 ⟨sub8_854, List.forall_mem_cons.2 ⟨sub8_855, List.forall_mem_cons.2 ⟨sub8_856, List.forall_mem_cons.2 ⟨sub8_857, List.forall_mem_cons.2 ⟨sub8_858, List.forall_mem_cons.2 ⟨sub8_859, List.forall_mem_cons.2 ⟨sub8_860, List.forall_mem_cons.2 ⟨sub8_861, List.forall_mem_cons.2 ⟨sub8_862, List.forall_mem_cons.2 ⟨sub8_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_864 : sub8 [0, 0, 3] = true := by decide +kernel
theorem sub8_865 : sub8 [0, 0, 4] = true := by decide +kernel
theorem sub8_866 : sub8 [0, 0, 5] = true := by decide +kernel
theorem sub8_867 : sub8 [0, 0, 6] = true := by decide +kernel
theorem sub8_868 : sub8 [0, 0, 7] = true := by decide +kernel
theorem sub8_869 : sub8 [0, 0, 8] = true := by decide +kernel
theorem sub8_870 : sub8 [0, 1, -9] = true := by decide +kernel
theorem sub8_871 : sub8 [0, 1, -8] = true := by decide +kernel
theorem sub8_872 : sub8 [0, 1, -7] = true := by decide +kernel
theorem sub8_873 : sub8 [0, 1, -6] = true := by decide +kernel
theorem sub8_874 : sub8 [0, 1, -5] = true := by decide +kernel
theorem sub8_875 : sub8 [0, 1, -4] = true := by decide +kernel
theorem sub8_876 : sub8 [0, 1, -3] = true := by decide +kernel
theorem sub8_877 : sub8 [0, 1, -2] = true := by decide +kernel
theorem sub8_878 : sub8 [0, 1, -1] = true := by decide +kernel
theorem sub8_879 : sub8 [0, 1, 0] = true := by decide +kernel
theorem sub8_880 : sub8 [0, 1, 1] = true := by decide +kernel
theorem sub8_881 : sub8 [0, 1, 2] = true := by decide +kernel
theorem sub8_882 : sub8 [0, 1, 3] = true := by decide +kernel
theorem sub8_883 : sub8 [0, 1, 4] = true := by decide +kernel
theorem sub8_884 : sub8 [0, 1, 5] = true := by decide +kernel
theorem sub8_885 : sub8 [0, 1, 6] = true := by decide +kernel
theorem sub8_886 : sub8 [0, 1, 7] = true := by decide +kernel
theorem sub8_887 : sub8 [0, 1, 8] = true := by decide +kernel
theorem sub8_888 : sub8 [0, 2, -9] = true := by decide +kernel
theorem sub8_889 : sub8 [0, 2, -8] = true := by decide +kernel
theorem sub8_890 : sub8 [0, 2, -7] = true := by decide +kernel
theorem sub8_891 : sub8 [0, 2, -6] = true := by decide +kernel
theorem sub8_892 : sub8 [0, 2, -5] = true := by decide +kernel
theorem sub8_893 : sub8 [0, 2, -4] = true := by decide +kernel
theorem sub8_894 : sub8 [0, 2, -3] = true := by decide +kernel
theorem sub8_895 : sub8 [0, 2, -2] = true := by decide +kernel
theorem sb8_27 : ∀ q ∈ blk8_27, sub8 q = true := by
  unfold blk8_27
  exact List.forall_mem_cons.2 ⟨sub8_864, List.forall_mem_cons.2 ⟨sub8_865, List.forall_mem_cons.2 ⟨sub8_866, List.forall_mem_cons.2 ⟨sub8_867, List.forall_mem_cons.2 ⟨sub8_868, List.forall_mem_cons.2 ⟨sub8_869, List.forall_mem_cons.2 ⟨sub8_870, List.forall_mem_cons.2 ⟨sub8_871, List.forall_mem_cons.2 ⟨sub8_872, List.forall_mem_cons.2 ⟨sub8_873, List.forall_mem_cons.2 ⟨sub8_874, List.forall_mem_cons.2 ⟨sub8_875, List.forall_mem_cons.2 ⟨sub8_876, List.forall_mem_cons.2 ⟨sub8_877, List.forall_mem_cons.2 ⟨sub8_878, List.forall_mem_cons.2 ⟨sub8_879, List.forall_mem_cons.2 ⟨sub8_880, List.forall_mem_cons.2 ⟨sub8_881, List.forall_mem_cons.2 ⟨sub8_882, List.forall_mem_cons.2 ⟨sub8_883, List.forall_mem_cons.2 ⟨sub8_884, List.forall_mem_cons.2 ⟨sub8_885, List.forall_mem_cons.2 ⟨sub8_886, List.forall_mem_cons.2 ⟨sub8_887, List.forall_mem_cons.2 ⟨sub8_888, List.forall_mem_cons.2 ⟨sub8_889, List.forall_mem_cons.2 ⟨sub8_890, List.forall_mem_cons.2 ⟨sub8_891, List.forall_mem_cons.2 ⟨sub8_892, List.forall_mem_cons.2 ⟨sub8_893, List.forall_mem_cons.2 ⟨sub8_894, List.forall_mem_cons.2 ⟨sub8_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C102
