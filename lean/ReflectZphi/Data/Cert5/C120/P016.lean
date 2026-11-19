import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub12_448 : sub12 [1, 2, 6] = true := by decide +kernel
theorem sub12_449 : sub12 [1, 2, 7] = true := by decide +kernel
theorem sub12_450 : sub12 [1, 3, -7] = true := by decide +kernel
theorem sub12_451 : sub12 [1, 3, -6] = true := by decide +kernel
theorem sub12_452 : sub12 [1, 3, -5] = true := by decide +kernel
theorem sub12_453 : sub12 [1, 3, -4] = true := by decide +kernel
theorem sub12_454 : sub12 [1, 3, -3] = true := by decide +kernel
theorem sub12_455 : sub12 [1, 3, -2] = true := by decide +kernel
theorem sub12_456 : sub12 [1, 3, -1] = true := by decide +kernel
theorem sub12_457 : sub12 [1, 3, 0] = true := by decide +kernel
theorem sub12_458 : sub12 [1, 3, 1] = true := by decide +kernel
theorem sub12_459 : sub12 [1, 3, 2] = true := by decide +kernel
theorem sub12_460 : sub12 [1, 3, 3] = true := by decide +kernel
theorem sub12_461 : sub12 [1, 3, 4] = true := by decide +kernel
theorem sub12_462 : sub12 [1, 3, 5] = true := by decide +kernel
theorem sub12_463 : sub12 [1, 4] = true := by decide +kernel
theorem sub12_464 : sub12 [2, -5] = true := by decide +kernel
theorem sub12_465 : sub12 [2, -4] = true := by decide +kernel
theorem sub12_466 : sub12 [2, -3] = true := by decide +kernel
theorem sub12_467 : sub12 [2, -2, -6] = true := by decide +kernel
theorem sub12_468 : sub12 [2, -2, -5] = true := by decide +kernel
theorem sub12_469 : sub12 [2, -2, -4] = true := by decide +kernel
theorem sub12_470 : sub12 [2, -2, -3] = true := by decide +kernel
theorem sub12_471 : sub12 [2, -2, -2] = true := by decide +kernel
theorem sub12_472 : sub12 [2, -2, -1] = true := by decide +kernel
theorem sub12_473 : sub12 [2, -2, 0] = true := by decide +kernel
theorem sub12_474 : sub12 [2, -2, 1] = true := by decide +kernel
theorem sub12_475 : sub12 [2, -2, 2] = true := by decide +kernel
theorem sub12_476 : sub12 [2, -2, 3] = true := by decide +kernel
theorem sub12_477 : sub12 [2, -2, 4] = true := by decide +kernel
theorem sub12_478 : sub12 [2, -2, 5] = true := by decide +kernel
theorem sub12_479 : sub12 [2, -2, 6] = true := by decide +kernel
theorem sb12_14 : ∀ q ∈ blk12_14, sub12 q = true := by
  unfold blk12_14
  exact List.forall_mem_cons.2 ⟨sub12_448, List.forall_mem_cons.2 ⟨sub12_449, List.forall_mem_cons.2 ⟨sub12_450, List.forall_mem_cons.2 ⟨sub12_451, List.forall_mem_cons.2 ⟨sub12_452, List.forall_mem_cons.2 ⟨sub12_453, List.forall_mem_cons.2 ⟨sub12_454, List.forall_mem_cons.2 ⟨sub12_455, List.forall_mem_cons.2 ⟨sub12_456, List.forall_mem_cons.2 ⟨sub12_457, List.forall_mem_cons.2 ⟨sub12_458, List.forall_mem_cons.2 ⟨sub12_459, List.forall_mem_cons.2 ⟨sub12_460, List.forall_mem_cons.2 ⟨sub12_461, List.forall_mem_cons.2 ⟨sub12_462, List.forall_mem_cons.2 ⟨sub12_463, List.forall_mem_cons.2 ⟨sub12_464, List.forall_mem_cons.2 ⟨sub12_465, List.forall_mem_cons.2 ⟨sub12_466, List.forall_mem_cons.2 ⟨sub12_467, List.forall_mem_cons.2 ⟨sub12_468, List.forall_mem_cons.2 ⟨sub12_469, List.forall_mem_cons.2 ⟨sub12_470, List.forall_mem_cons.2 ⟨sub12_471, List.forall_mem_cons.2 ⟨sub12_472, List.forall_mem_cons.2 ⟨sub12_473, List.forall_mem_cons.2 ⟨sub12_474, List.forall_mem_cons.2 ⟨sub12_475, List.forall_mem_cons.2 ⟨sub12_476, List.forall_mem_cons.2 ⟨sub12_477, List.forall_mem_cons.2 ⟨sub12_478, List.forall_mem_cons.2 ⟨sub12_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_480 : sub12 [2, -2, 7] = true := by decide +kernel
theorem sub12_481 : sub12 [2, -1, -7] = true := by decide +kernel
theorem sub12_482 : sub12 [2, -1, -6] = true := by decide +kernel
theorem sub12_483 : sub12 [2, -1, -5] = true := by decide +kernel
theorem sub12_484 : sub12 [2, -1, -4] = true := by decide +kernel
theorem sub12_485 : sub12 [2, -1, -3] = true := by decide +kernel
theorem sub12_486 : sub12 [2, -1, -2] = true := by decide +kernel
theorem sub12_487 : sub12 [2, -1, -1] = true := by decide +kernel
theorem sub12_488 : sub12 [2, -1, 0] = true := by decide +kernel
theorem sub12_489 : sub12 [2, -1, 1] = true := by decide +kernel
theorem sub12_490 : sub12 [2, -1, 2] = true := by decide +kernel
theorem sub12_491 : sub12 [2, -1, 3] = true := by decide +kernel
theorem sub12_492 : sub12 [2, -1, 4] = true := by decide +kernel
theorem sub12_493 : sub12 [2, -1, 5] = true := by decide +kernel
theorem sub12_494 : sub12 [2, -1, 6] = true := by decide +kernel
theorem sub12_495 : sub12 [2, -1, 7] = true := by decide +kernel
theorem sub12_496 : sub12 [2, 0, -7] = true := by decide +kernel
theorem sub12_497 : sub12 [2, 0, -6] = true := by decide +kernel
theorem sub12_498 : sub12 [2, 0, -5] = true := by decide +kernel
theorem sub12_499 : sub12 [2, 0, -4] = true := by decide +kernel
theorem sub12_500 : sub12 [2, 0, -3] = true := by decide +kernel
theorem sub12_501 : sub12 [2, 0, -2] = true := by decide +kernel
theorem sub12_502 : sub12 [2, 0, -1] = true := by decide +kernel
theorem sub12_503 : sub12 [2, 0, 0] = true := by decide +kernel
theorem sub12_504 : sub12 [2, 0, 1] = true := by decide +kernel
theorem sub12_505 : sub12 [2, 0, 2] = true := by decide +kernel
theorem sub12_506 : sub12 [2, 0, 3] = true := by decide +kernel
theorem sub12_507 : sub12 [2, 0, 4] = true := by decide +kernel
theorem sub12_508 : sub12 [2, 0, 5] = true := by decide +kernel
theorem sub12_509 : sub12 [2, 0, 6] = true := by decide +kernel
theorem sub12_510 : sub12 [2, 0, 7] = true := by decide +kernel
theorem sub12_511 : sub12 [2, 1, -7] = true := by decide +kernel
theorem sb12_15 : ∀ q ∈ blk12_15, sub12 q = true := by
  unfold blk12_15
  exact List.forall_mem_cons.2 ⟨sub12_480, List.forall_mem_cons.2 ⟨sub12_481, List.forall_mem_cons.2 ⟨sub12_482, List.forall_mem_cons.2 ⟨sub12_483, List.forall_mem_cons.2 ⟨sub12_484, List.forall_mem_cons.2 ⟨sub12_485, List.forall_mem_cons.2 ⟨sub12_486, List.forall_mem_cons.2 ⟨sub12_487, List.forall_mem_cons.2 ⟨sub12_488, List.forall_mem_cons.2 ⟨sub12_489, List.forall_mem_cons.2 ⟨sub12_490, List.forall_mem_cons.2 ⟨sub12_491, List.forall_mem_cons.2 ⟨sub12_492, List.forall_mem_cons.2 ⟨sub12_493, List.forall_mem_cons.2 ⟨sub12_494, List.forall_mem_cons.2 ⟨sub12_495, List.forall_mem_cons.2 ⟨sub12_496, List.forall_mem_cons.2 ⟨sub12_497, List.forall_mem_cons.2 ⟨sub12_498, List.forall_mem_cons.2 ⟨sub12_499, List.forall_mem_cons.2 ⟨sub12_500, List.forall_mem_cons.2 ⟨sub12_501, List.forall_mem_cons.2 ⟨sub12_502, List.forall_mem_cons.2 ⟨sub12_503, List.forall_mem_cons.2 ⟨sub12_504, List.forall_mem_cons.2 ⟨sub12_505, List.forall_mem_cons.2 ⟨sub12_506, List.forall_mem_cons.2 ⟨sub12_507, List.forall_mem_cons.2 ⟨sub12_508, List.forall_mem_cons.2 ⟨sub12_509, List.forall_mem_cons.2 ⟨sub12_510, List.forall_mem_cons.2 ⟨sub12_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_512 : sub12 [2, 1, -6] = true := by decide +kernel
theorem sub12_513 : sub12 [2, 1, -5] = true := by decide +kernel
theorem sub12_514 : sub12 [2, 1, -4] = true := by decide +kernel
theorem sub12_515 : sub12 [2, 1, -3] = true := by decide +kernel
theorem sub12_516 : sub12 [2, 1, -2] = true := by decide +kernel
theorem sub12_517 : sub12 [2, 1, -1] = true := by decide +kernel
theorem sub12_518 : sub12 [2, 1, 0] = true := by decide +kernel
theorem sub12_519 : sub12 [2, 1, 1] = true := by decide +kernel
theorem sub12_520 : sub12 [2, 1, 2] = true := by decide +kernel
theorem sub12_521 : sub12 [2, 1, 3] = true := by decide +kernel
theorem sub12_522 : sub12 [2, 1, 4] = true := by decide +kernel
theorem sub12_523 : sub12 [2, 1, 5] = true := by decide +kernel
theorem sub12_524 : sub12 [2, 1, 6] = true := by decide +kernel
theorem sub12_525 : sub12 [2, 1, 7] = true := by decide +kernel
theorem sub12_526 : sub12 [2, 2, -7] = true := by decide +kernel
theorem sub12_527 : sub12 [2, 2, -6] = true := by decide +kernel
theorem sub12_528 : sub12 [2, 2, -5] = true := by decide +kernel
theorem sub12_529 : sub12 [2, 2, -4] = true := by decide +kernel
theorem sub12_530 : sub12 [2, 2, -3] = true := by decide +kernel
theorem sub12_531 : sub12 [2, 2, -2] = true := by decide +kernel
theorem sub12_532 : sub12 [2, 2, -1] = true := by decide +kernel
theorem sub12_533 : sub12 [2, 2, 0] = true := by decide +kernel
theorem sub12_534 : sub12 [2, 2, 1] = true := by decide +kernel
theorem sub12_535 : sub12 [2, 2, 2] = true := by decide +kernel
theorem sub12_536 : sub12 [2, 2, 3] = true := by decide +kernel
theorem sub12_537 : sub12 [2, 2, 4] = true := by decide +kernel
theorem sub12_538 : sub12 [2, 2, 5] = true := by decide +kernel
theorem sub12_539 : sub12 [2, 2, 6] = true := by decide +kernel
theorem sub12_540 : sub12 [2, 3] = true := by decide +kernel
theorem sub12_541 : sub12 [2, 4] = true := by decide +kernel
theorem sub12_542 : sub12 [3, -5] = true := by decide +kernel
theorem sub12_543 : sub12 [3, -4] = true := by decide +kernel
theorem sb12_16 : ∀ q ∈ blk12_16, sub12 q = true := by
  unfold blk12_16
  exact List.forall_mem_cons.2 ⟨sub12_512, List.forall_mem_cons.2 ⟨sub12_513, List.forall_mem_cons.2 ⟨sub12_514, List.forall_mem_cons.2 ⟨sub12_515, List.forall_mem_cons.2 ⟨sub12_516, List.forall_mem_cons.2 ⟨sub12_517, List.forall_mem_cons.2 ⟨sub12_518, List.forall_mem_cons.2 ⟨sub12_519, List.forall_mem_cons.2 ⟨sub12_520, List.forall_mem_cons.2 ⟨sub12_521, List.forall_mem_cons.2 ⟨sub12_522, List.forall_mem_cons.2 ⟨sub12_523, List.forall_mem_cons.2 ⟨sub12_524, List.forall_mem_cons.2 ⟨sub12_525, List.forall_mem_cons.2 ⟨sub12_526, List.forall_mem_cons.2 ⟨sub12_527, List.forall_mem_cons.2 ⟨sub12_528, List.forall_mem_cons.2 ⟨sub12_529, List.forall_mem_cons.2 ⟨sub12_530, List.forall_mem_cons.2 ⟨sub12_531, List.forall_mem_cons.2 ⟨sub12_532, List.forall_mem_cons.2 ⟨sub12_533, List.forall_mem_cons.2 ⟨sub12_534, List.forall_mem_cons.2 ⟨sub12_535, List.forall_mem_cons.2 ⟨sub12_536, List.forall_mem_cons.2 ⟨sub12_537, List.forall_mem_cons.2 ⟨sub12_538, List.forall_mem_cons.2 ⟨sub12_539, List.forall_mem_cons.2 ⟨sub12_540, List.forall_mem_cons.2 ⟨sub12_541, List.forall_mem_cons.2 ⟨sub12_542, List.forall_mem_cons.2 ⟨sub12_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_544 : sub12 [3, -3] = true := by decide +kernel
theorem sub12_545 : sub12 [3, -2] = true := by decide +kernel
theorem sub12_546 : sub12 [3, -1, -6] = true := by decide +kernel
theorem sub12_547 : sub12 [3, -1, -5] = true := by decide +kernel
theorem sub12_548 : sub12 [3, -1, -4] = true := by decide +kernel
theorem sub12_549 : sub12 [3, -1, -3] = true := by decide +kernel
theorem sub12_550 : sub12 [3, -1, -2] = true := by decide +kernel
theorem sub12_551 : sub12 [3, -1, -1] = true := by decide +kernel
theorem sub12_552 : sub12 [3, -1, 0] = true := by decide +kernel
theorem sub12_553 : sub12 [3, -1, 1] = true := by decide +kernel
theorem sub12_554 : sub12 [3, -1, 2] = true := by decide +kernel
theorem sub12_555 : sub12 [3, -1, 3] = true := by decide +kernel
theorem sub12_556 : sub12 [3, -1, 4] = true := by decide +kernel
theorem sub12_557 : sub12 [3, -1, 5] = true := by decide +kernel
theorem sub12_558 : sub12 [3, -1, 6] = true := by decide +kernel
theorem sub12_559 : sub12 [3, -1, 7] = true := by decide +kernel
theorem sub12_560 : sub12 [3, 0, -6] = true := by decide +kernel
theorem sub12_561 : sub12 [3, 0, -5] = true := by decide +kernel
theorem sub12_562 : sub12 [3, 0, -4] = true := by decide +kernel
theorem sub12_563 : sub12 [3, 0, -3] = true := by decide +kernel
theorem sub12_564 : sub12 [3, 0, -2] = true := by decide +kernel
theorem sub12_565 : sub12 [3, 0, -1] = true := by decide +kernel
theorem sub12_566 : sub12 [3, 0, 0] = true := by decide +kernel
theorem sub12_567 : sub12 [3, 0, 1] = true := by decide +kernel
theorem sub12_568 : sub12 [3, 0, 2] = true := by decide +kernel
theorem sub12_569 : sub12 [3, 0, 3] = true := by decide +kernel
theorem sub12_570 : sub12 [3, 0, 4] = true := by decide +kernel
theorem sub12_571 : sub12 [3, 0, 5] = true := by decide +kernel
theorem sub12_572 : sub12 [3, 0, 6] = true := by decide +kernel
theorem sub12_573 : sub12 [3, 0, 7] = true := by decide +kernel
theorem sub12_574 : sub12 [3, 1, -6] = true := by decide +kernel
theorem sub12_575 : sub12 [3, 1, -5] = true := by decide +kernel
theorem sb12_17 : ∀ q ∈ blk12_17, sub12 q = true := by
  unfold blk12_17
  exact List.forall_mem_cons.2 ⟨sub12_544, List.forall_mem_cons.2 ⟨sub12_545, List.forall_mem_cons.2 ⟨sub12_546, List.forall_mem_cons.2 ⟨sub12_547, List.forall_mem_cons.2 ⟨sub12_548, List.forall_mem_cons.2 ⟨sub12_549, List.forall_mem_cons.2 ⟨sub12_550, List.forall_mem_cons.2 ⟨sub12_551, List.forall_mem_cons.2 ⟨sub12_552, List.forall_mem_cons.2 ⟨sub12_553, List.forall_mem_cons.2 ⟨sub12_554, List.forall_mem_cons.2 ⟨sub12_555, List.forall_mem_cons.2 ⟨sub12_556, List.forall_mem_cons.2 ⟨sub12_557, List.forall_mem_cons.2 ⟨sub12_558, List.forall_mem_cons.2 ⟨sub12_559, List.forall_mem_cons.2 ⟨sub12_560, List.forall_mem_cons.2 ⟨sub12_561, List.forall_mem_cons.2 ⟨sub12_562, List.forall_mem_cons.2 ⟨sub12_563, List.forall_mem_cons.2 ⟨sub12_564, List.forall_mem_cons.2 ⟨sub12_565, List.forall_mem_cons.2 ⟨sub12_566, List.forall_mem_cons.2 ⟨sub12_567, List.forall_mem_cons.2 ⟨sub12_568, List.forall_mem_cons.2 ⟨sub12_569, List.forall_mem_cons.2 ⟨sub12_570, List.forall_mem_cons.2 ⟨sub12_571, List.forall_mem_cons.2 ⟨sub12_572, List.forall_mem_cons.2 ⟨sub12_573, List.forall_mem_cons.2 ⟨sub12_574, List.forall_mem_cons.2 ⟨sub12_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_576 : sub12 [3, 1, -4] = true := by decide +kernel
theorem sub12_577 : sub12 [3, 1, -3] = true := by decide +kernel
theorem sub12_578 : sub12 [3, 1, -2] = true := by decide +kernel
theorem sub12_579 : sub12 [3, 1, -1] = true := by decide +kernel
theorem sub12_580 : sub12 [3, 1, 0] = true := by decide +kernel
theorem sub12_581 : sub12 [3, 1, 1] = true := by decide +kernel
theorem sub12_582 : sub12 [3, 1, 2] = true := by decide +kernel
theorem sub12_583 : sub12 [3, 1, 3] = true := by decide +kernel
theorem sub12_584 : sub12 [3, 1, 4] = true := by decide +kernel
theorem sub12_585 : sub12 [3, 1, 5] = true := by decide +kernel
theorem sub12_586 : sub12 [3, 1, 6] = true := by decide +kernel
theorem sub12_587 : sub12 [3, 2] = true := by decide +kernel
theorem sub12_588 : sub12 [3, 3] = true := by decide +kernel
theorem sub12_589 : sub12 [4, -4] = true := by decide +kernel
theorem sub12_590 : sub12 [4, -3] = true := by decide +kernel
theorem sub12_591 : sub12 [4, -2] = true := by decide +kernel
theorem sub12_592 : sub12 [4, -1] = true := by decide +kernel
theorem sub12_593 : sub12 [4, 0] = true := by decide +kernel
theorem sub12_594 : sub12 [4, 1] = true := by decide +kernel
theorem sub12_595 : sub12 [4, 2] = true := by decide +kernel
theorem sub12_596 : sub12 [5] = true := by decide +kernel
theorem sb12_18 : ∀ q ∈ blk12_18, sub12 q = true := by
  unfold blk12_18
  exact List.forall_mem_cons.2 ⟨sub12_576, List.forall_mem_cons.2 ⟨sub12_577, List.forall_mem_cons.2 ⟨sub12_578, List.forall_mem_cons.2 ⟨sub12_579, List.forall_mem_cons.2 ⟨sub12_580, List.forall_mem_cons.2 ⟨sub12_581, List.forall_mem_cons.2 ⟨sub12_582, List.forall_mem_cons.2 ⟨sub12_583, List.forall_mem_cons.2 ⟨sub12_584, List.forall_mem_cons.2 ⟨sub12_585, List.forall_mem_cons.2 ⟨sub12_586, List.forall_mem_cons.2 ⟨sub12_587, List.forall_mem_cons.2 ⟨sub12_588, List.forall_mem_cons.2 ⟨sub12_589, List.forall_mem_cons.2 ⟨sub12_590, List.forall_mem_cons.2 ⟨sub12_591, List.forall_mem_cons.2 ⟨sub12_592, List.forall_mem_cons.2 ⟨sub12_593, List.forall_mem_cons.2 ⟨sub12_594, List.forall_mem_cons.2 ⟨sub12_595, List.forall_mem_cons.2 ⟨sub12_596, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_0 : sub13 [-7] = true := by decide +kernel
theorem sub13_1 : sub13 [-6, -3] = true := by decide +kernel
theorem sub13_2 : sub13 [-6, -2] = true := by decide +kernel
theorem sub13_3 : sub13 [-6, -1] = true := by decide +kernel
theorem sub13_4 : sub13 [-6, 0] = true := by decide +kernel
theorem sub13_5 : sub13 [-6, 1] = true := by decide +kernel
theorem sub13_6 : sub13 [-6, 2] = true := by decide +kernel
theorem sub13_7 : sub13 [-6, 3] = true := by decide +kernel
theorem sub13_8 : sub13 [-6, 4] = true := by decide +kernel
theorem sub13_9 : sub13 [-6, 5] = true := by decide +kernel
theorem sub13_10 : sub13 [-5, -5] = true := by decide +kernel
theorem sub13_11 : sub13 [-5, -4] = true := by decide +kernel
theorem sub13_12 : sub13 [-5, -3] = true := by decide +kernel
theorem sub13_13 : sub13 [-5, -2] = true := by decide +kernel
theorem sub13_14 : sub13 [-5, -1] = true := by decide +kernel
theorem sub13_15 : sub13 [-5, 0] = true := by decide +kernel
theorem sub13_16 : sub13 [-5, 1] = true := by decide +kernel
theorem sub13_17 : sub13 [-5, 2] = true := by decide +kernel
theorem sub13_18 : sub13 [-5, 3] = true := by decide +kernel
theorem sub13_19 : sub13 [-5, 4] = true := by decide +kernel
theorem sub13_20 : sub13 [-5, 5] = true := by decide +kernel
theorem sub13_21 : sub13 [-5, 6] = true := by decide +kernel
theorem sub13_22 : sub13 [-4, -6] = true := by decide +kernel
theorem sub13_23 : sub13 [-4, -5] = true := by decide +kernel
theorem sub13_24 : sub13 [-4, -4] = true := by decide +kernel
theorem sub13_25 : sub13 [-4, -3] = true := by decide +kernel
theorem sub13_26 : sub13 [-4, -2] = true := by decide +kernel
theorem sub13_27 : sub13 [-4, -1] = true := by decide +kernel
theorem sub13_28 : sub13 [-4, 0] = true := by decide +kernel
theorem sub13_29 : sub13 [-4, 1, -8] = true := by decide +kernel
theorem sub13_30 : sub13 [-4, 1, -7] = true := by decide +kernel
theorem sub13_31 : sub13 [-4, 1, -6] = true := by decide +kernel
theorem sb13_0 : ∀ q ∈ blk13_0, sub13 q = true := by
  unfold blk13_0
  exact List.forall_mem_cons.2 ⟨sub13_0, List.forall_mem_cons.2 ⟨sub13_1, List.forall_mem_cons.2 ⟨sub13_2, List.forall_mem_cons.2 ⟨sub13_3, List.forall_mem_cons.2 ⟨sub13_4, List.forall_mem_cons.2 ⟨sub13_5, List.forall_mem_cons.2 ⟨sub13_6, List.forall_mem_cons.2 ⟨sub13_7, List.forall_mem_cons.2 ⟨sub13_8, List.forall_mem_cons.2 ⟨sub13_9, List.forall_mem_cons.2 ⟨sub13_10, List.forall_mem_cons.2 ⟨sub13_11, List.forall_mem_cons.2 ⟨sub13_12, List.forall_mem_cons.2 ⟨sub13_13, List.forall_mem_cons.2 ⟨sub13_14, List.forall_mem_cons.2 ⟨sub13_15, List.forall_mem_cons.2 ⟨sub13_16, List.forall_mem_cons.2 ⟨sub13_17, List.forall_mem_cons.2 ⟨sub13_18, List.forall_mem_cons.2 ⟨sub13_19, List.forall_mem_cons.2 ⟨sub13_20, List.forall_mem_cons.2 ⟨sub13_21, List.forall_mem_cons.2 ⟨sub13_22, List.forall_mem_cons.2 ⟨sub13_23, List.forall_mem_cons.2 ⟨sub13_24, List.forall_mem_cons.2 ⟨sub13_25, List.forall_mem_cons.2 ⟨sub13_26, List.forall_mem_cons.2 ⟨sub13_27, List.forall_mem_cons.2 ⟨sub13_28, List.forall_mem_cons.2 ⟨sub13_29, List.forall_mem_cons.2 ⟨sub13_30, List.forall_mem_cons.2 ⟨sub13_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_32 : sub13 [-4, 1, -5] = true := by decide +kernel
theorem sub13_33 : sub13 [-4, 1, -4] = true := by decide +kernel
theorem sub13_34 : sub13 [-4, 1, -3] = true := by decide +kernel
theorem sub13_35 : sub13 [-4, 1, -2] = true := by decide +kernel
theorem sub13_36 : sub13 [-4, 1, -1] = true := by decide +kernel
theorem sub13_37 : sub13 [-4, 1, 0] = true := by decide +kernel
theorem sub13_38 : sub13 [-4, 1, 1] = true := by decide +kernel
theorem sub13_39 : sub13 [-4, 1, 2] = true := by decide +kernel
theorem sub13_40 : sub13 [-4, 1, 3] = true := by decide +kernel
theorem sub13_41 : sub13 [-4, 1, 4] = true := by decide +kernel
theorem sub13_42 : sub13 [-4, 1, 5] = true := by decide +kernel
theorem sub13_43 : sub13 [-4, 2] = true := by decide +kernel
theorem sub13_44 : sub13 [-4, 3] = true := by decide +kernel
theorem sub13_45 : sub13 [-4, 4] = true := by decide +kernel
theorem sub13_46 : sub13 [-4, 5] = true := by decide +kernel
theorem sub13_47 : sub13 [-4, 6] = true := by decide +kernel
theorem sub13_48 : sub13 [-4, 7] = true := by decide +kernel
theorem sub13_49 : sub13 [-3, -7] = true := by decide +kernel
theorem sub13_50 : sub13 [-3, -6] = true := by decide +kernel
theorem sub13_51 : sub13 [-3, -5] = true := by decide +kernel
theorem sub13_52 : sub13 [-3, -4] = true := by decide +kernel
theorem sub13_53 : sub13 [-3, -3] = true := by decide +kernel
theorem sub13_54 : sub13 [-3, -2, -7] = true := by decide +kernel
theorem sub13_55 : sub13 [-3, -2, -6] = true := by decide +kernel
theorem sub13_56 : sub13 [-3, -2, -5] = true := by decide +kernel
theorem sub13_57 : sub13 [-3, -2, -4] = true := by decide +kernel
theorem sub13_58 : sub13 [-3, -2, -3] = true := by decide +kernel
theorem sub13_59 : sub13 [-3, -2, -2] = true := by decide +kernel
theorem sub13_60 : sub13 [-3, -2, -1] = true := by decide +kernel
theorem sub13_61 : sub13 [-3, -2, 0] = true := by decide +kernel
theorem sub13_62 : sub13 [-3, -2, 1] = true := by decide +kernel
theorem sub13_63 : sub13 [-3, -2, 2] = true := by decide +kernel
theorem sb13_1 : ∀ q ∈ blk13_1, sub13 q = true := by
  unfold blk13_1
  exact List.forall_mem_cons.2 ⟨sub13_32, List.forall_mem_cons.2 ⟨sub13_33, List.forall_mem_cons.2 ⟨sub13_34, List.forall_mem_cons.2 ⟨sub13_35, List.forall_mem_cons.2 ⟨sub13_36, List.forall_mem_cons.2 ⟨sub13_37, List.forall_mem_cons.2 ⟨sub13_38, List.forall_mem_cons.2 ⟨sub13_39, List.forall_mem_cons.2 ⟨sub13_40, List.forall_mem_cons.2 ⟨sub13_41, List.forall_mem_cons.2 ⟨sub13_42, List.forall_mem_cons.2 ⟨sub13_43, List.forall_mem_cons.2 ⟨sub13_44, List.forall_mem_cons.2 ⟨sub13_45, List.forall_mem_cons.2 ⟨sub13_46, List.forall_mem_cons.2 ⟨sub13_47, List.forall_mem_cons.2 ⟨sub13_48, List.forall_mem_cons.2 ⟨sub13_49, List.forall_mem_cons.2 ⟨sub13_50, List.forall_mem_cons.2 ⟨sub13_51, List.forall_mem_cons.2 ⟨sub13_52, List.forall_mem_cons.2 ⟨sub13_53, List.forall_mem_cons.2 ⟨sub13_54, List.forall_mem_cons.2 ⟨sub13_55, List.forall_mem_cons.2 ⟨sub13_56, List.forall_mem_cons.2 ⟨sub13_57, List.forall_mem_cons.2 ⟨sub13_58, List.forall_mem_cons.2 ⟨sub13_59, List.forall_mem_cons.2 ⟨sub13_60, List.forall_mem_cons.2 ⟨sub13_61, List.forall_mem_cons.2 ⟨sub13_62, List.forall_mem_cons.2 ⟨sub13_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_64 : sub13 [-3, -2, 3] = true := by decide +kernel
theorem sub13_65 : sub13 [-3, -2, 4] = true := by decide +kernel
theorem sub13_66 : sub13 [-3, -2, 5] = true := by decide +kernel
theorem sub13_67 : sub13 [-3, -2, 6] = true := by decide +kernel
theorem sub13_68 : sub13 [-3, -1, -7] = true := by decide +kernel
theorem sub13_69 : sub13 [-3, -1, -6] = true := by decide +kernel
theorem sub13_70 : sub13 [-3, -1, -5] = true := by decide +kernel
theorem sub13_71 : sub13 [-3, -1, -4] = true := by decide +kernel
theorem sub13_72 : sub13 [-3, -1, -3] = true := by decide +kernel
theorem sub13_73 : sub13 [-3, -1, -2] = true := by decide +kernel
theorem sub13_74 : sub13 [-3, -1, -1] = true := by decide +kernel
theorem sub13_75 : sub13 [-3, -1, 0] = true := by decide +kernel
theorem sub13_76 : sub13 [-3, -1, 1] = true := by decide +kernel
theorem sub13_77 : sub13 [-3, -1, 2] = true := by decide +kernel
theorem sub13_78 : sub13 [-3, -1, 3] = true := by decide +kernel
theorem sub13_79 : sub13 [-3, -1, 4] = true := by decide +kernel
theorem sub13_80 : sub13 [-3, -1, 5] = true := by decide +kernel
theorem sub13_81 : sub13 [-3, -1, 6] = true := by decide +kernel
theorem sub13_82 : sub13 [-3, 0, -8] = true := by decide +kernel
theorem sub13_83 : sub13 [-3, 0, -7] = true := by decide +kernel
theorem sub13_84 : sub13 [-3, 0, -6] = true := by decide +kernel
theorem sub13_85 : sub13 [-3, 0, -5] = true := by decide +kernel
theorem sub13_86 : sub13 [-3, 0, -4] = true := by decide +kernel
theorem sub13_87 : sub13 [-3, 0, -3] = true := by decide +kernel
theorem sub13_88 : sub13 [-3, 0, -2] = true := by decide +kernel
theorem sub13_89 : sub13 [-3, 0, -1] = true := by decide +kernel
theorem sub13_90 : sub13 [-3, 0, 0] = true := by decide +kernel
theorem sub13_91 : sub13 [-3, 0, 1] = true := by decide +kernel
theorem sub13_92 : sub13 [-3, 0, 2] = true := by decide +kernel
theorem sub13_93 : sub13 [-3, 0, 3] = true := by decide +kernel
theorem sub13_94 : sub13 [-3, 0, 4] = true := by decide +kernel
theorem sub13_95 : sub13 [-3, 0, 5] = true := by decide +kernel
theorem sb13_2 : ∀ q ∈ blk13_2, sub13 q = true := by
  unfold blk13_2
  exact List.forall_mem_cons.2 ⟨sub13_64, List.forall_mem_cons.2 ⟨sub13_65, List.forall_mem_cons.2 ⟨sub13_66, List.forall_mem_cons.2 ⟨sub13_67, List.forall_mem_cons.2 ⟨sub13_68, List.forall_mem_cons.2 ⟨sub13_69, List.forall_mem_cons.2 ⟨sub13_70, List.forall_mem_cons.2 ⟨sub13_71, List.forall_mem_cons.2 ⟨sub13_72, List.forall_mem_cons.2 ⟨sub13_73, List.forall_mem_cons.2 ⟨sub13_74, List.forall_mem_cons.2 ⟨sub13_75, List.forall_mem_cons.2 ⟨sub13_76, List.forall_mem_cons.2 ⟨sub13_77, List.forall_mem_cons.2 ⟨sub13_78, List.forall_mem_cons.2 ⟨sub13_79, List.forall_mem_cons.2 ⟨sub13_80, List.forall_mem_cons.2 ⟨sub13_81, List.forall_mem_cons.2 ⟨sub13_82, List.forall_mem_cons.2 ⟨sub13_83, List.forall_mem_cons.2 ⟨sub13_84, List.forall_mem_cons.2 ⟨sub13_85, List.forall_mem_cons.2 ⟨sub13_86, List.forall_mem_cons.2 ⟨sub13_87, List.forall_mem_cons.2 ⟨sub13_88, List.forall_mem_cons.2 ⟨sub13_89, List.forall_mem_cons.2 ⟨sub13_90, List.forall_mem_cons.2 ⟨sub13_91, List.forall_mem_cons.2 ⟨sub13_92, List.forall_mem_cons.2 ⟨sub13_93, List.forall_mem_cons.2 ⟨sub13_94, List.forall_mem_cons.2 ⟨sub13_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_96 : sub13 [-3, 0, 6] = true := by decide +kernel
theorem sub13_97 : sub13 [-3, 1, -8] = true := by decide +kernel
theorem sub13_98 : sub13 [-3, 1, -7] = true := by decide +kernel
theorem sub13_99 : sub13 [-3, 1, -6] = true := by decide +kernel
theorem sub13_100 : sub13 [-3, 1, -5] = true := by decide +kernel
theorem sub13_101 : sub13 [-3, 1, -4] = true := by decide +kernel
theorem sub13_102 : sub13 [-3, 1, -3] = true := by decide +kernel
theorem sub13_103 : sub13 [-3, 1, -2] = true := by decide +kernel
theorem sub13_104 : sub13 [-3, 1, -1] = true := by decide +kernel
theorem sub13_105 : sub13 [-3, 1, 0] = true := by decide +kernel
theorem sub13_106 : sub13 [-3, 1, 1] = true := by decide +kernel
theorem sub13_107 : sub13 [-3, 1, 2] = true := by decide +kernel
theorem sub13_108 : sub13 [-3, 1, 3] = true := by decide +kernel
theorem sub13_109 : sub13 [-3, 1, 4] = true := by decide +kernel
theorem sub13_110 : sub13 [-3, 1, 5] = true := by decide +kernel
theorem sub13_111 : sub13 [-3, 1, 6] = true := by decide +kernel
theorem sub13_112 : sub13 [-3, 2, -8] = true := by decide +kernel
theorem sub13_113 : sub13 [-3, 2, -7] = true := by decide +kernel
theorem sub13_114 : sub13 [-3, 2, -6] = true := by decide +kernel
theorem sub13_115 : sub13 [-3, 2, -5] = true := by decide +kernel
theorem sub13_116 : sub13 [-3, 2, -4] = true := by decide +kernel
theorem sub13_117 : sub13 [-3, 2, -3] = true := by decide +kernel
theorem sub13_118 : sub13 [-3, 2, -2] = true := by decide +kernel
theorem sub13_119 : sub13 [-3, 2, -1] = true := by decide +kernel
theorem sub13_120 : sub13 [-3, 2, 0] = true := by decide +kernel
theorem sub13_121 : sub13 [-3, 2, 1] = true := by decide +kernel
theorem sub13_122 : sub13 [-3, 2, 2] = true := by decide +kernel
theorem sub13_123 : sub13 [-3, 2, 3] = true := by decide +kernel
theorem sub13_124 : sub13 [-3, 2, 4] = true := by decide +kernel
theorem sub13_125 : sub13 [-3, 2, 5] = true := by decide +kernel
theorem sub13_126 : sub13 [-3, 3, -8] = true := by decide +kernel
theorem sub13_127 : sub13 [-3, 3, -7] = true := by decide +kernel
theorem sb13_3 : ∀ q ∈ blk13_3, sub13 q = true := by
  unfold blk13_3
  exact List.forall_mem_cons.2 ⟨sub13_96, List.forall_mem_cons.2 ⟨sub13_97, List.forall_mem_cons.2 ⟨sub13_98, List.forall_mem_cons.2 ⟨sub13_99, List.forall_mem_cons.2 ⟨sub13_100, List.forall_mem_cons.2 ⟨sub13_101, List.forall_mem_cons.2 ⟨sub13_102, List.forall_mem_cons.2 ⟨sub13_103, List.forall_mem_cons.2 ⟨sub13_104, List.forall_mem_cons.2 ⟨sub13_105, List.forall_mem_cons.2 ⟨sub13_106, List.forall_mem_cons.2 ⟨sub13_107, List.forall_mem_cons.2 ⟨sub13_108, List.forall_mem_cons.2 ⟨sub13_109, List.forall_mem_cons.2 ⟨sub13_110, List.forall_mem_cons.2 ⟨sub13_111, List.forall_mem_cons.2 ⟨sub13_112, List.forall_mem_cons.2 ⟨sub13_113, List.forall_mem_cons.2 ⟨sub13_114, List.forall_mem_cons.2 ⟨sub13_115, List.forall_mem_cons.2 ⟨sub13_116, List.forall_mem_cons.2 ⟨sub13_117, List.forall_mem_cons.2 ⟨sub13_118, List.forall_mem_cons.2 ⟨sub13_119, List.forall_mem_cons.2 ⟨sub13_120, List.forall_mem_cons.2 ⟨sub13_121, List.forall_mem_cons.2 ⟨sub13_122, List.forall_mem_cons.2 ⟨sub13_123, List.forall_mem_cons.2 ⟨sub13_124, List.forall_mem_cons.2 ⟨sub13_125, List.forall_mem_cons.2 ⟨sub13_126, List.forall_mem_cons.2 ⟨sub13_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
