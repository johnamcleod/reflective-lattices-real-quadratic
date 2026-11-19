import ReflectZphi.Data.Cert5.C054.Base

namespace ReflectZphi.Data.Cert5.C054
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_480 : sub3 [1, 3, 0] = true := by decide +kernel
theorem sub3_481 : sub3 [1, 3, 1] = true := by decide +kernel
theorem sub3_482 : sub3 [1, 3, 2] = true := by decide +kernel
theorem sub3_483 : sub3 [1, 3, 3] = true := by decide +kernel
theorem sub3_484 : sub3 [1, 3, 4] = true := by decide +kernel
theorem sub3_485 : sub3 [1, 3, 5] = true := by decide +kernel
theorem sub3_486 : sub3 [1, 3, 6] = true := by decide +kernel
theorem sub3_487 : sub3 [1, 3, 7] = true := by decide +kernel
theorem sub3_488 : sub3 [1, 3, 8] = true := by decide +kernel
theorem sub3_489 : sub3 [1, 4] = true := by decide +kernel
theorem sub3_490 : sub3 [2, -5] = true := by decide +kernel
theorem sub3_491 : sub3 [2, -4] = true := by decide +kernel
theorem sub3_492 : sub3 [2, -3] = true := by decide +kernel
theorem sub3_493 : sub3 [2, -2, -8] = true := by decide +kernel
theorem sub3_494 : sub3 [2, -2, -7] = true := by decide +kernel
theorem sub3_495 : sub3 [2, -2, -6] = true := by decide +kernel
theorem sub3_496 : sub3 [2, -2, -5] = true := by decide +kernel
theorem sub3_497 : sub3 [2, -2, -4] = true := by decide +kernel
theorem sub3_498 : sub3 [2, -2, -3] = true := by decide +kernel
theorem sub3_499 : sub3 [2, -2, -2] = true := by decide +kernel
theorem sub3_500 : sub3 [2, -2, -1] = true := by decide +kernel
theorem sub3_501 : sub3 [2, -2, 0] = true := by decide +kernel
theorem sub3_502 : sub3 [2, -2, 1] = true := by decide +kernel
theorem sub3_503 : sub3 [2, -2, 2] = true := by decide +kernel
theorem sub3_504 : sub3 [2, -2, 3] = true := by decide +kernel
theorem sub3_505 : sub3 [2, -2, 4] = true := by decide +kernel
theorem sub3_506 : sub3 [2, -2, 5] = true := by decide +kernel
theorem sub3_507 : sub3 [2, -2, 6] = true := by decide +kernel
theorem sub3_508 : sub3 [2, -1, -8] = true := by decide +kernel
theorem sub3_509 : sub3 [2, -1, -7] = true := by decide +kernel
theorem sub3_510 : sub3 [2, -1, -6] = true := by decide +kernel
theorem sub3_511 : sub3 [2, -1, -5] = true := by decide +kernel
theorem sb3_15 : ∀ q ∈ blk3_15, sub3 q = true := by
  unfold blk3_15
  exact List.forall_mem_cons.2 ⟨sub3_480, List.forall_mem_cons.2 ⟨sub3_481, List.forall_mem_cons.2 ⟨sub3_482, List.forall_mem_cons.2 ⟨sub3_483, List.forall_mem_cons.2 ⟨sub3_484, List.forall_mem_cons.2 ⟨sub3_485, List.forall_mem_cons.2 ⟨sub3_486, List.forall_mem_cons.2 ⟨sub3_487, List.forall_mem_cons.2 ⟨sub3_488, List.forall_mem_cons.2 ⟨sub3_489, List.forall_mem_cons.2 ⟨sub3_490, List.forall_mem_cons.2 ⟨sub3_491, List.forall_mem_cons.2 ⟨sub3_492, List.forall_mem_cons.2 ⟨sub3_493, List.forall_mem_cons.2 ⟨sub3_494, List.forall_mem_cons.2 ⟨sub3_495, List.forall_mem_cons.2 ⟨sub3_496, List.forall_mem_cons.2 ⟨sub3_497, List.forall_mem_cons.2 ⟨sub3_498, List.forall_mem_cons.2 ⟨sub3_499, List.forall_mem_cons.2 ⟨sub3_500, List.forall_mem_cons.2 ⟨sub3_501, List.forall_mem_cons.2 ⟨sub3_502, List.forall_mem_cons.2 ⟨sub3_503, List.forall_mem_cons.2 ⟨sub3_504, List.forall_mem_cons.2 ⟨sub3_505, List.forall_mem_cons.2 ⟨sub3_506, List.forall_mem_cons.2 ⟨sub3_507, List.forall_mem_cons.2 ⟨sub3_508, List.forall_mem_cons.2 ⟨sub3_509, List.forall_mem_cons.2 ⟨sub3_510, List.forall_mem_cons.2 ⟨sub3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_512 : sub3 [2, -1, -4] = true := by decide +kernel
theorem sub3_513 : sub3 [2, -1, -3] = true := by decide +kernel
theorem sub3_514 : sub3 [2, -1, -2] = true := by decide +kernel
theorem sub3_515 : sub3 [2, -1, -1] = true := by decide +kernel
theorem sub3_516 : sub3 [2, -1, 0] = true := by decide +kernel
theorem sub3_517 : sub3 [2, -1, 1] = true := by decide +kernel
theorem sub3_518 : sub3 [2, -1, 2] = true := by decide +kernel
theorem sub3_519 : sub3 [2, -1, 3] = true := by decide +kernel
theorem sub3_520 : sub3 [2, -1, 4] = true := by decide +kernel
theorem sub3_521 : sub3 [2, -1, 5] = true := by decide +kernel
theorem sub3_522 : sub3 [2, -1, 6] = true := by decide +kernel
theorem sub3_523 : sub3 [2, -1, 7] = true := by decide +kernel
theorem sub3_524 : sub3 [2, 0, -8] = true := by decide +kernel
theorem sub3_525 : sub3 [2, 0, -7] = true := by decide +kernel
theorem sub3_526 : sub3 [2, 0, -6] = true := by decide +kernel
theorem sub3_527 : sub3 [2, 0, -5] = true := by decide +kernel
theorem sub3_528 : sub3 [2, 0, -4] = true := by decide +kernel
theorem sub3_529 : sub3 [2, 0, -3] = true := by decide +kernel
theorem sub3_530 : sub3 [2, 0, -2] = true := by decide +kernel
theorem sub3_531 : sub3 [2, 0, -1] = true := by decide +kernel
theorem sub3_532 : sub3 [2, 0, 0] = true := by decide +kernel
theorem sub3_533 : sub3 [2, 0, 1] = true := by decide +kernel
theorem sub3_534 : sub3 [2, 0, 2] = true := by decide +kernel
theorem sub3_535 : sub3 [2, 0, 3] = true := by decide +kernel
theorem sub3_536 : sub3 [2, 0, 4] = true := by decide +kernel
theorem sub3_537 : sub3 [2, 0, 5] = true := by decide +kernel
theorem sub3_538 : sub3 [2, 0, 6] = true := by decide +kernel
theorem sub3_539 : sub3 [2, 0, 7] = true := by decide +kernel
theorem sub3_540 : sub3 [2, 0, 8] = true := by decide +kernel
theorem sub3_541 : sub3 [2, 1, -7] = true := by decide +kernel
theorem sub3_542 : sub3 [2, 1, -6] = true := by decide +kernel
theorem sub3_543 : sub3 [2, 1, -5] = true := by decide +kernel
theorem sb3_16 : ∀ q ∈ blk3_16, sub3 q = true := by
  unfold blk3_16
  exact List.forall_mem_cons.2 ⟨sub3_512, List.forall_mem_cons.2 ⟨sub3_513, List.forall_mem_cons.2 ⟨sub3_514, List.forall_mem_cons.2 ⟨sub3_515, List.forall_mem_cons.2 ⟨sub3_516, List.forall_mem_cons.2 ⟨sub3_517, List.forall_mem_cons.2 ⟨sub3_518, List.forall_mem_cons.2 ⟨sub3_519, List.forall_mem_cons.2 ⟨sub3_520, List.forall_mem_cons.2 ⟨sub3_521, List.forall_mem_cons.2 ⟨sub3_522, List.forall_mem_cons.2 ⟨sub3_523, List.forall_mem_cons.2 ⟨sub3_524, List.forall_mem_cons.2 ⟨sub3_525, List.forall_mem_cons.2 ⟨sub3_526, List.forall_mem_cons.2 ⟨sub3_527, List.forall_mem_cons.2 ⟨sub3_528, List.forall_mem_cons.2 ⟨sub3_529, List.forall_mem_cons.2 ⟨sub3_530, List.forall_mem_cons.2 ⟨sub3_531, List.forall_mem_cons.2 ⟨sub3_532, List.forall_mem_cons.2 ⟨sub3_533, List.forall_mem_cons.2 ⟨sub3_534, List.forall_mem_cons.2 ⟨sub3_535, List.forall_mem_cons.2 ⟨sub3_536, List.forall_mem_cons.2 ⟨sub3_537, List.forall_mem_cons.2 ⟨sub3_538, List.forall_mem_cons.2 ⟨sub3_539, List.forall_mem_cons.2 ⟨sub3_540, List.forall_mem_cons.2 ⟨sub3_541, List.forall_mem_cons.2 ⟨sub3_542, List.forall_mem_cons.2 ⟨sub3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_544 : sub3 [2, 1, -4] = true := by decide +kernel
theorem sub3_545 : sub3 [2, 1, -3] = true := by decide +kernel
theorem sub3_546 : sub3 [2, 1, -2] = true := by decide +kernel
theorem sub3_547 : sub3 [2, 1, -1] = true := by decide +kernel
theorem sub3_548 : sub3 [2, 1, 0] = true := by decide +kernel
theorem sub3_549 : sub3 [2, 1, 1] = true := by decide +kernel
theorem sub3_550 : sub3 [2, 1, 2] = true := by decide +kernel
theorem sub3_551 : sub3 [2, 1, 3] = true := by decide +kernel
theorem sub3_552 : sub3 [2, 1, 4] = true := by decide +kernel
theorem sub3_553 : sub3 [2, 1, 5] = true := by decide +kernel
theorem sub3_554 : sub3 [2, 1, 6] = true := by decide +kernel
theorem sub3_555 : sub3 [2, 1, 7] = true := by decide +kernel
theorem sub3_556 : sub3 [2, 1, 8] = true := by decide +kernel
theorem sub3_557 : sub3 [2, 2, -6] = true := by decide +kernel
theorem sub3_558 : sub3 [2, 2, -5] = true := by decide +kernel
theorem sub3_559 : sub3 [2, 2, -4] = true := by decide +kernel
theorem sub3_560 : sub3 [2, 2, -3] = true := by decide +kernel
theorem sub3_561 : sub3 [2, 2, -2] = true := by decide +kernel
theorem sub3_562 : sub3 [2, 2, -1] = true := by decide +kernel
theorem sub3_563 : sub3 [2, 2, 0] = true := by decide +kernel
theorem sub3_564 : sub3 [2, 2, 1] = true := by decide +kernel
theorem sub3_565 : sub3 [2, 2, 2] = true := by decide +kernel
theorem sub3_566 : sub3 [2, 2, 3] = true := by decide +kernel
theorem sub3_567 : sub3 [2, 2, 4] = true := by decide +kernel
theorem sub3_568 : sub3 [2, 2, 5] = true := by decide +kernel
theorem sub3_569 : sub3 [2, 2, 6] = true := by decide +kernel
theorem sub3_570 : sub3 [2, 2, 7] = true := by decide +kernel
theorem sub3_571 : sub3 [2, 2, 8] = true := by decide +kernel
theorem sub3_572 : sub3 [2, 3] = true := by decide +kernel
theorem sub3_573 : sub3 [2, 4] = true := by decide +kernel
theorem sub3_574 : sub3 [3, -4] = true := by decide +kernel
theorem sub3_575 : sub3 [3, -3] = true := by decide +kernel
theorem sb3_17 : ∀ q ∈ blk3_17, sub3 q = true := by
  unfold blk3_17
  exact List.forall_mem_cons.2 ⟨sub3_544, List.forall_mem_cons.2 ⟨sub3_545, List.forall_mem_cons.2 ⟨sub3_546, List.forall_mem_cons.2 ⟨sub3_547, List.forall_mem_cons.2 ⟨sub3_548, List.forall_mem_cons.2 ⟨sub3_549, List.forall_mem_cons.2 ⟨sub3_550, List.forall_mem_cons.2 ⟨sub3_551, List.forall_mem_cons.2 ⟨sub3_552, List.forall_mem_cons.2 ⟨sub3_553, List.forall_mem_cons.2 ⟨sub3_554, List.forall_mem_cons.2 ⟨sub3_555, List.forall_mem_cons.2 ⟨sub3_556, List.forall_mem_cons.2 ⟨sub3_557, List.forall_mem_cons.2 ⟨sub3_558, List.forall_mem_cons.2 ⟨sub3_559, List.forall_mem_cons.2 ⟨sub3_560, List.forall_mem_cons.2 ⟨sub3_561, List.forall_mem_cons.2 ⟨sub3_562, List.forall_mem_cons.2 ⟨sub3_563, List.forall_mem_cons.2 ⟨sub3_564, List.forall_mem_cons.2 ⟨sub3_565, List.forall_mem_cons.2 ⟨sub3_566, List.forall_mem_cons.2 ⟨sub3_567, List.forall_mem_cons.2 ⟨sub3_568, List.forall_mem_cons.2 ⟨sub3_569, List.forall_mem_cons.2 ⟨sub3_570, List.forall_mem_cons.2 ⟨sub3_571, List.forall_mem_cons.2 ⟨sub3_572, List.forall_mem_cons.2 ⟨sub3_573, List.forall_mem_cons.2 ⟨sub3_574, List.forall_mem_cons.2 ⟨sub3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_576 : sub3 [3, -2] = true := by decide +kernel
theorem sub3_577 : sub3 [3, -1, -6] = true := by decide +kernel
theorem sub3_578 : sub3 [3, -1, -5] = true := by decide +kernel
theorem sub3_579 : sub3 [3, -1, -4] = true := by decide +kernel
theorem sub3_580 : sub3 [3, -1, -3] = true := by decide +kernel
theorem sub3_581 : sub3 [3, -1, -2] = true := by decide +kernel
theorem sub3_582 : sub3 [3, -1, -1] = true := by decide +kernel
theorem sub3_583 : sub3 [3, -1, 0] = true := by decide +kernel
theorem sub3_584 : sub3 [3, -1, 1] = true := by decide +kernel
theorem sub3_585 : sub3 [3, -1, 2] = true := by decide +kernel
theorem sub3_586 : sub3 [3, -1, 3] = true := by decide +kernel
theorem sub3_587 : sub3 [3, -1, 4] = true := by decide +kernel
theorem sub3_588 : sub3 [3, -1, 5] = true := by decide +kernel
theorem sub3_589 : sub3 [3, -1, 6] = true := by decide +kernel
theorem sub3_590 : sub3 [3, -1, 7] = true := by decide +kernel
theorem sub3_591 : sub3 [3, 0, -6] = true := by decide +kernel
theorem sub3_592 : sub3 [3, 0, -5] = true := by decide +kernel
theorem sub3_593 : sub3 [3, 0, -4] = true := by decide +kernel
theorem sub3_594 : sub3 [3, 0, -3] = true := by decide +kernel
theorem sub3_595 : sub3 [3, 0, -2] = true := by decide +kernel
theorem sub3_596 : sub3 [3, 0, -1] = true := by decide +kernel
theorem sub3_597 : sub3 [3, 0, 0] = true := by decide +kernel
theorem sub3_598 : sub3 [3, 0, 1] = true := by decide +kernel
theorem sub3_599 : sub3 [3, 0, 2] = true := by decide +kernel
theorem sub3_600 : sub3 [3, 0, 3] = true := by decide +kernel
theorem sub3_601 : sub3 [3, 0, 4] = true := by decide +kernel
theorem sub3_602 : sub3 [3, 0, 5] = true := by decide +kernel
theorem sub3_603 : sub3 [3, 0, 6] = true := by decide +kernel
theorem sub3_604 : sub3 [3, 0, 7] = true := by decide +kernel
theorem sub3_605 : sub3 [3, 1, -6] = true := by decide +kernel
theorem sub3_606 : sub3 [3, 1, -5] = true := by decide +kernel
theorem sub3_607 : sub3 [3, 1, -4] = true := by decide +kernel
theorem sb3_18 : ∀ q ∈ blk3_18, sub3 q = true := by
  unfold blk3_18
  exact List.forall_mem_cons.2 ⟨sub3_576, List.forall_mem_cons.2 ⟨sub3_577, List.forall_mem_cons.2 ⟨sub3_578, List.forall_mem_cons.2 ⟨sub3_579, List.forall_mem_cons.2 ⟨sub3_580, List.forall_mem_cons.2 ⟨sub3_581, List.forall_mem_cons.2 ⟨sub3_582, List.forall_mem_cons.2 ⟨sub3_583, List.forall_mem_cons.2 ⟨sub3_584, List.forall_mem_cons.2 ⟨sub3_585, List.forall_mem_cons.2 ⟨sub3_586, List.forall_mem_cons.2 ⟨sub3_587, List.forall_mem_cons.2 ⟨sub3_588, List.forall_mem_cons.2 ⟨sub3_589, List.forall_mem_cons.2 ⟨sub3_590, List.forall_mem_cons.2 ⟨sub3_591, List.forall_mem_cons.2 ⟨sub3_592, List.forall_mem_cons.2 ⟨sub3_593, List.forall_mem_cons.2 ⟨sub3_594, List.forall_mem_cons.2 ⟨sub3_595, List.forall_mem_cons.2 ⟨sub3_596, List.forall_mem_cons.2 ⟨sub3_597, List.forall_mem_cons.2 ⟨sub3_598, List.forall_mem_cons.2 ⟨sub3_599, List.forall_mem_cons.2 ⟨sub3_600, List.forall_mem_cons.2 ⟨sub3_601, List.forall_mem_cons.2 ⟨sub3_602, List.forall_mem_cons.2 ⟨sub3_603, List.forall_mem_cons.2 ⟨sub3_604, List.forall_mem_cons.2 ⟨sub3_605, List.forall_mem_cons.2 ⟨sub3_606, List.forall_mem_cons.2 ⟨sub3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_608 : sub3 [3, 1, -3] = true := by decide +kernel
theorem sub3_609 : sub3 [3, 1, -2] = true := by decide +kernel
theorem sub3_610 : sub3 [3, 1, -1] = true := by decide +kernel
theorem sub3_611 : sub3 [3, 1, 0] = true := by decide +kernel
theorem sub3_612 : sub3 [3, 1, 1] = true := by decide +kernel
theorem sub3_613 : sub3 [3, 1, 2] = true := by decide +kernel
theorem sub3_614 : sub3 [3, 1, 3] = true := by decide +kernel
theorem sub3_615 : sub3 [3, 1, 4] = true := by decide +kernel
theorem sub3_616 : sub3 [3, 1, 5] = true := by decide +kernel
theorem sub3_617 : sub3 [3, 1, 6] = true := by decide +kernel
theorem sub3_618 : sub3 [3, 1, 7] = true := by decide +kernel
theorem sub3_619 : sub3 [3, 2] = true := by decide +kernel
theorem sub3_620 : sub3 [3, 3] = true := by decide +kernel
theorem sub3_621 : sub3 [3, 4] = true := by decide +kernel
theorem sub3_622 : sub3 [4, -3] = true := by decide +kernel
theorem sub3_623 : sub3 [4, -2] = true := by decide +kernel
theorem sub3_624 : sub3 [4, -1] = true := by decide +kernel
theorem sub3_625 : sub3 [4, 0] = true := by decide +kernel
theorem sub3_626 : sub3 [4, 1] = true := by decide +kernel
theorem sub3_627 : sub3 [4, 2] = true := by decide +kernel
theorem sub3_628 : sub3 [4, 3] = true := by decide +kernel
theorem sb3_19 : ∀ q ∈ blk3_19, sub3 q = true := by
  unfold blk3_19
  exact List.forall_mem_cons.2 ⟨sub3_608, List.forall_mem_cons.2 ⟨sub3_609, List.forall_mem_cons.2 ⟨sub3_610, List.forall_mem_cons.2 ⟨sub3_611, List.forall_mem_cons.2 ⟨sub3_612, List.forall_mem_cons.2 ⟨sub3_613, List.forall_mem_cons.2 ⟨sub3_614, List.forall_mem_cons.2 ⟨sub3_615, List.forall_mem_cons.2 ⟨sub3_616, List.forall_mem_cons.2 ⟨sub3_617, List.forall_mem_cons.2 ⟨sub3_618, List.forall_mem_cons.2 ⟨sub3_619, List.forall_mem_cons.2 ⟨sub3_620, List.forall_mem_cons.2 ⟨sub3_621, List.forall_mem_cons.2 ⟨sub3_622, List.forall_mem_cons.2 ⟨sub3_623, List.forall_mem_cons.2 ⟨sub3_624, List.forall_mem_cons.2 ⟨sub3_625, List.forall_mem_cons.2 ⟨sub3_626, List.forall_mem_cons.2 ⟨sub3_627, List.forall_mem_cons.2 ⟨sub3_628, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_0 : sub4 [-5] = true := by decide +kernel
theorem sub4_1 : sub4 [-4, -2] = true := by decide +kernel
theorem sub4_2 : sub4 [-4, -1] = true := by decide +kernel
theorem sub4_3 : sub4 [-4, 0] = true := by decide +kernel
theorem sub4_4 : sub4 [-4, 1] = true := by decide +kernel
theorem sub4_5 : sub4 [-4, 2] = true := by decide +kernel
theorem sub4_6 : sub4 [-4, 3] = true := by decide +kernel
theorem sub4_7 : sub4 [-4, 4] = true := by decide +kernel
theorem sub4_8 : sub4 [-4, 5] = true := by decide +kernel
theorem sub4_9 : sub4 [-3, -4] = true := by decide +kernel
theorem sub4_10 : sub4 [-3, -3] = true := by decide +kernel
theorem sub4_11 : sub4 [-3, -2] = true := by decide +kernel
theorem sub4_12 : sub4 [-3, -1] = true := by decide +kernel
theorem sub4_13 : sub4 [-3, 0] = true := by decide +kernel
theorem sub4_14 : sub4 [-3, 1] = true := by decide +kernel
theorem sub4_15 : sub4 [-3, 2] = true := by decide +kernel
theorem sub4_16 : sub4 [-3, 3] = true := by decide +kernel
theorem sub4_17 : sub4 [-3, 4] = true := by decide +kernel
theorem sub4_18 : sub4 [-3, 5] = true := by decide +kernel
theorem sub4_19 : sub4 [-3, 6] = true := by decide +kernel
theorem sub4_20 : sub4 [-2, -5] = true := by decide +kernel
theorem sub4_21 : sub4 [-2, -4] = true := by decide +kernel
theorem sub4_22 : sub4 [-2, -3] = true := by decide +kernel
theorem sub4_23 : sub4 [-2, -2] = true := by decide +kernel
theorem sub4_24 : sub4 [-2, -1] = true := by decide +kernel
theorem sub4_25 : sub4 [-2, 0] = true := by decide +kernel
theorem sub4_26 : sub4 [-2, 1] = true := by decide +kernel
theorem sub4_27 : sub4 [-2, 2] = true := by decide +kernel
theorem sub4_28 : sub4 [-2, 3] = true := by decide +kernel
theorem sub4_29 : sub4 [-2, 4] = true := by decide +kernel
theorem sub4_30 : sub4 [-2, 5] = true := by decide +kernel
theorem sub4_31 : sub4 [-2, 6] = true := by decide +kernel
theorem sb4_0 : ∀ q ∈ blk4_0, sub4 q = true := by
  unfold blk4_0
  exact List.forall_mem_cons.2 ⟨sub4_0, List.forall_mem_cons.2 ⟨sub4_1, List.forall_mem_cons.2 ⟨sub4_2, List.forall_mem_cons.2 ⟨sub4_3, List.forall_mem_cons.2 ⟨sub4_4, List.forall_mem_cons.2 ⟨sub4_5, List.forall_mem_cons.2 ⟨sub4_6, List.forall_mem_cons.2 ⟨sub4_7, List.forall_mem_cons.2 ⟨sub4_8, List.forall_mem_cons.2 ⟨sub4_9, List.forall_mem_cons.2 ⟨sub4_10, List.forall_mem_cons.2 ⟨sub4_11, List.forall_mem_cons.2 ⟨sub4_12, List.forall_mem_cons.2 ⟨sub4_13, List.forall_mem_cons.2 ⟨sub4_14, List.forall_mem_cons.2 ⟨sub4_15, List.forall_mem_cons.2 ⟨sub4_16, List.forall_mem_cons.2 ⟨sub4_17, List.forall_mem_cons.2 ⟨sub4_18, List.forall_mem_cons.2 ⟨sub4_19, List.forall_mem_cons.2 ⟨sub4_20, List.forall_mem_cons.2 ⟨sub4_21, List.forall_mem_cons.2 ⟨sub4_22, List.forall_mem_cons.2 ⟨sub4_23, List.forall_mem_cons.2 ⟨sub4_24, List.forall_mem_cons.2 ⟨sub4_25, List.forall_mem_cons.2 ⟨sub4_26, List.forall_mem_cons.2 ⟨sub4_27, List.forall_mem_cons.2 ⟨sub4_28, List.forall_mem_cons.2 ⟨sub4_29, List.forall_mem_cons.2 ⟨sub4_30, List.forall_mem_cons.2 ⟨sub4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_32 : sub4 [-1, -5] = true := by decide +kernel
theorem sub4_33 : sub4 [-1, -4] = true := by decide +kernel
theorem sub4_34 : sub4 [-1, -3] = true := by decide +kernel
theorem sub4_35 : sub4 [-1, -2] = true := by decide +kernel
theorem sub4_36 : sub4 [-1, -1] = true := by decide +kernel
theorem sub4_37 : sub4 [-1, 0] = true := by decide +kernel
theorem sub4_38 : sub4 [-1, 1] = true := by decide +kernel
theorem sub4_39 : sub4 [-1, 2] = true := by decide +kernel
theorem sub4_40 : sub4 [-1, 3] = true := by decide +kernel
theorem sub4_41 : sub4 [-1, 4] = true := by decide +kernel
theorem sub4_42 : sub4 [-1, 5] = true := by decide +kernel
theorem sub4_43 : sub4 [0, -6] = true := by decide +kernel
theorem sub4_44 : sub4 [0, -5] = true := by decide +kernel
theorem sub4_45 : sub4 [0, -4] = true := by decide +kernel
theorem sub4_46 : sub4 [0, -3] = true := by decide +kernel
theorem sub4_47 : sub4 [0, -2] = true := by decide +kernel
theorem sub4_48 : sub4 [0, -1] = true := by decide +kernel
theorem sub4_49 : sub4 [0, 0] = true := by decide +kernel
theorem sub4_50 : sub4 [0, 1] = true := by decide +kernel
theorem sub4_51 : sub4 [0, 2] = true := by decide +kernel
theorem sub4_52 : sub4 [0, 3] = true := by decide +kernel
theorem sub4_53 : sub4 [0, 4] = true := by decide +kernel
theorem sub4_54 : sub4 [0, 5] = true := by decide +kernel
theorem sub4_55 : sub4 [1, -6] = true := by decide +kernel
theorem sub4_56 : sub4 [1, -5] = true := by decide +kernel
theorem sub4_57 : sub4 [1, -4] = true := by decide +kernel
theorem sub4_58 : sub4 [1, -3] = true := by decide +kernel
theorem sub4_59 : sub4 [1, -2] = true := by decide +kernel
theorem sub4_60 : sub4 [1, -1] = true := by decide +kernel
theorem sub4_61 : sub4 [1, 0] = true := by decide +kernel
theorem sub4_62 : sub4 [1, 1] = true := by decide +kernel
theorem sub4_63 : sub4 [1, 2] = true := by decide +kernel
theorem sb4_1 : ∀ q ∈ blk4_1, sub4 q = true := by
  unfold blk4_1
  exact List.forall_mem_cons.2 ⟨sub4_32, List.forall_mem_cons.2 ⟨sub4_33, List.forall_mem_cons.2 ⟨sub4_34, List.forall_mem_cons.2 ⟨sub4_35, List.forall_mem_cons.2 ⟨sub4_36, List.forall_mem_cons.2 ⟨sub4_37, List.forall_mem_cons.2 ⟨sub4_38, List.forall_mem_cons.2 ⟨sub4_39, List.forall_mem_cons.2 ⟨sub4_40, List.forall_mem_cons.2 ⟨sub4_41, List.forall_mem_cons.2 ⟨sub4_42, List.forall_mem_cons.2 ⟨sub4_43, List.forall_mem_cons.2 ⟨sub4_44, List.forall_mem_cons.2 ⟨sub4_45, List.forall_mem_cons.2 ⟨sub4_46, List.forall_mem_cons.2 ⟨sub4_47, List.forall_mem_cons.2 ⟨sub4_48, List.forall_mem_cons.2 ⟨sub4_49, List.forall_mem_cons.2 ⟨sub4_50, List.forall_mem_cons.2 ⟨sub4_51, List.forall_mem_cons.2 ⟨sub4_52, List.forall_mem_cons.2 ⟨sub4_53, List.forall_mem_cons.2 ⟨sub4_54, List.forall_mem_cons.2 ⟨sub4_55, List.forall_mem_cons.2 ⟨sub4_56, List.forall_mem_cons.2 ⟨sub4_57, List.forall_mem_cons.2 ⟨sub4_58, List.forall_mem_cons.2 ⟨sub4_59, List.forall_mem_cons.2 ⟨sub4_60, List.forall_mem_cons.2 ⟨sub4_61, List.forall_mem_cons.2 ⟨sub4_62, List.forall_mem_cons.2 ⟨sub4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C054
