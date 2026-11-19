import ReflectZphi.Data.Cert5.C083.Base

namespace ReflectZphi.Data.Cert5.C083
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_480 : sub7 [1, 2, 4] = true := by decide +kernel
theorem sub7_481 : sub7 [1, 2, 5] = true := by decide +kernel
theorem sub7_482 : sub7 [1, 3, -8] = true := by decide +kernel
theorem sub7_483 : sub7 [1, 3, -7] = true := by decide +kernel
theorem sub7_484 : sub7 [1, 3, -6] = true := by decide +kernel
theorem sub7_485 : sub7 [1, 3, -5] = true := by decide +kernel
theorem sub7_486 : sub7 [1, 3, -4] = true := by decide +kernel
theorem sub7_487 : sub7 [1, 3, -3] = true := by decide +kernel
theorem sub7_488 : sub7 [1, 3, -2] = true := by decide +kernel
theorem sub7_489 : sub7 [1, 3, -1] = true := by decide +kernel
theorem sub7_490 : sub7 [1, 3, 0] = true := by decide +kernel
theorem sub7_491 : sub7 [1, 3, 1] = true := by decide +kernel
theorem sub7_492 : sub7 [1, 3, 2] = true := by decide +kernel
theorem sub7_493 : sub7 [1, 3, 3] = true := by decide +kernel
theorem sub7_494 : sub7 [1, 3, 4] = true := by decide +kernel
theorem sub7_495 : sub7 [1, 4] = true := by decide +kernel
theorem sub7_496 : sub7 [1, 5] = true := by decide +kernel
theorem sub7_497 : sub7 [1, 6] = true := by decide +kernel
theorem sub7_498 : sub7 [2, -8] = true := by decide +kernel
theorem sub7_499 : sub7 [2, -7] = true := by decide +kernel
theorem sub7_500 : sub7 [2, -6] = true := by decide +kernel
theorem sub7_501 : sub7 [2, -5] = true := by decide +kernel
theorem sub7_502 : sub7 [2, -4] = true := by decide +kernel
theorem sub7_503 : sub7 [2, -3, -7] = true := by decide +kernel
theorem sub7_504 : sub7 [2, -3, -6] = true := by decide +kernel
theorem sub7_505 : sub7 [2, -3, -5] = true := by decide +kernel
theorem sub7_506 : sub7 [2, -3, -4] = true := by decide +kernel
theorem sub7_507 : sub7 [2, -3, -3] = true := by decide +kernel
theorem sub7_508 : sub7 [2, -3, -2] = true := by decide +kernel
theorem sub7_509 : sub7 [2, -3, -1] = true := by decide +kernel
theorem sub7_510 : sub7 [2, -3, 0] = true := by decide +kernel
theorem sub7_511 : sub7 [2, -3, 1] = true := by decide +kernel
theorem sb7_15 : ∀ q ∈ blk7_15, sub7 q = true := by
  unfold blk7_15
  exact List.forall_mem_cons.2 ⟨sub7_480, List.forall_mem_cons.2 ⟨sub7_481, List.forall_mem_cons.2 ⟨sub7_482, List.forall_mem_cons.2 ⟨sub7_483, List.forall_mem_cons.2 ⟨sub7_484, List.forall_mem_cons.2 ⟨sub7_485, List.forall_mem_cons.2 ⟨sub7_486, List.forall_mem_cons.2 ⟨sub7_487, List.forall_mem_cons.2 ⟨sub7_488, List.forall_mem_cons.2 ⟨sub7_489, List.forall_mem_cons.2 ⟨sub7_490, List.forall_mem_cons.2 ⟨sub7_491, List.forall_mem_cons.2 ⟨sub7_492, List.forall_mem_cons.2 ⟨sub7_493, List.forall_mem_cons.2 ⟨sub7_494, List.forall_mem_cons.2 ⟨sub7_495, List.forall_mem_cons.2 ⟨sub7_496, List.forall_mem_cons.2 ⟨sub7_497, List.forall_mem_cons.2 ⟨sub7_498, List.forall_mem_cons.2 ⟨sub7_499, List.forall_mem_cons.2 ⟨sub7_500, List.forall_mem_cons.2 ⟨sub7_501, List.forall_mem_cons.2 ⟨sub7_502, List.forall_mem_cons.2 ⟨sub7_503, List.forall_mem_cons.2 ⟨sub7_504, List.forall_mem_cons.2 ⟨sub7_505, List.forall_mem_cons.2 ⟨sub7_506, List.forall_mem_cons.2 ⟨sub7_507, List.forall_mem_cons.2 ⟨sub7_508, List.forall_mem_cons.2 ⟨sub7_509, List.forall_mem_cons.2 ⟨sub7_510, List.forall_mem_cons.2 ⟨sub7_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_512 : sub7 [2, -3, 2] = true := by decide +kernel
theorem sub7_513 : sub7 [2, -3, 3] = true := by decide +kernel
theorem sub7_514 : sub7 [2, -3, 4] = true := by decide +kernel
theorem sub7_515 : sub7 [2, -3, 5] = true := by decide +kernel
theorem sub7_516 : sub7 [2, -3, 6] = true := by decide +kernel
theorem sub7_517 : sub7 [2, -2, -7] = true := by decide +kernel
theorem sub7_518 : sub7 [2, -2, -6] = true := by decide +kernel
theorem sub7_519 : sub7 [2, -2, -5] = true := by decide +kernel
theorem sub7_520 : sub7 [2, -2, -4] = true := by decide +kernel
theorem sub7_521 : sub7 [2, -2, -3] = true := by decide +kernel
theorem sub7_522 : sub7 [2, -2, -2] = true := by decide +kernel
theorem sub7_523 : sub7 [2, -2, -1] = true := by decide +kernel
theorem sub7_524 : sub7 [2, -2, 0] = true := by decide +kernel
theorem sub7_525 : sub7 [2, -2, 1] = true := by decide +kernel
theorem sub7_526 : sub7 [2, -2, 2] = true := by decide +kernel
theorem sub7_527 : sub7 [2, -2, 3] = true := by decide +kernel
theorem sub7_528 : sub7 [2, -2, 4] = true := by decide +kernel
theorem sub7_529 : sub7 [2, -2, 5] = true := by decide +kernel
theorem sub7_530 : sub7 [2, -2, 6] = true := by decide +kernel
theorem sub7_531 : sub7 [2, -1, -8] = true := by decide +kernel
theorem sub7_532 : sub7 [2, -1, -7] = true := by decide +kernel
theorem sub7_533 : sub7 [2, -1, -6] = true := by decide +kernel
theorem sub7_534 : sub7 [2, -1, -5] = true := by decide +kernel
theorem sub7_535 : sub7 [2, -1, -4] = true := by decide +kernel
theorem sub7_536 : sub7 [2, -1, -3] = true := by decide +kernel
theorem sub7_537 : sub7 [2, -1, -2] = true := by decide +kernel
theorem sub7_538 : sub7 [2, -1, -1] = true := by decide +kernel
theorem sub7_539 : sub7 [2, -1, 0] = true := by decide +kernel
theorem sub7_540 : sub7 [2, -1, 1] = true := by decide +kernel
theorem sub7_541 : sub7 [2, -1, 2] = true := by decide +kernel
theorem sub7_542 : sub7 [2, -1, 3] = true := by decide +kernel
theorem sub7_543 : sub7 [2, -1, 4] = true := by decide +kernel
theorem sb7_16 : ∀ q ∈ blk7_16, sub7 q = true := by
  unfold blk7_16
  exact List.forall_mem_cons.2 ⟨sub7_512, List.forall_mem_cons.2 ⟨sub7_513, List.forall_mem_cons.2 ⟨sub7_514, List.forall_mem_cons.2 ⟨sub7_515, List.forall_mem_cons.2 ⟨sub7_516, List.forall_mem_cons.2 ⟨sub7_517, List.forall_mem_cons.2 ⟨sub7_518, List.forall_mem_cons.2 ⟨sub7_519, List.forall_mem_cons.2 ⟨sub7_520, List.forall_mem_cons.2 ⟨sub7_521, List.forall_mem_cons.2 ⟨sub7_522, List.forall_mem_cons.2 ⟨sub7_523, List.forall_mem_cons.2 ⟨sub7_524, List.forall_mem_cons.2 ⟨sub7_525, List.forall_mem_cons.2 ⟨sub7_526, List.forall_mem_cons.2 ⟨sub7_527, List.forall_mem_cons.2 ⟨sub7_528, List.forall_mem_cons.2 ⟨sub7_529, List.forall_mem_cons.2 ⟨sub7_530, List.forall_mem_cons.2 ⟨sub7_531, List.forall_mem_cons.2 ⟨sub7_532, List.forall_mem_cons.2 ⟨sub7_533, List.forall_mem_cons.2 ⟨sub7_534, List.forall_mem_cons.2 ⟨sub7_535, List.forall_mem_cons.2 ⟨sub7_536, List.forall_mem_cons.2 ⟨sub7_537, List.forall_mem_cons.2 ⟨sub7_538, List.forall_mem_cons.2 ⟨sub7_539, List.forall_mem_cons.2 ⟨sub7_540, List.forall_mem_cons.2 ⟨sub7_541, List.forall_mem_cons.2 ⟨sub7_542, List.forall_mem_cons.2 ⟨sub7_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_544 : sub7 [2, -1, 5] = true := by decide +kernel
theorem sub7_545 : sub7 [2, -1, 6] = true := by decide +kernel
theorem sub7_546 : sub7 [2, 0, -8] = true := by decide +kernel
theorem sub7_547 : sub7 [2, 0, -7] = true := by decide +kernel
theorem sub7_548 : sub7 [2, 0, -6] = true := by decide +kernel
theorem sub7_549 : sub7 [2, 0, -5] = true := by decide +kernel
theorem sub7_550 : sub7 [2, 0, -4] = true := by decide +kernel
theorem sub7_551 : sub7 [2, 0, -3] = true := by decide +kernel
theorem sub7_552 : sub7 [2, 0, -2] = true := by decide +kernel
theorem sub7_553 : sub7 [2, 0, -1] = true := by decide +kernel
theorem sub7_554 : sub7 [2, 0, 0] = true := by decide +kernel
theorem sub7_555 : sub7 [2, 0, 1] = true := by decide +kernel
theorem sub7_556 : sub7 [2, 0, 2] = true := by decide +kernel
theorem sub7_557 : sub7 [2, 0, 3] = true := by decide +kernel
theorem sub7_558 : sub7 [2, 0, 4] = true := by decide +kernel
theorem sub7_559 : sub7 [2, 0, 5] = true := by decide +kernel
theorem sub7_560 : sub7 [2, 0, 6] = true := by decide +kernel
theorem sub7_561 : sub7 [2, 1, -8] = true := by decide +kernel
theorem sub7_562 : sub7 [2, 1, -7] = true := by decide +kernel
theorem sub7_563 : sub7 [2, 1, -6] = true := by decide +kernel
theorem sub7_564 : sub7 [2, 1, -5] = true := by decide +kernel
theorem sub7_565 : sub7 [2, 1, -4] = true := by decide +kernel
theorem sub7_566 : sub7 [2, 1, -3] = true := by decide +kernel
theorem sub7_567 : sub7 [2, 1, -2] = true := by decide +kernel
theorem sub7_568 : sub7 [2, 1, -1] = true := by decide +kernel
theorem sub7_569 : sub7 [2, 1, 0] = true := by decide +kernel
theorem sub7_570 : sub7 [2, 1, 1] = true := by decide +kernel
theorem sub7_571 : sub7 [2, 1, 2] = true := by decide +kernel
theorem sub7_572 : sub7 [2, 1, 3] = true := by decide +kernel
theorem sub7_573 : sub7 [2, 1, 4] = true := by decide +kernel
theorem sub7_574 : sub7 [2, 1, 5] = true := by decide +kernel
theorem sub7_575 : sub7 [2, 2, -8] = true := by decide +kernel
theorem sb7_17 : ∀ q ∈ blk7_17, sub7 q = true := by
  unfold blk7_17
  exact List.forall_mem_cons.2 ⟨sub7_544, List.forall_mem_cons.2 ⟨sub7_545, List.forall_mem_cons.2 ⟨sub7_546, List.forall_mem_cons.2 ⟨sub7_547, List.forall_mem_cons.2 ⟨sub7_548, List.forall_mem_cons.2 ⟨sub7_549, List.forall_mem_cons.2 ⟨sub7_550, List.forall_mem_cons.2 ⟨sub7_551, List.forall_mem_cons.2 ⟨sub7_552, List.forall_mem_cons.2 ⟨sub7_553, List.forall_mem_cons.2 ⟨sub7_554, List.forall_mem_cons.2 ⟨sub7_555, List.forall_mem_cons.2 ⟨sub7_556, List.forall_mem_cons.2 ⟨sub7_557, List.forall_mem_cons.2 ⟨sub7_558, List.forall_mem_cons.2 ⟨sub7_559, List.forall_mem_cons.2 ⟨sub7_560, List.forall_mem_cons.2 ⟨sub7_561, List.forall_mem_cons.2 ⟨sub7_562, List.forall_mem_cons.2 ⟨sub7_563, List.forall_mem_cons.2 ⟨sub7_564, List.forall_mem_cons.2 ⟨sub7_565, List.forall_mem_cons.2 ⟨sub7_566, List.forall_mem_cons.2 ⟨sub7_567, List.forall_mem_cons.2 ⟨sub7_568, List.forall_mem_cons.2 ⟨sub7_569, List.forall_mem_cons.2 ⟨sub7_570, List.forall_mem_cons.2 ⟨sub7_571, List.forall_mem_cons.2 ⟨sub7_572, List.forall_mem_cons.2 ⟨sub7_573, List.forall_mem_cons.2 ⟨sub7_574, List.forall_mem_cons.2 ⟨sub7_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_576 : sub7 [2, 2, -7] = true := by decide +kernel
theorem sub7_577 : sub7 [2, 2, -6] = true := by decide +kernel
theorem sub7_578 : sub7 [2, 2, -5] = true := by decide +kernel
theorem sub7_579 : sub7 [2, 2, -4] = true := by decide +kernel
theorem sub7_580 : sub7 [2, 2, -3] = true := by decide +kernel
theorem sub7_581 : sub7 [2, 2, -2] = true := by decide +kernel
theorem sub7_582 : sub7 [2, 2, -1] = true := by decide +kernel
theorem sub7_583 : sub7 [2, 2, 0] = true := by decide +kernel
theorem sub7_584 : sub7 [2, 2, 1] = true := by decide +kernel
theorem sub7_585 : sub7 [2, 2, 2] = true := by decide +kernel
theorem sub7_586 : sub7 [2, 2, 3] = true := by decide +kernel
theorem sub7_587 : sub7 [2, 2, 4] = true := by decide +kernel
theorem sub7_588 : sub7 [2, 3] = true := by decide +kernel
theorem sub7_589 : sub7 [2, 4] = true := by decide +kernel
theorem sub7_590 : sub7 [2, 5] = true := by decide +kernel
theorem sub7_591 : sub7 [3, -8] = true := by decide +kernel
theorem sub7_592 : sub7 [3, -7] = true := by decide +kernel
theorem sub7_593 : sub7 [3, -6] = true := by decide +kernel
theorem sub7_594 : sub7 [3, -5] = true := by decide +kernel
theorem sub7_595 : sub7 [3, -4] = true := by decide +kernel
theorem sub7_596 : sub7 [3, -3] = true := by decide +kernel
theorem sub7_597 : sub7 [3, -2, -7] = true := by decide +kernel
theorem sub7_598 : sub7 [3, -2, -6] = true := by decide +kernel
theorem sub7_599 : sub7 [3, -2, -5] = true := by decide +kernel
theorem sub7_600 : sub7 [3, -2, -4] = true := by decide +kernel
theorem sub7_601 : sub7 [3, -2, -3] = true := by decide +kernel
theorem sub7_602 : sub7 [3, -2, -2] = true := by decide +kernel
theorem sub7_603 : sub7 [3, -2, -1] = true := by decide +kernel
theorem sub7_604 : sub7 [3, -2, 0] = true := by decide +kernel
theorem sub7_605 : sub7 [3, -2, 1] = true := by decide +kernel
theorem sub7_606 : sub7 [3, -2, 2] = true := by decide +kernel
theorem sub7_607 : sub7 [3, -2, 3] = true := by decide +kernel
theorem sb7_18 : ∀ q ∈ blk7_18, sub7 q = true := by
  unfold blk7_18
  exact List.forall_mem_cons.2 ⟨sub7_576, List.forall_mem_cons.2 ⟨sub7_577, List.forall_mem_cons.2 ⟨sub7_578, List.forall_mem_cons.2 ⟨sub7_579, List.forall_mem_cons.2 ⟨sub7_580, List.forall_mem_cons.2 ⟨sub7_581, List.forall_mem_cons.2 ⟨sub7_582, List.forall_mem_cons.2 ⟨sub7_583, List.forall_mem_cons.2 ⟨sub7_584, List.forall_mem_cons.2 ⟨sub7_585, List.forall_mem_cons.2 ⟨sub7_586, List.forall_mem_cons.2 ⟨sub7_587, List.forall_mem_cons.2 ⟨sub7_588, List.forall_mem_cons.2 ⟨sub7_589, List.forall_mem_cons.2 ⟨sub7_590, List.forall_mem_cons.2 ⟨sub7_591, List.forall_mem_cons.2 ⟨sub7_592, List.forall_mem_cons.2 ⟨sub7_593, List.forall_mem_cons.2 ⟨sub7_594, List.forall_mem_cons.2 ⟨sub7_595, List.forall_mem_cons.2 ⟨sub7_596, List.forall_mem_cons.2 ⟨sub7_597, List.forall_mem_cons.2 ⟨sub7_598, List.forall_mem_cons.2 ⟨sub7_599, List.forall_mem_cons.2 ⟨sub7_600, List.forall_mem_cons.2 ⟨sub7_601, List.forall_mem_cons.2 ⟨sub7_602, List.forall_mem_cons.2 ⟨sub7_603, List.forall_mem_cons.2 ⟨sub7_604, List.forall_mem_cons.2 ⟨sub7_605, List.forall_mem_cons.2 ⟨sub7_606, List.forall_mem_cons.2 ⟨sub7_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_608 : sub7 [3, -2, 4] = true := by decide +kernel
theorem sub7_609 : sub7 [3, -2, 5] = true := by decide +kernel
theorem sub7_610 : sub7 [3, -1, -8] = true := by decide +kernel
theorem sub7_611 : sub7 [3, -1, -7] = true := by decide +kernel
theorem sub7_612 : sub7 [3, -1, -6] = true := by decide +kernel
theorem sub7_613 : sub7 [3, -1, -5] = true := by decide +kernel
theorem sub7_614 : sub7 [3, -1, -4] = true := by decide +kernel
theorem sub7_615 : sub7 [3, -1, -3] = true := by decide +kernel
theorem sub7_616 : sub7 [3, -1, -2] = true := by decide +kernel
theorem sub7_617 : sub7 [3, -1, -1] = true := by decide +kernel
theorem sub7_618 : sub7 [3, -1, 0] = true := by decide +kernel
theorem sub7_619 : sub7 [3, -1, 1] = true := by decide +kernel
theorem sub7_620 : sub7 [3, -1, 2] = true := by decide +kernel
theorem sub7_621 : sub7 [3, -1, 3] = true := by decide +kernel
theorem sub7_622 : sub7 [3, -1, 4] = true := by decide +kernel
theorem sub7_623 : sub7 [3, -1, 5] = true := by decide +kernel
theorem sub7_624 : sub7 [3, 0, -8] = true := by decide +kernel
theorem sub7_625 : sub7 [3, 0, -7] = true := by decide +kernel
theorem sub7_626 : sub7 [3, 0, -6] = true := by decide +kernel
theorem sub7_627 : sub7 [3, 0, -5] = true := by decide +kernel
theorem sub7_628 : sub7 [3, 0, -4] = true := by decide +kernel
theorem sub7_629 : sub7 [3, 0, -3] = true := by decide +kernel
theorem sub7_630 : sub7 [3, 0, -2] = true := by decide +kernel
theorem sub7_631 : sub7 [3, 0, -1] = true := by decide +kernel
theorem sub7_632 : sub7 [3, 0, 0] = true := by decide +kernel
theorem sub7_633 : sub7 [3, 0, 1] = true := by decide +kernel
theorem sub7_634 : sub7 [3, 0, 2] = true := by decide +kernel
theorem sub7_635 : sub7 [3, 0, 3] = true := by decide +kernel
theorem sub7_636 : sub7 [3, 0, 4] = true := by decide +kernel
theorem sub7_637 : sub7 [3, 0, 5] = true := by decide +kernel
theorem sub7_638 : sub7 [3, 1] = true := by decide +kernel
theorem sub7_639 : sub7 [3, 2] = true := by decide +kernel
theorem sb7_19 : ∀ q ∈ blk7_19, sub7 q = true := by
  unfold blk7_19
  exact List.forall_mem_cons.2 ⟨sub7_608, List.forall_mem_cons.2 ⟨sub7_609, List.forall_mem_cons.2 ⟨sub7_610, List.forall_mem_cons.2 ⟨sub7_611, List.forall_mem_cons.2 ⟨sub7_612, List.forall_mem_cons.2 ⟨sub7_613, List.forall_mem_cons.2 ⟨sub7_614, List.forall_mem_cons.2 ⟨sub7_615, List.forall_mem_cons.2 ⟨sub7_616, List.forall_mem_cons.2 ⟨sub7_617, List.forall_mem_cons.2 ⟨sub7_618, List.forall_mem_cons.2 ⟨sub7_619, List.forall_mem_cons.2 ⟨sub7_620, List.forall_mem_cons.2 ⟨sub7_621, List.forall_mem_cons.2 ⟨sub7_622, List.forall_mem_cons.2 ⟨sub7_623, List.forall_mem_cons.2 ⟨sub7_624, List.forall_mem_cons.2 ⟨sub7_625, List.forall_mem_cons.2 ⟨sub7_626, List.forall_mem_cons.2 ⟨sub7_627, List.forall_mem_cons.2 ⟨sub7_628, List.forall_mem_cons.2 ⟨sub7_629, List.forall_mem_cons.2 ⟨sub7_630, List.forall_mem_cons.2 ⟨sub7_631, List.forall_mem_cons.2 ⟨sub7_632, List.forall_mem_cons.2 ⟨sub7_633, List.forall_mem_cons.2 ⟨sub7_634, List.forall_mem_cons.2 ⟨sub7_635, List.forall_mem_cons.2 ⟨sub7_636, List.forall_mem_cons.2 ⟨sub7_637, List.forall_mem_cons.2 ⟨sub7_638, List.forall_mem_cons.2 ⟨sub7_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_640 : sub7 [3, 3] = true := by decide +kernel
theorem sub7_641 : sub7 [3, 4] = true := by decide +kernel
theorem sub7_642 : sub7 [4, -7] = true := by decide +kernel
theorem sub7_643 : sub7 [4, -6] = true := by decide +kernel
theorem sub7_644 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_645 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_646 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_647 : sub7 [4, -2] = true := by decide +kernel
theorem sub7_648 : sub7 [4, -1] = true := by decide +kernel
theorem sub7_649 : sub7 [4, 0] = true := by decide +kernel
theorem sub7_650 : sub7 [4, 1] = true := by decide +kernel
theorem sub7_651 : sub7 [4, 2] = true := by decide +kernel
theorem sub7_652 : sub7 [4, 3] = true := by decide +kernel
theorem sub7_653 : sub7 [5, -7] = true := by decide +kernel
theorem sub7_654 : sub7 [5, -6] = true := by decide +kernel
theorem sub7_655 : sub7 [5, -5] = true := by decide +kernel
theorem sub7_656 : sub7 [5, -4] = true := by decide +kernel
theorem sub7_657 : sub7 [5, -3] = true := by decide +kernel
theorem sub7_658 : sub7 [5, -2] = true := by decide +kernel
theorem sub7_659 : sub7 [5, -1] = true := by decide +kernel
theorem sub7_660 : sub7 [5, 0] = true := by decide +kernel
theorem sub7_661 : sub7 [5, 1] = true := by decide +kernel
theorem sub7_662 : sub7 [6] = true := by decide +kernel
theorem sb7_20 : ∀ q ∈ blk7_20, sub7 q = true := by
  unfold blk7_20
  exact List.forall_mem_cons.2 ⟨sub7_640, List.forall_mem_cons.2 ⟨sub7_641, List.forall_mem_cons.2 ⟨sub7_642, List.forall_mem_cons.2 ⟨sub7_643, List.forall_mem_cons.2 ⟨sub7_644, List.forall_mem_cons.2 ⟨sub7_645, List.forall_mem_cons.2 ⟨sub7_646, List.forall_mem_cons.2 ⟨sub7_647, List.forall_mem_cons.2 ⟨sub7_648, List.forall_mem_cons.2 ⟨sub7_649, List.forall_mem_cons.2 ⟨sub7_650, List.forall_mem_cons.2 ⟨sub7_651, List.forall_mem_cons.2 ⟨sub7_652, List.forall_mem_cons.2 ⟨sub7_653, List.forall_mem_cons.2 ⟨sub7_654, List.forall_mem_cons.2 ⟨sub7_655, List.forall_mem_cons.2 ⟨sub7_656, List.forall_mem_cons.2 ⟨sub7_657, List.forall_mem_cons.2 ⟨sub7_658, List.forall_mem_cons.2 ⟨sub7_659, List.forall_mem_cons.2 ⟨sub7_660, List.forall_mem_cons.2 ⟨sub7_661, List.forall_mem_cons.2 ⟨sub7_662, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_0 : sub8 [-4] = true := by decide +kernel
theorem sub8_1 : sub8 [-3, -4] = true := by decide +kernel
theorem sub8_2 : sub8 [-3, -3] = true := by decide +kernel
theorem sub8_3 : sub8 [-3, -2] = true := by decide +kernel
theorem sub8_4 : sub8 [-3, -1] = true := by decide +kernel
theorem sub8_5 : sub8 [-3, 0] = true := by decide +kernel
theorem sub8_6 : sub8 [-3, 1] = true := by decide +kernel
theorem sub8_7 : sub8 [-3, 2] = true := by decide +kernel
theorem sub8_8 : sub8 [-3, 3] = true := by decide +kernel
theorem sub8_9 : sub8 [-2, -4] = true := by decide +kernel
theorem sub8_10 : sub8 [-2, -3] = true := by decide +kernel
theorem sub8_11 : sub8 [-2, -2] = true := by decide +kernel
theorem sub8_12 : sub8 [-2, -1] = true := by decide +kernel
theorem sub8_13 : sub8 [-2, 0] = true := by decide +kernel
theorem sub8_14 : sub8 [-2, 1] = true := by decide +kernel
theorem sub8_15 : sub8 [-2, 2] = true := by decide +kernel
theorem sub8_16 : sub8 [-2, 3] = true := by decide +kernel
theorem sub8_17 : sub8 [-2, 4] = true := by decide +kernel
theorem sub8_18 : sub8 [-1, -5] = true := by decide +kernel
theorem sub8_19 : sub8 [-1, -4] = true := by decide +kernel
theorem sub8_20 : sub8 [-1, -3] = true := by decide +kernel
theorem sub8_21 : sub8 [-1, -2] = true := by decide +kernel
theorem sub8_22 : sub8 [-1, -1] = true := by decide +kernel
theorem sub8_23 : sub8 [-1, 0] = true := by decide +kernel
theorem sub8_24 : sub8 [-1, 1] = true := by decide +kernel
theorem sub8_25 : sub8 [-1, 2] = true := by decide +kernel
theorem sub8_26 : sub8 [-1, 3] = true := by decide +kernel
theorem sub8_27 : sub8 [-1, 4] = true := by decide +kernel
theorem sub8_28 : sub8 [0, -5] = true := by decide +kernel
theorem sub8_29 : sub8 [0, -4] = true := by decide +kernel
theorem sub8_30 : sub8 [0, -3] = true := by decide +kernel
theorem sub8_31 : sub8 [0, -2] = true := by decide +kernel
theorem sb8_0 : ∀ q ∈ blk8_0, sub8 q = true := by
  unfold blk8_0
  exact List.forall_mem_cons.2 ⟨sub8_0, List.forall_mem_cons.2 ⟨sub8_1, List.forall_mem_cons.2 ⟨sub8_2, List.forall_mem_cons.2 ⟨sub8_3, List.forall_mem_cons.2 ⟨sub8_4, List.forall_mem_cons.2 ⟨sub8_5, List.forall_mem_cons.2 ⟨sub8_6, List.forall_mem_cons.2 ⟨sub8_7, List.forall_mem_cons.2 ⟨sub8_8, List.forall_mem_cons.2 ⟨sub8_9, List.forall_mem_cons.2 ⟨sub8_10, List.forall_mem_cons.2 ⟨sub8_11, List.forall_mem_cons.2 ⟨sub8_12, List.forall_mem_cons.2 ⟨sub8_13, List.forall_mem_cons.2 ⟨sub8_14, List.forall_mem_cons.2 ⟨sub8_15, List.forall_mem_cons.2 ⟨sub8_16, List.forall_mem_cons.2 ⟨sub8_17, List.forall_mem_cons.2 ⟨sub8_18, List.forall_mem_cons.2 ⟨sub8_19, List.forall_mem_cons.2 ⟨sub8_20, List.forall_mem_cons.2 ⟨sub8_21, List.forall_mem_cons.2 ⟨sub8_22, List.forall_mem_cons.2 ⟨sub8_23, List.forall_mem_cons.2 ⟨sub8_24, List.forall_mem_cons.2 ⟨sub8_25, List.forall_mem_cons.2 ⟨sub8_26, List.forall_mem_cons.2 ⟨sub8_27, List.forall_mem_cons.2 ⟨sub8_28, List.forall_mem_cons.2 ⟨sub8_29, List.forall_mem_cons.2 ⟨sub8_30, List.forall_mem_cons.2 ⟨sub8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C083
