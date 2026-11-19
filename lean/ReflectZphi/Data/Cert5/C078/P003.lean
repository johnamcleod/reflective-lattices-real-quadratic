import ReflectZphi.Data.Cert5.C078.Base

namespace ReflectZphi.Data.Cert5.C078
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_512 : sub3 [1, 1, 2] = true := by decide +kernel
theorem sub3_513 : sub3 [1, 1, 3] = true := by decide +kernel
theorem sub3_514 : sub3 [1, 1, 4] = true := by decide +kernel
theorem sub3_515 : sub3 [1, 1, 5] = true := by decide +kernel
theorem sub3_516 : sub3 [1, 1, 6] = true := by decide +kernel
theorem sub3_517 : sub3 [1, 1, 7] = true := by decide +kernel
theorem sub3_518 : sub3 [1, 2, -7] = true := by decide +kernel
theorem sub3_519 : sub3 [1, 2, -6] = true := by decide +kernel
theorem sub3_520 : sub3 [1, 2, -5] = true := by decide +kernel
theorem sub3_521 : sub3 [1, 2, -4] = true := by decide +kernel
theorem sub3_522 : sub3 [1, 2, -3] = true := by decide +kernel
theorem sub3_523 : sub3 [1, 2, -2] = true := by decide +kernel
theorem sub3_524 : sub3 [1, 2, -1] = true := by decide +kernel
theorem sub3_525 : sub3 [1, 2, 0] = true := by decide +kernel
theorem sub3_526 : sub3 [1, 2, 1] = true := by decide +kernel
theorem sub3_527 : sub3 [1, 2, 2] = true := by decide +kernel
theorem sub3_528 : sub3 [1, 2, 3] = true := by decide +kernel
theorem sub3_529 : sub3 [1, 2, 4] = true := by decide +kernel
theorem sub3_530 : sub3 [1, 2, 5] = true := by decide +kernel
theorem sub3_531 : sub3 [1, 2, 6] = true := by decide +kernel
theorem sub3_532 : sub3 [1, 2, 7] = true := by decide +kernel
theorem sub3_533 : sub3 [1, 3, -7] = true := by decide +kernel
theorem sub3_534 : sub3 [1, 3, -6] = true := by decide +kernel
theorem sub3_535 : sub3 [1, 3, -5] = true := by decide +kernel
theorem sub3_536 : sub3 [1, 3, -4] = true := by decide +kernel
theorem sub3_537 : sub3 [1, 3, -3] = true := by decide +kernel
theorem sub3_538 : sub3 [1, 3, -2] = true := by decide +kernel
theorem sub3_539 : sub3 [1, 3, -1] = true := by decide +kernel
theorem sub3_540 : sub3 [1, 3, 0] = true := by decide +kernel
theorem sub3_541 : sub3 [1, 3, 1] = true := by decide +kernel
theorem sub3_542 : sub3 [1, 3, 2] = true := by decide +kernel
theorem sub3_543 : sub3 [1, 3, 3] = true := by decide +kernel
theorem sb3_16 : ∀ q ∈ blk3_16, sub3 q = true := by
  unfold blk3_16
  exact List.forall_mem_cons.2 ⟨sub3_512, List.forall_mem_cons.2 ⟨sub3_513, List.forall_mem_cons.2 ⟨sub3_514, List.forall_mem_cons.2 ⟨sub3_515, List.forall_mem_cons.2 ⟨sub3_516, List.forall_mem_cons.2 ⟨sub3_517, List.forall_mem_cons.2 ⟨sub3_518, List.forall_mem_cons.2 ⟨sub3_519, List.forall_mem_cons.2 ⟨sub3_520, List.forall_mem_cons.2 ⟨sub3_521, List.forall_mem_cons.2 ⟨sub3_522, List.forall_mem_cons.2 ⟨sub3_523, List.forall_mem_cons.2 ⟨sub3_524, List.forall_mem_cons.2 ⟨sub3_525, List.forall_mem_cons.2 ⟨sub3_526, List.forall_mem_cons.2 ⟨sub3_527, List.forall_mem_cons.2 ⟨sub3_528, List.forall_mem_cons.2 ⟨sub3_529, List.forall_mem_cons.2 ⟨sub3_530, List.forall_mem_cons.2 ⟨sub3_531, List.forall_mem_cons.2 ⟨sub3_532, List.forall_mem_cons.2 ⟨sub3_533, List.forall_mem_cons.2 ⟨sub3_534, List.forall_mem_cons.2 ⟨sub3_535, List.forall_mem_cons.2 ⟨sub3_536, List.forall_mem_cons.2 ⟨sub3_537, List.forall_mem_cons.2 ⟨sub3_538, List.forall_mem_cons.2 ⟨sub3_539, List.forall_mem_cons.2 ⟨sub3_540, List.forall_mem_cons.2 ⟨sub3_541, List.forall_mem_cons.2 ⟨sub3_542, List.forall_mem_cons.2 ⟨sub3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_544 : sub3 [1, 3, 4] = true := by decide +kernel
theorem sub3_545 : sub3 [1, 3, 5] = true := by decide +kernel
theorem sub3_546 : sub3 [1, 3, 6] = true := by decide +kernel
theorem sub3_547 : sub3 [1, 3, 7] = true := by decide +kernel
theorem sub3_548 : sub3 [1, 4] = true := by decide +kernel
theorem sub3_549 : sub3 [1, 5] = true := by decide +kernel
theorem sub3_550 : sub3 [1, 6] = true := by decide +kernel
theorem sub3_551 : sub3 [1, 7] = true := by decide +kernel
theorem sub3_552 : sub3 [2, -7] = true := by decide +kernel
theorem sub3_553 : sub3 [2, -6] = true := by decide +kernel
theorem sub3_554 : sub3 [2, -5] = true := by decide +kernel
theorem sub3_555 : sub3 [2, -4] = true := by decide +kernel
theorem sub3_556 : sub3 [2, -3] = true := by decide +kernel
theorem sub3_557 : sub3 [2, -2, -7] = true := by decide +kernel
theorem sub3_558 : sub3 [2, -2, -6] = true := by decide +kernel
theorem sub3_559 : sub3 [2, -2, -5] = true := by decide +kernel
theorem sub3_560 : sub3 [2, -2, -4] = true := by decide +kernel
theorem sub3_561 : sub3 [2, -2, -3] = true := by decide +kernel
theorem sub3_562 : sub3 [2, -2, -2] = true := by decide +kernel
theorem sub3_563 : sub3 [2, -2, -1] = true := by decide +kernel
theorem sub3_564 : sub3 [2, -2, 0] = true := by decide +kernel
theorem sub3_565 : sub3 [2, -2, 1] = true := by decide +kernel
theorem sub3_566 : sub3 [2, -2, 2] = true := by decide +kernel
theorem sub3_567 : sub3 [2, -2, 3] = true := by decide +kernel
theorem sub3_568 : sub3 [2, -2, 4] = true := by decide +kernel
theorem sub3_569 : sub3 [2, -2, 5] = true := by decide +kernel
theorem sub3_570 : sub3 [2, -2, 6] = true := by decide +kernel
theorem sub3_571 : sub3 [2, -2, 7] = true := by decide +kernel
theorem sub3_572 : sub3 [2, -1, -7] = true := by decide +kernel
theorem sub3_573 : sub3 [2, -1, -6] = true := by decide +kernel
theorem sub3_574 : sub3 [2, -1, -5] = true := by decide +kernel
theorem sub3_575 : sub3 [2, -1, -4] = true := by decide +kernel
theorem sb3_17 : ∀ q ∈ blk3_17, sub3 q = true := by
  unfold blk3_17
  exact List.forall_mem_cons.2 ⟨sub3_544, List.forall_mem_cons.2 ⟨sub3_545, List.forall_mem_cons.2 ⟨sub3_546, List.forall_mem_cons.2 ⟨sub3_547, List.forall_mem_cons.2 ⟨sub3_548, List.forall_mem_cons.2 ⟨sub3_549, List.forall_mem_cons.2 ⟨sub3_550, List.forall_mem_cons.2 ⟨sub3_551, List.forall_mem_cons.2 ⟨sub3_552, List.forall_mem_cons.2 ⟨sub3_553, List.forall_mem_cons.2 ⟨sub3_554, List.forall_mem_cons.2 ⟨sub3_555, List.forall_mem_cons.2 ⟨sub3_556, List.forall_mem_cons.2 ⟨sub3_557, List.forall_mem_cons.2 ⟨sub3_558, List.forall_mem_cons.2 ⟨sub3_559, List.forall_mem_cons.2 ⟨sub3_560, List.forall_mem_cons.2 ⟨sub3_561, List.forall_mem_cons.2 ⟨sub3_562, List.forall_mem_cons.2 ⟨sub3_563, List.forall_mem_cons.2 ⟨sub3_564, List.forall_mem_cons.2 ⟨sub3_565, List.forall_mem_cons.2 ⟨sub3_566, List.forall_mem_cons.2 ⟨sub3_567, List.forall_mem_cons.2 ⟨sub3_568, List.forall_mem_cons.2 ⟨sub3_569, List.forall_mem_cons.2 ⟨sub3_570, List.forall_mem_cons.2 ⟨sub3_571, List.forall_mem_cons.2 ⟨sub3_572, List.forall_mem_cons.2 ⟨sub3_573, List.forall_mem_cons.2 ⟨sub3_574, List.forall_mem_cons.2 ⟨sub3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_576 : sub3 [2, -1, -3] = true := by decide +kernel
theorem sub3_577 : sub3 [2, -1, -2] = true := by decide +kernel
theorem sub3_578 : sub3 [2, -1, -1] = true := by decide +kernel
theorem sub3_579 : sub3 [2, -1, 0] = true := by decide +kernel
theorem sub3_580 : sub3 [2, -1, 1] = true := by decide +kernel
theorem sub3_581 : sub3 [2, -1, 2] = true := by decide +kernel
theorem sub3_582 : sub3 [2, -1, 3] = true := by decide +kernel
theorem sub3_583 : sub3 [2, -1, 4] = true := by decide +kernel
theorem sub3_584 : sub3 [2, -1, 5] = true := by decide +kernel
theorem sub3_585 : sub3 [2, -1, 6] = true := by decide +kernel
theorem sub3_586 : sub3 [2, -1, 7] = true := by decide +kernel
theorem sub3_587 : sub3 [2, 0, -7] = true := by decide +kernel
theorem sub3_588 : sub3 [2, 0, -6] = true := by decide +kernel
theorem sub3_589 : sub3 [2, 0, -5] = true := by decide +kernel
theorem sub3_590 : sub3 [2, 0, -4] = true := by decide +kernel
theorem sub3_591 : sub3 [2, 0, -3] = true := by decide +kernel
theorem sub3_592 : sub3 [2, 0, -2] = true := by decide +kernel
theorem sub3_593 : sub3 [2, 0, -1] = true := by decide +kernel
theorem sub3_594 : sub3 [2, 0, 0] = true := by decide +kernel
theorem sub3_595 : sub3 [2, 0, 1] = true := by decide +kernel
theorem sub3_596 : sub3 [2, 0, 2] = true := by decide +kernel
theorem sub3_597 : sub3 [2, 0, 3] = true := by decide +kernel
theorem sub3_598 : sub3 [2, 0, 4] = true := by decide +kernel
theorem sub3_599 : sub3 [2, 0, 5] = true := by decide +kernel
theorem sub3_600 : sub3 [2, 0, 6] = true := by decide +kernel
theorem sub3_601 : sub3 [2, 0, 7] = true := by decide +kernel
theorem sub3_602 : sub3 [2, 1, -7] = true := by decide +kernel
theorem sub3_603 : sub3 [2, 1, -6] = true := by decide +kernel
theorem sub3_604 : sub3 [2, 1, -5] = true := by decide +kernel
theorem sub3_605 : sub3 [2, 1, -4] = true := by decide +kernel
theorem sub3_606 : sub3 [2, 1, -3] = true := by decide +kernel
theorem sub3_607 : sub3 [2, 1, -2] = true := by decide +kernel
theorem sb3_18 : ∀ q ∈ blk3_18, sub3 q = true := by
  unfold blk3_18
  exact List.forall_mem_cons.2 ⟨sub3_576, List.forall_mem_cons.2 ⟨sub3_577, List.forall_mem_cons.2 ⟨sub3_578, List.forall_mem_cons.2 ⟨sub3_579, List.forall_mem_cons.2 ⟨sub3_580, List.forall_mem_cons.2 ⟨sub3_581, List.forall_mem_cons.2 ⟨sub3_582, List.forall_mem_cons.2 ⟨sub3_583, List.forall_mem_cons.2 ⟨sub3_584, List.forall_mem_cons.2 ⟨sub3_585, List.forall_mem_cons.2 ⟨sub3_586, List.forall_mem_cons.2 ⟨sub3_587, List.forall_mem_cons.2 ⟨sub3_588, List.forall_mem_cons.2 ⟨sub3_589, List.forall_mem_cons.2 ⟨sub3_590, List.forall_mem_cons.2 ⟨sub3_591, List.forall_mem_cons.2 ⟨sub3_592, List.forall_mem_cons.2 ⟨sub3_593, List.forall_mem_cons.2 ⟨sub3_594, List.forall_mem_cons.2 ⟨sub3_595, List.forall_mem_cons.2 ⟨sub3_596, List.forall_mem_cons.2 ⟨sub3_597, List.forall_mem_cons.2 ⟨sub3_598, List.forall_mem_cons.2 ⟨sub3_599, List.forall_mem_cons.2 ⟨sub3_600, List.forall_mem_cons.2 ⟨sub3_601, List.forall_mem_cons.2 ⟨sub3_602, List.forall_mem_cons.2 ⟨sub3_603, List.forall_mem_cons.2 ⟨sub3_604, List.forall_mem_cons.2 ⟨sub3_605, List.forall_mem_cons.2 ⟨sub3_606, List.forall_mem_cons.2 ⟨sub3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_608 : sub3 [2, 1, -1] = true := by decide +kernel
theorem sub3_609 : sub3 [2, 1, 0] = true := by decide +kernel
theorem sub3_610 : sub3 [2, 1, 1] = true := by decide +kernel
theorem sub3_611 : sub3 [2, 1, 2] = true := by decide +kernel
theorem sub3_612 : sub3 [2, 1, 3] = true := by decide +kernel
theorem sub3_613 : sub3 [2, 1, 4] = true := by decide +kernel
theorem sub3_614 : sub3 [2, 1, 5] = true := by decide +kernel
theorem sub3_615 : sub3 [2, 1, 6] = true := by decide +kernel
theorem sub3_616 : sub3 [2, 1, 7] = true := by decide +kernel
theorem sub3_617 : sub3 [2, 2, -7] = true := by decide +kernel
theorem sub3_618 : sub3 [2, 2, -6] = true := by decide +kernel
theorem sub3_619 : sub3 [2, 2, -5] = true := by decide +kernel
theorem sub3_620 : sub3 [2, 2, -4] = true := by decide +kernel
theorem sub3_621 : sub3 [2, 2, -3] = true := by decide +kernel
theorem sub3_622 : sub3 [2, 2, -2] = true := by decide +kernel
theorem sub3_623 : sub3 [2, 2, -1] = true := by decide +kernel
theorem sub3_624 : sub3 [2, 2, 0] = true := by decide +kernel
theorem sub3_625 : sub3 [2, 2, 1] = true := by decide +kernel
theorem sub3_626 : sub3 [2, 2, 2] = true := by decide +kernel
theorem sub3_627 : sub3 [2, 2, 3] = true := by decide +kernel
theorem sub3_628 : sub3 [2, 2, 4] = true := by decide +kernel
theorem sub3_629 : sub3 [2, 2, 5] = true := by decide +kernel
theorem sub3_630 : sub3 [2, 2, 6] = true := by decide +kernel
theorem sub3_631 : sub3 [2, 2, 7] = true := by decide +kernel
theorem sub3_632 : sub3 [2, 3, -6] = true := by decide +kernel
theorem sub3_633 : sub3 [2, 3, -5] = true := by decide +kernel
theorem sub3_634 : sub3 [2, 3, -4] = true := by decide +kernel
theorem sub3_635 : sub3 [2, 3, -3] = true := by decide +kernel
theorem sub3_636 : sub3 [2, 3, -2] = true := by decide +kernel
theorem sub3_637 : sub3 [2, 3, -1] = true := by decide +kernel
theorem sub3_638 : sub3 [2, 3, 0] = true := by decide +kernel
theorem sub3_639 : sub3 [2, 3, 1] = true := by decide +kernel
theorem sb3_19 : ∀ q ∈ blk3_19, sub3 q = true := by
  unfold blk3_19
  exact List.forall_mem_cons.2 ⟨sub3_608, List.forall_mem_cons.2 ⟨sub3_609, List.forall_mem_cons.2 ⟨sub3_610, List.forall_mem_cons.2 ⟨sub3_611, List.forall_mem_cons.2 ⟨sub3_612, List.forall_mem_cons.2 ⟨sub3_613, List.forall_mem_cons.2 ⟨sub3_614, List.forall_mem_cons.2 ⟨sub3_615, List.forall_mem_cons.2 ⟨sub3_616, List.forall_mem_cons.2 ⟨sub3_617, List.forall_mem_cons.2 ⟨sub3_618, List.forall_mem_cons.2 ⟨sub3_619, List.forall_mem_cons.2 ⟨sub3_620, List.forall_mem_cons.2 ⟨sub3_621, List.forall_mem_cons.2 ⟨sub3_622, List.forall_mem_cons.2 ⟨sub3_623, List.forall_mem_cons.2 ⟨sub3_624, List.forall_mem_cons.2 ⟨sub3_625, List.forall_mem_cons.2 ⟨sub3_626, List.forall_mem_cons.2 ⟨sub3_627, List.forall_mem_cons.2 ⟨sub3_628, List.forall_mem_cons.2 ⟨sub3_629, List.forall_mem_cons.2 ⟨sub3_630, List.forall_mem_cons.2 ⟨sub3_631, List.forall_mem_cons.2 ⟨sub3_632, List.forall_mem_cons.2 ⟨sub3_633, List.forall_mem_cons.2 ⟨sub3_634, List.forall_mem_cons.2 ⟨sub3_635, List.forall_mem_cons.2 ⟨sub3_636, List.forall_mem_cons.2 ⟨sub3_637, List.forall_mem_cons.2 ⟨sub3_638, List.forall_mem_cons.2 ⟨sub3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_640 : sub3 [2, 3, 2] = true := by decide +kernel
theorem sub3_641 : sub3 [2, 3, 3] = true := by decide +kernel
theorem sub3_642 : sub3 [2, 3, 4] = true := by decide +kernel
theorem sub3_643 : sub3 [2, 3, 5] = true := by decide +kernel
theorem sub3_644 : sub3 [2, 3, 6] = true := by decide +kernel
theorem sub3_645 : sub3 [2, 3, 7] = true := by decide +kernel
theorem sub3_646 : sub3 [2, 4] = true := by decide +kernel
theorem sub3_647 : sub3 [2, 5] = true := by decide +kernel
theorem sub3_648 : sub3 [2, 6] = true := by decide +kernel
theorem sub3_649 : sub3 [2, 7] = true := by decide +kernel
theorem sub3_650 : sub3 [3, -7] = true := by decide +kernel
theorem sub3_651 : sub3 [3, -6] = true := by decide +kernel
theorem sub3_652 : sub3 [3, -5] = true := by decide +kernel
theorem sub3_653 : sub3 [3, -4] = true := by decide +kernel
theorem sub3_654 : sub3 [3, -3] = true := by decide +kernel
theorem sub3_655 : sub3 [3, -2] = true := by decide +kernel
theorem sub3_656 : sub3 [3, -1, -6] = true := by decide +kernel
theorem sub3_657 : sub3 [3, -1, -5] = true := by decide +kernel
theorem sub3_658 : sub3 [3, -1, -4] = true := by decide +kernel
theorem sub3_659 : sub3 [3, -1, -3] = true := by decide +kernel
theorem sub3_660 : sub3 [3, -1, -2] = true := by decide +kernel
theorem sub3_661 : sub3 [3, -1, -1] = true := by decide +kernel
theorem sub3_662 : sub3 [3, -1, 0] = true := by decide +kernel
theorem sub3_663 : sub3 [3, -1, 1] = true := by decide +kernel
theorem sub3_664 : sub3 [3, -1, 2] = true := by decide +kernel
theorem sub3_665 : sub3 [3, -1, 3] = true := by decide +kernel
theorem sub3_666 : sub3 [3, -1, 4] = true := by decide +kernel
theorem sub3_667 : sub3 [3, -1, 5] = true := by decide +kernel
theorem sub3_668 : sub3 [3, -1, 6] = true := by decide +kernel
theorem sub3_669 : sub3 [3, -1, 7] = true := by decide +kernel
theorem sub3_670 : sub3 [3, 0, -6] = true := by decide +kernel
theorem sub3_671 : sub3 [3, 0, -5] = true := by decide +kernel
theorem sb3_20 : ∀ q ∈ blk3_20, sub3 q = true := by
  unfold blk3_20
  exact List.forall_mem_cons.2 ⟨sub3_640, List.forall_mem_cons.2 ⟨sub3_641, List.forall_mem_cons.2 ⟨sub3_642, List.forall_mem_cons.2 ⟨sub3_643, List.forall_mem_cons.2 ⟨sub3_644, List.forall_mem_cons.2 ⟨sub3_645, List.forall_mem_cons.2 ⟨sub3_646, List.forall_mem_cons.2 ⟨sub3_647, List.forall_mem_cons.2 ⟨sub3_648, List.forall_mem_cons.2 ⟨sub3_649, List.forall_mem_cons.2 ⟨sub3_650, List.forall_mem_cons.2 ⟨sub3_651, List.forall_mem_cons.2 ⟨sub3_652, List.forall_mem_cons.2 ⟨sub3_653, List.forall_mem_cons.2 ⟨sub3_654, List.forall_mem_cons.2 ⟨sub3_655, List.forall_mem_cons.2 ⟨sub3_656, List.forall_mem_cons.2 ⟨sub3_657, List.forall_mem_cons.2 ⟨sub3_658, List.forall_mem_cons.2 ⟨sub3_659, List.forall_mem_cons.2 ⟨sub3_660, List.forall_mem_cons.2 ⟨sub3_661, List.forall_mem_cons.2 ⟨sub3_662, List.forall_mem_cons.2 ⟨sub3_663, List.forall_mem_cons.2 ⟨sub3_664, List.forall_mem_cons.2 ⟨sub3_665, List.forall_mem_cons.2 ⟨sub3_666, List.forall_mem_cons.2 ⟨sub3_667, List.forall_mem_cons.2 ⟨sub3_668, List.forall_mem_cons.2 ⟨sub3_669, List.forall_mem_cons.2 ⟨sub3_670, List.forall_mem_cons.2 ⟨sub3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_672 : sub3 [3, 0, -4] = true := by decide +kernel
theorem sub3_673 : sub3 [3, 0, -3] = true := by decide +kernel
theorem sub3_674 : sub3 [3, 0, -2] = true := by decide +kernel
theorem sub3_675 : sub3 [3, 0, -1] = true := by decide +kernel
theorem sub3_676 : sub3 [3, 0, 0] = true := by decide +kernel
theorem sub3_677 : sub3 [3, 0, 1] = true := by decide +kernel
theorem sub3_678 : sub3 [3, 0, 2] = true := by decide +kernel
theorem sub3_679 : sub3 [3, 0, 3] = true := by decide +kernel
theorem sub3_680 : sub3 [3, 0, 4] = true := by decide +kernel
theorem sub3_681 : sub3 [3, 0, 5] = true := by decide +kernel
theorem sub3_682 : sub3 [3, 0, 6] = true := by decide +kernel
theorem sub3_683 : sub3 [3, 0, 7] = true := by decide +kernel
theorem sub3_684 : sub3 [3, 1, -6] = true := by decide +kernel
theorem sub3_685 : sub3 [3, 1, -5] = true := by decide +kernel
theorem sub3_686 : sub3 [3, 1, -4] = true := by decide +kernel
theorem sub3_687 : sub3 [3, 1, -3] = true := by decide +kernel
theorem sub3_688 : sub3 [3, 1, -2] = true := by decide +kernel
theorem sub3_689 : sub3 [3, 1, -1] = true := by decide +kernel
theorem sub3_690 : sub3 [3, 1, 0] = true := by decide +kernel
theorem sub3_691 : sub3 [3, 1, 1] = true := by decide +kernel
theorem sub3_692 : sub3 [3, 1, 2] = true := by decide +kernel
theorem sub3_693 : sub3 [3, 1, 3] = true := by decide +kernel
theorem sub3_694 : sub3 [3, 1, 4] = true := by decide +kernel
theorem sub3_695 : sub3 [3, 1, 5] = true := by decide +kernel
theorem sub3_696 : sub3 [3, 1, 6] = true := by decide +kernel
theorem sub3_697 : sub3 [3, 1, 7] = true := by decide +kernel
theorem sub3_698 : sub3 [3, 2, -6] = true := by decide +kernel
theorem sub3_699 : sub3 [3, 2, -5] = true := by decide +kernel
theorem sub3_700 : sub3 [3, 2, -4] = true := by decide +kernel
theorem sub3_701 : sub3 [3, 2, -3] = true := by decide +kernel
theorem sub3_702 : sub3 [3, 2, -2] = true := by decide +kernel
theorem sub3_703 : sub3 [3, 2, -1] = true := by decide +kernel
theorem sb3_21 : ∀ q ∈ blk3_21, sub3 q = true := by
  unfold blk3_21
  exact List.forall_mem_cons.2 ⟨sub3_672, List.forall_mem_cons.2 ⟨sub3_673, List.forall_mem_cons.2 ⟨sub3_674, List.forall_mem_cons.2 ⟨sub3_675, List.forall_mem_cons.2 ⟨sub3_676, List.forall_mem_cons.2 ⟨sub3_677, List.forall_mem_cons.2 ⟨sub3_678, List.forall_mem_cons.2 ⟨sub3_679, List.forall_mem_cons.2 ⟨sub3_680, List.forall_mem_cons.2 ⟨sub3_681, List.forall_mem_cons.2 ⟨sub3_682, List.forall_mem_cons.2 ⟨sub3_683, List.forall_mem_cons.2 ⟨sub3_684, List.forall_mem_cons.2 ⟨sub3_685, List.forall_mem_cons.2 ⟨sub3_686, List.forall_mem_cons.2 ⟨sub3_687, List.forall_mem_cons.2 ⟨sub3_688, List.forall_mem_cons.2 ⟨sub3_689, List.forall_mem_cons.2 ⟨sub3_690, List.forall_mem_cons.2 ⟨sub3_691, List.forall_mem_cons.2 ⟨sub3_692, List.forall_mem_cons.2 ⟨sub3_693, List.forall_mem_cons.2 ⟨sub3_694, List.forall_mem_cons.2 ⟨sub3_695, List.forall_mem_cons.2 ⟨sub3_696, List.forall_mem_cons.2 ⟨sub3_697, List.forall_mem_cons.2 ⟨sub3_698, List.forall_mem_cons.2 ⟨sub3_699, List.forall_mem_cons.2 ⟨sub3_700, List.forall_mem_cons.2 ⟨sub3_701, List.forall_mem_cons.2 ⟨sub3_702, List.forall_mem_cons.2 ⟨sub3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_704 : sub3 [3, 2, 0] = true := by decide +kernel
theorem sub3_705 : sub3 [3, 2, 1] = true := by decide +kernel
theorem sub3_706 : sub3 [3, 2, 2] = true := by decide +kernel
theorem sub3_707 : sub3 [3, 2, 3] = true := by decide +kernel
theorem sub3_708 : sub3 [3, 2, 4] = true := by decide +kernel
theorem sub3_709 : sub3 [3, 2, 5] = true := by decide +kernel
theorem sub3_710 : sub3 [3, 2, 6] = true := by decide +kernel
theorem sub3_711 : sub3 [3, 2, 7] = true := by decide +kernel
theorem sub3_712 : sub3 [3, 3] = true := by decide +kernel
theorem sub3_713 : sub3 [3, 4] = true := by decide +kernel
theorem sub3_714 : sub3 [3, 5] = true := by decide +kernel
theorem sub3_715 : sub3 [3, 6] = true := by decide +kernel
theorem sub3_716 : sub3 [3, 7] = true := by decide +kernel
theorem sub3_717 : sub3 [4, -6] = true := by decide +kernel
theorem sub3_718 : sub3 [4, -5] = true := by decide +kernel
theorem sub3_719 : sub3 [4, -4] = true := by decide +kernel
theorem sub3_720 : sub3 [4, -3] = true := by decide +kernel
theorem sub3_721 : sub3 [4, -2] = true := by decide +kernel
theorem sub3_722 : sub3 [4, -1] = true := by decide +kernel
theorem sub3_723 : sub3 [4, 0] = true := by decide +kernel
theorem sub3_724 : sub3 [4, 1] = true := by decide +kernel
theorem sub3_725 : sub3 [4, 2] = true := by decide +kernel
theorem sub3_726 : sub3 [4, 3] = true := by decide +kernel
theorem sub3_727 : sub3 [4, 4] = true := by decide +kernel
theorem sub3_728 : sub3 [4, 5] = true := by decide +kernel
theorem sub3_729 : sub3 [4, 6] = true := by decide +kernel
theorem sub3_730 : sub3 [5, -5] = true := by decide +kernel
theorem sub3_731 : sub3 [5, -4] = true := by decide +kernel
theorem sub3_732 : sub3 [5, -3] = true := by decide +kernel
theorem sub3_733 : sub3 [5, -2] = true := by decide +kernel
theorem sub3_734 : sub3 [5, -1] = true := by decide +kernel
theorem sub3_735 : sub3 [5, 0] = true := by decide +kernel
theorem sb3_22 : ∀ q ∈ blk3_22, sub3 q = true := by
  unfold blk3_22
  exact List.forall_mem_cons.2 ⟨sub3_704, List.forall_mem_cons.2 ⟨sub3_705, List.forall_mem_cons.2 ⟨sub3_706, List.forall_mem_cons.2 ⟨sub3_707, List.forall_mem_cons.2 ⟨sub3_708, List.forall_mem_cons.2 ⟨sub3_709, List.forall_mem_cons.2 ⟨sub3_710, List.forall_mem_cons.2 ⟨sub3_711, List.forall_mem_cons.2 ⟨sub3_712, List.forall_mem_cons.2 ⟨sub3_713, List.forall_mem_cons.2 ⟨sub3_714, List.forall_mem_cons.2 ⟨sub3_715, List.forall_mem_cons.2 ⟨sub3_716, List.forall_mem_cons.2 ⟨sub3_717, List.forall_mem_cons.2 ⟨sub3_718, List.forall_mem_cons.2 ⟨sub3_719, List.forall_mem_cons.2 ⟨sub3_720, List.forall_mem_cons.2 ⟨sub3_721, List.forall_mem_cons.2 ⟨sub3_722, List.forall_mem_cons.2 ⟨sub3_723, List.forall_mem_cons.2 ⟨sub3_724, List.forall_mem_cons.2 ⟨sub3_725, List.forall_mem_cons.2 ⟨sub3_726, List.forall_mem_cons.2 ⟨sub3_727, List.forall_mem_cons.2 ⟨sub3_728, List.forall_mem_cons.2 ⟨sub3_729, List.forall_mem_cons.2 ⟨sub3_730, List.forall_mem_cons.2 ⟨sub3_731, List.forall_mem_cons.2 ⟨sub3_732, List.forall_mem_cons.2 ⟨sub3_733, List.forall_mem_cons.2 ⟨sub3_734, List.forall_mem_cons.2 ⟨sub3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_736 : sub3 [5, 1] = true := by decide +kernel
theorem sub3_737 : sub3 [5, 2] = true := by decide +kernel
theorem sub3_738 : sub3 [5, 3] = true := by decide +kernel
theorem sub3_739 : sub3 [5, 4] = true := by decide +kernel
theorem sub3_740 : sub3 [5, 5] = true := by decide +kernel
theorem sub3_741 : sub3 [5, 6] = true := by decide +kernel
theorem sub3_742 : sub3 [6, -4] = true := by decide +kernel
theorem sub3_743 : sub3 [6, -3] = true := by decide +kernel
theorem sub3_744 : sub3 [6, -2] = true := by decide +kernel
theorem sub3_745 : sub3 [6, -1] = true := by decide +kernel
theorem sub3_746 : sub3 [6, 0] = true := by decide +kernel
theorem sub3_747 : sub3 [6, 1] = true := by decide +kernel
theorem sub3_748 : sub3 [6, 2] = true := by decide +kernel
theorem sub3_749 : sub3 [6, 3] = true := by decide +kernel
theorem sub3_750 : sub3 [6, 4] = true := by decide +kernel
theorem sub3_751 : sub3 [6, 5] = true := by decide +kernel
theorem sub3_752 : sub3 [7] = true := by decide +kernel
theorem sb3_23 : ∀ q ∈ blk3_23, sub3 q = true := by
  unfold blk3_23
  exact List.forall_mem_cons.2 ⟨sub3_736, List.forall_mem_cons.2 ⟨sub3_737, List.forall_mem_cons.2 ⟨sub3_738, List.forall_mem_cons.2 ⟨sub3_739, List.forall_mem_cons.2 ⟨sub3_740, List.forall_mem_cons.2 ⟨sub3_741, List.forall_mem_cons.2 ⟨sub3_742, List.forall_mem_cons.2 ⟨sub3_743, List.forall_mem_cons.2 ⟨sub3_744, List.forall_mem_cons.2 ⟨sub3_745, List.forall_mem_cons.2 ⟨sub3_746, List.forall_mem_cons.2 ⟨sub3_747, List.forall_mem_cons.2 ⟨sub3_748, List.forall_mem_cons.2 ⟨sub3_749, List.forall_mem_cons.2 ⟨sub3_750, List.forall_mem_cons.2 ⟨sub3_751, List.forall_mem_cons.2 ⟨sub3_752, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C078
