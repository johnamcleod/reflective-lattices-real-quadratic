import ReflectZphi.Data.Cert5.C083.Base

namespace ReflectZphi.Data.Cert5.C083
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_512 : sub6 [2, -3, 3] = true := by decide +kernel
theorem sub6_513 : sub6 [2, -3, 4] = true := by decide +kernel
theorem sub6_514 : sub6 [2, -2, -8] = true := by decide +kernel
theorem sub6_515 : sub6 [2, -2, -7] = true := by decide +kernel
theorem sub6_516 : sub6 [2, -2, -6] = true := by decide +kernel
theorem sub6_517 : sub6 [2, -2, -5] = true := by decide +kernel
theorem sub6_518 : sub6 [2, -2, -4] = true := by decide +kernel
theorem sub6_519 : sub6 [2, -2, -3] = true := by decide +kernel
theorem sub6_520 : sub6 [2, -2, -2] = true := by decide +kernel
theorem sub6_521 : sub6 [2, -2, -1] = true := by decide +kernel
theorem sub6_522 : sub6 [2, -2, 0] = true := by decide +kernel
theorem sub6_523 : sub6 [2, -2, 1] = true := by decide +kernel
theorem sub6_524 : sub6 [2, -2, 2] = true := by decide +kernel
theorem sub6_525 : sub6 [2, -2, 3] = true := by decide +kernel
theorem sub6_526 : sub6 [2, -2, 4] = true := by decide +kernel
theorem sub6_527 : sub6 [2, -2, 5] = true := by decide +kernel
theorem sub6_528 : sub6 [2, -1, -8] = true := by decide +kernel
theorem sub6_529 : sub6 [2, -1, -7] = true := by decide +kernel
theorem sub6_530 : sub6 [2, -1, -6] = true := by decide +kernel
theorem sub6_531 : sub6 [2, -1, -5] = true := by decide +kernel
theorem sub6_532 : sub6 [2, -1, -4] = true := by decide +kernel
theorem sub6_533 : sub6 [2, -1, -3] = true := by decide +kernel
theorem sub6_534 : sub6 [2, -1, -2] = true := by decide +kernel
theorem sub6_535 : sub6 [2, -1, -1] = true := by decide +kernel
theorem sub6_536 : sub6 [2, -1, 0] = true := by decide +kernel
theorem sub6_537 : sub6 [2, -1, 1] = true := by decide +kernel
theorem sub6_538 : sub6 [2, -1, 2] = true := by decide +kernel
theorem sub6_539 : sub6 [2, -1, 3] = true := by decide +kernel
theorem sub6_540 : sub6 [2, -1, 4] = true := by decide +kernel
theorem sub6_541 : sub6 [2, -1, 5] = true := by decide +kernel
theorem sub6_542 : sub6 [2, 0, -8] = true := by decide +kernel
theorem sub6_543 : sub6 [2, 0, -7] = true := by decide +kernel
theorem sb6_16 : ∀ q ∈ blk6_16, sub6 q = true := by
  unfold blk6_16
  exact List.forall_mem_cons.2 ⟨sub6_512, List.forall_mem_cons.2 ⟨sub6_513, List.forall_mem_cons.2 ⟨sub6_514, List.forall_mem_cons.2 ⟨sub6_515, List.forall_mem_cons.2 ⟨sub6_516, List.forall_mem_cons.2 ⟨sub6_517, List.forall_mem_cons.2 ⟨sub6_518, List.forall_mem_cons.2 ⟨sub6_519, List.forall_mem_cons.2 ⟨sub6_520, List.forall_mem_cons.2 ⟨sub6_521, List.forall_mem_cons.2 ⟨sub6_522, List.forall_mem_cons.2 ⟨sub6_523, List.forall_mem_cons.2 ⟨sub6_524, List.forall_mem_cons.2 ⟨sub6_525, List.forall_mem_cons.2 ⟨sub6_526, List.forall_mem_cons.2 ⟨sub6_527, List.forall_mem_cons.2 ⟨sub6_528, List.forall_mem_cons.2 ⟨sub6_529, List.forall_mem_cons.2 ⟨sub6_530, List.forall_mem_cons.2 ⟨sub6_531, List.forall_mem_cons.2 ⟨sub6_532, List.forall_mem_cons.2 ⟨sub6_533, List.forall_mem_cons.2 ⟨sub6_534, List.forall_mem_cons.2 ⟨sub6_535, List.forall_mem_cons.2 ⟨sub6_536, List.forall_mem_cons.2 ⟨sub6_537, List.forall_mem_cons.2 ⟨sub6_538, List.forall_mem_cons.2 ⟨sub6_539, List.forall_mem_cons.2 ⟨sub6_540, List.forall_mem_cons.2 ⟨sub6_541, List.forall_mem_cons.2 ⟨sub6_542, List.forall_mem_cons.2 ⟨sub6_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_544 : sub6 [2, 0, -6] = true := by decide +kernel
theorem sub6_545 : sub6 [2, 0, -5] = true := by decide +kernel
theorem sub6_546 : sub6 [2, 0, -4] = true := by decide +kernel
theorem sub6_547 : sub6 [2, 0, -3] = true := by decide +kernel
theorem sub6_548 : sub6 [2, 0, -2] = true := by decide +kernel
theorem sub6_549 : sub6 [2, 0, -1] = true := by decide +kernel
theorem sub6_550 : sub6 [2, 0, 0] = true := by decide +kernel
theorem sub6_551 : sub6 [2, 0, 1] = true := by decide +kernel
theorem sub6_552 : sub6 [2, 0, 2] = true := by decide +kernel
theorem sub6_553 : sub6 [2, 0, 3] = true := by decide +kernel
theorem sub6_554 : sub6 [2, 0, 4] = true := by decide +kernel
theorem sub6_555 : sub6 [2, 0, 5] = true := by decide +kernel
theorem sub6_556 : sub6 [2, 0, 6] = true := by decide +kernel
theorem sub6_557 : sub6 [2, 1, -8] = true := by decide +kernel
theorem sub6_558 : sub6 [2, 1, -7] = true := by decide +kernel
theorem sub6_559 : sub6 [2, 1, -6] = true := by decide +kernel
theorem sub6_560 : sub6 [2, 1, -5] = true := by decide +kernel
theorem sub6_561 : sub6 [2, 1, -4] = true := by decide +kernel
theorem sub6_562 : sub6 [2, 1, -3] = true := by decide +kernel
theorem sub6_563 : sub6 [2, 1, -2] = true := by decide +kernel
theorem sub6_564 : sub6 [2, 1, -1] = true := by decide +kernel
theorem sub6_565 : sub6 [2, 1, 0] = true := by decide +kernel
theorem sub6_566 : sub6 [2, 1, 1] = true := by decide +kernel
theorem sub6_567 : sub6 [2, 1, 2] = true := by decide +kernel
theorem sub6_568 : sub6 [2, 1, 3] = true := by decide +kernel
theorem sub6_569 : sub6 [2, 1, 4] = true := by decide +kernel
theorem sub6_570 : sub6 [2, 1, 5] = true := by decide +kernel
theorem sub6_571 : sub6 [2, 1, 6] = true := by decide +kernel
theorem sub6_572 : sub6 [2, 2, -7] = true := by decide +kernel
theorem sub6_573 : sub6 [2, 2, -6] = true := by decide +kernel
theorem sub6_574 : sub6 [2, 2, -5] = true := by decide +kernel
theorem sub6_575 : sub6 [2, 2, -4] = true := by decide +kernel
theorem sb6_17 : ∀ q ∈ blk6_17, sub6 q = true := by
  unfold blk6_17
  exact List.forall_mem_cons.2 ⟨sub6_544, List.forall_mem_cons.2 ⟨sub6_545, List.forall_mem_cons.2 ⟨sub6_546, List.forall_mem_cons.2 ⟨sub6_547, List.forall_mem_cons.2 ⟨sub6_548, List.forall_mem_cons.2 ⟨sub6_549, List.forall_mem_cons.2 ⟨sub6_550, List.forall_mem_cons.2 ⟨sub6_551, List.forall_mem_cons.2 ⟨sub6_552, List.forall_mem_cons.2 ⟨sub6_553, List.forall_mem_cons.2 ⟨sub6_554, List.forall_mem_cons.2 ⟨sub6_555, List.forall_mem_cons.2 ⟨sub6_556, List.forall_mem_cons.2 ⟨sub6_557, List.forall_mem_cons.2 ⟨sub6_558, List.forall_mem_cons.2 ⟨sub6_559, List.forall_mem_cons.2 ⟨sub6_560, List.forall_mem_cons.2 ⟨sub6_561, List.forall_mem_cons.2 ⟨sub6_562, List.forall_mem_cons.2 ⟨sub6_563, List.forall_mem_cons.2 ⟨sub6_564, List.forall_mem_cons.2 ⟨sub6_565, List.forall_mem_cons.2 ⟨sub6_566, List.forall_mem_cons.2 ⟨sub6_567, List.forall_mem_cons.2 ⟨sub6_568, List.forall_mem_cons.2 ⟨sub6_569, List.forall_mem_cons.2 ⟨sub6_570, List.forall_mem_cons.2 ⟨sub6_571, List.forall_mem_cons.2 ⟨sub6_572, List.forall_mem_cons.2 ⟨sub6_573, List.forall_mem_cons.2 ⟨sub6_574, List.forall_mem_cons.2 ⟨sub6_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_576 : sub6 [2, 2, -3] = true := by decide +kernel
theorem sub6_577 : sub6 [2, 2, -2] = true := by decide +kernel
theorem sub6_578 : sub6 [2, 2, -1] = true := by decide +kernel
theorem sub6_579 : sub6 [2, 2, 0] = true := by decide +kernel
theorem sub6_580 : sub6 [2, 2, 1] = true := by decide +kernel
theorem sub6_581 : sub6 [2, 2, 2] = true := by decide +kernel
theorem sub6_582 : sub6 [2, 2, 3] = true := by decide +kernel
theorem sub6_583 : sub6 [2, 2, 4] = true := by decide +kernel
theorem sub6_584 : sub6 [2, 2, 5] = true := by decide +kernel
theorem sub6_585 : sub6 [2, 2, 6] = true := by decide +kernel
theorem sub6_586 : sub6 [2, 3] = true := by decide +kernel
theorem sub6_587 : sub6 [2, 4] = true := by decide +kernel
theorem sub6_588 : sub6 [2, 5] = true := by decide +kernel
theorem sub6_589 : sub6 [3, -7] = true := by decide +kernel
theorem sub6_590 : sub6 [3, -6] = true := by decide +kernel
theorem sub6_591 : sub6 [3, -5] = true := by decide +kernel
theorem sub6_592 : sub6 [3, -4] = true := by decide +kernel
theorem sub6_593 : sub6 [3, -3] = true := by decide +kernel
theorem sub6_594 : sub6 [3, -2, -9] = true := by decide +kernel
theorem sub6_595 : sub6 [3, -2, -8] = true := by decide +kernel
theorem sub6_596 : sub6 [3, -2, -7] = true := by decide +kernel
theorem sub6_597 : sub6 [3, -2, -6] = true := by decide +kernel
theorem sub6_598 : sub6 [3, -2, -5] = true := by decide +kernel
theorem sub6_599 : sub6 [3, -2, -4] = true := by decide +kernel
theorem sub6_600 : sub6 [3, -2, -3] = true := by decide +kernel
theorem sub6_601 : sub6 [3, -2, -2] = true := by decide +kernel
theorem sub6_602 : sub6 [3, -2, -1] = true := by decide +kernel
theorem sub6_603 : sub6 [3, -2, 0] = true := by decide +kernel
theorem sub6_604 : sub6 [3, -2, 1] = true := by decide +kernel
theorem sub6_605 : sub6 [3, -2, 2] = true := by decide +kernel
theorem sub6_606 : sub6 [3, -2, 3] = true := by decide +kernel
theorem sub6_607 : sub6 [3, -2, 4] = true := by decide +kernel
theorem sb6_18 : ∀ q ∈ blk6_18, sub6 q = true := by
  unfold blk6_18
  exact List.forall_mem_cons.2 ⟨sub6_576, List.forall_mem_cons.2 ⟨sub6_577, List.forall_mem_cons.2 ⟨sub6_578, List.forall_mem_cons.2 ⟨sub6_579, List.forall_mem_cons.2 ⟨sub6_580, List.forall_mem_cons.2 ⟨sub6_581, List.forall_mem_cons.2 ⟨sub6_582, List.forall_mem_cons.2 ⟨sub6_583, List.forall_mem_cons.2 ⟨sub6_584, List.forall_mem_cons.2 ⟨sub6_585, List.forall_mem_cons.2 ⟨sub6_586, List.forall_mem_cons.2 ⟨sub6_587, List.forall_mem_cons.2 ⟨sub6_588, List.forall_mem_cons.2 ⟨sub6_589, List.forall_mem_cons.2 ⟨sub6_590, List.forall_mem_cons.2 ⟨sub6_591, List.forall_mem_cons.2 ⟨sub6_592, List.forall_mem_cons.2 ⟨sub6_593, List.forall_mem_cons.2 ⟨sub6_594, List.forall_mem_cons.2 ⟨sub6_595, List.forall_mem_cons.2 ⟨sub6_596, List.forall_mem_cons.2 ⟨sub6_597, List.forall_mem_cons.2 ⟨sub6_598, List.forall_mem_cons.2 ⟨sub6_599, List.forall_mem_cons.2 ⟨sub6_600, List.forall_mem_cons.2 ⟨sub6_601, List.forall_mem_cons.2 ⟨sub6_602, List.forall_mem_cons.2 ⟨sub6_603, List.forall_mem_cons.2 ⟨sub6_604, List.forall_mem_cons.2 ⟨sub6_605, List.forall_mem_cons.2 ⟨sub6_606, List.forall_mem_cons.2 ⟨sub6_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_608 : sub6 [3, -1, -8] = true := by decide +kernel
theorem sub6_609 : sub6 [3, -1, -7] = true := by decide +kernel
theorem sub6_610 : sub6 [3, -1, -6] = true := by decide +kernel
theorem sub6_611 : sub6 [3, -1, -5] = true := by decide +kernel
theorem sub6_612 : sub6 [3, -1, -4] = true := by decide +kernel
theorem sub6_613 : sub6 [3, -1, -3] = true := by decide +kernel
theorem sub6_614 : sub6 [3, -1, -2] = true := by decide +kernel
theorem sub6_615 : sub6 [3, -1, -1] = true := by decide +kernel
theorem sub6_616 : sub6 [3, -1, 0] = true := by decide +kernel
theorem sub6_617 : sub6 [3, -1, 1] = true := by decide +kernel
theorem sub6_618 : sub6 [3, -1, 2] = true := by decide +kernel
theorem sub6_619 : sub6 [3, -1, 3] = true := by decide +kernel
theorem sub6_620 : sub6 [3, -1, 4] = true := by decide +kernel
theorem sub6_621 : sub6 [3, -1, 5] = true := by decide +kernel
theorem sub6_622 : sub6 [3, 0, -8] = true := by decide +kernel
theorem sub6_623 : sub6 [3, 0, -7] = true := by decide +kernel
theorem sub6_624 : sub6 [3, 0, -6] = true := by decide +kernel
theorem sub6_625 : sub6 [3, 0, -5] = true := by decide +kernel
theorem sub6_626 : sub6 [3, 0, -4] = true := by decide +kernel
theorem sub6_627 : sub6 [3, 0, -3] = true := by decide +kernel
theorem sub6_628 : sub6 [3, 0, -2] = true := by decide +kernel
theorem sub6_629 : sub6 [3, 0, -1] = true := by decide +kernel
theorem sub6_630 : sub6 [3, 0, 0] = true := by decide +kernel
theorem sub6_631 : sub6 [3, 0, 1] = true := by decide +kernel
theorem sub6_632 : sub6 [3, 0, 2] = true := by decide +kernel
theorem sub6_633 : sub6 [3, 0, 3] = true := by decide +kernel
theorem sub6_634 : sub6 [3, 0, 4] = true := by decide +kernel
theorem sub6_635 : sub6 [3, 0, 5] = true := by decide +kernel
theorem sub6_636 : sub6 [3, 1, -8] = true := by decide +kernel
theorem sub6_637 : sub6 [3, 1, -7] = true := by decide +kernel
theorem sub6_638 : sub6 [3, 1, -6] = true := by decide +kernel
theorem sub6_639 : sub6 [3, 1, -5] = true := by decide +kernel
theorem sb6_19 : ∀ q ∈ blk6_19, sub6 q = true := by
  unfold blk6_19
  exact List.forall_mem_cons.2 ⟨sub6_608, List.forall_mem_cons.2 ⟨sub6_609, List.forall_mem_cons.2 ⟨sub6_610, List.forall_mem_cons.2 ⟨sub6_611, List.forall_mem_cons.2 ⟨sub6_612, List.forall_mem_cons.2 ⟨sub6_613, List.forall_mem_cons.2 ⟨sub6_614, List.forall_mem_cons.2 ⟨sub6_615, List.forall_mem_cons.2 ⟨sub6_616, List.forall_mem_cons.2 ⟨sub6_617, List.forall_mem_cons.2 ⟨sub6_618, List.forall_mem_cons.2 ⟨sub6_619, List.forall_mem_cons.2 ⟨sub6_620, List.forall_mem_cons.2 ⟨sub6_621, List.forall_mem_cons.2 ⟨sub6_622, List.forall_mem_cons.2 ⟨sub6_623, List.forall_mem_cons.2 ⟨sub6_624, List.forall_mem_cons.2 ⟨sub6_625, List.forall_mem_cons.2 ⟨sub6_626, List.forall_mem_cons.2 ⟨sub6_627, List.forall_mem_cons.2 ⟨sub6_628, List.forall_mem_cons.2 ⟨sub6_629, List.forall_mem_cons.2 ⟨sub6_630, List.forall_mem_cons.2 ⟨sub6_631, List.forall_mem_cons.2 ⟨sub6_632, List.forall_mem_cons.2 ⟨sub6_633, List.forall_mem_cons.2 ⟨sub6_634, List.forall_mem_cons.2 ⟨sub6_635, List.forall_mem_cons.2 ⟨sub6_636, List.forall_mem_cons.2 ⟨sub6_637, List.forall_mem_cons.2 ⟨sub6_638, List.forall_mem_cons.2 ⟨sub6_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_640 : sub6 [3, 1, -4] = true := by decide +kernel
theorem sub6_641 : sub6 [3, 1, -3] = true := by decide +kernel
theorem sub6_642 : sub6 [3, 1, -2] = true := by decide +kernel
theorem sub6_643 : sub6 [3, 1, -1] = true := by decide +kernel
theorem sub6_644 : sub6 [3, 1, 0] = true := by decide +kernel
theorem sub6_645 : sub6 [3, 1, 1] = true := by decide +kernel
theorem sub6_646 : sub6 [3, 1, 2] = true := by decide +kernel
theorem sub6_647 : sub6 [3, 1, 3] = true := by decide +kernel
theorem sub6_648 : sub6 [3, 1, 4] = true := by decide +kernel
theorem sub6_649 : sub6 [3, 1, 5] = true := by decide +kernel
theorem sub6_650 : sub6 [3, 2] = true := by decide +kernel
theorem sub6_651 : sub6 [3, 3] = true := by decide +kernel
theorem sub6_652 : sub6 [3, 4] = true := by decide +kernel
theorem sub6_653 : sub6 [3, 5] = true := by decide +kernel
theorem sub6_654 : sub6 [4, -7] = true := by decide +kernel
theorem sub6_655 : sub6 [4, -6] = true := by decide +kernel
theorem sub6_656 : sub6 [4, -5] = true := by decide +kernel
theorem sub6_657 : sub6 [4, -4] = true := by decide +kernel
theorem sub6_658 : sub6 [4, -3] = true := by decide +kernel
theorem sub6_659 : sub6 [4, -2] = true := by decide +kernel
theorem sub6_660 : sub6 [4, -1] = true := by decide +kernel
theorem sub6_661 : sub6 [4, 0] = true := by decide +kernel
theorem sub6_662 : sub6 [4, 1] = true := by decide +kernel
theorem sub6_663 : sub6 [4, 2] = true := by decide +kernel
theorem sub6_664 : sub6 [4, 3] = true := by decide +kernel
theorem sub6_665 : sub6 [4, 4] = true := by decide +kernel
theorem sub6_666 : sub6 [5, -7] = true := by decide +kernel
theorem sub6_667 : sub6 [5, -6] = true := by decide +kernel
theorem sub6_668 : sub6 [5, -5] = true := by decide +kernel
theorem sub6_669 : sub6 [5, -4] = true := by decide +kernel
theorem sub6_670 : sub6 [5, -3] = true := by decide +kernel
theorem sub6_671 : sub6 [5, -2] = true := by decide +kernel
theorem sb6_20 : ∀ q ∈ blk6_20, sub6 q = true := by
  unfold blk6_20
  exact List.forall_mem_cons.2 ⟨sub6_640, List.forall_mem_cons.2 ⟨sub6_641, List.forall_mem_cons.2 ⟨sub6_642, List.forall_mem_cons.2 ⟨sub6_643, List.forall_mem_cons.2 ⟨sub6_644, List.forall_mem_cons.2 ⟨sub6_645, List.forall_mem_cons.2 ⟨sub6_646, List.forall_mem_cons.2 ⟨sub6_647, List.forall_mem_cons.2 ⟨sub6_648, List.forall_mem_cons.2 ⟨sub6_649, List.forall_mem_cons.2 ⟨sub6_650, List.forall_mem_cons.2 ⟨sub6_651, List.forall_mem_cons.2 ⟨sub6_652, List.forall_mem_cons.2 ⟨sub6_653, List.forall_mem_cons.2 ⟨sub6_654, List.forall_mem_cons.2 ⟨sub6_655, List.forall_mem_cons.2 ⟨sub6_656, List.forall_mem_cons.2 ⟨sub6_657, List.forall_mem_cons.2 ⟨sub6_658, List.forall_mem_cons.2 ⟨sub6_659, List.forall_mem_cons.2 ⟨sub6_660, List.forall_mem_cons.2 ⟨sub6_661, List.forall_mem_cons.2 ⟨sub6_662, List.forall_mem_cons.2 ⟨sub6_663, List.forall_mem_cons.2 ⟨sub6_664, List.forall_mem_cons.2 ⟨sub6_665, List.forall_mem_cons.2 ⟨sub6_666, List.forall_mem_cons.2 ⟨sub6_667, List.forall_mem_cons.2 ⟨sub6_668, List.forall_mem_cons.2 ⟨sub6_669, List.forall_mem_cons.2 ⟨sub6_670, List.forall_mem_cons.2 ⟨sub6_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_672 : sub6 [5, -1] = true := by decide +kernel
theorem sub6_673 : sub6 [5, 0] = true := by decide +kernel
theorem sub6_674 : sub6 [5, 1] = true := by decide +kernel
theorem sub6_675 : sub6 [5, 2] = true := by decide +kernel
theorem sub6_676 : sub6 [5, 3] = true := by decide +kernel
theorem sub6_677 : sub6 [6, -6] = true := by decide +kernel
theorem sub6_678 : sub6 [6, -5] = true := by decide +kernel
theorem sub6_679 : sub6 [6, -4] = true := by decide +kernel
theorem sub6_680 : sub6 [6, -3] = true := by decide +kernel
theorem sub6_681 : sub6 [6, -2] = true := by decide +kernel
theorem sub6_682 : sub6 [6, -1] = true := by decide +kernel
theorem sub6_683 : sub6 [6, 0] = true := by decide +kernel
theorem sub6_684 : sub6 [6, 1] = true := by decide +kernel
theorem sub6_685 : sub6 [6, 2] = true := by decide +kernel
theorem sub6_686 : sub6 [7, -5] = true := by decide +kernel
theorem sub6_687 : sub6 [7, -4] = true := by decide +kernel
theorem sub6_688 : sub6 [7, -3] = true := by decide +kernel
theorem sub6_689 : sub6 [7, -2] = true := by decide +kernel
theorem sub6_690 : sub6 [7, -1] = true := by decide +kernel
theorem sub6_691 : sub6 [7, 0] = true := by decide +kernel
theorem sub6_692 : sub6 [7, 1] = true := by decide +kernel
theorem sb6_21 : ∀ q ∈ blk6_21, sub6 q = true := by
  unfold blk6_21
  exact List.forall_mem_cons.2 ⟨sub6_672, List.forall_mem_cons.2 ⟨sub6_673, List.forall_mem_cons.2 ⟨sub6_674, List.forall_mem_cons.2 ⟨sub6_675, List.forall_mem_cons.2 ⟨sub6_676, List.forall_mem_cons.2 ⟨sub6_677, List.forall_mem_cons.2 ⟨sub6_678, List.forall_mem_cons.2 ⟨sub6_679, List.forall_mem_cons.2 ⟨sub6_680, List.forall_mem_cons.2 ⟨sub6_681, List.forall_mem_cons.2 ⟨sub6_682, List.forall_mem_cons.2 ⟨sub6_683, List.forall_mem_cons.2 ⟨sub6_684, List.forall_mem_cons.2 ⟨sub6_685, List.forall_mem_cons.2 ⟨sub6_686, List.forall_mem_cons.2 ⟨sub6_687, List.forall_mem_cons.2 ⟨sub6_688, List.forall_mem_cons.2 ⟨sub6_689, List.forall_mem_cons.2 ⟨sub6_690, List.forall_mem_cons.2 ⟨sub6_691, List.forall_mem_cons.2 ⟨sub6_692, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_0 : sub7 [-6] = true := by decide +kernel
theorem sub7_1 : sub7 [-5, -2] = true := by decide +kernel
theorem sub7_2 : sub7 [-5, -1] = true := by decide +kernel
theorem sub7_3 : sub7 [-5, 0] = true := by decide +kernel
theorem sub7_4 : sub7 [-5, 1] = true := by decide +kernel
theorem sub7_5 : sub7 [-5, 2] = true := by decide +kernel
theorem sub7_6 : sub7 [-5, 3] = true := by decide +kernel
theorem sub7_7 : sub7 [-5, 4] = true := by decide +kernel
theorem sub7_8 : sub7 [-5, 5] = true := by decide +kernel
theorem sub7_9 : sub7 [-5, 6] = true := by decide +kernel
theorem sub7_10 : sub7 [-4, -4] = true := by decide +kernel
theorem sub7_11 : sub7 [-4, -3] = true := by decide +kernel
theorem sub7_12 : sub7 [-4, -2] = true := by decide +kernel
theorem sub7_13 : sub7 [-4, -1] = true := by decide +kernel
theorem sub7_14 : sub7 [-4, 0] = true := by decide +kernel
theorem sub7_15 : sub7 [-4, 1] = true := by decide +kernel
theorem sub7_16 : sub7 [-4, 2] = true := by decide +kernel
theorem sub7_17 : sub7 [-4, 3] = true := by decide +kernel
theorem sub7_18 : sub7 [-4, 4] = true := by decide +kernel
theorem sub7_19 : sub7 [-4, 5] = true := by decide +kernel
theorem sub7_20 : sub7 [-4, 6] = true := by decide +kernel
theorem sub7_21 : sub7 [-3, -5] = true := by decide +kernel
theorem sub7_22 : sub7 [-3, -4] = true := by decide +kernel
theorem sub7_23 : sub7 [-3, -3] = true := by decide +kernel
theorem sub7_24 : sub7 [-3, -2] = true := by decide +kernel
theorem sub7_25 : sub7 [-3, -1] = true := by decide +kernel
theorem sub7_26 : sub7 [-3, 0, -6] = true := by decide +kernel
theorem sub7_27 : sub7 [-3, 0, -5] = true := by decide +kernel
theorem sub7_28 : sub7 [-3, 0, -4] = true := by decide +kernel
theorem sub7_29 : sub7 [-3, 0, -3] = true := by decide +kernel
theorem sub7_30 : sub7 [-3, 0, -2] = true := by decide +kernel
theorem sub7_31 : sub7 [-3, 0, -1] = true := by decide +kernel
theorem sb7_0 : ∀ q ∈ blk7_0, sub7 q = true := by
  unfold blk7_0
  exact List.forall_mem_cons.2 ⟨sub7_0, List.forall_mem_cons.2 ⟨sub7_1, List.forall_mem_cons.2 ⟨sub7_2, List.forall_mem_cons.2 ⟨sub7_3, List.forall_mem_cons.2 ⟨sub7_4, List.forall_mem_cons.2 ⟨sub7_5, List.forall_mem_cons.2 ⟨sub7_6, List.forall_mem_cons.2 ⟨sub7_7, List.forall_mem_cons.2 ⟨sub7_8, List.forall_mem_cons.2 ⟨sub7_9, List.forall_mem_cons.2 ⟨sub7_10, List.forall_mem_cons.2 ⟨sub7_11, List.forall_mem_cons.2 ⟨sub7_12, List.forall_mem_cons.2 ⟨sub7_13, List.forall_mem_cons.2 ⟨sub7_14, List.forall_mem_cons.2 ⟨sub7_15, List.forall_mem_cons.2 ⟨sub7_16, List.forall_mem_cons.2 ⟨sub7_17, List.forall_mem_cons.2 ⟨sub7_18, List.forall_mem_cons.2 ⟨sub7_19, List.forall_mem_cons.2 ⟨sub7_20, List.forall_mem_cons.2 ⟨sub7_21, List.forall_mem_cons.2 ⟨sub7_22, List.forall_mem_cons.2 ⟨sub7_23, List.forall_mem_cons.2 ⟨sub7_24, List.forall_mem_cons.2 ⟨sub7_25, List.forall_mem_cons.2 ⟨sub7_26, List.forall_mem_cons.2 ⟨sub7_27, List.forall_mem_cons.2 ⟨sub7_28, List.forall_mem_cons.2 ⟨sub7_29, List.forall_mem_cons.2 ⟨sub7_30, List.forall_mem_cons.2 ⟨sub7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_32 : sub7 [-3, 0, 0] = true := by decide +kernel
theorem sub7_33 : sub7 [-3, 0, 1] = true := by decide +kernel
theorem sub7_34 : sub7 [-3, 0, 2] = true := by decide +kernel
theorem sub7_35 : sub7 [-3, 0, 3] = true := by decide +kernel
theorem sub7_36 : sub7 [-3, 0, 4] = true := by decide +kernel
theorem sub7_37 : sub7 [-3, 0, 5] = true := by decide +kernel
theorem sub7_38 : sub7 [-3, 0, 6] = true := by decide +kernel
theorem sub7_39 : sub7 [-3, 0, 7] = true := by decide +kernel
theorem sub7_40 : sub7 [-3, 1, -6] = true := by decide +kernel
theorem sub7_41 : sub7 [-3, 1, -5] = true := by decide +kernel
theorem sub7_42 : sub7 [-3, 1, -4] = true := by decide +kernel
theorem sub7_43 : sub7 [-3, 1, -3] = true := by decide +kernel
theorem sub7_44 : sub7 [-3, 1, -2] = true := by decide +kernel
theorem sub7_45 : sub7 [-3, 1, -1] = true := by decide +kernel
theorem sub7_46 : sub7 [-3, 1, 0] = true := by decide +kernel
theorem sub7_47 : sub7 [-3, 1, 1] = true := by decide +kernel
theorem sub7_48 : sub7 [-3, 1, 2] = true := by decide +kernel
theorem sub7_49 : sub7 [-3, 1, 3] = true := by decide +kernel
theorem sub7_50 : sub7 [-3, 1, 4] = true := by decide +kernel
theorem sub7_51 : sub7 [-3, 1, 5] = true := by decide +kernel
theorem sub7_52 : sub7 [-3, 1, 6] = true := by decide +kernel
theorem sub7_53 : sub7 [-3, 1, 7] = true := by decide +kernel
theorem sub7_54 : sub7 [-3, 2, -6] = true := by decide +kernel
theorem sub7_55 : sub7 [-3, 2, -5] = true := by decide +kernel
theorem sub7_56 : sub7 [-3, 2, -4] = true := by decide +kernel
theorem sub7_57 : sub7 [-3, 2, -3] = true := by decide +kernel
theorem sub7_58 : sub7 [-3, 2, -2] = true := by decide +kernel
theorem sub7_59 : sub7 [-3, 2, -1] = true := by decide +kernel
theorem sub7_60 : sub7 [-3, 2, 0] = true := by decide +kernel
theorem sub7_61 : sub7 [-3, 2, 1] = true := by decide +kernel
theorem sub7_62 : sub7 [-3, 2, 2] = true := by decide +kernel
theorem sub7_63 : sub7 [-3, 2, 3] = true := by decide +kernel
theorem sb7_1 : ∀ q ∈ blk7_1, sub7 q = true := by
  unfold blk7_1
  exact List.forall_mem_cons.2 ⟨sub7_32, List.forall_mem_cons.2 ⟨sub7_33, List.forall_mem_cons.2 ⟨sub7_34, List.forall_mem_cons.2 ⟨sub7_35, List.forall_mem_cons.2 ⟨sub7_36, List.forall_mem_cons.2 ⟨sub7_37, List.forall_mem_cons.2 ⟨sub7_38, List.forall_mem_cons.2 ⟨sub7_39, List.forall_mem_cons.2 ⟨sub7_40, List.forall_mem_cons.2 ⟨sub7_41, List.forall_mem_cons.2 ⟨sub7_42, List.forall_mem_cons.2 ⟨sub7_43, List.forall_mem_cons.2 ⟨sub7_44, List.forall_mem_cons.2 ⟨sub7_45, List.forall_mem_cons.2 ⟨sub7_46, List.forall_mem_cons.2 ⟨sub7_47, List.forall_mem_cons.2 ⟨sub7_48, List.forall_mem_cons.2 ⟨sub7_49, List.forall_mem_cons.2 ⟨sub7_50, List.forall_mem_cons.2 ⟨sub7_51, List.forall_mem_cons.2 ⟨sub7_52, List.forall_mem_cons.2 ⟨sub7_53, List.forall_mem_cons.2 ⟨sub7_54, List.forall_mem_cons.2 ⟨sub7_55, List.forall_mem_cons.2 ⟨sub7_56, List.forall_mem_cons.2 ⟨sub7_57, List.forall_mem_cons.2 ⟨sub7_58, List.forall_mem_cons.2 ⟨sub7_59, List.forall_mem_cons.2 ⟨sub7_60, List.forall_mem_cons.2 ⟨sub7_61, List.forall_mem_cons.2 ⟨sub7_62, List.forall_mem_cons.2 ⟨sub7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C083
