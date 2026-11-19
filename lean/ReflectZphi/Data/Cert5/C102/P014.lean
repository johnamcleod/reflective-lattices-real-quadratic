import ReflectZphi.Data.Cert5.C102.Base

namespace ReflectZphi.Data.Cert5.C102
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub9_512 : sub9 [2, -4] = true := by decide +kernel
theorem sub9_513 : sub9 [2, -3, -7] = true := by decide +kernel
theorem sub9_514 : sub9 [2, -3, -6] = true := by decide +kernel
theorem sub9_515 : sub9 [2, -3, -5] = true := by decide +kernel
theorem sub9_516 : sub9 [2, -3, -4] = true := by decide +kernel
theorem sub9_517 : sub9 [2, -3, -3] = true := by decide +kernel
theorem sub9_518 : sub9 [2, -3, -2] = true := by decide +kernel
theorem sub9_519 : sub9 [2, -3, -1] = true := by decide +kernel
theorem sub9_520 : sub9 [2, -3, 0] = true := by decide +kernel
theorem sub9_521 : sub9 [2, -3, 1] = true := by decide +kernel
theorem sub9_522 : sub9 [2, -3, 2] = true := by decide +kernel
theorem sub9_523 : sub9 [2, -3, 3] = true := by decide +kernel
theorem sub9_524 : sub9 [2, -3, 4] = true := by decide +kernel
theorem sub9_525 : sub9 [2, -3, 5] = true := by decide +kernel
theorem sub9_526 : sub9 [2, -3, 6] = true := by decide +kernel
theorem sub9_527 : sub9 [2, -2, -8] = true := by decide +kernel
theorem sub9_528 : sub9 [2, -2, -7] = true := by decide +kernel
theorem sub9_529 : sub9 [2, -2, -6] = true := by decide +kernel
theorem sub9_530 : sub9 [2, -2, -5] = true := by decide +kernel
theorem sub9_531 : sub9 [2, -2, -4] = true := by decide +kernel
theorem sub9_532 : sub9 [2, -2, -3] = true := by decide +kernel
theorem sub9_533 : sub9 [2, -2, -2] = true := by decide +kernel
theorem sub9_534 : sub9 [2, -2, -1] = true := by decide +kernel
theorem sub9_535 : sub9 [2, -2, 0] = true := by decide +kernel
theorem sub9_536 : sub9 [2, -2, 1] = true := by decide +kernel
theorem sub9_537 : sub9 [2, -2, 2] = true := by decide +kernel
theorem sub9_538 : sub9 [2, -2, 3] = true := by decide +kernel
theorem sub9_539 : sub9 [2, -2, 4] = true := by decide +kernel
theorem sub9_540 : sub9 [2, -2, 5] = true := by decide +kernel
theorem sub9_541 : sub9 [2, -2, 6] = true := by decide +kernel
theorem sub9_542 : sub9 [2, -2, 7] = true := by decide +kernel
theorem sub9_543 : sub9 [2, -1, -8] = true := by decide +kernel
theorem sb9_16 : ∀ q ∈ blk9_16, sub9 q = true := by
  unfold blk9_16
  exact List.forall_mem_cons.2 ⟨sub9_512, List.forall_mem_cons.2 ⟨sub9_513, List.forall_mem_cons.2 ⟨sub9_514, List.forall_mem_cons.2 ⟨sub9_515, List.forall_mem_cons.2 ⟨sub9_516, List.forall_mem_cons.2 ⟨sub9_517, List.forall_mem_cons.2 ⟨sub9_518, List.forall_mem_cons.2 ⟨sub9_519, List.forall_mem_cons.2 ⟨sub9_520, List.forall_mem_cons.2 ⟨sub9_521, List.forall_mem_cons.2 ⟨sub9_522, List.forall_mem_cons.2 ⟨sub9_523, List.forall_mem_cons.2 ⟨sub9_524, List.forall_mem_cons.2 ⟨sub9_525, List.forall_mem_cons.2 ⟨sub9_526, List.forall_mem_cons.2 ⟨sub9_527, List.forall_mem_cons.2 ⟨sub9_528, List.forall_mem_cons.2 ⟨sub9_529, List.forall_mem_cons.2 ⟨sub9_530, List.forall_mem_cons.2 ⟨sub9_531, List.forall_mem_cons.2 ⟨sub9_532, List.forall_mem_cons.2 ⟨sub9_533, List.forall_mem_cons.2 ⟨sub9_534, List.forall_mem_cons.2 ⟨sub9_535, List.forall_mem_cons.2 ⟨sub9_536, List.forall_mem_cons.2 ⟨sub9_537, List.forall_mem_cons.2 ⟨sub9_538, List.forall_mem_cons.2 ⟨sub9_539, List.forall_mem_cons.2 ⟨sub9_540, List.forall_mem_cons.2 ⟨sub9_541, List.forall_mem_cons.2 ⟨sub9_542, List.forall_mem_cons.2 ⟨sub9_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_544 : sub9 [2, -1, -7] = true := by decide +kernel
theorem sub9_545 : sub9 [2, -1, -6] = true := by decide +kernel
theorem sub9_546 : sub9 [2, -1, -5] = true := by decide +kernel
theorem sub9_547 : sub9 [2, -1, -4] = true := by decide +kernel
theorem sub9_548 : sub9 [2, -1, -3] = true := by decide +kernel
theorem sub9_549 : sub9 [2, -1, -2] = true := by decide +kernel
theorem sub9_550 : sub9 [2, -1, -1] = true := by decide +kernel
theorem sub9_551 : sub9 [2, -1, 0] = true := by decide +kernel
theorem sub9_552 : sub9 [2, -1, 1] = true := by decide +kernel
theorem sub9_553 : sub9 [2, -1, 2] = true := by decide +kernel
theorem sub9_554 : sub9 [2, -1, 3] = true := by decide +kernel
theorem sub9_555 : sub9 [2, -1, 4] = true := by decide +kernel
theorem sub9_556 : sub9 [2, -1, 5] = true := by decide +kernel
theorem sub9_557 : sub9 [2, -1, 6] = true := by decide +kernel
theorem sub9_558 : sub9 [2, -1, 7] = true := by decide +kernel
theorem sub9_559 : sub9 [2, 0, -8] = true := by decide +kernel
theorem sub9_560 : sub9 [2, 0, -7] = true := by decide +kernel
theorem sub9_561 : sub9 [2, 0, -6] = true := by decide +kernel
theorem sub9_562 : sub9 [2, 0, -5] = true := by decide +kernel
theorem sub9_563 : sub9 [2, 0, -4] = true := by decide +kernel
theorem sub9_564 : sub9 [2, 0, -3] = true := by decide +kernel
theorem sub9_565 : sub9 [2, 0, -2] = true := by decide +kernel
theorem sub9_566 : sub9 [2, 0, -1] = true := by decide +kernel
theorem sub9_567 : sub9 [2, 0, 0] = true := by decide +kernel
theorem sub9_568 : sub9 [2, 0, 1] = true := by decide +kernel
theorem sub9_569 : sub9 [2, 0, 2] = true := by decide +kernel
theorem sub9_570 : sub9 [2, 0, 3] = true := by decide +kernel
theorem sub9_571 : sub9 [2, 0, 4] = true := by decide +kernel
theorem sub9_572 : sub9 [2, 0, 5] = true := by decide +kernel
theorem sub9_573 : sub9 [2, 0, 6] = true := by decide +kernel
theorem sub9_574 : sub9 [2, 0, 7] = true := by decide +kernel
theorem sub9_575 : sub9 [2, 1, -7] = true := by decide +kernel
theorem sb9_17 : ∀ q ∈ blk9_17, sub9 q = true := by
  unfold blk9_17
  exact List.forall_mem_cons.2 ⟨sub9_544, List.forall_mem_cons.2 ⟨sub9_545, List.forall_mem_cons.2 ⟨sub9_546, List.forall_mem_cons.2 ⟨sub9_547, List.forall_mem_cons.2 ⟨sub9_548, List.forall_mem_cons.2 ⟨sub9_549, List.forall_mem_cons.2 ⟨sub9_550, List.forall_mem_cons.2 ⟨sub9_551, List.forall_mem_cons.2 ⟨sub9_552, List.forall_mem_cons.2 ⟨sub9_553, List.forall_mem_cons.2 ⟨sub9_554, List.forall_mem_cons.2 ⟨sub9_555, List.forall_mem_cons.2 ⟨sub9_556, List.forall_mem_cons.2 ⟨sub9_557, List.forall_mem_cons.2 ⟨sub9_558, List.forall_mem_cons.2 ⟨sub9_559, List.forall_mem_cons.2 ⟨sub9_560, List.forall_mem_cons.2 ⟨sub9_561, List.forall_mem_cons.2 ⟨sub9_562, List.forall_mem_cons.2 ⟨sub9_563, List.forall_mem_cons.2 ⟨sub9_564, List.forall_mem_cons.2 ⟨sub9_565, List.forall_mem_cons.2 ⟨sub9_566, List.forall_mem_cons.2 ⟨sub9_567, List.forall_mem_cons.2 ⟨sub9_568, List.forall_mem_cons.2 ⟨sub9_569, List.forall_mem_cons.2 ⟨sub9_570, List.forall_mem_cons.2 ⟨sub9_571, List.forall_mem_cons.2 ⟨sub9_572, List.forall_mem_cons.2 ⟨sub9_573, List.forall_mem_cons.2 ⟨sub9_574, List.forall_mem_cons.2 ⟨sub9_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_576 : sub9 [2, 1, -6] = true := by decide +kernel
theorem sub9_577 : sub9 [2, 1, -5] = true := by decide +kernel
theorem sub9_578 : sub9 [2, 1, -4] = true := by decide +kernel
theorem sub9_579 : sub9 [2, 1, -3] = true := by decide +kernel
theorem sub9_580 : sub9 [2, 1, -2] = true := by decide +kernel
theorem sub9_581 : sub9 [2, 1, -1] = true := by decide +kernel
theorem sub9_582 : sub9 [2, 1, 0] = true := by decide +kernel
theorem sub9_583 : sub9 [2, 1, 1] = true := by decide +kernel
theorem sub9_584 : sub9 [2, 1, 2] = true := by decide +kernel
theorem sub9_585 : sub9 [2, 1, 3] = true := by decide +kernel
theorem sub9_586 : sub9 [2, 1, 4] = true := by decide +kernel
theorem sub9_587 : sub9 [2, 1, 5] = true := by decide +kernel
theorem sub9_588 : sub9 [2, 1, 6] = true := by decide +kernel
theorem sub9_589 : sub9 [2, 1, 7] = true := by decide +kernel
theorem sub9_590 : sub9 [2, 2, -6] = true := by decide +kernel
theorem sub9_591 : sub9 [2, 2, -5] = true := by decide +kernel
theorem sub9_592 : sub9 [2, 2, -4] = true := by decide +kernel
theorem sub9_593 : sub9 [2, 2, -3] = true := by decide +kernel
theorem sub9_594 : sub9 [2, 2, -2] = true := by decide +kernel
theorem sub9_595 : sub9 [2, 2, -1] = true := by decide +kernel
theorem sub9_596 : sub9 [2, 2, 0] = true := by decide +kernel
theorem sub9_597 : sub9 [2, 2, 1] = true := by decide +kernel
theorem sub9_598 : sub9 [2, 2, 2] = true := by decide +kernel
theorem sub9_599 : sub9 [2, 2, 3] = true := by decide +kernel
theorem sub9_600 : sub9 [2, 2, 4] = true := by decide +kernel
theorem sub9_601 : sub9 [2, 2, 5] = true := by decide +kernel
theorem sub9_602 : sub9 [2, 2, 6] = true := by decide +kernel
theorem sub9_603 : sub9 [2, 2, 7] = true := by decide +kernel
theorem sub9_604 : sub9 [2, 3] = true := by decide +kernel
theorem sub9_605 : sub9 [2, 4] = true := by decide +kernel
theorem sub9_606 : sub9 [3, -6] = true := by decide +kernel
theorem sub9_607 : sub9 [3, -5] = true := by decide +kernel
theorem sb9_18 : ∀ q ∈ blk9_18, sub9 q = true := by
  unfold blk9_18
  exact List.forall_mem_cons.2 ⟨sub9_576, List.forall_mem_cons.2 ⟨sub9_577, List.forall_mem_cons.2 ⟨sub9_578, List.forall_mem_cons.2 ⟨sub9_579, List.forall_mem_cons.2 ⟨sub9_580, List.forall_mem_cons.2 ⟨sub9_581, List.forall_mem_cons.2 ⟨sub9_582, List.forall_mem_cons.2 ⟨sub9_583, List.forall_mem_cons.2 ⟨sub9_584, List.forall_mem_cons.2 ⟨sub9_585, List.forall_mem_cons.2 ⟨sub9_586, List.forall_mem_cons.2 ⟨sub9_587, List.forall_mem_cons.2 ⟨sub9_588, List.forall_mem_cons.2 ⟨sub9_589, List.forall_mem_cons.2 ⟨sub9_590, List.forall_mem_cons.2 ⟨sub9_591, List.forall_mem_cons.2 ⟨sub9_592, List.forall_mem_cons.2 ⟨sub9_593, List.forall_mem_cons.2 ⟨sub9_594, List.forall_mem_cons.2 ⟨sub9_595, List.forall_mem_cons.2 ⟨sub9_596, List.forall_mem_cons.2 ⟨sub9_597, List.forall_mem_cons.2 ⟨sub9_598, List.forall_mem_cons.2 ⟨sub9_599, List.forall_mem_cons.2 ⟨sub9_600, List.forall_mem_cons.2 ⟨sub9_601, List.forall_mem_cons.2 ⟨sub9_602, List.forall_mem_cons.2 ⟨sub9_603, List.forall_mem_cons.2 ⟨sub9_604, List.forall_mem_cons.2 ⟨sub9_605, List.forall_mem_cons.2 ⟨sub9_606, List.forall_mem_cons.2 ⟨sub9_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_608 : sub9 [3, -4] = true := by decide +kernel
theorem sub9_609 : sub9 [3, -3] = true := by decide +kernel
theorem sub9_610 : sub9 [3, -2, -7] = true := by decide +kernel
theorem sub9_611 : sub9 [3, -2, -6] = true := by decide +kernel
theorem sub9_612 : sub9 [3, -2, -5] = true := by decide +kernel
theorem sub9_613 : sub9 [3, -2, -4] = true := by decide +kernel
theorem sub9_614 : sub9 [3, -2, -3] = true := by decide +kernel
theorem sub9_615 : sub9 [3, -2, -2] = true := by decide +kernel
theorem sub9_616 : sub9 [3, -2, -1] = true := by decide +kernel
theorem sub9_617 : sub9 [3, -2, 0] = true := by decide +kernel
theorem sub9_618 : sub9 [3, -2, 1] = true := by decide +kernel
theorem sub9_619 : sub9 [3, -2, 2] = true := by decide +kernel
theorem sub9_620 : sub9 [3, -2, 3] = true := by decide +kernel
theorem sub9_621 : sub9 [3, -2, 4] = true := by decide +kernel
theorem sub9_622 : sub9 [3, -2, 5] = true := by decide +kernel
theorem sub9_623 : sub9 [3, -2, 6] = true := by decide +kernel
theorem sub9_624 : sub9 [3, -1, -7] = true := by decide +kernel
theorem sub9_625 : sub9 [3, -1, -6] = true := by decide +kernel
theorem sub9_626 : sub9 [3, -1, -5] = true := by decide +kernel
theorem sub9_627 : sub9 [3, -1, -4] = true := by decide +kernel
theorem sub9_628 : sub9 [3, -1, -3] = true := by decide +kernel
theorem sub9_629 : sub9 [3, -1, -2] = true := by decide +kernel
theorem sub9_630 : sub9 [3, -1, -1] = true := by decide +kernel
theorem sub9_631 : sub9 [3, -1, 0] = true := by decide +kernel
theorem sub9_632 : sub9 [3, -1, 1] = true := by decide +kernel
theorem sub9_633 : sub9 [3, -1, 2] = true := by decide +kernel
theorem sub9_634 : sub9 [3, -1, 3] = true := by decide +kernel
theorem sub9_635 : sub9 [3, -1, 4] = true := by decide +kernel
theorem sub9_636 : sub9 [3, -1, 5] = true := by decide +kernel
theorem sub9_637 : sub9 [3, -1, 6] = true := by decide +kernel
theorem sub9_638 : sub9 [3, 0, -6] = true := by decide +kernel
theorem sub9_639 : sub9 [3, 0, -5] = true := by decide +kernel
theorem sb9_19 : ∀ q ∈ blk9_19, sub9 q = true := by
  unfold blk9_19
  exact List.forall_mem_cons.2 ⟨sub9_608, List.forall_mem_cons.2 ⟨sub9_609, List.forall_mem_cons.2 ⟨sub9_610, List.forall_mem_cons.2 ⟨sub9_611, List.forall_mem_cons.2 ⟨sub9_612, List.forall_mem_cons.2 ⟨sub9_613, List.forall_mem_cons.2 ⟨sub9_614, List.forall_mem_cons.2 ⟨sub9_615, List.forall_mem_cons.2 ⟨sub9_616, List.forall_mem_cons.2 ⟨sub9_617, List.forall_mem_cons.2 ⟨sub9_618, List.forall_mem_cons.2 ⟨sub9_619, List.forall_mem_cons.2 ⟨sub9_620, List.forall_mem_cons.2 ⟨sub9_621, List.forall_mem_cons.2 ⟨sub9_622, List.forall_mem_cons.2 ⟨sub9_623, List.forall_mem_cons.2 ⟨sub9_624, List.forall_mem_cons.2 ⟨sub9_625, List.forall_mem_cons.2 ⟨sub9_626, List.forall_mem_cons.2 ⟨sub9_627, List.forall_mem_cons.2 ⟨sub9_628, List.forall_mem_cons.2 ⟨sub9_629, List.forall_mem_cons.2 ⟨sub9_630, List.forall_mem_cons.2 ⟨sub9_631, List.forall_mem_cons.2 ⟨sub9_632, List.forall_mem_cons.2 ⟨sub9_633, List.forall_mem_cons.2 ⟨sub9_634, List.forall_mem_cons.2 ⟨sub9_635, List.forall_mem_cons.2 ⟨sub9_636, List.forall_mem_cons.2 ⟨sub9_637, List.forall_mem_cons.2 ⟨sub9_638, List.forall_mem_cons.2 ⟨sub9_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_640 : sub9 [3, 0, -4] = true := by decide +kernel
theorem sub9_641 : sub9 [3, 0, -3] = true := by decide +kernel
theorem sub9_642 : sub9 [3, 0, -2] = true := by decide +kernel
theorem sub9_643 : sub9 [3, 0, -1] = true := by decide +kernel
theorem sub9_644 : sub9 [3, 0, 0] = true := by decide +kernel
theorem sub9_645 : sub9 [3, 0, 1] = true := by decide +kernel
theorem sub9_646 : sub9 [3, 0, 2] = true := by decide +kernel
theorem sub9_647 : sub9 [3, 0, 3] = true := by decide +kernel
theorem sub9_648 : sub9 [3, 0, 4] = true := by decide +kernel
theorem sub9_649 : sub9 [3, 0, 5] = true := by decide +kernel
theorem sub9_650 : sub9 [3, 0, 6] = true := by decide +kernel
theorem sub9_651 : sub9 [3, 1] = true := by decide +kernel
theorem sub9_652 : sub9 [3, 2] = true := by decide +kernel
theorem sub9_653 : sub9 [3, 3] = true := by decide +kernel
theorem sub9_654 : sub9 [4, -5] = true := by decide +kernel
theorem sub9_655 : sub9 [4, -4] = true := by decide +kernel
theorem sub9_656 : sub9 [4, -3] = true := by decide +kernel
theorem sub9_657 : sub9 [4, -2] = true := by decide +kernel
theorem sub9_658 : sub9 [4, -1] = true := by decide +kernel
theorem sub9_659 : sub9 [4, 0] = true := by decide +kernel
theorem sub9_660 : sub9 [4, 1] = true := by decide +kernel
theorem sb9_20 : ∀ q ∈ blk9_20, sub9 q = true := by
  unfold blk9_20
  exact List.forall_mem_cons.2 ⟨sub9_640, List.forall_mem_cons.2 ⟨sub9_641, List.forall_mem_cons.2 ⟨sub9_642, List.forall_mem_cons.2 ⟨sub9_643, List.forall_mem_cons.2 ⟨sub9_644, List.forall_mem_cons.2 ⟨sub9_645, List.forall_mem_cons.2 ⟨sub9_646, List.forall_mem_cons.2 ⟨sub9_647, List.forall_mem_cons.2 ⟨sub9_648, List.forall_mem_cons.2 ⟨sub9_649, List.forall_mem_cons.2 ⟨sub9_650, List.forall_mem_cons.2 ⟨sub9_651, List.forall_mem_cons.2 ⟨sub9_652, List.forall_mem_cons.2 ⟨sub9_653, List.forall_mem_cons.2 ⟨sub9_654, List.forall_mem_cons.2 ⟨sub9_655, List.forall_mem_cons.2 ⟨sub9_656, List.forall_mem_cons.2 ⟨sub9_657, List.forall_mem_cons.2 ⟨sub9_658, List.forall_mem_cons.2 ⟨sub9_659, List.forall_mem_cons.2 ⟨sub9_660, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C102
