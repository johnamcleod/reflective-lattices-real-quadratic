import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_9_544 : subd6_9 [1, 2, 1] = true := by decide +kernel
theorem subd6_9_545 : subd6_9 [1, 2, 2] = true := by decide +kernel
theorem subd6_9_546 : subd6_9 [1, 2, 3] = true := by decide +kernel
theorem subd6_9_547 : subd6_9 [1, 2, 4] = true := by decide +kernel
theorem subd6_9_548 : subd6_9 [1, 2, 5] = true := by decide +kernel
theorem subd6_9_549 : subd6_9 [1, 2, 6] = true := by decide +kernel
theorem subd6_9_550 : subd6_9 [1, 2, 7] = true := by decide +kernel
theorem subd6_9_551 : subd6_9 [1, 3, -8] = true := by decide +kernel
theorem subd6_9_552 : subd6_9 [1, 3, -7] = true := by decide +kernel
theorem subd6_9_553 : subd6_9 [1, 3, -6] = true := by decide +kernel
theorem subd6_9_554 : subd6_9 [1, 3, -5] = true := by decide +kernel
theorem subd6_9_555 : subd6_9 [1, 3, -4] = true := by decide +kernel
theorem subd6_9_556 : subd6_9 [1, 3, -3] = true := by decide +kernel
theorem subd6_9_557 : subd6_9 [1, 3, -2] = true := by decide +kernel
theorem subd6_9_558 : subd6_9 [1, 3, -1] = true := by decide +kernel
theorem subd6_9_559 : subd6_9 [1, 3, 0] = true := by decide +kernel
theorem subd6_9_560 : subd6_9 [1, 3, 1] = true := by decide +kernel
theorem subd6_9_561 : subd6_9 [1, 3, 2] = true := by decide +kernel
theorem subd6_9_562 : subd6_9 [1, 3, 3] = true := by decide +kernel
theorem subd6_9_563 : subd6_9 [1, 3, 4] = true := by decide +kernel
theorem subd6_9_564 : subd6_9 [1, 3, 5] = true := by decide +kernel
theorem subd6_9_565 : subd6_9 [1, 3, 6] = true := by decide +kernel
theorem subd6_9_566 : subd6_9 [1, 4] = true := by decide +kernel
theorem subd6_9_567 : subd6_9 [1, 5] = true := by decide +kernel
theorem subd6_9_568 : subd6_9 [2, -6] = true := by decide +kernel
theorem subd6_9_569 : subd6_9 [2, -5] = true := by decide +kernel
theorem subd6_9_570 : subd6_9 [2, -4] = true := by decide +kernel
theorem subd6_9_571 : subd6_9 [2, -3, -5] = true := by decide +kernel
theorem subd6_9_572 : subd6_9 [2, -3, -4] = true := by decide +kernel
theorem subd6_9_573 : subd6_9 [2, -3, -3] = true := by decide +kernel
theorem subd6_9_574 : subd6_9 [2, -3, -2] = true := by decide +kernel
theorem subd6_9_575 : subd6_9 [2, -3, -1] = true := by decide +kernel
theorem sbd6_9_17 : ∀ q ∈ blkd6_9_17, subd6_9 q = true := by
  unfold blkd6_9_17
  exact List.forall_mem_cons.2 ⟨subd6_9_544, List.forall_mem_cons.2 ⟨subd6_9_545, List.forall_mem_cons.2 ⟨subd6_9_546, List.forall_mem_cons.2 ⟨subd6_9_547, List.forall_mem_cons.2 ⟨subd6_9_548, List.forall_mem_cons.2 ⟨subd6_9_549, List.forall_mem_cons.2 ⟨subd6_9_550, List.forall_mem_cons.2 ⟨subd6_9_551, List.forall_mem_cons.2 ⟨subd6_9_552, List.forall_mem_cons.2 ⟨subd6_9_553, List.forall_mem_cons.2 ⟨subd6_9_554, List.forall_mem_cons.2 ⟨subd6_9_555, List.forall_mem_cons.2 ⟨subd6_9_556, List.forall_mem_cons.2 ⟨subd6_9_557, List.forall_mem_cons.2 ⟨subd6_9_558, List.forall_mem_cons.2 ⟨subd6_9_559, List.forall_mem_cons.2 ⟨subd6_9_560, List.forall_mem_cons.2 ⟨subd6_9_561, List.forall_mem_cons.2 ⟨subd6_9_562, List.forall_mem_cons.2 ⟨subd6_9_563, List.forall_mem_cons.2 ⟨subd6_9_564, List.forall_mem_cons.2 ⟨subd6_9_565, List.forall_mem_cons.2 ⟨subd6_9_566, List.forall_mem_cons.2 ⟨subd6_9_567, List.forall_mem_cons.2 ⟨subd6_9_568, List.forall_mem_cons.2 ⟨subd6_9_569, List.forall_mem_cons.2 ⟨subd6_9_570, List.forall_mem_cons.2 ⟨subd6_9_571, List.forall_mem_cons.2 ⟨subd6_9_572, List.forall_mem_cons.2 ⟨subd6_9_573, List.forall_mem_cons.2 ⟨subd6_9_574, List.forall_mem_cons.2 ⟨subd6_9_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_576 : subd6_9 [2, -3, 0] = true := by decide +kernel
theorem subd6_9_577 : subd6_9 [2, -3, 1] = true := by decide +kernel
theorem subd6_9_578 : subd6_9 [2, -3, 2] = true := by decide +kernel
theorem subd6_9_579 : subd6_9 [2, -3, 3] = true := by decide +kernel
theorem subd6_9_580 : subd6_9 [2, -3, 4] = true := by decide +kernel
theorem subd6_9_581 : subd6_9 [2, -3, 5] = true := by decide +kernel
theorem subd6_9_582 : subd6_9 [2, -3, 6] = true := by decide +kernel
theorem subd6_9_583 : subd6_9 [2, -3, 7] = true := by decide +kernel
theorem subd6_9_584 : subd6_9 [2, -3, 8] = true := by decide +kernel
theorem subd6_9_585 : subd6_9 [2, -2, -6] = true := by decide +kernel
theorem subd6_9_586 : subd6_9 [2, -2, -5] = true := by decide +kernel
theorem subd6_9_587 : subd6_9 [2, -2, -4] = true := by decide +kernel
theorem subd6_9_588 : subd6_9 [2, -2, -3] = true := by decide +kernel
theorem subd6_9_589 : subd6_9 [2, -2, -2] = true := by decide +kernel
theorem subd6_9_590 : subd6_9 [2, -2, -1] = true := by decide +kernel
theorem subd6_9_591 : subd6_9 [2, -2, 0] = true := by decide +kernel
theorem subd6_9_592 : subd6_9 [2, -2, 1] = true := by decide +kernel
theorem subd6_9_593 : subd6_9 [2, -2, 2] = true := by decide +kernel
theorem subd6_9_594 : subd6_9 [2, -2, 3] = true := by decide +kernel
theorem subd6_9_595 : subd6_9 [2, -2, 4] = true := by decide +kernel
theorem subd6_9_596 : subd6_9 [2, -2, 5] = true := by decide +kernel
theorem subd6_9_597 : subd6_9 [2, -2, 6] = true := by decide +kernel
theorem subd6_9_598 : subd6_9 [2, -2, 7] = true := by decide +kernel
theorem subd6_9_599 : subd6_9 [2, -2, 8] = true := by decide +kernel
theorem subd6_9_600 : subd6_9 [2, -1, -7] = true := by decide +kernel
theorem subd6_9_601 : subd6_9 [2, -1, -6] = true := by decide +kernel
theorem subd6_9_602 : subd6_9 [2, -1, -5] = true := by decide +kernel
theorem subd6_9_603 : subd6_9 [2, -1, -4] = true := by decide +kernel
theorem subd6_9_604 : subd6_9 [2, -1, -3] = true := by decide +kernel
theorem subd6_9_605 : subd6_9 [2, -1, -2] = true := by decide +kernel
theorem subd6_9_606 : subd6_9 [2, -1, -1] = true := by decide +kernel
theorem subd6_9_607 : subd6_9 [2, -1, 0] = true := by decide +kernel
theorem sbd6_9_18 : ∀ q ∈ blkd6_9_18, subd6_9 q = true := by
  unfold blkd6_9_18
  exact List.forall_mem_cons.2 ⟨subd6_9_576, List.forall_mem_cons.2 ⟨subd6_9_577, List.forall_mem_cons.2 ⟨subd6_9_578, List.forall_mem_cons.2 ⟨subd6_9_579, List.forall_mem_cons.2 ⟨subd6_9_580, List.forall_mem_cons.2 ⟨subd6_9_581, List.forall_mem_cons.2 ⟨subd6_9_582, List.forall_mem_cons.2 ⟨subd6_9_583, List.forall_mem_cons.2 ⟨subd6_9_584, List.forall_mem_cons.2 ⟨subd6_9_585, List.forall_mem_cons.2 ⟨subd6_9_586, List.forall_mem_cons.2 ⟨subd6_9_587, List.forall_mem_cons.2 ⟨subd6_9_588, List.forall_mem_cons.2 ⟨subd6_9_589, List.forall_mem_cons.2 ⟨subd6_9_590, List.forall_mem_cons.2 ⟨subd6_9_591, List.forall_mem_cons.2 ⟨subd6_9_592, List.forall_mem_cons.2 ⟨subd6_9_593, List.forall_mem_cons.2 ⟨subd6_9_594, List.forall_mem_cons.2 ⟨subd6_9_595, List.forall_mem_cons.2 ⟨subd6_9_596, List.forall_mem_cons.2 ⟨subd6_9_597, List.forall_mem_cons.2 ⟨subd6_9_598, List.forall_mem_cons.2 ⟨subd6_9_599, List.forall_mem_cons.2 ⟨subd6_9_600, List.forall_mem_cons.2 ⟨subd6_9_601, List.forall_mem_cons.2 ⟨subd6_9_602, List.forall_mem_cons.2 ⟨subd6_9_603, List.forall_mem_cons.2 ⟨subd6_9_604, List.forall_mem_cons.2 ⟨subd6_9_605, List.forall_mem_cons.2 ⟨subd6_9_606, List.forall_mem_cons.2 ⟨subd6_9_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_608 : subd6_9 [2, -1, 1] = true := by decide +kernel
theorem subd6_9_609 : subd6_9 [2, -1, 2] = true := by decide +kernel
theorem subd6_9_610 : subd6_9 [2, -1, 3] = true := by decide +kernel
theorem subd6_9_611 : subd6_9 [2, -1, 4] = true := by decide +kernel
theorem subd6_9_612 : subd6_9 [2, -1, 5] = true := by decide +kernel
theorem subd6_9_613 : subd6_9 [2, -1, 6] = true := by decide +kernel
theorem subd6_9_614 : subd6_9 [2, -1, 7] = true := by decide +kernel
theorem subd6_9_615 : subd6_9 [2, -1, 8] = true := by decide +kernel
theorem subd6_9_616 : subd6_9 [2, 0, -7] = true := by decide +kernel
theorem subd6_9_617 : subd6_9 [2, 0, -6] = true := by decide +kernel
theorem subd6_9_618 : subd6_9 [2, 0, -5] = true := by decide +kernel
theorem subd6_9_619 : subd6_9 [2, 0, -4] = true := by decide +kernel
theorem subd6_9_620 : subd6_9 [2, 0, -3] = true := by decide +kernel
theorem subd6_9_621 : subd6_9 [2, 0, -2] = true := by decide +kernel
theorem subd6_9_622 : subd6_9 [2, 0, -1] = true := by decide +kernel
theorem subd6_9_623 : subd6_9 [2, 0, 0] = true := by decide +kernel
theorem subd6_9_624 : subd6_9 [2, 0, 1] = true := by decide +kernel
theorem subd6_9_625 : subd6_9 [2, 0, 2] = true := by decide +kernel
theorem subd6_9_626 : subd6_9 [2, 0, 3] = true := by decide +kernel
theorem subd6_9_627 : subd6_9 [2, 0, 4] = true := by decide +kernel
theorem subd6_9_628 : subd6_9 [2, 0, 5] = true := by decide +kernel
theorem subd6_9_629 : subd6_9 [2, 0, 6] = true := by decide +kernel
theorem subd6_9_630 : subd6_9 [2, 0, 7] = true := by decide +kernel
theorem subd6_9_631 : subd6_9 [2, 0, 8] = true := by decide +kernel
theorem subd6_9_632 : subd6_9 [2, 1, -7] = true := by decide +kernel
theorem subd6_9_633 : subd6_9 [2, 1, -6] = true := by decide +kernel
theorem subd6_9_634 : subd6_9 [2, 1, -5] = true := by decide +kernel
theorem subd6_9_635 : subd6_9 [2, 1, -4] = true := by decide +kernel
theorem subd6_9_636 : subd6_9 [2, 1, -3] = true := by decide +kernel
theorem subd6_9_637 : subd6_9 [2, 1, -2] = true := by decide +kernel
theorem subd6_9_638 : subd6_9 [2, 1, -1] = true := by decide +kernel
theorem subd6_9_639 : subd6_9 [2, 1, 0] = true := by decide +kernel
theorem sbd6_9_19 : ∀ q ∈ blkd6_9_19, subd6_9 q = true := by
  unfold blkd6_9_19
  exact List.forall_mem_cons.2 ⟨subd6_9_608, List.forall_mem_cons.2 ⟨subd6_9_609, List.forall_mem_cons.2 ⟨subd6_9_610, List.forall_mem_cons.2 ⟨subd6_9_611, List.forall_mem_cons.2 ⟨subd6_9_612, List.forall_mem_cons.2 ⟨subd6_9_613, List.forall_mem_cons.2 ⟨subd6_9_614, List.forall_mem_cons.2 ⟨subd6_9_615, List.forall_mem_cons.2 ⟨subd6_9_616, List.forall_mem_cons.2 ⟨subd6_9_617, List.forall_mem_cons.2 ⟨subd6_9_618, List.forall_mem_cons.2 ⟨subd6_9_619, List.forall_mem_cons.2 ⟨subd6_9_620, List.forall_mem_cons.2 ⟨subd6_9_621, List.forall_mem_cons.2 ⟨subd6_9_622, List.forall_mem_cons.2 ⟨subd6_9_623, List.forall_mem_cons.2 ⟨subd6_9_624, List.forall_mem_cons.2 ⟨subd6_9_625, List.forall_mem_cons.2 ⟨subd6_9_626, List.forall_mem_cons.2 ⟨subd6_9_627, List.forall_mem_cons.2 ⟨subd6_9_628, List.forall_mem_cons.2 ⟨subd6_9_629, List.forall_mem_cons.2 ⟨subd6_9_630, List.forall_mem_cons.2 ⟨subd6_9_631, List.forall_mem_cons.2 ⟨subd6_9_632, List.forall_mem_cons.2 ⟨subd6_9_633, List.forall_mem_cons.2 ⟨subd6_9_634, List.forall_mem_cons.2 ⟨subd6_9_635, List.forall_mem_cons.2 ⟨subd6_9_636, List.forall_mem_cons.2 ⟨subd6_9_637, List.forall_mem_cons.2 ⟨subd6_9_638, List.forall_mem_cons.2 ⟨subd6_9_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_640 : subd6_9 [2, 1, 1] = true := by decide +kernel
theorem subd6_9_641 : subd6_9 [2, 1, 2] = true := by decide +kernel
theorem subd6_9_642 : subd6_9 [2, 1, 3] = true := by decide +kernel
theorem subd6_9_643 : subd6_9 [2, 1, 4] = true := by decide +kernel
theorem subd6_9_644 : subd6_9 [2, 1, 5] = true := by decide +kernel
theorem subd6_9_645 : subd6_9 [2, 1, 6] = true := by decide +kernel
theorem subd6_9_646 : subd6_9 [2, 1, 7] = true := by decide +kernel
theorem subd6_9_647 : subd6_9 [2, 1, 8] = true := by decide +kernel
theorem subd6_9_648 : subd6_9 [2, 2, -7] = true := by decide +kernel
theorem subd6_9_649 : subd6_9 [2, 2, -6] = true := by decide +kernel
theorem subd6_9_650 : subd6_9 [2, 2, -5] = true := by decide +kernel
theorem subd6_9_651 : subd6_9 [2, 2, -4] = true := by decide +kernel
theorem subd6_9_652 : subd6_9 [2, 2, -3] = true := by decide +kernel
theorem subd6_9_653 : subd6_9 [2, 2, -2] = true := by decide +kernel
theorem subd6_9_654 : subd6_9 [2, 2, -1] = true := by decide +kernel
theorem subd6_9_655 : subd6_9 [2, 2, 0] = true := by decide +kernel
theorem subd6_9_656 : subd6_9 [2, 2, 1] = true := by decide +kernel
theorem subd6_9_657 : subd6_9 [2, 2, 2] = true := by decide +kernel
theorem subd6_9_658 : subd6_9 [2, 2, 3] = true := by decide +kernel
theorem subd6_9_659 : subd6_9 [2, 2, 4] = true := by decide +kernel
theorem subd6_9_660 : subd6_9 [2, 2, 5] = true := by decide +kernel
theorem subd6_9_661 : subd6_9 [2, 2, 6] = true := by decide +kernel
theorem subd6_9_662 : subd6_9 [2, 2, 7] = true := by decide +kernel
theorem subd6_9_663 : subd6_9 [2, 3, -7] = true := by decide +kernel
theorem subd6_9_664 : subd6_9 [2, 3, -6] = true := by decide +kernel
theorem subd6_9_665 : subd6_9 [2, 3, -5] = true := by decide +kernel
theorem subd6_9_666 : subd6_9 [2, 3, -4] = true := by decide +kernel
theorem subd6_9_667 : subd6_9 [2, 3, -3] = true := by decide +kernel
theorem subd6_9_668 : subd6_9 [2, 3, -2] = true := by decide +kernel
theorem subd6_9_669 : subd6_9 [2, 3, -1] = true := by decide +kernel
theorem subd6_9_670 : subd6_9 [2, 3, 0] = true := by decide +kernel
theorem subd6_9_671 : subd6_9 [2, 3, 1] = true := by decide +kernel
theorem sbd6_9_20 : ∀ q ∈ blkd6_9_20, subd6_9 q = true := by
  unfold blkd6_9_20
  exact List.forall_mem_cons.2 ⟨subd6_9_640, List.forall_mem_cons.2 ⟨subd6_9_641, List.forall_mem_cons.2 ⟨subd6_9_642, List.forall_mem_cons.2 ⟨subd6_9_643, List.forall_mem_cons.2 ⟨subd6_9_644, List.forall_mem_cons.2 ⟨subd6_9_645, List.forall_mem_cons.2 ⟨subd6_9_646, List.forall_mem_cons.2 ⟨subd6_9_647, List.forall_mem_cons.2 ⟨subd6_9_648, List.forall_mem_cons.2 ⟨subd6_9_649, List.forall_mem_cons.2 ⟨subd6_9_650, List.forall_mem_cons.2 ⟨subd6_9_651, List.forall_mem_cons.2 ⟨subd6_9_652, List.forall_mem_cons.2 ⟨subd6_9_653, List.forall_mem_cons.2 ⟨subd6_9_654, List.forall_mem_cons.2 ⟨subd6_9_655, List.forall_mem_cons.2 ⟨subd6_9_656, List.forall_mem_cons.2 ⟨subd6_9_657, List.forall_mem_cons.2 ⟨subd6_9_658, List.forall_mem_cons.2 ⟨subd6_9_659, List.forall_mem_cons.2 ⟨subd6_9_660, List.forall_mem_cons.2 ⟨subd6_9_661, List.forall_mem_cons.2 ⟨subd6_9_662, List.forall_mem_cons.2 ⟨subd6_9_663, List.forall_mem_cons.2 ⟨subd6_9_664, List.forall_mem_cons.2 ⟨subd6_9_665, List.forall_mem_cons.2 ⟨subd6_9_666, List.forall_mem_cons.2 ⟨subd6_9_667, List.forall_mem_cons.2 ⟨subd6_9_668, List.forall_mem_cons.2 ⟨subd6_9_669, List.forall_mem_cons.2 ⟨subd6_9_670, List.forall_mem_cons.2 ⟨subd6_9_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_672 : subd6_9 [2, 3, 2] = true := by decide +kernel
theorem subd6_9_673 : subd6_9 [2, 3, 3] = true := by decide +kernel
theorem subd6_9_674 : subd6_9 [2, 3, 4] = true := by decide +kernel
theorem subd6_9_675 : subd6_9 [2, 3, 5] = true := by decide +kernel
theorem subd6_9_676 : subd6_9 [2, 3, 6] = true := by decide +kernel
theorem subd6_9_677 : subd6_9 [2, 4] = true := by decide +kernel
theorem subd6_9_678 : subd6_9 [2, 5] = true := by decide +kernel
theorem subd6_9_679 : subd6_9 [3, -6] = true := by decide +kernel
theorem subd6_9_680 : subd6_9 [3, -5] = true := by decide +kernel
theorem subd6_9_681 : subd6_9 [3, -4] = true := by decide +kernel
theorem subd6_9_682 : subd6_9 [3, -3] = true := by decide +kernel
theorem subd6_9_683 : subd6_9 [3, -2, -5] = true := by decide +kernel
theorem subd6_9_684 : subd6_9 [3, -2, -4] = true := by decide +kernel
theorem subd6_9_685 : subd6_9 [3, -2, -3] = true := by decide +kernel
theorem subd6_9_686 : subd6_9 [3, -2, -2] = true := by decide +kernel
theorem subd6_9_687 : subd6_9 [3, -2, -1] = true := by decide +kernel
theorem subd6_9_688 : subd6_9 [3, -2, 0] = true := by decide +kernel
theorem subd6_9_689 : subd6_9 [3, -2, 1] = true := by decide +kernel
theorem subd6_9_690 : subd6_9 [3, -2, 2] = true := by decide +kernel
theorem subd6_9_691 : subd6_9 [3, -2, 3] = true := by decide +kernel
theorem subd6_9_692 : subd6_9 [3, -2, 4] = true := by decide +kernel
theorem subd6_9_693 : subd6_9 [3, -2, 5] = true := by decide +kernel
theorem subd6_9_694 : subd6_9 [3, -2, 6] = true := by decide +kernel
theorem subd6_9_695 : subd6_9 [3, -2, 7] = true := by decide +kernel
theorem subd6_9_696 : subd6_9 [3, -2, 8] = true := by decide +kernel
theorem subd6_9_697 : subd6_9 [3, -1, -6] = true := by decide +kernel
theorem subd6_9_698 : subd6_9 [3, -1, -5] = true := by decide +kernel
theorem subd6_9_699 : subd6_9 [3, -1, -4] = true := by decide +kernel
theorem subd6_9_700 : subd6_9 [3, -1, -3] = true := by decide +kernel
theorem subd6_9_701 : subd6_9 [3, -1, -2] = true := by decide +kernel
theorem subd6_9_702 : subd6_9 [3, -1, -1] = true := by decide +kernel
theorem subd6_9_703 : subd6_9 [3, -1, 0] = true := by decide +kernel
theorem sbd6_9_21 : ∀ q ∈ blkd6_9_21, subd6_9 q = true := by
  unfold blkd6_9_21
  exact List.forall_mem_cons.2 ⟨subd6_9_672, List.forall_mem_cons.2 ⟨subd6_9_673, List.forall_mem_cons.2 ⟨subd6_9_674, List.forall_mem_cons.2 ⟨subd6_9_675, List.forall_mem_cons.2 ⟨subd6_9_676, List.forall_mem_cons.2 ⟨subd6_9_677, List.forall_mem_cons.2 ⟨subd6_9_678, List.forall_mem_cons.2 ⟨subd6_9_679, List.forall_mem_cons.2 ⟨subd6_9_680, List.forall_mem_cons.2 ⟨subd6_9_681, List.forall_mem_cons.2 ⟨subd6_9_682, List.forall_mem_cons.2 ⟨subd6_9_683, List.forall_mem_cons.2 ⟨subd6_9_684, List.forall_mem_cons.2 ⟨subd6_9_685, List.forall_mem_cons.2 ⟨subd6_9_686, List.forall_mem_cons.2 ⟨subd6_9_687, List.forall_mem_cons.2 ⟨subd6_9_688, List.forall_mem_cons.2 ⟨subd6_9_689, List.forall_mem_cons.2 ⟨subd6_9_690, List.forall_mem_cons.2 ⟨subd6_9_691, List.forall_mem_cons.2 ⟨subd6_9_692, List.forall_mem_cons.2 ⟨subd6_9_693, List.forall_mem_cons.2 ⟨subd6_9_694, List.forall_mem_cons.2 ⟨subd6_9_695, List.forall_mem_cons.2 ⟨subd6_9_696, List.forall_mem_cons.2 ⟨subd6_9_697, List.forall_mem_cons.2 ⟨subd6_9_698, List.forall_mem_cons.2 ⟨subd6_9_699, List.forall_mem_cons.2 ⟨subd6_9_700, List.forall_mem_cons.2 ⟨subd6_9_701, List.forall_mem_cons.2 ⟨subd6_9_702, List.forall_mem_cons.2 ⟨subd6_9_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_704 : subd6_9 [3, -1, 1] = true := by decide +kernel
theorem subd6_9_705 : subd6_9 [3, -1, 2] = true := by decide +kernel
theorem subd6_9_706 : subd6_9 [3, -1, 3] = true := by decide +kernel
theorem subd6_9_707 : subd6_9 [3, -1, 4] = true := by decide +kernel
theorem subd6_9_708 : subd6_9 [3, -1, 5] = true := by decide +kernel
theorem subd6_9_709 : subd6_9 [3, -1, 6] = true := by decide +kernel
theorem subd6_9_710 : subd6_9 [3, -1, 7] = true := by decide +kernel
theorem subd6_9_711 : subd6_9 [3, -1, 8] = true := by decide +kernel
theorem subd6_9_712 : subd6_9 [3, 0, -6] = true := by decide +kernel
theorem subd6_9_713 : subd6_9 [3, 0, -5] = true := by decide +kernel
theorem subd6_9_714 : subd6_9 [3, 0, -4] = true := by decide +kernel
theorem subd6_9_715 : subd6_9 [3, 0, -3] = true := by decide +kernel
theorem subd6_9_716 : subd6_9 [3, 0, -2] = true := by decide +kernel
theorem subd6_9_717 : subd6_9 [3, 0, -1] = true := by decide +kernel
theorem subd6_9_718 : subd6_9 [3, 0, 0] = true := by decide +kernel
theorem subd6_9_719 : subd6_9 [3, 0, 1] = true := by decide +kernel
theorem subd6_9_720 : subd6_9 [3, 0, 2] = true := by decide +kernel
theorem subd6_9_721 : subd6_9 [3, 0, 3] = true := by decide +kernel
theorem subd6_9_722 : subd6_9 [3, 0, 4] = true := by decide +kernel
theorem subd6_9_723 : subd6_9 [3, 0, 5] = true := by decide +kernel
theorem subd6_9_724 : subd6_9 [3, 0, 6] = true := by decide +kernel
theorem subd6_9_725 : subd6_9 [3, 0, 7] = true := by decide +kernel
theorem subd6_9_726 : subd6_9 [3, 0, 8] = true := by decide +kernel
theorem subd6_9_727 : subd6_9 [3, 1, -6] = true := by decide +kernel
theorem subd6_9_728 : subd6_9 [3, 1, -5] = true := by decide +kernel
theorem subd6_9_729 : subd6_9 [3, 1, -4] = true := by decide +kernel
theorem subd6_9_730 : subd6_9 [3, 1, -3] = true := by decide +kernel
theorem subd6_9_731 : subd6_9 [3, 1, -2] = true := by decide +kernel
theorem subd6_9_732 : subd6_9 [3, 1, -1] = true := by decide +kernel
theorem subd6_9_733 : subd6_9 [3, 1, 0] = true := by decide +kernel
theorem subd6_9_734 : subd6_9 [3, 1, 1] = true := by decide +kernel
theorem subd6_9_735 : subd6_9 [3, 1, 2] = true := by decide +kernel
theorem sbd6_9_22 : ∀ q ∈ blkd6_9_22, subd6_9 q = true := by
  unfold blkd6_9_22
  exact List.forall_mem_cons.2 ⟨subd6_9_704, List.forall_mem_cons.2 ⟨subd6_9_705, List.forall_mem_cons.2 ⟨subd6_9_706, List.forall_mem_cons.2 ⟨subd6_9_707, List.forall_mem_cons.2 ⟨subd6_9_708, List.forall_mem_cons.2 ⟨subd6_9_709, List.forall_mem_cons.2 ⟨subd6_9_710, List.forall_mem_cons.2 ⟨subd6_9_711, List.forall_mem_cons.2 ⟨subd6_9_712, List.forall_mem_cons.2 ⟨subd6_9_713, List.forall_mem_cons.2 ⟨subd6_9_714, List.forall_mem_cons.2 ⟨subd6_9_715, List.forall_mem_cons.2 ⟨subd6_9_716, List.forall_mem_cons.2 ⟨subd6_9_717, List.forall_mem_cons.2 ⟨subd6_9_718, List.forall_mem_cons.2 ⟨subd6_9_719, List.forall_mem_cons.2 ⟨subd6_9_720, List.forall_mem_cons.2 ⟨subd6_9_721, List.forall_mem_cons.2 ⟨subd6_9_722, List.forall_mem_cons.2 ⟨subd6_9_723, List.forall_mem_cons.2 ⟨subd6_9_724, List.forall_mem_cons.2 ⟨subd6_9_725, List.forall_mem_cons.2 ⟨subd6_9_726, List.forall_mem_cons.2 ⟨subd6_9_727, List.forall_mem_cons.2 ⟨subd6_9_728, List.forall_mem_cons.2 ⟨subd6_9_729, List.forall_mem_cons.2 ⟨subd6_9_730, List.forall_mem_cons.2 ⟨subd6_9_731, List.forall_mem_cons.2 ⟨subd6_9_732, List.forall_mem_cons.2 ⟨subd6_9_733, List.forall_mem_cons.2 ⟨subd6_9_734, List.forall_mem_cons.2 ⟨subd6_9_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_736 : subd6_9 [3, 1, 3] = true := by decide +kernel
theorem subd6_9_737 : subd6_9 [3, 1, 4] = true := by decide +kernel
theorem subd6_9_738 : subd6_9 [3, 1, 5] = true := by decide +kernel
theorem subd6_9_739 : subd6_9 [3, 1, 6] = true := by decide +kernel
theorem subd6_9_740 : subd6_9 [3, 1, 7] = true := by decide +kernel
theorem subd6_9_741 : subd6_9 [3, 1, 8] = true := by decide +kernel
theorem subd6_9_742 : subd6_9 [3, 2, -6] = true := by decide +kernel
theorem subd6_9_743 : subd6_9 [3, 2, -5] = true := by decide +kernel
theorem subd6_9_744 : subd6_9 [3, 2, -4] = true := by decide +kernel
theorem subd6_9_745 : subd6_9 [3, 2, -3] = true := by decide +kernel
theorem subd6_9_746 : subd6_9 [3, 2, -2] = true := by decide +kernel
theorem subd6_9_747 : subd6_9 [3, 2, -1] = true := by decide +kernel
theorem subd6_9_748 : subd6_9 [3, 2, 0] = true := by decide +kernel
theorem subd6_9_749 : subd6_9 [3, 2, 1] = true := by decide +kernel
theorem subd6_9_750 : subd6_9 [3, 2, 2] = true := by decide +kernel
theorem subd6_9_751 : subd6_9 [3, 2, 3] = true := by decide +kernel
theorem subd6_9_752 : subd6_9 [3, 2, 4] = true := by decide +kernel
theorem subd6_9_753 : subd6_9 [3, 2, 5] = true := by decide +kernel
theorem subd6_9_754 : subd6_9 [3, 2, 6] = true := by decide +kernel
theorem subd6_9_755 : subd6_9 [3, 2, 7] = true := by decide +kernel
theorem subd6_9_756 : subd6_9 [3, 3] = true := by decide +kernel
theorem subd6_9_757 : subd6_9 [3, 4] = true := by decide +kernel
theorem subd6_9_758 : subd6_9 [3, 5] = true := by decide +kernel
theorem subd6_9_759 : subd6_9 [4, -5] = true := by decide +kernel
theorem subd6_9_760 : subd6_9 [4, -4] = true := by decide +kernel
theorem subd6_9_761 : subd6_9 [4, -3] = true := by decide +kernel
theorem subd6_9_762 : subd6_9 [4, -2] = true := by decide +kernel
theorem subd6_9_763 : subd6_9 [4, -1] = true := by decide +kernel
theorem subd6_9_764 : subd6_9 [4, 0] = true := by decide +kernel
theorem subd6_9_765 : subd6_9 [4, 1] = true := by decide +kernel
theorem subd6_9_766 : subd6_9 [4, 2] = true := by decide +kernel
theorem subd6_9_767 : subd6_9 [4, 3] = true := by decide +kernel
theorem sbd6_9_23 : ∀ q ∈ blkd6_9_23, subd6_9 q = true := by
  unfold blkd6_9_23
  exact List.forall_mem_cons.2 ⟨subd6_9_736, List.forall_mem_cons.2 ⟨subd6_9_737, List.forall_mem_cons.2 ⟨subd6_9_738, List.forall_mem_cons.2 ⟨subd6_9_739, List.forall_mem_cons.2 ⟨subd6_9_740, List.forall_mem_cons.2 ⟨subd6_9_741, List.forall_mem_cons.2 ⟨subd6_9_742, List.forall_mem_cons.2 ⟨subd6_9_743, List.forall_mem_cons.2 ⟨subd6_9_744, List.forall_mem_cons.2 ⟨subd6_9_745, List.forall_mem_cons.2 ⟨subd6_9_746, List.forall_mem_cons.2 ⟨subd6_9_747, List.forall_mem_cons.2 ⟨subd6_9_748, List.forall_mem_cons.2 ⟨subd6_9_749, List.forall_mem_cons.2 ⟨subd6_9_750, List.forall_mem_cons.2 ⟨subd6_9_751, List.forall_mem_cons.2 ⟨subd6_9_752, List.forall_mem_cons.2 ⟨subd6_9_753, List.forall_mem_cons.2 ⟨subd6_9_754, List.forall_mem_cons.2 ⟨subd6_9_755, List.forall_mem_cons.2 ⟨subd6_9_756, List.forall_mem_cons.2 ⟨subd6_9_757, List.forall_mem_cons.2 ⟨subd6_9_758, List.forall_mem_cons.2 ⟨subd6_9_759, List.forall_mem_cons.2 ⟨subd6_9_760, List.forall_mem_cons.2 ⟨subd6_9_761, List.forall_mem_cons.2 ⟨subd6_9_762, List.forall_mem_cons.2 ⟨subd6_9_763, List.forall_mem_cons.2 ⟨subd6_9_764, List.forall_mem_cons.2 ⟨subd6_9_765, List.forall_mem_cons.2 ⟨subd6_9_766, List.forall_mem_cons.2 ⟨subd6_9_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_768 : subd6_9 [4, 4] = true := by decide +kernel
theorem subd6_9_769 : subd6_9 [5, -4] = true := by decide +kernel
theorem subd6_9_770 : subd6_9 [5, -3] = true := by decide +kernel
theorem subd6_9_771 : subd6_9 [5, -2] = true := by decide +kernel
theorem subd6_9_772 : subd6_9 [5, -1] = true := by decide +kernel
theorem subd6_9_773 : subd6_9 [5, 0] = true := by decide +kernel
theorem subd6_9_774 : subd6_9 [5, 1] = true := by decide +kernel
theorem subd6_9_775 : subd6_9 [5, 2] = true := by decide +kernel
theorem subd6_9_776 : subd6_9 [5, 3] = true := by decide +kernel
theorem sbd6_9_24 : ∀ q ∈ blkd6_9_24, subd6_9 q = true := by
  unfold blkd6_9_24
  exact List.forall_mem_cons.2 ⟨subd6_9_768, List.forall_mem_cons.2 ⟨subd6_9_769, List.forall_mem_cons.2 ⟨subd6_9_770, List.forall_mem_cons.2 ⟨subd6_9_771, List.forall_mem_cons.2 ⟨subd6_9_772, List.forall_mem_cons.2 ⟨subd6_9_773, List.forall_mem_cons.2 ⟨subd6_9_774, List.forall_mem_cons.2 ⟨subd6_9_775, List.forall_mem_cons.2 ⟨subd6_9_776, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_10 : ldCheck G d6_10.U d6_10.ms ldd6_10 = true := by decide +kernel
theorem pre_okd6_10 : subPre G cell6 d6_10 = true := by decide +kernel
theorem subd6_10_0 : subd6_10 [-3, -1] = true := by decide +kernel
theorem subd6_10_1 : subd6_10 [-3, 0] = true := by decide +kernel
theorem subd6_10_2 : subd6_10 [-3, 1] = true := by decide +kernel
theorem subd6_10_3 : subd6_10 [-3, 2] = true := by decide +kernel
theorem subd6_10_4 : subd6_10 [-2, -2] = true := by decide +kernel
theorem subd6_10_5 : subd6_10 [-2, -1, -7] = true := by decide +kernel
theorem subd6_10_6 : subd6_10 [-2, -1, -6] = true := by decide +kernel
theorem subd6_10_7 : subd6_10 [-2, -1, -5] = true := by decide +kernel
theorem subd6_10_8 : subd6_10 [-2, -1, -4] = true := by decide +kernel
theorem subd6_10_9 : subd6_10 [-2, -1, -3] = true := by decide +kernel
theorem subd6_10_10 : subd6_10 [-2, -1, -2] = true := by decide +kernel
theorem subd6_10_11 : subd6_10 [-2, -1, -1] = true := by decide +kernel
theorem subd6_10_12 : subd6_10 [-2, -1, 0] = true := by decide +kernel
theorem subd6_10_13 : subd6_10 [-2, -1, 1] = true := by decide +kernel
theorem subd6_10_14 : subd6_10 [-2, -1, 2] = true := by decide +kernel
theorem subd6_10_15 : subd6_10 [-2, -1, 3] = true := by decide +kernel
theorem subd6_10_16 : subd6_10 [-2, -1, 4] = true := by decide +kernel
theorem subd6_10_17 : subd6_10 [-2, -1, 5] = true := by decide +kernel
theorem subd6_10_18 : subd6_10 [-2, -1, 6] = true := by decide +kernel
theorem subd6_10_19 : subd6_10 [-2, 0, -9] = true := by decide +kernel
theorem subd6_10_20 : subd6_10 [-2, 0, -8] = true := by decide +kernel
theorem subd6_10_21 : subd6_10 [-2, 0, -7] = true := by decide +kernel
theorem subd6_10_22 : subd6_10 [-2, 0, -6] = true := by decide +kernel
theorem subd6_10_23 : subd6_10 [-2, 0, -5] = true := by decide +kernel
theorem subd6_10_24 : subd6_10 [-2, 0, -4] = true := by decide +kernel
theorem subd6_10_25 : subd6_10 [-2, 0, -3] = true := by decide +kernel
theorem subd6_10_26 : subd6_10 [-2, 0, -2] = true := by decide +kernel
theorem subd6_10_27 : subd6_10 [-2, 0, -1] = true := by decide +kernel
theorem subd6_10_28 : subd6_10 [-2, 0, 0] = true := by decide +kernel
theorem subd6_10_29 : subd6_10 [-2, 0, 1] = true := by decide +kernel
theorem subd6_10_30 : subd6_10 [-2, 0, 2] = true := by decide +kernel
theorem subd6_10_31 : subd6_10 [-2, 0, 3] = true := by decide +kernel
theorem sbd6_10_0 : ∀ q ∈ blkd6_10_0, subd6_10 q = true := by
  unfold blkd6_10_0
  exact List.forall_mem_cons.2 ⟨subd6_10_0, List.forall_mem_cons.2 ⟨subd6_10_1, List.forall_mem_cons.2 ⟨subd6_10_2, List.forall_mem_cons.2 ⟨subd6_10_3, List.forall_mem_cons.2 ⟨subd6_10_4, List.forall_mem_cons.2 ⟨subd6_10_5, List.forall_mem_cons.2 ⟨subd6_10_6, List.forall_mem_cons.2 ⟨subd6_10_7, List.forall_mem_cons.2 ⟨subd6_10_8, List.forall_mem_cons.2 ⟨subd6_10_9, List.forall_mem_cons.2 ⟨subd6_10_10, List.forall_mem_cons.2 ⟨subd6_10_11, List.forall_mem_cons.2 ⟨subd6_10_12, List.forall_mem_cons.2 ⟨subd6_10_13, List.forall_mem_cons.2 ⟨subd6_10_14, List.forall_mem_cons.2 ⟨subd6_10_15, List.forall_mem_cons.2 ⟨subd6_10_16, List.forall_mem_cons.2 ⟨subd6_10_17, List.forall_mem_cons.2 ⟨subd6_10_18, List.forall_mem_cons.2 ⟨subd6_10_19, List.forall_mem_cons.2 ⟨subd6_10_20, List.forall_mem_cons.2 ⟨subd6_10_21, List.forall_mem_cons.2 ⟨subd6_10_22, List.forall_mem_cons.2 ⟨subd6_10_23, List.forall_mem_cons.2 ⟨subd6_10_24, List.forall_mem_cons.2 ⟨subd6_10_25, List.forall_mem_cons.2 ⟨subd6_10_26, List.forall_mem_cons.2 ⟨subd6_10_27, List.forall_mem_cons.2 ⟨subd6_10_28, List.forall_mem_cons.2 ⟨subd6_10_29, List.forall_mem_cons.2 ⟨subd6_10_30, List.forall_mem_cons.2 ⟨subd6_10_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_10_32 : subd6_10 [-2, 0, 4] = true := by decide +kernel
theorem subd6_10_33 : subd6_10 [-2, 0, 5] = true := by decide +kernel
theorem subd6_10_34 : subd6_10 [-2, 0, 6] = true := by decide +kernel
theorem subd6_10_35 : subd6_10 [-2, 0, 7] = true := by decide +kernel
theorem subd6_10_36 : subd6_10 [-2, 0, 8] = true := by decide +kernel
theorem subd6_10_37 : subd6_10 [-2, 1, -9] = true := by decide +kernel
theorem subd6_10_38 : subd6_10 [-2, 1, -8] = true := by decide +kernel
theorem subd6_10_39 : subd6_10 [-2, 1, -7] = true := by decide +kernel
theorem subd6_10_40 : subd6_10 [-2, 1, -6] = true := by decide +kernel
theorem subd6_10_41 : subd6_10 [-2, 1, -5] = true := by decide +kernel
theorem subd6_10_42 : subd6_10 [-2, 1, -4] = true := by decide +kernel
theorem subd6_10_43 : subd6_10 [-2, 1, -3] = true := by decide +kernel
theorem subd6_10_44 : subd6_10 [-2, 1, -2] = true := by decide +kernel
theorem subd6_10_45 : subd6_10 [-2, 1, -1] = true := by decide +kernel
theorem subd6_10_46 : subd6_10 [-2, 1, 0] = true := by decide +kernel
theorem subd6_10_47 : subd6_10 [-2, 1, 1] = true := by decide +kernel
theorem subd6_10_48 : subd6_10 [-2, 1, 2] = true := by decide +kernel
theorem subd6_10_49 : subd6_10 [-2, 1, 3] = true := by decide +kernel
theorem subd6_10_50 : subd6_10 [-2, 1, 4] = true := by decide +kernel
theorem subd6_10_51 : subd6_10 [-2, 1, 5] = true := by decide +kernel
theorem subd6_10_52 : subd6_10 [-2, 1, 6] = true := by decide +kernel
theorem subd6_10_53 : subd6_10 [-2, 1, 7] = true := by decide +kernel
theorem subd6_10_54 : subd6_10 [-2, 1, 8] = true := by decide +kernel
theorem subd6_10_55 : subd6_10 [-2, 2, -7] = true := by decide +kernel
theorem subd6_10_56 : subd6_10 [-2, 2, -6] = true := by decide +kernel
theorem subd6_10_57 : subd6_10 [-2, 2, -5] = true := by decide +kernel
theorem subd6_10_58 : subd6_10 [-2, 2, -4] = true := by decide +kernel
theorem subd6_10_59 : subd6_10 [-2, 2, -3] = true := by decide +kernel
theorem subd6_10_60 : subd6_10 [-2, 2, -2] = true := by decide +kernel
theorem subd6_10_61 : subd6_10 [-2, 2, -1] = true := by decide +kernel
theorem subd6_10_62 : subd6_10 [-2, 2, 0] = true := by decide +kernel
theorem subd6_10_63 : subd6_10 [-2, 2, 1] = true := by decide +kernel
theorem sbd6_10_1 : ∀ q ∈ blkd6_10_1, subd6_10 q = true := by
  unfold blkd6_10_1
  exact List.forall_mem_cons.2 ⟨subd6_10_32, List.forall_mem_cons.2 ⟨subd6_10_33, List.forall_mem_cons.2 ⟨subd6_10_34, List.forall_mem_cons.2 ⟨subd6_10_35, List.forall_mem_cons.2 ⟨subd6_10_36, List.forall_mem_cons.2 ⟨subd6_10_37, List.forall_mem_cons.2 ⟨subd6_10_38, List.forall_mem_cons.2 ⟨subd6_10_39, List.forall_mem_cons.2 ⟨subd6_10_40, List.forall_mem_cons.2 ⟨subd6_10_41, List.forall_mem_cons.2 ⟨subd6_10_42, List.forall_mem_cons.2 ⟨subd6_10_43, List.forall_mem_cons.2 ⟨subd6_10_44, List.forall_mem_cons.2 ⟨subd6_10_45, List.forall_mem_cons.2 ⟨subd6_10_46, List.forall_mem_cons.2 ⟨subd6_10_47, List.forall_mem_cons.2 ⟨subd6_10_48, List.forall_mem_cons.2 ⟨subd6_10_49, List.forall_mem_cons.2 ⟨subd6_10_50, List.forall_mem_cons.2 ⟨subd6_10_51, List.forall_mem_cons.2 ⟨subd6_10_52, List.forall_mem_cons.2 ⟨subd6_10_53, List.forall_mem_cons.2 ⟨subd6_10_54, List.forall_mem_cons.2 ⟨subd6_10_55, List.forall_mem_cons.2 ⟨subd6_10_56, List.forall_mem_cons.2 ⟨subd6_10_57, List.forall_mem_cons.2 ⟨subd6_10_58, List.forall_mem_cons.2 ⟨subd6_10_59, List.forall_mem_cons.2 ⟨subd6_10_60, List.forall_mem_cons.2 ⟨subd6_10_61, List.forall_mem_cons.2 ⟨subd6_10_62, List.forall_mem_cons.2 ⟨subd6_10_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_10_64 : subd6_10 [-2, 2, 2] = true := by decide +kernel
theorem subd6_10_65 : subd6_10 [-2, 2, 3] = true := by decide +kernel
theorem subd6_10_66 : subd6_10 [-2, 2, 4] = true := by decide +kernel
theorem subd6_10_67 : subd6_10 [-2, 2, 5] = true := by decide +kernel
theorem subd6_10_68 : subd6_10 [-2, 2, 6] = true := by decide +kernel
theorem subd6_10_69 : subd6_10 [-1, -3] = true := by decide +kernel
theorem subd6_10_70 : subd6_10 [-1, -2] = true := by decide +kernel
theorem subd6_10_71 : subd6_10 [-1, -1, -10] = true := by decide +kernel
theorem subd6_10_72 : subd6_10 [-1, -1, -9] = true := by decide +kernel
theorem subd6_10_73 : subd6_10 [-1, -1, -8] = true := by decide +kernel
theorem subd6_10_74 : subd6_10 [-1, -1, -7] = true := by decide +kernel
theorem subd6_10_75 : subd6_10 [-1, -1, -6] = true := by decide +kernel
theorem subd6_10_76 : subd6_10 [-1, -1, -5] = true := by decide +kernel
theorem subd6_10_77 : subd6_10 [-1, -1, -4] = true := by decide +kernel
theorem subd6_10_78 : subd6_10 [-1, -1, -3] = true := by decide +kernel
theorem subd6_10_79 : subd6_10 [-1, -1, -2] = true := by decide +kernel
theorem subd6_10_80 : subd6_10 [-1, -1, -1] = true := by decide +kernel
theorem subd6_10_81 : subd6_10 [-1, -1, 0] = true := by decide +kernel
theorem subd6_10_82 : subd6_10 [-1, -1, 1] = true := by decide +kernel
theorem subd6_10_83 : subd6_10 [-1, -1, 2] = true := by decide +kernel
theorem subd6_10_84 : subd6_10 [-1, -1, 3] = true := by decide +kernel
theorem subd6_10_85 : subd6_10 [-1, -1, 4] = true := by decide +kernel
theorem subd6_10_86 : subd6_10 [-1, -1, 5] = true := by decide +kernel
theorem subd6_10_87 : subd6_10 [-1, -1, 6] = true := by decide +kernel
theorem subd6_10_88 : subd6_10 [-1, -1, 7] = true := by decide +kernel
theorem subd6_10_89 : subd6_10 [-1, -1, 8] = true := by decide +kernel
theorem subd6_10_90 : subd6_10 [-1, -1, 9] = true := by decide +kernel
theorem subd6_10_91 : subd6_10 [-1, 0, -11] = true := by decide +kernel
theorem subd6_10_92 : subd6_10 [-1, 0, -10] = true := by decide +kernel
theorem subd6_10_93 : subd6_10 [-1, 0, -9] = true := by decide +kernel
theorem subd6_10_94 : subd6_10 [-1, 0, -8] = true := by decide +kernel
theorem subd6_10_95 : subd6_10 [-1, 0, -7] = true := by decide +kernel
theorem sbd6_10_2 : ∀ q ∈ blkd6_10_2, subd6_10 q = true := by
  unfold blkd6_10_2
  exact List.forall_mem_cons.2 ⟨subd6_10_64, List.forall_mem_cons.2 ⟨subd6_10_65, List.forall_mem_cons.2 ⟨subd6_10_66, List.forall_mem_cons.2 ⟨subd6_10_67, List.forall_mem_cons.2 ⟨subd6_10_68, List.forall_mem_cons.2 ⟨subd6_10_69, List.forall_mem_cons.2 ⟨subd6_10_70, List.forall_mem_cons.2 ⟨subd6_10_71, List.forall_mem_cons.2 ⟨subd6_10_72, List.forall_mem_cons.2 ⟨subd6_10_73, List.forall_mem_cons.2 ⟨subd6_10_74, List.forall_mem_cons.2 ⟨subd6_10_75, List.forall_mem_cons.2 ⟨subd6_10_76, List.forall_mem_cons.2 ⟨subd6_10_77, List.forall_mem_cons.2 ⟨subd6_10_78, List.forall_mem_cons.2 ⟨subd6_10_79, List.forall_mem_cons.2 ⟨subd6_10_80, List.forall_mem_cons.2 ⟨subd6_10_81, List.forall_mem_cons.2 ⟨subd6_10_82, List.forall_mem_cons.2 ⟨subd6_10_83, List.forall_mem_cons.2 ⟨subd6_10_84, List.forall_mem_cons.2 ⟨subd6_10_85, List.forall_mem_cons.2 ⟨subd6_10_86, List.forall_mem_cons.2 ⟨subd6_10_87, List.forall_mem_cons.2 ⟨subd6_10_88, List.forall_mem_cons.2 ⟨subd6_10_89, List.forall_mem_cons.2 ⟨subd6_10_90, List.forall_mem_cons.2 ⟨subd6_10_91, List.forall_mem_cons.2 ⟨subd6_10_92, List.forall_mem_cons.2 ⟨subd6_10_93, List.forall_mem_cons.2 ⟨subd6_10_94, List.forall_mem_cons.2 ⟨subd6_10_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
