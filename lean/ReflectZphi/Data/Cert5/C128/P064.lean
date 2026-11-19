import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_2_576 : subd9_2 [1, 2, -1] = true := by decide +kernel
theorem subd9_2_577 : subd9_2 [1, 2, 0] = true := by decide +kernel
theorem subd9_2_578 : subd9_2 [1, 2, 1] = true := by decide +kernel
theorem subd9_2_579 : subd9_2 [1, 2, 2] = true := by decide +kernel
theorem subd9_2_580 : subd9_2 [1, 2, 3] = true := by decide +kernel
theorem subd9_2_581 : subd9_2 [1, 2, 4] = true := by decide +kernel
theorem subd9_2_582 : subd9_2 [1, 2, 5] = true := by decide +kernel
theorem subd9_2_583 : subd9_2 [1, 2, 6] = true := by decide +kernel
theorem subd9_2_584 : subd9_2 [1, 2, 7] = true := by decide +kernel
theorem subd9_2_585 : subd9_2 [1, 2, 8] = true := by decide +kernel
theorem subd9_2_586 : subd9_2 [1, 2, 9] = true := by decide +kernel
theorem subd9_2_587 : subd9_2 [1, 2, 10] = true := by decide +kernel
theorem subd9_2_588 : subd9_2 [1, 3, -6] = true := by decide +kernel
theorem subd9_2_589 : subd9_2 [1, 3, -5] = true := by decide +kernel
theorem subd9_2_590 : subd9_2 [1, 3, -4] = true := by decide +kernel
theorem subd9_2_591 : subd9_2 [1, 3, -3] = true := by decide +kernel
theorem subd9_2_592 : subd9_2 [1, 3, -2] = true := by decide +kernel
theorem subd9_2_593 : subd9_2 [1, 3, -1] = true := by decide +kernel
theorem subd9_2_594 : subd9_2 [1, 3, 0] = true := by decide +kernel
theorem subd9_2_595 : subd9_2 [1, 3, 1] = true := by decide +kernel
theorem subd9_2_596 : subd9_2 [1, 3, 2] = true := by decide +kernel
theorem subd9_2_597 : subd9_2 [1, 3, 3] = true := by decide +kernel
theorem subd9_2_598 : subd9_2 [1, 3, 4] = true := by decide +kernel
theorem subd9_2_599 : subd9_2 [1, 3, 5] = true := by decide +kernel
theorem subd9_2_600 : subd9_2 [1, 3, 6] = true := by decide +kernel
theorem subd9_2_601 : subd9_2 [1, 3, 7] = true := by decide +kernel
theorem subd9_2_602 : subd9_2 [1, 3, 8] = true := by decide +kernel
theorem subd9_2_603 : subd9_2 [1, 4] = true := by decide +kernel
theorem subd9_2_604 : subd9_2 [2, -6] = true := by decide +kernel
theorem subd9_2_605 : subd9_2 [2, -5] = true := by decide +kernel
theorem subd9_2_606 : subd9_2 [2, -4] = true := by decide +kernel
theorem subd9_2_607 : subd9_2 [2, -3, -9] = true := by decide +kernel
theorem sbd9_2_18 : ∀ q ∈ blkd9_2_18, subd9_2 q = true := by
  unfold blkd9_2_18
  exact List.forall_mem_cons.2 ⟨subd9_2_576, List.forall_mem_cons.2 ⟨subd9_2_577, List.forall_mem_cons.2 ⟨subd9_2_578, List.forall_mem_cons.2 ⟨subd9_2_579, List.forall_mem_cons.2 ⟨subd9_2_580, List.forall_mem_cons.2 ⟨subd9_2_581, List.forall_mem_cons.2 ⟨subd9_2_582, List.forall_mem_cons.2 ⟨subd9_2_583, List.forall_mem_cons.2 ⟨subd9_2_584, List.forall_mem_cons.2 ⟨subd9_2_585, List.forall_mem_cons.2 ⟨subd9_2_586, List.forall_mem_cons.2 ⟨subd9_2_587, List.forall_mem_cons.2 ⟨subd9_2_588, List.forall_mem_cons.2 ⟨subd9_2_589, List.forall_mem_cons.2 ⟨subd9_2_590, List.forall_mem_cons.2 ⟨subd9_2_591, List.forall_mem_cons.2 ⟨subd9_2_592, List.forall_mem_cons.2 ⟨subd9_2_593, List.forall_mem_cons.2 ⟨subd9_2_594, List.forall_mem_cons.2 ⟨subd9_2_595, List.forall_mem_cons.2 ⟨subd9_2_596, List.forall_mem_cons.2 ⟨subd9_2_597, List.forall_mem_cons.2 ⟨subd9_2_598, List.forall_mem_cons.2 ⟨subd9_2_599, List.forall_mem_cons.2 ⟨subd9_2_600, List.forall_mem_cons.2 ⟨subd9_2_601, List.forall_mem_cons.2 ⟨subd9_2_602, List.forall_mem_cons.2 ⟨subd9_2_603, List.forall_mem_cons.2 ⟨subd9_2_604, List.forall_mem_cons.2 ⟨subd9_2_605, List.forall_mem_cons.2 ⟨subd9_2_606, List.forall_mem_cons.2 ⟨subd9_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_608 : subd9_2 [2, -3, -8] = true := by decide +kernel
theorem subd9_2_609 : subd9_2 [2, -3, -7] = true := by decide +kernel
theorem subd9_2_610 : subd9_2 [2, -3, -6] = true := by decide +kernel
theorem subd9_2_611 : subd9_2 [2, -3, -5] = true := by decide +kernel
theorem subd9_2_612 : subd9_2 [2, -3, -4] = true := by decide +kernel
theorem subd9_2_613 : subd9_2 [2, -3, -3] = true := by decide +kernel
theorem subd9_2_614 : subd9_2 [2, -3, -2] = true := by decide +kernel
theorem subd9_2_615 : subd9_2 [2, -3, -1] = true := by decide +kernel
theorem subd9_2_616 : subd9_2 [2, -3, 0] = true := by decide +kernel
theorem subd9_2_617 : subd9_2 [2, -3, 1] = true := by decide +kernel
theorem subd9_2_618 : subd9_2 [2, -3, 2] = true := by decide +kernel
theorem subd9_2_619 : subd9_2 [2, -3, 3] = true := by decide +kernel
theorem subd9_2_620 : subd9_2 [2, -3, 4] = true := by decide +kernel
theorem subd9_2_621 : subd9_2 [2, -3, 5] = true := by decide +kernel
theorem subd9_2_622 : subd9_2 [2, -3, 6] = true := by decide +kernel
theorem subd9_2_623 : subd9_2 [2, -3, 7] = true := by decide +kernel
theorem subd9_2_624 : subd9_2 [2, -2, -10] = true := by decide +kernel
theorem subd9_2_625 : subd9_2 [2, -2, -9] = true := by decide +kernel
theorem subd9_2_626 : subd9_2 [2, -2, -8] = true := by decide +kernel
theorem subd9_2_627 : subd9_2 [2, -2, -7] = true := by decide +kernel
theorem subd9_2_628 : subd9_2 [2, -2, -6] = true := by decide +kernel
theorem subd9_2_629 : subd9_2 [2, -2, -5] = true := by decide +kernel
theorem subd9_2_630 : subd9_2 [2, -2, -4] = true := by decide +kernel
theorem subd9_2_631 : subd9_2 [2, -2, -3] = true := by decide +kernel
theorem subd9_2_632 : subd9_2 [2, -2, -2] = true := by decide +kernel
theorem subd9_2_633 : subd9_2 [2, -2, -1] = true := by decide +kernel
theorem subd9_2_634 : subd9_2 [2, -2, 0] = true := by decide +kernel
theorem subd9_2_635 : subd9_2 [2, -2, 1] = true := by decide +kernel
theorem subd9_2_636 : subd9_2 [2, -2, 2] = true := by decide +kernel
theorem subd9_2_637 : subd9_2 [2, -2, 3] = true := by decide +kernel
theorem subd9_2_638 : subd9_2 [2, -2, 4] = true := by decide +kernel
theorem subd9_2_639 : subd9_2 [2, -2, 5] = true := by decide +kernel
theorem sbd9_2_19 : ∀ q ∈ blkd9_2_19, subd9_2 q = true := by
  unfold blkd9_2_19
  exact List.forall_mem_cons.2 ⟨subd9_2_608, List.forall_mem_cons.2 ⟨subd9_2_609, List.forall_mem_cons.2 ⟨subd9_2_610, List.forall_mem_cons.2 ⟨subd9_2_611, List.forall_mem_cons.2 ⟨subd9_2_612, List.forall_mem_cons.2 ⟨subd9_2_613, List.forall_mem_cons.2 ⟨subd9_2_614, List.forall_mem_cons.2 ⟨subd9_2_615, List.forall_mem_cons.2 ⟨subd9_2_616, List.forall_mem_cons.2 ⟨subd9_2_617, List.forall_mem_cons.2 ⟨subd9_2_618, List.forall_mem_cons.2 ⟨subd9_2_619, List.forall_mem_cons.2 ⟨subd9_2_620, List.forall_mem_cons.2 ⟨subd9_2_621, List.forall_mem_cons.2 ⟨subd9_2_622, List.forall_mem_cons.2 ⟨subd9_2_623, List.forall_mem_cons.2 ⟨subd9_2_624, List.forall_mem_cons.2 ⟨subd9_2_625, List.forall_mem_cons.2 ⟨subd9_2_626, List.forall_mem_cons.2 ⟨subd9_2_627, List.forall_mem_cons.2 ⟨subd9_2_628, List.forall_mem_cons.2 ⟨subd9_2_629, List.forall_mem_cons.2 ⟨subd9_2_630, List.forall_mem_cons.2 ⟨subd9_2_631, List.forall_mem_cons.2 ⟨subd9_2_632, List.forall_mem_cons.2 ⟨subd9_2_633, List.forall_mem_cons.2 ⟨subd9_2_634, List.forall_mem_cons.2 ⟨subd9_2_635, List.forall_mem_cons.2 ⟨subd9_2_636, List.forall_mem_cons.2 ⟨subd9_2_637, List.forall_mem_cons.2 ⟨subd9_2_638, List.forall_mem_cons.2 ⟨subd9_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_640 : subd9_2 [2, -2, 6] = true := by decide +kernel
theorem subd9_2_641 : subd9_2 [2, -2, 7] = true := by decide +kernel
theorem subd9_2_642 : subd9_2 [2, -2, 8] = true := by decide +kernel
theorem subd9_2_643 : subd9_2 [2, -2, 9] = true := by decide +kernel
theorem subd9_2_644 : subd9_2 [2, -1, -10] = true := by decide +kernel
theorem subd9_2_645 : subd9_2 [2, -1, -9] = true := by decide +kernel
theorem subd9_2_646 : subd9_2 [2, -1, -8] = true := by decide +kernel
theorem subd9_2_647 : subd9_2 [2, -1, -7] = true := by decide +kernel
theorem subd9_2_648 : subd9_2 [2, -1, -6] = true := by decide +kernel
theorem subd9_2_649 : subd9_2 [2, -1, -5] = true := by decide +kernel
theorem subd9_2_650 : subd9_2 [2, -1, -4] = true := by decide +kernel
theorem subd9_2_651 : subd9_2 [2, -1, -3] = true := by decide +kernel
theorem subd9_2_652 : subd9_2 [2, -1, -2] = true := by decide +kernel
theorem subd9_2_653 : subd9_2 [2, -1, -1] = true := by decide +kernel
theorem subd9_2_654 : subd9_2 [2, -1, 0] = true := by decide +kernel
theorem subd9_2_655 : subd9_2 [2, -1, 1] = true := by decide +kernel
theorem subd9_2_656 : subd9_2 [2, -1, 2] = true := by decide +kernel
theorem subd9_2_657 : subd9_2 [2, -1, 3] = true := by decide +kernel
theorem subd9_2_658 : subd9_2 [2, -1, 4] = true := by decide +kernel
theorem subd9_2_659 : subd9_2 [2, -1, 5] = true := by decide +kernel
theorem subd9_2_660 : subd9_2 [2, -1, 6] = true := by decide +kernel
theorem subd9_2_661 : subd9_2 [2, -1, 7] = true := by decide +kernel
theorem subd9_2_662 : subd9_2 [2, -1, 8] = true := by decide +kernel
theorem subd9_2_663 : subd9_2 [2, -1, 9] = true := by decide +kernel
theorem subd9_2_664 : subd9_2 [2, 0, -9] = true := by decide +kernel
theorem subd9_2_665 : subd9_2 [2, 0, -8] = true := by decide +kernel
theorem subd9_2_666 : subd9_2 [2, 0, -7] = true := by decide +kernel
theorem subd9_2_667 : subd9_2 [2, 0, -6] = true := by decide +kernel
theorem subd9_2_668 : subd9_2 [2, 0, -5] = true := by decide +kernel
theorem subd9_2_669 : subd9_2 [2, 0, -4] = true := by decide +kernel
theorem subd9_2_670 : subd9_2 [2, 0, -3] = true := by decide +kernel
theorem subd9_2_671 : subd9_2 [2, 0, -2] = true := by decide +kernel
theorem sbd9_2_20 : ∀ q ∈ blkd9_2_20, subd9_2 q = true := by
  unfold blkd9_2_20
  exact List.forall_mem_cons.2 ⟨subd9_2_640, List.forall_mem_cons.2 ⟨subd9_2_641, List.forall_mem_cons.2 ⟨subd9_2_642, List.forall_mem_cons.2 ⟨subd9_2_643, List.forall_mem_cons.2 ⟨subd9_2_644, List.forall_mem_cons.2 ⟨subd9_2_645, List.forall_mem_cons.2 ⟨subd9_2_646, List.forall_mem_cons.2 ⟨subd9_2_647, List.forall_mem_cons.2 ⟨subd9_2_648, List.forall_mem_cons.2 ⟨subd9_2_649, List.forall_mem_cons.2 ⟨subd9_2_650, List.forall_mem_cons.2 ⟨subd9_2_651, List.forall_mem_cons.2 ⟨subd9_2_652, List.forall_mem_cons.2 ⟨subd9_2_653, List.forall_mem_cons.2 ⟨subd9_2_654, List.forall_mem_cons.2 ⟨subd9_2_655, List.forall_mem_cons.2 ⟨subd9_2_656, List.forall_mem_cons.2 ⟨subd9_2_657, List.forall_mem_cons.2 ⟨subd9_2_658, List.forall_mem_cons.2 ⟨subd9_2_659, List.forall_mem_cons.2 ⟨subd9_2_660, List.forall_mem_cons.2 ⟨subd9_2_661, List.forall_mem_cons.2 ⟨subd9_2_662, List.forall_mem_cons.2 ⟨subd9_2_663, List.forall_mem_cons.2 ⟨subd9_2_664, List.forall_mem_cons.2 ⟨subd9_2_665, List.forall_mem_cons.2 ⟨subd9_2_666, List.forall_mem_cons.2 ⟨subd9_2_667, List.forall_mem_cons.2 ⟨subd9_2_668, List.forall_mem_cons.2 ⟨subd9_2_669, List.forall_mem_cons.2 ⟨subd9_2_670, List.forall_mem_cons.2 ⟨subd9_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_672 : subd9_2 [2, 0, -1] = true := by decide +kernel
theorem subd9_2_673 : subd9_2 [2, 0, 0] = true := by decide +kernel
theorem subd9_2_674 : subd9_2 [2, 0, 1] = true := by decide +kernel
theorem subd9_2_675 : subd9_2 [2, 0, 2] = true := by decide +kernel
theorem subd9_2_676 : subd9_2 [2, 0, 3] = true := by decide +kernel
theorem subd9_2_677 : subd9_2 [2, 0, 4] = true := by decide +kernel
theorem subd9_2_678 : subd9_2 [2, 0, 5] = true := by decide +kernel
theorem subd9_2_679 : subd9_2 [2, 0, 6] = true := by decide +kernel
theorem subd9_2_680 : subd9_2 [2, 0, 7] = true := by decide +kernel
theorem subd9_2_681 : subd9_2 [2, 0, 8] = true := by decide +kernel
theorem subd9_2_682 : subd9_2 [2, 0, 9] = true := by decide +kernel
theorem subd9_2_683 : subd9_2 [2, 0, 10] = true := by decide +kernel
theorem subd9_2_684 : subd9_2 [2, 1, -8] = true := by decide +kernel
theorem subd9_2_685 : subd9_2 [2, 1, -7] = true := by decide +kernel
theorem subd9_2_686 : subd9_2 [2, 1, -6] = true := by decide +kernel
theorem subd9_2_687 : subd9_2 [2, 1, -5] = true := by decide +kernel
theorem subd9_2_688 : subd9_2 [2, 1, -4] = true := by decide +kernel
theorem subd9_2_689 : subd9_2 [2, 1, -3] = true := by decide +kernel
theorem subd9_2_690 : subd9_2 [2, 1, -2] = true := by decide +kernel
theorem subd9_2_691 : subd9_2 [2, 1, -1] = true := by decide +kernel
theorem subd9_2_692 : subd9_2 [2, 1, 0] = true := by decide +kernel
theorem subd9_2_693 : subd9_2 [2, 1, 1] = true := by decide +kernel
theorem subd9_2_694 : subd9_2 [2, 1, 2] = true := by decide +kernel
theorem subd9_2_695 : subd9_2 [2, 1, 3] = true := by decide +kernel
theorem subd9_2_696 : subd9_2 [2, 1, 4] = true := by decide +kernel
theorem subd9_2_697 : subd9_2 [2, 1, 5] = true := by decide +kernel
theorem subd9_2_698 : subd9_2 [2, 1, 6] = true := by decide +kernel
theorem subd9_2_699 : subd9_2 [2, 1, 7] = true := by decide +kernel
theorem subd9_2_700 : subd9_2 [2, 1, 8] = true := by decide +kernel
theorem subd9_2_701 : subd9_2 [2, 1, 9] = true := by decide +kernel
theorem subd9_2_702 : subd9_2 [2, 2, -6] = true := by decide +kernel
theorem subd9_2_703 : subd9_2 [2, 2, -5] = true := by decide +kernel
theorem sbd9_2_21 : ∀ q ∈ blkd9_2_21, subd9_2 q = true := by
  unfold blkd9_2_21
  exact List.forall_mem_cons.2 ⟨subd9_2_672, List.forall_mem_cons.2 ⟨subd9_2_673, List.forall_mem_cons.2 ⟨subd9_2_674, List.forall_mem_cons.2 ⟨subd9_2_675, List.forall_mem_cons.2 ⟨subd9_2_676, List.forall_mem_cons.2 ⟨subd9_2_677, List.forall_mem_cons.2 ⟨subd9_2_678, List.forall_mem_cons.2 ⟨subd9_2_679, List.forall_mem_cons.2 ⟨subd9_2_680, List.forall_mem_cons.2 ⟨subd9_2_681, List.forall_mem_cons.2 ⟨subd9_2_682, List.forall_mem_cons.2 ⟨subd9_2_683, List.forall_mem_cons.2 ⟨subd9_2_684, List.forall_mem_cons.2 ⟨subd9_2_685, List.forall_mem_cons.2 ⟨subd9_2_686, List.forall_mem_cons.2 ⟨subd9_2_687, List.forall_mem_cons.2 ⟨subd9_2_688, List.forall_mem_cons.2 ⟨subd9_2_689, List.forall_mem_cons.2 ⟨subd9_2_690, List.forall_mem_cons.2 ⟨subd9_2_691, List.forall_mem_cons.2 ⟨subd9_2_692, List.forall_mem_cons.2 ⟨subd9_2_693, List.forall_mem_cons.2 ⟨subd9_2_694, List.forall_mem_cons.2 ⟨subd9_2_695, List.forall_mem_cons.2 ⟨subd9_2_696, List.forall_mem_cons.2 ⟨subd9_2_697, List.forall_mem_cons.2 ⟨subd9_2_698, List.forall_mem_cons.2 ⟨subd9_2_699, List.forall_mem_cons.2 ⟨subd9_2_700, List.forall_mem_cons.2 ⟨subd9_2_701, List.forall_mem_cons.2 ⟨subd9_2_702, List.forall_mem_cons.2 ⟨subd9_2_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_704 : subd9_2 [2, 2, -4] = true := by decide +kernel
theorem subd9_2_705 : subd9_2 [2, 2, -3] = true := by decide +kernel
theorem subd9_2_706 : subd9_2 [2, 2, -2] = true := by decide +kernel
theorem subd9_2_707 : subd9_2 [2, 2, -1] = true := by decide +kernel
theorem subd9_2_708 : subd9_2 [2, 2, 0] = true := by decide +kernel
theorem subd9_2_709 : subd9_2 [2, 2, 1] = true := by decide +kernel
theorem subd9_2_710 : subd9_2 [2, 2, 2] = true := by decide +kernel
theorem subd9_2_711 : subd9_2 [2, 2, 3] = true := by decide +kernel
theorem subd9_2_712 : subd9_2 [2, 2, 4] = true := by decide +kernel
theorem subd9_2_713 : subd9_2 [2, 2, 5] = true := by decide +kernel
theorem subd9_2_714 : subd9_2 [2, 2, 6] = true := by decide +kernel
theorem subd9_2_715 : subd9_2 [2, 2, 7] = true := by decide +kernel
theorem subd9_2_716 : subd9_2 [2, 2, 8] = true := by decide +kernel
theorem subd9_2_717 : subd9_2 [2, 3] = true := by decide +kernel
theorem subd9_2_718 : subd9_2 [3, -5] = true := by decide +kernel
theorem subd9_2_719 : subd9_2 [3, -4] = true := by decide +kernel
theorem subd9_2_720 : subd9_2 [3, -3] = true := by decide +kernel
theorem subd9_2_721 : subd9_2 [3, -2, -8] = true := by decide +kernel
theorem subd9_2_722 : subd9_2 [3, -2, -7] = true := by decide +kernel
theorem subd9_2_723 : subd9_2 [3, -2, -6] = true := by decide +kernel
theorem subd9_2_724 : subd9_2 [3, -2, -5] = true := by decide +kernel
theorem subd9_2_725 : subd9_2 [3, -2, -4] = true := by decide +kernel
theorem subd9_2_726 : subd9_2 [3, -2, -3] = true := by decide +kernel
theorem subd9_2_727 : subd9_2 [3, -2, -2] = true := by decide +kernel
theorem subd9_2_728 : subd9_2 [3, -2, -1] = true := by decide +kernel
theorem subd9_2_729 : subd9_2 [3, -2, 0] = true := by decide +kernel
theorem subd9_2_730 : subd9_2 [3, -2, 1] = true := by decide +kernel
theorem subd9_2_731 : subd9_2 [3, -2, 2] = true := by decide +kernel
theorem subd9_2_732 : subd9_2 [3, -2, 3] = true := by decide +kernel
theorem subd9_2_733 : subd9_2 [3, -2, 4] = true := by decide +kernel
theorem subd9_2_734 : subd9_2 [3, -2, 5] = true := by decide +kernel
theorem subd9_2_735 : subd9_2 [3, -2, 6] = true := by decide +kernel
theorem sbd9_2_22 : ∀ q ∈ blkd9_2_22, subd9_2 q = true := by
  unfold blkd9_2_22
  exact List.forall_mem_cons.2 ⟨subd9_2_704, List.forall_mem_cons.2 ⟨subd9_2_705, List.forall_mem_cons.2 ⟨subd9_2_706, List.forall_mem_cons.2 ⟨subd9_2_707, List.forall_mem_cons.2 ⟨subd9_2_708, List.forall_mem_cons.2 ⟨subd9_2_709, List.forall_mem_cons.2 ⟨subd9_2_710, List.forall_mem_cons.2 ⟨subd9_2_711, List.forall_mem_cons.2 ⟨subd9_2_712, List.forall_mem_cons.2 ⟨subd9_2_713, List.forall_mem_cons.2 ⟨subd9_2_714, List.forall_mem_cons.2 ⟨subd9_2_715, List.forall_mem_cons.2 ⟨subd9_2_716, List.forall_mem_cons.2 ⟨subd9_2_717, List.forall_mem_cons.2 ⟨subd9_2_718, List.forall_mem_cons.2 ⟨subd9_2_719, List.forall_mem_cons.2 ⟨subd9_2_720, List.forall_mem_cons.2 ⟨subd9_2_721, List.forall_mem_cons.2 ⟨subd9_2_722, List.forall_mem_cons.2 ⟨subd9_2_723, List.forall_mem_cons.2 ⟨subd9_2_724, List.forall_mem_cons.2 ⟨subd9_2_725, List.forall_mem_cons.2 ⟨subd9_2_726, List.forall_mem_cons.2 ⟨subd9_2_727, List.forall_mem_cons.2 ⟨subd9_2_728, List.forall_mem_cons.2 ⟨subd9_2_729, List.forall_mem_cons.2 ⟨subd9_2_730, List.forall_mem_cons.2 ⟨subd9_2_731, List.forall_mem_cons.2 ⟨subd9_2_732, List.forall_mem_cons.2 ⟨subd9_2_733, List.forall_mem_cons.2 ⟨subd9_2_734, List.forall_mem_cons.2 ⟨subd9_2_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_736 : subd9_2 [3, -2, 7] = true := by decide +kernel
theorem subd9_2_737 : subd9_2 [3, -1, -8] = true := by decide +kernel
theorem subd9_2_738 : subd9_2 [3, -1, -7] = true := by decide +kernel
theorem subd9_2_739 : subd9_2 [3, -1, -6] = true := by decide +kernel
theorem subd9_2_740 : subd9_2 [3, -1, -5] = true := by decide +kernel
theorem subd9_2_741 : subd9_2 [3, -1, -4] = true := by decide +kernel
theorem subd9_2_742 : subd9_2 [3, -1, -3] = true := by decide +kernel
theorem subd9_2_743 : subd9_2 [3, -1, -2] = true := by decide +kernel
theorem subd9_2_744 : subd9_2 [3, -1, -1] = true := by decide +kernel
theorem subd9_2_745 : subd9_2 [3, -1, 0] = true := by decide +kernel
theorem subd9_2_746 : subd9_2 [3, -1, 1] = true := by decide +kernel
theorem subd9_2_747 : subd9_2 [3, -1, 2] = true := by decide +kernel
theorem subd9_2_748 : subd9_2 [3, -1, 3] = true := by decide +kernel
theorem subd9_2_749 : subd9_2 [3, -1, 4] = true := by decide +kernel
theorem subd9_2_750 : subd9_2 [3, -1, 5] = true := by decide +kernel
theorem subd9_2_751 : subd9_2 [3, -1, 6] = true := by decide +kernel
theorem subd9_2_752 : subd9_2 [3, -1, 7] = true := by decide +kernel
theorem subd9_2_753 : subd9_2 [3, -1, 8] = true := by decide +kernel
theorem subd9_2_754 : subd9_2 [3, 0, -7] = true := by decide +kernel
theorem subd9_2_755 : subd9_2 [3, 0, -6] = true := by decide +kernel
theorem subd9_2_756 : subd9_2 [3, 0, -5] = true := by decide +kernel
theorem subd9_2_757 : subd9_2 [3, 0, -4] = true := by decide +kernel
theorem subd9_2_758 : subd9_2 [3, 0, -3] = true := by decide +kernel
theorem subd9_2_759 : subd9_2 [3, 0, -2] = true := by decide +kernel
theorem subd9_2_760 : subd9_2 [3, 0, -1] = true := by decide +kernel
theorem subd9_2_761 : subd9_2 [3, 0, 0] = true := by decide +kernel
theorem subd9_2_762 : subd9_2 [3, 0, 1] = true := by decide +kernel
theorem subd9_2_763 : subd9_2 [3, 0, 2] = true := by decide +kernel
theorem subd9_2_764 : subd9_2 [3, 0, 3] = true := by decide +kernel
theorem subd9_2_765 : subd9_2 [3, 0, 4] = true := by decide +kernel
theorem subd9_2_766 : subd9_2 [3, 0, 5] = true := by decide +kernel
theorem subd9_2_767 : subd9_2 [3, 0, 6] = true := by decide +kernel
theorem sbd9_2_23 : ∀ q ∈ blkd9_2_23, subd9_2 q = true := by
  unfold blkd9_2_23
  exact List.forall_mem_cons.2 ⟨subd9_2_736, List.forall_mem_cons.2 ⟨subd9_2_737, List.forall_mem_cons.2 ⟨subd9_2_738, List.forall_mem_cons.2 ⟨subd9_2_739, List.forall_mem_cons.2 ⟨subd9_2_740, List.forall_mem_cons.2 ⟨subd9_2_741, List.forall_mem_cons.2 ⟨subd9_2_742, List.forall_mem_cons.2 ⟨subd9_2_743, List.forall_mem_cons.2 ⟨subd9_2_744, List.forall_mem_cons.2 ⟨subd9_2_745, List.forall_mem_cons.2 ⟨subd9_2_746, List.forall_mem_cons.2 ⟨subd9_2_747, List.forall_mem_cons.2 ⟨subd9_2_748, List.forall_mem_cons.2 ⟨subd9_2_749, List.forall_mem_cons.2 ⟨subd9_2_750, List.forall_mem_cons.2 ⟨subd9_2_751, List.forall_mem_cons.2 ⟨subd9_2_752, List.forall_mem_cons.2 ⟨subd9_2_753, List.forall_mem_cons.2 ⟨subd9_2_754, List.forall_mem_cons.2 ⟨subd9_2_755, List.forall_mem_cons.2 ⟨subd9_2_756, List.forall_mem_cons.2 ⟨subd9_2_757, List.forall_mem_cons.2 ⟨subd9_2_758, List.forall_mem_cons.2 ⟨subd9_2_759, List.forall_mem_cons.2 ⟨subd9_2_760, List.forall_mem_cons.2 ⟨subd9_2_761, List.forall_mem_cons.2 ⟨subd9_2_762, List.forall_mem_cons.2 ⟨subd9_2_763, List.forall_mem_cons.2 ⟨subd9_2_764, List.forall_mem_cons.2 ⟨subd9_2_765, List.forall_mem_cons.2 ⟨subd9_2_766, List.forall_mem_cons.2 ⟨subd9_2_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_768 : subd9_2 [3, 0, 7] = true := by decide +kernel
theorem subd9_2_769 : subd9_2 [3, 0, 8] = true := by decide +kernel
theorem subd9_2_770 : subd9_2 [3, 1] = true := by decide +kernel
theorem subd9_2_771 : subd9_2 [3, 2] = true := by decide +kernel
theorem subd9_2_772 : subd9_2 [4] = true := by decide +kernel
theorem sbd9_2_24 : ∀ q ∈ blkd9_2_24, subd9_2 q = true := by
  unfold blkd9_2_24
  exact List.forall_mem_cons.2 ⟨subd9_2_768, List.forall_mem_cons.2 ⟨subd9_2_769, List.forall_mem_cons.2 ⟨subd9_2_770, List.forall_mem_cons.2 ⟨subd9_2_771, List.forall_mem_cons.2 ⟨subd9_2_772, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [-6] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-5, -6] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [-5, -5] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [-5, -4] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [-5, -3] = true := by decide +kernel
theorem subd9_3_5 : subd9_3 [-5, -2] = true := by decide +kernel
theorem subd9_3_6 : subd9_3 [-5, -1] = true := by decide +kernel
theorem subd9_3_7 : subd9_3 [-5, 0] = true := by decide +kernel
theorem subd9_3_8 : subd9_3 [-5, 1] = true := by decide +kernel
theorem subd9_3_9 : subd9_3 [-5, 2] = true := by decide +kernel
theorem subd9_3_10 : subd9_3 [-4, -7] = true := by decide +kernel
theorem subd9_3_11 : subd9_3 [-4, -6] = true := by decide +kernel
theorem subd9_3_12 : subd9_3 [-4, -5] = true := by decide +kernel
theorem subd9_3_13 : subd9_3 [-4, -4] = true := by decide +kernel
theorem subd9_3_14 : subd9_3 [-4, -3] = true := by decide +kernel
theorem subd9_3_15 : subd9_3 [-4, -2] = true := by decide +kernel
theorem subd9_3_16 : subd9_3 [-4, -1] = true := by decide +kernel
theorem subd9_3_17 : subd9_3 [-4, 0] = true := by decide +kernel
theorem subd9_3_18 : subd9_3 [-4, 1] = true := by decide +kernel
theorem subd9_3_19 : subd9_3 [-4, 2] = true := by decide +kernel
theorem subd9_3_20 : subd9_3 [-4, 3] = true := by decide +kernel
theorem subd9_3_21 : subd9_3 [-4, 4] = true := by decide +kernel
theorem subd9_3_22 : subd9_3 [-3, -8] = true := by decide +kernel
theorem subd9_3_23 : subd9_3 [-3, -7] = true := by decide +kernel
theorem subd9_3_24 : subd9_3 [-3, -6] = true := by decide +kernel
theorem subd9_3_25 : subd9_3 [-3, -5] = true := by decide +kernel
theorem subd9_3_26 : subd9_3 [-3, -4] = true := by decide +kernel
theorem subd9_3_27 : subd9_3 [-3, -3] = true := by decide +kernel
theorem subd9_3_28 : subd9_3 [-3, -2] = true := by decide +kernel
theorem subd9_3_29 : subd9_3 [-3, -1] = true := by decide +kernel
theorem subd9_3_30 : subd9_3 [-3, 0] = true := by decide +kernel
theorem subd9_3_31 : subd9_3 [-3, 1] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_cons.2 ⟨subd9_3_5, List.forall_mem_cons.2 ⟨subd9_3_6, List.forall_mem_cons.2 ⟨subd9_3_7, List.forall_mem_cons.2 ⟨subd9_3_8, List.forall_mem_cons.2 ⟨subd9_3_9, List.forall_mem_cons.2 ⟨subd9_3_10, List.forall_mem_cons.2 ⟨subd9_3_11, List.forall_mem_cons.2 ⟨subd9_3_12, List.forall_mem_cons.2 ⟨subd9_3_13, List.forall_mem_cons.2 ⟨subd9_3_14, List.forall_mem_cons.2 ⟨subd9_3_15, List.forall_mem_cons.2 ⟨subd9_3_16, List.forall_mem_cons.2 ⟨subd9_3_17, List.forall_mem_cons.2 ⟨subd9_3_18, List.forall_mem_cons.2 ⟨subd9_3_19, List.forall_mem_cons.2 ⟨subd9_3_20, List.forall_mem_cons.2 ⟨subd9_3_21, List.forall_mem_cons.2 ⟨subd9_3_22, List.forall_mem_cons.2 ⟨subd9_3_23, List.forall_mem_cons.2 ⟨subd9_3_24, List.forall_mem_cons.2 ⟨subd9_3_25, List.forall_mem_cons.2 ⟨subd9_3_26, List.forall_mem_cons.2 ⟨subd9_3_27, List.forall_mem_cons.2 ⟨subd9_3_28, List.forall_mem_cons.2 ⟨subd9_3_29, List.forall_mem_cons.2 ⟨subd9_3_30, List.forall_mem_cons.2 ⟨subd9_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
