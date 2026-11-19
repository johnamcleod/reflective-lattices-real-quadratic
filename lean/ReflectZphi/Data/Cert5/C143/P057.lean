import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd18_1_576 : subd18_1 [1, 1, 0] = true := by decide +kernel
theorem subd18_1_577 : subd18_1 [1, 1, 1] = true := by decide +kernel
theorem subd18_1_578 : subd18_1 [1, 1, 2] = true := by decide +kernel
theorem subd18_1_579 : subd18_1 [1, 1, 3] = true := by decide +kernel
theorem subd18_1_580 : subd18_1 [1, 1, 4] = true := by decide +kernel
theorem subd18_1_581 : subd18_1 [1, 1, 5] = true := by decide +kernel
theorem subd18_1_582 : subd18_1 [1, 1, 6] = true := by decide +kernel
theorem subd18_1_583 : subd18_1 [1, 1, 7] = true := by decide +kernel
theorem subd18_1_584 : subd18_1 [1, 2, -9] = true := by decide +kernel
theorem subd18_1_585 : subd18_1 [1, 2, -8] = true := by decide +kernel
theorem subd18_1_586 : subd18_1 [1, 2, -7] = true := by decide +kernel
theorem subd18_1_587 : subd18_1 [1, 2, -6] = true := by decide +kernel
theorem subd18_1_588 : subd18_1 [1, 2, -5] = true := by decide +kernel
theorem subd18_1_589 : subd18_1 [1, 2, -4] = true := by decide +kernel
theorem subd18_1_590 : subd18_1 [1, 2, -3] = true := by decide +kernel
theorem subd18_1_591 : subd18_1 [1, 2, -2] = true := by decide +kernel
theorem subd18_1_592 : subd18_1 [1, 2, -1] = true := by decide +kernel
theorem subd18_1_593 : subd18_1 [1, 2, 0] = true := by decide +kernel
theorem subd18_1_594 : subd18_1 [1, 2, 1] = true := by decide +kernel
theorem subd18_1_595 : subd18_1 [1, 2, 2] = true := by decide +kernel
theorem subd18_1_596 : subd18_1 [1, 2, 3] = true := by decide +kernel
theorem subd18_1_597 : subd18_1 [1, 2, 4] = true := by decide +kernel
theorem subd18_1_598 : subd18_1 [1, 2, 5] = true := by decide +kernel
theorem subd18_1_599 : subd18_1 [1, 2, 6] = true := by decide +kernel
theorem subd18_1_600 : subd18_1 [1, 2, 7] = true := by decide +kernel
theorem subd18_1_601 : subd18_1 [1, 3, -9] = true := by decide +kernel
theorem subd18_1_602 : subd18_1 [1, 3, -8] = true := by decide +kernel
theorem subd18_1_603 : subd18_1 [1, 3, -7] = true := by decide +kernel
theorem subd18_1_604 : subd18_1 [1, 3, -6] = true := by decide +kernel
theorem subd18_1_605 : subd18_1 [1, 3, -5] = true := by decide +kernel
theorem subd18_1_606 : subd18_1 [1, 3, -4] = true := by decide +kernel
theorem subd18_1_607 : subd18_1 [1, 3, -3] = true := by decide +kernel
theorem sbd18_1_18 : ∀ q ∈ blkd18_1_18, subd18_1 q = true := by
  unfold blkd18_1_18
  exact List.forall_mem_cons.2 ⟨subd18_1_576, List.forall_mem_cons.2 ⟨subd18_1_577, List.forall_mem_cons.2 ⟨subd18_1_578, List.forall_mem_cons.2 ⟨subd18_1_579, List.forall_mem_cons.2 ⟨subd18_1_580, List.forall_mem_cons.2 ⟨subd18_1_581, List.forall_mem_cons.2 ⟨subd18_1_582, List.forall_mem_cons.2 ⟨subd18_1_583, List.forall_mem_cons.2 ⟨subd18_1_584, List.forall_mem_cons.2 ⟨subd18_1_585, List.forall_mem_cons.2 ⟨subd18_1_586, List.forall_mem_cons.2 ⟨subd18_1_587, List.forall_mem_cons.2 ⟨subd18_1_588, List.forall_mem_cons.2 ⟨subd18_1_589, List.forall_mem_cons.2 ⟨subd18_1_590, List.forall_mem_cons.2 ⟨subd18_1_591, List.forall_mem_cons.2 ⟨subd18_1_592, List.forall_mem_cons.2 ⟨subd18_1_593, List.forall_mem_cons.2 ⟨subd18_1_594, List.forall_mem_cons.2 ⟨subd18_1_595, List.forall_mem_cons.2 ⟨subd18_1_596, List.forall_mem_cons.2 ⟨subd18_1_597, List.forall_mem_cons.2 ⟨subd18_1_598, List.forall_mem_cons.2 ⟨subd18_1_599, List.forall_mem_cons.2 ⟨subd18_1_600, List.forall_mem_cons.2 ⟨subd18_1_601, List.forall_mem_cons.2 ⟨subd18_1_602, List.forall_mem_cons.2 ⟨subd18_1_603, List.forall_mem_cons.2 ⟨subd18_1_604, List.forall_mem_cons.2 ⟨subd18_1_605, List.forall_mem_cons.2 ⟨subd18_1_606, List.forall_mem_cons.2 ⟨subd18_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_608 : subd18_1 [1, 3, -2] = true := by decide +kernel
theorem subd18_1_609 : subd18_1 [1, 3, -1] = true := by decide +kernel
theorem subd18_1_610 : subd18_1 [1, 3, 0] = true := by decide +kernel
theorem subd18_1_611 : subd18_1 [1, 3, 1] = true := by decide +kernel
theorem subd18_1_612 : subd18_1 [1, 3, 2] = true := by decide +kernel
theorem subd18_1_613 : subd18_1 [1, 3, 3] = true := by decide +kernel
theorem subd18_1_614 : subd18_1 [1, 3, 4] = true := by decide +kernel
theorem subd18_1_615 : subd18_1 [1, 3, 5] = true := by decide +kernel
theorem subd18_1_616 : subd18_1 [1, 3, 6] = true := by decide +kernel
theorem subd18_1_617 : subd18_1 [1, 4, -9] = true := by decide +kernel
theorem subd18_1_618 : subd18_1 [1, 4, -8] = true := by decide +kernel
theorem subd18_1_619 : subd18_1 [1, 4, -7] = true := by decide +kernel
theorem subd18_1_620 : subd18_1 [1, 4, -6] = true := by decide +kernel
theorem subd18_1_621 : subd18_1 [1, 4, -5] = true := by decide +kernel
theorem subd18_1_622 : subd18_1 [1, 4, -4] = true := by decide +kernel
theorem subd18_1_623 : subd18_1 [1, 4, -3] = true := by decide +kernel
theorem subd18_1_624 : subd18_1 [1, 4, -2] = true := by decide +kernel
theorem subd18_1_625 : subd18_1 [1, 4, -1] = true := by decide +kernel
theorem subd18_1_626 : subd18_1 [1, 4, 0] = true := by decide +kernel
theorem subd18_1_627 : subd18_1 [1, 4, 1] = true := by decide +kernel
theorem subd18_1_628 : subd18_1 [1, 4, 2] = true := by decide +kernel
theorem subd18_1_629 : subd18_1 [1, 4, 3] = true := by decide +kernel
theorem subd18_1_630 : subd18_1 [1, 4, 4] = true := by decide +kernel
theorem subd18_1_631 : subd18_1 [1, 4, 5] = true := by decide +kernel
theorem subd18_1_632 : subd18_1 [1, 5] = true := by decide +kernel
theorem subd18_1_633 : subd18_1 [1, 6] = true := by decide +kernel
theorem subd18_1_634 : subd18_1 [1, 7] = true := by decide +kernel
theorem subd18_1_635 : subd18_1 [2, -7] = true := by decide +kernel
theorem subd18_1_636 : subd18_1 [2, -6] = true := by decide +kernel
theorem subd18_1_637 : subd18_1 [2, -5] = true := by decide +kernel
theorem subd18_1_638 : subd18_1 [2, -4] = true := by decide +kernel
theorem subd18_1_639 : subd18_1 [2, -3] = true := by decide +kernel
theorem sbd18_1_19 : ∀ q ∈ blkd18_1_19, subd18_1 q = true := by
  unfold blkd18_1_19
  exact List.forall_mem_cons.2 ⟨subd18_1_608, List.forall_mem_cons.2 ⟨subd18_1_609, List.forall_mem_cons.2 ⟨subd18_1_610, List.forall_mem_cons.2 ⟨subd18_1_611, List.forall_mem_cons.2 ⟨subd18_1_612, List.forall_mem_cons.2 ⟨subd18_1_613, List.forall_mem_cons.2 ⟨subd18_1_614, List.forall_mem_cons.2 ⟨subd18_1_615, List.forall_mem_cons.2 ⟨subd18_1_616, List.forall_mem_cons.2 ⟨subd18_1_617, List.forall_mem_cons.2 ⟨subd18_1_618, List.forall_mem_cons.2 ⟨subd18_1_619, List.forall_mem_cons.2 ⟨subd18_1_620, List.forall_mem_cons.2 ⟨subd18_1_621, List.forall_mem_cons.2 ⟨subd18_1_622, List.forall_mem_cons.2 ⟨subd18_1_623, List.forall_mem_cons.2 ⟨subd18_1_624, List.forall_mem_cons.2 ⟨subd18_1_625, List.forall_mem_cons.2 ⟨subd18_1_626, List.forall_mem_cons.2 ⟨subd18_1_627, List.forall_mem_cons.2 ⟨subd18_1_628, List.forall_mem_cons.2 ⟨subd18_1_629, List.forall_mem_cons.2 ⟨subd18_1_630, List.forall_mem_cons.2 ⟨subd18_1_631, List.forall_mem_cons.2 ⟨subd18_1_632, List.forall_mem_cons.2 ⟨subd18_1_633, List.forall_mem_cons.2 ⟨subd18_1_634, List.forall_mem_cons.2 ⟨subd18_1_635, List.forall_mem_cons.2 ⟨subd18_1_636, List.forall_mem_cons.2 ⟨subd18_1_637, List.forall_mem_cons.2 ⟨subd18_1_638, List.forall_mem_cons.2 ⟨subd18_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_640 : subd18_1 [2, -2, -6] = true := by decide +kernel
theorem subd18_1_641 : subd18_1 [2, -2, -5] = true := by decide +kernel
theorem subd18_1_642 : subd18_1 [2, -2, -4] = true := by decide +kernel
theorem subd18_1_643 : subd18_1 [2, -2, -3] = true := by decide +kernel
theorem subd18_1_644 : subd18_1 [2, -2, -2] = true := by decide +kernel
theorem subd18_1_645 : subd18_1 [2, -2, -1] = true := by decide +kernel
theorem subd18_1_646 : subd18_1 [2, -2, 0] = true := by decide +kernel
theorem subd18_1_647 : subd18_1 [2, -2, 1] = true := by decide +kernel
theorem subd18_1_648 : subd18_1 [2, -2, 2] = true := by decide +kernel
theorem subd18_1_649 : subd18_1 [2, -2, 3] = true := by decide +kernel
theorem subd18_1_650 : subd18_1 [2, -2, 4] = true := by decide +kernel
theorem subd18_1_651 : subd18_1 [2, -2, 5] = true := by decide +kernel
theorem subd18_1_652 : subd18_1 [2, -2, 6] = true := by decide +kernel
theorem subd18_1_653 : subd18_1 [2, -2, 7] = true := by decide +kernel
theorem subd18_1_654 : subd18_1 [2, -2, 8] = true := by decide +kernel
theorem subd18_1_655 : subd18_1 [2, -1, -6] = true := by decide +kernel
theorem subd18_1_656 : subd18_1 [2, -1, -5] = true := by decide +kernel
theorem subd18_1_657 : subd18_1 [2, -1, -4] = true := by decide +kernel
theorem subd18_1_658 : subd18_1 [2, -1, -3] = true := by decide +kernel
theorem subd18_1_659 : subd18_1 [2, -1, -2] = true := by decide +kernel
theorem subd18_1_660 : subd18_1 [2, -1, -1] = true := by decide +kernel
theorem subd18_1_661 : subd18_1 [2, -1, 0] = true := by decide +kernel
theorem subd18_1_662 : subd18_1 [2, -1, 1] = true := by decide +kernel
theorem subd18_1_663 : subd18_1 [2, -1, 2] = true := by decide +kernel
theorem subd18_1_664 : subd18_1 [2, -1, 3] = true := by decide +kernel
theorem subd18_1_665 : subd18_1 [2, -1, 4] = true := by decide +kernel
theorem subd18_1_666 : subd18_1 [2, -1, 5] = true := by decide +kernel
theorem subd18_1_667 : subd18_1 [2, -1, 6] = true := by decide +kernel
theorem subd18_1_668 : subd18_1 [2, -1, 7] = true := by decide +kernel
theorem subd18_1_669 : subd18_1 [2, -1, 8] = true := by decide +kernel
theorem subd18_1_670 : subd18_1 [2, 0, -7] = true := by decide +kernel
theorem subd18_1_671 : subd18_1 [2, 0, -6] = true := by decide +kernel
theorem sbd18_1_20 : ∀ q ∈ blkd18_1_20, subd18_1 q = true := by
  unfold blkd18_1_20
  exact List.forall_mem_cons.2 ⟨subd18_1_640, List.forall_mem_cons.2 ⟨subd18_1_641, List.forall_mem_cons.2 ⟨subd18_1_642, List.forall_mem_cons.2 ⟨subd18_1_643, List.forall_mem_cons.2 ⟨subd18_1_644, List.forall_mem_cons.2 ⟨subd18_1_645, List.forall_mem_cons.2 ⟨subd18_1_646, List.forall_mem_cons.2 ⟨subd18_1_647, List.forall_mem_cons.2 ⟨subd18_1_648, List.forall_mem_cons.2 ⟨subd18_1_649, List.forall_mem_cons.2 ⟨subd18_1_650, List.forall_mem_cons.2 ⟨subd18_1_651, List.forall_mem_cons.2 ⟨subd18_1_652, List.forall_mem_cons.2 ⟨subd18_1_653, List.forall_mem_cons.2 ⟨subd18_1_654, List.forall_mem_cons.2 ⟨subd18_1_655, List.forall_mem_cons.2 ⟨subd18_1_656, List.forall_mem_cons.2 ⟨subd18_1_657, List.forall_mem_cons.2 ⟨subd18_1_658, List.forall_mem_cons.2 ⟨subd18_1_659, List.forall_mem_cons.2 ⟨subd18_1_660, List.forall_mem_cons.2 ⟨subd18_1_661, List.forall_mem_cons.2 ⟨subd18_1_662, List.forall_mem_cons.2 ⟨subd18_1_663, List.forall_mem_cons.2 ⟨subd18_1_664, List.forall_mem_cons.2 ⟨subd18_1_665, List.forall_mem_cons.2 ⟨subd18_1_666, List.forall_mem_cons.2 ⟨subd18_1_667, List.forall_mem_cons.2 ⟨subd18_1_668, List.forall_mem_cons.2 ⟨subd18_1_669, List.forall_mem_cons.2 ⟨subd18_1_670, List.forall_mem_cons.2 ⟨subd18_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_672 : subd18_1 [2, 0, -5] = true := by decide +kernel
theorem subd18_1_673 : subd18_1 [2, 0, -4] = true := by decide +kernel
theorem subd18_1_674 : subd18_1 [2, 0, -3] = true := by decide +kernel
theorem subd18_1_675 : subd18_1 [2, 0, -2] = true := by decide +kernel
theorem subd18_1_676 : subd18_1 [2, 0, -1] = true := by decide +kernel
theorem subd18_1_677 : subd18_1 [2, 0, 0] = true := by decide +kernel
theorem subd18_1_678 : subd18_1 [2, 0, 1] = true := by decide +kernel
theorem subd18_1_679 : subd18_1 [2, 0, 2] = true := by decide +kernel
theorem subd18_1_680 : subd18_1 [2, 0, 3] = true := by decide +kernel
theorem subd18_1_681 : subd18_1 [2, 0, 4] = true := by decide +kernel
theorem subd18_1_682 : subd18_1 [2, 0, 5] = true := by decide +kernel
theorem subd18_1_683 : subd18_1 [2, 0, 6] = true := by decide +kernel
theorem subd18_1_684 : subd18_1 [2, 0, 7] = true := by decide +kernel
theorem subd18_1_685 : subd18_1 [2, 0, 8] = true := by decide +kernel
theorem subd18_1_686 : subd18_1 [2, 1, -8] = true := by decide +kernel
theorem subd18_1_687 : subd18_1 [2, 1, -7] = true := by decide +kernel
theorem subd18_1_688 : subd18_1 [2, 1, -6] = true := by decide +kernel
theorem subd18_1_689 : subd18_1 [2, 1, -5] = true := by decide +kernel
theorem subd18_1_690 : subd18_1 [2, 1, -4] = true := by decide +kernel
theorem subd18_1_691 : subd18_1 [2, 1, -3] = true := by decide +kernel
theorem subd18_1_692 : subd18_1 [2, 1, -2] = true := by decide +kernel
theorem subd18_1_693 : subd18_1 [2, 1, -1] = true := by decide +kernel
theorem subd18_1_694 : subd18_1 [2, 1, 0] = true := by decide +kernel
theorem subd18_1_695 : subd18_1 [2, 1, 1] = true := by decide +kernel
theorem subd18_1_696 : subd18_1 [2, 1, 2] = true := by decide +kernel
theorem subd18_1_697 : subd18_1 [2, 1, 3] = true := by decide +kernel
theorem subd18_1_698 : subd18_1 [2, 1, 4] = true := by decide +kernel
theorem subd18_1_699 : subd18_1 [2, 1, 5] = true := by decide +kernel
theorem subd18_1_700 : subd18_1 [2, 1, 6] = true := by decide +kernel
theorem subd18_1_701 : subd18_1 [2, 1, 7] = true := by decide +kernel
theorem subd18_1_702 : subd18_1 [2, 2, -8] = true := by decide +kernel
theorem subd18_1_703 : subd18_1 [2, 2, -7] = true := by decide +kernel
theorem sbd18_1_21 : ∀ q ∈ blkd18_1_21, subd18_1 q = true := by
  unfold blkd18_1_21
  exact List.forall_mem_cons.2 ⟨subd18_1_672, List.forall_mem_cons.2 ⟨subd18_1_673, List.forall_mem_cons.2 ⟨subd18_1_674, List.forall_mem_cons.2 ⟨subd18_1_675, List.forall_mem_cons.2 ⟨subd18_1_676, List.forall_mem_cons.2 ⟨subd18_1_677, List.forall_mem_cons.2 ⟨subd18_1_678, List.forall_mem_cons.2 ⟨subd18_1_679, List.forall_mem_cons.2 ⟨subd18_1_680, List.forall_mem_cons.2 ⟨subd18_1_681, List.forall_mem_cons.2 ⟨subd18_1_682, List.forall_mem_cons.2 ⟨subd18_1_683, List.forall_mem_cons.2 ⟨subd18_1_684, List.forall_mem_cons.2 ⟨subd18_1_685, List.forall_mem_cons.2 ⟨subd18_1_686, List.forall_mem_cons.2 ⟨subd18_1_687, List.forall_mem_cons.2 ⟨subd18_1_688, List.forall_mem_cons.2 ⟨subd18_1_689, List.forall_mem_cons.2 ⟨subd18_1_690, List.forall_mem_cons.2 ⟨subd18_1_691, List.forall_mem_cons.2 ⟨subd18_1_692, List.forall_mem_cons.2 ⟨subd18_1_693, List.forall_mem_cons.2 ⟨subd18_1_694, List.forall_mem_cons.2 ⟨subd18_1_695, List.forall_mem_cons.2 ⟨subd18_1_696, List.forall_mem_cons.2 ⟨subd18_1_697, List.forall_mem_cons.2 ⟨subd18_1_698, List.forall_mem_cons.2 ⟨subd18_1_699, List.forall_mem_cons.2 ⟨subd18_1_700, List.forall_mem_cons.2 ⟨subd18_1_701, List.forall_mem_cons.2 ⟨subd18_1_702, List.forall_mem_cons.2 ⟨subd18_1_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_704 : subd18_1 [2, 2, -6] = true := by decide +kernel
theorem subd18_1_705 : subd18_1 [2, 2, -5] = true := by decide +kernel
theorem subd18_1_706 : subd18_1 [2, 2, -4] = true := by decide +kernel
theorem subd18_1_707 : subd18_1 [2, 2, -3] = true := by decide +kernel
theorem subd18_1_708 : subd18_1 [2, 2, -2] = true := by decide +kernel
theorem subd18_1_709 : subd18_1 [2, 2, -1] = true := by decide +kernel
theorem subd18_1_710 : subd18_1 [2, 2, 0] = true := by decide +kernel
theorem subd18_1_711 : subd18_1 [2, 2, 1] = true := by decide +kernel
theorem subd18_1_712 : subd18_1 [2, 2, 2] = true := by decide +kernel
theorem subd18_1_713 : subd18_1 [2, 2, 3] = true := by decide +kernel
theorem subd18_1_714 : subd18_1 [2, 2, 4] = true := by decide +kernel
theorem subd18_1_715 : subd18_1 [2, 2, 5] = true := by decide +kernel
theorem subd18_1_716 : subd18_1 [2, 2, 6] = true := by decide +kernel
theorem subd18_1_717 : subd18_1 [2, 2, 7] = true := by decide +kernel
theorem subd18_1_718 : subd18_1 [2, 3, -8] = true := by decide +kernel
theorem subd18_1_719 : subd18_1 [2, 3, -7] = true := by decide +kernel
theorem subd18_1_720 : subd18_1 [2, 3, -6] = true := by decide +kernel
theorem subd18_1_721 : subd18_1 [2, 3, -5] = true := by decide +kernel
theorem subd18_1_722 : subd18_1 [2, 3, -4] = true := by decide +kernel
theorem subd18_1_723 : subd18_1 [2, 3, -3] = true := by decide +kernel
theorem subd18_1_724 : subd18_1 [2, 3, -2] = true := by decide +kernel
theorem subd18_1_725 : subd18_1 [2, 3, -1] = true := by decide +kernel
theorem subd18_1_726 : subd18_1 [2, 3, 0] = true := by decide +kernel
theorem subd18_1_727 : subd18_1 [2, 3, 1] = true := by decide +kernel
theorem subd18_1_728 : subd18_1 [2, 3, 2] = true := by decide +kernel
theorem subd18_1_729 : subd18_1 [2, 3, 3] = true := by decide +kernel
theorem subd18_1_730 : subd18_1 [2, 3, 4] = true := by decide +kernel
theorem subd18_1_731 : subd18_1 [2, 3, 5] = true := by decide +kernel
theorem subd18_1_732 : subd18_1 [2, 3, 6] = true := by decide +kernel
theorem subd18_1_733 : subd18_1 [2, 4, -8] = true := by decide +kernel
theorem subd18_1_734 : subd18_1 [2, 4, -7] = true := by decide +kernel
theorem subd18_1_735 : subd18_1 [2, 4, -6] = true := by decide +kernel
theorem sbd18_1_22 : ∀ q ∈ blkd18_1_22, subd18_1 q = true := by
  unfold blkd18_1_22
  exact List.forall_mem_cons.2 ⟨subd18_1_704, List.forall_mem_cons.2 ⟨subd18_1_705, List.forall_mem_cons.2 ⟨subd18_1_706, List.forall_mem_cons.2 ⟨subd18_1_707, List.forall_mem_cons.2 ⟨subd18_1_708, List.forall_mem_cons.2 ⟨subd18_1_709, List.forall_mem_cons.2 ⟨subd18_1_710, List.forall_mem_cons.2 ⟨subd18_1_711, List.forall_mem_cons.2 ⟨subd18_1_712, List.forall_mem_cons.2 ⟨subd18_1_713, List.forall_mem_cons.2 ⟨subd18_1_714, List.forall_mem_cons.2 ⟨subd18_1_715, List.forall_mem_cons.2 ⟨subd18_1_716, List.forall_mem_cons.2 ⟨subd18_1_717, List.forall_mem_cons.2 ⟨subd18_1_718, List.forall_mem_cons.2 ⟨subd18_1_719, List.forall_mem_cons.2 ⟨subd18_1_720, List.forall_mem_cons.2 ⟨subd18_1_721, List.forall_mem_cons.2 ⟨subd18_1_722, List.forall_mem_cons.2 ⟨subd18_1_723, List.forall_mem_cons.2 ⟨subd18_1_724, List.forall_mem_cons.2 ⟨subd18_1_725, List.forall_mem_cons.2 ⟨subd18_1_726, List.forall_mem_cons.2 ⟨subd18_1_727, List.forall_mem_cons.2 ⟨subd18_1_728, List.forall_mem_cons.2 ⟨subd18_1_729, List.forall_mem_cons.2 ⟨subd18_1_730, List.forall_mem_cons.2 ⟨subd18_1_731, List.forall_mem_cons.2 ⟨subd18_1_732, List.forall_mem_cons.2 ⟨subd18_1_733, List.forall_mem_cons.2 ⟨subd18_1_734, List.forall_mem_cons.2 ⟨subd18_1_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_736 : subd18_1 [2, 4, -5] = true := by decide +kernel
theorem subd18_1_737 : subd18_1 [2, 4, -4] = true := by decide +kernel
theorem subd18_1_738 : subd18_1 [2, 4, -3] = true := by decide +kernel
theorem subd18_1_739 : subd18_1 [2, 4, -2] = true := by decide +kernel
theorem subd18_1_740 : subd18_1 [2, 4, -1] = true := by decide +kernel
theorem subd18_1_741 : subd18_1 [2, 4, 0] = true := by decide +kernel
theorem subd18_1_742 : subd18_1 [2, 4, 1] = true := by decide +kernel
theorem subd18_1_743 : subd18_1 [2, 4, 2] = true := by decide +kernel
theorem subd18_1_744 : subd18_1 [2, 4, 3] = true := by decide +kernel
theorem subd18_1_745 : subd18_1 [2, 4, 4] = true := by decide +kernel
theorem subd18_1_746 : subd18_1 [2, 4, 5] = true := by decide +kernel
theorem subd18_1_747 : subd18_1 [2, 5] = true := by decide +kernel
theorem subd18_1_748 : subd18_1 [2, 6] = true := by decide +kernel
theorem subd18_1_749 : subd18_1 [2, 7] = true := by decide +kernel
theorem subd18_1_750 : subd18_1 [3, -6] = true := by decide +kernel
theorem subd18_1_751 : subd18_1 [3, -5] = true := by decide +kernel
theorem subd18_1_752 : subd18_1 [3, -4] = true := by decide +kernel
theorem subd18_1_753 : subd18_1 [3, -3] = true := by decide +kernel
theorem subd18_1_754 : subd18_1 [3, -2] = true := by decide +kernel
theorem subd18_1_755 : subd18_1 [3, -1, -5] = true := by decide +kernel
theorem subd18_1_756 : subd18_1 [3, -1, -4] = true := by decide +kernel
theorem subd18_1_757 : subd18_1 [3, -1, -3] = true := by decide +kernel
theorem subd18_1_758 : subd18_1 [3, -1, -2] = true := by decide +kernel
theorem subd18_1_759 : subd18_1 [3, -1, -1] = true := by decide +kernel
theorem subd18_1_760 : subd18_1 [3, -1, 0] = true := by decide +kernel
theorem subd18_1_761 : subd18_1 [3, -1, 1] = true := by decide +kernel
theorem subd18_1_762 : subd18_1 [3, -1, 2] = true := by decide +kernel
theorem subd18_1_763 : subd18_1 [3, -1, 3] = true := by decide +kernel
theorem subd18_1_764 : subd18_1 [3, -1, 4] = true := by decide +kernel
theorem subd18_1_765 : subd18_1 [3, -1, 5] = true := by decide +kernel
theorem subd18_1_766 : subd18_1 [3, -1, 6] = true := by decide +kernel
theorem subd18_1_767 : subd18_1 [3, -1, 7] = true := by decide +kernel
theorem sbd18_1_23 : ∀ q ∈ blkd18_1_23, subd18_1 q = true := by
  unfold blkd18_1_23
  exact List.forall_mem_cons.2 ⟨subd18_1_736, List.forall_mem_cons.2 ⟨subd18_1_737, List.forall_mem_cons.2 ⟨subd18_1_738, List.forall_mem_cons.2 ⟨subd18_1_739, List.forall_mem_cons.2 ⟨subd18_1_740, List.forall_mem_cons.2 ⟨subd18_1_741, List.forall_mem_cons.2 ⟨subd18_1_742, List.forall_mem_cons.2 ⟨subd18_1_743, List.forall_mem_cons.2 ⟨subd18_1_744, List.forall_mem_cons.2 ⟨subd18_1_745, List.forall_mem_cons.2 ⟨subd18_1_746, List.forall_mem_cons.2 ⟨subd18_1_747, List.forall_mem_cons.2 ⟨subd18_1_748, List.forall_mem_cons.2 ⟨subd18_1_749, List.forall_mem_cons.2 ⟨subd18_1_750, List.forall_mem_cons.2 ⟨subd18_1_751, List.forall_mem_cons.2 ⟨subd18_1_752, List.forall_mem_cons.2 ⟨subd18_1_753, List.forall_mem_cons.2 ⟨subd18_1_754, List.forall_mem_cons.2 ⟨subd18_1_755, List.forall_mem_cons.2 ⟨subd18_1_756, List.forall_mem_cons.2 ⟨subd18_1_757, List.forall_mem_cons.2 ⟨subd18_1_758, List.forall_mem_cons.2 ⟨subd18_1_759, List.forall_mem_cons.2 ⟨subd18_1_760, List.forall_mem_cons.2 ⟨subd18_1_761, List.forall_mem_cons.2 ⟨subd18_1_762, List.forall_mem_cons.2 ⟨subd18_1_763, List.forall_mem_cons.2 ⟨subd18_1_764, List.forall_mem_cons.2 ⟨subd18_1_765, List.forall_mem_cons.2 ⟨subd18_1_766, List.forall_mem_cons.2 ⟨subd18_1_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_768 : subd18_1 [3, -1, 8] = true := by decide +kernel
theorem subd18_1_769 : subd18_1 [3, 0, -6] = true := by decide +kernel
theorem subd18_1_770 : subd18_1 [3, 0, -5] = true := by decide +kernel
theorem subd18_1_771 : subd18_1 [3, 0, -4] = true := by decide +kernel
theorem subd18_1_772 : subd18_1 [3, 0, -3] = true := by decide +kernel
theorem subd18_1_773 : subd18_1 [3, 0, -2] = true := by decide +kernel
theorem subd18_1_774 : subd18_1 [3, 0, -1] = true := by decide +kernel
theorem subd18_1_775 : subd18_1 [3, 0, 0] = true := by decide +kernel
theorem subd18_1_776 : subd18_1 [3, 0, 1] = true := by decide +kernel
theorem subd18_1_777 : subd18_1 [3, 0, 2] = true := by decide +kernel
theorem subd18_1_778 : subd18_1 [3, 0, 3] = true := by decide +kernel
theorem subd18_1_779 : subd18_1 [3, 0, 4] = true := by decide +kernel
theorem subd18_1_780 : subd18_1 [3, 0, 5] = true := by decide +kernel
theorem subd18_1_781 : subd18_1 [3, 0, 6] = true := by decide +kernel
theorem subd18_1_782 : subd18_1 [3, 0, 7] = true := by decide +kernel
theorem subd18_1_783 : subd18_1 [3, 0, 8] = true := by decide +kernel
theorem subd18_1_784 : subd18_1 [3, 1, -7] = true := by decide +kernel
theorem subd18_1_785 : subd18_1 [3, 1, -6] = true := by decide +kernel
theorem subd18_1_786 : subd18_1 [3, 1, -5] = true := by decide +kernel
theorem subd18_1_787 : subd18_1 [3, 1, -4] = true := by decide +kernel
theorem subd18_1_788 : subd18_1 [3, 1, -3] = true := by decide +kernel
theorem subd18_1_789 : subd18_1 [3, 1, -2] = true := by decide +kernel
theorem subd18_1_790 : subd18_1 [3, 1, -1] = true := by decide +kernel
theorem subd18_1_791 : subd18_1 [3, 1, 0] = true := by decide +kernel
theorem subd18_1_792 : subd18_1 [3, 1, 1] = true := by decide +kernel
theorem subd18_1_793 : subd18_1 [3, 1, 2] = true := by decide +kernel
theorem subd18_1_794 : subd18_1 [3, 1, 3] = true := by decide +kernel
theorem subd18_1_795 : subd18_1 [3, 1, 4] = true := by decide +kernel
theorem subd18_1_796 : subd18_1 [3, 1, 5] = true := by decide +kernel
theorem subd18_1_797 : subd18_1 [3, 1, 6] = true := by decide +kernel
theorem subd18_1_798 : subd18_1 [3, 1, 7] = true := by decide +kernel
theorem subd18_1_799 : subd18_1 [3, 2, -7] = true := by decide +kernel
theorem sbd18_1_24 : ∀ q ∈ blkd18_1_24, subd18_1 q = true := by
  unfold blkd18_1_24
  exact List.forall_mem_cons.2 ⟨subd18_1_768, List.forall_mem_cons.2 ⟨subd18_1_769, List.forall_mem_cons.2 ⟨subd18_1_770, List.forall_mem_cons.2 ⟨subd18_1_771, List.forall_mem_cons.2 ⟨subd18_1_772, List.forall_mem_cons.2 ⟨subd18_1_773, List.forall_mem_cons.2 ⟨subd18_1_774, List.forall_mem_cons.2 ⟨subd18_1_775, List.forall_mem_cons.2 ⟨subd18_1_776, List.forall_mem_cons.2 ⟨subd18_1_777, List.forall_mem_cons.2 ⟨subd18_1_778, List.forall_mem_cons.2 ⟨subd18_1_779, List.forall_mem_cons.2 ⟨subd18_1_780, List.forall_mem_cons.2 ⟨subd18_1_781, List.forall_mem_cons.2 ⟨subd18_1_782, List.forall_mem_cons.2 ⟨subd18_1_783, List.forall_mem_cons.2 ⟨subd18_1_784, List.forall_mem_cons.2 ⟨subd18_1_785, List.forall_mem_cons.2 ⟨subd18_1_786, List.forall_mem_cons.2 ⟨subd18_1_787, List.forall_mem_cons.2 ⟨subd18_1_788, List.forall_mem_cons.2 ⟨subd18_1_789, List.forall_mem_cons.2 ⟨subd18_1_790, List.forall_mem_cons.2 ⟨subd18_1_791, List.forall_mem_cons.2 ⟨subd18_1_792, List.forall_mem_cons.2 ⟨subd18_1_793, List.forall_mem_cons.2 ⟨subd18_1_794, List.forall_mem_cons.2 ⟨subd18_1_795, List.forall_mem_cons.2 ⟨subd18_1_796, List.forall_mem_cons.2 ⟨subd18_1_797, List.forall_mem_cons.2 ⟨subd18_1_798, List.forall_mem_cons.2 ⟨subd18_1_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_800 : subd18_1 [3, 2, -6] = true := by decide +kernel
theorem subd18_1_801 : subd18_1 [3, 2, -5] = true := by decide +kernel
theorem subd18_1_802 : subd18_1 [3, 2, -4] = true := by decide +kernel
theorem subd18_1_803 : subd18_1 [3, 2, -3] = true := by decide +kernel
theorem subd18_1_804 : subd18_1 [3, 2, -2] = true := by decide +kernel
theorem subd18_1_805 : subd18_1 [3, 2, -1] = true := by decide +kernel
theorem subd18_1_806 : subd18_1 [3, 2, 0] = true := by decide +kernel
theorem subd18_1_807 : subd18_1 [3, 2, 1] = true := by decide +kernel
theorem subd18_1_808 : subd18_1 [3, 2, 2] = true := by decide +kernel
theorem subd18_1_809 : subd18_1 [3, 2, 3] = true := by decide +kernel
theorem subd18_1_810 : subd18_1 [3, 2, 4] = true := by decide +kernel
theorem subd18_1_811 : subd18_1 [3, 2, 5] = true := by decide +kernel
theorem subd18_1_812 : subd18_1 [3, 2, 6] = true := by decide +kernel
theorem subd18_1_813 : subd18_1 [3, 2, 7] = true := by decide +kernel
theorem subd18_1_814 : subd18_1 [3, 3, -7] = true := by decide +kernel
theorem subd18_1_815 : subd18_1 [3, 3, -6] = true := by decide +kernel
theorem subd18_1_816 : subd18_1 [3, 3, -5] = true := by decide +kernel
theorem subd18_1_817 : subd18_1 [3, 3, -4] = true := by decide +kernel
theorem subd18_1_818 : subd18_1 [3, 3, -3] = true := by decide +kernel
theorem subd18_1_819 : subd18_1 [3, 3, -2] = true := by decide +kernel
theorem subd18_1_820 : subd18_1 [3, 3, -1] = true := by decide +kernel
theorem subd18_1_821 : subd18_1 [3, 3, 0] = true := by decide +kernel
theorem subd18_1_822 : subd18_1 [3, 3, 1] = true := by decide +kernel
theorem subd18_1_823 : subd18_1 [3, 3, 2] = true := by decide +kernel
theorem subd18_1_824 : subd18_1 [3, 3, 3] = true := by decide +kernel
theorem subd18_1_825 : subd18_1 [3, 3, 4] = true := by decide +kernel
theorem subd18_1_826 : subd18_1 [3, 3, 5] = true := by decide +kernel
theorem subd18_1_827 : subd18_1 [3, 3, 6] = true := by decide +kernel
theorem subd18_1_828 : subd18_1 [3, 4] = true := by decide +kernel
theorem subd18_1_829 : subd18_1 [3, 5] = true := by decide +kernel
theorem subd18_1_830 : subd18_1 [3, 6] = true := by decide +kernel
theorem subd18_1_831 : subd18_1 [3, 7] = true := by decide +kernel
theorem sbd18_1_25 : ∀ q ∈ blkd18_1_25, subd18_1 q = true := by
  unfold blkd18_1_25
  exact List.forall_mem_cons.2 ⟨subd18_1_800, List.forall_mem_cons.2 ⟨subd18_1_801, List.forall_mem_cons.2 ⟨subd18_1_802, List.forall_mem_cons.2 ⟨subd18_1_803, List.forall_mem_cons.2 ⟨subd18_1_804, List.forall_mem_cons.2 ⟨subd18_1_805, List.forall_mem_cons.2 ⟨subd18_1_806, List.forall_mem_cons.2 ⟨subd18_1_807, List.forall_mem_cons.2 ⟨subd18_1_808, List.forall_mem_cons.2 ⟨subd18_1_809, List.forall_mem_cons.2 ⟨subd18_1_810, List.forall_mem_cons.2 ⟨subd18_1_811, List.forall_mem_cons.2 ⟨subd18_1_812, List.forall_mem_cons.2 ⟨subd18_1_813, List.forall_mem_cons.2 ⟨subd18_1_814, List.forall_mem_cons.2 ⟨subd18_1_815, List.forall_mem_cons.2 ⟨subd18_1_816, List.forall_mem_cons.2 ⟨subd18_1_817, List.forall_mem_cons.2 ⟨subd18_1_818, List.forall_mem_cons.2 ⟨subd18_1_819, List.forall_mem_cons.2 ⟨subd18_1_820, List.forall_mem_cons.2 ⟨subd18_1_821, List.forall_mem_cons.2 ⟨subd18_1_822, List.forall_mem_cons.2 ⟨subd18_1_823, List.forall_mem_cons.2 ⟨subd18_1_824, List.forall_mem_cons.2 ⟨subd18_1_825, List.forall_mem_cons.2 ⟨subd18_1_826, List.forall_mem_cons.2 ⟨subd18_1_827, List.forall_mem_cons.2 ⟨subd18_1_828, List.forall_mem_cons.2 ⟨subd18_1_829, List.forall_mem_cons.2 ⟨subd18_1_830, List.forall_mem_cons.2 ⟨subd18_1_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_1_832 : subd18_1 [4, -5] = true := by decide +kernel
theorem subd18_1_833 : subd18_1 [4, -4] = true := by decide +kernel
theorem subd18_1_834 : subd18_1 [4, -3] = true := by decide +kernel
theorem subd18_1_835 : subd18_1 [4, -2] = true := by decide +kernel
theorem subd18_1_836 : subd18_1 [4, -1] = true := by decide +kernel
theorem subd18_1_837 : subd18_1 [4, 0] = true := by decide +kernel
theorem subd18_1_838 : subd18_1 [4, 1] = true := by decide +kernel
theorem subd18_1_839 : subd18_1 [4, 2] = true := by decide +kernel
theorem subd18_1_840 : subd18_1 [4, 3] = true := by decide +kernel
theorem subd18_1_841 : subd18_1 [4, 4] = true := by decide +kernel
theorem subd18_1_842 : subd18_1 [4, 5] = true := by decide +kernel
theorem subd18_1_843 : subd18_1 [4, 6] = true := by decide +kernel
theorem subd18_1_844 : subd18_1 [5, -3] = true := by decide +kernel
theorem subd18_1_845 : subd18_1 [5, -2] = true := by decide +kernel
theorem subd18_1_846 : subd18_1 [5, -1] = true := by decide +kernel
theorem subd18_1_847 : subd18_1 [5, 0] = true := by decide +kernel
theorem subd18_1_848 : subd18_1 [5, 1] = true := by decide +kernel
theorem subd18_1_849 : subd18_1 [5, 2] = true := by decide +kernel
theorem subd18_1_850 : subd18_1 [5, 3] = true := by decide +kernel
theorem subd18_1_851 : subd18_1 [5, 4] = true := by decide +kernel
theorem subd18_1_852 : subd18_1 [5, 5] = true := by decide +kernel
theorem subd18_1_853 : subd18_1 [5, 6] = true := by decide +kernel
theorem subd18_1_854 : subd18_1 [6] = true := by decide +kernel
theorem sbd18_1_26 : ∀ q ∈ blkd18_1_26, subd18_1 q = true := by
  unfold blkd18_1_26
  exact List.forall_mem_cons.2 ⟨subd18_1_832, List.forall_mem_cons.2 ⟨subd18_1_833, List.forall_mem_cons.2 ⟨subd18_1_834, List.forall_mem_cons.2 ⟨subd18_1_835, List.forall_mem_cons.2 ⟨subd18_1_836, List.forall_mem_cons.2 ⟨subd18_1_837, List.forall_mem_cons.2 ⟨subd18_1_838, List.forall_mem_cons.2 ⟨subd18_1_839, List.forall_mem_cons.2 ⟨subd18_1_840, List.forall_mem_cons.2 ⟨subd18_1_841, List.forall_mem_cons.2 ⟨subd18_1_842, List.forall_mem_cons.2 ⟨subd18_1_843, List.forall_mem_cons.2 ⟨subd18_1_844, List.forall_mem_cons.2 ⟨subd18_1_845, List.forall_mem_cons.2 ⟨subd18_1_846, List.forall_mem_cons.2 ⟨subd18_1_847, List.forall_mem_cons.2 ⟨subd18_1_848, List.forall_mem_cons.2 ⟨subd18_1_849, List.forall_mem_cons.2 ⟨subd18_1_850, List.forall_mem_cons.2 ⟨subd18_1_851, List.forall_mem_cons.2 ⟨subd18_1_852, List.forall_mem_cons.2 ⟨subd18_1_853, List.forall_mem_cons.2 ⟨subd18_1_854, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd18_2 : ldCheck G d18_2.U d18_2.ms ldd18_2 = true := by decide +kernel
theorem pre_okd18_2 : subPre G cell18 d18_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
