import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub13_576 : sub13 [1, -2, -5] = true := by decide +kernel
theorem sub13_577 : sub13 [1, -2, -4] = true := by decide +kernel
theorem sub13_578 : sub13 [1, -2, -3] = true := by decide +kernel
theorem sub13_579 : sub13 [1, -2, -2] = true := by decide +kernel
theorem sub13_580 : sub13 [1, -2, -1] = true := by decide +kernel
theorem sub13_581 : sub13 [1, -2, 0] = true := by decide +kernel
theorem sub13_582 : sub13 [1, -2, 1] = true := by decide +kernel
theorem sub13_583 : sub13 [1, -2, 2] = true := by decide +kernel
theorem sub13_584 : sub13 [1, -2, 3] = true := by decide +kernel
theorem sub13_585 : sub13 [1, -2, 4] = true := by decide +kernel
theorem sub13_586 : sub13 [1, -2, 5] = true := by decide +kernel
theorem sub13_587 : sub13 [1, -2, 6] = true := by decide +kernel
theorem sub13_588 : sub13 [1, -2, 7] = true := by decide +kernel
theorem sub13_589 : sub13 [1, -1, -8] = true := by decide +kernel
theorem sub13_590 : sub13 [1, -1, -7] = true := by decide +kernel
theorem sub13_591 : sub13 [1, -1, -6] = true := by decide +kernel
theorem sub13_592 : sub13 [1, -1, -5] = true := by decide +kernel
theorem sub13_593 : sub13 [1, -1, -4] = true := by decide +kernel
theorem sub13_594 : sub13 [1, -1, -3] = true := by decide +kernel
theorem sub13_595 : sub13 [1, -1, -2] = true := by decide +kernel
theorem sub13_596 : sub13 [1, -1, -1] = true := by decide +kernel
theorem sub13_597 : sub13 [1, -1, 0] = true := by decide +kernel
theorem sub13_598 : sub13 [1, -1, 1] = true := by decide +kernel
theorem sub13_599 : sub13 [1, -1, 2] = true := by decide +kernel
theorem sub13_600 : sub13 [1, -1, 3] = true := by decide +kernel
theorem sub13_601 : sub13 [1, -1, 4] = true := by decide +kernel
theorem sub13_602 : sub13 [1, -1, 5] = true := by decide +kernel
theorem sub13_603 : sub13 [1, -1, 6] = true := by decide +kernel
theorem sub13_604 : sub13 [1, -1, 7] = true := by decide +kernel
theorem sub13_605 : sub13 [1, 0, -8] = true := by decide +kernel
theorem sub13_606 : sub13 [1, 0, -7] = true := by decide +kernel
theorem sub13_607 : sub13 [1, 0, -6] = true := by decide +kernel
theorem sb13_18 : ∀ q ∈ blk13_18, sub13 q = true := by
  unfold blk13_18
  exact List.forall_mem_cons.2 ⟨sub13_576, List.forall_mem_cons.2 ⟨sub13_577, List.forall_mem_cons.2 ⟨sub13_578, List.forall_mem_cons.2 ⟨sub13_579, List.forall_mem_cons.2 ⟨sub13_580, List.forall_mem_cons.2 ⟨sub13_581, List.forall_mem_cons.2 ⟨sub13_582, List.forall_mem_cons.2 ⟨sub13_583, List.forall_mem_cons.2 ⟨sub13_584, List.forall_mem_cons.2 ⟨sub13_585, List.forall_mem_cons.2 ⟨sub13_586, List.forall_mem_cons.2 ⟨sub13_587, List.forall_mem_cons.2 ⟨sub13_588, List.forall_mem_cons.2 ⟨sub13_589, List.forall_mem_cons.2 ⟨sub13_590, List.forall_mem_cons.2 ⟨sub13_591, List.forall_mem_cons.2 ⟨sub13_592, List.forall_mem_cons.2 ⟨sub13_593, List.forall_mem_cons.2 ⟨sub13_594, List.forall_mem_cons.2 ⟨sub13_595, List.forall_mem_cons.2 ⟨sub13_596, List.forall_mem_cons.2 ⟨sub13_597, List.forall_mem_cons.2 ⟨sub13_598, List.forall_mem_cons.2 ⟨sub13_599, List.forall_mem_cons.2 ⟨sub13_600, List.forall_mem_cons.2 ⟨sub13_601, List.forall_mem_cons.2 ⟨sub13_602, List.forall_mem_cons.2 ⟨sub13_603, List.forall_mem_cons.2 ⟨sub13_604, List.forall_mem_cons.2 ⟨sub13_605, List.forall_mem_cons.2 ⟨sub13_606, List.forall_mem_cons.2 ⟨sub13_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_608 : sub13 [1, 0, -5] = true := by decide +kernel
theorem sub13_609 : sub13 [1, 0, -4] = true := by decide +kernel
theorem sub13_610 : sub13 [1, 0, -3] = true := by decide +kernel
theorem sub13_611 : sub13 [1, 0, -2] = true := by decide +kernel
theorem sub13_612 : sub13 [1, 0, -1] = true := by decide +kernel
theorem sub13_613 : sub13 [1, 0, 0] = true := by decide +kernel
theorem sub13_614 : sub13 [1, 0, 1] = true := by decide +kernel
theorem sub13_615 : sub13 [1, 0, 2] = true := by decide +kernel
theorem sub13_616 : sub13 [1, 0, 3] = true := by decide +kernel
theorem sub13_617 : sub13 [1, 0, 4] = true := by decide +kernel
theorem sub13_618 : sub13 [1, 0, 5] = true := by decide +kernel
theorem sub13_619 : sub13 [1, 0, 6] = true := by decide +kernel
theorem sub13_620 : sub13 [1, 0, 7] = true := by decide +kernel
theorem sub13_621 : sub13 [1, 1, -8] = true := by decide +kernel
theorem sub13_622 : sub13 [1, 1, -7] = true := by decide +kernel
theorem sub13_623 : sub13 [1, 1, -6] = true := by decide +kernel
theorem sub13_624 : sub13 [1, 1, -5] = true := by decide +kernel
theorem sub13_625 : sub13 [1, 1, -4] = true := by decide +kernel
theorem sub13_626 : sub13 [1, 1, -3] = true := by decide +kernel
theorem sub13_627 : sub13 [1, 1, -2] = true := by decide +kernel
theorem sub13_628 : sub13 [1, 1, -1] = true := by decide +kernel
theorem sub13_629 : sub13 [1, 1, 0] = true := by decide +kernel
theorem sub13_630 : sub13 [1, 1, 1] = true := by decide +kernel
theorem sub13_631 : sub13 [1, 1, 2] = true := by decide +kernel
theorem sub13_632 : sub13 [1, 1, 3] = true := by decide +kernel
theorem sub13_633 : sub13 [1, 1, 4] = true := by decide +kernel
theorem sub13_634 : sub13 [1, 1, 5] = true := by decide +kernel
theorem sub13_635 : sub13 [1, 1, 6] = true := by decide +kernel
theorem sub13_636 : sub13 [1, 1, 7] = true := by decide +kernel
theorem sub13_637 : sub13 [1, 2, -8] = true := by decide +kernel
theorem sub13_638 : sub13 [1, 2, -7] = true := by decide +kernel
theorem sub13_639 : sub13 [1, 2, -6] = true := by decide +kernel
theorem sb13_19 : ∀ q ∈ blk13_19, sub13 q = true := by
  unfold blk13_19
  exact List.forall_mem_cons.2 ⟨sub13_608, List.forall_mem_cons.2 ⟨sub13_609, List.forall_mem_cons.2 ⟨sub13_610, List.forall_mem_cons.2 ⟨sub13_611, List.forall_mem_cons.2 ⟨sub13_612, List.forall_mem_cons.2 ⟨sub13_613, List.forall_mem_cons.2 ⟨sub13_614, List.forall_mem_cons.2 ⟨sub13_615, List.forall_mem_cons.2 ⟨sub13_616, List.forall_mem_cons.2 ⟨sub13_617, List.forall_mem_cons.2 ⟨sub13_618, List.forall_mem_cons.2 ⟨sub13_619, List.forall_mem_cons.2 ⟨sub13_620, List.forall_mem_cons.2 ⟨sub13_621, List.forall_mem_cons.2 ⟨sub13_622, List.forall_mem_cons.2 ⟨sub13_623, List.forall_mem_cons.2 ⟨sub13_624, List.forall_mem_cons.2 ⟨sub13_625, List.forall_mem_cons.2 ⟨sub13_626, List.forall_mem_cons.2 ⟨sub13_627, List.forall_mem_cons.2 ⟨sub13_628, List.forall_mem_cons.2 ⟨sub13_629, List.forall_mem_cons.2 ⟨sub13_630, List.forall_mem_cons.2 ⟨sub13_631, List.forall_mem_cons.2 ⟨sub13_632, List.forall_mem_cons.2 ⟨sub13_633, List.forall_mem_cons.2 ⟨sub13_634, List.forall_mem_cons.2 ⟨sub13_635, List.forall_mem_cons.2 ⟨sub13_636, List.forall_mem_cons.2 ⟨sub13_637, List.forall_mem_cons.2 ⟨sub13_638, List.forall_mem_cons.2 ⟨sub13_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_640 : sub13 [1, 2, -5] = true := by decide +kernel
theorem sub13_641 : sub13 [1, 2, -4] = true := by decide +kernel
theorem sub13_642 : sub13 [1, 2, -3] = true := by decide +kernel
theorem sub13_643 : sub13 [1, 2, -2] = true := by decide +kernel
theorem sub13_644 : sub13 [1, 2, -1] = true := by decide +kernel
theorem sub13_645 : sub13 [1, 2, 0] = true := by decide +kernel
theorem sub13_646 : sub13 [1, 2, 1] = true := by decide +kernel
theorem sub13_647 : sub13 [1, 2, 2] = true := by decide +kernel
theorem sub13_648 : sub13 [1, 2, 3] = true := by decide +kernel
theorem sub13_649 : sub13 [1, 2, 4] = true := by decide +kernel
theorem sub13_650 : sub13 [1, 2, 5] = true := by decide +kernel
theorem sub13_651 : sub13 [1, 2, 6] = true := by decide +kernel
theorem sub13_652 : sub13 [1, 3, -8] = true := by decide +kernel
theorem sub13_653 : sub13 [1, 3, -7] = true := by decide +kernel
theorem sub13_654 : sub13 [1, 3, -6] = true := by decide +kernel
theorem sub13_655 : sub13 [1, 3, -5] = true := by decide +kernel
theorem sub13_656 : sub13 [1, 3, -4] = true := by decide +kernel
theorem sub13_657 : sub13 [1, 3, -3] = true := by decide +kernel
theorem sub13_658 : sub13 [1, 3, -2] = true := by decide +kernel
theorem sub13_659 : sub13 [1, 3, -1] = true := by decide +kernel
theorem sub13_660 : sub13 [1, 3, 0] = true := by decide +kernel
theorem sub13_661 : sub13 [1, 3, 1] = true := by decide +kernel
theorem sub13_662 : sub13 [1, 3, 2] = true := by decide +kernel
theorem sub13_663 : sub13 [1, 3, 3] = true := by decide +kernel
theorem sub13_664 : sub13 [1, 3, 4] = true := by decide +kernel
theorem sub13_665 : sub13 [1, 3, 5] = true := by decide +kernel
theorem sub13_666 : sub13 [1, 3, 6] = true := by decide +kernel
theorem sub13_667 : sub13 [1, 4] = true := by decide +kernel
theorem sub13_668 : sub13 [1, 5] = true := by decide +kernel
theorem sub13_669 : sub13 [1, 6] = true := by decide +kernel
theorem sub13_670 : sub13 [1, 7] = true := by decide +kernel
theorem sub13_671 : sub13 [2, -8] = true := by decide +kernel
theorem sb13_20 : ∀ q ∈ blk13_20, sub13 q = true := by
  unfold blk13_20
  exact List.forall_mem_cons.2 ⟨sub13_640, List.forall_mem_cons.2 ⟨sub13_641, List.forall_mem_cons.2 ⟨sub13_642, List.forall_mem_cons.2 ⟨sub13_643, List.forall_mem_cons.2 ⟨sub13_644, List.forall_mem_cons.2 ⟨sub13_645, List.forall_mem_cons.2 ⟨sub13_646, List.forall_mem_cons.2 ⟨sub13_647, List.forall_mem_cons.2 ⟨sub13_648, List.forall_mem_cons.2 ⟨sub13_649, List.forall_mem_cons.2 ⟨sub13_650, List.forall_mem_cons.2 ⟨sub13_651, List.forall_mem_cons.2 ⟨sub13_652, List.forall_mem_cons.2 ⟨sub13_653, List.forall_mem_cons.2 ⟨sub13_654, List.forall_mem_cons.2 ⟨sub13_655, List.forall_mem_cons.2 ⟨sub13_656, List.forall_mem_cons.2 ⟨sub13_657, List.forall_mem_cons.2 ⟨sub13_658, List.forall_mem_cons.2 ⟨sub13_659, List.forall_mem_cons.2 ⟨sub13_660, List.forall_mem_cons.2 ⟨sub13_661, List.forall_mem_cons.2 ⟨sub13_662, List.forall_mem_cons.2 ⟨sub13_663, List.forall_mem_cons.2 ⟨sub13_664, List.forall_mem_cons.2 ⟨sub13_665, List.forall_mem_cons.2 ⟨sub13_666, List.forall_mem_cons.2 ⟨sub13_667, List.forall_mem_cons.2 ⟨sub13_668, List.forall_mem_cons.2 ⟨sub13_669, List.forall_mem_cons.2 ⟨sub13_670, List.forall_mem_cons.2 ⟨sub13_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_672 : sub13 [2, -7] = true := by decide +kernel
theorem sub13_673 : sub13 [2, -6] = true := by decide +kernel
theorem sub13_674 : sub13 [2, -5] = true := by decide +kernel
theorem sub13_675 : sub13 [2, -4, -6] = true := by decide +kernel
theorem sub13_676 : sub13 [2, -4, -5] = true := by decide +kernel
theorem sub13_677 : sub13 [2, -4, -4] = true := by decide +kernel
theorem sub13_678 : sub13 [2, -4, -3] = true := by decide +kernel
theorem sub13_679 : sub13 [2, -4, -2] = true := by decide +kernel
theorem sub13_680 : sub13 [2, -4, -1] = true := by decide +kernel
theorem sub13_681 : sub13 [2, -4, 0] = true := by decide +kernel
theorem sub13_682 : sub13 [2, -4, 1] = true := by decide +kernel
theorem sub13_683 : sub13 [2, -4, 2] = true := by decide +kernel
theorem sub13_684 : sub13 [2, -4, 3] = true := by decide +kernel
theorem sub13_685 : sub13 [2, -4, 4] = true := by decide +kernel
theorem sub13_686 : sub13 [2, -4, 5] = true := by decide +kernel
theorem sub13_687 : sub13 [2, -4, 6] = true := by decide +kernel
theorem sub13_688 : sub13 [2, -4, 7] = true := by decide +kernel
theorem sub13_689 : sub13 [2, -3, -6] = true := by decide +kernel
theorem sub13_690 : sub13 [2, -3, -5] = true := by decide +kernel
theorem sub13_691 : sub13 [2, -3, -4] = true := by decide +kernel
theorem sub13_692 : sub13 [2, -3, -3] = true := by decide +kernel
theorem sub13_693 : sub13 [2, -3, -2] = true := by decide +kernel
theorem sub13_694 : sub13 [2, -3, -1] = true := by decide +kernel
theorem sub13_695 : sub13 [2, -3, 0] = true := by decide +kernel
theorem sub13_696 : sub13 [2, -3, 1] = true := by decide +kernel
theorem sub13_697 : sub13 [2, -3, 2] = true := by decide +kernel
theorem sub13_698 : sub13 [2, -3, 3] = true := by decide +kernel
theorem sub13_699 : sub13 [2, -3, 4] = true := by decide +kernel
theorem sub13_700 : sub13 [2, -3, 5] = true := by decide +kernel
theorem sub13_701 : sub13 [2, -3, 6] = true := by decide +kernel
theorem sub13_702 : sub13 [2, -3, 7] = true := by decide +kernel
theorem sub13_703 : sub13 [2, -2, -7] = true := by decide +kernel
theorem sb13_21 : ∀ q ∈ blk13_21, sub13 q = true := by
  unfold blk13_21
  exact List.forall_mem_cons.2 ⟨sub13_672, List.forall_mem_cons.2 ⟨sub13_673, List.forall_mem_cons.2 ⟨sub13_674, List.forall_mem_cons.2 ⟨sub13_675, List.forall_mem_cons.2 ⟨sub13_676, List.forall_mem_cons.2 ⟨sub13_677, List.forall_mem_cons.2 ⟨sub13_678, List.forall_mem_cons.2 ⟨sub13_679, List.forall_mem_cons.2 ⟨sub13_680, List.forall_mem_cons.2 ⟨sub13_681, List.forall_mem_cons.2 ⟨sub13_682, List.forall_mem_cons.2 ⟨sub13_683, List.forall_mem_cons.2 ⟨sub13_684, List.forall_mem_cons.2 ⟨sub13_685, List.forall_mem_cons.2 ⟨sub13_686, List.forall_mem_cons.2 ⟨sub13_687, List.forall_mem_cons.2 ⟨sub13_688, List.forall_mem_cons.2 ⟨sub13_689, List.forall_mem_cons.2 ⟨sub13_690, List.forall_mem_cons.2 ⟨sub13_691, List.forall_mem_cons.2 ⟨sub13_692, List.forall_mem_cons.2 ⟨sub13_693, List.forall_mem_cons.2 ⟨sub13_694, List.forall_mem_cons.2 ⟨sub13_695, List.forall_mem_cons.2 ⟨sub13_696, List.forall_mem_cons.2 ⟨sub13_697, List.forall_mem_cons.2 ⟨sub13_698, List.forall_mem_cons.2 ⟨sub13_699, List.forall_mem_cons.2 ⟨sub13_700, List.forall_mem_cons.2 ⟨sub13_701, List.forall_mem_cons.2 ⟨sub13_702, List.forall_mem_cons.2 ⟨sub13_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_704 : sub13 [2, -2, -6] = true := by decide +kernel
theorem sub13_705 : sub13 [2, -2, -5] = true := by decide +kernel
theorem sub13_706 : sub13 [2, -2, -4] = true := by decide +kernel
theorem sub13_707 : sub13 [2, -2, -3] = true := by decide +kernel
theorem sub13_708 : sub13 [2, -2, -2] = true := by decide +kernel
theorem sub13_709 : sub13 [2, -2, -1] = true := by decide +kernel
theorem sub13_710 : sub13 [2, -2, 0] = true := by decide +kernel
theorem sub13_711 : sub13 [2, -2, 1] = true := by decide +kernel
theorem sub13_712 : sub13 [2, -2, 2] = true := by decide +kernel
theorem sub13_713 : sub13 [2, -2, 3] = true := by decide +kernel
theorem sub13_714 : sub13 [2, -2, 4] = true := by decide +kernel
theorem sub13_715 : sub13 [2, -2, 5] = true := by decide +kernel
theorem sub13_716 : sub13 [2, -2, 6] = true := by decide +kernel
theorem sub13_717 : sub13 [2, -2, 7] = true := by decide +kernel
theorem sub13_718 : sub13 [2, -1, -7] = true := by decide +kernel
theorem sub13_719 : sub13 [2, -1, -6] = true := by decide +kernel
theorem sub13_720 : sub13 [2, -1, -5] = true := by decide +kernel
theorem sub13_721 : sub13 [2, -1, -4] = true := by decide +kernel
theorem sub13_722 : sub13 [2, -1, -3] = true := by decide +kernel
theorem sub13_723 : sub13 [2, -1, -2] = true := by decide +kernel
theorem sub13_724 : sub13 [2, -1, -1] = true := by decide +kernel
theorem sub13_725 : sub13 [2, -1, 0] = true := by decide +kernel
theorem sub13_726 : sub13 [2, -1, 1] = true := by decide +kernel
theorem sub13_727 : sub13 [2, -1, 2] = true := by decide +kernel
theorem sub13_728 : sub13 [2, -1, 3] = true := by decide +kernel
theorem sub13_729 : sub13 [2, -1, 4] = true := by decide +kernel
theorem sub13_730 : sub13 [2, -1, 5] = true := by decide +kernel
theorem sub13_731 : sub13 [2, -1, 6] = true := by decide +kernel
theorem sub13_732 : sub13 [2, -1, 7] = true := by decide +kernel
theorem sub13_733 : sub13 [2, 0, -7] = true := by decide +kernel
theorem sub13_734 : sub13 [2, 0, -6] = true := by decide +kernel
theorem sub13_735 : sub13 [2, 0, -5] = true := by decide +kernel
theorem sb13_22 : ∀ q ∈ blk13_22, sub13 q = true := by
  unfold blk13_22
  exact List.forall_mem_cons.2 ⟨sub13_704, List.forall_mem_cons.2 ⟨sub13_705, List.forall_mem_cons.2 ⟨sub13_706, List.forall_mem_cons.2 ⟨sub13_707, List.forall_mem_cons.2 ⟨sub13_708, List.forall_mem_cons.2 ⟨sub13_709, List.forall_mem_cons.2 ⟨sub13_710, List.forall_mem_cons.2 ⟨sub13_711, List.forall_mem_cons.2 ⟨sub13_712, List.forall_mem_cons.2 ⟨sub13_713, List.forall_mem_cons.2 ⟨sub13_714, List.forall_mem_cons.2 ⟨sub13_715, List.forall_mem_cons.2 ⟨sub13_716, List.forall_mem_cons.2 ⟨sub13_717, List.forall_mem_cons.2 ⟨sub13_718, List.forall_mem_cons.2 ⟨sub13_719, List.forall_mem_cons.2 ⟨sub13_720, List.forall_mem_cons.2 ⟨sub13_721, List.forall_mem_cons.2 ⟨sub13_722, List.forall_mem_cons.2 ⟨sub13_723, List.forall_mem_cons.2 ⟨sub13_724, List.forall_mem_cons.2 ⟨sub13_725, List.forall_mem_cons.2 ⟨sub13_726, List.forall_mem_cons.2 ⟨sub13_727, List.forall_mem_cons.2 ⟨sub13_728, List.forall_mem_cons.2 ⟨sub13_729, List.forall_mem_cons.2 ⟨sub13_730, List.forall_mem_cons.2 ⟨sub13_731, List.forall_mem_cons.2 ⟨sub13_732, List.forall_mem_cons.2 ⟨sub13_733, List.forall_mem_cons.2 ⟨sub13_734, List.forall_mem_cons.2 ⟨sub13_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_736 : sub13 [2, 0, -4] = true := by decide +kernel
theorem sub13_737 : sub13 [2, 0, -3] = true := by decide +kernel
theorem sub13_738 : sub13 [2, 0, -2] = true := by decide +kernel
theorem sub13_739 : sub13 [2, 0, -1] = true := by decide +kernel
theorem sub13_740 : sub13 [2, 0, 0] = true := by decide +kernel
theorem sub13_741 : sub13 [2, 0, 1] = true := by decide +kernel
theorem sub13_742 : sub13 [2, 0, 2] = true := by decide +kernel
theorem sub13_743 : sub13 [2, 0, 3] = true := by decide +kernel
theorem sub13_744 : sub13 [2, 0, 4] = true := by decide +kernel
theorem sub13_745 : sub13 [2, 0, 5] = true := by decide +kernel
theorem sub13_746 : sub13 [2, 0, 6] = true := by decide +kernel
theorem sub13_747 : sub13 [2, 0, 7] = true := by decide +kernel
theorem sub13_748 : sub13 [2, 1, -8] = true := by decide +kernel
theorem sub13_749 : sub13 [2, 1, -7] = true := by decide +kernel
theorem sub13_750 : sub13 [2, 1, -6] = true := by decide +kernel
theorem sub13_751 : sub13 [2, 1, -5] = true := by decide +kernel
theorem sub13_752 : sub13 [2, 1, -4] = true := by decide +kernel
theorem sub13_753 : sub13 [2, 1, -3] = true := by decide +kernel
theorem sub13_754 : sub13 [2, 1, -2] = true := by decide +kernel
theorem sub13_755 : sub13 [2, 1, -1] = true := by decide +kernel
theorem sub13_756 : sub13 [2, 1, 0] = true := by decide +kernel
theorem sub13_757 : sub13 [2, 1, 1] = true := by decide +kernel
theorem sub13_758 : sub13 [2, 1, 2] = true := by decide +kernel
theorem sub13_759 : sub13 [2, 1, 3] = true := by decide +kernel
theorem sub13_760 : sub13 [2, 1, 4] = true := by decide +kernel
theorem sub13_761 : sub13 [2, 1, 5] = true := by decide +kernel
theorem sub13_762 : sub13 [2, 1, 6] = true := by decide +kernel
theorem sub13_763 : sub13 [2, 1, 7] = true := by decide +kernel
theorem sub13_764 : sub13 [2, 2, -8] = true := by decide +kernel
theorem sub13_765 : sub13 [2, 2, -7] = true := by decide +kernel
theorem sub13_766 : sub13 [2, 2, -6] = true := by decide +kernel
theorem sub13_767 : sub13 [2, 2, -5] = true := by decide +kernel
theorem sb13_23 : ∀ q ∈ blk13_23, sub13 q = true := by
  unfold blk13_23
  exact List.forall_mem_cons.2 ⟨sub13_736, List.forall_mem_cons.2 ⟨sub13_737, List.forall_mem_cons.2 ⟨sub13_738, List.forall_mem_cons.2 ⟨sub13_739, List.forall_mem_cons.2 ⟨sub13_740, List.forall_mem_cons.2 ⟨sub13_741, List.forall_mem_cons.2 ⟨sub13_742, List.forall_mem_cons.2 ⟨sub13_743, List.forall_mem_cons.2 ⟨sub13_744, List.forall_mem_cons.2 ⟨sub13_745, List.forall_mem_cons.2 ⟨sub13_746, List.forall_mem_cons.2 ⟨sub13_747, List.forall_mem_cons.2 ⟨sub13_748, List.forall_mem_cons.2 ⟨sub13_749, List.forall_mem_cons.2 ⟨sub13_750, List.forall_mem_cons.2 ⟨sub13_751, List.forall_mem_cons.2 ⟨sub13_752, List.forall_mem_cons.2 ⟨sub13_753, List.forall_mem_cons.2 ⟨sub13_754, List.forall_mem_cons.2 ⟨sub13_755, List.forall_mem_cons.2 ⟨sub13_756, List.forall_mem_cons.2 ⟨sub13_757, List.forall_mem_cons.2 ⟨sub13_758, List.forall_mem_cons.2 ⟨sub13_759, List.forall_mem_cons.2 ⟨sub13_760, List.forall_mem_cons.2 ⟨sub13_761, List.forall_mem_cons.2 ⟨sub13_762, List.forall_mem_cons.2 ⟨sub13_763, List.forall_mem_cons.2 ⟨sub13_764, List.forall_mem_cons.2 ⟨sub13_765, List.forall_mem_cons.2 ⟨sub13_766, List.forall_mem_cons.2 ⟨sub13_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_768 : sub13 [2, 2, -4] = true := by decide +kernel
theorem sub13_769 : sub13 [2, 2, -3] = true := by decide +kernel
theorem sub13_770 : sub13 [2, 2, -2] = true := by decide +kernel
theorem sub13_771 : sub13 [2, 2, -1] = true := by decide +kernel
theorem sub13_772 : sub13 [2, 2, 0] = true := by decide +kernel
theorem sub13_773 : sub13 [2, 2, 1] = true := by decide +kernel
theorem sub13_774 : sub13 [2, 2, 2] = true := by decide +kernel
theorem sub13_775 : sub13 [2, 2, 3] = true := by decide +kernel
theorem sub13_776 : sub13 [2, 2, 4] = true := by decide +kernel
theorem sub13_777 : sub13 [2, 2, 5] = true := by decide +kernel
theorem sub13_778 : sub13 [2, 2, 6] = true := by decide +kernel
theorem sub13_779 : sub13 [2, 3, -7] = true := by decide +kernel
theorem sub13_780 : sub13 [2, 3, -6] = true := by decide +kernel
theorem sub13_781 : sub13 [2, 3, -5] = true := by decide +kernel
theorem sub13_782 : sub13 [2, 3, -4] = true := by decide +kernel
theorem sub13_783 : sub13 [2, 3, -3] = true := by decide +kernel
theorem sub13_784 : sub13 [2, 3, -2] = true := by decide +kernel
theorem sub13_785 : sub13 [2, 3, -1] = true := by decide +kernel
theorem sub13_786 : sub13 [2, 3, 0] = true := by decide +kernel
theorem sub13_787 : sub13 [2, 3, 1] = true := by decide +kernel
theorem sub13_788 : sub13 [2, 3, 2] = true := by decide +kernel
theorem sub13_789 : sub13 [2, 3, 3] = true := by decide +kernel
theorem sub13_790 : sub13 [2, 3, 4] = true := by decide +kernel
theorem sub13_791 : sub13 [2, 3, 5] = true := by decide +kernel
theorem sub13_792 : sub13 [2, 4] = true := by decide +kernel
theorem sub13_793 : sub13 [2, 5] = true := by decide +kernel
theorem sub13_794 : sub13 [2, 6] = true := by decide +kernel
theorem sub13_795 : sub13 [3, -8] = true := by decide +kernel
theorem sub13_796 : sub13 [3, -7] = true := by decide +kernel
theorem sub13_797 : sub13 [3, -6] = true := by decide +kernel
theorem sub13_798 : sub13 [3, -5] = true := by decide +kernel
theorem sub13_799 : sub13 [3, -4] = true := by decide +kernel
theorem sb13_24 : ∀ q ∈ blk13_24, sub13 q = true := by
  unfold blk13_24
  exact List.forall_mem_cons.2 ⟨sub13_768, List.forall_mem_cons.2 ⟨sub13_769, List.forall_mem_cons.2 ⟨sub13_770, List.forall_mem_cons.2 ⟨sub13_771, List.forall_mem_cons.2 ⟨sub13_772, List.forall_mem_cons.2 ⟨sub13_773, List.forall_mem_cons.2 ⟨sub13_774, List.forall_mem_cons.2 ⟨sub13_775, List.forall_mem_cons.2 ⟨sub13_776, List.forall_mem_cons.2 ⟨sub13_777, List.forall_mem_cons.2 ⟨sub13_778, List.forall_mem_cons.2 ⟨sub13_779, List.forall_mem_cons.2 ⟨sub13_780, List.forall_mem_cons.2 ⟨sub13_781, List.forall_mem_cons.2 ⟨sub13_782, List.forall_mem_cons.2 ⟨sub13_783, List.forall_mem_cons.2 ⟨sub13_784, List.forall_mem_cons.2 ⟨sub13_785, List.forall_mem_cons.2 ⟨sub13_786, List.forall_mem_cons.2 ⟨sub13_787, List.forall_mem_cons.2 ⟨sub13_788, List.forall_mem_cons.2 ⟨sub13_789, List.forall_mem_cons.2 ⟨sub13_790, List.forall_mem_cons.2 ⟨sub13_791, List.forall_mem_cons.2 ⟨sub13_792, List.forall_mem_cons.2 ⟨sub13_793, List.forall_mem_cons.2 ⟨sub13_794, List.forall_mem_cons.2 ⟨sub13_795, List.forall_mem_cons.2 ⟨sub13_796, List.forall_mem_cons.2 ⟨sub13_797, List.forall_mem_cons.2 ⟨sub13_798, List.forall_mem_cons.2 ⟨sub13_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_800 : sub13 [3, -3, -6] = true := by decide +kernel
theorem sub13_801 : sub13 [3, -3, -5] = true := by decide +kernel
theorem sub13_802 : sub13 [3, -3, -4] = true := by decide +kernel
theorem sub13_803 : sub13 [3, -3, -3] = true := by decide +kernel
theorem sub13_804 : sub13 [3, -3, -2] = true := by decide +kernel
theorem sub13_805 : sub13 [3, -3, -1] = true := by decide +kernel
theorem sub13_806 : sub13 [3, -3, 0] = true := by decide +kernel
theorem sub13_807 : sub13 [3, -3, 1] = true := by decide +kernel
theorem sub13_808 : sub13 [3, -3, 2] = true := by decide +kernel
theorem sub13_809 : sub13 [3, -3, 3] = true := by decide +kernel
theorem sub13_810 : sub13 [3, -3, 4] = true := by decide +kernel
theorem sub13_811 : sub13 [3, -3, 5] = true := by decide +kernel
theorem sub13_812 : sub13 [3, -3, 6] = true := by decide +kernel
theorem sub13_813 : sub13 [3, -3, 7] = true := by decide +kernel
theorem sub13_814 : sub13 [3, -2, -6] = true := by decide +kernel
theorem sub13_815 : sub13 [3, -2, -5] = true := by decide +kernel
theorem sub13_816 : sub13 [3, -2, -4] = true := by decide +kernel
theorem sub13_817 : sub13 [3, -2, -3] = true := by decide +kernel
theorem sub13_818 : sub13 [3, -2, -2] = true := by decide +kernel
theorem sub13_819 : sub13 [3, -2, -1] = true := by decide +kernel
theorem sub13_820 : sub13 [3, -2, 0] = true := by decide +kernel
theorem sub13_821 : sub13 [3, -2, 1] = true := by decide +kernel
theorem sub13_822 : sub13 [3, -2, 2] = true := by decide +kernel
theorem sub13_823 : sub13 [3, -2, 3] = true := by decide +kernel
theorem sub13_824 : sub13 [3, -2, 4] = true := by decide +kernel
theorem sub13_825 : sub13 [3, -2, 5] = true := by decide +kernel
theorem sub13_826 : sub13 [3, -2, 6] = true := by decide +kernel
theorem sub13_827 : sub13 [3, -2, 7] = true := by decide +kernel
theorem sub13_828 : sub13 [3, -1, -7] = true := by decide +kernel
theorem sub13_829 : sub13 [3, -1, -6] = true := by decide +kernel
theorem sub13_830 : sub13 [3, -1, -5] = true := by decide +kernel
theorem sub13_831 : sub13 [3, -1, -4] = true := by decide +kernel
theorem sb13_25 : ∀ q ∈ blk13_25, sub13 q = true := by
  unfold blk13_25
  exact List.forall_mem_cons.2 ⟨sub13_800, List.forall_mem_cons.2 ⟨sub13_801, List.forall_mem_cons.2 ⟨sub13_802, List.forall_mem_cons.2 ⟨sub13_803, List.forall_mem_cons.2 ⟨sub13_804, List.forall_mem_cons.2 ⟨sub13_805, List.forall_mem_cons.2 ⟨sub13_806, List.forall_mem_cons.2 ⟨sub13_807, List.forall_mem_cons.2 ⟨sub13_808, List.forall_mem_cons.2 ⟨sub13_809, List.forall_mem_cons.2 ⟨sub13_810, List.forall_mem_cons.2 ⟨sub13_811, List.forall_mem_cons.2 ⟨sub13_812, List.forall_mem_cons.2 ⟨sub13_813, List.forall_mem_cons.2 ⟨sub13_814, List.forall_mem_cons.2 ⟨sub13_815, List.forall_mem_cons.2 ⟨sub13_816, List.forall_mem_cons.2 ⟨sub13_817, List.forall_mem_cons.2 ⟨sub13_818, List.forall_mem_cons.2 ⟨sub13_819, List.forall_mem_cons.2 ⟨sub13_820, List.forall_mem_cons.2 ⟨sub13_821, List.forall_mem_cons.2 ⟨sub13_822, List.forall_mem_cons.2 ⟨sub13_823, List.forall_mem_cons.2 ⟨sub13_824, List.forall_mem_cons.2 ⟨sub13_825, List.forall_mem_cons.2 ⟨sub13_826, List.forall_mem_cons.2 ⟨sub13_827, List.forall_mem_cons.2 ⟨sub13_828, List.forall_mem_cons.2 ⟨sub13_829, List.forall_mem_cons.2 ⟨sub13_830, List.forall_mem_cons.2 ⟨sub13_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_832 : sub13 [3, -1, -3] = true := by decide +kernel
theorem sub13_833 : sub13 [3, -1, -2] = true := by decide +kernel
theorem sub13_834 : sub13 [3, -1, -1] = true := by decide +kernel
theorem sub13_835 : sub13 [3, -1, 0] = true := by decide +kernel
theorem sub13_836 : sub13 [3, -1, 1] = true := by decide +kernel
theorem sub13_837 : sub13 [3, -1, 2] = true := by decide +kernel
theorem sub13_838 : sub13 [3, -1, 3] = true := by decide +kernel
theorem sub13_839 : sub13 [3, -1, 4] = true := by decide +kernel
theorem sub13_840 : sub13 [3, -1, 5] = true := by decide +kernel
theorem sub13_841 : sub13 [3, -1, 6] = true := by decide +kernel
theorem sub13_842 : sub13 [3, -1, 7] = true := by decide +kernel
theorem sub13_843 : sub13 [3, 0, -7] = true := by decide +kernel
theorem sub13_844 : sub13 [3, 0, -6] = true := by decide +kernel
theorem sub13_845 : sub13 [3, 0, -5] = true := by decide +kernel
theorem sub13_846 : sub13 [3, 0, -4] = true := by decide +kernel
theorem sub13_847 : sub13 [3, 0, -3] = true := by decide +kernel
theorem sub13_848 : sub13 [3, 0, -2] = true := by decide +kernel
theorem sub13_849 : sub13 [3, 0, -1] = true := by decide +kernel
theorem sub13_850 : sub13 [3, 0, 0] = true := by decide +kernel
theorem sub13_851 : sub13 [3, 0, 1] = true := by decide +kernel
theorem sub13_852 : sub13 [3, 0, 2] = true := by decide +kernel
theorem sub13_853 : sub13 [3, 0, 3] = true := by decide +kernel
theorem sub13_854 : sub13 [3, 0, 4] = true := by decide +kernel
theorem sub13_855 : sub13 [3, 0, 5] = true := by decide +kernel
theorem sub13_856 : sub13 [3, 0, 6] = true := by decide +kernel
theorem sub13_857 : sub13 [3, 0, 7] = true := by decide +kernel
theorem sub13_858 : sub13 [3, 1, -7] = true := by decide +kernel
theorem sub13_859 : sub13 [3, 1, -6] = true := by decide +kernel
theorem sub13_860 : sub13 [3, 1, -5] = true := by decide +kernel
theorem sub13_861 : sub13 [3, 1, -4] = true := by decide +kernel
theorem sub13_862 : sub13 [3, 1, -3] = true := by decide +kernel
theorem sub13_863 : sub13 [3, 1, -2] = true := by decide +kernel
theorem sb13_26 : ∀ q ∈ blk13_26, sub13 q = true := by
  unfold blk13_26
  exact List.forall_mem_cons.2 ⟨sub13_832, List.forall_mem_cons.2 ⟨sub13_833, List.forall_mem_cons.2 ⟨sub13_834, List.forall_mem_cons.2 ⟨sub13_835, List.forall_mem_cons.2 ⟨sub13_836, List.forall_mem_cons.2 ⟨sub13_837, List.forall_mem_cons.2 ⟨sub13_838, List.forall_mem_cons.2 ⟨sub13_839, List.forall_mem_cons.2 ⟨sub13_840, List.forall_mem_cons.2 ⟨sub13_841, List.forall_mem_cons.2 ⟨sub13_842, List.forall_mem_cons.2 ⟨sub13_843, List.forall_mem_cons.2 ⟨sub13_844, List.forall_mem_cons.2 ⟨sub13_845, List.forall_mem_cons.2 ⟨sub13_846, List.forall_mem_cons.2 ⟨sub13_847, List.forall_mem_cons.2 ⟨sub13_848, List.forall_mem_cons.2 ⟨sub13_849, List.forall_mem_cons.2 ⟨sub13_850, List.forall_mem_cons.2 ⟨sub13_851, List.forall_mem_cons.2 ⟨sub13_852, List.forall_mem_cons.2 ⟨sub13_853, List.forall_mem_cons.2 ⟨sub13_854, List.forall_mem_cons.2 ⟨sub13_855, List.forall_mem_cons.2 ⟨sub13_856, List.forall_mem_cons.2 ⟨sub13_857, List.forall_mem_cons.2 ⟨sub13_858, List.forall_mem_cons.2 ⟨sub13_859, List.forall_mem_cons.2 ⟨sub13_860, List.forall_mem_cons.2 ⟨sub13_861, List.forall_mem_cons.2 ⟨sub13_862, List.forall_mem_cons.2 ⟨sub13_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_864 : sub13 [3, 1, -1] = true := by decide +kernel
theorem sub13_865 : sub13 [3, 1, 0] = true := by decide +kernel
theorem sub13_866 : sub13 [3, 1, 1] = true := by decide +kernel
theorem sub13_867 : sub13 [3, 1, 2] = true := by decide +kernel
theorem sub13_868 : sub13 [3, 1, 3] = true := by decide +kernel
theorem sub13_869 : sub13 [3, 1, 4] = true := by decide +kernel
theorem sub13_870 : sub13 [3, 1, 5] = true := by decide +kernel
theorem sub13_871 : sub13 [3, 1, 6] = true := by decide +kernel
theorem sub13_872 : sub13 [3, 2, -7] = true := by decide +kernel
theorem sub13_873 : sub13 [3, 2, -6] = true := by decide +kernel
theorem sub13_874 : sub13 [3, 2, -5] = true := by decide +kernel
theorem sub13_875 : sub13 [3, 2, -4] = true := by decide +kernel
theorem sub13_876 : sub13 [3, 2, -3] = true := by decide +kernel
theorem sub13_877 : sub13 [3, 2, -2] = true := by decide +kernel
theorem sub13_878 : sub13 [3, 2, -1] = true := by decide +kernel
theorem sub13_879 : sub13 [3, 2, 0] = true := by decide +kernel
theorem sub13_880 : sub13 [3, 2, 1] = true := by decide +kernel
theorem sub13_881 : sub13 [3, 2, 2] = true := by decide +kernel
theorem sub13_882 : sub13 [3, 2, 3] = true := by decide +kernel
theorem sub13_883 : sub13 [3, 2, 4] = true := by decide +kernel
theorem sub13_884 : sub13 [3, 2, 5] = true := by decide +kernel
theorem sub13_885 : sub13 [3, 2, 6] = true := by decide +kernel
theorem sub13_886 : sub13 [3, 3] = true := by decide +kernel
theorem sub13_887 : sub13 [3, 4] = true := by decide +kernel
theorem sub13_888 : sub13 [3, 5] = true := by decide +kernel
theorem sub13_889 : sub13 [3, 6] = true := by decide +kernel
theorem sub13_890 : sub13 [4, -8] = true := by decide +kernel
theorem sub13_891 : sub13 [4, -7] = true := by decide +kernel
theorem sub13_892 : sub13 [4, -6] = true := by decide +kernel
theorem sub13_893 : sub13 [4, -5] = true := by decide +kernel
theorem sub13_894 : sub13 [4, -4] = true := by decide +kernel
theorem sub13_895 : sub13 [4, -3] = true := by decide +kernel
theorem sb13_27 : ∀ q ∈ blk13_27, sub13 q = true := by
  unfold blk13_27
  exact List.forall_mem_cons.2 ⟨sub13_864, List.forall_mem_cons.2 ⟨sub13_865, List.forall_mem_cons.2 ⟨sub13_866, List.forall_mem_cons.2 ⟨sub13_867, List.forall_mem_cons.2 ⟨sub13_868, List.forall_mem_cons.2 ⟨sub13_869, List.forall_mem_cons.2 ⟨sub13_870, List.forall_mem_cons.2 ⟨sub13_871, List.forall_mem_cons.2 ⟨sub13_872, List.forall_mem_cons.2 ⟨sub13_873, List.forall_mem_cons.2 ⟨sub13_874, List.forall_mem_cons.2 ⟨sub13_875, List.forall_mem_cons.2 ⟨sub13_876, List.forall_mem_cons.2 ⟨sub13_877, List.forall_mem_cons.2 ⟨sub13_878, List.forall_mem_cons.2 ⟨sub13_879, List.forall_mem_cons.2 ⟨sub13_880, List.forall_mem_cons.2 ⟨sub13_881, List.forall_mem_cons.2 ⟨sub13_882, List.forall_mem_cons.2 ⟨sub13_883, List.forall_mem_cons.2 ⟨sub13_884, List.forall_mem_cons.2 ⟨sub13_885, List.forall_mem_cons.2 ⟨sub13_886, List.forall_mem_cons.2 ⟨sub13_887, List.forall_mem_cons.2 ⟨sub13_888, List.forall_mem_cons.2 ⟨sub13_889, List.forall_mem_cons.2 ⟨sub13_890, List.forall_mem_cons.2 ⟨sub13_891, List.forall_mem_cons.2 ⟨sub13_892, List.forall_mem_cons.2 ⟨sub13_893, List.forall_mem_cons.2 ⟨sub13_894, List.forall_mem_cons.2 ⟨sub13_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_896 : sub13 [4, -2] = true := by decide +kernel
theorem sub13_897 : sub13 [4, -1, -6] = true := by decide +kernel
theorem sub13_898 : sub13 [4, -1, -5] = true := by decide +kernel
theorem sub13_899 : sub13 [4, -1, -4] = true := by decide +kernel
theorem sub13_900 : sub13 [4, -1, -3] = true := by decide +kernel
theorem sub13_901 : sub13 [4, -1, -2] = true := by decide +kernel
theorem sub13_902 : sub13 [4, -1, -1] = true := by decide +kernel
theorem sub13_903 : sub13 [4, -1, 0] = true := by decide +kernel
theorem sub13_904 : sub13 [4, -1, 1] = true := by decide +kernel
theorem sub13_905 : sub13 [4, -1, 2] = true := by decide +kernel
theorem sub13_906 : sub13 [4, -1, 3] = true := by decide +kernel
theorem sub13_907 : sub13 [4, -1, 4] = true := by decide +kernel
theorem sub13_908 : sub13 [4, -1, 5] = true := by decide +kernel
theorem sub13_909 : sub13 [4, -1, 6] = true := by decide +kernel
theorem sub13_910 : sub13 [4, -1, 7] = true := by decide +kernel
theorem sub13_911 : sub13 [4, 0] = true := by decide +kernel
theorem sub13_912 : sub13 [4, 1] = true := by decide +kernel
theorem sub13_913 : sub13 [4, 2] = true := by decide +kernel
theorem sub13_914 : sub13 [4, 3] = true := by decide +kernel
theorem sub13_915 : sub13 [4, 4] = true := by decide +kernel
theorem sub13_916 : sub13 [4, 5] = true := by decide +kernel
theorem sub13_917 : sub13 [5, -7] = true := by decide +kernel
theorem sub13_918 : sub13 [5, -6] = true := by decide +kernel
theorem sub13_919 : sub13 [5, -5] = true := by decide +kernel
theorem sub13_920 : sub13 [5, -4] = true := by decide +kernel
theorem sub13_921 : sub13 [5, -3] = true := by decide +kernel
theorem sub13_922 : sub13 [5, -2] = true := by decide +kernel
theorem sub13_923 : sub13 [5, -1] = true := by decide +kernel
theorem sub13_924 : sub13 [5, 0] = true := by decide +kernel
theorem sub13_925 : sub13 [5, 1] = true := by decide +kernel
theorem sub13_926 : sub13 [5, 2] = true := by decide +kernel
theorem sub13_927 : sub13 [5, 3] = true := by decide +kernel
theorem sb13_28 : ∀ q ∈ blk13_28, sub13 q = true := by
  unfold blk13_28
  exact List.forall_mem_cons.2 ⟨sub13_896, List.forall_mem_cons.2 ⟨sub13_897, List.forall_mem_cons.2 ⟨sub13_898, List.forall_mem_cons.2 ⟨sub13_899, List.forall_mem_cons.2 ⟨sub13_900, List.forall_mem_cons.2 ⟨sub13_901, List.forall_mem_cons.2 ⟨sub13_902, List.forall_mem_cons.2 ⟨sub13_903, List.forall_mem_cons.2 ⟨sub13_904, List.forall_mem_cons.2 ⟨sub13_905, List.forall_mem_cons.2 ⟨sub13_906, List.forall_mem_cons.2 ⟨sub13_907, List.forall_mem_cons.2 ⟨sub13_908, List.forall_mem_cons.2 ⟨sub13_909, List.forall_mem_cons.2 ⟨sub13_910, List.forall_mem_cons.2 ⟨sub13_911, List.forall_mem_cons.2 ⟨sub13_912, List.forall_mem_cons.2 ⟨sub13_913, List.forall_mem_cons.2 ⟨sub13_914, List.forall_mem_cons.2 ⟨sub13_915, List.forall_mem_cons.2 ⟨sub13_916, List.forall_mem_cons.2 ⟨sub13_917, List.forall_mem_cons.2 ⟨sub13_918, List.forall_mem_cons.2 ⟨sub13_919, List.forall_mem_cons.2 ⟨sub13_920, List.forall_mem_cons.2 ⟨sub13_921, List.forall_mem_cons.2 ⟨sub13_922, List.forall_mem_cons.2 ⟨sub13_923, List.forall_mem_cons.2 ⟨sub13_924, List.forall_mem_cons.2 ⟨sub13_925, List.forall_mem_cons.2 ⟨sub13_926, List.forall_mem_cons.2 ⟨sub13_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
