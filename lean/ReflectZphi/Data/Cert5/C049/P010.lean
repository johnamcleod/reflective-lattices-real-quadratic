import ReflectZphi.Data.Cert5.C049.Base

namespace ReflectZphi.Data.Cert5.C049
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_576 : sub7 [-3, 4, 7] = true := by decide +kernel
theorem sub7_577 : sub7 [-3, 4, 8] = true := by decide +kernel
theorem sub7_578 : sub7 [-3, 4, 9] = true := by decide +kernel
theorem sub7_579 : sub7 [-3, 5] = true := by decide +kernel
theorem sub7_580 : sub7 [-3, 6] = true := by decide +kernel
theorem sub7_581 : sub7 [-2, -8] = true := by decide +kernel
theorem sub7_582 : sub7 [-2, -7] = true := by decide +kernel
theorem sub7_583 : sub7 [-2, -6] = true := by decide +kernel
theorem sub7_584 : sub7 [-2, -5, -8] = true := by decide +kernel
theorem sub7_585 : sub7 [-2, -5, -7] = true := by decide +kernel
theorem sub7_586 : sub7 [-2, -5, -6] = true := by decide +kernel
theorem sub7_587 : sub7 [-2, -5, -5] = true := by decide +kernel
theorem sub7_588 : sub7 [-2, -5, -4] = true := by decide +kernel
theorem sub7_589 : sub7 [-2, -5, -3] = true := by decide +kernel
theorem sub7_590 : sub7 [-2, -5, -2] = true := by decide +kernel
theorem sub7_591 : sub7 [-2, -5, -1] = true := by decide +kernel
theorem sub7_592 : sub7 [-2, -5, 0] = true := by decide +kernel
theorem sub7_593 : sub7 [-2, -5, 1] = true := by decide +kernel
theorem sub7_594 : sub7 [-2, -5, 2] = true := by decide +kernel
theorem sub7_595 : sub7 [-2, -5, 3] = true := by decide +kernel
theorem sub7_596 : sub7 [-2, -5, 4] = true := by decide +kernel
theorem sub7_597 : sub7 [-2, -5, 5] = true := by decide +kernel
theorem sub7_598 : sub7 [-2, -5, 6] = true := by decide +kernel
theorem sub7_599 : sub7 [-2, -5, 7] = true := by decide +kernel
theorem sub7_600 : sub7 [-2, -4, -9] = true := by decide +kernel
theorem sub7_601 : sub7 [-2, -4, -8] = true := by decide +kernel
theorem sub7_602 : sub7 [-2, -4, -7] = true := by decide +kernel
theorem sub7_603 : sub7 [-2, -4, -6] = true := by decide +kernel
theorem sub7_604 : sub7 [-2, -4, -5] = true := by decide +kernel
theorem sub7_605 : sub7 [-2, -4, -4] = true := by decide +kernel
theorem sub7_606 : sub7 [-2, -4, -3] = true := by decide +kernel
theorem sub7_607 : sub7 [-2, -4, -2] = true := by decide +kernel
theorem sb7_18 : ∀ q ∈ blk7_18, sub7 q = true := by
  unfold blk7_18
  exact List.forall_mem_cons.2 ⟨sub7_576, List.forall_mem_cons.2 ⟨sub7_577, List.forall_mem_cons.2 ⟨sub7_578, List.forall_mem_cons.2 ⟨sub7_579, List.forall_mem_cons.2 ⟨sub7_580, List.forall_mem_cons.2 ⟨sub7_581, List.forall_mem_cons.2 ⟨sub7_582, List.forall_mem_cons.2 ⟨sub7_583, List.forall_mem_cons.2 ⟨sub7_584, List.forall_mem_cons.2 ⟨sub7_585, List.forall_mem_cons.2 ⟨sub7_586, List.forall_mem_cons.2 ⟨sub7_587, List.forall_mem_cons.2 ⟨sub7_588, List.forall_mem_cons.2 ⟨sub7_589, List.forall_mem_cons.2 ⟨sub7_590, List.forall_mem_cons.2 ⟨sub7_591, List.forall_mem_cons.2 ⟨sub7_592, List.forall_mem_cons.2 ⟨sub7_593, List.forall_mem_cons.2 ⟨sub7_594, List.forall_mem_cons.2 ⟨sub7_595, List.forall_mem_cons.2 ⟨sub7_596, List.forall_mem_cons.2 ⟨sub7_597, List.forall_mem_cons.2 ⟨sub7_598, List.forall_mem_cons.2 ⟨sub7_599, List.forall_mem_cons.2 ⟨sub7_600, List.forall_mem_cons.2 ⟨sub7_601, List.forall_mem_cons.2 ⟨sub7_602, List.forall_mem_cons.2 ⟨sub7_603, List.forall_mem_cons.2 ⟨sub7_604, List.forall_mem_cons.2 ⟨sub7_605, List.forall_mem_cons.2 ⟨sub7_606, List.forall_mem_cons.2 ⟨sub7_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_608 : sub7 [-2, -4, -1] = true := by decide +kernel
theorem sub7_609 : sub7 [-2, -4, 0] = true := by decide +kernel
theorem sub7_610 : sub7 [-2, -4, 1] = true := by decide +kernel
theorem sub7_611 : sub7 [-2, -4, 2] = true := by decide +kernel
theorem sub7_612 : sub7 [-2, -4, 3] = true := by decide +kernel
theorem sub7_613 : sub7 [-2, -4, 4] = true := by decide +kernel
theorem sub7_614 : sub7 [-2, -4, 5] = true := by decide +kernel
theorem sub7_615 : sub7 [-2, -4, 6] = true := by decide +kernel
theorem sub7_616 : sub7 [-2, -4, 7] = true := by decide +kernel
theorem sub7_617 : sub7 [-2, -4, 8] = true := by decide +kernel
theorem sub7_618 : sub7 [-2, -3, -9] = true := by decide +kernel
theorem sub7_619 : sub7 [-2, -3, -8] = true := by decide +kernel
theorem sub7_620 : sub7 [-2, -3, -7] = true := by decide +kernel
theorem sub7_621 : sub7 [-2, -3, -6] = true := by decide +kernel
theorem sub7_622 : sub7 [-2, -3, -5] = true := by decide +kernel
theorem sub7_623 : sub7 [-2, -3, -4] = true := by decide +kernel
theorem sub7_624 : sub7 [-2, -3, -3] = true := by decide +kernel
theorem sub7_625 : sub7 [-2, -3, -2] = true := by decide +kernel
theorem sub7_626 : sub7 [-2, -3, -1] = true := by decide +kernel
theorem sub7_627 : sub7 [-2, -3, 0] = true := by decide +kernel
theorem sub7_628 : sub7 [-2, -3, 1] = true := by decide +kernel
theorem sub7_629 : sub7 [-2, -3, 2] = true := by decide +kernel
theorem sub7_630 : sub7 [-2, -3, 3] = true := by decide +kernel
theorem sub7_631 : sub7 [-2, -3, 4] = true := by decide +kernel
theorem sub7_632 : sub7 [-2, -3, 5] = true := by decide +kernel
theorem sub7_633 : sub7 [-2, -3, 6] = true := by decide +kernel
theorem sub7_634 : sub7 [-2, -3, 7] = true := by decide +kernel
theorem sub7_635 : sub7 [-2, -3, 8] = true := by decide +kernel
theorem sub7_636 : sub7 [-2, -3, 9] = true := by decide +kernel
theorem sub7_637 : sub7 [-2, -2, -9] = true := by decide +kernel
theorem sub7_638 : sub7 [-2, -2, -8] = true := by decide +kernel
theorem sub7_639 : sub7 [-2, -2, -7] = true := by decide +kernel
theorem sb7_19 : ∀ q ∈ blk7_19, sub7 q = true := by
  unfold blk7_19
  exact List.forall_mem_cons.2 ⟨sub7_608, List.forall_mem_cons.2 ⟨sub7_609, List.forall_mem_cons.2 ⟨sub7_610, List.forall_mem_cons.2 ⟨sub7_611, List.forall_mem_cons.2 ⟨sub7_612, List.forall_mem_cons.2 ⟨sub7_613, List.forall_mem_cons.2 ⟨sub7_614, List.forall_mem_cons.2 ⟨sub7_615, List.forall_mem_cons.2 ⟨sub7_616, List.forall_mem_cons.2 ⟨sub7_617, List.forall_mem_cons.2 ⟨sub7_618, List.forall_mem_cons.2 ⟨sub7_619, List.forall_mem_cons.2 ⟨sub7_620, List.forall_mem_cons.2 ⟨sub7_621, List.forall_mem_cons.2 ⟨sub7_622, List.forall_mem_cons.2 ⟨sub7_623, List.forall_mem_cons.2 ⟨sub7_624, List.forall_mem_cons.2 ⟨sub7_625, List.forall_mem_cons.2 ⟨sub7_626, List.forall_mem_cons.2 ⟨sub7_627, List.forall_mem_cons.2 ⟨sub7_628, List.forall_mem_cons.2 ⟨sub7_629, List.forall_mem_cons.2 ⟨sub7_630, List.forall_mem_cons.2 ⟨sub7_631, List.forall_mem_cons.2 ⟨sub7_632, List.forall_mem_cons.2 ⟨sub7_633, List.forall_mem_cons.2 ⟨sub7_634, List.forall_mem_cons.2 ⟨sub7_635, List.forall_mem_cons.2 ⟨sub7_636, List.forall_mem_cons.2 ⟨sub7_637, List.forall_mem_cons.2 ⟨sub7_638, List.forall_mem_cons.2 ⟨sub7_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_640 : sub7 [-2, -2, -6] = true := by decide +kernel
theorem sub7_641 : sub7 [-2, -2, -5] = true := by decide +kernel
theorem sub7_642 : sub7 [-2, -2, -4] = true := by decide +kernel
theorem sub7_643 : sub7 [-2, -2, -3] = true := by decide +kernel
theorem sub7_644 : sub7 [-2, -2, -2] = true := by decide +kernel
theorem sub7_645 : sub7 [-2, -2, -1] = true := by decide +kernel
theorem sub7_646 : sub7 [-2, -2, 0] = true := by decide +kernel
theorem sub7_647 : sub7 [-2, -2, 1] = true := by decide +kernel
theorem sub7_648 : sub7 [-2, -2, 2] = true := by decide +kernel
theorem sub7_649 : sub7 [-2, -2, 3] = true := by decide +kernel
theorem sub7_650 : sub7 [-2, -2, 4] = true := by decide +kernel
theorem sub7_651 : sub7 [-2, -2, 5] = true := by decide +kernel
theorem sub7_652 : sub7 [-2, -2, 6] = true := by decide +kernel
theorem sub7_653 : sub7 [-2, -2, 7] = true := by decide +kernel
theorem sub7_654 : sub7 [-2, -2, 8] = true := by decide +kernel
theorem sub7_655 : sub7 [-2, -2, 9] = true := by decide +kernel
theorem sub7_656 : sub7 [-2, -1, -9] = true := by decide +kernel
theorem sub7_657 : sub7 [-2, -1, -8] = true := by decide +kernel
theorem sub7_658 : sub7 [-2, -1, -7] = true := by decide +kernel
theorem sub7_659 : sub7 [-2, -1, -6] = true := by decide +kernel
theorem sub7_660 : sub7 [-2, -1, -5] = true := by decide +kernel
theorem sub7_661 : sub7 [-2, -1, -4] = true := by decide +kernel
theorem sub7_662 : sub7 [-2, -1, -3] = true := by decide +kernel
theorem sub7_663 : sub7 [-2, -1, -2] = true := by decide +kernel
theorem sub7_664 : sub7 [-2, -1, -1] = true := by decide +kernel
theorem sub7_665 : sub7 [-2, -1, 0] = true := by decide +kernel
theorem sub7_666 : sub7 [-2, -1, 1] = true := by decide +kernel
theorem sub7_667 : sub7 [-2, -1, 2] = true := by decide +kernel
theorem sub7_668 : sub7 [-2, -1, 3] = true := by decide +kernel
theorem sub7_669 : sub7 [-2, -1, 4] = true := by decide +kernel
theorem sub7_670 : sub7 [-2, -1, 5] = true := by decide +kernel
theorem sub7_671 : sub7 [-2, -1, 6] = true := by decide +kernel
theorem sb7_20 : ∀ q ∈ blk7_20, sub7 q = true := by
  unfold blk7_20
  exact List.forall_mem_cons.2 ⟨sub7_640, List.forall_mem_cons.2 ⟨sub7_641, List.forall_mem_cons.2 ⟨sub7_642, List.forall_mem_cons.2 ⟨sub7_643, List.forall_mem_cons.2 ⟨sub7_644, List.forall_mem_cons.2 ⟨sub7_645, List.forall_mem_cons.2 ⟨sub7_646, List.forall_mem_cons.2 ⟨sub7_647, List.forall_mem_cons.2 ⟨sub7_648, List.forall_mem_cons.2 ⟨sub7_649, List.forall_mem_cons.2 ⟨sub7_650, List.forall_mem_cons.2 ⟨sub7_651, List.forall_mem_cons.2 ⟨sub7_652, List.forall_mem_cons.2 ⟨sub7_653, List.forall_mem_cons.2 ⟨sub7_654, List.forall_mem_cons.2 ⟨sub7_655, List.forall_mem_cons.2 ⟨sub7_656, List.forall_mem_cons.2 ⟨sub7_657, List.forall_mem_cons.2 ⟨sub7_658, List.forall_mem_cons.2 ⟨sub7_659, List.forall_mem_cons.2 ⟨sub7_660, List.forall_mem_cons.2 ⟨sub7_661, List.forall_mem_cons.2 ⟨sub7_662, List.forall_mem_cons.2 ⟨sub7_663, List.forall_mem_cons.2 ⟨sub7_664, List.forall_mem_cons.2 ⟨sub7_665, List.forall_mem_cons.2 ⟨sub7_666, List.forall_mem_cons.2 ⟨sub7_667, List.forall_mem_cons.2 ⟨sub7_668, List.forall_mem_cons.2 ⟨sub7_669, List.forall_mem_cons.2 ⟨sub7_670, List.forall_mem_cons.2 ⟨sub7_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_672 : sub7 [-2, -1, 7] = true := by decide +kernel
theorem sub7_673 : sub7 [-2, -1, 8] = true := by decide +kernel
theorem sub7_674 : sub7 [-2, -1, 9] = true := by decide +kernel
theorem sub7_675 : sub7 [-2, -1, 10] = true := by decide +kernel
theorem sub7_676 : sub7 [-2, 0, -9] = true := by decide +kernel
theorem sub7_677 : sub7 [-2, 0, -8] = true := by decide +kernel
theorem sub7_678 : sub7 [-2, 0, -7] = true := by decide +kernel
theorem sub7_679 : sub7 [-2, 0, -6] = true := by decide +kernel
theorem sub7_680 : sub7 [-2, 0, -5] = true := by decide +kernel
theorem sub7_681 : sub7 [-2, 0, -4] = true := by decide +kernel
theorem sub7_682 : sub7 [-2, 0, -3] = true := by decide +kernel
theorem sub7_683 : sub7 [-2, 0, -2] = true := by decide +kernel
theorem sub7_684 : sub7 [-2, 0, -1] = true := by decide +kernel
theorem sub7_685 : sub7 [-2, 0, 0] = true := by decide +kernel
theorem sub7_686 : sub7 [-2, 0, 1] = true := by decide +kernel
theorem sub7_687 : sub7 [-2, 0, 2] = true := by decide +kernel
theorem sub7_688 : sub7 [-2, 0, 3] = true := by decide +kernel
theorem sub7_689 : sub7 [-2, 0, 4] = true := by decide +kernel
theorem sub7_690 : sub7 [-2, 0, 5] = true := by decide +kernel
theorem sub7_691 : sub7 [-2, 0, 6] = true := by decide +kernel
theorem sub7_692 : sub7 [-2, 0, 7] = true := by decide +kernel
theorem sub7_693 : sub7 [-2, 0, 8] = true := by decide +kernel
theorem sub7_694 : sub7 [-2, 0, 9] = true := by decide +kernel
theorem sub7_695 : sub7 [-2, 0, 10] = true := by decide +kernel
theorem sub7_696 : sub7 [-2, 1, -9] = true := by decide +kernel
theorem sub7_697 : sub7 [-2, 1, -8] = true := by decide +kernel
theorem sub7_698 : sub7 [-2, 1, -7] = true := by decide +kernel
theorem sub7_699 : sub7 [-2, 1, -6] = true := by decide +kernel
theorem sub7_700 : sub7 [-2, 1, -5] = true := by decide +kernel
theorem sub7_701 : sub7 [-2, 1, -4] = true := by decide +kernel
theorem sub7_702 : sub7 [-2, 1, -3] = true := by decide +kernel
theorem sub7_703 : sub7 [-2, 1, -2] = true := by decide +kernel
theorem sb7_21 : ∀ q ∈ blk7_21, sub7 q = true := by
  unfold blk7_21
  exact List.forall_mem_cons.2 ⟨sub7_672, List.forall_mem_cons.2 ⟨sub7_673, List.forall_mem_cons.2 ⟨sub7_674, List.forall_mem_cons.2 ⟨sub7_675, List.forall_mem_cons.2 ⟨sub7_676, List.forall_mem_cons.2 ⟨sub7_677, List.forall_mem_cons.2 ⟨sub7_678, List.forall_mem_cons.2 ⟨sub7_679, List.forall_mem_cons.2 ⟨sub7_680, List.forall_mem_cons.2 ⟨sub7_681, List.forall_mem_cons.2 ⟨sub7_682, List.forall_mem_cons.2 ⟨sub7_683, List.forall_mem_cons.2 ⟨sub7_684, List.forall_mem_cons.2 ⟨sub7_685, List.forall_mem_cons.2 ⟨sub7_686, List.forall_mem_cons.2 ⟨sub7_687, List.forall_mem_cons.2 ⟨sub7_688, List.forall_mem_cons.2 ⟨sub7_689, List.forall_mem_cons.2 ⟨sub7_690, List.forall_mem_cons.2 ⟨sub7_691, List.forall_mem_cons.2 ⟨sub7_692, List.forall_mem_cons.2 ⟨sub7_693, List.forall_mem_cons.2 ⟨sub7_694, List.forall_mem_cons.2 ⟨sub7_695, List.forall_mem_cons.2 ⟨sub7_696, List.forall_mem_cons.2 ⟨sub7_697, List.forall_mem_cons.2 ⟨sub7_698, List.forall_mem_cons.2 ⟨sub7_699, List.forall_mem_cons.2 ⟨sub7_700, List.forall_mem_cons.2 ⟨sub7_701, List.forall_mem_cons.2 ⟨sub7_702, List.forall_mem_cons.2 ⟨sub7_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_704 : sub7 [-2, 1, -1] = true := by decide +kernel
theorem sub7_705 : sub7 [-2, 1, 0] = true := by decide +kernel
theorem sub7_706 : sub7 [-2, 1, 1] = true := by decide +kernel
theorem sub7_707 : sub7 [-2, 1, 2] = true := by decide +kernel
theorem sub7_708 : sub7 [-2, 1, 3] = true := by decide +kernel
theorem sub7_709 : sub7 [-2, 1, 4] = true := by decide +kernel
theorem sub7_710 : sub7 [-2, 1, 5] = true := by decide +kernel
theorem sub7_711 : sub7 [-2, 1, 6] = true := by decide +kernel
theorem sub7_712 : sub7 [-2, 1, 7] = true := by decide +kernel
theorem sub7_713 : sub7 [-2, 1, 8] = true := by decide +kernel
theorem sub7_714 : sub7 [-2, 1, 9] = true := by decide +kernel
theorem sub7_715 : sub7 [-2, 1, 10] = true := by decide +kernel
theorem sub7_716 : sub7 [-2, 2, -9] = true := by decide +kernel
theorem sub7_717 : sub7 [-2, 2, -8] = true := by decide +kernel
theorem sub7_718 : sub7 [-2, 2, -7] = true := by decide +kernel
theorem sub7_719 : sub7 [-2, 2, -6] = true := by decide +kernel
theorem sub7_720 : sub7 [-2, 2, -5] = true := by decide +kernel
theorem sub7_721 : sub7 [-2, 2, -4] = true := by decide +kernel
theorem sub7_722 : sub7 [-2, 2, -3] = true := by decide +kernel
theorem sub7_723 : sub7 [-2, 2, -2] = true := by decide +kernel
theorem sub7_724 : sub7 [-2, 2, -1] = true := by decide +kernel
theorem sub7_725 : sub7 [-2, 2, 0] = true := by decide +kernel
theorem sub7_726 : sub7 [-2, 2, 1] = true := by decide +kernel
theorem sub7_727 : sub7 [-2, 2, 2] = true := by decide +kernel
theorem sub7_728 : sub7 [-2, 2, 3] = true := by decide +kernel
theorem sub7_729 : sub7 [-2, 2, 4] = true := by decide +kernel
theorem sub7_730 : sub7 [-2, 2, 5] = true := by decide +kernel
theorem sub7_731 : sub7 [-2, 2, 6] = true := by decide +kernel
theorem sub7_732 : sub7 [-2, 2, 7] = true := by decide +kernel
theorem sub7_733 : sub7 [-2, 2, 8] = true := by decide +kernel
theorem sub7_734 : sub7 [-2, 2, 9] = true := by decide +kernel
theorem sub7_735 : sub7 [-2, 2, 10] = true := by decide +kernel
theorem sb7_22 : ∀ q ∈ blk7_22, sub7 q = true := by
  unfold blk7_22
  exact List.forall_mem_cons.2 ⟨sub7_704, List.forall_mem_cons.2 ⟨sub7_705, List.forall_mem_cons.2 ⟨sub7_706, List.forall_mem_cons.2 ⟨sub7_707, List.forall_mem_cons.2 ⟨sub7_708, List.forall_mem_cons.2 ⟨sub7_709, List.forall_mem_cons.2 ⟨sub7_710, List.forall_mem_cons.2 ⟨sub7_711, List.forall_mem_cons.2 ⟨sub7_712, List.forall_mem_cons.2 ⟨sub7_713, List.forall_mem_cons.2 ⟨sub7_714, List.forall_mem_cons.2 ⟨sub7_715, List.forall_mem_cons.2 ⟨sub7_716, List.forall_mem_cons.2 ⟨sub7_717, List.forall_mem_cons.2 ⟨sub7_718, List.forall_mem_cons.2 ⟨sub7_719, List.forall_mem_cons.2 ⟨sub7_720, List.forall_mem_cons.2 ⟨sub7_721, List.forall_mem_cons.2 ⟨sub7_722, List.forall_mem_cons.2 ⟨sub7_723, List.forall_mem_cons.2 ⟨sub7_724, List.forall_mem_cons.2 ⟨sub7_725, List.forall_mem_cons.2 ⟨sub7_726, List.forall_mem_cons.2 ⟨sub7_727, List.forall_mem_cons.2 ⟨sub7_728, List.forall_mem_cons.2 ⟨sub7_729, List.forall_mem_cons.2 ⟨sub7_730, List.forall_mem_cons.2 ⟨sub7_731, List.forall_mem_cons.2 ⟨sub7_732, List.forall_mem_cons.2 ⟨sub7_733, List.forall_mem_cons.2 ⟨sub7_734, List.forall_mem_cons.2 ⟨sub7_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_736 : sub7 [-2, 3, -8] = true := by decide +kernel
theorem sub7_737 : sub7 [-2, 3, -7] = true := by decide +kernel
theorem sub7_738 : sub7 [-2, 3, -6] = true := by decide +kernel
theorem sub7_739 : sub7 [-2, 3, -5] = true := by decide +kernel
theorem sub7_740 : sub7 [-2, 3, -4] = true := by decide +kernel
theorem sub7_741 : sub7 [-2, 3, -3] = true := by decide +kernel
theorem sub7_742 : sub7 [-2, 3, -2] = true := by decide +kernel
theorem sub7_743 : sub7 [-2, 3, -1] = true := by decide +kernel
theorem sub7_744 : sub7 [-2, 3, 0] = true := by decide +kernel
theorem sub7_745 : sub7 [-2, 3, 1] = true := by decide +kernel
theorem sub7_746 : sub7 [-2, 3, 2] = true := by decide +kernel
theorem sub7_747 : sub7 [-2, 3, 3] = true := by decide +kernel
theorem sub7_748 : sub7 [-2, 3, 4] = true := by decide +kernel
theorem sub7_749 : sub7 [-2, 3, 5] = true := by decide +kernel
theorem sub7_750 : sub7 [-2, 3, 6] = true := by decide +kernel
theorem sub7_751 : sub7 [-2, 3, 7] = true := by decide +kernel
theorem sub7_752 : sub7 [-2, 3, 8] = true := by decide +kernel
theorem sub7_753 : sub7 [-2, 3, 9] = true := by decide +kernel
theorem sub7_754 : sub7 [-2, 3, 10] = true := by decide +kernel
theorem sub7_755 : sub7 [-2, 4, -7] = true := by decide +kernel
theorem sub7_756 : sub7 [-2, 4, -6] = true := by decide +kernel
theorem sub7_757 : sub7 [-2, 4, -5] = true := by decide +kernel
theorem sub7_758 : sub7 [-2, 4, -4] = true := by decide +kernel
theorem sub7_759 : sub7 [-2, 4, -3] = true := by decide +kernel
theorem sub7_760 : sub7 [-2, 4, -2] = true := by decide +kernel
theorem sub7_761 : sub7 [-2, 4, -1] = true := by decide +kernel
theorem sub7_762 : sub7 [-2, 4, 0] = true := by decide +kernel
theorem sub7_763 : sub7 [-2, 4, 1] = true := by decide +kernel
theorem sub7_764 : sub7 [-2, 4, 2] = true := by decide +kernel
theorem sub7_765 : sub7 [-2, 4, 3] = true := by decide +kernel
theorem sub7_766 : sub7 [-2, 4, 4] = true := by decide +kernel
theorem sub7_767 : sub7 [-2, 4, 5] = true := by decide +kernel
theorem sb7_23 : ∀ q ∈ blk7_23, sub7 q = true := by
  unfold blk7_23
  exact List.forall_mem_cons.2 ⟨sub7_736, List.forall_mem_cons.2 ⟨sub7_737, List.forall_mem_cons.2 ⟨sub7_738, List.forall_mem_cons.2 ⟨sub7_739, List.forall_mem_cons.2 ⟨sub7_740, List.forall_mem_cons.2 ⟨sub7_741, List.forall_mem_cons.2 ⟨sub7_742, List.forall_mem_cons.2 ⟨sub7_743, List.forall_mem_cons.2 ⟨sub7_744, List.forall_mem_cons.2 ⟨sub7_745, List.forall_mem_cons.2 ⟨sub7_746, List.forall_mem_cons.2 ⟨sub7_747, List.forall_mem_cons.2 ⟨sub7_748, List.forall_mem_cons.2 ⟨sub7_749, List.forall_mem_cons.2 ⟨sub7_750, List.forall_mem_cons.2 ⟨sub7_751, List.forall_mem_cons.2 ⟨sub7_752, List.forall_mem_cons.2 ⟨sub7_753, List.forall_mem_cons.2 ⟨sub7_754, List.forall_mem_cons.2 ⟨sub7_755, List.forall_mem_cons.2 ⟨sub7_756, List.forall_mem_cons.2 ⟨sub7_757, List.forall_mem_cons.2 ⟨sub7_758, List.forall_mem_cons.2 ⟨sub7_759, List.forall_mem_cons.2 ⟨sub7_760, List.forall_mem_cons.2 ⟨sub7_761, List.forall_mem_cons.2 ⟨sub7_762, List.forall_mem_cons.2 ⟨sub7_763, List.forall_mem_cons.2 ⟨sub7_764, List.forall_mem_cons.2 ⟨sub7_765, List.forall_mem_cons.2 ⟨sub7_766, List.forall_mem_cons.2 ⟨sub7_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_768 : sub7 [-2, 4, 6] = true := by decide +kernel
theorem sub7_769 : sub7 [-2, 4, 7] = true := by decide +kernel
theorem sub7_770 : sub7 [-2, 4, 8] = true := by decide +kernel
theorem sub7_771 : sub7 [-2, 4, 9] = true := by decide +kernel
theorem sub7_772 : sub7 [-2, 5, -6] = true := by decide +kernel
theorem sub7_773 : sub7 [-2, 5, -5] = true := by decide +kernel
theorem sub7_774 : sub7 [-2, 5, -4] = true := by decide +kernel
theorem sub7_775 : sub7 [-2, 5, -3] = true := by decide +kernel
theorem sub7_776 : sub7 [-2, 5, -2] = true := by decide +kernel
theorem sub7_777 : sub7 [-2, 5, -1] = true := by decide +kernel
theorem sub7_778 : sub7 [-2, 5, 0] = true := by decide +kernel
theorem sub7_779 : sub7 [-2, 5, 1] = true := by decide +kernel
theorem sub7_780 : sub7 [-2, 5, 2] = true := by decide +kernel
theorem sub7_781 : sub7 [-2, 5, 3] = true := by decide +kernel
theorem sub7_782 : sub7 [-2, 5, 4] = true := by decide +kernel
theorem sub7_783 : sub7 [-2, 5, 5] = true := by decide +kernel
theorem sub7_784 : sub7 [-2, 5, 6] = true := by decide +kernel
theorem sub7_785 : sub7 [-2, 5, 7] = true := by decide +kernel
theorem sub7_786 : sub7 [-2, 5, 8] = true := by decide +kernel
theorem sub7_787 : sub7 [-2, 6] = true := by decide +kernel
theorem sub7_788 : sub7 [-2, 7] = true := by decide +kernel
theorem sub7_789 : sub7 [-1, -8] = true := by decide +kernel
theorem sub7_790 : sub7 [-1, -7] = true := by decide +kernel
theorem sub7_791 : sub7 [-1, -6] = true := by decide +kernel
theorem sub7_792 : sub7 [-1, -5, -9] = true := by decide +kernel
theorem sub7_793 : sub7 [-1, -5, -8] = true := by decide +kernel
theorem sub7_794 : sub7 [-1, -5, -7] = true := by decide +kernel
theorem sub7_795 : sub7 [-1, -5, -6] = true := by decide +kernel
theorem sub7_796 : sub7 [-1, -5, -5] = true := by decide +kernel
theorem sub7_797 : sub7 [-1, -5, -4] = true := by decide +kernel
theorem sub7_798 : sub7 [-1, -5, -3] = true := by decide +kernel
theorem sub7_799 : sub7 [-1, -5, -2] = true := by decide +kernel
theorem sb7_24 : ∀ q ∈ blk7_24, sub7 q = true := by
  unfold blk7_24
  exact List.forall_mem_cons.2 ⟨sub7_768, List.forall_mem_cons.2 ⟨sub7_769, List.forall_mem_cons.2 ⟨sub7_770, List.forall_mem_cons.2 ⟨sub7_771, List.forall_mem_cons.2 ⟨sub7_772, List.forall_mem_cons.2 ⟨sub7_773, List.forall_mem_cons.2 ⟨sub7_774, List.forall_mem_cons.2 ⟨sub7_775, List.forall_mem_cons.2 ⟨sub7_776, List.forall_mem_cons.2 ⟨sub7_777, List.forall_mem_cons.2 ⟨sub7_778, List.forall_mem_cons.2 ⟨sub7_779, List.forall_mem_cons.2 ⟨sub7_780, List.forall_mem_cons.2 ⟨sub7_781, List.forall_mem_cons.2 ⟨sub7_782, List.forall_mem_cons.2 ⟨sub7_783, List.forall_mem_cons.2 ⟨sub7_784, List.forall_mem_cons.2 ⟨sub7_785, List.forall_mem_cons.2 ⟨sub7_786, List.forall_mem_cons.2 ⟨sub7_787, List.forall_mem_cons.2 ⟨sub7_788, List.forall_mem_cons.2 ⟨sub7_789, List.forall_mem_cons.2 ⟨sub7_790, List.forall_mem_cons.2 ⟨sub7_791, List.forall_mem_cons.2 ⟨sub7_792, List.forall_mem_cons.2 ⟨sub7_793, List.forall_mem_cons.2 ⟨sub7_794, List.forall_mem_cons.2 ⟨sub7_795, List.forall_mem_cons.2 ⟨sub7_796, List.forall_mem_cons.2 ⟨sub7_797, List.forall_mem_cons.2 ⟨sub7_798, List.forall_mem_cons.2 ⟨sub7_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_800 : sub7 [-1, -5, -1] = true := by decide +kernel
theorem sub7_801 : sub7 [-1, -5, 0] = true := by decide +kernel
theorem sub7_802 : sub7 [-1, -5, 1] = true := by decide +kernel
theorem sub7_803 : sub7 [-1, -5, 2] = true := by decide +kernel
theorem sub7_804 : sub7 [-1, -5, 3] = true := by decide +kernel
theorem sub7_805 : sub7 [-1, -5, 4] = true := by decide +kernel
theorem sub7_806 : sub7 [-1, -5, 5] = true := by decide +kernel
theorem sub7_807 : sub7 [-1, -5, 6] = true := by decide +kernel
theorem sub7_808 : sub7 [-1, -5, 7] = true := by decide +kernel
theorem sub7_809 : sub7 [-1, -4, -9] = true := by decide +kernel
theorem sub7_810 : sub7 [-1, -4, -8] = true := by decide +kernel
theorem sub7_811 : sub7 [-1, -4, -7] = true := by decide +kernel
theorem sub7_812 : sub7 [-1, -4, -6] = true := by decide +kernel
theorem sub7_813 : sub7 [-1, -4, -5] = true := by decide +kernel
theorem sub7_814 : sub7 [-1, -4, -4] = true := by decide +kernel
theorem sub7_815 : sub7 [-1, -4, -3] = true := by decide +kernel
theorem sub7_816 : sub7 [-1, -4, -2] = true := by decide +kernel
theorem sub7_817 : sub7 [-1, -4, -1] = true := by decide +kernel
theorem sub7_818 : sub7 [-1, -4, 0] = true := by decide +kernel
theorem sub7_819 : sub7 [-1, -4, 1] = true := by decide +kernel
theorem sub7_820 : sub7 [-1, -4, 2] = true := by decide +kernel
theorem sub7_821 : sub7 [-1, -4, 3] = true := by decide +kernel
theorem sub7_822 : sub7 [-1, -4, 4] = true := by decide +kernel
theorem sub7_823 : sub7 [-1, -4, 5] = true := by decide +kernel
theorem sub7_824 : sub7 [-1, -4, 6] = true := by decide +kernel
theorem sub7_825 : sub7 [-1, -4, 7] = true := by decide +kernel
theorem sub7_826 : sub7 [-1, -4, 8] = true := by decide +kernel
theorem sub7_827 : sub7 [-1, -3, -10] = true := by decide +kernel
theorem sub7_828 : sub7 [-1, -3, -9] = true := by decide +kernel
theorem sub7_829 : sub7 [-1, -3, -8] = true := by decide +kernel
theorem sub7_830 : sub7 [-1, -3, -7] = true := by decide +kernel
theorem sub7_831 : sub7 [-1, -3, -6] = true := by decide +kernel
theorem sb7_25 : ∀ q ∈ blk7_25, sub7 q = true := by
  unfold blk7_25
  exact List.forall_mem_cons.2 ⟨sub7_800, List.forall_mem_cons.2 ⟨sub7_801, List.forall_mem_cons.2 ⟨sub7_802, List.forall_mem_cons.2 ⟨sub7_803, List.forall_mem_cons.2 ⟨sub7_804, List.forall_mem_cons.2 ⟨sub7_805, List.forall_mem_cons.2 ⟨sub7_806, List.forall_mem_cons.2 ⟨sub7_807, List.forall_mem_cons.2 ⟨sub7_808, List.forall_mem_cons.2 ⟨sub7_809, List.forall_mem_cons.2 ⟨sub7_810, List.forall_mem_cons.2 ⟨sub7_811, List.forall_mem_cons.2 ⟨sub7_812, List.forall_mem_cons.2 ⟨sub7_813, List.forall_mem_cons.2 ⟨sub7_814, List.forall_mem_cons.2 ⟨sub7_815, List.forall_mem_cons.2 ⟨sub7_816, List.forall_mem_cons.2 ⟨sub7_817, List.forall_mem_cons.2 ⟨sub7_818, List.forall_mem_cons.2 ⟨sub7_819, List.forall_mem_cons.2 ⟨sub7_820, List.forall_mem_cons.2 ⟨sub7_821, List.forall_mem_cons.2 ⟨sub7_822, List.forall_mem_cons.2 ⟨sub7_823, List.forall_mem_cons.2 ⟨sub7_824, List.forall_mem_cons.2 ⟨sub7_825, List.forall_mem_cons.2 ⟨sub7_826, List.forall_mem_cons.2 ⟨sub7_827, List.forall_mem_cons.2 ⟨sub7_828, List.forall_mem_cons.2 ⟨sub7_829, List.forall_mem_cons.2 ⟨sub7_830, List.forall_mem_cons.2 ⟨sub7_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_832 : sub7 [-1, -3, -5] = true := by decide +kernel
theorem sub7_833 : sub7 [-1, -3, -4] = true := by decide +kernel
theorem sub7_834 : sub7 [-1, -3, -3] = true := by decide +kernel
theorem sub7_835 : sub7 [-1, -3, -2] = true := by decide +kernel
theorem sub7_836 : sub7 [-1, -3, -1] = true := by decide +kernel
theorem sub7_837 : sub7 [-1, -3, 0] = true := by decide +kernel
theorem sub7_838 : sub7 [-1, -3, 1] = true := by decide +kernel
theorem sub7_839 : sub7 [-1, -3, 2] = true := by decide +kernel
theorem sub7_840 : sub7 [-1, -3, 3] = true := by decide +kernel
theorem sub7_841 : sub7 [-1, -3, 4] = true := by decide +kernel
theorem sub7_842 : sub7 [-1, -3, 5] = true := by decide +kernel
theorem sub7_843 : sub7 [-1, -3, 6] = true := by decide +kernel
theorem sub7_844 : sub7 [-1, -3, 7] = true := by decide +kernel
theorem sub7_845 : sub7 [-1, -3, 8] = true := by decide +kernel
theorem sub7_846 : sub7 [-1, -3, 9] = true := by decide +kernel
theorem sub7_847 : sub7 [-1, -2, -10] = true := by decide +kernel
theorem sub7_848 : sub7 [-1, -2, -9] = true := by decide +kernel
theorem sub7_849 : sub7 [-1, -2, -8] = true := by decide +kernel
theorem sub7_850 : sub7 [-1, -2, -7] = true := by decide +kernel
theorem sub7_851 : sub7 [-1, -2, -6] = true := by decide +kernel
theorem sub7_852 : sub7 [-1, -2, -5] = true := by decide +kernel
theorem sub7_853 : sub7 [-1, -2, -4] = true := by decide +kernel
theorem sub7_854 : sub7 [-1, -2, -3] = true := by decide +kernel
theorem sub7_855 : sub7 [-1, -2, -2] = true := by decide +kernel
theorem sub7_856 : sub7 [-1, -2, -1] = true := by decide +kernel
theorem sub7_857 : sub7 [-1, -2, 0] = true := by decide +kernel
theorem sub7_858 : sub7 [-1, -2, 1] = true := by decide +kernel
theorem sub7_859 : sub7 [-1, -2, 2] = true := by decide +kernel
theorem sub7_860 : sub7 [-1, -2, 3] = true := by decide +kernel
theorem sub7_861 : sub7 [-1, -2, 4] = true := by decide +kernel
theorem sub7_862 : sub7 [-1, -2, 5] = true := by decide +kernel
theorem sub7_863 : sub7 [-1, -2, 6] = true := by decide +kernel
theorem sb7_26 : ∀ q ∈ blk7_26, sub7 q = true := by
  unfold blk7_26
  exact List.forall_mem_cons.2 ⟨sub7_832, List.forall_mem_cons.2 ⟨sub7_833, List.forall_mem_cons.2 ⟨sub7_834, List.forall_mem_cons.2 ⟨sub7_835, List.forall_mem_cons.2 ⟨sub7_836, List.forall_mem_cons.2 ⟨sub7_837, List.forall_mem_cons.2 ⟨sub7_838, List.forall_mem_cons.2 ⟨sub7_839, List.forall_mem_cons.2 ⟨sub7_840, List.forall_mem_cons.2 ⟨sub7_841, List.forall_mem_cons.2 ⟨sub7_842, List.forall_mem_cons.2 ⟨sub7_843, List.forall_mem_cons.2 ⟨sub7_844, List.forall_mem_cons.2 ⟨sub7_845, List.forall_mem_cons.2 ⟨sub7_846, List.forall_mem_cons.2 ⟨sub7_847, List.forall_mem_cons.2 ⟨sub7_848, List.forall_mem_cons.2 ⟨sub7_849, List.forall_mem_cons.2 ⟨sub7_850, List.forall_mem_cons.2 ⟨sub7_851, List.forall_mem_cons.2 ⟨sub7_852, List.forall_mem_cons.2 ⟨sub7_853, List.forall_mem_cons.2 ⟨sub7_854, List.forall_mem_cons.2 ⟨sub7_855, List.forall_mem_cons.2 ⟨sub7_856, List.forall_mem_cons.2 ⟨sub7_857, List.forall_mem_cons.2 ⟨sub7_858, List.forall_mem_cons.2 ⟨sub7_859, List.forall_mem_cons.2 ⟨sub7_860, List.forall_mem_cons.2 ⟨sub7_861, List.forall_mem_cons.2 ⟨sub7_862, List.forall_mem_cons.2 ⟨sub7_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_864 : sub7 [-1, -2, 7] = true := by decide +kernel
theorem sub7_865 : sub7 [-1, -2, 8] = true := by decide +kernel
theorem sub7_866 : sub7 [-1, -2, 9] = true := by decide +kernel
theorem sub7_867 : sub7 [-1, -1, -10] = true := by decide +kernel
theorem sub7_868 : sub7 [-1, -1, -9] = true := by decide +kernel
theorem sub7_869 : sub7 [-1, -1, -8] = true := by decide +kernel
theorem sub7_870 : sub7 [-1, -1, -7] = true := by decide +kernel
theorem sub7_871 : sub7 [-1, -1, -6] = true := by decide +kernel
theorem sub7_872 : sub7 [-1, -1, -5] = true := by decide +kernel
theorem sub7_873 : sub7 [-1, -1, -4] = true := by decide +kernel
theorem sub7_874 : sub7 [-1, -1, -3] = true := by decide +kernel
theorem sub7_875 : sub7 [-1, -1, -2] = true := by decide +kernel
theorem sub7_876 : sub7 [-1, -1, -1] = true := by decide +kernel
theorem sub7_877 : sub7 [-1, -1, 0] = true := by decide +kernel
theorem sub7_878 : sub7 [-1, -1, 1] = true := by decide +kernel
theorem sub7_879 : sub7 [-1, -1, 2] = true := by decide +kernel
theorem sub7_880 : sub7 [-1, -1, 3] = true := by decide +kernel
theorem sub7_881 : sub7 [-1, -1, 4] = true := by decide +kernel
theorem sub7_882 : sub7 [-1, -1, 5] = true := by decide +kernel
theorem sub7_883 : sub7 [-1, -1, 6] = true := by decide +kernel
theorem sub7_884 : sub7 [-1, -1, 7] = true := by decide +kernel
theorem sub7_885 : sub7 [-1, -1, 8] = true := by decide +kernel
theorem sub7_886 : sub7 [-1, -1, 9] = true := by decide +kernel
theorem sub7_887 : sub7 [-1, -1, 10] = true := by decide +kernel
theorem sub7_888 : sub7 [-1, 0, -10] = true := by decide +kernel
theorem sub7_889 : sub7 [-1, 0, -9] = true := by decide +kernel
theorem sub7_890 : sub7 [-1, 0, -8] = true := by decide +kernel
theorem sub7_891 : sub7 [-1, 0, -7] = true := by decide +kernel
theorem sub7_892 : sub7 [-1, 0, -6] = true := by decide +kernel
theorem sub7_893 : sub7 [-1, 0, -5] = true := by decide +kernel
theorem sub7_894 : sub7 [-1, 0, -4] = true := by decide +kernel
theorem sub7_895 : sub7 [-1, 0, -3] = true := by decide +kernel
theorem sb7_27 : ∀ q ∈ blk7_27, sub7 q = true := by
  unfold blk7_27
  exact List.forall_mem_cons.2 ⟨sub7_864, List.forall_mem_cons.2 ⟨sub7_865, List.forall_mem_cons.2 ⟨sub7_866, List.forall_mem_cons.2 ⟨sub7_867, List.forall_mem_cons.2 ⟨sub7_868, List.forall_mem_cons.2 ⟨sub7_869, List.forall_mem_cons.2 ⟨sub7_870, List.forall_mem_cons.2 ⟨sub7_871, List.forall_mem_cons.2 ⟨sub7_872, List.forall_mem_cons.2 ⟨sub7_873, List.forall_mem_cons.2 ⟨sub7_874, List.forall_mem_cons.2 ⟨sub7_875, List.forall_mem_cons.2 ⟨sub7_876, List.forall_mem_cons.2 ⟨sub7_877, List.forall_mem_cons.2 ⟨sub7_878, List.forall_mem_cons.2 ⟨sub7_879, List.forall_mem_cons.2 ⟨sub7_880, List.forall_mem_cons.2 ⟨sub7_881, List.forall_mem_cons.2 ⟨sub7_882, List.forall_mem_cons.2 ⟨sub7_883, List.forall_mem_cons.2 ⟨sub7_884, List.forall_mem_cons.2 ⟨sub7_885, List.forall_mem_cons.2 ⟨sub7_886, List.forall_mem_cons.2 ⟨sub7_887, List.forall_mem_cons.2 ⟨sub7_888, List.forall_mem_cons.2 ⟨sub7_889, List.forall_mem_cons.2 ⟨sub7_890, List.forall_mem_cons.2 ⟨sub7_891, List.forall_mem_cons.2 ⟨sub7_892, List.forall_mem_cons.2 ⟨sub7_893, List.forall_mem_cons.2 ⟨sub7_894, List.forall_mem_cons.2 ⟨sub7_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_896 : sub7 [-1, 0, -2] = true := by decide +kernel
theorem sub7_897 : sub7 [-1, 0, -1] = true := by decide +kernel
theorem sub7_898 : sub7 [-1, 0, 0] = true := by decide +kernel
theorem sub7_899 : sub7 [-1, 0, 1] = true := by decide +kernel
theorem sub7_900 : sub7 [-1, 0, 2] = true := by decide +kernel
theorem sub7_901 : sub7 [-1, 0, 3] = true := by decide +kernel
theorem sub7_902 : sub7 [-1, 0, 4] = true := by decide +kernel
theorem sub7_903 : sub7 [-1, 0, 5] = true := by decide +kernel
theorem sub7_904 : sub7 [-1, 0, 6] = true := by decide +kernel
theorem sub7_905 : sub7 [-1, 0, 7] = true := by decide +kernel
theorem sub7_906 : sub7 [-1, 0, 8] = true := by decide +kernel
theorem sub7_907 : sub7 [-1, 0, 9] = true := by decide +kernel
theorem sub7_908 : sub7 [-1, 0, 10] = true := by decide +kernel
theorem sub7_909 : sub7 [-1, 1, -10] = true := by decide +kernel
theorem sub7_910 : sub7 [-1, 1, -9] = true := by decide +kernel
theorem sub7_911 : sub7 [-1, 1, -8] = true := by decide +kernel
theorem sub7_912 : sub7 [-1, 1, -7] = true := by decide +kernel
theorem sub7_913 : sub7 [-1, 1, -6] = true := by decide +kernel
theorem sub7_914 : sub7 [-1, 1, -5] = true := by decide +kernel
theorem sub7_915 : sub7 [-1, 1, -4] = true := by decide +kernel
theorem sub7_916 : sub7 [-1, 1, -3] = true := by decide +kernel
theorem sub7_917 : sub7 [-1, 1, -2] = true := by decide +kernel
theorem sub7_918 : sub7 [-1, 1, -1] = true := by decide +kernel
theorem sub7_919 : sub7 [-1, 1, 0] = true := by decide +kernel
theorem sub7_920 : sub7 [-1, 1, 1] = true := by decide +kernel
theorem sub7_921 : sub7 [-1, 1, 2] = true := by decide +kernel
theorem sub7_922 : sub7 [-1, 1, 3] = true := by decide +kernel
theorem sub7_923 : sub7 [-1, 1, 4] = true := by decide +kernel
theorem sub7_924 : sub7 [-1, 1, 5] = true := by decide +kernel
theorem sub7_925 : sub7 [-1, 1, 6] = true := by decide +kernel
theorem sub7_926 : sub7 [-1, 1, 7] = true := by decide +kernel
theorem sub7_927 : sub7 [-1, 1, 8] = true := by decide +kernel
theorem sb7_28 : ∀ q ∈ blk7_28, sub7 q = true := by
  unfold blk7_28
  exact List.forall_mem_cons.2 ⟨sub7_896, List.forall_mem_cons.2 ⟨sub7_897, List.forall_mem_cons.2 ⟨sub7_898, List.forall_mem_cons.2 ⟨sub7_899, List.forall_mem_cons.2 ⟨sub7_900, List.forall_mem_cons.2 ⟨sub7_901, List.forall_mem_cons.2 ⟨sub7_902, List.forall_mem_cons.2 ⟨sub7_903, List.forall_mem_cons.2 ⟨sub7_904, List.forall_mem_cons.2 ⟨sub7_905, List.forall_mem_cons.2 ⟨sub7_906, List.forall_mem_cons.2 ⟨sub7_907, List.forall_mem_cons.2 ⟨sub7_908, List.forall_mem_cons.2 ⟨sub7_909, List.forall_mem_cons.2 ⟨sub7_910, List.forall_mem_cons.2 ⟨sub7_911, List.forall_mem_cons.2 ⟨sub7_912, List.forall_mem_cons.2 ⟨sub7_913, List.forall_mem_cons.2 ⟨sub7_914, List.forall_mem_cons.2 ⟨sub7_915, List.forall_mem_cons.2 ⟨sub7_916, List.forall_mem_cons.2 ⟨sub7_917, List.forall_mem_cons.2 ⟨sub7_918, List.forall_mem_cons.2 ⟨sub7_919, List.forall_mem_cons.2 ⟨sub7_920, List.forall_mem_cons.2 ⟨sub7_921, List.forall_mem_cons.2 ⟨sub7_922, List.forall_mem_cons.2 ⟨sub7_923, List.forall_mem_cons.2 ⟨sub7_924, List.forall_mem_cons.2 ⟨sub7_925, List.forall_mem_cons.2 ⟨sub7_926, List.forall_mem_cons.2 ⟨sub7_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_928 : sub7 [-1, 1, 9] = true := by decide +kernel
theorem sub7_929 : sub7 [-1, 1, 10] = true := by decide +kernel
theorem sub7_930 : sub7 [-1, 2, -9] = true := by decide +kernel
theorem sub7_931 : sub7 [-1, 2, -8] = true := by decide +kernel
theorem sub7_932 : sub7 [-1, 2, -7] = true := by decide +kernel
theorem sub7_933 : sub7 [-1, 2, -6] = true := by decide +kernel
theorem sub7_934 : sub7 [-1, 2, -5] = true := by decide +kernel
theorem sub7_935 : sub7 [-1, 2, -4] = true := by decide +kernel
theorem sub7_936 : sub7 [-1, 2, -3] = true := by decide +kernel
theorem sub7_937 : sub7 [-1, 2, -2] = true := by decide +kernel
theorem sub7_938 : sub7 [-1, 2, -1] = true := by decide +kernel
theorem sub7_939 : sub7 [-1, 2, 0] = true := by decide +kernel
theorem sub7_940 : sub7 [-1, 2, 1] = true := by decide +kernel
theorem sub7_941 : sub7 [-1, 2, 2] = true := by decide +kernel
theorem sub7_942 : sub7 [-1, 2, 3] = true := by decide +kernel
theorem sub7_943 : sub7 [-1, 2, 4] = true := by decide +kernel
theorem sub7_944 : sub7 [-1, 2, 5] = true := by decide +kernel
theorem sub7_945 : sub7 [-1, 2, 6] = true := by decide +kernel
theorem sub7_946 : sub7 [-1, 2, 7] = true := by decide +kernel
theorem sub7_947 : sub7 [-1, 2, 8] = true := by decide +kernel
theorem sub7_948 : sub7 [-1, 2, 9] = true := by decide +kernel
theorem sub7_949 : sub7 [-1, 2, 10] = true := by decide +kernel
theorem sub7_950 : sub7 [-1, 3, -9] = true := by decide +kernel
theorem sub7_951 : sub7 [-1, 3, -8] = true := by decide +kernel
theorem sub7_952 : sub7 [-1, 3, -7] = true := by decide +kernel
theorem sub7_953 : sub7 [-1, 3, -6] = true := by decide +kernel
theorem sub7_954 : sub7 [-1, 3, -5] = true := by decide +kernel
theorem sub7_955 : sub7 [-1, 3, -4] = true := by decide +kernel
theorem sub7_956 : sub7 [-1, 3, -3] = true := by decide +kernel
theorem sub7_957 : sub7 [-1, 3, -2] = true := by decide +kernel
theorem sub7_958 : sub7 [-1, 3, -1] = true := by decide +kernel
theorem sub7_959 : sub7 [-1, 3, 0] = true := by decide +kernel
theorem sb7_29 : ∀ q ∈ blk7_29, sub7 q = true := by
  unfold blk7_29
  exact List.forall_mem_cons.2 ⟨sub7_928, List.forall_mem_cons.2 ⟨sub7_929, List.forall_mem_cons.2 ⟨sub7_930, List.forall_mem_cons.2 ⟨sub7_931, List.forall_mem_cons.2 ⟨sub7_932, List.forall_mem_cons.2 ⟨sub7_933, List.forall_mem_cons.2 ⟨sub7_934, List.forall_mem_cons.2 ⟨sub7_935, List.forall_mem_cons.2 ⟨sub7_936, List.forall_mem_cons.2 ⟨sub7_937, List.forall_mem_cons.2 ⟨sub7_938, List.forall_mem_cons.2 ⟨sub7_939, List.forall_mem_cons.2 ⟨sub7_940, List.forall_mem_cons.2 ⟨sub7_941, List.forall_mem_cons.2 ⟨sub7_942, List.forall_mem_cons.2 ⟨sub7_943, List.forall_mem_cons.2 ⟨sub7_944, List.forall_mem_cons.2 ⟨sub7_945, List.forall_mem_cons.2 ⟨sub7_946, List.forall_mem_cons.2 ⟨sub7_947, List.forall_mem_cons.2 ⟨sub7_948, List.forall_mem_cons.2 ⟨sub7_949, List.forall_mem_cons.2 ⟨sub7_950, List.forall_mem_cons.2 ⟨sub7_951, List.forall_mem_cons.2 ⟨sub7_952, List.forall_mem_cons.2 ⟨sub7_953, List.forall_mem_cons.2 ⟨sub7_954, List.forall_mem_cons.2 ⟨sub7_955, List.forall_mem_cons.2 ⟨sub7_956, List.forall_mem_cons.2 ⟨sub7_957, List.forall_mem_cons.2 ⟨sub7_958, List.forall_mem_cons.2 ⟨sub7_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_960 : sub7 [-1, 3, 1] = true := by decide +kernel
theorem sub7_961 : sub7 [-1, 3, 2] = true := by decide +kernel
theorem sub7_962 : sub7 [-1, 3, 3] = true := by decide +kernel
theorem sub7_963 : sub7 [-1, 3, 4] = true := by decide +kernel
theorem sub7_964 : sub7 [-1, 3, 5] = true := by decide +kernel
theorem sub7_965 : sub7 [-1, 3, 6] = true := by decide +kernel
theorem sub7_966 : sub7 [-1, 3, 7] = true := by decide +kernel
theorem sub7_967 : sub7 [-1, 3, 8] = true := by decide +kernel
theorem sub7_968 : sub7 [-1, 3, 9] = true := by decide +kernel
theorem sub7_969 : sub7 [-1, 4, -8] = true := by decide +kernel
theorem sub7_970 : sub7 [-1, 4, -7] = true := by decide +kernel
theorem sub7_971 : sub7 [-1, 4, -6] = true := by decide +kernel
theorem sub7_972 : sub7 [-1, 4, -5] = true := by decide +kernel
theorem sub7_973 : sub7 [-1, 4, -4] = true := by decide +kernel
theorem sub7_974 : sub7 [-1, 4, -3] = true := by decide +kernel
theorem sub7_975 : sub7 [-1, 4, -2] = true := by decide +kernel
theorem sub7_976 : sub7 [-1, 4, -1] = true := by decide +kernel
theorem sub7_977 : sub7 [-1, 4, 0] = true := by decide +kernel
theorem sub7_978 : sub7 [-1, 4, 1] = true := by decide +kernel
theorem sub7_979 : sub7 [-1, 4, 2] = true := by decide +kernel
theorem sub7_980 : sub7 [-1, 4, 3] = true := by decide +kernel
theorem sub7_981 : sub7 [-1, 4, 4] = true := by decide +kernel
theorem sub7_982 : sub7 [-1, 4, 5] = true := by decide +kernel
theorem sub7_983 : sub7 [-1, 4, 6] = true := by decide +kernel
theorem sub7_984 : sub7 [-1, 4, 7] = true := by decide +kernel
theorem sub7_985 : sub7 [-1, 4, 8] = true := by decide +kernel
theorem sub7_986 : sub7 [-1, 4, 9] = true := by decide +kernel
theorem sub7_987 : sub7 [-1, 5, -7] = true := by decide +kernel
theorem sub7_988 : sub7 [-1, 5, -6] = true := by decide +kernel
theorem sub7_989 : sub7 [-1, 5, -5] = true := by decide +kernel
theorem sub7_990 : sub7 [-1, 5, -4] = true := by decide +kernel
theorem sub7_991 : sub7 [-1, 5, -3] = true := by decide +kernel
theorem sb7_30 : ∀ q ∈ blk7_30, sub7 q = true := by
  unfold blk7_30
  exact List.forall_mem_cons.2 ⟨sub7_960, List.forall_mem_cons.2 ⟨sub7_961, List.forall_mem_cons.2 ⟨sub7_962, List.forall_mem_cons.2 ⟨sub7_963, List.forall_mem_cons.2 ⟨sub7_964, List.forall_mem_cons.2 ⟨sub7_965, List.forall_mem_cons.2 ⟨sub7_966, List.forall_mem_cons.2 ⟨sub7_967, List.forall_mem_cons.2 ⟨sub7_968, List.forall_mem_cons.2 ⟨sub7_969, List.forall_mem_cons.2 ⟨sub7_970, List.forall_mem_cons.2 ⟨sub7_971, List.forall_mem_cons.2 ⟨sub7_972, List.forall_mem_cons.2 ⟨sub7_973, List.forall_mem_cons.2 ⟨sub7_974, List.forall_mem_cons.2 ⟨sub7_975, List.forall_mem_cons.2 ⟨sub7_976, List.forall_mem_cons.2 ⟨sub7_977, List.forall_mem_cons.2 ⟨sub7_978, List.forall_mem_cons.2 ⟨sub7_979, List.forall_mem_cons.2 ⟨sub7_980, List.forall_mem_cons.2 ⟨sub7_981, List.forall_mem_cons.2 ⟨sub7_982, List.forall_mem_cons.2 ⟨sub7_983, List.forall_mem_cons.2 ⟨sub7_984, List.forall_mem_cons.2 ⟨sub7_985, List.forall_mem_cons.2 ⟨sub7_986, List.forall_mem_cons.2 ⟨sub7_987, List.forall_mem_cons.2 ⟨sub7_988, List.forall_mem_cons.2 ⟨sub7_989, List.forall_mem_cons.2 ⟨sub7_990, List.forall_mem_cons.2 ⟨sub7_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_992 : sub7 [-1, 5, -2] = true := by decide +kernel
theorem sub7_993 : sub7 [-1, 5, -1] = true := by decide +kernel
theorem sub7_994 : sub7 [-1, 5, 0] = true := by decide +kernel
theorem sub7_995 : sub7 [-1, 5, 1] = true := by decide +kernel
theorem sub7_996 : sub7 [-1, 5, 2] = true := by decide +kernel
theorem sub7_997 : sub7 [-1, 5, 3] = true := by decide +kernel
theorem sub7_998 : sub7 [-1, 5, 4] = true := by decide +kernel
theorem sub7_999 : sub7 [-1, 5, 5] = true := by decide +kernel
theorem sub7_1000 : sub7 [-1, 5, 6] = true := by decide +kernel
theorem sub7_1001 : sub7 [-1, 5, 7] = true := by decide +kernel
theorem sub7_1002 : sub7 [-1, 5, 8] = true := by decide +kernel
theorem sub7_1003 : sub7 [-1, 6] = true := by decide +kernel
theorem sub7_1004 : sub7 [-1, 7] = true := by decide +kernel
theorem sub7_1005 : sub7 [0, -8] = true := by decide +kernel
theorem sub7_1006 : sub7 [0, -7] = true := by decide +kernel
theorem sub7_1007 : sub7 [0, -6] = true := by decide +kernel
theorem sub7_1008 : sub7 [0, -5, -9] = true := by decide +kernel
theorem sub7_1009 : sub7 [0, -5, -8] = true := by decide +kernel
theorem sub7_1010 : sub7 [0, -5, -7] = true := by decide +kernel
theorem sub7_1011 : sub7 [0, -5, -6] = true := by decide +kernel
theorem sub7_1012 : sub7 [0, -5, -5] = true := by decide +kernel
theorem sub7_1013 : sub7 [0, -5, -4] = true := by decide +kernel
theorem sub7_1014 : sub7 [0, -5, -3] = true := by decide +kernel
theorem sub7_1015 : sub7 [0, -5, -2] = true := by decide +kernel
theorem sub7_1016 : sub7 [0, -5, -1] = true := by decide +kernel
theorem sub7_1017 : sub7 [0, -5, 0] = true := by decide +kernel
theorem sub7_1018 : sub7 [0, -5, 1] = true := by decide +kernel
theorem sub7_1019 : sub7 [0, -5, 2] = true := by decide +kernel
theorem sub7_1020 : sub7 [0, -5, 3] = true := by decide +kernel
theorem sub7_1021 : sub7 [0, -5, 4] = true := by decide +kernel
theorem sub7_1022 : sub7 [0, -5, 5] = true := by decide +kernel
theorem sub7_1023 : sub7 [0, -5, 6] = true := by decide +kernel
theorem sb7_31 : ∀ q ∈ blk7_31, sub7 q = true := by
  unfold blk7_31
  exact List.forall_mem_cons.2 ⟨sub7_992, List.forall_mem_cons.2 ⟨sub7_993, List.forall_mem_cons.2 ⟨sub7_994, List.forall_mem_cons.2 ⟨sub7_995, List.forall_mem_cons.2 ⟨sub7_996, List.forall_mem_cons.2 ⟨sub7_997, List.forall_mem_cons.2 ⟨sub7_998, List.forall_mem_cons.2 ⟨sub7_999, List.forall_mem_cons.2 ⟨sub7_1000, List.forall_mem_cons.2 ⟨sub7_1001, List.forall_mem_cons.2 ⟨sub7_1002, List.forall_mem_cons.2 ⟨sub7_1003, List.forall_mem_cons.2 ⟨sub7_1004, List.forall_mem_cons.2 ⟨sub7_1005, List.forall_mem_cons.2 ⟨sub7_1006, List.forall_mem_cons.2 ⟨sub7_1007, List.forall_mem_cons.2 ⟨sub7_1008, List.forall_mem_cons.2 ⟨sub7_1009, List.forall_mem_cons.2 ⟨sub7_1010, List.forall_mem_cons.2 ⟨sub7_1011, List.forall_mem_cons.2 ⟨sub7_1012, List.forall_mem_cons.2 ⟨sub7_1013, List.forall_mem_cons.2 ⟨sub7_1014, List.forall_mem_cons.2 ⟨sub7_1015, List.forall_mem_cons.2 ⟨sub7_1016, List.forall_mem_cons.2 ⟨sub7_1017, List.forall_mem_cons.2 ⟨sub7_1018, List.forall_mem_cons.2 ⟨sub7_1019, List.forall_mem_cons.2 ⟨sub7_1020, List.forall_mem_cons.2 ⟨sub7_1021, List.forall_mem_cons.2 ⟨sub7_1022, List.forall_mem_cons.2 ⟨sub7_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C049
