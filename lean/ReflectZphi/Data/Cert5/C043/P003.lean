import ReflectZphi.Data.Cert5.C043.Base

namespace ReflectZphi.Data.Cert5.C043
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub1_576 : sub1 [0, 4, 4] = true := by decide +kernel
theorem sub1_577 : sub1 [0, 4, 5] = true := by decide +kernel
theorem sub1_578 : sub1 [0, 5] = true := by decide +kernel
theorem sub1_579 : sub1 [0, 6] = true := by decide +kernel
theorem sub1_580 : sub1 [1, -7] = true := by decide +kernel
theorem sub1_581 : sub1 [1, -6] = true := by decide +kernel
theorem sub1_582 : sub1 [1, -5] = true := by decide +kernel
theorem sub1_583 : sub1 [1, -4, -6] = true := by decide +kernel
theorem sub1_584 : sub1 [1, -4, -5] = true := by decide +kernel
theorem sub1_585 : sub1 [1, -4, -4] = true := by decide +kernel
theorem sub1_586 : sub1 [1, -4, -3] = true := by decide +kernel
theorem sub1_587 : sub1 [1, -4, -2] = true := by decide +kernel
theorem sub1_588 : sub1 [1, -4, -1] = true := by decide +kernel
theorem sub1_589 : sub1 [1, -4, 0] = true := by decide +kernel
theorem sub1_590 : sub1 [1, -4, 1] = true := by decide +kernel
theorem sub1_591 : sub1 [1, -4, 2] = true := by decide +kernel
theorem sub1_592 : sub1 [1, -4, 3] = true := by decide +kernel
theorem sub1_593 : sub1 [1, -4, 4] = true := by decide +kernel
theorem sub1_594 : sub1 [1, -4, 5] = true := by decide +kernel
theorem sub1_595 : sub1 [1, -4, 6] = true := by decide +kernel
theorem sub1_596 : sub1 [1, -4, 7] = true := by decide +kernel
theorem sub1_597 : sub1 [1, -3, -7] = true := by decide +kernel
theorem sub1_598 : sub1 [1, -3, -6] = true := by decide +kernel
theorem sub1_599 : sub1 [1, -3, -5] = true := by decide +kernel
theorem sub1_600 : sub1 [1, -3, -4] = true := by decide +kernel
theorem sub1_601 : sub1 [1, -3, -3] = true := by decide +kernel
theorem sub1_602 : sub1 [1, -3, -2] = true := by decide +kernel
theorem sub1_603 : sub1 [1, -3, -1] = true := by decide +kernel
theorem sub1_604 : sub1 [1, -3, 0] = true := by decide +kernel
theorem sub1_605 : sub1 [1, -3, 1] = true := by decide +kernel
theorem sub1_606 : sub1 [1, -3, 2] = true := by decide +kernel
theorem sub1_607 : sub1 [1, -3, 3] = true := by decide +kernel
theorem sb1_18 : ∀ q ∈ blk1_18, sub1 q = true := by
  unfold blk1_18
  exact List.forall_mem_cons.2 ⟨sub1_576, List.forall_mem_cons.2 ⟨sub1_577, List.forall_mem_cons.2 ⟨sub1_578, List.forall_mem_cons.2 ⟨sub1_579, List.forall_mem_cons.2 ⟨sub1_580, List.forall_mem_cons.2 ⟨sub1_581, List.forall_mem_cons.2 ⟨sub1_582, List.forall_mem_cons.2 ⟨sub1_583, List.forall_mem_cons.2 ⟨sub1_584, List.forall_mem_cons.2 ⟨sub1_585, List.forall_mem_cons.2 ⟨sub1_586, List.forall_mem_cons.2 ⟨sub1_587, List.forall_mem_cons.2 ⟨sub1_588, List.forall_mem_cons.2 ⟨sub1_589, List.forall_mem_cons.2 ⟨sub1_590, List.forall_mem_cons.2 ⟨sub1_591, List.forall_mem_cons.2 ⟨sub1_592, List.forall_mem_cons.2 ⟨sub1_593, List.forall_mem_cons.2 ⟨sub1_594, List.forall_mem_cons.2 ⟨sub1_595, List.forall_mem_cons.2 ⟨sub1_596, List.forall_mem_cons.2 ⟨sub1_597, List.forall_mem_cons.2 ⟨sub1_598, List.forall_mem_cons.2 ⟨sub1_599, List.forall_mem_cons.2 ⟨sub1_600, List.forall_mem_cons.2 ⟨sub1_601, List.forall_mem_cons.2 ⟨sub1_602, List.forall_mem_cons.2 ⟨sub1_603, List.forall_mem_cons.2 ⟨sub1_604, List.forall_mem_cons.2 ⟨sub1_605, List.forall_mem_cons.2 ⟨sub1_606, List.forall_mem_cons.2 ⟨sub1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_608 : sub1 [1, -3, 4] = true := by decide +kernel
theorem sub1_609 : sub1 [1, -3, 5] = true := by decide +kernel
theorem sub1_610 : sub1 [1, -3, 6] = true := by decide +kernel
theorem sub1_611 : sub1 [1, -3, 7] = true := by decide +kernel
theorem sub1_612 : sub1 [1, -2, -8] = true := by decide +kernel
theorem sub1_613 : sub1 [1, -2, -7] = true := by decide +kernel
theorem sub1_614 : sub1 [1, -2, -6] = true := by decide +kernel
theorem sub1_615 : sub1 [1, -2, -5] = true := by decide +kernel
theorem sub1_616 : sub1 [1, -2, -4] = true := by decide +kernel
theorem sub1_617 : sub1 [1, -2, -3] = true := by decide +kernel
theorem sub1_618 : sub1 [1, -2, -2] = true := by decide +kernel
theorem sub1_619 : sub1 [1, -2, -1] = true := by decide +kernel
theorem sub1_620 : sub1 [1, -2, 0] = true := by decide +kernel
theorem sub1_621 : sub1 [1, -2, 1] = true := by decide +kernel
theorem sub1_622 : sub1 [1, -2, 2] = true := by decide +kernel
theorem sub1_623 : sub1 [1, -2, 3] = true := by decide +kernel
theorem sub1_624 : sub1 [1, -2, 4] = true := by decide +kernel
theorem sub1_625 : sub1 [1, -2, 5] = true := by decide +kernel
theorem sub1_626 : sub1 [1, -2, 6] = true := by decide +kernel
theorem sub1_627 : sub1 [1, -2, 7] = true := by decide +kernel
theorem sub1_628 : sub1 [1, -1, -8] = true := by decide +kernel
theorem sub1_629 : sub1 [1, -1, -7] = true := by decide +kernel
theorem sub1_630 : sub1 [1, -1, -6] = true := by decide +kernel
theorem sub1_631 : sub1 [1, -1, -5] = true := by decide +kernel
theorem sub1_632 : sub1 [1, -1, -4] = true := by decide +kernel
theorem sub1_633 : sub1 [1, -1, -3] = true := by decide +kernel
theorem sub1_634 : sub1 [1, -1, -2] = true := by decide +kernel
theorem sub1_635 : sub1 [1, -1, -1] = true := by decide +kernel
theorem sub1_636 : sub1 [1, -1, 0] = true := by decide +kernel
theorem sub1_637 : sub1 [1, -1, 1] = true := by decide +kernel
theorem sub1_638 : sub1 [1, -1, 2] = true := by decide +kernel
theorem sub1_639 : sub1 [1, -1, 3] = true := by decide +kernel
theorem sb1_19 : ∀ q ∈ blk1_19, sub1 q = true := by
  unfold blk1_19
  exact List.forall_mem_cons.2 ⟨sub1_608, List.forall_mem_cons.2 ⟨sub1_609, List.forall_mem_cons.2 ⟨sub1_610, List.forall_mem_cons.2 ⟨sub1_611, List.forall_mem_cons.2 ⟨sub1_612, List.forall_mem_cons.2 ⟨sub1_613, List.forall_mem_cons.2 ⟨sub1_614, List.forall_mem_cons.2 ⟨sub1_615, List.forall_mem_cons.2 ⟨sub1_616, List.forall_mem_cons.2 ⟨sub1_617, List.forall_mem_cons.2 ⟨sub1_618, List.forall_mem_cons.2 ⟨sub1_619, List.forall_mem_cons.2 ⟨sub1_620, List.forall_mem_cons.2 ⟨sub1_621, List.forall_mem_cons.2 ⟨sub1_622, List.forall_mem_cons.2 ⟨sub1_623, List.forall_mem_cons.2 ⟨sub1_624, List.forall_mem_cons.2 ⟨sub1_625, List.forall_mem_cons.2 ⟨sub1_626, List.forall_mem_cons.2 ⟨sub1_627, List.forall_mem_cons.2 ⟨sub1_628, List.forall_mem_cons.2 ⟨sub1_629, List.forall_mem_cons.2 ⟨sub1_630, List.forall_mem_cons.2 ⟨sub1_631, List.forall_mem_cons.2 ⟨sub1_632, List.forall_mem_cons.2 ⟨sub1_633, List.forall_mem_cons.2 ⟨sub1_634, List.forall_mem_cons.2 ⟨sub1_635, List.forall_mem_cons.2 ⟨sub1_636, List.forall_mem_cons.2 ⟨sub1_637, List.forall_mem_cons.2 ⟨sub1_638, List.forall_mem_cons.2 ⟨sub1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_640 : sub1 [1, -1, 4] = true := by decide +kernel
theorem sub1_641 : sub1 [1, -1, 5] = true := by decide +kernel
theorem sub1_642 : sub1 [1, -1, 6] = true := by decide +kernel
theorem sub1_643 : sub1 [1, -1, 7] = true := by decide +kernel
theorem sub1_644 : sub1 [1, 0, -8] = true := by decide +kernel
theorem sub1_645 : sub1 [1, 0, -7] = true := by decide +kernel
theorem sub1_646 : sub1 [1, 0, -6] = true := by decide +kernel
theorem sub1_647 : sub1 [1, 0, -5] = true := by decide +kernel
theorem sub1_648 : sub1 [1, 0, -4] = true := by decide +kernel
theorem sub1_649 : sub1 [1, 0, -3] = true := by decide +kernel
theorem sub1_650 : sub1 [1, 0, -2] = true := by decide +kernel
theorem sub1_651 : sub1 [1, 0, -1] = true := by decide +kernel
theorem sub1_652 : sub1 [1, 0, 0] = true := by decide +kernel
theorem sub1_653 : sub1 [1, 0, 1] = true := by decide +kernel
theorem sub1_654 : sub1 [1, 0, 2] = true := by decide +kernel
theorem sub1_655 : sub1 [1, 0, 3] = true := by decide +kernel
theorem sub1_656 : sub1 [1, 0, 4] = true := by decide +kernel
theorem sub1_657 : sub1 [1, 0, 5] = true := by decide +kernel
theorem sub1_658 : sub1 [1, 0, 6] = true := by decide +kernel
theorem sub1_659 : sub1 [1, 0, 7] = true := by decide +kernel
theorem sub1_660 : sub1 [1, 1, -8] = true := by decide +kernel
theorem sub1_661 : sub1 [1, 1, -7] = true := by decide +kernel
theorem sub1_662 : sub1 [1, 1, -6] = true := by decide +kernel
theorem sub1_663 : sub1 [1, 1, -5] = true := by decide +kernel
theorem sub1_664 : sub1 [1, 1, -4] = true := by decide +kernel
theorem sub1_665 : sub1 [1, 1, -3] = true := by decide +kernel
theorem sub1_666 : sub1 [1, 1, -2] = true := by decide +kernel
theorem sub1_667 : sub1 [1, 1, -1] = true := by decide +kernel
theorem sub1_668 : sub1 [1, 1, 0] = true := by decide +kernel
theorem sub1_669 : sub1 [1, 1, 1] = true := by decide +kernel
theorem sub1_670 : sub1 [1, 1, 2] = true := by decide +kernel
theorem sub1_671 : sub1 [1, 1, 3] = true := by decide +kernel
theorem sb1_20 : ∀ q ∈ blk1_20, sub1 q = true := by
  unfold blk1_20
  exact List.forall_mem_cons.2 ⟨sub1_640, List.forall_mem_cons.2 ⟨sub1_641, List.forall_mem_cons.2 ⟨sub1_642, List.forall_mem_cons.2 ⟨sub1_643, List.forall_mem_cons.2 ⟨sub1_644, List.forall_mem_cons.2 ⟨sub1_645, List.forall_mem_cons.2 ⟨sub1_646, List.forall_mem_cons.2 ⟨sub1_647, List.forall_mem_cons.2 ⟨sub1_648, List.forall_mem_cons.2 ⟨sub1_649, List.forall_mem_cons.2 ⟨sub1_650, List.forall_mem_cons.2 ⟨sub1_651, List.forall_mem_cons.2 ⟨sub1_652, List.forall_mem_cons.2 ⟨sub1_653, List.forall_mem_cons.2 ⟨sub1_654, List.forall_mem_cons.2 ⟨sub1_655, List.forall_mem_cons.2 ⟨sub1_656, List.forall_mem_cons.2 ⟨sub1_657, List.forall_mem_cons.2 ⟨sub1_658, List.forall_mem_cons.2 ⟨sub1_659, List.forall_mem_cons.2 ⟨sub1_660, List.forall_mem_cons.2 ⟨sub1_661, List.forall_mem_cons.2 ⟨sub1_662, List.forall_mem_cons.2 ⟨sub1_663, List.forall_mem_cons.2 ⟨sub1_664, List.forall_mem_cons.2 ⟨sub1_665, List.forall_mem_cons.2 ⟨sub1_666, List.forall_mem_cons.2 ⟨sub1_667, List.forall_mem_cons.2 ⟨sub1_668, List.forall_mem_cons.2 ⟨sub1_669, List.forall_mem_cons.2 ⟨sub1_670, List.forall_mem_cons.2 ⟨sub1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_672 : sub1 [1, 1, 4] = true := by decide +kernel
theorem sub1_673 : sub1 [1, 1, 5] = true := by decide +kernel
theorem sub1_674 : sub1 [1, 1, 6] = true := by decide +kernel
theorem sub1_675 : sub1 [1, 1, 7] = true := by decide +kernel
theorem sub1_676 : sub1 [1, 2, -8] = true := by decide +kernel
theorem sub1_677 : sub1 [1, 2, -7] = true := by decide +kernel
theorem sub1_678 : sub1 [1, 2, -6] = true := by decide +kernel
theorem sub1_679 : sub1 [1, 2, -5] = true := by decide +kernel
theorem sub1_680 : sub1 [1, 2, -4] = true := by decide +kernel
theorem sub1_681 : sub1 [1, 2, -3] = true := by decide +kernel
theorem sub1_682 : sub1 [1, 2, -2] = true := by decide +kernel
theorem sub1_683 : sub1 [1, 2, -1] = true := by decide +kernel
theorem sub1_684 : sub1 [1, 2, 0] = true := by decide +kernel
theorem sub1_685 : sub1 [1, 2, 1] = true := by decide +kernel
theorem sub1_686 : sub1 [1, 2, 2] = true := by decide +kernel
theorem sub1_687 : sub1 [1, 2, 3] = true := by decide +kernel
theorem sub1_688 : sub1 [1, 2, 4] = true := by decide +kernel
theorem sub1_689 : sub1 [1, 2, 5] = true := by decide +kernel
theorem sub1_690 : sub1 [1, 2, 6] = true := by decide +kernel
theorem sub1_691 : sub1 [1, 2, 7] = true := by decide +kernel
theorem sub1_692 : sub1 [1, 3, -8] = true := by decide +kernel
theorem sub1_693 : sub1 [1, 3, -7] = true := by decide +kernel
theorem sub1_694 : sub1 [1, 3, -6] = true := by decide +kernel
theorem sub1_695 : sub1 [1, 3, -5] = true := by decide +kernel
theorem sub1_696 : sub1 [1, 3, -4] = true := by decide +kernel
theorem sub1_697 : sub1 [1, 3, -3] = true := by decide +kernel
theorem sub1_698 : sub1 [1, 3, -2] = true := by decide +kernel
theorem sub1_699 : sub1 [1, 3, -1] = true := by decide +kernel
theorem sub1_700 : sub1 [1, 3, 0] = true := by decide +kernel
theorem sub1_701 : sub1 [1, 3, 1] = true := by decide +kernel
theorem sub1_702 : sub1 [1, 3, 2] = true := by decide +kernel
theorem sub1_703 : sub1 [1, 3, 3] = true := by decide +kernel
theorem sb1_21 : ∀ q ∈ blk1_21, sub1 q = true := by
  unfold blk1_21
  exact List.forall_mem_cons.2 ⟨sub1_672, List.forall_mem_cons.2 ⟨sub1_673, List.forall_mem_cons.2 ⟨sub1_674, List.forall_mem_cons.2 ⟨sub1_675, List.forall_mem_cons.2 ⟨sub1_676, List.forall_mem_cons.2 ⟨sub1_677, List.forall_mem_cons.2 ⟨sub1_678, List.forall_mem_cons.2 ⟨sub1_679, List.forall_mem_cons.2 ⟨sub1_680, List.forall_mem_cons.2 ⟨sub1_681, List.forall_mem_cons.2 ⟨sub1_682, List.forall_mem_cons.2 ⟨sub1_683, List.forall_mem_cons.2 ⟨sub1_684, List.forall_mem_cons.2 ⟨sub1_685, List.forall_mem_cons.2 ⟨sub1_686, List.forall_mem_cons.2 ⟨sub1_687, List.forall_mem_cons.2 ⟨sub1_688, List.forall_mem_cons.2 ⟨sub1_689, List.forall_mem_cons.2 ⟨sub1_690, List.forall_mem_cons.2 ⟨sub1_691, List.forall_mem_cons.2 ⟨sub1_692, List.forall_mem_cons.2 ⟨sub1_693, List.forall_mem_cons.2 ⟨sub1_694, List.forall_mem_cons.2 ⟨sub1_695, List.forall_mem_cons.2 ⟨sub1_696, List.forall_mem_cons.2 ⟨sub1_697, List.forall_mem_cons.2 ⟨sub1_698, List.forall_mem_cons.2 ⟨sub1_699, List.forall_mem_cons.2 ⟨sub1_700, List.forall_mem_cons.2 ⟨sub1_701, List.forall_mem_cons.2 ⟨sub1_702, List.forall_mem_cons.2 ⟨sub1_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_704 : sub1 [1, 3, 4] = true := by decide +kernel
theorem sub1_705 : sub1 [1, 3, 5] = true := by decide +kernel
theorem sub1_706 : sub1 [1, 3, 6] = true := by decide +kernel
theorem sub1_707 : sub1 [1, 4] = true := by decide +kernel
theorem sub1_708 : sub1 [1, 5] = true := by decide +kernel
theorem sub1_709 : sub1 [1, 6] = true := by decide +kernel
theorem sub1_710 : sub1 [2, -7] = true := by decide +kernel
theorem sub1_711 : sub1 [2, -6] = true := by decide +kernel
theorem sub1_712 : sub1 [2, -5] = true := by decide +kernel
theorem sub1_713 : sub1 [2, -4, -6] = true := by decide +kernel
theorem sub1_714 : sub1 [2, -4, -5] = true := by decide +kernel
theorem sub1_715 : sub1 [2, -4, -4] = true := by decide +kernel
theorem sub1_716 : sub1 [2, -4, -3] = true := by decide +kernel
theorem sub1_717 : sub1 [2, -4, -2] = true := by decide +kernel
theorem sub1_718 : sub1 [2, -4, -1] = true := by decide +kernel
theorem sub1_719 : sub1 [2, -4, 0] = true := by decide +kernel
theorem sub1_720 : sub1 [2, -4, 1] = true := by decide +kernel
theorem sub1_721 : sub1 [2, -4, 2] = true := by decide +kernel
theorem sub1_722 : sub1 [2, -4, 3] = true := by decide +kernel
theorem sub1_723 : sub1 [2, -4, 4] = true := by decide +kernel
theorem sub1_724 : sub1 [2, -4, 5] = true := by decide +kernel
theorem sub1_725 : sub1 [2, -4, 6] = true := by decide +kernel
theorem sub1_726 : sub1 [2, -3, -7] = true := by decide +kernel
theorem sub1_727 : sub1 [2, -3, -6] = true := by decide +kernel
theorem sub1_728 : sub1 [2, -3, -5] = true := by decide +kernel
theorem sub1_729 : sub1 [2, -3, -4] = true := by decide +kernel
theorem sub1_730 : sub1 [2, -3, -3] = true := by decide +kernel
theorem sub1_731 : sub1 [2, -3, -2] = true := by decide +kernel
theorem sub1_732 : sub1 [2, -3, -1] = true := by decide +kernel
theorem sub1_733 : sub1 [2, -3, 0] = true := by decide +kernel
theorem sub1_734 : sub1 [2, -3, 1] = true := by decide +kernel
theorem sub1_735 : sub1 [2, -3, 2] = true := by decide +kernel
theorem sb1_22 : ∀ q ∈ blk1_22, sub1 q = true := by
  unfold blk1_22
  exact List.forall_mem_cons.2 ⟨sub1_704, List.forall_mem_cons.2 ⟨sub1_705, List.forall_mem_cons.2 ⟨sub1_706, List.forall_mem_cons.2 ⟨sub1_707, List.forall_mem_cons.2 ⟨sub1_708, List.forall_mem_cons.2 ⟨sub1_709, List.forall_mem_cons.2 ⟨sub1_710, List.forall_mem_cons.2 ⟨sub1_711, List.forall_mem_cons.2 ⟨sub1_712, List.forall_mem_cons.2 ⟨sub1_713, List.forall_mem_cons.2 ⟨sub1_714, List.forall_mem_cons.2 ⟨sub1_715, List.forall_mem_cons.2 ⟨sub1_716, List.forall_mem_cons.2 ⟨sub1_717, List.forall_mem_cons.2 ⟨sub1_718, List.forall_mem_cons.2 ⟨sub1_719, List.forall_mem_cons.2 ⟨sub1_720, List.forall_mem_cons.2 ⟨sub1_721, List.forall_mem_cons.2 ⟨sub1_722, List.forall_mem_cons.2 ⟨sub1_723, List.forall_mem_cons.2 ⟨sub1_724, List.forall_mem_cons.2 ⟨sub1_725, List.forall_mem_cons.2 ⟨sub1_726, List.forall_mem_cons.2 ⟨sub1_727, List.forall_mem_cons.2 ⟨sub1_728, List.forall_mem_cons.2 ⟨sub1_729, List.forall_mem_cons.2 ⟨sub1_730, List.forall_mem_cons.2 ⟨sub1_731, List.forall_mem_cons.2 ⟨sub1_732, List.forall_mem_cons.2 ⟨sub1_733, List.forall_mem_cons.2 ⟨sub1_734, List.forall_mem_cons.2 ⟨sub1_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_736 : sub1 [2, -3, 3] = true := by decide +kernel
theorem sub1_737 : sub1 [2, -3, 4] = true := by decide +kernel
theorem sub1_738 : sub1 [2, -3, 5] = true := by decide +kernel
theorem sub1_739 : sub1 [2, -3, 6] = true := by decide +kernel
theorem sub1_740 : sub1 [2, -3, 7] = true := by decide +kernel
theorem sub1_741 : sub1 [2, -2, -7] = true := by decide +kernel
theorem sub1_742 : sub1 [2, -2, -6] = true := by decide +kernel
theorem sub1_743 : sub1 [2, -2, -5] = true := by decide +kernel
theorem sub1_744 : sub1 [2, -2, -4] = true := by decide +kernel
theorem sub1_745 : sub1 [2, -2, -3] = true := by decide +kernel
theorem sub1_746 : sub1 [2, -2, -2] = true := by decide +kernel
theorem sub1_747 : sub1 [2, -2, -1] = true := by decide +kernel
theorem sub1_748 : sub1 [2, -2, 0] = true := by decide +kernel
theorem sub1_749 : sub1 [2, -2, 1] = true := by decide +kernel
theorem sub1_750 : sub1 [2, -2, 2] = true := by decide +kernel
theorem sub1_751 : sub1 [2, -2, 3] = true := by decide +kernel
theorem sub1_752 : sub1 [2, -2, 4] = true := by decide +kernel
theorem sub1_753 : sub1 [2, -2, 5] = true := by decide +kernel
theorem sub1_754 : sub1 [2, -2, 6] = true := by decide +kernel
theorem sub1_755 : sub1 [2, -2, 7] = true := by decide +kernel
theorem sub1_756 : sub1 [2, -1, -8] = true := by decide +kernel
theorem sub1_757 : sub1 [2, -1, -7] = true := by decide +kernel
theorem sub1_758 : sub1 [2, -1, -6] = true := by decide +kernel
theorem sub1_759 : sub1 [2, -1, -5] = true := by decide +kernel
theorem sub1_760 : sub1 [2, -1, -4] = true := by decide +kernel
theorem sub1_761 : sub1 [2, -1, -3] = true := by decide +kernel
theorem sub1_762 : sub1 [2, -1, -2] = true := by decide +kernel
theorem sub1_763 : sub1 [2, -1, -1] = true := by decide +kernel
theorem sub1_764 : sub1 [2, -1, 0] = true := by decide +kernel
theorem sub1_765 : sub1 [2, -1, 1] = true := by decide +kernel
theorem sub1_766 : sub1 [2, -1, 2] = true := by decide +kernel
theorem sub1_767 : sub1 [2, -1, 3] = true := by decide +kernel
theorem sb1_23 : ∀ q ∈ blk1_23, sub1 q = true := by
  unfold blk1_23
  exact List.forall_mem_cons.2 ⟨sub1_736, List.forall_mem_cons.2 ⟨sub1_737, List.forall_mem_cons.2 ⟨sub1_738, List.forall_mem_cons.2 ⟨sub1_739, List.forall_mem_cons.2 ⟨sub1_740, List.forall_mem_cons.2 ⟨sub1_741, List.forall_mem_cons.2 ⟨sub1_742, List.forall_mem_cons.2 ⟨sub1_743, List.forall_mem_cons.2 ⟨sub1_744, List.forall_mem_cons.2 ⟨sub1_745, List.forall_mem_cons.2 ⟨sub1_746, List.forall_mem_cons.2 ⟨sub1_747, List.forall_mem_cons.2 ⟨sub1_748, List.forall_mem_cons.2 ⟨sub1_749, List.forall_mem_cons.2 ⟨sub1_750, List.forall_mem_cons.2 ⟨sub1_751, List.forall_mem_cons.2 ⟨sub1_752, List.forall_mem_cons.2 ⟨sub1_753, List.forall_mem_cons.2 ⟨sub1_754, List.forall_mem_cons.2 ⟨sub1_755, List.forall_mem_cons.2 ⟨sub1_756, List.forall_mem_cons.2 ⟨sub1_757, List.forall_mem_cons.2 ⟨sub1_758, List.forall_mem_cons.2 ⟨sub1_759, List.forall_mem_cons.2 ⟨sub1_760, List.forall_mem_cons.2 ⟨sub1_761, List.forall_mem_cons.2 ⟨sub1_762, List.forall_mem_cons.2 ⟨sub1_763, List.forall_mem_cons.2 ⟨sub1_764, List.forall_mem_cons.2 ⟨sub1_765, List.forall_mem_cons.2 ⟨sub1_766, List.forall_mem_cons.2 ⟨sub1_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_768 : sub1 [2, -1, 4] = true := by decide +kernel
theorem sub1_769 : sub1 [2, -1, 5] = true := by decide +kernel
theorem sub1_770 : sub1 [2, -1, 6] = true := by decide +kernel
theorem sub1_771 : sub1 [2, -1, 7] = true := by decide +kernel
theorem sub1_772 : sub1 [2, 0, -8] = true := by decide +kernel
theorem sub1_773 : sub1 [2, 0, -7] = true := by decide +kernel
theorem sub1_774 : sub1 [2, 0, -6] = true := by decide +kernel
theorem sub1_775 : sub1 [2, 0, -5] = true := by decide +kernel
theorem sub1_776 : sub1 [2, 0, -4] = true := by decide +kernel
theorem sub1_777 : sub1 [2, 0, -3] = true := by decide +kernel
theorem sub1_778 : sub1 [2, 0, -2] = true := by decide +kernel
theorem sub1_779 : sub1 [2, 0, -1] = true := by decide +kernel
theorem sub1_780 : sub1 [2, 0, 0] = true := by decide +kernel
theorem sub1_781 : sub1 [2, 0, 1] = true := by decide +kernel
theorem sub1_782 : sub1 [2, 0, 2] = true := by decide +kernel
theorem sub1_783 : sub1 [2, 0, 3] = true := by decide +kernel
theorem sub1_784 : sub1 [2, 0, 4] = true := by decide +kernel
theorem sub1_785 : sub1 [2, 0, 5] = true := by decide +kernel
theorem sub1_786 : sub1 [2, 0, 6] = true := by decide +kernel
theorem sub1_787 : sub1 [2, 0, 7] = true := by decide +kernel
theorem sub1_788 : sub1 [2, 1, -8] = true := by decide +kernel
theorem sub1_789 : sub1 [2, 1, -7] = true := by decide +kernel
theorem sub1_790 : sub1 [2, 1, -6] = true := by decide +kernel
theorem sub1_791 : sub1 [2, 1, -5] = true := by decide +kernel
theorem sub1_792 : sub1 [2, 1, -4] = true := by decide +kernel
theorem sub1_793 : sub1 [2, 1, -3] = true := by decide +kernel
theorem sub1_794 : sub1 [2, 1, -2] = true := by decide +kernel
theorem sub1_795 : sub1 [2, 1, -1] = true := by decide +kernel
theorem sub1_796 : sub1 [2, 1, 0] = true := by decide +kernel
theorem sub1_797 : sub1 [2, 1, 1] = true := by decide +kernel
theorem sub1_798 : sub1 [2, 1, 2] = true := by decide +kernel
theorem sub1_799 : sub1 [2, 1, 3] = true := by decide +kernel
theorem sb1_24 : ∀ q ∈ blk1_24, sub1 q = true := by
  unfold blk1_24
  exact List.forall_mem_cons.2 ⟨sub1_768, List.forall_mem_cons.2 ⟨sub1_769, List.forall_mem_cons.2 ⟨sub1_770, List.forall_mem_cons.2 ⟨sub1_771, List.forall_mem_cons.2 ⟨sub1_772, List.forall_mem_cons.2 ⟨sub1_773, List.forall_mem_cons.2 ⟨sub1_774, List.forall_mem_cons.2 ⟨sub1_775, List.forall_mem_cons.2 ⟨sub1_776, List.forall_mem_cons.2 ⟨sub1_777, List.forall_mem_cons.2 ⟨sub1_778, List.forall_mem_cons.2 ⟨sub1_779, List.forall_mem_cons.2 ⟨sub1_780, List.forall_mem_cons.2 ⟨sub1_781, List.forall_mem_cons.2 ⟨sub1_782, List.forall_mem_cons.2 ⟨sub1_783, List.forall_mem_cons.2 ⟨sub1_784, List.forall_mem_cons.2 ⟨sub1_785, List.forall_mem_cons.2 ⟨sub1_786, List.forall_mem_cons.2 ⟨sub1_787, List.forall_mem_cons.2 ⟨sub1_788, List.forall_mem_cons.2 ⟨sub1_789, List.forall_mem_cons.2 ⟨sub1_790, List.forall_mem_cons.2 ⟨sub1_791, List.forall_mem_cons.2 ⟨sub1_792, List.forall_mem_cons.2 ⟨sub1_793, List.forall_mem_cons.2 ⟨sub1_794, List.forall_mem_cons.2 ⟨sub1_795, List.forall_mem_cons.2 ⟨sub1_796, List.forall_mem_cons.2 ⟨sub1_797, List.forall_mem_cons.2 ⟨sub1_798, List.forall_mem_cons.2 ⟨sub1_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_800 : sub1 [2, 1, 4] = true := by decide +kernel
theorem sub1_801 : sub1 [2, 1, 5] = true := by decide +kernel
theorem sub1_802 : sub1 [2, 1, 6] = true := by decide +kernel
theorem sub1_803 : sub1 [2, 1, 7] = true := by decide +kernel
theorem sub1_804 : sub1 [2, 2, -8] = true := by decide +kernel
theorem sub1_805 : sub1 [2, 2, -7] = true := by decide +kernel
theorem sub1_806 : sub1 [2, 2, -6] = true := by decide +kernel
theorem sub1_807 : sub1 [2, 2, -5] = true := by decide +kernel
theorem sub1_808 : sub1 [2, 2, -4] = true := by decide +kernel
theorem sub1_809 : sub1 [2, 2, -3] = true := by decide +kernel
theorem sub1_810 : sub1 [2, 2, -2] = true := by decide +kernel
theorem sub1_811 : sub1 [2, 2, -1] = true := by decide +kernel
theorem sub1_812 : sub1 [2, 2, 0] = true := by decide +kernel
theorem sub1_813 : sub1 [2, 2, 1] = true := by decide +kernel
theorem sub1_814 : sub1 [2, 2, 2] = true := by decide +kernel
theorem sub1_815 : sub1 [2, 2, 3] = true := by decide +kernel
theorem sub1_816 : sub1 [2, 2, 4] = true := by decide +kernel
theorem sub1_817 : sub1 [2, 2, 5] = true := by decide +kernel
theorem sub1_818 : sub1 [2, 2, 6] = true := by decide +kernel
theorem sub1_819 : sub1 [2, 2, 7] = true := by decide +kernel
theorem sub1_820 : sub1 [2, 3, -7] = true := by decide +kernel
theorem sub1_821 : sub1 [2, 3, -6] = true := by decide +kernel
theorem sub1_822 : sub1 [2, 3, -5] = true := by decide +kernel
theorem sub1_823 : sub1 [2, 3, -4] = true := by decide +kernel
theorem sub1_824 : sub1 [2, 3, -3] = true := by decide +kernel
theorem sub1_825 : sub1 [2, 3, -2] = true := by decide +kernel
theorem sub1_826 : sub1 [2, 3, -1] = true := by decide +kernel
theorem sub1_827 : sub1 [2, 3, 0] = true := by decide +kernel
theorem sub1_828 : sub1 [2, 3, 1] = true := by decide +kernel
theorem sub1_829 : sub1 [2, 3, 2] = true := by decide +kernel
theorem sub1_830 : sub1 [2, 3, 3] = true := by decide +kernel
theorem sub1_831 : sub1 [2, 3, 4] = true := by decide +kernel
theorem sb1_25 : ∀ q ∈ blk1_25, sub1 q = true := by
  unfold blk1_25
  exact List.forall_mem_cons.2 ⟨sub1_800, List.forall_mem_cons.2 ⟨sub1_801, List.forall_mem_cons.2 ⟨sub1_802, List.forall_mem_cons.2 ⟨sub1_803, List.forall_mem_cons.2 ⟨sub1_804, List.forall_mem_cons.2 ⟨sub1_805, List.forall_mem_cons.2 ⟨sub1_806, List.forall_mem_cons.2 ⟨sub1_807, List.forall_mem_cons.2 ⟨sub1_808, List.forall_mem_cons.2 ⟨sub1_809, List.forall_mem_cons.2 ⟨sub1_810, List.forall_mem_cons.2 ⟨sub1_811, List.forall_mem_cons.2 ⟨sub1_812, List.forall_mem_cons.2 ⟨sub1_813, List.forall_mem_cons.2 ⟨sub1_814, List.forall_mem_cons.2 ⟨sub1_815, List.forall_mem_cons.2 ⟨sub1_816, List.forall_mem_cons.2 ⟨sub1_817, List.forall_mem_cons.2 ⟨sub1_818, List.forall_mem_cons.2 ⟨sub1_819, List.forall_mem_cons.2 ⟨sub1_820, List.forall_mem_cons.2 ⟨sub1_821, List.forall_mem_cons.2 ⟨sub1_822, List.forall_mem_cons.2 ⟨sub1_823, List.forall_mem_cons.2 ⟨sub1_824, List.forall_mem_cons.2 ⟨sub1_825, List.forall_mem_cons.2 ⟨sub1_826, List.forall_mem_cons.2 ⟨sub1_827, List.forall_mem_cons.2 ⟨sub1_828, List.forall_mem_cons.2 ⟨sub1_829, List.forall_mem_cons.2 ⟨sub1_830, List.forall_mem_cons.2 ⟨sub1_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_832 : sub1 [2, 3, 5] = true := by decide +kernel
theorem sub1_833 : sub1 [2, 3, 6] = true := by decide +kernel
theorem sub1_834 : sub1 [2, 4] = true := by decide +kernel
theorem sub1_835 : sub1 [2, 5] = true := by decide +kernel
theorem sub1_836 : sub1 [2, 6] = true := by decide +kernel
theorem sub1_837 : sub1 [3, -7] = true := by decide +kernel
theorem sub1_838 : sub1 [3, -6] = true := by decide +kernel
theorem sub1_839 : sub1 [3, -5] = true := by decide +kernel
theorem sub1_840 : sub1 [3, -4] = true := by decide +kernel
theorem sub1_841 : sub1 [3, -3, -6] = true := by decide +kernel
theorem sub1_842 : sub1 [3, -3, -5] = true := by decide +kernel
theorem sub1_843 : sub1 [3, -3, -4] = true := by decide +kernel
theorem sub1_844 : sub1 [3, -3, -3] = true := by decide +kernel
theorem sub1_845 : sub1 [3, -3, -2] = true := by decide +kernel
theorem sub1_846 : sub1 [3, -3, -1] = true := by decide +kernel
theorem sub1_847 : sub1 [3, -3, 0] = true := by decide +kernel
theorem sub1_848 : sub1 [3, -3, 1] = true := by decide +kernel
theorem sub1_849 : sub1 [3, -3, 2] = true := by decide +kernel
theorem sub1_850 : sub1 [3, -3, 3] = true := by decide +kernel
theorem sub1_851 : sub1 [3, -3, 4] = true := by decide +kernel
theorem sub1_852 : sub1 [3, -3, 5] = true := by decide +kernel
theorem sub1_853 : sub1 [3, -3, 6] = true := by decide +kernel
theorem sub1_854 : sub1 [3, -3, 7] = true := by decide +kernel
theorem sub1_855 : sub1 [3, -2, -7] = true := by decide +kernel
theorem sub1_856 : sub1 [3, -2, -6] = true := by decide +kernel
theorem sub1_857 : sub1 [3, -2, -5] = true := by decide +kernel
theorem sub1_858 : sub1 [3, -2, -4] = true := by decide +kernel
theorem sub1_859 : sub1 [3, -2, -3] = true := by decide +kernel
theorem sub1_860 : sub1 [3, -2, -2] = true := by decide +kernel
theorem sub1_861 : sub1 [3, -2, -1] = true := by decide +kernel
theorem sub1_862 : sub1 [3, -2, 0] = true := by decide +kernel
theorem sub1_863 : sub1 [3, -2, 1] = true := by decide +kernel
theorem sb1_26 : ∀ q ∈ blk1_26, sub1 q = true := by
  unfold blk1_26
  exact List.forall_mem_cons.2 ⟨sub1_832, List.forall_mem_cons.2 ⟨sub1_833, List.forall_mem_cons.2 ⟨sub1_834, List.forall_mem_cons.2 ⟨sub1_835, List.forall_mem_cons.2 ⟨sub1_836, List.forall_mem_cons.2 ⟨sub1_837, List.forall_mem_cons.2 ⟨sub1_838, List.forall_mem_cons.2 ⟨sub1_839, List.forall_mem_cons.2 ⟨sub1_840, List.forall_mem_cons.2 ⟨sub1_841, List.forall_mem_cons.2 ⟨sub1_842, List.forall_mem_cons.2 ⟨sub1_843, List.forall_mem_cons.2 ⟨sub1_844, List.forall_mem_cons.2 ⟨sub1_845, List.forall_mem_cons.2 ⟨sub1_846, List.forall_mem_cons.2 ⟨sub1_847, List.forall_mem_cons.2 ⟨sub1_848, List.forall_mem_cons.2 ⟨sub1_849, List.forall_mem_cons.2 ⟨sub1_850, List.forall_mem_cons.2 ⟨sub1_851, List.forall_mem_cons.2 ⟨sub1_852, List.forall_mem_cons.2 ⟨sub1_853, List.forall_mem_cons.2 ⟨sub1_854, List.forall_mem_cons.2 ⟨sub1_855, List.forall_mem_cons.2 ⟨sub1_856, List.forall_mem_cons.2 ⟨sub1_857, List.forall_mem_cons.2 ⟨sub1_858, List.forall_mem_cons.2 ⟨sub1_859, List.forall_mem_cons.2 ⟨sub1_860, List.forall_mem_cons.2 ⟨sub1_861, List.forall_mem_cons.2 ⟨sub1_862, List.forall_mem_cons.2 ⟨sub1_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_864 : sub1 [3, -2, 2] = true := by decide +kernel
theorem sub1_865 : sub1 [3, -2, 3] = true := by decide +kernel
theorem sub1_866 : sub1 [3, -2, 4] = true := by decide +kernel
theorem sub1_867 : sub1 [3, -2, 5] = true := by decide +kernel
theorem sub1_868 : sub1 [3, -2, 6] = true := by decide +kernel
theorem sub1_869 : sub1 [3, -2, 7] = true := by decide +kernel
theorem sub1_870 : sub1 [3, -1, -7] = true := by decide +kernel
theorem sub1_871 : sub1 [3, -1, -6] = true := by decide +kernel
theorem sub1_872 : sub1 [3, -1, -5] = true := by decide +kernel
theorem sub1_873 : sub1 [3, -1, -4] = true := by decide +kernel
theorem sub1_874 : sub1 [3, -1, -3] = true := by decide +kernel
theorem sub1_875 : sub1 [3, -1, -2] = true := by decide +kernel
theorem sub1_876 : sub1 [3, -1, -1] = true := by decide +kernel
theorem sub1_877 : sub1 [3, -1, 0] = true := by decide +kernel
theorem sub1_878 : sub1 [3, -1, 1] = true := by decide +kernel
theorem sub1_879 : sub1 [3, -1, 2] = true := by decide +kernel
theorem sub1_880 : sub1 [3, -1, 3] = true := by decide +kernel
theorem sub1_881 : sub1 [3, -1, 4] = true := by decide +kernel
theorem sub1_882 : sub1 [3, -1, 5] = true := by decide +kernel
theorem sub1_883 : sub1 [3, -1, 6] = true := by decide +kernel
theorem sub1_884 : sub1 [3, -1, 7] = true := by decide +kernel
theorem sub1_885 : sub1 [3, 0, -8] = true := by decide +kernel
theorem sub1_886 : sub1 [3, 0, -7] = true := by decide +kernel
theorem sub1_887 : sub1 [3, 0, -6] = true := by decide +kernel
theorem sub1_888 : sub1 [3, 0, -5] = true := by decide +kernel
theorem sub1_889 : sub1 [3, 0, -4] = true := by decide +kernel
theorem sub1_890 : sub1 [3, 0, -3] = true := by decide +kernel
theorem sub1_891 : sub1 [3, 0, -2] = true := by decide +kernel
theorem sub1_892 : sub1 [3, 0, -1] = true := by decide +kernel
theorem sub1_893 : sub1 [3, 0, 0] = true := by decide +kernel
theorem sub1_894 : sub1 [3, 0, 1] = true := by decide +kernel
theorem sub1_895 : sub1 [3, 0, 2] = true := by decide +kernel
theorem sb1_27 : ∀ q ∈ blk1_27, sub1 q = true := by
  unfold blk1_27
  exact List.forall_mem_cons.2 ⟨sub1_864, List.forall_mem_cons.2 ⟨sub1_865, List.forall_mem_cons.2 ⟨sub1_866, List.forall_mem_cons.2 ⟨sub1_867, List.forall_mem_cons.2 ⟨sub1_868, List.forall_mem_cons.2 ⟨sub1_869, List.forall_mem_cons.2 ⟨sub1_870, List.forall_mem_cons.2 ⟨sub1_871, List.forall_mem_cons.2 ⟨sub1_872, List.forall_mem_cons.2 ⟨sub1_873, List.forall_mem_cons.2 ⟨sub1_874, List.forall_mem_cons.2 ⟨sub1_875, List.forall_mem_cons.2 ⟨sub1_876, List.forall_mem_cons.2 ⟨sub1_877, List.forall_mem_cons.2 ⟨sub1_878, List.forall_mem_cons.2 ⟨sub1_879, List.forall_mem_cons.2 ⟨sub1_880, List.forall_mem_cons.2 ⟨sub1_881, List.forall_mem_cons.2 ⟨sub1_882, List.forall_mem_cons.2 ⟨sub1_883, List.forall_mem_cons.2 ⟨sub1_884, List.forall_mem_cons.2 ⟨sub1_885, List.forall_mem_cons.2 ⟨sub1_886, List.forall_mem_cons.2 ⟨sub1_887, List.forall_mem_cons.2 ⟨sub1_888, List.forall_mem_cons.2 ⟨sub1_889, List.forall_mem_cons.2 ⟨sub1_890, List.forall_mem_cons.2 ⟨sub1_891, List.forall_mem_cons.2 ⟨sub1_892, List.forall_mem_cons.2 ⟨sub1_893, List.forall_mem_cons.2 ⟨sub1_894, List.forall_mem_cons.2 ⟨sub1_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_896 : sub1 [3, 0, 3] = true := by decide +kernel
theorem sub1_897 : sub1 [3, 0, 4] = true := by decide +kernel
theorem sub1_898 : sub1 [3, 0, 5] = true := by decide +kernel
theorem sub1_899 : sub1 [3, 0, 6] = true := by decide +kernel
theorem sub1_900 : sub1 [3, 0, 7] = true := by decide +kernel
theorem sub1_901 : sub1 [3, 1, -7] = true := by decide +kernel
theorem sub1_902 : sub1 [3, 1, -6] = true := by decide +kernel
theorem sub1_903 : sub1 [3, 1, -5] = true := by decide +kernel
theorem sub1_904 : sub1 [3, 1, -4] = true := by decide +kernel
theorem sub1_905 : sub1 [3, 1, -3] = true := by decide +kernel
theorem sub1_906 : sub1 [3, 1, -2] = true := by decide +kernel
theorem sub1_907 : sub1 [3, 1, -1] = true := by decide +kernel
theorem sub1_908 : sub1 [3, 1, 0] = true := by decide +kernel
theorem sub1_909 : sub1 [3, 1, 1] = true := by decide +kernel
theorem sub1_910 : sub1 [3, 1, 2] = true := by decide +kernel
theorem sub1_911 : sub1 [3, 1, 3] = true := by decide +kernel
theorem sub1_912 : sub1 [3, 1, 4] = true := by decide +kernel
theorem sub1_913 : sub1 [3, 1, 5] = true := by decide +kernel
theorem sub1_914 : sub1 [3, 1, 6] = true := by decide +kernel
theorem sub1_915 : sub1 [3, 1, 7] = true := by decide +kernel
theorem sub1_916 : sub1 [3, 2, -7] = true := by decide +kernel
theorem sub1_917 : sub1 [3, 2, -6] = true := by decide +kernel
theorem sub1_918 : sub1 [3, 2, -5] = true := by decide +kernel
theorem sub1_919 : sub1 [3, 2, -4] = true := by decide +kernel
theorem sub1_920 : sub1 [3, 2, -3] = true := by decide +kernel
theorem sub1_921 : sub1 [3, 2, -2] = true := by decide +kernel
theorem sub1_922 : sub1 [3, 2, -1] = true := by decide +kernel
theorem sub1_923 : sub1 [3, 2, 0] = true := by decide +kernel
theorem sub1_924 : sub1 [3, 2, 1] = true := by decide +kernel
theorem sub1_925 : sub1 [3, 2, 2] = true := by decide +kernel
theorem sub1_926 : sub1 [3, 2, 3] = true := by decide +kernel
theorem sub1_927 : sub1 [3, 2, 4] = true := by decide +kernel
theorem sb1_28 : ∀ q ∈ blk1_28, sub1 q = true := by
  unfold blk1_28
  exact List.forall_mem_cons.2 ⟨sub1_896, List.forall_mem_cons.2 ⟨sub1_897, List.forall_mem_cons.2 ⟨sub1_898, List.forall_mem_cons.2 ⟨sub1_899, List.forall_mem_cons.2 ⟨sub1_900, List.forall_mem_cons.2 ⟨sub1_901, List.forall_mem_cons.2 ⟨sub1_902, List.forall_mem_cons.2 ⟨sub1_903, List.forall_mem_cons.2 ⟨sub1_904, List.forall_mem_cons.2 ⟨sub1_905, List.forall_mem_cons.2 ⟨sub1_906, List.forall_mem_cons.2 ⟨sub1_907, List.forall_mem_cons.2 ⟨sub1_908, List.forall_mem_cons.2 ⟨sub1_909, List.forall_mem_cons.2 ⟨sub1_910, List.forall_mem_cons.2 ⟨sub1_911, List.forall_mem_cons.2 ⟨sub1_912, List.forall_mem_cons.2 ⟨sub1_913, List.forall_mem_cons.2 ⟨sub1_914, List.forall_mem_cons.2 ⟨sub1_915, List.forall_mem_cons.2 ⟨sub1_916, List.forall_mem_cons.2 ⟨sub1_917, List.forall_mem_cons.2 ⟨sub1_918, List.forall_mem_cons.2 ⟨sub1_919, List.forall_mem_cons.2 ⟨sub1_920, List.forall_mem_cons.2 ⟨sub1_921, List.forall_mem_cons.2 ⟨sub1_922, List.forall_mem_cons.2 ⟨sub1_923, List.forall_mem_cons.2 ⟨sub1_924, List.forall_mem_cons.2 ⟨sub1_925, List.forall_mem_cons.2 ⟨sub1_926, List.forall_mem_cons.2 ⟨sub1_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_928 : sub1 [3, 2, 5] = true := by decide +kernel
theorem sub1_929 : sub1 [3, 2, 6] = true := by decide +kernel
theorem sub1_930 : sub1 [3, 3] = true := by decide +kernel
theorem sub1_931 : sub1 [3, 4] = true := by decide +kernel
theorem sub1_932 : sub1 [3, 5] = true := by decide +kernel
theorem sub1_933 : sub1 [4, -7] = true := by decide +kernel
theorem sub1_934 : sub1 [4, -6] = true := by decide +kernel
theorem sub1_935 : sub1 [4, -5] = true := by decide +kernel
theorem sub1_936 : sub1 [4, -4] = true := by decide +kernel
theorem sub1_937 : sub1 [4, -3] = true := by decide +kernel
theorem sub1_938 : sub1 [4, -2, -6] = true := by decide +kernel
theorem sub1_939 : sub1 [4, -2, -5] = true := by decide +kernel
theorem sub1_940 : sub1 [4, -2, -4] = true := by decide +kernel
theorem sub1_941 : sub1 [4, -2, -3] = true := by decide +kernel
theorem sub1_942 : sub1 [4, -2, -2] = true := by decide +kernel
theorem sub1_943 : sub1 [4, -2, -1] = true := by decide +kernel
theorem sub1_944 : sub1 [4, -2, 0] = true := by decide +kernel
theorem sub1_945 : sub1 [4, -2, 1] = true := by decide +kernel
theorem sub1_946 : sub1 [4, -2, 2] = true := by decide +kernel
theorem sub1_947 : sub1 [4, -2, 3] = true := by decide +kernel
theorem sub1_948 : sub1 [4, -2, 4] = true := by decide +kernel
theorem sub1_949 : sub1 [4, -2, 5] = true := by decide +kernel
theorem sub1_950 : sub1 [4, -2, 6] = true := by decide +kernel
theorem sub1_951 : sub1 [4, -2, 7] = true := by decide +kernel
theorem sub1_952 : sub1 [4, -1, -7] = true := by decide +kernel
theorem sub1_953 : sub1 [4, -1, -6] = true := by decide +kernel
theorem sub1_954 : sub1 [4, -1, -5] = true := by decide +kernel
theorem sub1_955 : sub1 [4, -1, -4] = true := by decide +kernel
theorem sub1_956 : sub1 [4, -1, -3] = true := by decide +kernel
theorem sub1_957 : sub1 [4, -1, -2] = true := by decide +kernel
theorem sub1_958 : sub1 [4, -1, -1] = true := by decide +kernel
theorem sub1_959 : sub1 [4, -1, 0] = true := by decide +kernel
theorem sb1_29 : ∀ q ∈ blk1_29, sub1 q = true := by
  unfold blk1_29
  exact List.forall_mem_cons.2 ⟨sub1_928, List.forall_mem_cons.2 ⟨sub1_929, List.forall_mem_cons.2 ⟨sub1_930, List.forall_mem_cons.2 ⟨sub1_931, List.forall_mem_cons.2 ⟨sub1_932, List.forall_mem_cons.2 ⟨sub1_933, List.forall_mem_cons.2 ⟨sub1_934, List.forall_mem_cons.2 ⟨sub1_935, List.forall_mem_cons.2 ⟨sub1_936, List.forall_mem_cons.2 ⟨sub1_937, List.forall_mem_cons.2 ⟨sub1_938, List.forall_mem_cons.2 ⟨sub1_939, List.forall_mem_cons.2 ⟨sub1_940, List.forall_mem_cons.2 ⟨sub1_941, List.forall_mem_cons.2 ⟨sub1_942, List.forall_mem_cons.2 ⟨sub1_943, List.forall_mem_cons.2 ⟨sub1_944, List.forall_mem_cons.2 ⟨sub1_945, List.forall_mem_cons.2 ⟨sub1_946, List.forall_mem_cons.2 ⟨sub1_947, List.forall_mem_cons.2 ⟨sub1_948, List.forall_mem_cons.2 ⟨sub1_949, List.forall_mem_cons.2 ⟨sub1_950, List.forall_mem_cons.2 ⟨sub1_951, List.forall_mem_cons.2 ⟨sub1_952, List.forall_mem_cons.2 ⟨sub1_953, List.forall_mem_cons.2 ⟨sub1_954, List.forall_mem_cons.2 ⟨sub1_955, List.forall_mem_cons.2 ⟨sub1_956, List.forall_mem_cons.2 ⟨sub1_957, List.forall_mem_cons.2 ⟨sub1_958, List.forall_mem_cons.2 ⟨sub1_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_960 : sub1 [4, -1, 1] = true := by decide +kernel
theorem sub1_961 : sub1 [4, -1, 2] = true := by decide +kernel
theorem sub1_962 : sub1 [4, -1, 3] = true := by decide +kernel
theorem sub1_963 : sub1 [4, -1, 4] = true := by decide +kernel
theorem sub1_964 : sub1 [4, -1, 5] = true := by decide +kernel
theorem sub1_965 : sub1 [4, -1, 6] = true := by decide +kernel
theorem sub1_966 : sub1 [4, -1, 7] = true := by decide +kernel
theorem sub1_967 : sub1 [4, 0, -7] = true := by decide +kernel
theorem sub1_968 : sub1 [4, 0, -6] = true := by decide +kernel
theorem sub1_969 : sub1 [4, 0, -5] = true := by decide +kernel
theorem sub1_970 : sub1 [4, 0, -4] = true := by decide +kernel
theorem sub1_971 : sub1 [4, 0, -3] = true := by decide +kernel
theorem sub1_972 : sub1 [4, 0, -2] = true := by decide +kernel
theorem sub1_973 : sub1 [4, 0, -1] = true := by decide +kernel
theorem sub1_974 : sub1 [4, 0, 0] = true := by decide +kernel
theorem sub1_975 : sub1 [4, 0, 1] = true := by decide +kernel
theorem sub1_976 : sub1 [4, 0, 2] = true := by decide +kernel
theorem sub1_977 : sub1 [4, 0, 3] = true := by decide +kernel
theorem sub1_978 : sub1 [4, 0, 4] = true := by decide +kernel
theorem sub1_979 : sub1 [4, 0, 5] = true := by decide +kernel
theorem sub1_980 : sub1 [4, 0, 6] = true := by decide +kernel
theorem sub1_981 : sub1 [4, 1, -7] = true := by decide +kernel
theorem sub1_982 : sub1 [4, 1, -6] = true := by decide +kernel
theorem sub1_983 : sub1 [4, 1, -5] = true := by decide +kernel
theorem sub1_984 : sub1 [4, 1, -4] = true := by decide +kernel
theorem sub1_985 : sub1 [4, 1, -3] = true := by decide +kernel
theorem sub1_986 : sub1 [4, 1, -2] = true := by decide +kernel
theorem sub1_987 : sub1 [4, 1, -1] = true := by decide +kernel
theorem sub1_988 : sub1 [4, 1, 0] = true := by decide +kernel
theorem sub1_989 : sub1 [4, 1, 1] = true := by decide +kernel
theorem sub1_990 : sub1 [4, 1, 2] = true := by decide +kernel
theorem sub1_991 : sub1 [4, 1, 3] = true := by decide +kernel
theorem sb1_30 : ∀ q ∈ blk1_30, sub1 q = true := by
  unfold blk1_30
  exact List.forall_mem_cons.2 ⟨sub1_960, List.forall_mem_cons.2 ⟨sub1_961, List.forall_mem_cons.2 ⟨sub1_962, List.forall_mem_cons.2 ⟨sub1_963, List.forall_mem_cons.2 ⟨sub1_964, List.forall_mem_cons.2 ⟨sub1_965, List.forall_mem_cons.2 ⟨sub1_966, List.forall_mem_cons.2 ⟨sub1_967, List.forall_mem_cons.2 ⟨sub1_968, List.forall_mem_cons.2 ⟨sub1_969, List.forall_mem_cons.2 ⟨sub1_970, List.forall_mem_cons.2 ⟨sub1_971, List.forall_mem_cons.2 ⟨sub1_972, List.forall_mem_cons.2 ⟨sub1_973, List.forall_mem_cons.2 ⟨sub1_974, List.forall_mem_cons.2 ⟨sub1_975, List.forall_mem_cons.2 ⟨sub1_976, List.forall_mem_cons.2 ⟨sub1_977, List.forall_mem_cons.2 ⟨sub1_978, List.forall_mem_cons.2 ⟨sub1_979, List.forall_mem_cons.2 ⟨sub1_980, List.forall_mem_cons.2 ⟨sub1_981, List.forall_mem_cons.2 ⟨sub1_982, List.forall_mem_cons.2 ⟨sub1_983, List.forall_mem_cons.2 ⟨sub1_984, List.forall_mem_cons.2 ⟨sub1_985, List.forall_mem_cons.2 ⟨sub1_986, List.forall_mem_cons.2 ⟨sub1_987, List.forall_mem_cons.2 ⟨sub1_988, List.forall_mem_cons.2 ⟨sub1_989, List.forall_mem_cons.2 ⟨sub1_990, List.forall_mem_cons.2 ⟨sub1_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C043
