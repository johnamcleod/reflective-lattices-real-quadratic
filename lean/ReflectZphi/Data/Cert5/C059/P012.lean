import ReflectZphi.Data.Cert5.C059.Base

namespace ReflectZphi.Data.Cert5.C059
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_576 : sub6 [1, 1, -6] = true := by decide +kernel
theorem sub6_577 : sub6 [1, 1, -5] = true := by decide +kernel
theorem sub6_578 : sub6 [1, 1, -4] = true := by decide +kernel
theorem sub6_579 : sub6 [1, 1, -3] = true := by decide +kernel
theorem sub6_580 : sub6 [1, 1, -2] = true := by decide +kernel
theorem sub6_581 : sub6 [1, 1, -1] = true := by decide +kernel
theorem sub6_582 : sub6 [1, 1, 0] = true := by decide +kernel
theorem sub6_583 : sub6 [1, 1, 1] = true := by decide +kernel
theorem sub6_584 : sub6 [1, 1, 2] = true := by decide +kernel
theorem sub6_585 : sub6 [1, 1, 3] = true := by decide +kernel
theorem sub6_586 : sub6 [1, 1, 4] = true := by decide +kernel
theorem sub6_587 : sub6 [1, 1, 5] = true := by decide +kernel
theorem sub6_588 : sub6 [1, 1, 6] = true := by decide +kernel
theorem sub6_589 : sub6 [1, 1, 7] = true := by decide +kernel
theorem sub6_590 : sub6 [1, 1, 8] = true := by decide +kernel
theorem sub6_591 : sub6 [1, 1, 9] = true := by decide +kernel
theorem sub6_592 : sub6 [1, 1, 10] = true := by decide +kernel
theorem sub6_593 : sub6 [1, 2, -10] = true := by decide +kernel
theorem sub6_594 : sub6 [1, 2, -9] = true := by decide +kernel
theorem sub6_595 : sub6 [1, 2, -8] = true := by decide +kernel
theorem sub6_596 : sub6 [1, 2, -7] = true := by decide +kernel
theorem sub6_597 : sub6 [1, 2, -6] = true := by decide +kernel
theorem sub6_598 : sub6 [1, 2, -5] = true := by decide +kernel
theorem sub6_599 : sub6 [1, 2, -4] = true := by decide +kernel
theorem sub6_600 : sub6 [1, 2, -3] = true := by decide +kernel
theorem sub6_601 : sub6 [1, 2, -2] = true := by decide +kernel
theorem sub6_602 : sub6 [1, 2, -1] = true := by decide +kernel
theorem sub6_603 : sub6 [1, 2, 0] = true := by decide +kernel
theorem sub6_604 : sub6 [1, 2, 1] = true := by decide +kernel
theorem sub6_605 : sub6 [1, 2, 2] = true := by decide +kernel
theorem sub6_606 : sub6 [1, 2, 3] = true := by decide +kernel
theorem sub6_607 : sub6 [1, 2, 4] = true := by decide +kernel
theorem sb6_18 : ∀ q ∈ blk6_18, sub6 q = true := by
  unfold blk6_18
  exact List.forall_mem_cons.2 ⟨sub6_576, List.forall_mem_cons.2 ⟨sub6_577, List.forall_mem_cons.2 ⟨sub6_578, List.forall_mem_cons.2 ⟨sub6_579, List.forall_mem_cons.2 ⟨sub6_580, List.forall_mem_cons.2 ⟨sub6_581, List.forall_mem_cons.2 ⟨sub6_582, List.forall_mem_cons.2 ⟨sub6_583, List.forall_mem_cons.2 ⟨sub6_584, List.forall_mem_cons.2 ⟨sub6_585, List.forall_mem_cons.2 ⟨sub6_586, List.forall_mem_cons.2 ⟨sub6_587, List.forall_mem_cons.2 ⟨sub6_588, List.forall_mem_cons.2 ⟨sub6_589, List.forall_mem_cons.2 ⟨sub6_590, List.forall_mem_cons.2 ⟨sub6_591, List.forall_mem_cons.2 ⟨sub6_592, List.forall_mem_cons.2 ⟨sub6_593, List.forall_mem_cons.2 ⟨sub6_594, List.forall_mem_cons.2 ⟨sub6_595, List.forall_mem_cons.2 ⟨sub6_596, List.forall_mem_cons.2 ⟨sub6_597, List.forall_mem_cons.2 ⟨sub6_598, List.forall_mem_cons.2 ⟨sub6_599, List.forall_mem_cons.2 ⟨sub6_600, List.forall_mem_cons.2 ⟨sub6_601, List.forall_mem_cons.2 ⟨sub6_602, List.forall_mem_cons.2 ⟨sub6_603, List.forall_mem_cons.2 ⟨sub6_604, List.forall_mem_cons.2 ⟨sub6_605, List.forall_mem_cons.2 ⟨sub6_606, List.forall_mem_cons.2 ⟨sub6_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_608 : sub6 [1, 2, 5] = true := by decide +kernel
theorem sub6_609 : sub6 [1, 2, 6] = true := by decide +kernel
theorem sub6_610 : sub6 [1, 2, 7] = true := by decide +kernel
theorem sub6_611 : sub6 [1, 2, 8] = true := by decide +kernel
theorem sub6_612 : sub6 [1, 2, 9] = true := by decide +kernel
theorem sub6_613 : sub6 [1, 3, -8] = true := by decide +kernel
theorem sub6_614 : sub6 [1, 3, -7] = true := by decide +kernel
theorem sub6_615 : sub6 [1, 3, -6] = true := by decide +kernel
theorem sub6_616 : sub6 [1, 3, -5] = true := by decide +kernel
theorem sub6_617 : sub6 [1, 3, -4] = true := by decide +kernel
theorem sub6_618 : sub6 [1, 3, -3] = true := by decide +kernel
theorem sub6_619 : sub6 [1, 3, -2] = true := by decide +kernel
theorem sub6_620 : sub6 [1, 3, -1] = true := by decide +kernel
theorem sub6_621 : sub6 [1, 3, 0] = true := by decide +kernel
theorem sub6_622 : sub6 [1, 3, 1] = true := by decide +kernel
theorem sub6_623 : sub6 [1, 3, 2] = true := by decide +kernel
theorem sub6_624 : sub6 [1, 3, 3] = true := by decide +kernel
theorem sub6_625 : sub6 [1, 3, 4] = true := by decide +kernel
theorem sub6_626 : sub6 [1, 3, 5] = true := by decide +kernel
theorem sub6_627 : sub6 [1, 3, 6] = true := by decide +kernel
theorem sub6_628 : sub6 [1, 3, 7] = true := by decide +kernel
theorem sub6_629 : sub6 [1, 4] = true := by decide +kernel
theorem sub6_630 : sub6 [2, -5] = true := by decide +kernel
theorem sub6_631 : sub6 [2, -4] = true := by decide +kernel
theorem sub6_632 : sub6 [2, -3, -8] = true := by decide +kernel
theorem sub6_633 : sub6 [2, -3, -7] = true := by decide +kernel
theorem sub6_634 : sub6 [2, -3, -6] = true := by decide +kernel
theorem sub6_635 : sub6 [2, -3, -5] = true := by decide +kernel
theorem sub6_636 : sub6 [2, -3, -4] = true := by decide +kernel
theorem sub6_637 : sub6 [2, -3, -3] = true := by decide +kernel
theorem sub6_638 : sub6 [2, -3, -2] = true := by decide +kernel
theorem sub6_639 : sub6 [2, -3, -1] = true := by decide +kernel
theorem sb6_19 : ∀ q ∈ blk6_19, sub6 q = true := by
  unfold blk6_19
  exact List.forall_mem_cons.2 ⟨sub6_608, List.forall_mem_cons.2 ⟨sub6_609, List.forall_mem_cons.2 ⟨sub6_610, List.forall_mem_cons.2 ⟨sub6_611, List.forall_mem_cons.2 ⟨sub6_612, List.forall_mem_cons.2 ⟨sub6_613, List.forall_mem_cons.2 ⟨sub6_614, List.forall_mem_cons.2 ⟨sub6_615, List.forall_mem_cons.2 ⟨sub6_616, List.forall_mem_cons.2 ⟨sub6_617, List.forall_mem_cons.2 ⟨sub6_618, List.forall_mem_cons.2 ⟨sub6_619, List.forall_mem_cons.2 ⟨sub6_620, List.forall_mem_cons.2 ⟨sub6_621, List.forall_mem_cons.2 ⟨sub6_622, List.forall_mem_cons.2 ⟨sub6_623, List.forall_mem_cons.2 ⟨sub6_624, List.forall_mem_cons.2 ⟨sub6_625, List.forall_mem_cons.2 ⟨sub6_626, List.forall_mem_cons.2 ⟨sub6_627, List.forall_mem_cons.2 ⟨sub6_628, List.forall_mem_cons.2 ⟨sub6_629, List.forall_mem_cons.2 ⟨sub6_630, List.forall_mem_cons.2 ⟨sub6_631, List.forall_mem_cons.2 ⟨sub6_632, List.forall_mem_cons.2 ⟨sub6_633, List.forall_mem_cons.2 ⟨sub6_634, List.forall_mem_cons.2 ⟨sub6_635, List.forall_mem_cons.2 ⟨sub6_636, List.forall_mem_cons.2 ⟨sub6_637, List.forall_mem_cons.2 ⟨sub6_638, List.forall_mem_cons.2 ⟨sub6_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_640 : sub6 [2, -3, 0] = true := by decide +kernel
theorem sub6_641 : sub6 [2, -3, 1] = true := by decide +kernel
theorem sub6_642 : sub6 [2, -3, 2] = true := by decide +kernel
theorem sub6_643 : sub6 [2, -3, 3] = true := by decide +kernel
theorem sub6_644 : sub6 [2, -3, 4] = true := by decide +kernel
theorem sub6_645 : sub6 [2, -3, 5] = true := by decide +kernel
theorem sub6_646 : sub6 [2, -3, 6] = true := by decide +kernel
theorem sub6_647 : sub6 [2, -3, 7] = true := by decide +kernel
theorem sub6_648 : sub6 [2, -2, -10] = true := by decide +kernel
theorem sub6_649 : sub6 [2, -2, -9] = true := by decide +kernel
theorem sub6_650 : sub6 [2, -2, -8] = true := by decide +kernel
theorem sub6_651 : sub6 [2, -2, -7] = true := by decide +kernel
theorem sub6_652 : sub6 [2, -2, -6] = true := by decide +kernel
theorem sub6_653 : sub6 [2, -2, -5] = true := by decide +kernel
theorem sub6_654 : sub6 [2, -2, -4] = true := by decide +kernel
theorem sub6_655 : sub6 [2, -2, -3] = true := by decide +kernel
theorem sub6_656 : sub6 [2, -2, -2] = true := by decide +kernel
theorem sub6_657 : sub6 [2, -2, -1] = true := by decide +kernel
theorem sub6_658 : sub6 [2, -2, 0] = true := by decide +kernel
theorem sub6_659 : sub6 [2, -2, 1] = true := by decide +kernel
theorem sub6_660 : sub6 [2, -2, 2] = true := by decide +kernel
theorem sub6_661 : sub6 [2, -2, 3] = true := by decide +kernel
theorem sub6_662 : sub6 [2, -2, 4] = true := by decide +kernel
theorem sub6_663 : sub6 [2, -2, 5] = true := by decide +kernel
theorem sub6_664 : sub6 [2, -2, 6] = true := by decide +kernel
theorem sub6_665 : sub6 [2, -2, 7] = true := by decide +kernel
theorem sub6_666 : sub6 [2, -2, 8] = true := by decide +kernel
theorem sub6_667 : sub6 [2, -2, 9] = true := by decide +kernel
theorem sub6_668 : sub6 [2, -1, -10] = true := by decide +kernel
theorem sub6_669 : sub6 [2, -1, -9] = true := by decide +kernel
theorem sub6_670 : sub6 [2, -1, -8] = true := by decide +kernel
theorem sub6_671 : sub6 [2, -1, -7] = true := by decide +kernel
theorem sb6_20 : ∀ q ∈ blk6_20, sub6 q = true := by
  unfold blk6_20
  exact List.forall_mem_cons.2 ⟨sub6_640, List.forall_mem_cons.2 ⟨sub6_641, List.forall_mem_cons.2 ⟨sub6_642, List.forall_mem_cons.2 ⟨sub6_643, List.forall_mem_cons.2 ⟨sub6_644, List.forall_mem_cons.2 ⟨sub6_645, List.forall_mem_cons.2 ⟨sub6_646, List.forall_mem_cons.2 ⟨sub6_647, List.forall_mem_cons.2 ⟨sub6_648, List.forall_mem_cons.2 ⟨sub6_649, List.forall_mem_cons.2 ⟨sub6_650, List.forall_mem_cons.2 ⟨sub6_651, List.forall_mem_cons.2 ⟨sub6_652, List.forall_mem_cons.2 ⟨sub6_653, List.forall_mem_cons.2 ⟨sub6_654, List.forall_mem_cons.2 ⟨sub6_655, List.forall_mem_cons.2 ⟨sub6_656, List.forall_mem_cons.2 ⟨sub6_657, List.forall_mem_cons.2 ⟨sub6_658, List.forall_mem_cons.2 ⟨sub6_659, List.forall_mem_cons.2 ⟨sub6_660, List.forall_mem_cons.2 ⟨sub6_661, List.forall_mem_cons.2 ⟨sub6_662, List.forall_mem_cons.2 ⟨sub6_663, List.forall_mem_cons.2 ⟨sub6_664, List.forall_mem_cons.2 ⟨sub6_665, List.forall_mem_cons.2 ⟨sub6_666, List.forall_mem_cons.2 ⟨sub6_667, List.forall_mem_cons.2 ⟨sub6_668, List.forall_mem_cons.2 ⟨sub6_669, List.forall_mem_cons.2 ⟨sub6_670, List.forall_mem_cons.2 ⟨sub6_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_672 : sub6 [2, -1, -6] = true := by decide +kernel
theorem sub6_673 : sub6 [2, -1, -5] = true := by decide +kernel
theorem sub6_674 : sub6 [2, -1, -4] = true := by decide +kernel
theorem sub6_675 : sub6 [2, -1, -3] = true := by decide +kernel
theorem sub6_676 : sub6 [2, -1, -2] = true := by decide +kernel
theorem sub6_677 : sub6 [2, -1, -1] = true := by decide +kernel
theorem sub6_678 : sub6 [2, -1, 0] = true := by decide +kernel
theorem sub6_679 : sub6 [2, -1, 1] = true := by decide +kernel
theorem sub6_680 : sub6 [2, -1, 2] = true := by decide +kernel
theorem sub6_681 : sub6 [2, -1, 3] = true := by decide +kernel
theorem sub6_682 : sub6 [2, -1, 4] = true := by decide +kernel
theorem sub6_683 : sub6 [2, -1, 5] = true := by decide +kernel
theorem sub6_684 : sub6 [2, -1, 6] = true := by decide +kernel
theorem sub6_685 : sub6 [2, -1, 7] = true := by decide +kernel
theorem sub6_686 : sub6 [2, -1, 8] = true := by decide +kernel
theorem sub6_687 : sub6 [2, -1, 9] = true := by decide +kernel
theorem sub6_688 : sub6 [2, 0, -11] = true := by decide +kernel
theorem sub6_689 : sub6 [2, 0, -10] = true := by decide +kernel
theorem sub6_690 : sub6 [2, 0, -9] = true := by decide +kernel
theorem sub6_691 : sub6 [2, 0, -8] = true := by decide +kernel
theorem sub6_692 : sub6 [2, 0, -7] = true := by decide +kernel
theorem sub6_693 : sub6 [2, 0, -6] = true := by decide +kernel
theorem sub6_694 : sub6 [2, 0, -5] = true := by decide +kernel
theorem sub6_695 : sub6 [2, 0, -4] = true := by decide +kernel
theorem sub6_696 : sub6 [2, 0, -3] = true := by decide +kernel
theorem sub6_697 : sub6 [2, 0, -2] = true := by decide +kernel
theorem sub6_698 : sub6 [2, 0, -1] = true := by decide +kernel
theorem sub6_699 : sub6 [2, 0, 0] = true := by decide +kernel
theorem sub6_700 : sub6 [2, 0, 1] = true := by decide +kernel
theorem sub6_701 : sub6 [2, 0, 2] = true := by decide +kernel
theorem sub6_702 : sub6 [2, 0, 3] = true := by decide +kernel
theorem sub6_703 : sub6 [2, 0, 4] = true := by decide +kernel
theorem sb6_21 : ∀ q ∈ blk6_21, sub6 q = true := by
  unfold blk6_21
  exact List.forall_mem_cons.2 ⟨sub6_672, List.forall_mem_cons.2 ⟨sub6_673, List.forall_mem_cons.2 ⟨sub6_674, List.forall_mem_cons.2 ⟨sub6_675, List.forall_mem_cons.2 ⟨sub6_676, List.forall_mem_cons.2 ⟨sub6_677, List.forall_mem_cons.2 ⟨sub6_678, List.forall_mem_cons.2 ⟨sub6_679, List.forall_mem_cons.2 ⟨sub6_680, List.forall_mem_cons.2 ⟨sub6_681, List.forall_mem_cons.2 ⟨sub6_682, List.forall_mem_cons.2 ⟨sub6_683, List.forall_mem_cons.2 ⟨sub6_684, List.forall_mem_cons.2 ⟨sub6_685, List.forall_mem_cons.2 ⟨sub6_686, List.forall_mem_cons.2 ⟨sub6_687, List.forall_mem_cons.2 ⟨sub6_688, List.forall_mem_cons.2 ⟨sub6_689, List.forall_mem_cons.2 ⟨sub6_690, List.forall_mem_cons.2 ⟨sub6_691, List.forall_mem_cons.2 ⟨sub6_692, List.forall_mem_cons.2 ⟨sub6_693, List.forall_mem_cons.2 ⟨sub6_694, List.forall_mem_cons.2 ⟨sub6_695, List.forall_mem_cons.2 ⟨sub6_696, List.forall_mem_cons.2 ⟨sub6_697, List.forall_mem_cons.2 ⟨sub6_698, List.forall_mem_cons.2 ⟨sub6_699, List.forall_mem_cons.2 ⟨sub6_700, List.forall_mem_cons.2 ⟨sub6_701, List.forall_mem_cons.2 ⟨sub6_702, List.forall_mem_cons.2 ⟨sub6_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_704 : sub6 [2, 0, 5] = true := by decide +kernel
theorem sub6_705 : sub6 [2, 0, 6] = true := by decide +kernel
theorem sub6_706 : sub6 [2, 0, 7] = true := by decide +kernel
theorem sub6_707 : sub6 [2, 0, 8] = true := by decide +kernel
theorem sub6_708 : sub6 [2, 0, 9] = true := by decide +kernel
theorem sub6_709 : sub6 [2, 1, -10] = true := by decide +kernel
theorem sub6_710 : sub6 [2, 1, -9] = true := by decide +kernel
theorem sub6_711 : sub6 [2, 1, -8] = true := by decide +kernel
theorem sub6_712 : sub6 [2, 1, -7] = true := by decide +kernel
theorem sub6_713 : sub6 [2, 1, -6] = true := by decide +kernel
theorem sub6_714 : sub6 [2, 1, -5] = true := by decide +kernel
theorem sub6_715 : sub6 [2, 1, -4] = true := by decide +kernel
theorem sub6_716 : sub6 [2, 1, -3] = true := by decide +kernel
theorem sub6_717 : sub6 [2, 1, -2] = true := by decide +kernel
theorem sub6_718 : sub6 [2, 1, -1] = true := by decide +kernel
theorem sub6_719 : sub6 [2, 1, 0] = true := by decide +kernel
theorem sub6_720 : sub6 [2, 1, 1] = true := by decide +kernel
theorem sub6_721 : sub6 [2, 1, 2] = true := by decide +kernel
theorem sub6_722 : sub6 [2, 1, 3] = true := by decide +kernel
theorem sub6_723 : sub6 [2, 1, 4] = true := by decide +kernel
theorem sub6_724 : sub6 [2, 1, 5] = true := by decide +kernel
theorem sub6_725 : sub6 [2, 1, 6] = true := by decide +kernel
theorem sub6_726 : sub6 [2, 1, 7] = true := by decide +kernel
theorem sub6_727 : sub6 [2, 1, 8] = true := by decide +kernel
theorem sub6_728 : sub6 [2, 1, 9] = true := by decide +kernel
theorem sub6_729 : sub6 [2, 2, -9] = true := by decide +kernel
theorem sub6_730 : sub6 [2, 2, -8] = true := by decide +kernel
theorem sub6_731 : sub6 [2, 2, -7] = true := by decide +kernel
theorem sub6_732 : sub6 [2, 2, -6] = true := by decide +kernel
theorem sub6_733 : sub6 [2, 2, -5] = true := by decide +kernel
theorem sub6_734 : sub6 [2, 2, -4] = true := by decide +kernel
theorem sub6_735 : sub6 [2, 2, -3] = true := by decide +kernel
theorem sb6_22 : ∀ q ∈ blk6_22, sub6 q = true := by
  unfold blk6_22
  exact List.forall_mem_cons.2 ⟨sub6_704, List.forall_mem_cons.2 ⟨sub6_705, List.forall_mem_cons.2 ⟨sub6_706, List.forall_mem_cons.2 ⟨sub6_707, List.forall_mem_cons.2 ⟨sub6_708, List.forall_mem_cons.2 ⟨sub6_709, List.forall_mem_cons.2 ⟨sub6_710, List.forall_mem_cons.2 ⟨sub6_711, List.forall_mem_cons.2 ⟨sub6_712, List.forall_mem_cons.2 ⟨sub6_713, List.forall_mem_cons.2 ⟨sub6_714, List.forall_mem_cons.2 ⟨sub6_715, List.forall_mem_cons.2 ⟨sub6_716, List.forall_mem_cons.2 ⟨sub6_717, List.forall_mem_cons.2 ⟨sub6_718, List.forall_mem_cons.2 ⟨sub6_719, List.forall_mem_cons.2 ⟨sub6_720, List.forall_mem_cons.2 ⟨sub6_721, List.forall_mem_cons.2 ⟨sub6_722, List.forall_mem_cons.2 ⟨sub6_723, List.forall_mem_cons.2 ⟨sub6_724, List.forall_mem_cons.2 ⟨sub6_725, List.forall_mem_cons.2 ⟨sub6_726, List.forall_mem_cons.2 ⟨sub6_727, List.forall_mem_cons.2 ⟨sub6_728, List.forall_mem_cons.2 ⟨sub6_729, List.forall_mem_cons.2 ⟨sub6_730, List.forall_mem_cons.2 ⟨sub6_731, List.forall_mem_cons.2 ⟨sub6_732, List.forall_mem_cons.2 ⟨sub6_733, List.forall_mem_cons.2 ⟨sub6_734, List.forall_mem_cons.2 ⟨sub6_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_736 : sub6 [2, 2, -2] = true := by decide +kernel
theorem sub6_737 : sub6 [2, 2, -1] = true := by decide +kernel
theorem sub6_738 : sub6 [2, 2, 0] = true := by decide +kernel
theorem sub6_739 : sub6 [2, 2, 1] = true := by decide +kernel
theorem sub6_740 : sub6 [2, 2, 2] = true := by decide +kernel
theorem sub6_741 : sub6 [2, 2, 3] = true := by decide +kernel
theorem sub6_742 : sub6 [2, 2, 4] = true := by decide +kernel
theorem sub6_743 : sub6 [2, 2, 5] = true := by decide +kernel
theorem sub6_744 : sub6 [2, 2, 6] = true := by decide +kernel
theorem sub6_745 : sub6 [2, 2, 7] = true := by decide +kernel
theorem sub6_746 : sub6 [2, 2, 8] = true := by decide +kernel
theorem sub6_747 : sub6 [2, 3] = true := by decide +kernel
theorem sub6_748 : sub6 [3, -5] = true := by decide +kernel
theorem sub6_749 : sub6 [3, -4] = true := by decide +kernel
theorem sub6_750 : sub6 [3, -3] = true := by decide +kernel
theorem sub6_751 : sub6 [3, -2, -8] = true := by decide +kernel
theorem sub6_752 : sub6 [3, -2, -7] = true := by decide +kernel
theorem sub6_753 : sub6 [3, -2, -6] = true := by decide +kernel
theorem sub6_754 : sub6 [3, -2, -5] = true := by decide +kernel
theorem sub6_755 : sub6 [3, -2, -4] = true := by decide +kernel
theorem sub6_756 : sub6 [3, -2, -3] = true := by decide +kernel
theorem sub6_757 : sub6 [3, -2, -2] = true := by decide +kernel
theorem sub6_758 : sub6 [3, -2, -1] = true := by decide +kernel
theorem sub6_759 : sub6 [3, -2, 0] = true := by decide +kernel
theorem sub6_760 : sub6 [3, -2, 1] = true := by decide +kernel
theorem sub6_761 : sub6 [3, -2, 2] = true := by decide +kernel
theorem sub6_762 : sub6 [3, -2, 3] = true := by decide +kernel
theorem sub6_763 : sub6 [3, -2, 4] = true := by decide +kernel
theorem sub6_764 : sub6 [3, -2, 5] = true := by decide +kernel
theorem sub6_765 : sub6 [3, -2, 6] = true := by decide +kernel
theorem sub6_766 : sub6 [3, -2, 7] = true := by decide +kernel
theorem sub6_767 : sub6 [3, -1, -9] = true := by decide +kernel
theorem sb6_23 : ∀ q ∈ blk6_23, sub6 q = true := by
  unfold blk6_23
  exact List.forall_mem_cons.2 ⟨sub6_736, List.forall_mem_cons.2 ⟨sub6_737, List.forall_mem_cons.2 ⟨sub6_738, List.forall_mem_cons.2 ⟨sub6_739, List.forall_mem_cons.2 ⟨sub6_740, List.forall_mem_cons.2 ⟨sub6_741, List.forall_mem_cons.2 ⟨sub6_742, List.forall_mem_cons.2 ⟨sub6_743, List.forall_mem_cons.2 ⟨sub6_744, List.forall_mem_cons.2 ⟨sub6_745, List.forall_mem_cons.2 ⟨sub6_746, List.forall_mem_cons.2 ⟨sub6_747, List.forall_mem_cons.2 ⟨sub6_748, List.forall_mem_cons.2 ⟨sub6_749, List.forall_mem_cons.2 ⟨sub6_750, List.forall_mem_cons.2 ⟨sub6_751, List.forall_mem_cons.2 ⟨sub6_752, List.forall_mem_cons.2 ⟨sub6_753, List.forall_mem_cons.2 ⟨sub6_754, List.forall_mem_cons.2 ⟨sub6_755, List.forall_mem_cons.2 ⟨sub6_756, List.forall_mem_cons.2 ⟨sub6_757, List.forall_mem_cons.2 ⟨sub6_758, List.forall_mem_cons.2 ⟨sub6_759, List.forall_mem_cons.2 ⟨sub6_760, List.forall_mem_cons.2 ⟨sub6_761, List.forall_mem_cons.2 ⟨sub6_762, List.forall_mem_cons.2 ⟨sub6_763, List.forall_mem_cons.2 ⟨sub6_764, List.forall_mem_cons.2 ⟨sub6_765, List.forall_mem_cons.2 ⟨sub6_766, List.forall_mem_cons.2 ⟨sub6_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_768 : sub6 [3, -1, -8] = true := by decide +kernel
theorem sub6_769 : sub6 [3, -1, -7] = true := by decide +kernel
theorem sub6_770 : sub6 [3, -1, -6] = true := by decide +kernel
theorem sub6_771 : sub6 [3, -1, -5] = true := by decide +kernel
theorem sub6_772 : sub6 [3, -1, -4] = true := by decide +kernel
theorem sub6_773 : sub6 [3, -1, -3] = true := by decide +kernel
theorem sub6_774 : sub6 [3, -1, -2] = true := by decide +kernel
theorem sub6_775 : sub6 [3, -1, -1] = true := by decide +kernel
theorem sub6_776 : sub6 [3, -1, 0] = true := by decide +kernel
theorem sub6_777 : sub6 [3, -1, 1] = true := by decide +kernel
theorem sub6_778 : sub6 [3, -1, 2] = true := by decide +kernel
theorem sub6_779 : sub6 [3, -1, 3] = true := by decide +kernel
theorem sub6_780 : sub6 [3, -1, 4] = true := by decide +kernel
theorem sub6_781 : sub6 [3, -1, 5] = true := by decide +kernel
theorem sub6_782 : sub6 [3, -1, 6] = true := by decide +kernel
theorem sub6_783 : sub6 [3, -1, 7] = true := by decide +kernel
theorem sub6_784 : sub6 [3, -1, 8] = true := by decide +kernel
theorem sub6_785 : sub6 [3, 0, -9] = true := by decide +kernel
theorem sub6_786 : sub6 [3, 0, -8] = true := by decide +kernel
theorem sub6_787 : sub6 [3, 0, -7] = true := by decide +kernel
theorem sub6_788 : sub6 [3, 0, -6] = true := by decide +kernel
theorem sub6_789 : sub6 [3, 0, -5] = true := by decide +kernel
theorem sub6_790 : sub6 [3, 0, -4] = true := by decide +kernel
theorem sub6_791 : sub6 [3, 0, -3] = true := by decide +kernel
theorem sub6_792 : sub6 [3, 0, -2] = true := by decide +kernel
theorem sub6_793 : sub6 [3, 0, -1] = true := by decide +kernel
theorem sub6_794 : sub6 [3, 0, 0] = true := by decide +kernel
theorem sub6_795 : sub6 [3, 0, 1] = true := by decide +kernel
theorem sub6_796 : sub6 [3, 0, 2] = true := by decide +kernel
theorem sub6_797 : sub6 [3, 0, 3] = true := by decide +kernel
theorem sub6_798 : sub6 [3, 0, 4] = true := by decide +kernel
theorem sub6_799 : sub6 [3, 0, 5] = true := by decide +kernel
theorem sb6_24 : ∀ q ∈ blk6_24, sub6 q = true := by
  unfold blk6_24
  exact List.forall_mem_cons.2 ⟨sub6_768, List.forall_mem_cons.2 ⟨sub6_769, List.forall_mem_cons.2 ⟨sub6_770, List.forall_mem_cons.2 ⟨sub6_771, List.forall_mem_cons.2 ⟨sub6_772, List.forall_mem_cons.2 ⟨sub6_773, List.forall_mem_cons.2 ⟨sub6_774, List.forall_mem_cons.2 ⟨sub6_775, List.forall_mem_cons.2 ⟨sub6_776, List.forall_mem_cons.2 ⟨sub6_777, List.forall_mem_cons.2 ⟨sub6_778, List.forall_mem_cons.2 ⟨sub6_779, List.forall_mem_cons.2 ⟨sub6_780, List.forall_mem_cons.2 ⟨sub6_781, List.forall_mem_cons.2 ⟨sub6_782, List.forall_mem_cons.2 ⟨sub6_783, List.forall_mem_cons.2 ⟨sub6_784, List.forall_mem_cons.2 ⟨sub6_785, List.forall_mem_cons.2 ⟨sub6_786, List.forall_mem_cons.2 ⟨sub6_787, List.forall_mem_cons.2 ⟨sub6_788, List.forall_mem_cons.2 ⟨sub6_789, List.forall_mem_cons.2 ⟨sub6_790, List.forall_mem_cons.2 ⟨sub6_791, List.forall_mem_cons.2 ⟨sub6_792, List.forall_mem_cons.2 ⟨sub6_793, List.forall_mem_cons.2 ⟨sub6_794, List.forall_mem_cons.2 ⟨sub6_795, List.forall_mem_cons.2 ⟨sub6_796, List.forall_mem_cons.2 ⟨sub6_797, List.forall_mem_cons.2 ⟨sub6_798, List.forall_mem_cons.2 ⟨sub6_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_800 : sub6 [3, 0, 6] = true := by decide +kernel
theorem sub6_801 : sub6 [3, 0, 7] = true := by decide +kernel
theorem sub6_802 : sub6 [3, 0, 8] = true := by decide +kernel
theorem sub6_803 : sub6 [3, 1, -9] = true := by decide +kernel
theorem sub6_804 : sub6 [3, 1, -8] = true := by decide +kernel
theorem sub6_805 : sub6 [3, 1, -7] = true := by decide +kernel
theorem sub6_806 : sub6 [3, 1, -6] = true := by decide +kernel
theorem sub6_807 : sub6 [3, 1, -5] = true := by decide +kernel
theorem sub6_808 : sub6 [3, 1, -4] = true := by decide +kernel
theorem sub6_809 : sub6 [3, 1, -3] = true := by decide +kernel
theorem sub6_810 : sub6 [3, 1, -2] = true := by decide +kernel
theorem sub6_811 : sub6 [3, 1, -1] = true := by decide +kernel
theorem sub6_812 : sub6 [3, 1, 0] = true := by decide +kernel
theorem sub6_813 : sub6 [3, 1, 1] = true := by decide +kernel
theorem sub6_814 : sub6 [3, 1, 2] = true := by decide +kernel
theorem sub6_815 : sub6 [3, 1, 3] = true := by decide +kernel
theorem sub6_816 : sub6 [3, 1, 4] = true := by decide +kernel
theorem sub6_817 : sub6 [3, 1, 5] = true := by decide +kernel
theorem sub6_818 : sub6 [3, 1, 6] = true := by decide +kernel
theorem sub6_819 : sub6 [3, 1, 7] = true := by decide +kernel
theorem sub6_820 : sub6 [3, 2] = true := by decide +kernel
theorem sub6_821 : sub6 [3, 3] = true := by decide +kernel
theorem sub6_822 : sub6 [4, -4] = true := by decide +kernel
theorem sub6_823 : sub6 [4, -3] = true := by decide +kernel
theorem sub6_824 : sub6 [4, -2] = true := by decide +kernel
theorem sub6_825 : sub6 [4, -1] = true := by decide +kernel
theorem sub6_826 : sub6 [4, 0] = true := by decide +kernel
theorem sub6_827 : sub6 [4, 1] = true := by decide +kernel
theorem sub6_828 : sub6 [4, 2] = true := by decide +kernel
theorem sb6_25 : ∀ q ∈ blk6_25, sub6 q = true := by
  unfold blk6_25
  exact List.forall_mem_cons.2 ⟨sub6_800, List.forall_mem_cons.2 ⟨sub6_801, List.forall_mem_cons.2 ⟨sub6_802, List.forall_mem_cons.2 ⟨sub6_803, List.forall_mem_cons.2 ⟨sub6_804, List.forall_mem_cons.2 ⟨sub6_805, List.forall_mem_cons.2 ⟨sub6_806, List.forall_mem_cons.2 ⟨sub6_807, List.forall_mem_cons.2 ⟨sub6_808, List.forall_mem_cons.2 ⟨sub6_809, List.forall_mem_cons.2 ⟨sub6_810, List.forall_mem_cons.2 ⟨sub6_811, List.forall_mem_cons.2 ⟨sub6_812, List.forall_mem_cons.2 ⟨sub6_813, List.forall_mem_cons.2 ⟨sub6_814, List.forall_mem_cons.2 ⟨sub6_815, List.forall_mem_cons.2 ⟨sub6_816, List.forall_mem_cons.2 ⟨sub6_817, List.forall_mem_cons.2 ⟨sub6_818, List.forall_mem_cons.2 ⟨sub6_819, List.forall_mem_cons.2 ⟨sub6_820, List.forall_mem_cons.2 ⟨sub6_821, List.forall_mem_cons.2 ⟨sub6_822, List.forall_mem_cons.2 ⟨sub6_823, List.forall_mem_cons.2 ⟨sub6_824, List.forall_mem_cons.2 ⟨sub6_825, List.forall_mem_cons.2 ⟨sub6_826, List.forall_mem_cons.2 ⟨sub6_827, List.forall_mem_cons.2 ⟨sub6_828, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_0 : sub7 [-6] = true := by decide +kernel
theorem sub7_1 : sub7 [-5, -5] = true := by decide +kernel
theorem sub7_2 : sub7 [-5, -4] = true := by decide +kernel
theorem sub7_3 : sub7 [-5, -3] = true := by decide +kernel
theorem sub7_4 : sub7 [-5, -2] = true := by decide +kernel
theorem sub7_5 : sub7 [-5, -1] = true := by decide +kernel
theorem sub7_6 : sub7 [-5, 0] = true := by decide +kernel
theorem sub7_7 : sub7 [-5, 1] = true := by decide +kernel
theorem sub7_8 : sub7 [-5, 2] = true := by decide +kernel
theorem sub7_9 : sub7 [-4, -5] = true := by decide +kernel
theorem sub7_10 : sub7 [-4, -4] = true := by decide +kernel
theorem sub7_11 : sub7 [-4, -3] = true := by decide +kernel
theorem sub7_12 : sub7 [-4, -2] = true := by decide +kernel
theorem sub7_13 : sub7 [-4, -1] = true := by decide +kernel
theorem sub7_14 : sub7 [-4, 0] = true := by decide +kernel
theorem sub7_15 : sub7 [-4, 1] = true := by decide +kernel
theorem sub7_16 : sub7 [-4, 2] = true := by decide +kernel
theorem sub7_17 : sub7 [-4, 3] = true := by decide +kernel
theorem sub7_18 : sub7 [-3, -6] = true := by decide +kernel
theorem sub7_19 : sub7 [-3, -5] = true := by decide +kernel
theorem sub7_20 : sub7 [-3, -4] = true := by decide +kernel
theorem sub7_21 : sub7 [-3, -3] = true := by decide +kernel
theorem sub7_22 : sub7 [-3, -2] = true := by decide +kernel
theorem sub7_23 : sub7 [-3, -1, -6] = true := by decide +kernel
theorem sub7_24 : sub7 [-3, -1, -5] = true := by decide +kernel
theorem sub7_25 : sub7 [-3, -1, -4] = true := by decide +kernel
theorem sub7_26 : sub7 [-3, -1, -3] = true := by decide +kernel
theorem sub7_27 : sub7 [-3, -1, -2] = true := by decide +kernel
theorem sub7_28 : sub7 [-3, -1, -1] = true := by decide +kernel
theorem sub7_29 : sub7 [-3, -1, 0] = true := by decide +kernel
theorem sub7_30 : sub7 [-3, -1, 1] = true := by decide +kernel
theorem sub7_31 : sub7 [-3, -1, 2] = true := by decide +kernel
theorem sb7_0 : ∀ q ∈ blk7_0, sub7 q = true := by
  unfold blk7_0
  exact List.forall_mem_cons.2 ⟨sub7_0, List.forall_mem_cons.2 ⟨sub7_1, List.forall_mem_cons.2 ⟨sub7_2, List.forall_mem_cons.2 ⟨sub7_3, List.forall_mem_cons.2 ⟨sub7_4, List.forall_mem_cons.2 ⟨sub7_5, List.forall_mem_cons.2 ⟨sub7_6, List.forall_mem_cons.2 ⟨sub7_7, List.forall_mem_cons.2 ⟨sub7_8, List.forall_mem_cons.2 ⟨sub7_9, List.forall_mem_cons.2 ⟨sub7_10, List.forall_mem_cons.2 ⟨sub7_11, List.forall_mem_cons.2 ⟨sub7_12, List.forall_mem_cons.2 ⟨sub7_13, List.forall_mem_cons.2 ⟨sub7_14, List.forall_mem_cons.2 ⟨sub7_15, List.forall_mem_cons.2 ⟨sub7_16, List.forall_mem_cons.2 ⟨sub7_17, List.forall_mem_cons.2 ⟨sub7_18, List.forall_mem_cons.2 ⟨sub7_19, List.forall_mem_cons.2 ⟨sub7_20, List.forall_mem_cons.2 ⟨sub7_21, List.forall_mem_cons.2 ⟨sub7_22, List.forall_mem_cons.2 ⟨sub7_23, List.forall_mem_cons.2 ⟨sub7_24, List.forall_mem_cons.2 ⟨sub7_25, List.forall_mem_cons.2 ⟨sub7_26, List.forall_mem_cons.2 ⟨sub7_27, List.forall_mem_cons.2 ⟨sub7_28, List.forall_mem_cons.2 ⟨sub7_29, List.forall_mem_cons.2 ⟨sub7_30, List.forall_mem_cons.2 ⟨sub7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_32 : sub7 [-3, -1, 3] = true := by decide +kernel
theorem sub7_33 : sub7 [-3, -1, 4] = true := by decide +kernel
theorem sub7_34 : sub7 [-3, -1, 5] = true := by decide +kernel
theorem sub7_35 : sub7 [-3, -1, 6] = true := by decide +kernel
theorem sub7_36 : sub7 [-3, -1, 7] = true := by decide +kernel
theorem sub7_37 : sub7 [-3, 0, -6] = true := by decide +kernel
theorem sub7_38 : sub7 [-3, 0, -5] = true := by decide +kernel
theorem sub7_39 : sub7 [-3, 0, -4] = true := by decide +kernel
theorem sub7_40 : sub7 [-3, 0, -3] = true := by decide +kernel
theorem sub7_41 : sub7 [-3, 0, -2] = true := by decide +kernel
theorem sub7_42 : sub7 [-3, 0, -1] = true := by decide +kernel
theorem sub7_43 : sub7 [-3, 0, 0] = true := by decide +kernel
theorem sub7_44 : sub7 [-3, 0, 1] = true := by decide +kernel
theorem sub7_45 : sub7 [-3, 0, 2] = true := by decide +kernel
theorem sub7_46 : sub7 [-3, 0, 3] = true := by decide +kernel
theorem sub7_47 : sub7 [-3, 0, 4] = true := by decide +kernel
theorem sub7_48 : sub7 [-3, 0, 5] = true := by decide +kernel
theorem sub7_49 : sub7 [-3, 0, 6] = true := by decide +kernel
theorem sub7_50 : sub7 [-3, 0, 7] = true := by decide +kernel
theorem sub7_51 : sub7 [-3, 1] = true := by decide +kernel
theorem sub7_52 : sub7 [-3, 2] = true := by decide +kernel
theorem sub7_53 : sub7 [-3, 3] = true := by decide +kernel
theorem sub7_54 : sub7 [-3, 4] = true := by decide +kernel
theorem sub7_55 : sub7 [-2, -6] = true := by decide +kernel
theorem sub7_56 : sub7 [-2, -5] = true := by decide +kernel
theorem sub7_57 : sub7 [-2, -4] = true := by decide +kernel
theorem sub7_58 : sub7 [-2, -3] = true := by decide +kernel
theorem sub7_59 : sub7 [-2, -2, -7] = true := by decide +kernel
theorem sub7_60 : sub7 [-2, -2, -6] = true := by decide +kernel
theorem sub7_61 : sub7 [-2, -2, -5] = true := by decide +kernel
theorem sub7_62 : sub7 [-2, -2, -4] = true := by decide +kernel
theorem sub7_63 : sub7 [-2, -2, -3] = true := by decide +kernel
theorem sb7_1 : ∀ q ∈ blk7_1, sub7 q = true := by
  unfold blk7_1
  exact List.forall_mem_cons.2 ⟨sub7_32, List.forall_mem_cons.2 ⟨sub7_33, List.forall_mem_cons.2 ⟨sub7_34, List.forall_mem_cons.2 ⟨sub7_35, List.forall_mem_cons.2 ⟨sub7_36, List.forall_mem_cons.2 ⟨sub7_37, List.forall_mem_cons.2 ⟨sub7_38, List.forall_mem_cons.2 ⟨sub7_39, List.forall_mem_cons.2 ⟨sub7_40, List.forall_mem_cons.2 ⟨sub7_41, List.forall_mem_cons.2 ⟨sub7_42, List.forall_mem_cons.2 ⟨sub7_43, List.forall_mem_cons.2 ⟨sub7_44, List.forall_mem_cons.2 ⟨sub7_45, List.forall_mem_cons.2 ⟨sub7_46, List.forall_mem_cons.2 ⟨sub7_47, List.forall_mem_cons.2 ⟨sub7_48, List.forall_mem_cons.2 ⟨sub7_49, List.forall_mem_cons.2 ⟨sub7_50, List.forall_mem_cons.2 ⟨sub7_51, List.forall_mem_cons.2 ⟨sub7_52, List.forall_mem_cons.2 ⟨sub7_53, List.forall_mem_cons.2 ⟨sub7_54, List.forall_mem_cons.2 ⟨sub7_55, List.forall_mem_cons.2 ⟨sub7_56, List.forall_mem_cons.2 ⟨sub7_57, List.forall_mem_cons.2 ⟨sub7_58, List.forall_mem_cons.2 ⟨sub7_59, List.forall_mem_cons.2 ⟨sub7_60, List.forall_mem_cons.2 ⟨sub7_61, List.forall_mem_cons.2 ⟨sub7_62, List.forall_mem_cons.2 ⟨sub7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_64 : sub7 [-2, -2, -2] = true := by decide +kernel
theorem sub7_65 : sub7 [-2, -2, -1] = true := by decide +kernel
theorem sub7_66 : sub7 [-2, -2, 0] = true := by decide +kernel
theorem sub7_67 : sub7 [-2, -2, 1] = true := by decide +kernel
theorem sub7_68 : sub7 [-2, -2, 2] = true := by decide +kernel
theorem sub7_69 : sub7 [-2, -2, 3] = true := by decide +kernel
theorem sub7_70 : sub7 [-2, -2, 4] = true := by decide +kernel
theorem sub7_71 : sub7 [-2, -2, 5] = true := by decide +kernel
theorem sub7_72 : sub7 [-2, -2, 6] = true := by decide +kernel
theorem sub7_73 : sub7 [-2, -1, -7] = true := by decide +kernel
theorem sub7_74 : sub7 [-2, -1, -6] = true := by decide +kernel
theorem sub7_75 : sub7 [-2, -1, -5] = true := by decide +kernel
theorem sub7_76 : sub7 [-2, -1, -4] = true := by decide +kernel
theorem sub7_77 : sub7 [-2, -1, -3] = true := by decide +kernel
theorem sub7_78 : sub7 [-2, -1, -2] = true := by decide +kernel
theorem sub7_79 : sub7 [-2, -1, -1] = true := by decide +kernel
theorem sub7_80 : sub7 [-2, -1, 0] = true := by decide +kernel
theorem sub7_81 : sub7 [-2, -1, 1] = true := by decide +kernel
theorem sub7_82 : sub7 [-2, -1, 2] = true := by decide +kernel
theorem sub7_83 : sub7 [-2, -1, 3] = true := by decide +kernel
theorem sub7_84 : sub7 [-2, -1, 4] = true := by decide +kernel
theorem sub7_85 : sub7 [-2, -1, 5] = true := by decide +kernel
theorem sub7_86 : sub7 [-2, -1, 6] = true := by decide +kernel
theorem sub7_87 : sub7 [-2, -1, 7] = true := by decide +kernel
theorem sub7_88 : sub7 [-2, 0, -7] = true := by decide +kernel
theorem sub7_89 : sub7 [-2, 0, -6] = true := by decide +kernel
theorem sub7_90 : sub7 [-2, 0, -5] = true := by decide +kernel
theorem sub7_91 : sub7 [-2, 0, -4] = true := by decide +kernel
theorem sub7_92 : sub7 [-2, 0, -3] = true := by decide +kernel
theorem sub7_93 : sub7 [-2, 0, -2] = true := by decide +kernel
theorem sub7_94 : sub7 [-2, 0, -1] = true := by decide +kernel
theorem sub7_95 : sub7 [-2, 0, 0] = true := by decide +kernel
theorem sb7_2 : ∀ q ∈ blk7_2, sub7 q = true := by
  unfold blk7_2
  exact List.forall_mem_cons.2 ⟨sub7_64, List.forall_mem_cons.2 ⟨sub7_65, List.forall_mem_cons.2 ⟨sub7_66, List.forall_mem_cons.2 ⟨sub7_67, List.forall_mem_cons.2 ⟨sub7_68, List.forall_mem_cons.2 ⟨sub7_69, List.forall_mem_cons.2 ⟨sub7_70, List.forall_mem_cons.2 ⟨sub7_71, List.forall_mem_cons.2 ⟨sub7_72, List.forall_mem_cons.2 ⟨sub7_73, List.forall_mem_cons.2 ⟨sub7_74, List.forall_mem_cons.2 ⟨sub7_75, List.forall_mem_cons.2 ⟨sub7_76, List.forall_mem_cons.2 ⟨sub7_77, List.forall_mem_cons.2 ⟨sub7_78, List.forall_mem_cons.2 ⟨sub7_79, List.forall_mem_cons.2 ⟨sub7_80, List.forall_mem_cons.2 ⟨sub7_81, List.forall_mem_cons.2 ⟨sub7_82, List.forall_mem_cons.2 ⟨sub7_83, List.forall_mem_cons.2 ⟨sub7_84, List.forall_mem_cons.2 ⟨sub7_85, List.forall_mem_cons.2 ⟨sub7_86, List.forall_mem_cons.2 ⟨sub7_87, List.forall_mem_cons.2 ⟨sub7_88, List.forall_mem_cons.2 ⟨sub7_89, List.forall_mem_cons.2 ⟨sub7_90, List.forall_mem_cons.2 ⟨sub7_91, List.forall_mem_cons.2 ⟨sub7_92, List.forall_mem_cons.2 ⟨sub7_93, List.forall_mem_cons.2 ⟨sub7_94, List.forall_mem_cons.2 ⟨sub7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_96 : sub7 [-2, 0, 1] = true := by decide +kernel
theorem sub7_97 : sub7 [-2, 0, 2] = true := by decide +kernel
theorem sub7_98 : sub7 [-2, 0, 3] = true := by decide +kernel
theorem sub7_99 : sub7 [-2, 0, 4] = true := by decide +kernel
theorem sub7_100 : sub7 [-2, 0, 5] = true := by decide +kernel
theorem sub7_101 : sub7 [-2, 0, 6] = true := by decide +kernel
theorem sub7_102 : sub7 [-2, 0, 7] = true := by decide +kernel
theorem sub7_103 : sub7 [-2, 1, -6] = true := by decide +kernel
theorem sub7_104 : sub7 [-2, 1, -5] = true := by decide +kernel
theorem sub7_105 : sub7 [-2, 1, -4] = true := by decide +kernel
theorem sub7_106 : sub7 [-2, 1, -3] = true := by decide +kernel
theorem sub7_107 : sub7 [-2, 1, -2] = true := by decide +kernel
theorem sub7_108 : sub7 [-2, 1, -1] = true := by decide +kernel
theorem sub7_109 : sub7 [-2, 1, 0] = true := by decide +kernel
theorem sub7_110 : sub7 [-2, 1, 1] = true := by decide +kernel
theorem sub7_111 : sub7 [-2, 1, 2] = true := by decide +kernel
theorem sub7_112 : sub7 [-2, 1, 3] = true := by decide +kernel
theorem sub7_113 : sub7 [-2, 1, 4] = true := by decide +kernel
theorem sub7_114 : sub7 [-2, 1, 5] = true := by decide +kernel
theorem sub7_115 : sub7 [-2, 1, 6] = true := by decide +kernel
theorem sub7_116 : sub7 [-2, 1, 7] = true := by decide +kernel
theorem sub7_117 : sub7 [-2, 2, -5] = true := by decide +kernel
theorem sub7_118 : sub7 [-2, 2, -4] = true := by decide +kernel
theorem sub7_119 : sub7 [-2, 2, -3] = true := by decide +kernel
theorem sub7_120 : sub7 [-2, 2, -2] = true := by decide +kernel
theorem sub7_121 : sub7 [-2, 2, -1] = true := by decide +kernel
theorem sub7_122 : sub7 [-2, 2, 0] = true := by decide +kernel
theorem sub7_123 : sub7 [-2, 2, 1] = true := by decide +kernel
theorem sub7_124 : sub7 [-2, 2, 2] = true := by decide +kernel
theorem sub7_125 : sub7 [-2, 2, 3] = true := by decide +kernel
theorem sub7_126 : sub7 [-2, 2, 4] = true := by decide +kernel
theorem sub7_127 : sub7 [-2, 2, 5] = true := by decide +kernel
theorem sb7_3 : ∀ q ∈ blk7_3, sub7 q = true := by
  unfold blk7_3
  exact List.forall_mem_cons.2 ⟨sub7_96, List.forall_mem_cons.2 ⟨sub7_97, List.forall_mem_cons.2 ⟨sub7_98, List.forall_mem_cons.2 ⟨sub7_99, List.forall_mem_cons.2 ⟨sub7_100, List.forall_mem_cons.2 ⟨sub7_101, List.forall_mem_cons.2 ⟨sub7_102, List.forall_mem_cons.2 ⟨sub7_103, List.forall_mem_cons.2 ⟨sub7_104, List.forall_mem_cons.2 ⟨sub7_105, List.forall_mem_cons.2 ⟨sub7_106, List.forall_mem_cons.2 ⟨sub7_107, List.forall_mem_cons.2 ⟨sub7_108, List.forall_mem_cons.2 ⟨sub7_109, List.forall_mem_cons.2 ⟨sub7_110, List.forall_mem_cons.2 ⟨sub7_111, List.forall_mem_cons.2 ⟨sub7_112, List.forall_mem_cons.2 ⟨sub7_113, List.forall_mem_cons.2 ⟨sub7_114, List.forall_mem_cons.2 ⟨sub7_115, List.forall_mem_cons.2 ⟨sub7_116, List.forall_mem_cons.2 ⟨sub7_117, List.forall_mem_cons.2 ⟨sub7_118, List.forall_mem_cons.2 ⟨sub7_119, List.forall_mem_cons.2 ⟨sub7_120, List.forall_mem_cons.2 ⟨sub7_121, List.forall_mem_cons.2 ⟨sub7_122, List.forall_mem_cons.2 ⟨sub7_123, List.forall_mem_cons.2 ⟨sub7_124, List.forall_mem_cons.2 ⟨sub7_125, List.forall_mem_cons.2 ⟨sub7_126, List.forall_mem_cons.2 ⟨sub7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C059
