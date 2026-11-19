import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_0_608 : subd11_0 [-2, -3, 3] = true := by decide +kernel
theorem subd11_0_609 : subd11_0 [-2, -3, 4] = true := by decide +kernel
theorem subd11_0_610 : subd11_0 [-2, -3, 5] = true := by decide +kernel
theorem subd11_0_611 : subd11_0 [-2, -3, 6] = true := by decide +kernel
theorem subd11_0_612 : subd11_0 [-2, -3, 7] = true := by decide +kernel
theorem subd11_0_613 : subd11_0 [-2, -2, -9] = true := by decide +kernel
theorem subd11_0_614 : subd11_0 [-2, -2, -8] = true := by decide +kernel
theorem subd11_0_615 : subd11_0 [-2, -2, -7] = true := by decide +kernel
theorem subd11_0_616 : subd11_0 [-2, -2, -6] = true := by decide +kernel
theorem subd11_0_617 : subd11_0 [-2, -2, -5] = true := by decide +kernel
theorem subd11_0_618 : subd11_0 [-2, -2, -4] = true := by decide +kernel
theorem subd11_0_619 : subd11_0 [-2, -2, -3] = true := by decide +kernel
theorem subd11_0_620 : subd11_0 [-2, -2, -2] = true := by decide +kernel
theorem subd11_0_621 : subd11_0 [-2, -2, -1] = true := by decide +kernel
theorem subd11_0_622 : subd11_0 [-2, -2, 0] = true := by decide +kernel
theorem subd11_0_623 : subd11_0 [-2, -2, 1] = true := by decide +kernel
theorem subd11_0_624 : subd11_0 [-2, -2, 2] = true := by decide +kernel
theorem subd11_0_625 : subd11_0 [-2, -2, 3] = true := by decide +kernel
theorem subd11_0_626 : subd11_0 [-2, -2, 4] = true := by decide +kernel
theorem subd11_0_627 : subd11_0 [-2, -2, 5] = true := by decide +kernel
theorem subd11_0_628 : subd11_0 [-2, -2, 6] = true := by decide +kernel
theorem subd11_0_629 : subd11_0 [-2, -2, 7] = true := by decide +kernel
theorem subd11_0_630 : subd11_0 [-2, -2, 8] = true := by decide +kernel
theorem subd11_0_631 : subd11_0 [-2, -1, -9] = true := by decide +kernel
theorem subd11_0_632 : subd11_0 [-2, -1, -8] = true := by decide +kernel
theorem subd11_0_633 : subd11_0 [-2, -1, -7] = true := by decide +kernel
theorem subd11_0_634 : subd11_0 [-2, -1, -6] = true := by decide +kernel
theorem subd11_0_635 : subd11_0 [-2, -1, -5] = true := by decide +kernel
theorem subd11_0_636 : subd11_0 [-2, -1, -4] = true := by decide +kernel
theorem subd11_0_637 : subd11_0 [-2, -1, -3] = true := by decide +kernel
theorem subd11_0_638 : subd11_0 [-2, -1, -2] = true := by decide +kernel
theorem subd11_0_639 : subd11_0 [-2, -1, -1] = true := by decide +kernel
theorem sbd11_0_19 : ∀ q ∈ blkd11_0_19, subd11_0 q = true := by
  unfold blkd11_0_19
  exact List.forall_mem_cons.2 ⟨subd11_0_608, List.forall_mem_cons.2 ⟨subd11_0_609, List.forall_mem_cons.2 ⟨subd11_0_610, List.forall_mem_cons.2 ⟨subd11_0_611, List.forall_mem_cons.2 ⟨subd11_0_612, List.forall_mem_cons.2 ⟨subd11_0_613, List.forall_mem_cons.2 ⟨subd11_0_614, List.forall_mem_cons.2 ⟨subd11_0_615, List.forall_mem_cons.2 ⟨subd11_0_616, List.forall_mem_cons.2 ⟨subd11_0_617, List.forall_mem_cons.2 ⟨subd11_0_618, List.forall_mem_cons.2 ⟨subd11_0_619, List.forall_mem_cons.2 ⟨subd11_0_620, List.forall_mem_cons.2 ⟨subd11_0_621, List.forall_mem_cons.2 ⟨subd11_0_622, List.forall_mem_cons.2 ⟨subd11_0_623, List.forall_mem_cons.2 ⟨subd11_0_624, List.forall_mem_cons.2 ⟨subd11_0_625, List.forall_mem_cons.2 ⟨subd11_0_626, List.forall_mem_cons.2 ⟨subd11_0_627, List.forall_mem_cons.2 ⟨subd11_0_628, List.forall_mem_cons.2 ⟨subd11_0_629, List.forall_mem_cons.2 ⟨subd11_0_630, List.forall_mem_cons.2 ⟨subd11_0_631, List.forall_mem_cons.2 ⟨subd11_0_632, List.forall_mem_cons.2 ⟨subd11_0_633, List.forall_mem_cons.2 ⟨subd11_0_634, List.forall_mem_cons.2 ⟨subd11_0_635, List.forall_mem_cons.2 ⟨subd11_0_636, List.forall_mem_cons.2 ⟨subd11_0_637, List.forall_mem_cons.2 ⟨subd11_0_638, List.forall_mem_cons.2 ⟨subd11_0_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_640 : subd11_0 [-2, -1, 0] = true := by decide +kernel
theorem subd11_0_641 : subd11_0 [-2, -1, 1] = true := by decide +kernel
theorem subd11_0_642 : subd11_0 [-2, -1, 2] = true := by decide +kernel
theorem subd11_0_643 : subd11_0 [-2, -1, 3] = true := by decide +kernel
theorem subd11_0_644 : subd11_0 [-2, -1, 4] = true := by decide +kernel
theorem subd11_0_645 : subd11_0 [-2, -1, 5] = true := by decide +kernel
theorem subd11_0_646 : subd11_0 [-2, -1, 6] = true := by decide +kernel
theorem subd11_0_647 : subd11_0 [-2, -1, 7] = true := by decide +kernel
theorem subd11_0_648 : subd11_0 [-2, -1, 8] = true := by decide +kernel
theorem subd11_0_649 : subd11_0 [-2, 0, -9] = true := by decide +kernel
theorem subd11_0_650 : subd11_0 [-2, 0, -8] = true := by decide +kernel
theorem subd11_0_651 : subd11_0 [-2, 0, -7] = true := by decide +kernel
theorem subd11_0_652 : subd11_0 [-2, 0, -6] = true := by decide +kernel
theorem subd11_0_653 : subd11_0 [-2, 0, -5] = true := by decide +kernel
theorem subd11_0_654 : subd11_0 [-2, 0, -4] = true := by decide +kernel
theorem subd11_0_655 : subd11_0 [-2, 0, -3] = true := by decide +kernel
theorem subd11_0_656 : subd11_0 [-2, 0, -2] = true := by decide +kernel
theorem subd11_0_657 : subd11_0 [-2, 0, -1] = true := by decide +kernel
theorem subd11_0_658 : subd11_0 [-2, 0, 0] = true := by decide +kernel
theorem subd11_0_659 : subd11_0 [-2, 0, 1] = true := by decide +kernel
theorem subd11_0_660 : subd11_0 [-2, 0, 2] = true := by decide +kernel
theorem subd11_0_661 : subd11_0 [-2, 0, 3] = true := by decide +kernel
theorem subd11_0_662 : subd11_0 [-2, 0, 4] = true := by decide +kernel
theorem subd11_0_663 : subd11_0 [-2, 0, 5] = true := by decide +kernel
theorem subd11_0_664 : subd11_0 [-2, 0, 6] = true := by decide +kernel
theorem subd11_0_665 : subd11_0 [-2, 0, 7] = true := by decide +kernel
theorem subd11_0_666 : subd11_0 [-2, 1, -9] = true := by decide +kernel
theorem subd11_0_667 : subd11_0 [-2, 1, -8] = true := by decide +kernel
theorem subd11_0_668 : subd11_0 [-2, 1, -7] = true := by decide +kernel
theorem subd11_0_669 : subd11_0 [-2, 1, -6] = true := by decide +kernel
theorem subd11_0_670 : subd11_0 [-2, 1, -5] = true := by decide +kernel
theorem subd11_0_671 : subd11_0 [-2, 1, -4] = true := by decide +kernel
theorem sbd11_0_20 : ∀ q ∈ blkd11_0_20, subd11_0 q = true := by
  unfold blkd11_0_20
  exact List.forall_mem_cons.2 ⟨subd11_0_640, List.forall_mem_cons.2 ⟨subd11_0_641, List.forall_mem_cons.2 ⟨subd11_0_642, List.forall_mem_cons.2 ⟨subd11_0_643, List.forall_mem_cons.2 ⟨subd11_0_644, List.forall_mem_cons.2 ⟨subd11_0_645, List.forall_mem_cons.2 ⟨subd11_0_646, List.forall_mem_cons.2 ⟨subd11_0_647, List.forall_mem_cons.2 ⟨subd11_0_648, List.forall_mem_cons.2 ⟨subd11_0_649, List.forall_mem_cons.2 ⟨subd11_0_650, List.forall_mem_cons.2 ⟨subd11_0_651, List.forall_mem_cons.2 ⟨subd11_0_652, List.forall_mem_cons.2 ⟨subd11_0_653, List.forall_mem_cons.2 ⟨subd11_0_654, List.forall_mem_cons.2 ⟨subd11_0_655, List.forall_mem_cons.2 ⟨subd11_0_656, List.forall_mem_cons.2 ⟨subd11_0_657, List.forall_mem_cons.2 ⟨subd11_0_658, List.forall_mem_cons.2 ⟨subd11_0_659, List.forall_mem_cons.2 ⟨subd11_0_660, List.forall_mem_cons.2 ⟨subd11_0_661, List.forall_mem_cons.2 ⟨subd11_0_662, List.forall_mem_cons.2 ⟨subd11_0_663, List.forall_mem_cons.2 ⟨subd11_0_664, List.forall_mem_cons.2 ⟨subd11_0_665, List.forall_mem_cons.2 ⟨subd11_0_666, List.forall_mem_cons.2 ⟨subd11_0_667, List.forall_mem_cons.2 ⟨subd11_0_668, List.forall_mem_cons.2 ⟨subd11_0_669, List.forall_mem_cons.2 ⟨subd11_0_670, List.forall_mem_cons.2 ⟨subd11_0_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_672 : subd11_0 [-2, 1, -3] = true := by decide +kernel
theorem subd11_0_673 : subd11_0 [-2, 1, -2] = true := by decide +kernel
theorem subd11_0_674 : subd11_0 [-2, 1, -1] = true := by decide +kernel
theorem subd11_0_675 : subd11_0 [-2, 1, 0] = true := by decide +kernel
theorem subd11_0_676 : subd11_0 [-2, 1, 1] = true := by decide +kernel
theorem subd11_0_677 : subd11_0 [-2, 1, 2] = true := by decide +kernel
theorem subd11_0_678 : subd11_0 [-2, 1, 3] = true := by decide +kernel
theorem subd11_0_679 : subd11_0 [-2, 1, 4] = true := by decide +kernel
theorem subd11_0_680 : subd11_0 [-2, 1, 5] = true := by decide +kernel
theorem subd11_0_681 : subd11_0 [-2, 1, 6] = true := by decide +kernel
theorem subd11_0_682 : subd11_0 [-2, 1, 7] = true := by decide +kernel
theorem subd11_0_683 : subd11_0 [-2, 2, -9] = true := by decide +kernel
theorem subd11_0_684 : subd11_0 [-2, 2, -8] = true := by decide +kernel
theorem subd11_0_685 : subd11_0 [-2, 2, -7] = true := by decide +kernel
theorem subd11_0_686 : subd11_0 [-2, 2, -6] = true := by decide +kernel
theorem subd11_0_687 : subd11_0 [-2, 2, -5] = true := by decide +kernel
theorem subd11_0_688 : subd11_0 [-2, 2, -4] = true := by decide +kernel
theorem subd11_0_689 : subd11_0 [-2, 2, -3] = true := by decide +kernel
theorem subd11_0_690 : subd11_0 [-2, 2, -2] = true := by decide +kernel
theorem subd11_0_691 : subd11_0 [-2, 2, -1] = true := by decide +kernel
theorem subd11_0_692 : subd11_0 [-2, 2, 0] = true := by decide +kernel
theorem subd11_0_693 : subd11_0 [-2, 2, 1] = true := by decide +kernel
theorem subd11_0_694 : subd11_0 [-2, 2, 2] = true := by decide +kernel
theorem subd11_0_695 : subd11_0 [-2, 2, 3] = true := by decide +kernel
theorem subd11_0_696 : subd11_0 [-2, 2, 4] = true := by decide +kernel
theorem subd11_0_697 : subd11_0 [-2, 2, 5] = true := by decide +kernel
theorem subd11_0_698 : subd11_0 [-2, 2, 6] = true := by decide +kernel
theorem subd11_0_699 : subd11_0 [-2, 2, 7] = true := by decide +kernel
theorem subd11_0_700 : subd11_0 [-2, 3, -9] = true := by decide +kernel
theorem subd11_0_701 : subd11_0 [-2, 3, -8] = true := by decide +kernel
theorem subd11_0_702 : subd11_0 [-2, 3, -7] = true := by decide +kernel
theorem subd11_0_703 : subd11_0 [-2, 3, -6] = true := by decide +kernel
theorem sbd11_0_21 : ∀ q ∈ blkd11_0_21, subd11_0 q = true := by
  unfold blkd11_0_21
  exact List.forall_mem_cons.2 ⟨subd11_0_672, List.forall_mem_cons.2 ⟨subd11_0_673, List.forall_mem_cons.2 ⟨subd11_0_674, List.forall_mem_cons.2 ⟨subd11_0_675, List.forall_mem_cons.2 ⟨subd11_0_676, List.forall_mem_cons.2 ⟨subd11_0_677, List.forall_mem_cons.2 ⟨subd11_0_678, List.forall_mem_cons.2 ⟨subd11_0_679, List.forall_mem_cons.2 ⟨subd11_0_680, List.forall_mem_cons.2 ⟨subd11_0_681, List.forall_mem_cons.2 ⟨subd11_0_682, List.forall_mem_cons.2 ⟨subd11_0_683, List.forall_mem_cons.2 ⟨subd11_0_684, List.forall_mem_cons.2 ⟨subd11_0_685, List.forall_mem_cons.2 ⟨subd11_0_686, List.forall_mem_cons.2 ⟨subd11_0_687, List.forall_mem_cons.2 ⟨subd11_0_688, List.forall_mem_cons.2 ⟨subd11_0_689, List.forall_mem_cons.2 ⟨subd11_0_690, List.forall_mem_cons.2 ⟨subd11_0_691, List.forall_mem_cons.2 ⟨subd11_0_692, List.forall_mem_cons.2 ⟨subd11_0_693, List.forall_mem_cons.2 ⟨subd11_0_694, List.forall_mem_cons.2 ⟨subd11_0_695, List.forall_mem_cons.2 ⟨subd11_0_696, List.forall_mem_cons.2 ⟨subd11_0_697, List.forall_mem_cons.2 ⟨subd11_0_698, List.forall_mem_cons.2 ⟨subd11_0_699, List.forall_mem_cons.2 ⟨subd11_0_700, List.forall_mem_cons.2 ⟨subd11_0_701, List.forall_mem_cons.2 ⟨subd11_0_702, List.forall_mem_cons.2 ⟨subd11_0_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_704 : subd11_0 [-2, 3, -5] = true := by decide +kernel
theorem subd11_0_705 : subd11_0 [-2, 3, -4] = true := by decide +kernel
theorem subd11_0_706 : subd11_0 [-2, 3, -3] = true := by decide +kernel
theorem subd11_0_707 : subd11_0 [-2, 3, -2] = true := by decide +kernel
theorem subd11_0_708 : subd11_0 [-2, 3, -1] = true := by decide +kernel
theorem subd11_0_709 : subd11_0 [-2, 3, 0] = true := by decide +kernel
theorem subd11_0_710 : subd11_0 [-2, 3, 1] = true := by decide +kernel
theorem subd11_0_711 : subd11_0 [-2, 3, 2] = true := by decide +kernel
theorem subd11_0_712 : subd11_0 [-2, 3, 3] = true := by decide +kernel
theorem subd11_0_713 : subd11_0 [-2, 3, 4] = true := by decide +kernel
theorem subd11_0_714 : subd11_0 [-2, 3, 5] = true := by decide +kernel
theorem subd11_0_715 : subd11_0 [-2, 3, 6] = true := by decide +kernel
theorem subd11_0_716 : subd11_0 [-2, 3, 7] = true := by decide +kernel
theorem subd11_0_717 : subd11_0 [-2, 4, -8] = true := by decide +kernel
theorem subd11_0_718 : subd11_0 [-2, 4, -7] = true := by decide +kernel
theorem subd11_0_719 : subd11_0 [-2, 4, -6] = true := by decide +kernel
theorem subd11_0_720 : subd11_0 [-2, 4, -5] = true := by decide +kernel
theorem subd11_0_721 : subd11_0 [-2, 4, -4] = true := by decide +kernel
theorem subd11_0_722 : subd11_0 [-2, 4, -3] = true := by decide +kernel
theorem subd11_0_723 : subd11_0 [-2, 4, -2] = true := by decide +kernel
theorem subd11_0_724 : subd11_0 [-2, 4, -1] = true := by decide +kernel
theorem subd11_0_725 : subd11_0 [-2, 4, 0] = true := by decide +kernel
theorem subd11_0_726 : subd11_0 [-2, 4, 1] = true := by decide +kernel
theorem subd11_0_727 : subd11_0 [-2, 4, 2] = true := by decide +kernel
theorem subd11_0_728 : subd11_0 [-2, 4, 3] = true := by decide +kernel
theorem subd11_0_729 : subd11_0 [-2, 4, 4] = true := by decide +kernel
theorem subd11_0_730 : subd11_0 [-2, 4, 5] = true := by decide +kernel
theorem subd11_0_731 : subd11_0 [-2, 4, 6] = true := by decide +kernel
theorem subd11_0_732 : subd11_0 [-2, 5, -8] = true := by decide +kernel
theorem subd11_0_733 : subd11_0 [-2, 5, -7] = true := by decide +kernel
theorem subd11_0_734 : subd11_0 [-2, 5, -6] = true := by decide +kernel
theorem subd11_0_735 : subd11_0 [-2, 5, -5] = true := by decide +kernel
theorem sbd11_0_22 : ∀ q ∈ blkd11_0_22, subd11_0 q = true := by
  unfold blkd11_0_22
  exact List.forall_mem_cons.2 ⟨subd11_0_704, List.forall_mem_cons.2 ⟨subd11_0_705, List.forall_mem_cons.2 ⟨subd11_0_706, List.forall_mem_cons.2 ⟨subd11_0_707, List.forall_mem_cons.2 ⟨subd11_0_708, List.forall_mem_cons.2 ⟨subd11_0_709, List.forall_mem_cons.2 ⟨subd11_0_710, List.forall_mem_cons.2 ⟨subd11_0_711, List.forall_mem_cons.2 ⟨subd11_0_712, List.forall_mem_cons.2 ⟨subd11_0_713, List.forall_mem_cons.2 ⟨subd11_0_714, List.forall_mem_cons.2 ⟨subd11_0_715, List.forall_mem_cons.2 ⟨subd11_0_716, List.forall_mem_cons.2 ⟨subd11_0_717, List.forall_mem_cons.2 ⟨subd11_0_718, List.forall_mem_cons.2 ⟨subd11_0_719, List.forall_mem_cons.2 ⟨subd11_0_720, List.forall_mem_cons.2 ⟨subd11_0_721, List.forall_mem_cons.2 ⟨subd11_0_722, List.forall_mem_cons.2 ⟨subd11_0_723, List.forall_mem_cons.2 ⟨subd11_0_724, List.forall_mem_cons.2 ⟨subd11_0_725, List.forall_mem_cons.2 ⟨subd11_0_726, List.forall_mem_cons.2 ⟨subd11_0_727, List.forall_mem_cons.2 ⟨subd11_0_728, List.forall_mem_cons.2 ⟨subd11_0_729, List.forall_mem_cons.2 ⟨subd11_0_730, List.forall_mem_cons.2 ⟨subd11_0_731, List.forall_mem_cons.2 ⟨subd11_0_732, List.forall_mem_cons.2 ⟨subd11_0_733, List.forall_mem_cons.2 ⟨subd11_0_734, List.forall_mem_cons.2 ⟨subd11_0_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_736 : subd11_0 [-2, 5, -4] = true := by decide +kernel
theorem subd11_0_737 : subd11_0 [-2, 5, -3] = true := by decide +kernel
theorem subd11_0_738 : subd11_0 [-2, 5, -2] = true := by decide +kernel
theorem subd11_0_739 : subd11_0 [-2, 5, -1] = true := by decide +kernel
theorem subd11_0_740 : subd11_0 [-2, 5, 0] = true := by decide +kernel
theorem subd11_0_741 : subd11_0 [-2, 5, 1] = true := by decide +kernel
theorem subd11_0_742 : subd11_0 [-2, 5, 2] = true := by decide +kernel
theorem subd11_0_743 : subd11_0 [-2, 5, 3] = true := by decide +kernel
theorem subd11_0_744 : subd11_0 [-2, 5, 4] = true := by decide +kernel
theorem subd11_0_745 : subd11_0 [-2, 5, 5] = true := by decide +kernel
theorem subd11_0_746 : subd11_0 [-2, 6] = true := by decide +kernel
theorem subd11_0_747 : subd11_0 [-2, 7] = true := by decide +kernel
theorem subd11_0_748 : subd11_0 [-2, 8] = true := by decide +kernel
theorem subd11_0_749 : subd11_0 [-1, -10] = true := by decide +kernel
theorem subd11_0_750 : subd11_0 [-1, -9] = true := by decide +kernel
theorem subd11_0_751 : subd11_0 [-1, -8] = true := by decide +kernel
theorem subd11_0_752 : subd11_0 [-1, -7, -7] = true := by decide +kernel
theorem subd11_0_753 : subd11_0 [-1, -7, -6] = true := by decide +kernel
theorem subd11_0_754 : subd11_0 [-1, -7, -5] = true := by decide +kernel
theorem subd11_0_755 : subd11_0 [-1, -7, -4] = true := by decide +kernel
theorem subd11_0_756 : subd11_0 [-1, -7, -3] = true := by decide +kernel
theorem subd11_0_757 : subd11_0 [-1, -7, -2] = true := by decide +kernel
theorem subd11_0_758 : subd11_0 [-1, -7, -1] = true := by decide +kernel
theorem subd11_0_759 : subd11_0 [-1, -7, 0] = true := by decide +kernel
theorem subd11_0_760 : subd11_0 [-1, -7, 1] = true := by decide +kernel
theorem subd11_0_761 : subd11_0 [-1, -7, 2] = true := by decide +kernel
theorem subd11_0_762 : subd11_0 [-1, -7, 3] = true := by decide +kernel
theorem subd11_0_763 : subd11_0 [-1, -7, 4] = true := by decide +kernel
theorem subd11_0_764 : subd11_0 [-1, -7, 5] = true := by decide +kernel
theorem subd11_0_765 : subd11_0 [-1, -7, 6] = true := by decide +kernel
theorem subd11_0_766 : subd11_0 [-1, -6, -7] = true := by decide +kernel
theorem subd11_0_767 : subd11_0 [-1, -6, -6] = true := by decide +kernel
theorem sbd11_0_23 : ∀ q ∈ blkd11_0_23, subd11_0 q = true := by
  unfold blkd11_0_23
  exact List.forall_mem_cons.2 ⟨subd11_0_736, List.forall_mem_cons.2 ⟨subd11_0_737, List.forall_mem_cons.2 ⟨subd11_0_738, List.forall_mem_cons.2 ⟨subd11_0_739, List.forall_mem_cons.2 ⟨subd11_0_740, List.forall_mem_cons.2 ⟨subd11_0_741, List.forall_mem_cons.2 ⟨subd11_0_742, List.forall_mem_cons.2 ⟨subd11_0_743, List.forall_mem_cons.2 ⟨subd11_0_744, List.forall_mem_cons.2 ⟨subd11_0_745, List.forall_mem_cons.2 ⟨subd11_0_746, List.forall_mem_cons.2 ⟨subd11_0_747, List.forall_mem_cons.2 ⟨subd11_0_748, List.forall_mem_cons.2 ⟨subd11_0_749, List.forall_mem_cons.2 ⟨subd11_0_750, List.forall_mem_cons.2 ⟨subd11_0_751, List.forall_mem_cons.2 ⟨subd11_0_752, List.forall_mem_cons.2 ⟨subd11_0_753, List.forall_mem_cons.2 ⟨subd11_0_754, List.forall_mem_cons.2 ⟨subd11_0_755, List.forall_mem_cons.2 ⟨subd11_0_756, List.forall_mem_cons.2 ⟨subd11_0_757, List.forall_mem_cons.2 ⟨subd11_0_758, List.forall_mem_cons.2 ⟨subd11_0_759, List.forall_mem_cons.2 ⟨subd11_0_760, List.forall_mem_cons.2 ⟨subd11_0_761, List.forall_mem_cons.2 ⟨subd11_0_762, List.forall_mem_cons.2 ⟨subd11_0_763, List.forall_mem_cons.2 ⟨subd11_0_764, List.forall_mem_cons.2 ⟨subd11_0_765, List.forall_mem_cons.2 ⟨subd11_0_766, List.forall_mem_cons.2 ⟨subd11_0_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_768 : subd11_0 [-1, -6, -5] = true := by decide +kernel
theorem subd11_0_769 : subd11_0 [-1, -6, -4] = true := by decide +kernel
theorem subd11_0_770 : subd11_0 [-1, -6, -3] = true := by decide +kernel
theorem subd11_0_771 : subd11_0 [-1, -6, -2] = true := by decide +kernel
theorem subd11_0_772 : subd11_0 [-1, -6, -1] = true := by decide +kernel
theorem subd11_0_773 : subd11_0 [-1, -6, 0] = true := by decide +kernel
theorem subd11_0_774 : subd11_0 [-1, -6, 1] = true := by decide +kernel
theorem subd11_0_775 : subd11_0 [-1, -6, 2] = true := by decide +kernel
theorem subd11_0_776 : subd11_0 [-1, -6, 3] = true := by decide +kernel
theorem subd11_0_777 : subd11_0 [-1, -6, 4] = true := by decide +kernel
theorem subd11_0_778 : subd11_0 [-1, -6, 5] = true := by decide +kernel
theorem subd11_0_779 : subd11_0 [-1, -6, 6] = true := by decide +kernel
theorem subd11_0_780 : subd11_0 [-1, -6, 7] = true := by decide +kernel
theorem subd11_0_781 : subd11_0 [-1, -5, -8] = true := by decide +kernel
theorem subd11_0_782 : subd11_0 [-1, -5, -7] = true := by decide +kernel
theorem subd11_0_783 : subd11_0 [-1, -5, -6] = true := by decide +kernel
theorem subd11_0_784 : subd11_0 [-1, -5, -5] = true := by decide +kernel
theorem subd11_0_785 : subd11_0 [-1, -5, -4] = true := by decide +kernel
theorem subd11_0_786 : subd11_0 [-1, -5, -3] = true := by decide +kernel
theorem subd11_0_787 : subd11_0 [-1, -5, -2] = true := by decide +kernel
theorem subd11_0_788 : subd11_0 [-1, -5, -1] = true := by decide +kernel
theorem subd11_0_789 : subd11_0 [-1, -5, 0] = true := by decide +kernel
theorem subd11_0_790 : subd11_0 [-1, -5, 1] = true := by decide +kernel
theorem subd11_0_791 : subd11_0 [-1, -5, 2] = true := by decide +kernel
theorem subd11_0_792 : subd11_0 [-1, -5, 3] = true := by decide +kernel
theorem subd11_0_793 : subd11_0 [-1, -5, 4] = true := by decide +kernel
theorem subd11_0_794 : subd11_0 [-1, -5, 5] = true := by decide +kernel
theorem subd11_0_795 : subd11_0 [-1, -5, 6] = true := by decide +kernel
theorem subd11_0_796 : subd11_0 [-1, -5, 7] = true := by decide +kernel
theorem subd11_0_797 : subd11_0 [-1, -4, -9] = true := by decide +kernel
theorem subd11_0_798 : subd11_0 [-1, -4, -8] = true := by decide +kernel
theorem subd11_0_799 : subd11_0 [-1, -4, -7] = true := by decide +kernel
theorem sbd11_0_24 : ∀ q ∈ blkd11_0_24, subd11_0 q = true := by
  unfold blkd11_0_24
  exact List.forall_mem_cons.2 ⟨subd11_0_768, List.forall_mem_cons.2 ⟨subd11_0_769, List.forall_mem_cons.2 ⟨subd11_0_770, List.forall_mem_cons.2 ⟨subd11_0_771, List.forall_mem_cons.2 ⟨subd11_0_772, List.forall_mem_cons.2 ⟨subd11_0_773, List.forall_mem_cons.2 ⟨subd11_0_774, List.forall_mem_cons.2 ⟨subd11_0_775, List.forall_mem_cons.2 ⟨subd11_0_776, List.forall_mem_cons.2 ⟨subd11_0_777, List.forall_mem_cons.2 ⟨subd11_0_778, List.forall_mem_cons.2 ⟨subd11_0_779, List.forall_mem_cons.2 ⟨subd11_0_780, List.forall_mem_cons.2 ⟨subd11_0_781, List.forall_mem_cons.2 ⟨subd11_0_782, List.forall_mem_cons.2 ⟨subd11_0_783, List.forall_mem_cons.2 ⟨subd11_0_784, List.forall_mem_cons.2 ⟨subd11_0_785, List.forall_mem_cons.2 ⟨subd11_0_786, List.forall_mem_cons.2 ⟨subd11_0_787, List.forall_mem_cons.2 ⟨subd11_0_788, List.forall_mem_cons.2 ⟨subd11_0_789, List.forall_mem_cons.2 ⟨subd11_0_790, List.forall_mem_cons.2 ⟨subd11_0_791, List.forall_mem_cons.2 ⟨subd11_0_792, List.forall_mem_cons.2 ⟨subd11_0_793, List.forall_mem_cons.2 ⟨subd11_0_794, List.forall_mem_cons.2 ⟨subd11_0_795, List.forall_mem_cons.2 ⟨subd11_0_796, List.forall_mem_cons.2 ⟨subd11_0_797, List.forall_mem_cons.2 ⟨subd11_0_798, List.forall_mem_cons.2 ⟨subd11_0_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_800 : subd11_0 [-1, -4, -6] = true := by decide +kernel
theorem subd11_0_801 : subd11_0 [-1, -4, -5] = true := by decide +kernel
theorem subd11_0_802 : subd11_0 [-1, -4, -4] = true := by decide +kernel
theorem subd11_0_803 : subd11_0 [-1, -4, -3] = true := by decide +kernel
theorem subd11_0_804 : subd11_0 [-1, -4, -2] = true := by decide +kernel
theorem subd11_0_805 : subd11_0 [-1, -4, -1] = true := by decide +kernel
theorem subd11_0_806 : subd11_0 [-1, -4, 0] = true := by decide +kernel
theorem subd11_0_807 : subd11_0 [-1, -4, 1] = true := by decide +kernel
theorem subd11_0_808 : subd11_0 [-1, -4, 2] = true := by decide +kernel
theorem subd11_0_809 : subd11_0 [-1, -4, 3] = true := by decide +kernel
theorem subd11_0_810 : subd11_0 [-1, -4, 4] = true := by decide +kernel
theorem subd11_0_811 : subd11_0 [-1, -4, 5] = true := by decide +kernel
theorem subd11_0_812 : subd11_0 [-1, -4, 6] = true := by decide +kernel
theorem subd11_0_813 : subd11_0 [-1, -4, 7] = true := by decide +kernel
theorem subd11_0_814 : subd11_0 [-1, -3, -9] = true := by decide +kernel
theorem subd11_0_815 : subd11_0 [-1, -3, -8] = true := by decide +kernel
theorem subd11_0_816 : subd11_0 [-1, -3, -7] = true := by decide +kernel
theorem subd11_0_817 : subd11_0 [-1, -3, -6] = true := by decide +kernel
theorem subd11_0_818 : subd11_0 [-1, -3, -5] = true := by decide +kernel
theorem subd11_0_819 : subd11_0 [-1, -3, -4] = true := by decide +kernel
theorem subd11_0_820 : subd11_0 [-1, -3, -3] = true := by decide +kernel
theorem subd11_0_821 : subd11_0 [-1, -3, -2] = true := by decide +kernel
theorem subd11_0_822 : subd11_0 [-1, -3, -1] = true := by decide +kernel
theorem subd11_0_823 : subd11_0 [-1, -3, 0] = true := by decide +kernel
theorem subd11_0_824 : subd11_0 [-1, -3, 1] = true := by decide +kernel
theorem subd11_0_825 : subd11_0 [-1, -3, 2] = true := by decide +kernel
theorem subd11_0_826 : subd11_0 [-1, -3, 3] = true := by decide +kernel
theorem subd11_0_827 : subd11_0 [-1, -3, 4] = true := by decide +kernel
theorem subd11_0_828 : subd11_0 [-1, -3, 5] = true := by decide +kernel
theorem subd11_0_829 : subd11_0 [-1, -3, 6] = true := by decide +kernel
theorem subd11_0_830 : subd11_0 [-1, -3, 7] = true := by decide +kernel
theorem subd11_0_831 : subd11_0 [-1, -3, 8] = true := by decide +kernel
theorem sbd11_0_25 : ∀ q ∈ blkd11_0_25, subd11_0 q = true := by
  unfold blkd11_0_25
  exact List.forall_mem_cons.2 ⟨subd11_0_800, List.forall_mem_cons.2 ⟨subd11_0_801, List.forall_mem_cons.2 ⟨subd11_0_802, List.forall_mem_cons.2 ⟨subd11_0_803, List.forall_mem_cons.2 ⟨subd11_0_804, List.forall_mem_cons.2 ⟨subd11_0_805, List.forall_mem_cons.2 ⟨subd11_0_806, List.forall_mem_cons.2 ⟨subd11_0_807, List.forall_mem_cons.2 ⟨subd11_0_808, List.forall_mem_cons.2 ⟨subd11_0_809, List.forall_mem_cons.2 ⟨subd11_0_810, List.forall_mem_cons.2 ⟨subd11_0_811, List.forall_mem_cons.2 ⟨subd11_0_812, List.forall_mem_cons.2 ⟨subd11_0_813, List.forall_mem_cons.2 ⟨subd11_0_814, List.forall_mem_cons.2 ⟨subd11_0_815, List.forall_mem_cons.2 ⟨subd11_0_816, List.forall_mem_cons.2 ⟨subd11_0_817, List.forall_mem_cons.2 ⟨subd11_0_818, List.forall_mem_cons.2 ⟨subd11_0_819, List.forall_mem_cons.2 ⟨subd11_0_820, List.forall_mem_cons.2 ⟨subd11_0_821, List.forall_mem_cons.2 ⟨subd11_0_822, List.forall_mem_cons.2 ⟨subd11_0_823, List.forall_mem_cons.2 ⟨subd11_0_824, List.forall_mem_cons.2 ⟨subd11_0_825, List.forall_mem_cons.2 ⟨subd11_0_826, List.forall_mem_cons.2 ⟨subd11_0_827, List.forall_mem_cons.2 ⟨subd11_0_828, List.forall_mem_cons.2 ⟨subd11_0_829, List.forall_mem_cons.2 ⟨subd11_0_830, List.forall_mem_cons.2 ⟨subd11_0_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_832 : subd11_0 [-1, -2, -9] = true := by decide +kernel
theorem subd11_0_833 : subd11_0 [-1, -2, -8] = true := by decide +kernel
theorem subd11_0_834 : subd11_0 [-1, -2, -7] = true := by decide +kernel
theorem subd11_0_835 : subd11_0 [-1, -2, -6] = true := by decide +kernel
theorem subd11_0_836 : subd11_0 [-1, -2, -5] = true := by decide +kernel
theorem subd11_0_837 : subd11_0 [-1, -2, -4] = true := by decide +kernel
theorem subd11_0_838 : subd11_0 [-1, -2, -3] = true := by decide +kernel
theorem subd11_0_839 : subd11_0 [-1, -2, -2] = true := by decide +kernel
theorem subd11_0_840 : subd11_0 [-1, -2, -1] = true := by decide +kernel
theorem subd11_0_841 : subd11_0 [-1, -2, 0] = true := by decide +kernel
theorem subd11_0_842 : subd11_0 [-1, -2, 1] = true := by decide +kernel
theorem subd11_0_843 : subd11_0 [-1, -2, 2] = true := by decide +kernel
theorem subd11_0_844 : subd11_0 [-1, -2, 3] = true := by decide +kernel
theorem subd11_0_845 : subd11_0 [-1, -2, 4] = true := by decide +kernel
theorem subd11_0_846 : subd11_0 [-1, -2, 5] = true := by decide +kernel
theorem subd11_0_847 : subd11_0 [-1, -2, 6] = true := by decide +kernel
theorem subd11_0_848 : subd11_0 [-1, -2, 7] = true := by decide +kernel
theorem subd11_0_849 : subd11_0 [-1, -2, 8] = true := by decide +kernel
theorem subd11_0_850 : subd11_0 [-1, -1, -9] = true := by decide +kernel
theorem subd11_0_851 : subd11_0 [-1, -1, -8] = true := by decide +kernel
theorem subd11_0_852 : subd11_0 [-1, -1, -7] = true := by decide +kernel
theorem subd11_0_853 : subd11_0 [-1, -1, -6] = true := by decide +kernel
theorem subd11_0_854 : subd11_0 [-1, -1, -5] = true := by decide +kernel
theorem subd11_0_855 : subd11_0 [-1, -1, -4] = true := by decide +kernel
theorem subd11_0_856 : subd11_0 [-1, -1, -3] = true := by decide +kernel
theorem subd11_0_857 : subd11_0 [-1, -1, -2] = true := by decide +kernel
theorem subd11_0_858 : subd11_0 [-1, -1, -1] = true := by decide +kernel
theorem subd11_0_859 : subd11_0 [-1, -1, 0] = true := by decide +kernel
theorem subd11_0_860 : subd11_0 [-1, -1, 1] = true := by decide +kernel
theorem subd11_0_861 : subd11_0 [-1, -1, 2] = true := by decide +kernel
theorem subd11_0_862 : subd11_0 [-1, -1, 3] = true := by decide +kernel
theorem subd11_0_863 : subd11_0 [-1, -1, 4] = true := by decide +kernel
theorem sbd11_0_26 : ∀ q ∈ blkd11_0_26, subd11_0 q = true := by
  unfold blkd11_0_26
  exact List.forall_mem_cons.2 ⟨subd11_0_832, List.forall_mem_cons.2 ⟨subd11_0_833, List.forall_mem_cons.2 ⟨subd11_0_834, List.forall_mem_cons.2 ⟨subd11_0_835, List.forall_mem_cons.2 ⟨subd11_0_836, List.forall_mem_cons.2 ⟨subd11_0_837, List.forall_mem_cons.2 ⟨subd11_0_838, List.forall_mem_cons.2 ⟨subd11_0_839, List.forall_mem_cons.2 ⟨subd11_0_840, List.forall_mem_cons.2 ⟨subd11_0_841, List.forall_mem_cons.2 ⟨subd11_0_842, List.forall_mem_cons.2 ⟨subd11_0_843, List.forall_mem_cons.2 ⟨subd11_0_844, List.forall_mem_cons.2 ⟨subd11_0_845, List.forall_mem_cons.2 ⟨subd11_0_846, List.forall_mem_cons.2 ⟨subd11_0_847, List.forall_mem_cons.2 ⟨subd11_0_848, List.forall_mem_cons.2 ⟨subd11_0_849, List.forall_mem_cons.2 ⟨subd11_0_850, List.forall_mem_cons.2 ⟨subd11_0_851, List.forall_mem_cons.2 ⟨subd11_0_852, List.forall_mem_cons.2 ⟨subd11_0_853, List.forall_mem_cons.2 ⟨subd11_0_854, List.forall_mem_cons.2 ⟨subd11_0_855, List.forall_mem_cons.2 ⟨subd11_0_856, List.forall_mem_cons.2 ⟨subd11_0_857, List.forall_mem_cons.2 ⟨subd11_0_858, List.forall_mem_cons.2 ⟨subd11_0_859, List.forall_mem_cons.2 ⟨subd11_0_860, List.forall_mem_cons.2 ⟨subd11_0_861, List.forall_mem_cons.2 ⟨subd11_0_862, List.forall_mem_cons.2 ⟨subd11_0_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_864 : subd11_0 [-1, -1, 5] = true := by decide +kernel
theorem subd11_0_865 : subd11_0 [-1, -1, 6] = true := by decide +kernel
theorem subd11_0_866 : subd11_0 [-1, -1, 7] = true := by decide +kernel
theorem subd11_0_867 : subd11_0 [-1, -1, 8] = true := by decide +kernel
theorem subd11_0_868 : subd11_0 [-1, 0, -9] = true := by decide +kernel
theorem subd11_0_869 : subd11_0 [-1, 0, -8] = true := by decide +kernel
theorem subd11_0_870 : subd11_0 [-1, 0, -7] = true := by decide +kernel
theorem subd11_0_871 : subd11_0 [-1, 0, -6] = true := by decide +kernel
theorem subd11_0_872 : subd11_0 [-1, 0, -5] = true := by decide +kernel
theorem subd11_0_873 : subd11_0 [-1, 0, -4] = true := by decide +kernel
theorem subd11_0_874 : subd11_0 [-1, 0, -3] = true := by decide +kernel
theorem subd11_0_875 : subd11_0 [-1, 0, -2] = true := by decide +kernel
theorem subd11_0_876 : subd11_0 [-1, 0, -1] = true := by decide +kernel
theorem subd11_0_877 : subd11_0 [-1, 0, 0] = true := by decide +kernel
theorem subd11_0_878 : subd11_0 [-1, 0, 1] = true := by decide +kernel
theorem subd11_0_879 : subd11_0 [-1, 0, 2] = true := by decide +kernel
theorem subd11_0_880 : subd11_0 [-1, 0, 3] = true := by decide +kernel
theorem subd11_0_881 : subd11_0 [-1, 0, 4] = true := by decide +kernel
theorem subd11_0_882 : subd11_0 [-1, 0, 5] = true := by decide +kernel
theorem subd11_0_883 : subd11_0 [-1, 0, 6] = true := by decide +kernel
theorem subd11_0_884 : subd11_0 [-1, 0, 7] = true := by decide +kernel
theorem subd11_0_885 : subd11_0 [-1, 0, 8] = true := by decide +kernel
theorem subd11_0_886 : subd11_0 [-1, 1, -9] = true := by decide +kernel
theorem subd11_0_887 : subd11_0 [-1, 1, -8] = true := by decide +kernel
theorem subd11_0_888 : subd11_0 [-1, 1, -7] = true := by decide +kernel
theorem subd11_0_889 : subd11_0 [-1, 1, -6] = true := by decide +kernel
theorem subd11_0_890 : subd11_0 [-1, 1, -5] = true := by decide +kernel
theorem subd11_0_891 : subd11_0 [-1, 1, -4] = true := by decide +kernel
theorem subd11_0_892 : subd11_0 [-1, 1, -3] = true := by decide +kernel
theorem subd11_0_893 : subd11_0 [-1, 1, -2] = true := by decide +kernel
theorem subd11_0_894 : subd11_0 [-1, 1, -1] = true := by decide +kernel
theorem subd11_0_895 : subd11_0 [-1, 1, 0] = true := by decide +kernel
theorem sbd11_0_27 : ∀ q ∈ blkd11_0_27, subd11_0 q = true := by
  unfold blkd11_0_27
  exact List.forall_mem_cons.2 ⟨subd11_0_864, List.forall_mem_cons.2 ⟨subd11_0_865, List.forall_mem_cons.2 ⟨subd11_0_866, List.forall_mem_cons.2 ⟨subd11_0_867, List.forall_mem_cons.2 ⟨subd11_0_868, List.forall_mem_cons.2 ⟨subd11_0_869, List.forall_mem_cons.2 ⟨subd11_0_870, List.forall_mem_cons.2 ⟨subd11_0_871, List.forall_mem_cons.2 ⟨subd11_0_872, List.forall_mem_cons.2 ⟨subd11_0_873, List.forall_mem_cons.2 ⟨subd11_0_874, List.forall_mem_cons.2 ⟨subd11_0_875, List.forall_mem_cons.2 ⟨subd11_0_876, List.forall_mem_cons.2 ⟨subd11_0_877, List.forall_mem_cons.2 ⟨subd11_0_878, List.forall_mem_cons.2 ⟨subd11_0_879, List.forall_mem_cons.2 ⟨subd11_0_880, List.forall_mem_cons.2 ⟨subd11_0_881, List.forall_mem_cons.2 ⟨subd11_0_882, List.forall_mem_cons.2 ⟨subd11_0_883, List.forall_mem_cons.2 ⟨subd11_0_884, List.forall_mem_cons.2 ⟨subd11_0_885, List.forall_mem_cons.2 ⟨subd11_0_886, List.forall_mem_cons.2 ⟨subd11_0_887, List.forall_mem_cons.2 ⟨subd11_0_888, List.forall_mem_cons.2 ⟨subd11_0_889, List.forall_mem_cons.2 ⟨subd11_0_890, List.forall_mem_cons.2 ⟨subd11_0_891, List.forall_mem_cons.2 ⟨subd11_0_892, List.forall_mem_cons.2 ⟨subd11_0_893, List.forall_mem_cons.2 ⟨subd11_0_894, List.forall_mem_cons.2 ⟨subd11_0_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_896 : subd11_0 [-1, 1, 1] = true := by decide +kernel
theorem subd11_0_897 : subd11_0 [-1, 1, 2] = true := by decide +kernel
theorem subd11_0_898 : subd11_0 [-1, 1, 3] = true := by decide +kernel
theorem subd11_0_899 : subd11_0 [-1, 1, 4] = true := by decide +kernel
theorem subd11_0_900 : subd11_0 [-1, 1, 5] = true := by decide +kernel
theorem subd11_0_901 : subd11_0 [-1, 1, 6] = true := by decide +kernel
theorem subd11_0_902 : subd11_0 [-1, 1, 7] = true := by decide +kernel
theorem subd11_0_903 : subd11_0 [-1, 1, 8] = true := by decide +kernel
theorem subd11_0_904 : subd11_0 [-1, 2, -9] = true := by decide +kernel
theorem subd11_0_905 : subd11_0 [-1, 2, -8] = true := by decide +kernel
theorem subd11_0_906 : subd11_0 [-1, 2, -7] = true := by decide +kernel
theorem subd11_0_907 : subd11_0 [-1, 2, -6] = true := by decide +kernel
theorem subd11_0_908 : subd11_0 [-1, 2, -5] = true := by decide +kernel
theorem subd11_0_909 : subd11_0 [-1, 2, -4] = true := by decide +kernel
theorem subd11_0_910 : subd11_0 [-1, 2, -3] = true := by decide +kernel
theorem subd11_0_911 : subd11_0 [-1, 2, -2] = true := by decide +kernel
theorem subd11_0_912 : subd11_0 [-1, 2, -1] = true := by decide +kernel
theorem subd11_0_913 : subd11_0 [-1, 2, 0] = true := by decide +kernel
theorem subd11_0_914 : subd11_0 [-1, 2, 1] = true := by decide +kernel
theorem subd11_0_915 : subd11_0 [-1, 2, 2] = true := by decide +kernel
theorem subd11_0_916 : subd11_0 [-1, 2, 3] = true := by decide +kernel
theorem subd11_0_917 : subd11_0 [-1, 2, 4] = true := by decide +kernel
theorem subd11_0_918 : subd11_0 [-1, 2, 5] = true := by decide +kernel
theorem subd11_0_919 : subd11_0 [-1, 2, 6] = true := by decide +kernel
theorem subd11_0_920 : subd11_0 [-1, 2, 7] = true := by decide +kernel
theorem subd11_0_921 : subd11_0 [-1, 2, 8] = true := by decide +kernel
theorem subd11_0_922 : subd11_0 [-1, 3, -9] = true := by decide +kernel
theorem subd11_0_923 : subd11_0 [-1, 3, -8] = true := by decide +kernel
theorem subd11_0_924 : subd11_0 [-1, 3, -7] = true := by decide +kernel
theorem subd11_0_925 : subd11_0 [-1, 3, -6] = true := by decide +kernel
theorem subd11_0_926 : subd11_0 [-1, 3, -5] = true := by decide +kernel
theorem subd11_0_927 : subd11_0 [-1, 3, -4] = true := by decide +kernel
theorem sbd11_0_28 : ∀ q ∈ blkd11_0_28, subd11_0 q = true := by
  unfold blkd11_0_28
  exact List.forall_mem_cons.2 ⟨subd11_0_896, List.forall_mem_cons.2 ⟨subd11_0_897, List.forall_mem_cons.2 ⟨subd11_0_898, List.forall_mem_cons.2 ⟨subd11_0_899, List.forall_mem_cons.2 ⟨subd11_0_900, List.forall_mem_cons.2 ⟨subd11_0_901, List.forall_mem_cons.2 ⟨subd11_0_902, List.forall_mem_cons.2 ⟨subd11_0_903, List.forall_mem_cons.2 ⟨subd11_0_904, List.forall_mem_cons.2 ⟨subd11_0_905, List.forall_mem_cons.2 ⟨subd11_0_906, List.forall_mem_cons.2 ⟨subd11_0_907, List.forall_mem_cons.2 ⟨subd11_0_908, List.forall_mem_cons.2 ⟨subd11_0_909, List.forall_mem_cons.2 ⟨subd11_0_910, List.forall_mem_cons.2 ⟨subd11_0_911, List.forall_mem_cons.2 ⟨subd11_0_912, List.forall_mem_cons.2 ⟨subd11_0_913, List.forall_mem_cons.2 ⟨subd11_0_914, List.forall_mem_cons.2 ⟨subd11_0_915, List.forall_mem_cons.2 ⟨subd11_0_916, List.forall_mem_cons.2 ⟨subd11_0_917, List.forall_mem_cons.2 ⟨subd11_0_918, List.forall_mem_cons.2 ⟨subd11_0_919, List.forall_mem_cons.2 ⟨subd11_0_920, List.forall_mem_cons.2 ⟨subd11_0_921, List.forall_mem_cons.2 ⟨subd11_0_922, List.forall_mem_cons.2 ⟨subd11_0_923, List.forall_mem_cons.2 ⟨subd11_0_924, List.forall_mem_cons.2 ⟨subd11_0_925, List.forall_mem_cons.2 ⟨subd11_0_926, List.forall_mem_cons.2 ⟨subd11_0_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_928 : subd11_0 [-1, 3, -3] = true := by decide +kernel
theorem subd11_0_929 : subd11_0 [-1, 3, -2] = true := by decide +kernel
theorem subd11_0_930 : subd11_0 [-1, 3, -1] = true := by decide +kernel
theorem subd11_0_931 : subd11_0 [-1, 3, 0] = true := by decide +kernel
theorem subd11_0_932 : subd11_0 [-1, 3, 1] = true := by decide +kernel
theorem subd11_0_933 : subd11_0 [-1, 3, 2] = true := by decide +kernel
theorem subd11_0_934 : subd11_0 [-1, 3, 3] = true := by decide +kernel
theorem subd11_0_935 : subd11_0 [-1, 3, 4] = true := by decide +kernel
theorem subd11_0_936 : subd11_0 [-1, 3, 5] = true := by decide +kernel
theorem subd11_0_937 : subd11_0 [-1, 3, 6] = true := by decide +kernel
theorem subd11_0_938 : subd11_0 [-1, 3, 7] = true := by decide +kernel
theorem subd11_0_939 : subd11_0 [-1, 4, -9] = true := by decide +kernel
theorem subd11_0_940 : subd11_0 [-1, 4, -8] = true := by decide +kernel
theorem subd11_0_941 : subd11_0 [-1, 4, -7] = true := by decide +kernel
theorem subd11_0_942 : subd11_0 [-1, 4, -6] = true := by decide +kernel
theorem subd11_0_943 : subd11_0 [-1, 4, -5] = true := by decide +kernel
theorem subd11_0_944 : subd11_0 [-1, 4, -4] = true := by decide +kernel
theorem subd11_0_945 : subd11_0 [-1, 4, -3] = true := by decide +kernel
theorem subd11_0_946 : subd11_0 [-1, 4, -2] = true := by decide +kernel
theorem subd11_0_947 : subd11_0 [-1, 4, -1] = true := by decide +kernel
theorem subd11_0_948 : subd11_0 [-1, 4, 0] = true := by decide +kernel
theorem subd11_0_949 : subd11_0 [-1, 4, 1] = true := by decide +kernel
theorem subd11_0_950 : subd11_0 [-1, 4, 2] = true := by decide +kernel
theorem subd11_0_951 : subd11_0 [-1, 4, 3] = true := by decide +kernel
theorem subd11_0_952 : subd11_0 [-1, 4, 4] = true := by decide +kernel
theorem subd11_0_953 : subd11_0 [-1, 4, 5] = true := by decide +kernel
theorem subd11_0_954 : subd11_0 [-1, 4, 6] = true := by decide +kernel
theorem subd11_0_955 : subd11_0 [-1, 4, 7] = true := by decide +kernel
theorem subd11_0_956 : subd11_0 [-1, 5, -8] = true := by decide +kernel
theorem subd11_0_957 : subd11_0 [-1, 5, -7] = true := by decide +kernel
theorem subd11_0_958 : subd11_0 [-1, 5, -6] = true := by decide +kernel
theorem subd11_0_959 : subd11_0 [-1, 5, -5] = true := by decide +kernel
theorem sbd11_0_29 : ∀ q ∈ blkd11_0_29, subd11_0 q = true := by
  unfold blkd11_0_29
  exact List.forall_mem_cons.2 ⟨subd11_0_928, List.forall_mem_cons.2 ⟨subd11_0_929, List.forall_mem_cons.2 ⟨subd11_0_930, List.forall_mem_cons.2 ⟨subd11_0_931, List.forall_mem_cons.2 ⟨subd11_0_932, List.forall_mem_cons.2 ⟨subd11_0_933, List.forall_mem_cons.2 ⟨subd11_0_934, List.forall_mem_cons.2 ⟨subd11_0_935, List.forall_mem_cons.2 ⟨subd11_0_936, List.forall_mem_cons.2 ⟨subd11_0_937, List.forall_mem_cons.2 ⟨subd11_0_938, List.forall_mem_cons.2 ⟨subd11_0_939, List.forall_mem_cons.2 ⟨subd11_0_940, List.forall_mem_cons.2 ⟨subd11_0_941, List.forall_mem_cons.2 ⟨subd11_0_942, List.forall_mem_cons.2 ⟨subd11_0_943, List.forall_mem_cons.2 ⟨subd11_0_944, List.forall_mem_cons.2 ⟨subd11_0_945, List.forall_mem_cons.2 ⟨subd11_0_946, List.forall_mem_cons.2 ⟨subd11_0_947, List.forall_mem_cons.2 ⟨subd11_0_948, List.forall_mem_cons.2 ⟨subd11_0_949, List.forall_mem_cons.2 ⟨subd11_0_950, List.forall_mem_cons.2 ⟨subd11_0_951, List.forall_mem_cons.2 ⟨subd11_0_952, List.forall_mem_cons.2 ⟨subd11_0_953, List.forall_mem_cons.2 ⟨subd11_0_954, List.forall_mem_cons.2 ⟨subd11_0_955, List.forall_mem_cons.2 ⟨subd11_0_956, List.forall_mem_cons.2 ⟨subd11_0_957, List.forall_mem_cons.2 ⟨subd11_0_958, List.forall_mem_cons.2 ⟨subd11_0_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_960 : subd11_0 [-1, 5, -4] = true := by decide +kernel
theorem subd11_0_961 : subd11_0 [-1, 5, -3] = true := by decide +kernel
theorem subd11_0_962 : subd11_0 [-1, 5, -2] = true := by decide +kernel
theorem subd11_0_963 : subd11_0 [-1, 5, -1] = true := by decide +kernel
theorem subd11_0_964 : subd11_0 [-1, 5, 0] = true := by decide +kernel
theorem subd11_0_965 : subd11_0 [-1, 5, 1] = true := by decide +kernel
theorem subd11_0_966 : subd11_0 [-1, 5, 2] = true := by decide +kernel
theorem subd11_0_967 : subd11_0 [-1, 5, 3] = true := by decide +kernel
theorem subd11_0_968 : subd11_0 [-1, 5, 4] = true := by decide +kernel
theorem subd11_0_969 : subd11_0 [-1, 5, 5] = true := by decide +kernel
theorem subd11_0_970 : subd11_0 [-1, 5, 6] = true := by decide +kernel
theorem subd11_0_971 : subd11_0 [-1, 6, -7] = true := by decide +kernel
theorem subd11_0_972 : subd11_0 [-1, 6, -6] = true := by decide +kernel
theorem subd11_0_973 : subd11_0 [-1, 6, -5] = true := by decide +kernel
theorem subd11_0_974 : subd11_0 [-1, 6, -4] = true := by decide +kernel
theorem subd11_0_975 : subd11_0 [-1, 6, -3] = true := by decide +kernel
theorem subd11_0_976 : subd11_0 [-1, 6, -2] = true := by decide +kernel
theorem subd11_0_977 : subd11_0 [-1, 6, -1] = true := by decide +kernel
theorem subd11_0_978 : subd11_0 [-1, 6, 0] = true := by decide +kernel
theorem subd11_0_979 : subd11_0 [-1, 6, 1] = true := by decide +kernel
theorem subd11_0_980 : subd11_0 [-1, 6, 2] = true := by decide +kernel
theorem subd11_0_981 : subd11_0 [-1, 6, 3] = true := by decide +kernel
theorem subd11_0_982 : subd11_0 [-1, 6, 4] = true := by decide +kernel
theorem subd11_0_983 : subd11_0 [-1, 6, 5] = true := by decide +kernel
theorem subd11_0_984 : subd11_0 [-1, 7] = true := by decide +kernel
theorem subd11_0_985 : subd11_0 [-1, 8] = true := by decide +kernel
theorem subd11_0_986 : subd11_0 [-1, 9] = true := by decide +kernel
theorem subd11_0_987 : subd11_0 [0, -10] = true := by decide +kernel
theorem subd11_0_988 : subd11_0 [0, -9] = true := by decide +kernel
theorem subd11_0_989 : subd11_0 [0, -8] = true := by decide +kernel
theorem subd11_0_990 : subd11_0 [0, -7] = true := by decide +kernel
theorem subd11_0_991 : subd11_0 [0, -6, -7] = true := by decide +kernel
theorem sbd11_0_30 : ∀ q ∈ blkd11_0_30, subd11_0 q = true := by
  unfold blkd11_0_30
  exact List.forall_mem_cons.2 ⟨subd11_0_960, List.forall_mem_cons.2 ⟨subd11_0_961, List.forall_mem_cons.2 ⟨subd11_0_962, List.forall_mem_cons.2 ⟨subd11_0_963, List.forall_mem_cons.2 ⟨subd11_0_964, List.forall_mem_cons.2 ⟨subd11_0_965, List.forall_mem_cons.2 ⟨subd11_0_966, List.forall_mem_cons.2 ⟨subd11_0_967, List.forall_mem_cons.2 ⟨subd11_0_968, List.forall_mem_cons.2 ⟨subd11_0_969, List.forall_mem_cons.2 ⟨subd11_0_970, List.forall_mem_cons.2 ⟨subd11_0_971, List.forall_mem_cons.2 ⟨subd11_0_972, List.forall_mem_cons.2 ⟨subd11_0_973, List.forall_mem_cons.2 ⟨subd11_0_974, List.forall_mem_cons.2 ⟨subd11_0_975, List.forall_mem_cons.2 ⟨subd11_0_976, List.forall_mem_cons.2 ⟨subd11_0_977, List.forall_mem_cons.2 ⟨subd11_0_978, List.forall_mem_cons.2 ⟨subd11_0_979, List.forall_mem_cons.2 ⟨subd11_0_980, List.forall_mem_cons.2 ⟨subd11_0_981, List.forall_mem_cons.2 ⟨subd11_0_982, List.forall_mem_cons.2 ⟨subd11_0_983, List.forall_mem_cons.2 ⟨subd11_0_984, List.forall_mem_cons.2 ⟨subd11_0_985, List.forall_mem_cons.2 ⟨subd11_0_986, List.forall_mem_cons.2 ⟨subd11_0_987, List.forall_mem_cons.2 ⟨subd11_0_988, List.forall_mem_cons.2 ⟨subd11_0_989, List.forall_mem_cons.2 ⟨subd11_0_990, List.forall_mem_cons.2 ⟨subd11_0_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_992 : subd11_0 [0, -6, -6] = true := by decide +kernel
theorem subd11_0_993 : subd11_0 [0, -6, -5] = true := by decide +kernel
theorem subd11_0_994 : subd11_0 [0, -6, -4] = true := by decide +kernel
theorem subd11_0_995 : subd11_0 [0, -6, -3] = true := by decide +kernel
theorem subd11_0_996 : subd11_0 [0, -6, -2] = true := by decide +kernel
theorem subd11_0_997 : subd11_0 [0, -6, -1] = true := by decide +kernel
theorem subd11_0_998 : subd11_0 [0, -6, 0] = true := by decide +kernel
theorem subd11_0_999 : subd11_0 [0, -6, 1] = true := by decide +kernel
theorem subd11_0_1000 : subd11_0 [0, -6, 2] = true := by decide +kernel
theorem subd11_0_1001 : subd11_0 [0, -6, 3] = true := by decide +kernel
theorem subd11_0_1002 : subd11_0 [0, -6, 4] = true := by decide +kernel
theorem subd11_0_1003 : subd11_0 [0, -6, 5] = true := by decide +kernel
theorem subd11_0_1004 : subd11_0 [0, -6, 6] = true := by decide +kernel
theorem subd11_0_1005 : subd11_0 [0, -6, 7] = true := by decide +kernel
theorem subd11_0_1006 : subd11_0 [0, -5, -8] = true := by decide +kernel
theorem subd11_0_1007 : subd11_0 [0, -5, -7] = true := by decide +kernel
theorem subd11_0_1008 : subd11_0 [0, -5, -6] = true := by decide +kernel
theorem subd11_0_1009 : subd11_0 [0, -5, -5] = true := by decide +kernel
theorem subd11_0_1010 : subd11_0 [0, -5, -4] = true := by decide +kernel
theorem subd11_0_1011 : subd11_0 [0, -5, -3] = true := by decide +kernel
theorem subd11_0_1012 : subd11_0 [0, -5, -2] = true := by decide +kernel
theorem subd11_0_1013 : subd11_0 [0, -5, -1] = true := by decide +kernel
theorem subd11_0_1014 : subd11_0 [0, -5, 0] = true := by decide +kernel
theorem subd11_0_1015 : subd11_0 [0, -5, 1] = true := by decide +kernel
theorem subd11_0_1016 : subd11_0 [0, -5, 2] = true := by decide +kernel
theorem subd11_0_1017 : subd11_0 [0, -5, 3] = true := by decide +kernel
theorem subd11_0_1018 : subd11_0 [0, -5, 4] = true := by decide +kernel
theorem subd11_0_1019 : subd11_0 [0, -5, 5] = true := by decide +kernel
theorem subd11_0_1020 : subd11_0 [0, -5, 6] = true := by decide +kernel
theorem subd11_0_1021 : subd11_0 [0, -5, 7] = true := by decide +kernel
theorem subd11_0_1022 : subd11_0 [0, -4, -8] = true := by decide +kernel
theorem subd11_0_1023 : subd11_0 [0, -4, -7] = true := by decide +kernel
theorem sbd11_0_31 : ∀ q ∈ blkd11_0_31, subd11_0 q = true := by
  unfold blkd11_0_31
  exact List.forall_mem_cons.2 ⟨subd11_0_992, List.forall_mem_cons.2 ⟨subd11_0_993, List.forall_mem_cons.2 ⟨subd11_0_994, List.forall_mem_cons.2 ⟨subd11_0_995, List.forall_mem_cons.2 ⟨subd11_0_996, List.forall_mem_cons.2 ⟨subd11_0_997, List.forall_mem_cons.2 ⟨subd11_0_998, List.forall_mem_cons.2 ⟨subd11_0_999, List.forall_mem_cons.2 ⟨subd11_0_1000, List.forall_mem_cons.2 ⟨subd11_0_1001, List.forall_mem_cons.2 ⟨subd11_0_1002, List.forall_mem_cons.2 ⟨subd11_0_1003, List.forall_mem_cons.2 ⟨subd11_0_1004, List.forall_mem_cons.2 ⟨subd11_0_1005, List.forall_mem_cons.2 ⟨subd11_0_1006, List.forall_mem_cons.2 ⟨subd11_0_1007, List.forall_mem_cons.2 ⟨subd11_0_1008, List.forall_mem_cons.2 ⟨subd11_0_1009, List.forall_mem_cons.2 ⟨subd11_0_1010, List.forall_mem_cons.2 ⟨subd11_0_1011, List.forall_mem_cons.2 ⟨subd11_0_1012, List.forall_mem_cons.2 ⟨subd11_0_1013, List.forall_mem_cons.2 ⟨subd11_0_1014, List.forall_mem_cons.2 ⟨subd11_0_1015, List.forall_mem_cons.2 ⟨subd11_0_1016, List.forall_mem_cons.2 ⟨subd11_0_1017, List.forall_mem_cons.2 ⟨subd11_0_1018, List.forall_mem_cons.2 ⟨subd11_0_1019, List.forall_mem_cons.2 ⟨subd11_0_1020, List.forall_mem_cons.2 ⟨subd11_0_1021, List.forall_mem_cons.2 ⟨subd11_0_1022, List.forall_mem_cons.2 ⟨subd11_0_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1024 : subd11_0 [0, -4, -6] = true := by decide +kernel
theorem subd11_0_1025 : subd11_0 [0, -4, -5] = true := by decide +kernel
theorem subd11_0_1026 : subd11_0 [0, -4, -4] = true := by decide +kernel
theorem subd11_0_1027 : subd11_0 [0, -4, -3] = true := by decide +kernel
theorem subd11_0_1028 : subd11_0 [0, -4, -2] = true := by decide +kernel
theorem subd11_0_1029 : subd11_0 [0, -4, -1] = true := by decide +kernel
theorem subd11_0_1030 : subd11_0 [0, -4, 0] = true := by decide +kernel
theorem subd11_0_1031 : subd11_0 [0, -4, 1] = true := by decide +kernel
theorem subd11_0_1032 : subd11_0 [0, -4, 2] = true := by decide +kernel
theorem subd11_0_1033 : subd11_0 [0, -4, 3] = true := by decide +kernel
theorem subd11_0_1034 : subd11_0 [0, -4, 4] = true := by decide +kernel
theorem subd11_0_1035 : subd11_0 [0, -4, 5] = true := by decide +kernel
theorem subd11_0_1036 : subd11_0 [0, -4, 6] = true := by decide +kernel
theorem subd11_0_1037 : subd11_0 [0, -4, 7] = true := by decide +kernel
theorem subd11_0_1038 : subd11_0 [0, -4, 8] = true := by decide +kernel
theorem subd11_0_1039 : subd11_0 [0, -3, -9] = true := by decide +kernel
theorem subd11_0_1040 : subd11_0 [0, -3, -8] = true := by decide +kernel
theorem subd11_0_1041 : subd11_0 [0, -3, -7] = true := by decide +kernel
theorem subd11_0_1042 : subd11_0 [0, -3, -6] = true := by decide +kernel
theorem subd11_0_1043 : subd11_0 [0, -3, -5] = true := by decide +kernel
theorem subd11_0_1044 : subd11_0 [0, -3, -4] = true := by decide +kernel
theorem subd11_0_1045 : subd11_0 [0, -3, -3] = true := by decide +kernel
theorem subd11_0_1046 : subd11_0 [0, -3, -2] = true := by decide +kernel
theorem subd11_0_1047 : subd11_0 [0, -3, -1] = true := by decide +kernel
theorem subd11_0_1048 : subd11_0 [0, -3, 0] = true := by decide +kernel
theorem subd11_0_1049 : subd11_0 [0, -3, 1] = true := by decide +kernel
theorem subd11_0_1050 : subd11_0 [0, -3, 2] = true := by decide +kernel
theorem subd11_0_1051 : subd11_0 [0, -3, 3] = true := by decide +kernel
theorem subd11_0_1052 : subd11_0 [0, -3, 4] = true := by decide +kernel
theorem subd11_0_1053 : subd11_0 [0, -3, 5] = true := by decide +kernel
theorem subd11_0_1054 : subd11_0 [0, -3, 6] = true := by decide +kernel
theorem subd11_0_1055 : subd11_0 [0, -3, 7] = true := by decide +kernel
theorem sbd11_0_32 : ∀ q ∈ blkd11_0_32, subd11_0 q = true := by
  unfold blkd11_0_32
  exact List.forall_mem_cons.2 ⟨subd11_0_1024, List.forall_mem_cons.2 ⟨subd11_0_1025, List.forall_mem_cons.2 ⟨subd11_0_1026, List.forall_mem_cons.2 ⟨subd11_0_1027, List.forall_mem_cons.2 ⟨subd11_0_1028, List.forall_mem_cons.2 ⟨subd11_0_1029, List.forall_mem_cons.2 ⟨subd11_0_1030, List.forall_mem_cons.2 ⟨subd11_0_1031, List.forall_mem_cons.2 ⟨subd11_0_1032, List.forall_mem_cons.2 ⟨subd11_0_1033, List.forall_mem_cons.2 ⟨subd11_0_1034, List.forall_mem_cons.2 ⟨subd11_0_1035, List.forall_mem_cons.2 ⟨subd11_0_1036, List.forall_mem_cons.2 ⟨subd11_0_1037, List.forall_mem_cons.2 ⟨subd11_0_1038, List.forall_mem_cons.2 ⟨subd11_0_1039, List.forall_mem_cons.2 ⟨subd11_0_1040, List.forall_mem_cons.2 ⟨subd11_0_1041, List.forall_mem_cons.2 ⟨subd11_0_1042, List.forall_mem_cons.2 ⟨subd11_0_1043, List.forall_mem_cons.2 ⟨subd11_0_1044, List.forall_mem_cons.2 ⟨subd11_0_1045, List.forall_mem_cons.2 ⟨subd11_0_1046, List.forall_mem_cons.2 ⟨subd11_0_1047, List.forall_mem_cons.2 ⟨subd11_0_1048, List.forall_mem_cons.2 ⟨subd11_0_1049, List.forall_mem_cons.2 ⟨subd11_0_1050, List.forall_mem_cons.2 ⟨subd11_0_1051, List.forall_mem_cons.2 ⟨subd11_0_1052, List.forall_mem_cons.2 ⟨subd11_0_1053, List.forall_mem_cons.2 ⟨subd11_0_1054, List.forall_mem_cons.2 ⟨subd11_0_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1056 : subd11_0 [0, -3, 8] = true := by decide +kernel
theorem subd11_0_1057 : subd11_0 [0, -2, -9] = true := by decide +kernel
theorem subd11_0_1058 : subd11_0 [0, -2, -8] = true := by decide +kernel
theorem subd11_0_1059 : subd11_0 [0, -2, -7] = true := by decide +kernel
theorem subd11_0_1060 : subd11_0 [0, -2, -6] = true := by decide +kernel
theorem subd11_0_1061 : subd11_0 [0, -2, -5] = true := by decide +kernel
theorem subd11_0_1062 : subd11_0 [0, -2, -4] = true := by decide +kernel
theorem subd11_0_1063 : subd11_0 [0, -2, -3] = true := by decide +kernel
theorem subd11_0_1064 : subd11_0 [0, -2, -2] = true := by decide +kernel
theorem subd11_0_1065 : subd11_0 [0, -2, -1] = true := by decide +kernel
theorem subd11_0_1066 : subd11_0 [0, -2, 0] = true := by decide +kernel
theorem subd11_0_1067 : subd11_0 [0, -2, 1] = true := by decide +kernel
theorem subd11_0_1068 : subd11_0 [0, -2, 2] = true := by decide +kernel
theorem subd11_0_1069 : subd11_0 [0, -2, 3] = true := by decide +kernel
theorem subd11_0_1070 : subd11_0 [0, -2, 4] = true := by decide +kernel
theorem subd11_0_1071 : subd11_0 [0, -2, 5] = true := by decide +kernel
theorem subd11_0_1072 : subd11_0 [0, -2, 6] = true := by decide +kernel
theorem subd11_0_1073 : subd11_0 [0, -2, 7] = true := by decide +kernel
theorem subd11_0_1074 : subd11_0 [0, -2, 8] = true := by decide +kernel
theorem subd11_0_1075 : subd11_0 [0, -1, -9] = true := by decide +kernel
theorem subd11_0_1076 : subd11_0 [0, -1, -8] = true := by decide +kernel
theorem subd11_0_1077 : subd11_0 [0, -1, -7] = true := by decide +kernel
theorem subd11_0_1078 : subd11_0 [0, -1, -6] = true := by decide +kernel
theorem subd11_0_1079 : subd11_0 [0, -1, -5] = true := by decide +kernel
theorem subd11_0_1080 : subd11_0 [0, -1, -4] = true := by decide +kernel
theorem subd11_0_1081 : subd11_0 [0, -1, -3] = true := by decide +kernel
theorem subd11_0_1082 : subd11_0 [0, -1, -2] = true := by decide +kernel
theorem subd11_0_1083 : subd11_0 [0, -1, -1] = true := by decide +kernel
theorem subd11_0_1084 : subd11_0 [0, -1, 0] = true := by decide +kernel
theorem subd11_0_1085 : subd11_0 [0, -1, 1] = true := by decide +kernel
theorem subd11_0_1086 : subd11_0 [0, -1, 2] = true := by decide +kernel
theorem subd11_0_1087 : subd11_0 [0, -1, 3] = true := by decide +kernel
theorem sbd11_0_33 : ∀ q ∈ blkd11_0_33, subd11_0 q = true := by
  unfold blkd11_0_33
  exact List.forall_mem_cons.2 ⟨subd11_0_1056, List.forall_mem_cons.2 ⟨subd11_0_1057, List.forall_mem_cons.2 ⟨subd11_0_1058, List.forall_mem_cons.2 ⟨subd11_0_1059, List.forall_mem_cons.2 ⟨subd11_0_1060, List.forall_mem_cons.2 ⟨subd11_0_1061, List.forall_mem_cons.2 ⟨subd11_0_1062, List.forall_mem_cons.2 ⟨subd11_0_1063, List.forall_mem_cons.2 ⟨subd11_0_1064, List.forall_mem_cons.2 ⟨subd11_0_1065, List.forall_mem_cons.2 ⟨subd11_0_1066, List.forall_mem_cons.2 ⟨subd11_0_1067, List.forall_mem_cons.2 ⟨subd11_0_1068, List.forall_mem_cons.2 ⟨subd11_0_1069, List.forall_mem_cons.2 ⟨subd11_0_1070, List.forall_mem_cons.2 ⟨subd11_0_1071, List.forall_mem_cons.2 ⟨subd11_0_1072, List.forall_mem_cons.2 ⟨subd11_0_1073, List.forall_mem_cons.2 ⟨subd11_0_1074, List.forall_mem_cons.2 ⟨subd11_0_1075, List.forall_mem_cons.2 ⟨subd11_0_1076, List.forall_mem_cons.2 ⟨subd11_0_1077, List.forall_mem_cons.2 ⟨subd11_0_1078, List.forall_mem_cons.2 ⟨subd11_0_1079, List.forall_mem_cons.2 ⟨subd11_0_1080, List.forall_mem_cons.2 ⟨subd11_0_1081, List.forall_mem_cons.2 ⟨subd11_0_1082, List.forall_mem_cons.2 ⟨subd11_0_1083, List.forall_mem_cons.2 ⟨subd11_0_1084, List.forall_mem_cons.2 ⟨subd11_0_1085, List.forall_mem_cons.2 ⟨subd11_0_1086, List.forall_mem_cons.2 ⟨subd11_0_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
