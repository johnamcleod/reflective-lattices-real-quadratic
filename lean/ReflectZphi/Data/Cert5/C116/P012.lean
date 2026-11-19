import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_1_2720 : subd6_1 [4, -1, -2] = true := by decide +kernel
theorem subd6_1_2721 : subd6_1 [4, -1, -1] = true := by decide +kernel
theorem subd6_1_2722 : subd6_1 [4, -1, 0] = true := by decide +kernel
theorem subd6_1_2723 : subd6_1 [4, -1, 1] = true := by decide +kernel
theorem subd6_1_2724 : subd6_1 [4, -1, 2] = true := by decide +kernel
theorem subd6_1_2725 : subd6_1 [4, -1, 3] = true := by decide +kernel
theorem subd6_1_2726 : subd6_1 [4, -1, 4] = true := by decide +kernel
theorem subd6_1_2727 : subd6_1 [4, -1, 5] = true := by decide +kernel
theorem subd6_1_2728 : subd6_1 [4, -1, 6] = true := by decide +kernel
theorem subd6_1_2729 : subd6_1 [4, -1, 7] = true := by decide +kernel
theorem subd6_1_2730 : subd6_1 [4, 0, -11] = true := by decide +kernel
theorem subd6_1_2731 : subd6_1 [4, 0, -10] = true := by decide +kernel
theorem subd6_1_2732 : subd6_1 [4, 0, -9] = true := by decide +kernel
theorem subd6_1_2733 : subd6_1 [4, 0, -8] = true := by decide +kernel
theorem subd6_1_2734 : subd6_1 [4, 0, -7] = true := by decide +kernel
theorem subd6_1_2735 : subd6_1 [4, 0, -6] = true := by decide +kernel
theorem subd6_1_2736 : subd6_1 [4, 0, -5] = true := by decide +kernel
theorem subd6_1_2737 : subd6_1 [4, 0, -4] = true := by decide +kernel
theorem subd6_1_2738 : subd6_1 [4, 0, -3] = true := by decide +kernel
theorem subd6_1_2739 : subd6_1 [4, 0, -2] = true := by decide +kernel
theorem subd6_1_2740 : subd6_1 [4, 0, -1] = true := by decide +kernel
theorem subd6_1_2741 : subd6_1 [4, 0, 0] = true := by decide +kernel
theorem subd6_1_2742 : subd6_1 [4, 0, 1] = true := by decide +kernel
theorem subd6_1_2743 : subd6_1 [4, 0, 2] = true := by decide +kernel
theorem subd6_1_2744 : subd6_1 [4, 0, 3] = true := by decide +kernel
theorem subd6_1_2745 : subd6_1 [4, 0, 4] = true := by decide +kernel
theorem subd6_1_2746 : subd6_1 [4, 0, 5] = true := by decide +kernel
theorem subd6_1_2747 : subd6_1 [4, 0, 6] = true := by decide +kernel
theorem subd6_1_2748 : subd6_1 [4, 0, 7] = true := by decide +kernel
theorem subd6_1_2749 : subd6_1 [4, 1, -11] = true := by decide +kernel
theorem subd6_1_2750 : subd6_1 [4, 1, -10] = true := by decide +kernel
theorem subd6_1_2751 : subd6_1 [4, 1, -9] = true := by decide +kernel
theorem sbd6_1_85 : ∀ q ∈ blkd6_1_85, subd6_1 q = true := by
  unfold blkd6_1_85
  exact List.forall_mem_cons.2 ⟨subd6_1_2720, List.forall_mem_cons.2 ⟨subd6_1_2721, List.forall_mem_cons.2 ⟨subd6_1_2722, List.forall_mem_cons.2 ⟨subd6_1_2723, List.forall_mem_cons.2 ⟨subd6_1_2724, List.forall_mem_cons.2 ⟨subd6_1_2725, List.forall_mem_cons.2 ⟨subd6_1_2726, List.forall_mem_cons.2 ⟨subd6_1_2727, List.forall_mem_cons.2 ⟨subd6_1_2728, List.forall_mem_cons.2 ⟨subd6_1_2729, List.forall_mem_cons.2 ⟨subd6_1_2730, List.forall_mem_cons.2 ⟨subd6_1_2731, List.forall_mem_cons.2 ⟨subd6_1_2732, List.forall_mem_cons.2 ⟨subd6_1_2733, List.forall_mem_cons.2 ⟨subd6_1_2734, List.forall_mem_cons.2 ⟨subd6_1_2735, List.forall_mem_cons.2 ⟨subd6_1_2736, List.forall_mem_cons.2 ⟨subd6_1_2737, List.forall_mem_cons.2 ⟨subd6_1_2738, List.forall_mem_cons.2 ⟨subd6_1_2739, List.forall_mem_cons.2 ⟨subd6_1_2740, List.forall_mem_cons.2 ⟨subd6_1_2741, List.forall_mem_cons.2 ⟨subd6_1_2742, List.forall_mem_cons.2 ⟨subd6_1_2743, List.forall_mem_cons.2 ⟨subd6_1_2744, List.forall_mem_cons.2 ⟨subd6_1_2745, List.forall_mem_cons.2 ⟨subd6_1_2746, List.forall_mem_cons.2 ⟨subd6_1_2747, List.forall_mem_cons.2 ⟨subd6_1_2748, List.forall_mem_cons.2 ⟨subd6_1_2749, List.forall_mem_cons.2 ⟨subd6_1_2750, List.forall_mem_cons.2 ⟨subd6_1_2751, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_2752 : subd6_1 [4, 1, -8] = true := by decide +kernel
theorem subd6_1_2753 : subd6_1 [4, 1, -7] = true := by decide +kernel
theorem subd6_1_2754 : subd6_1 [4, 1, -6] = true := by decide +kernel
theorem subd6_1_2755 : subd6_1 [4, 1, -5] = true := by decide +kernel
theorem subd6_1_2756 : subd6_1 [4, 1, -4] = true := by decide +kernel
theorem subd6_1_2757 : subd6_1 [4, 1, -3] = true := by decide +kernel
theorem subd6_1_2758 : subd6_1 [4, 1, -2] = true := by decide +kernel
theorem subd6_1_2759 : subd6_1 [4, 1, -1] = true := by decide +kernel
theorem subd6_1_2760 : subd6_1 [4, 1, 0] = true := by decide +kernel
theorem subd6_1_2761 : subd6_1 [4, 1, 1] = true := by decide +kernel
theorem subd6_1_2762 : subd6_1 [4, 1, 2] = true := by decide +kernel
theorem subd6_1_2763 : subd6_1 [4, 1, 3] = true := by decide +kernel
theorem subd6_1_2764 : subd6_1 [4, 1, 4] = true := by decide +kernel
theorem subd6_1_2765 : subd6_1 [4, 1, 5] = true := by decide +kernel
theorem subd6_1_2766 : subd6_1 [4, 1, 6] = true := by decide +kernel
theorem subd6_1_2767 : subd6_1 [4, 1, 7] = true := by decide +kernel
theorem subd6_1_2768 : subd6_1 [4, 2, -11] = true := by decide +kernel
theorem subd6_1_2769 : subd6_1 [4, 2, -10] = true := by decide +kernel
theorem subd6_1_2770 : subd6_1 [4, 2, -9] = true := by decide +kernel
theorem subd6_1_2771 : subd6_1 [4, 2, -8] = true := by decide +kernel
theorem subd6_1_2772 : subd6_1 [4, 2, -7] = true := by decide +kernel
theorem subd6_1_2773 : subd6_1 [4, 2, -6] = true := by decide +kernel
theorem subd6_1_2774 : subd6_1 [4, 2, -5] = true := by decide +kernel
theorem subd6_1_2775 : subd6_1 [4, 2, -4] = true := by decide +kernel
theorem subd6_1_2776 : subd6_1 [4, 2, -3] = true := by decide +kernel
theorem subd6_1_2777 : subd6_1 [4, 2, -2] = true := by decide +kernel
theorem subd6_1_2778 : subd6_1 [4, 2, -1] = true := by decide +kernel
theorem subd6_1_2779 : subd6_1 [4, 2, 0] = true := by decide +kernel
theorem subd6_1_2780 : subd6_1 [4, 2, 1] = true := by decide +kernel
theorem subd6_1_2781 : subd6_1 [4, 2, 2] = true := by decide +kernel
theorem subd6_1_2782 : subd6_1 [4, 2, 3] = true := by decide +kernel
theorem subd6_1_2783 : subd6_1 [4, 2, 4] = true := by decide +kernel
theorem sbd6_1_86 : ∀ q ∈ blkd6_1_86, subd6_1 q = true := by
  unfold blkd6_1_86
  exact List.forall_mem_cons.2 ⟨subd6_1_2752, List.forall_mem_cons.2 ⟨subd6_1_2753, List.forall_mem_cons.2 ⟨subd6_1_2754, List.forall_mem_cons.2 ⟨subd6_1_2755, List.forall_mem_cons.2 ⟨subd6_1_2756, List.forall_mem_cons.2 ⟨subd6_1_2757, List.forall_mem_cons.2 ⟨subd6_1_2758, List.forall_mem_cons.2 ⟨subd6_1_2759, List.forall_mem_cons.2 ⟨subd6_1_2760, List.forall_mem_cons.2 ⟨subd6_1_2761, List.forall_mem_cons.2 ⟨subd6_1_2762, List.forall_mem_cons.2 ⟨subd6_1_2763, List.forall_mem_cons.2 ⟨subd6_1_2764, List.forall_mem_cons.2 ⟨subd6_1_2765, List.forall_mem_cons.2 ⟨subd6_1_2766, List.forall_mem_cons.2 ⟨subd6_1_2767, List.forall_mem_cons.2 ⟨subd6_1_2768, List.forall_mem_cons.2 ⟨subd6_1_2769, List.forall_mem_cons.2 ⟨subd6_1_2770, List.forall_mem_cons.2 ⟨subd6_1_2771, List.forall_mem_cons.2 ⟨subd6_1_2772, List.forall_mem_cons.2 ⟨subd6_1_2773, List.forall_mem_cons.2 ⟨subd6_1_2774, List.forall_mem_cons.2 ⟨subd6_1_2775, List.forall_mem_cons.2 ⟨subd6_1_2776, List.forall_mem_cons.2 ⟨subd6_1_2777, List.forall_mem_cons.2 ⟨subd6_1_2778, List.forall_mem_cons.2 ⟨subd6_1_2779, List.forall_mem_cons.2 ⟨subd6_1_2780, List.forall_mem_cons.2 ⟨subd6_1_2781, List.forall_mem_cons.2 ⟨subd6_1_2782, List.forall_mem_cons.2 ⟨subd6_1_2783, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_2784 : subd6_1 [4, 2, 5] = true := by decide +kernel
theorem subd6_1_2785 : subd6_1 [4, 2, 6] = true := by decide +kernel
theorem subd6_1_2786 : subd6_1 [4, 3, -10] = true := by decide +kernel
theorem subd6_1_2787 : subd6_1 [4, 3, -9] = true := by decide +kernel
theorem subd6_1_2788 : subd6_1 [4, 3, -8] = true := by decide +kernel
theorem subd6_1_2789 : subd6_1 [4, 3, -7] = true := by decide +kernel
theorem subd6_1_2790 : subd6_1 [4, 3, -6] = true := by decide +kernel
theorem subd6_1_2791 : subd6_1 [4, 3, -5] = true := by decide +kernel
theorem subd6_1_2792 : subd6_1 [4, 3, -4] = true := by decide +kernel
theorem subd6_1_2793 : subd6_1 [4, 3, -3] = true := by decide +kernel
theorem subd6_1_2794 : subd6_1 [4, 3, -2] = true := by decide +kernel
theorem subd6_1_2795 : subd6_1 [4, 3, -1] = true := by decide +kernel
theorem subd6_1_2796 : subd6_1 [4, 3, 0] = true := by decide +kernel
theorem subd6_1_2797 : subd6_1 [4, 3, 1] = true := by decide +kernel
theorem subd6_1_2798 : subd6_1 [4, 3, 2] = true := by decide +kernel
theorem subd6_1_2799 : subd6_1 [4, 3, 3] = true := by decide +kernel
theorem subd6_1_2800 : subd6_1 [4, 3, 4] = true := by decide +kernel
theorem subd6_1_2801 : subd6_1 [4, 3, 5] = true := by decide +kernel
theorem subd6_1_2802 : subd6_1 [4, 3, 6] = true := by decide +kernel
theorem subd6_1_2803 : subd6_1 [4, 4, -10] = true := by decide +kernel
theorem subd6_1_2804 : subd6_1 [4, 4, -9] = true := by decide +kernel
theorem subd6_1_2805 : subd6_1 [4, 4, -8] = true := by decide +kernel
theorem subd6_1_2806 : subd6_1 [4, 4, -7] = true := by decide +kernel
theorem subd6_1_2807 : subd6_1 [4, 4, -6] = true := by decide +kernel
theorem subd6_1_2808 : subd6_1 [4, 4, -5] = true := by decide +kernel
theorem subd6_1_2809 : subd6_1 [4, 4, -4] = true := by decide +kernel
theorem subd6_1_2810 : subd6_1 [4, 4, -3] = true := by decide +kernel
theorem subd6_1_2811 : subd6_1 [4, 4, -2] = true := by decide +kernel
theorem subd6_1_2812 : subd6_1 [4, 4, -1] = true := by decide +kernel
theorem subd6_1_2813 : subd6_1 [4, 4, 0] = true := by decide +kernel
theorem subd6_1_2814 : subd6_1 [4, 4, 1] = true := by decide +kernel
theorem subd6_1_2815 : subd6_1 [4, 4, 2] = true := by decide +kernel
theorem sbd6_1_87 : ∀ q ∈ blkd6_1_87, subd6_1 q = true := by
  unfold blkd6_1_87
  exact List.forall_mem_cons.2 ⟨subd6_1_2784, List.forall_mem_cons.2 ⟨subd6_1_2785, List.forall_mem_cons.2 ⟨subd6_1_2786, List.forall_mem_cons.2 ⟨subd6_1_2787, List.forall_mem_cons.2 ⟨subd6_1_2788, List.forall_mem_cons.2 ⟨subd6_1_2789, List.forall_mem_cons.2 ⟨subd6_1_2790, List.forall_mem_cons.2 ⟨subd6_1_2791, List.forall_mem_cons.2 ⟨subd6_1_2792, List.forall_mem_cons.2 ⟨subd6_1_2793, List.forall_mem_cons.2 ⟨subd6_1_2794, List.forall_mem_cons.2 ⟨subd6_1_2795, List.forall_mem_cons.2 ⟨subd6_1_2796, List.forall_mem_cons.2 ⟨subd6_1_2797, List.forall_mem_cons.2 ⟨subd6_1_2798, List.forall_mem_cons.2 ⟨subd6_1_2799, List.forall_mem_cons.2 ⟨subd6_1_2800, List.forall_mem_cons.2 ⟨subd6_1_2801, List.forall_mem_cons.2 ⟨subd6_1_2802, List.forall_mem_cons.2 ⟨subd6_1_2803, List.forall_mem_cons.2 ⟨subd6_1_2804, List.forall_mem_cons.2 ⟨subd6_1_2805, List.forall_mem_cons.2 ⟨subd6_1_2806, List.forall_mem_cons.2 ⟨subd6_1_2807, List.forall_mem_cons.2 ⟨subd6_1_2808, List.forall_mem_cons.2 ⟨subd6_1_2809, List.forall_mem_cons.2 ⟨subd6_1_2810, List.forall_mem_cons.2 ⟨subd6_1_2811, List.forall_mem_cons.2 ⟨subd6_1_2812, List.forall_mem_cons.2 ⟨subd6_1_2813, List.forall_mem_cons.2 ⟨subd6_1_2814, List.forall_mem_cons.2 ⟨subd6_1_2815, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_2816 : subd6_1 [4, 4, 3] = true := by decide +kernel
theorem subd6_1_2817 : subd6_1 [4, 4, 4] = true := by decide +kernel
theorem subd6_1_2818 : subd6_1 [4, 4, 5] = true := by decide +kernel
theorem subd6_1_2819 : subd6_1 [4, 5, -9] = true := by decide +kernel
theorem subd6_1_2820 : subd6_1 [4, 5, -8] = true := by decide +kernel
theorem subd6_1_2821 : subd6_1 [4, 5, -7] = true := by decide +kernel
theorem subd6_1_2822 : subd6_1 [4, 5, -6] = true := by decide +kernel
theorem subd6_1_2823 : subd6_1 [4, 5, -5] = true := by decide +kernel
theorem subd6_1_2824 : subd6_1 [4, 5, -4] = true := by decide +kernel
theorem subd6_1_2825 : subd6_1 [4, 5, -3] = true := by decide +kernel
theorem subd6_1_2826 : subd6_1 [4, 5, -2] = true := by decide +kernel
theorem subd6_1_2827 : subd6_1 [4, 5, -1] = true := by decide +kernel
theorem subd6_1_2828 : subd6_1 [4, 5, 0] = true := by decide +kernel
theorem subd6_1_2829 : subd6_1 [4, 5, 1] = true := by decide +kernel
theorem subd6_1_2830 : subd6_1 [4, 5, 2] = true := by decide +kernel
theorem subd6_1_2831 : subd6_1 [4, 5, 3] = true := by decide +kernel
theorem subd6_1_2832 : subd6_1 [4, 5, 4] = true := by decide +kernel
theorem subd6_1_2833 : subd6_1 [4, 6] = true := by decide +kernel
theorem subd6_1_2834 : subd6_1 [4, 7] = true := by decide +kernel
theorem subd6_1_2835 : subd6_1 [4, 8] = true := by decide +kernel
theorem subd6_1_2836 : subd6_1 [5, -11] = true := by decide +kernel
theorem subd6_1_2837 : subd6_1 [5, -10] = true := by decide +kernel
theorem subd6_1_2838 : subd6_1 [5, -9] = true := by decide +kernel
theorem subd6_1_2839 : subd6_1 [5, -8] = true := by decide +kernel
theorem subd6_1_2840 : subd6_1 [5, -7] = true := by decide +kernel
theorem subd6_1_2841 : subd6_1 [5, -6, -9] = true := by decide +kernel
theorem subd6_1_2842 : subd6_1 [5, -6, -8] = true := by decide +kernel
theorem subd6_1_2843 : subd6_1 [5, -6, -7] = true := by decide +kernel
theorem subd6_1_2844 : subd6_1 [5, -6, -6] = true := by decide +kernel
theorem subd6_1_2845 : subd6_1 [5, -6, -5] = true := by decide +kernel
theorem subd6_1_2846 : subd6_1 [5, -6, -4] = true := by decide +kernel
theorem subd6_1_2847 : subd6_1 [5, -6, -3] = true := by decide +kernel
theorem sbd6_1_88 : ∀ q ∈ blkd6_1_88, subd6_1 q = true := by
  unfold blkd6_1_88
  exact List.forall_mem_cons.2 ⟨subd6_1_2816, List.forall_mem_cons.2 ⟨subd6_1_2817, List.forall_mem_cons.2 ⟨subd6_1_2818, List.forall_mem_cons.2 ⟨subd6_1_2819, List.forall_mem_cons.2 ⟨subd6_1_2820, List.forall_mem_cons.2 ⟨subd6_1_2821, List.forall_mem_cons.2 ⟨subd6_1_2822, List.forall_mem_cons.2 ⟨subd6_1_2823, List.forall_mem_cons.2 ⟨subd6_1_2824, List.forall_mem_cons.2 ⟨subd6_1_2825, List.forall_mem_cons.2 ⟨subd6_1_2826, List.forall_mem_cons.2 ⟨subd6_1_2827, List.forall_mem_cons.2 ⟨subd6_1_2828, List.forall_mem_cons.2 ⟨subd6_1_2829, List.forall_mem_cons.2 ⟨subd6_1_2830, List.forall_mem_cons.2 ⟨subd6_1_2831, List.forall_mem_cons.2 ⟨subd6_1_2832, List.forall_mem_cons.2 ⟨subd6_1_2833, List.forall_mem_cons.2 ⟨subd6_1_2834, List.forall_mem_cons.2 ⟨subd6_1_2835, List.forall_mem_cons.2 ⟨subd6_1_2836, List.forall_mem_cons.2 ⟨subd6_1_2837, List.forall_mem_cons.2 ⟨subd6_1_2838, List.forall_mem_cons.2 ⟨subd6_1_2839, List.forall_mem_cons.2 ⟨subd6_1_2840, List.forall_mem_cons.2 ⟨subd6_1_2841, List.forall_mem_cons.2 ⟨subd6_1_2842, List.forall_mem_cons.2 ⟨subd6_1_2843, List.forall_mem_cons.2 ⟨subd6_1_2844, List.forall_mem_cons.2 ⟨subd6_1_2845, List.forall_mem_cons.2 ⟨subd6_1_2846, List.forall_mem_cons.2 ⟨subd6_1_2847, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_2848 : subd6_1 [5, -6, -2] = true := by decide +kernel
theorem subd6_1_2849 : subd6_1 [5, -6, -1] = true := by decide +kernel
theorem subd6_1_2850 : subd6_1 [5, -6, 0] = true := by decide +kernel
theorem subd6_1_2851 : subd6_1 [5, -6, 1] = true := by decide +kernel
theorem subd6_1_2852 : subd6_1 [5, -6, 2] = true := by decide +kernel
theorem subd6_1_2853 : subd6_1 [5, -6, 3] = true := by decide +kernel
theorem subd6_1_2854 : subd6_1 [5, -6, 4] = true := by decide +kernel
theorem subd6_1_2855 : subd6_1 [5, -6, 5] = true := by decide +kernel
theorem subd6_1_2856 : subd6_1 [5, -6, 6] = true := by decide +kernel
theorem subd6_1_2857 : subd6_1 [5, -5, -10] = true := by decide +kernel
theorem subd6_1_2858 : subd6_1 [5, -5, -9] = true := by decide +kernel
theorem subd6_1_2859 : subd6_1 [5, -5, -8] = true := by decide +kernel
theorem subd6_1_2860 : subd6_1 [5, -5, -7] = true := by decide +kernel
theorem subd6_1_2861 : subd6_1 [5, -5, -6] = true := by decide +kernel
theorem subd6_1_2862 : subd6_1 [5, -5, -5] = true := by decide +kernel
theorem subd6_1_2863 : subd6_1 [5, -5, -4] = true := by decide +kernel
theorem subd6_1_2864 : subd6_1 [5, -5, -3] = true := by decide +kernel
theorem subd6_1_2865 : subd6_1 [5, -5, -2] = true := by decide +kernel
theorem subd6_1_2866 : subd6_1 [5, -5, -1] = true := by decide +kernel
theorem subd6_1_2867 : subd6_1 [5, -5, 0] = true := by decide +kernel
theorem subd6_1_2868 : subd6_1 [5, -5, 1] = true := by decide +kernel
theorem subd6_1_2869 : subd6_1 [5, -5, 2] = true := by decide +kernel
theorem subd6_1_2870 : subd6_1 [5, -5, 3] = true := by decide +kernel
theorem subd6_1_2871 : subd6_1 [5, -5, 4] = true := by decide +kernel
theorem subd6_1_2872 : subd6_1 [5, -5, 5] = true := by decide +kernel
theorem subd6_1_2873 : subd6_1 [5, -5, 6] = true := by decide +kernel
theorem subd6_1_2874 : subd6_1 [5, -4, -10] = true := by decide +kernel
theorem subd6_1_2875 : subd6_1 [5, -4, -9] = true := by decide +kernel
theorem subd6_1_2876 : subd6_1 [5, -4, -8] = true := by decide +kernel
theorem subd6_1_2877 : subd6_1 [5, -4, -7] = true := by decide +kernel
theorem subd6_1_2878 : subd6_1 [5, -4, -6] = true := by decide +kernel
theorem subd6_1_2879 : subd6_1 [5, -4, -5] = true := by decide +kernel
theorem sbd6_1_89 : ∀ q ∈ blkd6_1_89, subd6_1 q = true := by
  unfold blkd6_1_89
  exact List.forall_mem_cons.2 ⟨subd6_1_2848, List.forall_mem_cons.2 ⟨subd6_1_2849, List.forall_mem_cons.2 ⟨subd6_1_2850, List.forall_mem_cons.2 ⟨subd6_1_2851, List.forall_mem_cons.2 ⟨subd6_1_2852, List.forall_mem_cons.2 ⟨subd6_1_2853, List.forall_mem_cons.2 ⟨subd6_1_2854, List.forall_mem_cons.2 ⟨subd6_1_2855, List.forall_mem_cons.2 ⟨subd6_1_2856, List.forall_mem_cons.2 ⟨subd6_1_2857, List.forall_mem_cons.2 ⟨subd6_1_2858, List.forall_mem_cons.2 ⟨subd6_1_2859, List.forall_mem_cons.2 ⟨subd6_1_2860, List.forall_mem_cons.2 ⟨subd6_1_2861, List.forall_mem_cons.2 ⟨subd6_1_2862, List.forall_mem_cons.2 ⟨subd6_1_2863, List.forall_mem_cons.2 ⟨subd6_1_2864, List.forall_mem_cons.2 ⟨subd6_1_2865, List.forall_mem_cons.2 ⟨subd6_1_2866, List.forall_mem_cons.2 ⟨subd6_1_2867, List.forall_mem_cons.2 ⟨subd6_1_2868, List.forall_mem_cons.2 ⟨subd6_1_2869, List.forall_mem_cons.2 ⟨subd6_1_2870, List.forall_mem_cons.2 ⟨subd6_1_2871, List.forall_mem_cons.2 ⟨subd6_1_2872, List.forall_mem_cons.2 ⟨subd6_1_2873, List.forall_mem_cons.2 ⟨subd6_1_2874, List.forall_mem_cons.2 ⟨subd6_1_2875, List.forall_mem_cons.2 ⟨subd6_1_2876, List.forall_mem_cons.2 ⟨subd6_1_2877, List.forall_mem_cons.2 ⟨subd6_1_2878, List.forall_mem_cons.2 ⟨subd6_1_2879, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_2880 : subd6_1 [5, -4, -4] = true := by decide +kernel
theorem subd6_1_2881 : subd6_1 [5, -4, -3] = true := by decide +kernel
theorem subd6_1_2882 : subd6_1 [5, -4, -2] = true := by decide +kernel
theorem subd6_1_2883 : subd6_1 [5, -4, -1] = true := by decide +kernel
theorem subd6_1_2884 : subd6_1 [5, -4, 0] = true := by decide +kernel
theorem subd6_1_2885 : subd6_1 [5, -4, 1] = true := by decide +kernel
theorem subd6_1_2886 : subd6_1 [5, -4, 2] = true := by decide +kernel
theorem subd6_1_2887 : subd6_1 [5, -4, 3] = true := by decide +kernel
theorem subd6_1_2888 : subd6_1 [5, -4, 4] = true := by decide +kernel
theorem subd6_1_2889 : subd6_1 [5, -4, 5] = true := by decide +kernel
theorem subd6_1_2890 : subd6_1 [5, -4, 6] = true := by decide +kernel
theorem subd6_1_2891 : subd6_1 [5, -3, -10] = true := by decide +kernel
theorem subd6_1_2892 : subd6_1 [5, -3, -9] = true := by decide +kernel
theorem subd6_1_2893 : subd6_1 [5, -3, -8] = true := by decide +kernel
theorem subd6_1_2894 : subd6_1 [5, -3, -7] = true := by decide +kernel
theorem subd6_1_2895 : subd6_1 [5, -3, -6] = true := by decide +kernel
theorem subd6_1_2896 : subd6_1 [5, -3, -5] = true := by decide +kernel
theorem subd6_1_2897 : subd6_1 [5, -3, -4] = true := by decide +kernel
theorem subd6_1_2898 : subd6_1 [5, -3, -3] = true := by decide +kernel
theorem subd6_1_2899 : subd6_1 [5, -3, -2] = true := by decide +kernel
theorem subd6_1_2900 : subd6_1 [5, -3, -1] = true := by decide +kernel
theorem subd6_1_2901 : subd6_1 [5, -3, 0] = true := by decide +kernel
theorem subd6_1_2902 : subd6_1 [5, -3, 1] = true := by decide +kernel
theorem subd6_1_2903 : subd6_1 [5, -3, 2] = true := by decide +kernel
theorem subd6_1_2904 : subd6_1 [5, -3, 3] = true := by decide +kernel
theorem subd6_1_2905 : subd6_1 [5, -3, 4] = true := by decide +kernel
theorem subd6_1_2906 : subd6_1 [5, -3, 5] = true := by decide +kernel
theorem subd6_1_2907 : subd6_1 [5, -3, 6] = true := by decide +kernel
theorem subd6_1_2908 : subd6_1 [5, -2, -11] = true := by decide +kernel
theorem subd6_1_2909 : subd6_1 [5, -2, -10] = true := by decide +kernel
theorem subd6_1_2910 : subd6_1 [5, -2, -9] = true := by decide +kernel
theorem subd6_1_2911 : subd6_1 [5, -2, -8] = true := by decide +kernel
theorem sbd6_1_90 : ∀ q ∈ blkd6_1_90, subd6_1 q = true := by
  unfold blkd6_1_90
  exact List.forall_mem_cons.2 ⟨subd6_1_2880, List.forall_mem_cons.2 ⟨subd6_1_2881, List.forall_mem_cons.2 ⟨subd6_1_2882, List.forall_mem_cons.2 ⟨subd6_1_2883, List.forall_mem_cons.2 ⟨subd6_1_2884, List.forall_mem_cons.2 ⟨subd6_1_2885, List.forall_mem_cons.2 ⟨subd6_1_2886, List.forall_mem_cons.2 ⟨subd6_1_2887, List.forall_mem_cons.2 ⟨subd6_1_2888, List.forall_mem_cons.2 ⟨subd6_1_2889, List.forall_mem_cons.2 ⟨subd6_1_2890, List.forall_mem_cons.2 ⟨subd6_1_2891, List.forall_mem_cons.2 ⟨subd6_1_2892, List.forall_mem_cons.2 ⟨subd6_1_2893, List.forall_mem_cons.2 ⟨subd6_1_2894, List.forall_mem_cons.2 ⟨subd6_1_2895, List.forall_mem_cons.2 ⟨subd6_1_2896, List.forall_mem_cons.2 ⟨subd6_1_2897, List.forall_mem_cons.2 ⟨subd6_1_2898, List.forall_mem_cons.2 ⟨subd6_1_2899, List.forall_mem_cons.2 ⟨subd6_1_2900, List.forall_mem_cons.2 ⟨subd6_1_2901, List.forall_mem_cons.2 ⟨subd6_1_2902, List.forall_mem_cons.2 ⟨subd6_1_2903, List.forall_mem_cons.2 ⟨subd6_1_2904, List.forall_mem_cons.2 ⟨subd6_1_2905, List.forall_mem_cons.2 ⟨subd6_1_2906, List.forall_mem_cons.2 ⟨subd6_1_2907, List.forall_mem_cons.2 ⟨subd6_1_2908, List.forall_mem_cons.2 ⟨subd6_1_2909, List.forall_mem_cons.2 ⟨subd6_1_2910, List.forall_mem_cons.2 ⟨subd6_1_2911, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_2912 : subd6_1 [5, -2, -7] = true := by decide +kernel
theorem subd6_1_2913 : subd6_1 [5, -2, -6] = true := by decide +kernel
theorem subd6_1_2914 : subd6_1 [5, -2, -5] = true := by decide +kernel
theorem subd6_1_2915 : subd6_1 [5, -2, -4] = true := by decide +kernel
theorem subd6_1_2916 : subd6_1 [5, -2, -3] = true := by decide +kernel
theorem subd6_1_2917 : subd6_1 [5, -2, -2] = true := by decide +kernel
theorem subd6_1_2918 : subd6_1 [5, -2, -1] = true := by decide +kernel
theorem subd6_1_2919 : subd6_1 [5, -2, 0] = true := by decide +kernel
theorem subd6_1_2920 : subd6_1 [5, -2, 1] = true := by decide +kernel
theorem subd6_1_2921 : subd6_1 [5, -2, 2] = true := by decide +kernel
theorem subd6_1_2922 : subd6_1 [5, -2, 3] = true := by decide +kernel
theorem subd6_1_2923 : subd6_1 [5, -2, 4] = true := by decide +kernel
theorem subd6_1_2924 : subd6_1 [5, -2, 5] = true := by decide +kernel
theorem subd6_1_2925 : subd6_1 [5, -2, 6] = true := by decide +kernel
theorem subd6_1_2926 : subd6_1 [5, -1, -11] = true := by decide +kernel
theorem subd6_1_2927 : subd6_1 [5, -1, -10] = true := by decide +kernel
theorem subd6_1_2928 : subd6_1 [5, -1, -9] = true := by decide +kernel
theorem subd6_1_2929 : subd6_1 [5, -1, -8] = true := by decide +kernel
theorem subd6_1_2930 : subd6_1 [5, -1, -7] = true := by decide +kernel
theorem subd6_1_2931 : subd6_1 [5, -1, -6] = true := by decide +kernel
theorem subd6_1_2932 : subd6_1 [5, -1, -5] = true := by decide +kernel
theorem subd6_1_2933 : subd6_1 [5, -1, -4] = true := by decide +kernel
theorem subd6_1_2934 : subd6_1 [5, -1, -3] = true := by decide +kernel
theorem subd6_1_2935 : subd6_1 [5, -1, -2] = true := by decide +kernel
theorem subd6_1_2936 : subd6_1 [5, -1, -1] = true := by decide +kernel
theorem subd6_1_2937 : subd6_1 [5, -1, 0] = true := by decide +kernel
theorem subd6_1_2938 : subd6_1 [5, -1, 1] = true := by decide +kernel
theorem subd6_1_2939 : subd6_1 [5, -1, 2] = true := by decide +kernel
theorem subd6_1_2940 : subd6_1 [5, -1, 3] = true := by decide +kernel
theorem subd6_1_2941 : subd6_1 [5, -1, 4] = true := by decide +kernel
theorem subd6_1_2942 : subd6_1 [5, -1, 5] = true := by decide +kernel
theorem subd6_1_2943 : subd6_1 [5, -1, 6] = true := by decide +kernel
theorem sbd6_1_91 : ∀ q ∈ blkd6_1_91, subd6_1 q = true := by
  unfold blkd6_1_91
  exact List.forall_mem_cons.2 ⟨subd6_1_2912, List.forall_mem_cons.2 ⟨subd6_1_2913, List.forall_mem_cons.2 ⟨subd6_1_2914, List.forall_mem_cons.2 ⟨subd6_1_2915, List.forall_mem_cons.2 ⟨subd6_1_2916, List.forall_mem_cons.2 ⟨subd6_1_2917, List.forall_mem_cons.2 ⟨subd6_1_2918, List.forall_mem_cons.2 ⟨subd6_1_2919, List.forall_mem_cons.2 ⟨subd6_1_2920, List.forall_mem_cons.2 ⟨subd6_1_2921, List.forall_mem_cons.2 ⟨subd6_1_2922, List.forall_mem_cons.2 ⟨subd6_1_2923, List.forall_mem_cons.2 ⟨subd6_1_2924, List.forall_mem_cons.2 ⟨subd6_1_2925, List.forall_mem_cons.2 ⟨subd6_1_2926, List.forall_mem_cons.2 ⟨subd6_1_2927, List.forall_mem_cons.2 ⟨subd6_1_2928, List.forall_mem_cons.2 ⟨subd6_1_2929, List.forall_mem_cons.2 ⟨subd6_1_2930, List.forall_mem_cons.2 ⟨subd6_1_2931, List.forall_mem_cons.2 ⟨subd6_1_2932, List.forall_mem_cons.2 ⟨subd6_1_2933, List.forall_mem_cons.2 ⟨subd6_1_2934, List.forall_mem_cons.2 ⟨subd6_1_2935, List.forall_mem_cons.2 ⟨subd6_1_2936, List.forall_mem_cons.2 ⟨subd6_1_2937, List.forall_mem_cons.2 ⟨subd6_1_2938, List.forall_mem_cons.2 ⟨subd6_1_2939, List.forall_mem_cons.2 ⟨subd6_1_2940, List.forall_mem_cons.2 ⟨subd6_1_2941, List.forall_mem_cons.2 ⟨subd6_1_2942, List.forall_mem_cons.2 ⟨subd6_1_2943, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_2944 : subd6_1 [5, 0, -11] = true := by decide +kernel
theorem subd6_1_2945 : subd6_1 [5, 0, -10] = true := by decide +kernel
theorem subd6_1_2946 : subd6_1 [5, 0, -9] = true := by decide +kernel
theorem subd6_1_2947 : subd6_1 [5, 0, -8] = true := by decide +kernel
theorem subd6_1_2948 : subd6_1 [5, 0, -7] = true := by decide +kernel
theorem subd6_1_2949 : subd6_1 [5, 0, -6] = true := by decide +kernel
theorem subd6_1_2950 : subd6_1 [5, 0, -5] = true := by decide +kernel
theorem subd6_1_2951 : subd6_1 [5, 0, -4] = true := by decide +kernel
theorem subd6_1_2952 : subd6_1 [5, 0, -3] = true := by decide +kernel
theorem subd6_1_2953 : subd6_1 [5, 0, -2] = true := by decide +kernel
theorem subd6_1_2954 : subd6_1 [5, 0, -1] = true := by decide +kernel
theorem subd6_1_2955 : subd6_1 [5, 0, 0] = true := by decide +kernel
theorem subd6_1_2956 : subd6_1 [5, 0, 1] = true := by decide +kernel
theorem subd6_1_2957 : subd6_1 [5, 0, 2] = true := by decide +kernel
theorem subd6_1_2958 : subd6_1 [5, 0, 3] = true := by decide +kernel
theorem subd6_1_2959 : subd6_1 [5, 0, 4] = true := by decide +kernel
theorem subd6_1_2960 : subd6_1 [5, 0, 5] = true := by decide +kernel
theorem subd6_1_2961 : subd6_1 [5, 0, 6] = true := by decide +kernel
theorem subd6_1_2962 : subd6_1 [5, 1, -11] = true := by decide +kernel
theorem subd6_1_2963 : subd6_1 [5, 1, -10] = true := by decide +kernel
theorem subd6_1_2964 : subd6_1 [5, 1, -9] = true := by decide +kernel
theorem subd6_1_2965 : subd6_1 [5, 1, -8] = true := by decide +kernel
theorem subd6_1_2966 : subd6_1 [5, 1, -7] = true := by decide +kernel
theorem subd6_1_2967 : subd6_1 [5, 1, -6] = true := by decide +kernel
theorem subd6_1_2968 : subd6_1 [5, 1, -5] = true := by decide +kernel
theorem subd6_1_2969 : subd6_1 [5, 1, -4] = true := by decide +kernel
theorem subd6_1_2970 : subd6_1 [5, 1, -3] = true := by decide +kernel
theorem subd6_1_2971 : subd6_1 [5, 1, -2] = true := by decide +kernel
theorem subd6_1_2972 : subd6_1 [5, 1, -1] = true := by decide +kernel
theorem subd6_1_2973 : subd6_1 [5, 1, 0] = true := by decide +kernel
theorem subd6_1_2974 : subd6_1 [5, 1, 1] = true := by decide +kernel
theorem subd6_1_2975 : subd6_1 [5, 1, 2] = true := by decide +kernel
theorem sbd6_1_92 : ∀ q ∈ blkd6_1_92, subd6_1 q = true := by
  unfold blkd6_1_92
  exact List.forall_mem_cons.2 ⟨subd6_1_2944, List.forall_mem_cons.2 ⟨subd6_1_2945, List.forall_mem_cons.2 ⟨subd6_1_2946, List.forall_mem_cons.2 ⟨subd6_1_2947, List.forall_mem_cons.2 ⟨subd6_1_2948, List.forall_mem_cons.2 ⟨subd6_1_2949, List.forall_mem_cons.2 ⟨subd6_1_2950, List.forall_mem_cons.2 ⟨subd6_1_2951, List.forall_mem_cons.2 ⟨subd6_1_2952, List.forall_mem_cons.2 ⟨subd6_1_2953, List.forall_mem_cons.2 ⟨subd6_1_2954, List.forall_mem_cons.2 ⟨subd6_1_2955, List.forall_mem_cons.2 ⟨subd6_1_2956, List.forall_mem_cons.2 ⟨subd6_1_2957, List.forall_mem_cons.2 ⟨subd6_1_2958, List.forall_mem_cons.2 ⟨subd6_1_2959, List.forall_mem_cons.2 ⟨subd6_1_2960, List.forall_mem_cons.2 ⟨subd6_1_2961, List.forall_mem_cons.2 ⟨subd6_1_2962, List.forall_mem_cons.2 ⟨subd6_1_2963, List.forall_mem_cons.2 ⟨subd6_1_2964, List.forall_mem_cons.2 ⟨subd6_1_2965, List.forall_mem_cons.2 ⟨subd6_1_2966, List.forall_mem_cons.2 ⟨subd6_1_2967, List.forall_mem_cons.2 ⟨subd6_1_2968, List.forall_mem_cons.2 ⟨subd6_1_2969, List.forall_mem_cons.2 ⟨subd6_1_2970, List.forall_mem_cons.2 ⟨subd6_1_2971, List.forall_mem_cons.2 ⟨subd6_1_2972, List.forall_mem_cons.2 ⟨subd6_1_2973, List.forall_mem_cons.2 ⟨subd6_1_2974, List.forall_mem_cons.2 ⟨subd6_1_2975, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_2976 : subd6_1 [5, 1, 3] = true := by decide +kernel
theorem subd6_1_2977 : subd6_1 [5, 1, 4] = true := by decide +kernel
theorem subd6_1_2978 : subd6_1 [5, 1, 5] = true := by decide +kernel
theorem subd6_1_2979 : subd6_1 [5, 1, 6] = true := by decide +kernel
theorem subd6_1_2980 : subd6_1 [5, 2, -10] = true := by decide +kernel
theorem subd6_1_2981 : subd6_1 [5, 2, -9] = true := by decide +kernel
theorem subd6_1_2982 : subd6_1 [5, 2, -8] = true := by decide +kernel
theorem subd6_1_2983 : subd6_1 [5, 2, -7] = true := by decide +kernel
theorem subd6_1_2984 : subd6_1 [5, 2, -6] = true := by decide +kernel
theorem subd6_1_2985 : subd6_1 [5, 2, -5] = true := by decide +kernel
theorem subd6_1_2986 : subd6_1 [5, 2, -4] = true := by decide +kernel
theorem subd6_1_2987 : subd6_1 [5, 2, -3] = true := by decide +kernel
theorem subd6_1_2988 : subd6_1 [5, 2, -2] = true := by decide +kernel
theorem subd6_1_2989 : subd6_1 [5, 2, -1] = true := by decide +kernel
theorem subd6_1_2990 : subd6_1 [5, 2, 0] = true := by decide +kernel
theorem subd6_1_2991 : subd6_1 [5, 2, 1] = true := by decide +kernel
theorem subd6_1_2992 : subd6_1 [5, 2, 2] = true := by decide +kernel
theorem subd6_1_2993 : subd6_1 [5, 2, 3] = true := by decide +kernel
theorem subd6_1_2994 : subd6_1 [5, 2, 4] = true := by decide +kernel
theorem subd6_1_2995 : subd6_1 [5, 2, 5] = true := by decide +kernel
theorem subd6_1_2996 : subd6_1 [5, 3, -10] = true := by decide +kernel
theorem subd6_1_2997 : subd6_1 [5, 3, -9] = true := by decide +kernel
theorem subd6_1_2998 : subd6_1 [5, 3, -8] = true := by decide +kernel
theorem subd6_1_2999 : subd6_1 [5, 3, -7] = true := by decide +kernel
theorem subd6_1_3000 : subd6_1 [5, 3, -6] = true := by decide +kernel
theorem subd6_1_3001 : subd6_1 [5, 3, -5] = true := by decide +kernel
theorem subd6_1_3002 : subd6_1 [5, 3, -4] = true := by decide +kernel
theorem subd6_1_3003 : subd6_1 [5, 3, -3] = true := by decide +kernel
theorem subd6_1_3004 : subd6_1 [5, 3, -2] = true := by decide +kernel
theorem subd6_1_3005 : subd6_1 [5, 3, -1] = true := by decide +kernel
theorem subd6_1_3006 : subd6_1 [5, 3, 0] = true := by decide +kernel
theorem subd6_1_3007 : subd6_1 [5, 3, 1] = true := by decide +kernel
theorem sbd6_1_93 : ∀ q ∈ blkd6_1_93, subd6_1 q = true := by
  unfold blkd6_1_93
  exact List.forall_mem_cons.2 ⟨subd6_1_2976, List.forall_mem_cons.2 ⟨subd6_1_2977, List.forall_mem_cons.2 ⟨subd6_1_2978, List.forall_mem_cons.2 ⟨subd6_1_2979, List.forall_mem_cons.2 ⟨subd6_1_2980, List.forall_mem_cons.2 ⟨subd6_1_2981, List.forall_mem_cons.2 ⟨subd6_1_2982, List.forall_mem_cons.2 ⟨subd6_1_2983, List.forall_mem_cons.2 ⟨subd6_1_2984, List.forall_mem_cons.2 ⟨subd6_1_2985, List.forall_mem_cons.2 ⟨subd6_1_2986, List.forall_mem_cons.2 ⟨subd6_1_2987, List.forall_mem_cons.2 ⟨subd6_1_2988, List.forall_mem_cons.2 ⟨subd6_1_2989, List.forall_mem_cons.2 ⟨subd6_1_2990, List.forall_mem_cons.2 ⟨subd6_1_2991, List.forall_mem_cons.2 ⟨subd6_1_2992, List.forall_mem_cons.2 ⟨subd6_1_2993, List.forall_mem_cons.2 ⟨subd6_1_2994, List.forall_mem_cons.2 ⟨subd6_1_2995, List.forall_mem_cons.2 ⟨subd6_1_2996, List.forall_mem_cons.2 ⟨subd6_1_2997, List.forall_mem_cons.2 ⟨subd6_1_2998, List.forall_mem_cons.2 ⟨subd6_1_2999, List.forall_mem_cons.2 ⟨subd6_1_3000, List.forall_mem_cons.2 ⟨subd6_1_3001, List.forall_mem_cons.2 ⟨subd6_1_3002, List.forall_mem_cons.2 ⟨subd6_1_3003, List.forall_mem_cons.2 ⟨subd6_1_3004, List.forall_mem_cons.2 ⟨subd6_1_3005, List.forall_mem_cons.2 ⟨subd6_1_3006, List.forall_mem_cons.2 ⟨subd6_1_3007, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_3008 : subd6_1 [5, 3, 2] = true := by decide +kernel
theorem subd6_1_3009 : subd6_1 [5, 3, 3] = true := by decide +kernel
theorem subd6_1_3010 : subd6_1 [5, 3, 4] = true := by decide +kernel
theorem subd6_1_3011 : subd6_1 [5, 3, 5] = true := by decide +kernel
theorem subd6_1_3012 : subd6_1 [5, 4] = true := by decide +kernel
theorem subd6_1_3013 : subd6_1 [5, 5] = true := by decide +kernel
theorem subd6_1_3014 : subd6_1 [5, 6] = true := by decide +kernel
theorem subd6_1_3015 : subd6_1 [5, 7] = true := by decide +kernel
theorem subd6_1_3016 : subd6_1 [6, -10] = true := by decide +kernel
theorem subd6_1_3017 : subd6_1 [6, -9] = true := by decide +kernel
theorem subd6_1_3018 : subd6_1 [6, -8] = true := by decide +kernel
theorem subd6_1_3019 : subd6_1 [6, -7] = true := by decide +kernel
theorem subd6_1_3020 : subd6_1 [6, -6] = true := by decide +kernel
theorem subd6_1_3021 : subd6_1 [6, -5, -9] = true := by decide +kernel
theorem subd6_1_3022 : subd6_1 [6, -5, -8] = true := by decide +kernel
theorem subd6_1_3023 : subd6_1 [6, -5, -7] = true := by decide +kernel
theorem subd6_1_3024 : subd6_1 [6, -5, -6] = true := by decide +kernel
theorem subd6_1_3025 : subd6_1 [6, -5, -5] = true := by decide +kernel
theorem subd6_1_3026 : subd6_1 [6, -5, -4] = true := by decide +kernel
theorem subd6_1_3027 : subd6_1 [6, -5, -3] = true := by decide +kernel
theorem subd6_1_3028 : subd6_1 [6, -5, -2] = true := by decide +kernel
theorem subd6_1_3029 : subd6_1 [6, -5, -1] = true := by decide +kernel
theorem subd6_1_3030 : subd6_1 [6, -5, 0] = true := by decide +kernel
theorem subd6_1_3031 : subd6_1 [6, -5, 1] = true := by decide +kernel
theorem subd6_1_3032 : subd6_1 [6, -5, 2] = true := by decide +kernel
theorem subd6_1_3033 : subd6_1 [6, -5, 3] = true := by decide +kernel
theorem subd6_1_3034 : subd6_1 [6, -5, 4] = true := by decide +kernel
theorem subd6_1_3035 : subd6_1 [6, -5, 5] = true := by decide +kernel
theorem subd6_1_3036 : subd6_1 [6, -4, -10] = true := by decide +kernel
theorem subd6_1_3037 : subd6_1 [6, -4, -9] = true := by decide +kernel
theorem subd6_1_3038 : subd6_1 [6, -4, -8] = true := by decide +kernel
theorem subd6_1_3039 : subd6_1 [6, -4, -7] = true := by decide +kernel
theorem sbd6_1_94 : ∀ q ∈ blkd6_1_94, subd6_1 q = true := by
  unfold blkd6_1_94
  exact List.forall_mem_cons.2 ⟨subd6_1_3008, List.forall_mem_cons.2 ⟨subd6_1_3009, List.forall_mem_cons.2 ⟨subd6_1_3010, List.forall_mem_cons.2 ⟨subd6_1_3011, List.forall_mem_cons.2 ⟨subd6_1_3012, List.forall_mem_cons.2 ⟨subd6_1_3013, List.forall_mem_cons.2 ⟨subd6_1_3014, List.forall_mem_cons.2 ⟨subd6_1_3015, List.forall_mem_cons.2 ⟨subd6_1_3016, List.forall_mem_cons.2 ⟨subd6_1_3017, List.forall_mem_cons.2 ⟨subd6_1_3018, List.forall_mem_cons.2 ⟨subd6_1_3019, List.forall_mem_cons.2 ⟨subd6_1_3020, List.forall_mem_cons.2 ⟨subd6_1_3021, List.forall_mem_cons.2 ⟨subd6_1_3022, List.forall_mem_cons.2 ⟨subd6_1_3023, List.forall_mem_cons.2 ⟨subd6_1_3024, List.forall_mem_cons.2 ⟨subd6_1_3025, List.forall_mem_cons.2 ⟨subd6_1_3026, List.forall_mem_cons.2 ⟨subd6_1_3027, List.forall_mem_cons.2 ⟨subd6_1_3028, List.forall_mem_cons.2 ⟨subd6_1_3029, List.forall_mem_cons.2 ⟨subd6_1_3030, List.forall_mem_cons.2 ⟨subd6_1_3031, List.forall_mem_cons.2 ⟨subd6_1_3032, List.forall_mem_cons.2 ⟨subd6_1_3033, List.forall_mem_cons.2 ⟨subd6_1_3034, List.forall_mem_cons.2 ⟨subd6_1_3035, List.forall_mem_cons.2 ⟨subd6_1_3036, List.forall_mem_cons.2 ⟨subd6_1_3037, List.forall_mem_cons.2 ⟨subd6_1_3038, List.forall_mem_cons.2 ⟨subd6_1_3039, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_3040 : subd6_1 [6, -4, -6] = true := by decide +kernel
theorem subd6_1_3041 : subd6_1 [6, -4, -5] = true := by decide +kernel
theorem subd6_1_3042 : subd6_1 [6, -4, -4] = true := by decide +kernel
theorem subd6_1_3043 : subd6_1 [6, -4, -3] = true := by decide +kernel
theorem subd6_1_3044 : subd6_1 [6, -4, -2] = true := by decide +kernel
theorem subd6_1_3045 : subd6_1 [6, -4, -1] = true := by decide +kernel
theorem subd6_1_3046 : subd6_1 [6, -4, 0] = true := by decide +kernel
theorem subd6_1_3047 : subd6_1 [6, -4, 1] = true := by decide +kernel
theorem subd6_1_3048 : subd6_1 [6, -4, 2] = true := by decide +kernel
theorem subd6_1_3049 : subd6_1 [6, -4, 3] = true := by decide +kernel
theorem subd6_1_3050 : subd6_1 [6, -4, 4] = true := by decide +kernel
theorem subd6_1_3051 : subd6_1 [6, -4, 5] = true := by decide +kernel
theorem subd6_1_3052 : subd6_1 [6, -3, -10] = true := by decide +kernel
theorem subd6_1_3053 : subd6_1 [6, -3, -9] = true := by decide +kernel
theorem subd6_1_3054 : subd6_1 [6, -3, -8] = true := by decide +kernel
theorem subd6_1_3055 : subd6_1 [6, -3, -7] = true := by decide +kernel
theorem subd6_1_3056 : subd6_1 [6, -3, -6] = true := by decide +kernel
theorem subd6_1_3057 : subd6_1 [6, -3, -5] = true := by decide +kernel
theorem subd6_1_3058 : subd6_1 [6, -3, -4] = true := by decide +kernel
theorem subd6_1_3059 : subd6_1 [6, -3, -3] = true := by decide +kernel
theorem subd6_1_3060 : subd6_1 [6, -3, -2] = true := by decide +kernel
theorem subd6_1_3061 : subd6_1 [6, -3, -1] = true := by decide +kernel
theorem subd6_1_3062 : subd6_1 [6, -3, 0] = true := by decide +kernel
theorem subd6_1_3063 : subd6_1 [6, -3, 1] = true := by decide +kernel
theorem subd6_1_3064 : subd6_1 [6, -3, 2] = true := by decide +kernel
theorem subd6_1_3065 : subd6_1 [6, -3, 3] = true := by decide +kernel
theorem subd6_1_3066 : subd6_1 [6, -3, 4] = true := by decide +kernel
theorem subd6_1_3067 : subd6_1 [6, -3, 5] = true := by decide +kernel
theorem subd6_1_3068 : subd6_1 [6, -2, -10] = true := by decide +kernel
theorem subd6_1_3069 : subd6_1 [6, -2, -9] = true := by decide +kernel
theorem subd6_1_3070 : subd6_1 [6, -2, -8] = true := by decide +kernel
theorem subd6_1_3071 : subd6_1 [6, -2, -7] = true := by decide +kernel
theorem sbd6_1_95 : ∀ q ∈ blkd6_1_95, subd6_1 q = true := by
  unfold blkd6_1_95
  exact List.forall_mem_cons.2 ⟨subd6_1_3040, List.forall_mem_cons.2 ⟨subd6_1_3041, List.forall_mem_cons.2 ⟨subd6_1_3042, List.forall_mem_cons.2 ⟨subd6_1_3043, List.forall_mem_cons.2 ⟨subd6_1_3044, List.forall_mem_cons.2 ⟨subd6_1_3045, List.forall_mem_cons.2 ⟨subd6_1_3046, List.forall_mem_cons.2 ⟨subd6_1_3047, List.forall_mem_cons.2 ⟨subd6_1_3048, List.forall_mem_cons.2 ⟨subd6_1_3049, List.forall_mem_cons.2 ⟨subd6_1_3050, List.forall_mem_cons.2 ⟨subd6_1_3051, List.forall_mem_cons.2 ⟨subd6_1_3052, List.forall_mem_cons.2 ⟨subd6_1_3053, List.forall_mem_cons.2 ⟨subd6_1_3054, List.forall_mem_cons.2 ⟨subd6_1_3055, List.forall_mem_cons.2 ⟨subd6_1_3056, List.forall_mem_cons.2 ⟨subd6_1_3057, List.forall_mem_cons.2 ⟨subd6_1_3058, List.forall_mem_cons.2 ⟨subd6_1_3059, List.forall_mem_cons.2 ⟨subd6_1_3060, List.forall_mem_cons.2 ⟨subd6_1_3061, List.forall_mem_cons.2 ⟨subd6_1_3062, List.forall_mem_cons.2 ⟨subd6_1_3063, List.forall_mem_cons.2 ⟨subd6_1_3064, List.forall_mem_cons.2 ⟨subd6_1_3065, List.forall_mem_cons.2 ⟨subd6_1_3066, List.forall_mem_cons.2 ⟨subd6_1_3067, List.forall_mem_cons.2 ⟨subd6_1_3068, List.forall_mem_cons.2 ⟨subd6_1_3069, List.forall_mem_cons.2 ⟨subd6_1_3070, List.forall_mem_cons.2 ⟨subd6_1_3071, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_3072 : subd6_1 [6, -2, -6] = true := by decide +kernel
theorem subd6_1_3073 : subd6_1 [6, -2, -5] = true := by decide +kernel
theorem subd6_1_3074 : subd6_1 [6, -2, -4] = true := by decide +kernel
theorem subd6_1_3075 : subd6_1 [6, -2, -3] = true := by decide +kernel
theorem subd6_1_3076 : subd6_1 [6, -2, -2] = true := by decide +kernel
theorem subd6_1_3077 : subd6_1 [6, -2, -1] = true := by decide +kernel
theorem subd6_1_3078 : subd6_1 [6, -2, 0] = true := by decide +kernel
theorem subd6_1_3079 : subd6_1 [6, -2, 1] = true := by decide +kernel
theorem subd6_1_3080 : subd6_1 [6, -2, 2] = true := by decide +kernel
theorem subd6_1_3081 : subd6_1 [6, -2, 3] = true := by decide +kernel
theorem subd6_1_3082 : subd6_1 [6, -2, 4] = true := by decide +kernel
theorem subd6_1_3083 : subd6_1 [6, -2, 5] = true := by decide +kernel
theorem subd6_1_3084 : subd6_1 [6, -1, -10] = true := by decide +kernel
theorem subd6_1_3085 : subd6_1 [6, -1, -9] = true := by decide +kernel
theorem subd6_1_3086 : subd6_1 [6, -1, -8] = true := by decide +kernel
theorem subd6_1_3087 : subd6_1 [6, -1, -7] = true := by decide +kernel
theorem subd6_1_3088 : subd6_1 [6, -1, -6] = true := by decide +kernel
theorem subd6_1_3089 : subd6_1 [6, -1, -5] = true := by decide +kernel
theorem subd6_1_3090 : subd6_1 [6, -1, -4] = true := by decide +kernel
theorem subd6_1_3091 : subd6_1 [6, -1, -3] = true := by decide +kernel
theorem subd6_1_3092 : subd6_1 [6, -1, -2] = true := by decide +kernel
theorem subd6_1_3093 : subd6_1 [6, -1, -1] = true := by decide +kernel
theorem subd6_1_3094 : subd6_1 [6, -1, 0] = true := by decide +kernel
theorem subd6_1_3095 : subd6_1 [6, -1, 1] = true := by decide +kernel
theorem subd6_1_3096 : subd6_1 [6, -1, 2] = true := by decide +kernel
theorem subd6_1_3097 : subd6_1 [6, -1, 3] = true := by decide +kernel
theorem subd6_1_3098 : subd6_1 [6, -1, 4] = true := by decide +kernel
theorem subd6_1_3099 : subd6_1 [6, -1, 5] = true := by decide +kernel
theorem subd6_1_3100 : subd6_1 [6, 0, -10] = true := by decide +kernel
theorem subd6_1_3101 : subd6_1 [6, 0, -9] = true := by decide +kernel
theorem subd6_1_3102 : subd6_1 [6, 0, -8] = true := by decide +kernel
theorem subd6_1_3103 : subd6_1 [6, 0, -7] = true := by decide +kernel
theorem sbd6_1_96 : ∀ q ∈ blkd6_1_96, subd6_1 q = true := by
  unfold blkd6_1_96
  exact List.forall_mem_cons.2 ⟨subd6_1_3072, List.forall_mem_cons.2 ⟨subd6_1_3073, List.forall_mem_cons.2 ⟨subd6_1_3074, List.forall_mem_cons.2 ⟨subd6_1_3075, List.forall_mem_cons.2 ⟨subd6_1_3076, List.forall_mem_cons.2 ⟨subd6_1_3077, List.forall_mem_cons.2 ⟨subd6_1_3078, List.forall_mem_cons.2 ⟨subd6_1_3079, List.forall_mem_cons.2 ⟨subd6_1_3080, List.forall_mem_cons.2 ⟨subd6_1_3081, List.forall_mem_cons.2 ⟨subd6_1_3082, List.forall_mem_cons.2 ⟨subd6_1_3083, List.forall_mem_cons.2 ⟨subd6_1_3084, List.forall_mem_cons.2 ⟨subd6_1_3085, List.forall_mem_cons.2 ⟨subd6_1_3086, List.forall_mem_cons.2 ⟨subd6_1_3087, List.forall_mem_cons.2 ⟨subd6_1_3088, List.forall_mem_cons.2 ⟨subd6_1_3089, List.forall_mem_cons.2 ⟨subd6_1_3090, List.forall_mem_cons.2 ⟨subd6_1_3091, List.forall_mem_cons.2 ⟨subd6_1_3092, List.forall_mem_cons.2 ⟨subd6_1_3093, List.forall_mem_cons.2 ⟨subd6_1_3094, List.forall_mem_cons.2 ⟨subd6_1_3095, List.forall_mem_cons.2 ⟨subd6_1_3096, List.forall_mem_cons.2 ⟨subd6_1_3097, List.forall_mem_cons.2 ⟨subd6_1_3098, List.forall_mem_cons.2 ⟨subd6_1_3099, List.forall_mem_cons.2 ⟨subd6_1_3100, List.forall_mem_cons.2 ⟨subd6_1_3101, List.forall_mem_cons.2 ⟨subd6_1_3102, List.forall_mem_cons.2 ⟨subd6_1_3103, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_3104 : subd6_1 [6, 0, -6] = true := by decide +kernel
theorem subd6_1_3105 : subd6_1 [6, 0, -5] = true := by decide +kernel
theorem subd6_1_3106 : subd6_1 [6, 0, -4] = true := by decide +kernel
theorem subd6_1_3107 : subd6_1 [6, 0, -3] = true := by decide +kernel
theorem subd6_1_3108 : subd6_1 [6, 0, -2] = true := by decide +kernel
theorem subd6_1_3109 : subd6_1 [6, 0, -1] = true := by decide +kernel
theorem subd6_1_3110 : subd6_1 [6, 0, 0] = true := by decide +kernel
theorem subd6_1_3111 : subd6_1 [6, 0, 1] = true := by decide +kernel
theorem subd6_1_3112 : subd6_1 [6, 0, 2] = true := by decide +kernel
theorem subd6_1_3113 : subd6_1 [6, 0, 3] = true := by decide +kernel
theorem subd6_1_3114 : subd6_1 [6, 0, 4] = true := by decide +kernel
theorem subd6_1_3115 : subd6_1 [6, 0, 5] = true := by decide +kernel
theorem subd6_1_3116 : subd6_1 [6, 1, -10] = true := by decide +kernel
theorem subd6_1_3117 : subd6_1 [6, 1, -9] = true := by decide +kernel
theorem subd6_1_3118 : subd6_1 [6, 1, -8] = true := by decide +kernel
theorem subd6_1_3119 : subd6_1 [6, 1, -7] = true := by decide +kernel
theorem subd6_1_3120 : subd6_1 [6, 1, -6] = true := by decide +kernel
theorem subd6_1_3121 : subd6_1 [6, 1, -5] = true := by decide +kernel
theorem subd6_1_3122 : subd6_1 [6, 1, -4] = true := by decide +kernel
theorem subd6_1_3123 : subd6_1 [6, 1, -3] = true := by decide +kernel
theorem subd6_1_3124 : subd6_1 [6, 1, -2] = true := by decide +kernel
theorem subd6_1_3125 : subd6_1 [6, 1, -1] = true := by decide +kernel
theorem subd6_1_3126 : subd6_1 [6, 1, 0] = true := by decide +kernel
theorem subd6_1_3127 : subd6_1 [6, 1, 1] = true := by decide +kernel
theorem subd6_1_3128 : subd6_1 [6, 1, 2] = true := by decide +kernel
theorem subd6_1_3129 : subd6_1 [6, 1, 3] = true := by decide +kernel
theorem subd6_1_3130 : subd6_1 [6, 1, 4] = true := by decide +kernel
theorem subd6_1_3131 : subd6_1 [6, 2, -10] = true := by decide +kernel
theorem subd6_1_3132 : subd6_1 [6, 2, -9] = true := by decide +kernel
theorem subd6_1_3133 : subd6_1 [6, 2, -8] = true := by decide +kernel
theorem subd6_1_3134 : subd6_1 [6, 2, -7] = true := by decide +kernel
theorem subd6_1_3135 : subd6_1 [6, 2, -6] = true := by decide +kernel
theorem sbd6_1_97 : ∀ q ∈ blkd6_1_97, subd6_1 q = true := by
  unfold blkd6_1_97
  exact List.forall_mem_cons.2 ⟨subd6_1_3104, List.forall_mem_cons.2 ⟨subd6_1_3105, List.forall_mem_cons.2 ⟨subd6_1_3106, List.forall_mem_cons.2 ⟨subd6_1_3107, List.forall_mem_cons.2 ⟨subd6_1_3108, List.forall_mem_cons.2 ⟨subd6_1_3109, List.forall_mem_cons.2 ⟨subd6_1_3110, List.forall_mem_cons.2 ⟨subd6_1_3111, List.forall_mem_cons.2 ⟨subd6_1_3112, List.forall_mem_cons.2 ⟨subd6_1_3113, List.forall_mem_cons.2 ⟨subd6_1_3114, List.forall_mem_cons.2 ⟨subd6_1_3115, List.forall_mem_cons.2 ⟨subd6_1_3116, List.forall_mem_cons.2 ⟨subd6_1_3117, List.forall_mem_cons.2 ⟨subd6_1_3118, List.forall_mem_cons.2 ⟨subd6_1_3119, List.forall_mem_cons.2 ⟨subd6_1_3120, List.forall_mem_cons.2 ⟨subd6_1_3121, List.forall_mem_cons.2 ⟨subd6_1_3122, List.forall_mem_cons.2 ⟨subd6_1_3123, List.forall_mem_cons.2 ⟨subd6_1_3124, List.forall_mem_cons.2 ⟨subd6_1_3125, List.forall_mem_cons.2 ⟨subd6_1_3126, List.forall_mem_cons.2 ⟨subd6_1_3127, List.forall_mem_cons.2 ⟨subd6_1_3128, List.forall_mem_cons.2 ⟨subd6_1_3129, List.forall_mem_cons.2 ⟨subd6_1_3130, List.forall_mem_cons.2 ⟨subd6_1_3131, List.forall_mem_cons.2 ⟨subd6_1_3132, List.forall_mem_cons.2 ⟨subd6_1_3133, List.forall_mem_cons.2 ⟨subd6_1_3134, List.forall_mem_cons.2 ⟨subd6_1_3135, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
