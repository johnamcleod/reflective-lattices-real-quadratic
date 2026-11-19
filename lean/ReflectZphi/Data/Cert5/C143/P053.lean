import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd17_3_832 : subd17_3 [1, 4, 1] = true := by decide +kernel
theorem subd17_3_833 : subd17_3 [1, 4, 2] = true := by decide +kernel
theorem subd17_3_834 : subd17_3 [1, 4, 3] = true := by decide +kernel
theorem subd17_3_835 : subd17_3 [1, 4, 4] = true := by decide +kernel
theorem subd17_3_836 : subd17_3 [1, 4, 5] = true := by decide +kernel
theorem subd17_3_837 : subd17_3 [1, 4, 6] = true := by decide +kernel
theorem subd17_3_838 : subd17_3 [1, 5, -7] = true := by decide +kernel
theorem subd17_3_839 : subd17_3 [1, 5, -6] = true := by decide +kernel
theorem subd17_3_840 : subd17_3 [1, 5, -5] = true := by decide +kernel
theorem subd17_3_841 : subd17_3 [1, 5, -4] = true := by decide +kernel
theorem subd17_3_842 : subd17_3 [1, 5, -3] = true := by decide +kernel
theorem subd17_3_843 : subd17_3 [1, 5, -2] = true := by decide +kernel
theorem subd17_3_844 : subd17_3 [1, 5, -1] = true := by decide +kernel
theorem subd17_3_845 : subd17_3 [1, 5, 0] = true := by decide +kernel
theorem subd17_3_846 : subd17_3 [1, 5, 1] = true := by decide +kernel
theorem subd17_3_847 : subd17_3 [1, 5, 2] = true := by decide +kernel
theorem subd17_3_848 : subd17_3 [1, 5, 3] = true := by decide +kernel
theorem subd17_3_849 : subd17_3 [1, 5, 4] = true := by decide +kernel
theorem subd17_3_850 : subd17_3 [1, 5, 5] = true := by decide +kernel
theorem subd17_3_851 : subd17_3 [1, 5, 6] = true := by decide +kernel
theorem subd17_3_852 : subd17_3 [1, 6] = true := by decide +kernel
theorem subd17_3_853 : subd17_3 [1, 7] = true := by decide +kernel
theorem subd17_3_854 : subd17_3 [2, -7] = true := by decide +kernel
theorem subd17_3_855 : subd17_3 [2, -6] = true := by decide +kernel
theorem subd17_3_856 : subd17_3 [2, -5] = true := by decide +kernel
theorem subd17_3_857 : subd17_3 [2, -4, -8] = true := by decide +kernel
theorem subd17_3_858 : subd17_3 [2, -4, -7] = true := by decide +kernel
theorem subd17_3_859 : subd17_3 [2, -4, -6] = true := by decide +kernel
theorem subd17_3_860 : subd17_3 [2, -4, -5] = true := by decide +kernel
theorem subd17_3_861 : subd17_3 [2, -4, -4] = true := by decide +kernel
theorem subd17_3_862 : subd17_3 [2, -4, -3] = true := by decide +kernel
theorem subd17_3_863 : subd17_3 [2, -4, -2] = true := by decide +kernel
theorem sbd17_3_26 : ∀ q ∈ blkd17_3_26, subd17_3 q = true := by
  unfold blkd17_3_26
  exact List.forall_mem_cons.2 ⟨subd17_3_832, List.forall_mem_cons.2 ⟨subd17_3_833, List.forall_mem_cons.2 ⟨subd17_3_834, List.forall_mem_cons.2 ⟨subd17_3_835, List.forall_mem_cons.2 ⟨subd17_3_836, List.forall_mem_cons.2 ⟨subd17_3_837, List.forall_mem_cons.2 ⟨subd17_3_838, List.forall_mem_cons.2 ⟨subd17_3_839, List.forall_mem_cons.2 ⟨subd17_3_840, List.forall_mem_cons.2 ⟨subd17_3_841, List.forall_mem_cons.2 ⟨subd17_3_842, List.forall_mem_cons.2 ⟨subd17_3_843, List.forall_mem_cons.2 ⟨subd17_3_844, List.forall_mem_cons.2 ⟨subd17_3_845, List.forall_mem_cons.2 ⟨subd17_3_846, List.forall_mem_cons.2 ⟨subd17_3_847, List.forall_mem_cons.2 ⟨subd17_3_848, List.forall_mem_cons.2 ⟨subd17_3_849, List.forall_mem_cons.2 ⟨subd17_3_850, List.forall_mem_cons.2 ⟨subd17_3_851, List.forall_mem_cons.2 ⟨subd17_3_852, List.forall_mem_cons.2 ⟨subd17_3_853, List.forall_mem_cons.2 ⟨subd17_3_854, List.forall_mem_cons.2 ⟨subd17_3_855, List.forall_mem_cons.2 ⟨subd17_3_856, List.forall_mem_cons.2 ⟨subd17_3_857, List.forall_mem_cons.2 ⟨subd17_3_858, List.forall_mem_cons.2 ⟨subd17_3_859, List.forall_mem_cons.2 ⟨subd17_3_860, List.forall_mem_cons.2 ⟨subd17_3_861, List.forall_mem_cons.2 ⟨subd17_3_862, List.forall_mem_cons.2 ⟨subd17_3_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_864 : subd17_3 [2, -4, -1] = true := by decide +kernel
theorem subd17_3_865 : subd17_3 [2, -4, 0] = true := by decide +kernel
theorem subd17_3_866 : subd17_3 [2, -4, 1] = true := by decide +kernel
theorem subd17_3_867 : subd17_3 [2, -4, 2] = true := by decide +kernel
theorem subd17_3_868 : subd17_3 [2, -4, 3] = true := by decide +kernel
theorem subd17_3_869 : subd17_3 [2, -4, 4] = true := by decide +kernel
theorem subd17_3_870 : subd17_3 [2, -3, -9] = true := by decide +kernel
theorem subd17_3_871 : subd17_3 [2, -3, -8] = true := by decide +kernel
theorem subd17_3_872 : subd17_3 [2, -3, -7] = true := by decide +kernel
theorem subd17_3_873 : subd17_3 [2, -3, -6] = true := by decide +kernel
theorem subd17_3_874 : subd17_3 [2, -3, -5] = true := by decide +kernel
theorem subd17_3_875 : subd17_3 [2, -3, -4] = true := by decide +kernel
theorem subd17_3_876 : subd17_3 [2, -3, -3] = true := by decide +kernel
theorem subd17_3_877 : subd17_3 [2, -3, -2] = true := by decide +kernel
theorem subd17_3_878 : subd17_3 [2, -3, -1] = true := by decide +kernel
theorem subd17_3_879 : subd17_3 [2, -3, 0] = true := by decide +kernel
theorem subd17_3_880 : subd17_3 [2, -3, 1] = true := by decide +kernel
theorem subd17_3_881 : subd17_3 [2, -3, 2] = true := by decide +kernel
theorem subd17_3_882 : subd17_3 [2, -3, 3] = true := by decide +kernel
theorem subd17_3_883 : subd17_3 [2, -3, 4] = true := by decide +kernel
theorem subd17_3_884 : subd17_3 [2, -3, 5] = true := by decide +kernel
theorem subd17_3_885 : subd17_3 [2, -2, -9] = true := by decide +kernel
theorem subd17_3_886 : subd17_3 [2, -2, -8] = true := by decide +kernel
theorem subd17_3_887 : subd17_3 [2, -2, -7] = true := by decide +kernel
theorem subd17_3_888 : subd17_3 [2, -2, -6] = true := by decide +kernel
theorem subd17_3_889 : subd17_3 [2, -2, -5] = true := by decide +kernel
theorem subd17_3_890 : subd17_3 [2, -2, -4] = true := by decide +kernel
theorem subd17_3_891 : subd17_3 [2, -2, -3] = true := by decide +kernel
theorem subd17_3_892 : subd17_3 [2, -2, -2] = true := by decide +kernel
theorem subd17_3_893 : subd17_3 [2, -2, -1] = true := by decide +kernel
theorem subd17_3_894 : subd17_3 [2, -2, 0] = true := by decide +kernel
theorem subd17_3_895 : subd17_3 [2, -2, 1] = true := by decide +kernel
theorem sbd17_3_27 : ∀ q ∈ blkd17_3_27, subd17_3 q = true := by
  unfold blkd17_3_27
  exact List.forall_mem_cons.2 ⟨subd17_3_864, List.forall_mem_cons.2 ⟨subd17_3_865, List.forall_mem_cons.2 ⟨subd17_3_866, List.forall_mem_cons.2 ⟨subd17_3_867, List.forall_mem_cons.2 ⟨subd17_3_868, List.forall_mem_cons.2 ⟨subd17_3_869, List.forall_mem_cons.2 ⟨subd17_3_870, List.forall_mem_cons.2 ⟨subd17_3_871, List.forall_mem_cons.2 ⟨subd17_3_872, List.forall_mem_cons.2 ⟨subd17_3_873, List.forall_mem_cons.2 ⟨subd17_3_874, List.forall_mem_cons.2 ⟨subd17_3_875, List.forall_mem_cons.2 ⟨subd17_3_876, List.forall_mem_cons.2 ⟨subd17_3_877, List.forall_mem_cons.2 ⟨subd17_3_878, List.forall_mem_cons.2 ⟨subd17_3_879, List.forall_mem_cons.2 ⟨subd17_3_880, List.forall_mem_cons.2 ⟨subd17_3_881, List.forall_mem_cons.2 ⟨subd17_3_882, List.forall_mem_cons.2 ⟨subd17_3_883, List.forall_mem_cons.2 ⟨subd17_3_884, List.forall_mem_cons.2 ⟨subd17_3_885, List.forall_mem_cons.2 ⟨subd17_3_886, List.forall_mem_cons.2 ⟨subd17_3_887, List.forall_mem_cons.2 ⟨subd17_3_888, List.forall_mem_cons.2 ⟨subd17_3_889, List.forall_mem_cons.2 ⟨subd17_3_890, List.forall_mem_cons.2 ⟨subd17_3_891, List.forall_mem_cons.2 ⟨subd17_3_892, List.forall_mem_cons.2 ⟨subd17_3_893, List.forall_mem_cons.2 ⟨subd17_3_894, List.forall_mem_cons.2 ⟨subd17_3_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_896 : subd17_3 [2, -2, 2] = true := by decide +kernel
theorem subd17_3_897 : subd17_3 [2, -2, 3] = true := by decide +kernel
theorem subd17_3_898 : subd17_3 [2, -2, 4] = true := by decide +kernel
theorem subd17_3_899 : subd17_3 [2, -2, 5] = true := by decide +kernel
theorem subd17_3_900 : subd17_3 [2, -2, 6] = true := by decide +kernel
theorem subd17_3_901 : subd17_3 [2, -1, -9] = true := by decide +kernel
theorem subd17_3_902 : subd17_3 [2, -1, -8] = true := by decide +kernel
theorem subd17_3_903 : subd17_3 [2, -1, -7] = true := by decide +kernel
theorem subd17_3_904 : subd17_3 [2, -1, -6] = true := by decide +kernel
theorem subd17_3_905 : subd17_3 [2, -1, -5] = true := by decide +kernel
theorem subd17_3_906 : subd17_3 [2, -1, -4] = true := by decide +kernel
theorem subd17_3_907 : subd17_3 [2, -1, -3] = true := by decide +kernel
theorem subd17_3_908 : subd17_3 [2, -1, -2] = true := by decide +kernel
theorem subd17_3_909 : subd17_3 [2, -1, -1] = true := by decide +kernel
theorem subd17_3_910 : subd17_3 [2, -1, 0] = true := by decide +kernel
theorem subd17_3_911 : subd17_3 [2, -1, 1] = true := by decide +kernel
theorem subd17_3_912 : subd17_3 [2, -1, 2] = true := by decide +kernel
theorem subd17_3_913 : subd17_3 [2, -1, 3] = true := by decide +kernel
theorem subd17_3_914 : subd17_3 [2, -1, 4] = true := by decide +kernel
theorem subd17_3_915 : subd17_3 [2, -1, 5] = true := by decide +kernel
theorem subd17_3_916 : subd17_3 [2, -1, 6] = true := by decide +kernel
theorem subd17_3_917 : subd17_3 [2, 0, -9] = true := by decide +kernel
theorem subd17_3_918 : subd17_3 [2, 0, -8] = true := by decide +kernel
theorem subd17_3_919 : subd17_3 [2, 0, -7] = true := by decide +kernel
theorem subd17_3_920 : subd17_3 [2, 0, -6] = true := by decide +kernel
theorem subd17_3_921 : subd17_3 [2, 0, -5] = true := by decide +kernel
theorem subd17_3_922 : subd17_3 [2, 0, -4] = true := by decide +kernel
theorem subd17_3_923 : subd17_3 [2, 0, -3] = true := by decide +kernel
theorem subd17_3_924 : subd17_3 [2, 0, -2] = true := by decide +kernel
theorem subd17_3_925 : subd17_3 [2, 0, -1] = true := by decide +kernel
theorem subd17_3_926 : subd17_3 [2, 0, 0] = true := by decide +kernel
theorem subd17_3_927 : subd17_3 [2, 0, 1] = true := by decide +kernel
theorem sbd17_3_28 : ∀ q ∈ blkd17_3_28, subd17_3 q = true := by
  unfold blkd17_3_28
  exact List.forall_mem_cons.2 ⟨subd17_3_896, List.forall_mem_cons.2 ⟨subd17_3_897, List.forall_mem_cons.2 ⟨subd17_3_898, List.forall_mem_cons.2 ⟨subd17_3_899, List.forall_mem_cons.2 ⟨subd17_3_900, List.forall_mem_cons.2 ⟨subd17_3_901, List.forall_mem_cons.2 ⟨subd17_3_902, List.forall_mem_cons.2 ⟨subd17_3_903, List.forall_mem_cons.2 ⟨subd17_3_904, List.forall_mem_cons.2 ⟨subd17_3_905, List.forall_mem_cons.2 ⟨subd17_3_906, List.forall_mem_cons.2 ⟨subd17_3_907, List.forall_mem_cons.2 ⟨subd17_3_908, List.forall_mem_cons.2 ⟨subd17_3_909, List.forall_mem_cons.2 ⟨subd17_3_910, List.forall_mem_cons.2 ⟨subd17_3_911, List.forall_mem_cons.2 ⟨subd17_3_912, List.forall_mem_cons.2 ⟨subd17_3_913, List.forall_mem_cons.2 ⟨subd17_3_914, List.forall_mem_cons.2 ⟨subd17_3_915, List.forall_mem_cons.2 ⟨subd17_3_916, List.forall_mem_cons.2 ⟨subd17_3_917, List.forall_mem_cons.2 ⟨subd17_3_918, List.forall_mem_cons.2 ⟨subd17_3_919, List.forall_mem_cons.2 ⟨subd17_3_920, List.forall_mem_cons.2 ⟨subd17_3_921, List.forall_mem_cons.2 ⟨subd17_3_922, List.forall_mem_cons.2 ⟨subd17_3_923, List.forall_mem_cons.2 ⟨subd17_3_924, List.forall_mem_cons.2 ⟨subd17_3_925, List.forall_mem_cons.2 ⟨subd17_3_926, List.forall_mem_cons.2 ⟨subd17_3_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_928 : subd17_3 [2, 0, 2] = true := by decide +kernel
theorem subd17_3_929 : subd17_3 [2, 0, 3] = true := by decide +kernel
theorem subd17_3_930 : subd17_3 [2, 0, 4] = true := by decide +kernel
theorem subd17_3_931 : subd17_3 [2, 0, 5] = true := by decide +kernel
theorem subd17_3_932 : subd17_3 [2, 0, 6] = true := by decide +kernel
theorem subd17_3_933 : subd17_3 [2, 0, 7] = true := by decide +kernel
theorem subd17_3_934 : subd17_3 [2, 1, -9] = true := by decide +kernel
theorem subd17_3_935 : subd17_3 [2, 1, -8] = true := by decide +kernel
theorem subd17_3_936 : subd17_3 [2, 1, -7] = true := by decide +kernel
theorem subd17_3_937 : subd17_3 [2, 1, -6] = true := by decide +kernel
theorem subd17_3_938 : subd17_3 [2, 1, -5] = true := by decide +kernel
theorem subd17_3_939 : subd17_3 [2, 1, -4] = true := by decide +kernel
theorem subd17_3_940 : subd17_3 [2, 1, -3] = true := by decide +kernel
theorem subd17_3_941 : subd17_3 [2, 1, -2] = true := by decide +kernel
theorem subd17_3_942 : subd17_3 [2, 1, -1] = true := by decide +kernel
theorem subd17_3_943 : subd17_3 [2, 1, 0] = true := by decide +kernel
theorem subd17_3_944 : subd17_3 [2, 1, 1] = true := by decide +kernel
theorem subd17_3_945 : subd17_3 [2, 1, 2] = true := by decide +kernel
theorem subd17_3_946 : subd17_3 [2, 1, 3] = true := by decide +kernel
theorem subd17_3_947 : subd17_3 [2, 1, 4] = true := by decide +kernel
theorem subd17_3_948 : subd17_3 [2, 1, 5] = true := by decide +kernel
theorem subd17_3_949 : subd17_3 [2, 1, 6] = true := by decide +kernel
theorem subd17_3_950 : subd17_3 [2, 1, 7] = true := by decide +kernel
theorem subd17_3_951 : subd17_3 [2, 2, -9] = true := by decide +kernel
theorem subd17_3_952 : subd17_3 [2, 2, -8] = true := by decide +kernel
theorem subd17_3_953 : subd17_3 [2, 2, -7] = true := by decide +kernel
theorem subd17_3_954 : subd17_3 [2, 2, -6] = true := by decide +kernel
theorem subd17_3_955 : subd17_3 [2, 2, -5] = true := by decide +kernel
theorem subd17_3_956 : subd17_3 [2, 2, -4] = true := by decide +kernel
theorem subd17_3_957 : subd17_3 [2, 2, -3] = true := by decide +kernel
theorem subd17_3_958 : subd17_3 [2, 2, -2] = true := by decide +kernel
theorem subd17_3_959 : subd17_3 [2, 2, -1] = true := by decide +kernel
theorem sbd17_3_29 : ∀ q ∈ blkd17_3_29, subd17_3 q = true := by
  unfold blkd17_3_29
  exact List.forall_mem_cons.2 ⟨subd17_3_928, List.forall_mem_cons.2 ⟨subd17_3_929, List.forall_mem_cons.2 ⟨subd17_3_930, List.forall_mem_cons.2 ⟨subd17_3_931, List.forall_mem_cons.2 ⟨subd17_3_932, List.forall_mem_cons.2 ⟨subd17_3_933, List.forall_mem_cons.2 ⟨subd17_3_934, List.forall_mem_cons.2 ⟨subd17_3_935, List.forall_mem_cons.2 ⟨subd17_3_936, List.forall_mem_cons.2 ⟨subd17_3_937, List.forall_mem_cons.2 ⟨subd17_3_938, List.forall_mem_cons.2 ⟨subd17_3_939, List.forall_mem_cons.2 ⟨subd17_3_940, List.forall_mem_cons.2 ⟨subd17_3_941, List.forall_mem_cons.2 ⟨subd17_3_942, List.forall_mem_cons.2 ⟨subd17_3_943, List.forall_mem_cons.2 ⟨subd17_3_944, List.forall_mem_cons.2 ⟨subd17_3_945, List.forall_mem_cons.2 ⟨subd17_3_946, List.forall_mem_cons.2 ⟨subd17_3_947, List.forall_mem_cons.2 ⟨subd17_3_948, List.forall_mem_cons.2 ⟨subd17_3_949, List.forall_mem_cons.2 ⟨subd17_3_950, List.forall_mem_cons.2 ⟨subd17_3_951, List.forall_mem_cons.2 ⟨subd17_3_952, List.forall_mem_cons.2 ⟨subd17_3_953, List.forall_mem_cons.2 ⟨subd17_3_954, List.forall_mem_cons.2 ⟨subd17_3_955, List.forall_mem_cons.2 ⟨subd17_3_956, List.forall_mem_cons.2 ⟨subd17_3_957, List.forall_mem_cons.2 ⟨subd17_3_958, List.forall_mem_cons.2 ⟨subd17_3_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_960 : subd17_3 [2, 2, 0] = true := by decide +kernel
theorem subd17_3_961 : subd17_3 [2, 2, 1] = true := by decide +kernel
theorem subd17_3_962 : subd17_3 [2, 2, 2] = true := by decide +kernel
theorem subd17_3_963 : subd17_3 [2, 2, 3] = true := by decide +kernel
theorem subd17_3_964 : subd17_3 [2, 2, 4] = true := by decide +kernel
theorem subd17_3_965 : subd17_3 [2, 2, 5] = true := by decide +kernel
theorem subd17_3_966 : subd17_3 [2, 2, 6] = true := by decide +kernel
theorem subd17_3_967 : subd17_3 [2, 2, 7] = true := by decide +kernel
theorem subd17_3_968 : subd17_3 [2, 3, -9] = true := by decide +kernel
theorem subd17_3_969 : subd17_3 [2, 3, -8] = true := by decide +kernel
theorem subd17_3_970 : subd17_3 [2, 3, -7] = true := by decide +kernel
theorem subd17_3_971 : subd17_3 [2, 3, -6] = true := by decide +kernel
theorem subd17_3_972 : subd17_3 [2, 3, -5] = true := by decide +kernel
theorem subd17_3_973 : subd17_3 [2, 3, -4] = true := by decide +kernel
theorem subd17_3_974 : subd17_3 [2, 3, -3] = true := by decide +kernel
theorem subd17_3_975 : subd17_3 [2, 3, -2] = true := by decide +kernel
theorem subd17_3_976 : subd17_3 [2, 3, -1] = true := by decide +kernel
theorem subd17_3_977 : subd17_3 [2, 3, 0] = true := by decide +kernel
theorem subd17_3_978 : subd17_3 [2, 3, 1] = true := by decide +kernel
theorem subd17_3_979 : subd17_3 [2, 3, 2] = true := by decide +kernel
theorem subd17_3_980 : subd17_3 [2, 3, 3] = true := by decide +kernel
theorem subd17_3_981 : subd17_3 [2, 3, 4] = true := by decide +kernel
theorem subd17_3_982 : subd17_3 [2, 3, 5] = true := by decide +kernel
theorem subd17_3_983 : subd17_3 [2, 3, 6] = true := by decide +kernel
theorem subd17_3_984 : subd17_3 [2, 4, -8] = true := by decide +kernel
theorem subd17_3_985 : subd17_3 [2, 4, -7] = true := by decide +kernel
theorem subd17_3_986 : subd17_3 [2, 4, -6] = true := by decide +kernel
theorem subd17_3_987 : subd17_3 [2, 4, -5] = true := by decide +kernel
theorem subd17_3_988 : subd17_3 [2, 4, -4] = true := by decide +kernel
theorem subd17_3_989 : subd17_3 [2, 4, -3] = true := by decide +kernel
theorem subd17_3_990 : subd17_3 [2, 4, -2] = true := by decide +kernel
theorem subd17_3_991 : subd17_3 [2, 4, -1] = true := by decide +kernel
theorem sbd17_3_30 : ∀ q ∈ blkd17_3_30, subd17_3 q = true := by
  unfold blkd17_3_30
  exact List.forall_mem_cons.2 ⟨subd17_3_960, List.forall_mem_cons.2 ⟨subd17_3_961, List.forall_mem_cons.2 ⟨subd17_3_962, List.forall_mem_cons.2 ⟨subd17_3_963, List.forall_mem_cons.2 ⟨subd17_3_964, List.forall_mem_cons.2 ⟨subd17_3_965, List.forall_mem_cons.2 ⟨subd17_3_966, List.forall_mem_cons.2 ⟨subd17_3_967, List.forall_mem_cons.2 ⟨subd17_3_968, List.forall_mem_cons.2 ⟨subd17_3_969, List.forall_mem_cons.2 ⟨subd17_3_970, List.forall_mem_cons.2 ⟨subd17_3_971, List.forall_mem_cons.2 ⟨subd17_3_972, List.forall_mem_cons.2 ⟨subd17_3_973, List.forall_mem_cons.2 ⟨subd17_3_974, List.forall_mem_cons.2 ⟨subd17_3_975, List.forall_mem_cons.2 ⟨subd17_3_976, List.forall_mem_cons.2 ⟨subd17_3_977, List.forall_mem_cons.2 ⟨subd17_3_978, List.forall_mem_cons.2 ⟨subd17_3_979, List.forall_mem_cons.2 ⟨subd17_3_980, List.forall_mem_cons.2 ⟨subd17_3_981, List.forall_mem_cons.2 ⟨subd17_3_982, List.forall_mem_cons.2 ⟨subd17_3_983, List.forall_mem_cons.2 ⟨subd17_3_984, List.forall_mem_cons.2 ⟨subd17_3_985, List.forall_mem_cons.2 ⟨subd17_3_986, List.forall_mem_cons.2 ⟨subd17_3_987, List.forall_mem_cons.2 ⟨subd17_3_988, List.forall_mem_cons.2 ⟨subd17_3_989, List.forall_mem_cons.2 ⟨subd17_3_990, List.forall_mem_cons.2 ⟨subd17_3_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_992 : subd17_3 [2, 4, 0] = true := by decide +kernel
theorem subd17_3_993 : subd17_3 [2, 4, 1] = true := by decide +kernel
theorem subd17_3_994 : subd17_3 [2, 4, 2] = true := by decide +kernel
theorem subd17_3_995 : subd17_3 [2, 4, 3] = true := by decide +kernel
theorem subd17_3_996 : subd17_3 [2, 4, 4] = true := by decide +kernel
theorem subd17_3_997 : subd17_3 [2, 4, 5] = true := by decide +kernel
theorem subd17_3_998 : subd17_3 [2, 4, 6] = true := by decide +kernel
theorem subd17_3_999 : subd17_3 [2, 5] = true := by decide +kernel
theorem subd17_3_1000 : subd17_3 [2, 6] = true := by decide +kernel
theorem subd17_3_1001 : subd17_3 [2, 7] = true := by decide +kernel
theorem subd17_3_1002 : subd17_3 [3, -6] = true := by decide +kernel
theorem subd17_3_1003 : subd17_3 [3, -5] = true := by decide +kernel
theorem subd17_3_1004 : subd17_3 [3, -4] = true := by decide +kernel
theorem subd17_3_1005 : subd17_3 [3, -3, -8] = true := by decide +kernel
theorem subd17_3_1006 : subd17_3 [3, -3, -7] = true := by decide +kernel
theorem subd17_3_1007 : subd17_3 [3, -3, -6] = true := by decide +kernel
theorem subd17_3_1008 : subd17_3 [3, -3, -5] = true := by decide +kernel
theorem subd17_3_1009 : subd17_3 [3, -3, -4] = true := by decide +kernel
theorem subd17_3_1010 : subd17_3 [3, -3, -3] = true := by decide +kernel
theorem subd17_3_1011 : subd17_3 [3, -3, -2] = true := by decide +kernel
theorem subd17_3_1012 : subd17_3 [3, -3, -1] = true := by decide +kernel
theorem subd17_3_1013 : subd17_3 [3, -3, 0] = true := by decide +kernel
theorem subd17_3_1014 : subd17_3 [3, -3, 1] = true := by decide +kernel
theorem subd17_3_1015 : subd17_3 [3, -3, 2] = true := by decide +kernel
theorem subd17_3_1016 : subd17_3 [3, -3, 3] = true := by decide +kernel
theorem subd17_3_1017 : subd17_3 [3, -3, 4] = true := by decide +kernel
theorem subd17_3_1018 : subd17_3 [3, -2, -9] = true := by decide +kernel
theorem subd17_3_1019 : subd17_3 [3, -2, -8] = true := by decide +kernel
theorem subd17_3_1020 : subd17_3 [3, -2, -7] = true := by decide +kernel
theorem subd17_3_1021 : subd17_3 [3, -2, -6] = true := by decide +kernel
theorem subd17_3_1022 : subd17_3 [3, -2, -5] = true := by decide +kernel
theorem subd17_3_1023 : subd17_3 [3, -2, -4] = true := by decide +kernel
theorem sbd17_3_31 : ∀ q ∈ blkd17_3_31, subd17_3 q = true := by
  unfold blkd17_3_31
  exact List.forall_mem_cons.2 ⟨subd17_3_992, List.forall_mem_cons.2 ⟨subd17_3_993, List.forall_mem_cons.2 ⟨subd17_3_994, List.forall_mem_cons.2 ⟨subd17_3_995, List.forall_mem_cons.2 ⟨subd17_3_996, List.forall_mem_cons.2 ⟨subd17_3_997, List.forall_mem_cons.2 ⟨subd17_3_998, List.forall_mem_cons.2 ⟨subd17_3_999, List.forall_mem_cons.2 ⟨subd17_3_1000, List.forall_mem_cons.2 ⟨subd17_3_1001, List.forall_mem_cons.2 ⟨subd17_3_1002, List.forall_mem_cons.2 ⟨subd17_3_1003, List.forall_mem_cons.2 ⟨subd17_3_1004, List.forall_mem_cons.2 ⟨subd17_3_1005, List.forall_mem_cons.2 ⟨subd17_3_1006, List.forall_mem_cons.2 ⟨subd17_3_1007, List.forall_mem_cons.2 ⟨subd17_3_1008, List.forall_mem_cons.2 ⟨subd17_3_1009, List.forall_mem_cons.2 ⟨subd17_3_1010, List.forall_mem_cons.2 ⟨subd17_3_1011, List.forall_mem_cons.2 ⟨subd17_3_1012, List.forall_mem_cons.2 ⟨subd17_3_1013, List.forall_mem_cons.2 ⟨subd17_3_1014, List.forall_mem_cons.2 ⟨subd17_3_1015, List.forall_mem_cons.2 ⟨subd17_3_1016, List.forall_mem_cons.2 ⟨subd17_3_1017, List.forall_mem_cons.2 ⟨subd17_3_1018, List.forall_mem_cons.2 ⟨subd17_3_1019, List.forall_mem_cons.2 ⟨subd17_3_1020, List.forall_mem_cons.2 ⟨subd17_3_1021, List.forall_mem_cons.2 ⟨subd17_3_1022, List.forall_mem_cons.2 ⟨subd17_3_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_1024 : subd17_3 [3, -2, -3] = true := by decide +kernel
theorem subd17_3_1025 : subd17_3 [3, -2, -2] = true := by decide +kernel
theorem subd17_3_1026 : subd17_3 [3, -2, -1] = true := by decide +kernel
theorem subd17_3_1027 : subd17_3 [3, -2, 0] = true := by decide +kernel
theorem subd17_3_1028 : subd17_3 [3, -2, 1] = true := by decide +kernel
theorem subd17_3_1029 : subd17_3 [3, -2, 2] = true := by decide +kernel
theorem subd17_3_1030 : subd17_3 [3, -2, 3] = true := by decide +kernel
theorem subd17_3_1031 : subd17_3 [3, -2, 4] = true := by decide +kernel
theorem subd17_3_1032 : subd17_3 [3, -2, 5] = true := by decide +kernel
theorem subd17_3_1033 : subd17_3 [3, -1, -9] = true := by decide +kernel
theorem subd17_3_1034 : subd17_3 [3, -1, -8] = true := by decide +kernel
theorem subd17_3_1035 : subd17_3 [3, -1, -7] = true := by decide +kernel
theorem subd17_3_1036 : subd17_3 [3, -1, -6] = true := by decide +kernel
theorem subd17_3_1037 : subd17_3 [3, -1, -5] = true := by decide +kernel
theorem subd17_3_1038 : subd17_3 [3, -1, -4] = true := by decide +kernel
theorem subd17_3_1039 : subd17_3 [3, -1, -3] = true := by decide +kernel
theorem subd17_3_1040 : subd17_3 [3, -1, -2] = true := by decide +kernel
theorem subd17_3_1041 : subd17_3 [3, -1, -1] = true := by decide +kernel
theorem subd17_3_1042 : subd17_3 [3, -1, 0] = true := by decide +kernel
theorem subd17_3_1043 : subd17_3 [3, -1, 1] = true := by decide +kernel
theorem subd17_3_1044 : subd17_3 [3, -1, 2] = true := by decide +kernel
theorem subd17_3_1045 : subd17_3 [3, -1, 3] = true := by decide +kernel
theorem subd17_3_1046 : subd17_3 [3, -1, 4] = true := by decide +kernel
theorem subd17_3_1047 : subd17_3 [3, -1, 5] = true := by decide +kernel
theorem subd17_3_1048 : subd17_3 [3, 0, -9] = true := by decide +kernel
theorem subd17_3_1049 : subd17_3 [3, 0, -8] = true := by decide +kernel
theorem subd17_3_1050 : subd17_3 [3, 0, -7] = true := by decide +kernel
theorem subd17_3_1051 : subd17_3 [3, 0, -6] = true := by decide +kernel
theorem subd17_3_1052 : subd17_3 [3, 0, -5] = true := by decide +kernel
theorem subd17_3_1053 : subd17_3 [3, 0, -4] = true := by decide +kernel
theorem subd17_3_1054 : subd17_3 [3, 0, -3] = true := by decide +kernel
theorem subd17_3_1055 : subd17_3 [3, 0, -2] = true := by decide +kernel
theorem sbd17_3_32 : ∀ q ∈ blkd17_3_32, subd17_3 q = true := by
  unfold blkd17_3_32
  exact List.forall_mem_cons.2 ⟨subd17_3_1024, List.forall_mem_cons.2 ⟨subd17_3_1025, List.forall_mem_cons.2 ⟨subd17_3_1026, List.forall_mem_cons.2 ⟨subd17_3_1027, List.forall_mem_cons.2 ⟨subd17_3_1028, List.forall_mem_cons.2 ⟨subd17_3_1029, List.forall_mem_cons.2 ⟨subd17_3_1030, List.forall_mem_cons.2 ⟨subd17_3_1031, List.forall_mem_cons.2 ⟨subd17_3_1032, List.forall_mem_cons.2 ⟨subd17_3_1033, List.forall_mem_cons.2 ⟨subd17_3_1034, List.forall_mem_cons.2 ⟨subd17_3_1035, List.forall_mem_cons.2 ⟨subd17_3_1036, List.forall_mem_cons.2 ⟨subd17_3_1037, List.forall_mem_cons.2 ⟨subd17_3_1038, List.forall_mem_cons.2 ⟨subd17_3_1039, List.forall_mem_cons.2 ⟨subd17_3_1040, List.forall_mem_cons.2 ⟨subd17_3_1041, List.forall_mem_cons.2 ⟨subd17_3_1042, List.forall_mem_cons.2 ⟨subd17_3_1043, List.forall_mem_cons.2 ⟨subd17_3_1044, List.forall_mem_cons.2 ⟨subd17_3_1045, List.forall_mem_cons.2 ⟨subd17_3_1046, List.forall_mem_cons.2 ⟨subd17_3_1047, List.forall_mem_cons.2 ⟨subd17_3_1048, List.forall_mem_cons.2 ⟨subd17_3_1049, List.forall_mem_cons.2 ⟨subd17_3_1050, List.forall_mem_cons.2 ⟨subd17_3_1051, List.forall_mem_cons.2 ⟨subd17_3_1052, List.forall_mem_cons.2 ⟨subd17_3_1053, List.forall_mem_cons.2 ⟨subd17_3_1054, List.forall_mem_cons.2 ⟨subd17_3_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_1056 : subd17_3 [3, 0, -1] = true := by decide +kernel
theorem subd17_3_1057 : subd17_3 [3, 0, 0] = true := by decide +kernel
theorem subd17_3_1058 : subd17_3 [3, 0, 1] = true := by decide +kernel
theorem subd17_3_1059 : subd17_3 [3, 0, 2] = true := by decide +kernel
theorem subd17_3_1060 : subd17_3 [3, 0, 3] = true := by decide +kernel
theorem subd17_3_1061 : subd17_3 [3, 0, 4] = true := by decide +kernel
theorem subd17_3_1062 : subd17_3 [3, 0, 5] = true := by decide +kernel
theorem subd17_3_1063 : subd17_3 [3, 0, 6] = true := by decide +kernel
theorem subd17_3_1064 : subd17_3 [3, 1, -9] = true := by decide +kernel
theorem subd17_3_1065 : subd17_3 [3, 1, -8] = true := by decide +kernel
theorem subd17_3_1066 : subd17_3 [3, 1, -7] = true := by decide +kernel
theorem subd17_3_1067 : subd17_3 [3, 1, -6] = true := by decide +kernel
theorem subd17_3_1068 : subd17_3 [3, 1, -5] = true := by decide +kernel
theorem subd17_3_1069 : subd17_3 [3, 1, -4] = true := by decide +kernel
theorem subd17_3_1070 : subd17_3 [3, 1, -3] = true := by decide +kernel
theorem subd17_3_1071 : subd17_3 [3, 1, -2] = true := by decide +kernel
theorem subd17_3_1072 : subd17_3 [3, 1, -1] = true := by decide +kernel
theorem subd17_3_1073 : subd17_3 [3, 1, 0] = true := by decide +kernel
theorem subd17_3_1074 : subd17_3 [3, 1, 1] = true := by decide +kernel
theorem subd17_3_1075 : subd17_3 [3, 1, 2] = true := by decide +kernel
theorem subd17_3_1076 : subd17_3 [3, 1, 3] = true := by decide +kernel
theorem subd17_3_1077 : subd17_3 [3, 1, 4] = true := by decide +kernel
theorem subd17_3_1078 : subd17_3 [3, 1, 5] = true := by decide +kernel
theorem subd17_3_1079 : subd17_3 [3, 1, 6] = true := by decide +kernel
theorem subd17_3_1080 : subd17_3 [3, 2, -9] = true := by decide +kernel
theorem subd17_3_1081 : subd17_3 [3, 2, -8] = true := by decide +kernel
theorem subd17_3_1082 : subd17_3 [3, 2, -7] = true := by decide +kernel
theorem subd17_3_1083 : subd17_3 [3, 2, -6] = true := by decide +kernel
theorem subd17_3_1084 : subd17_3 [3, 2, -5] = true := by decide +kernel
theorem subd17_3_1085 : subd17_3 [3, 2, -4] = true := by decide +kernel
theorem subd17_3_1086 : subd17_3 [3, 2, -3] = true := by decide +kernel
theorem subd17_3_1087 : subd17_3 [3, 2, -2] = true := by decide +kernel
theorem sbd17_3_33 : ∀ q ∈ blkd17_3_33, subd17_3 q = true := by
  unfold blkd17_3_33
  exact List.forall_mem_cons.2 ⟨subd17_3_1056, List.forall_mem_cons.2 ⟨subd17_3_1057, List.forall_mem_cons.2 ⟨subd17_3_1058, List.forall_mem_cons.2 ⟨subd17_3_1059, List.forall_mem_cons.2 ⟨subd17_3_1060, List.forall_mem_cons.2 ⟨subd17_3_1061, List.forall_mem_cons.2 ⟨subd17_3_1062, List.forall_mem_cons.2 ⟨subd17_3_1063, List.forall_mem_cons.2 ⟨subd17_3_1064, List.forall_mem_cons.2 ⟨subd17_3_1065, List.forall_mem_cons.2 ⟨subd17_3_1066, List.forall_mem_cons.2 ⟨subd17_3_1067, List.forall_mem_cons.2 ⟨subd17_3_1068, List.forall_mem_cons.2 ⟨subd17_3_1069, List.forall_mem_cons.2 ⟨subd17_3_1070, List.forall_mem_cons.2 ⟨subd17_3_1071, List.forall_mem_cons.2 ⟨subd17_3_1072, List.forall_mem_cons.2 ⟨subd17_3_1073, List.forall_mem_cons.2 ⟨subd17_3_1074, List.forall_mem_cons.2 ⟨subd17_3_1075, List.forall_mem_cons.2 ⟨subd17_3_1076, List.forall_mem_cons.2 ⟨subd17_3_1077, List.forall_mem_cons.2 ⟨subd17_3_1078, List.forall_mem_cons.2 ⟨subd17_3_1079, List.forall_mem_cons.2 ⟨subd17_3_1080, List.forall_mem_cons.2 ⟨subd17_3_1081, List.forall_mem_cons.2 ⟨subd17_3_1082, List.forall_mem_cons.2 ⟨subd17_3_1083, List.forall_mem_cons.2 ⟨subd17_3_1084, List.forall_mem_cons.2 ⟨subd17_3_1085, List.forall_mem_cons.2 ⟨subd17_3_1086, List.forall_mem_cons.2 ⟨subd17_3_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_1088 : subd17_3 [3, 2, -1] = true := by decide +kernel
theorem subd17_3_1089 : subd17_3 [3, 2, 0] = true := by decide +kernel
theorem subd17_3_1090 : subd17_3 [3, 2, 1] = true := by decide +kernel
theorem subd17_3_1091 : subd17_3 [3, 2, 2] = true := by decide +kernel
theorem subd17_3_1092 : subd17_3 [3, 2, 3] = true := by decide +kernel
theorem subd17_3_1093 : subd17_3 [3, 2, 4] = true := by decide +kernel
theorem subd17_3_1094 : subd17_3 [3, 2, 5] = true := by decide +kernel
theorem subd17_3_1095 : subd17_3 [3, 2, 6] = true := by decide +kernel
theorem subd17_3_1096 : subd17_3 [3, 3, -9] = true := by decide +kernel
theorem subd17_3_1097 : subd17_3 [3, 3, -8] = true := by decide +kernel
theorem subd17_3_1098 : subd17_3 [3, 3, -7] = true := by decide +kernel
theorem subd17_3_1099 : subd17_3 [3, 3, -6] = true := by decide +kernel
theorem subd17_3_1100 : subd17_3 [3, 3, -5] = true := by decide +kernel
theorem subd17_3_1101 : subd17_3 [3, 3, -4] = true := by decide +kernel
theorem subd17_3_1102 : subd17_3 [3, 3, -3] = true := by decide +kernel
theorem subd17_3_1103 : subd17_3 [3, 3, -2] = true := by decide +kernel
theorem subd17_3_1104 : subd17_3 [3, 3, -1] = true := by decide +kernel
theorem subd17_3_1105 : subd17_3 [3, 3, 0] = true := by decide +kernel
theorem subd17_3_1106 : subd17_3 [3, 3, 1] = true := by decide +kernel
theorem subd17_3_1107 : subd17_3 [3, 3, 2] = true := by decide +kernel
theorem subd17_3_1108 : subd17_3 [3, 3, 3] = true := by decide +kernel
theorem subd17_3_1109 : subd17_3 [3, 3, 4] = true := by decide +kernel
theorem subd17_3_1110 : subd17_3 [3, 3, 5] = true := by decide +kernel
theorem subd17_3_1111 : subd17_3 [3, 4, -8] = true := by decide +kernel
theorem subd17_3_1112 : subd17_3 [3, 4, -7] = true := by decide +kernel
theorem subd17_3_1113 : subd17_3 [3, 4, -6] = true := by decide +kernel
theorem subd17_3_1114 : subd17_3 [3, 4, -5] = true := by decide +kernel
theorem subd17_3_1115 : subd17_3 [3, 4, -4] = true := by decide +kernel
theorem subd17_3_1116 : subd17_3 [3, 4, -3] = true := by decide +kernel
theorem subd17_3_1117 : subd17_3 [3, 4, -2] = true := by decide +kernel
theorem subd17_3_1118 : subd17_3 [3, 4, -1] = true := by decide +kernel
theorem subd17_3_1119 : subd17_3 [3, 4, 0] = true := by decide +kernel
theorem sbd17_3_34 : ∀ q ∈ blkd17_3_34, subd17_3 q = true := by
  unfold blkd17_3_34
  exact List.forall_mem_cons.2 ⟨subd17_3_1088, List.forall_mem_cons.2 ⟨subd17_3_1089, List.forall_mem_cons.2 ⟨subd17_3_1090, List.forall_mem_cons.2 ⟨subd17_3_1091, List.forall_mem_cons.2 ⟨subd17_3_1092, List.forall_mem_cons.2 ⟨subd17_3_1093, List.forall_mem_cons.2 ⟨subd17_3_1094, List.forall_mem_cons.2 ⟨subd17_3_1095, List.forall_mem_cons.2 ⟨subd17_3_1096, List.forall_mem_cons.2 ⟨subd17_3_1097, List.forall_mem_cons.2 ⟨subd17_3_1098, List.forall_mem_cons.2 ⟨subd17_3_1099, List.forall_mem_cons.2 ⟨subd17_3_1100, List.forall_mem_cons.2 ⟨subd17_3_1101, List.forall_mem_cons.2 ⟨subd17_3_1102, List.forall_mem_cons.2 ⟨subd17_3_1103, List.forall_mem_cons.2 ⟨subd17_3_1104, List.forall_mem_cons.2 ⟨subd17_3_1105, List.forall_mem_cons.2 ⟨subd17_3_1106, List.forall_mem_cons.2 ⟨subd17_3_1107, List.forall_mem_cons.2 ⟨subd17_3_1108, List.forall_mem_cons.2 ⟨subd17_3_1109, List.forall_mem_cons.2 ⟨subd17_3_1110, List.forall_mem_cons.2 ⟨subd17_3_1111, List.forall_mem_cons.2 ⟨subd17_3_1112, List.forall_mem_cons.2 ⟨subd17_3_1113, List.forall_mem_cons.2 ⟨subd17_3_1114, List.forall_mem_cons.2 ⟨subd17_3_1115, List.forall_mem_cons.2 ⟨subd17_3_1116, List.forall_mem_cons.2 ⟨subd17_3_1117, List.forall_mem_cons.2 ⟨subd17_3_1118, List.forall_mem_cons.2 ⟨subd17_3_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_1120 : subd17_3 [3, 4, 1] = true := by decide +kernel
theorem subd17_3_1121 : subd17_3 [3, 4, 2] = true := by decide +kernel
theorem subd17_3_1122 : subd17_3 [3, 4, 3] = true := by decide +kernel
theorem subd17_3_1123 : subd17_3 [3, 4, 4] = true := by decide +kernel
theorem subd17_3_1124 : subd17_3 [3, 4, 5] = true := by decide +kernel
theorem subd17_3_1125 : subd17_3 [3, 5] = true := by decide +kernel
theorem subd17_3_1126 : subd17_3 [3, 6] = true := by decide +kernel
theorem subd17_3_1127 : subd17_3 [3, 7] = true := by decide +kernel
theorem subd17_3_1128 : subd17_3 [4, -5] = true := by decide +kernel
theorem subd17_3_1129 : subd17_3 [4, -4] = true := by decide +kernel
theorem subd17_3_1130 : subd17_3 [4, -3] = true := by decide +kernel
theorem subd17_3_1131 : subd17_3 [4, -2] = true := by decide +kernel
theorem subd17_3_1132 : subd17_3 [4, -1, -9] = true := by decide +kernel
theorem subd17_3_1133 : subd17_3 [4, -1, -8] = true := by decide +kernel
theorem subd17_3_1134 : subd17_3 [4, -1, -7] = true := by decide +kernel
theorem subd17_3_1135 : subd17_3 [4, -1, -6] = true := by decide +kernel
theorem subd17_3_1136 : subd17_3 [4, -1, -5] = true := by decide +kernel
theorem subd17_3_1137 : subd17_3 [4, -1, -4] = true := by decide +kernel
theorem subd17_3_1138 : subd17_3 [4, -1, -3] = true := by decide +kernel
theorem subd17_3_1139 : subd17_3 [4, -1, -2] = true := by decide +kernel
theorem subd17_3_1140 : subd17_3 [4, -1, -1] = true := by decide +kernel
theorem subd17_3_1141 : subd17_3 [4, -1, 0] = true := by decide +kernel
theorem subd17_3_1142 : subd17_3 [4, -1, 1] = true := by decide +kernel
theorem subd17_3_1143 : subd17_3 [4, -1, 2] = true := by decide +kernel
theorem subd17_3_1144 : subd17_3 [4, -1, 3] = true := by decide +kernel
theorem subd17_3_1145 : subd17_3 [4, -1, 4] = true := by decide +kernel
theorem subd17_3_1146 : subd17_3 [4, 0, -9] = true := by decide +kernel
theorem subd17_3_1147 : subd17_3 [4, 0, -8] = true := by decide +kernel
theorem subd17_3_1148 : subd17_3 [4, 0, -7] = true := by decide +kernel
theorem subd17_3_1149 : subd17_3 [4, 0, -6] = true := by decide +kernel
theorem subd17_3_1150 : subd17_3 [4, 0, -5] = true := by decide +kernel
theorem subd17_3_1151 : subd17_3 [4, 0, -4] = true := by decide +kernel
theorem sbd17_3_35 : ∀ q ∈ blkd17_3_35, subd17_3 q = true := by
  unfold blkd17_3_35
  exact List.forall_mem_cons.2 ⟨subd17_3_1120, List.forall_mem_cons.2 ⟨subd17_3_1121, List.forall_mem_cons.2 ⟨subd17_3_1122, List.forall_mem_cons.2 ⟨subd17_3_1123, List.forall_mem_cons.2 ⟨subd17_3_1124, List.forall_mem_cons.2 ⟨subd17_3_1125, List.forall_mem_cons.2 ⟨subd17_3_1126, List.forall_mem_cons.2 ⟨subd17_3_1127, List.forall_mem_cons.2 ⟨subd17_3_1128, List.forall_mem_cons.2 ⟨subd17_3_1129, List.forall_mem_cons.2 ⟨subd17_3_1130, List.forall_mem_cons.2 ⟨subd17_3_1131, List.forall_mem_cons.2 ⟨subd17_3_1132, List.forall_mem_cons.2 ⟨subd17_3_1133, List.forall_mem_cons.2 ⟨subd17_3_1134, List.forall_mem_cons.2 ⟨subd17_3_1135, List.forall_mem_cons.2 ⟨subd17_3_1136, List.forall_mem_cons.2 ⟨subd17_3_1137, List.forall_mem_cons.2 ⟨subd17_3_1138, List.forall_mem_cons.2 ⟨subd17_3_1139, List.forall_mem_cons.2 ⟨subd17_3_1140, List.forall_mem_cons.2 ⟨subd17_3_1141, List.forall_mem_cons.2 ⟨subd17_3_1142, List.forall_mem_cons.2 ⟨subd17_3_1143, List.forall_mem_cons.2 ⟨subd17_3_1144, List.forall_mem_cons.2 ⟨subd17_3_1145, List.forall_mem_cons.2 ⟨subd17_3_1146, List.forall_mem_cons.2 ⟨subd17_3_1147, List.forall_mem_cons.2 ⟨subd17_3_1148, List.forall_mem_cons.2 ⟨subd17_3_1149, List.forall_mem_cons.2 ⟨subd17_3_1150, List.forall_mem_cons.2 ⟨subd17_3_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_1152 : subd17_3 [4, 0, -3] = true := by decide +kernel
theorem subd17_3_1153 : subd17_3 [4, 0, -2] = true := by decide +kernel
theorem subd17_3_1154 : subd17_3 [4, 0, -1] = true := by decide +kernel
theorem subd17_3_1155 : subd17_3 [4, 0, 0] = true := by decide +kernel
theorem subd17_3_1156 : subd17_3 [4, 0, 1] = true := by decide +kernel
theorem subd17_3_1157 : subd17_3 [4, 0, 2] = true := by decide +kernel
theorem subd17_3_1158 : subd17_3 [4, 0, 3] = true := by decide +kernel
theorem subd17_3_1159 : subd17_3 [4, 0, 4] = true := by decide +kernel
theorem subd17_3_1160 : subd17_3 [4, 1, -9] = true := by decide +kernel
theorem subd17_3_1161 : subd17_3 [4, 1, -8] = true := by decide +kernel
theorem subd17_3_1162 : subd17_3 [4, 1, -7] = true := by decide +kernel
theorem subd17_3_1163 : subd17_3 [4, 1, -6] = true := by decide +kernel
theorem subd17_3_1164 : subd17_3 [4, 1, -5] = true := by decide +kernel
theorem subd17_3_1165 : subd17_3 [4, 1, -4] = true := by decide +kernel
theorem subd17_3_1166 : subd17_3 [4, 1, -3] = true := by decide +kernel
theorem subd17_3_1167 : subd17_3 [4, 1, -2] = true := by decide +kernel
theorem subd17_3_1168 : subd17_3 [4, 1, -1] = true := by decide +kernel
theorem subd17_3_1169 : subd17_3 [4, 1, 0] = true := by decide +kernel
theorem subd17_3_1170 : subd17_3 [4, 1, 1] = true := by decide +kernel
theorem subd17_3_1171 : subd17_3 [4, 1, 2] = true := by decide +kernel
theorem subd17_3_1172 : subd17_3 [4, 1, 3] = true := by decide +kernel
theorem subd17_3_1173 : subd17_3 [4, 1, 4] = true := by decide +kernel
theorem subd17_3_1174 : subd17_3 [4, 2, -9] = true := by decide +kernel
theorem subd17_3_1175 : subd17_3 [4, 2, -8] = true := by decide +kernel
theorem subd17_3_1176 : subd17_3 [4, 2, -7] = true := by decide +kernel
theorem subd17_3_1177 : subd17_3 [4, 2, -6] = true := by decide +kernel
theorem subd17_3_1178 : subd17_3 [4, 2, -5] = true := by decide +kernel
theorem subd17_3_1179 : subd17_3 [4, 2, -4] = true := by decide +kernel
theorem subd17_3_1180 : subd17_3 [4, 2, -3] = true := by decide +kernel
theorem subd17_3_1181 : subd17_3 [4, 2, -2] = true := by decide +kernel
theorem subd17_3_1182 : subd17_3 [4, 2, -1] = true := by decide +kernel
theorem subd17_3_1183 : subd17_3 [4, 2, 0] = true := by decide +kernel
theorem sbd17_3_36 : ∀ q ∈ blkd17_3_36, subd17_3 q = true := by
  unfold blkd17_3_36
  exact List.forall_mem_cons.2 ⟨subd17_3_1152, List.forall_mem_cons.2 ⟨subd17_3_1153, List.forall_mem_cons.2 ⟨subd17_3_1154, List.forall_mem_cons.2 ⟨subd17_3_1155, List.forall_mem_cons.2 ⟨subd17_3_1156, List.forall_mem_cons.2 ⟨subd17_3_1157, List.forall_mem_cons.2 ⟨subd17_3_1158, List.forall_mem_cons.2 ⟨subd17_3_1159, List.forall_mem_cons.2 ⟨subd17_3_1160, List.forall_mem_cons.2 ⟨subd17_3_1161, List.forall_mem_cons.2 ⟨subd17_3_1162, List.forall_mem_cons.2 ⟨subd17_3_1163, List.forall_mem_cons.2 ⟨subd17_3_1164, List.forall_mem_cons.2 ⟨subd17_3_1165, List.forall_mem_cons.2 ⟨subd17_3_1166, List.forall_mem_cons.2 ⟨subd17_3_1167, List.forall_mem_cons.2 ⟨subd17_3_1168, List.forall_mem_cons.2 ⟨subd17_3_1169, List.forall_mem_cons.2 ⟨subd17_3_1170, List.forall_mem_cons.2 ⟨subd17_3_1171, List.forall_mem_cons.2 ⟨subd17_3_1172, List.forall_mem_cons.2 ⟨subd17_3_1173, List.forall_mem_cons.2 ⟨subd17_3_1174, List.forall_mem_cons.2 ⟨subd17_3_1175, List.forall_mem_cons.2 ⟨subd17_3_1176, List.forall_mem_cons.2 ⟨subd17_3_1177, List.forall_mem_cons.2 ⟨subd17_3_1178, List.forall_mem_cons.2 ⟨subd17_3_1179, List.forall_mem_cons.2 ⟨subd17_3_1180, List.forall_mem_cons.2 ⟨subd17_3_1181, List.forall_mem_cons.2 ⟨subd17_3_1182, List.forall_mem_cons.2 ⟨subd17_3_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_1184 : subd17_3 [4, 2, 1] = true := by decide +kernel
theorem subd17_3_1185 : subd17_3 [4, 2, 2] = true := by decide +kernel
theorem subd17_3_1186 : subd17_3 [4, 2, 3] = true := by decide +kernel
theorem subd17_3_1187 : subd17_3 [4, 2, 4] = true := by decide +kernel
theorem subd17_3_1188 : subd17_3 [4, 3, -8] = true := by decide +kernel
theorem subd17_3_1189 : subd17_3 [4, 3, -7] = true := by decide +kernel
theorem subd17_3_1190 : subd17_3 [4, 3, -6] = true := by decide +kernel
theorem subd17_3_1191 : subd17_3 [4, 3, -5] = true := by decide +kernel
theorem subd17_3_1192 : subd17_3 [4, 3, -4] = true := by decide +kernel
theorem subd17_3_1193 : subd17_3 [4, 3, -3] = true := by decide +kernel
theorem subd17_3_1194 : subd17_3 [4, 3, -2] = true := by decide +kernel
theorem subd17_3_1195 : subd17_3 [4, 3, -1] = true := by decide +kernel
theorem subd17_3_1196 : subd17_3 [4, 3, 0] = true := by decide +kernel
theorem subd17_3_1197 : subd17_3 [4, 3, 1] = true := by decide +kernel
theorem subd17_3_1198 : subd17_3 [4, 3, 2] = true := by decide +kernel
theorem subd17_3_1199 : subd17_3 [4, 3, 3] = true := by decide +kernel
theorem subd17_3_1200 : subd17_3 [4, 3, 4] = true := by decide +kernel
theorem subd17_3_1201 : subd17_3 [4, 4] = true := by decide +kernel
theorem subd17_3_1202 : subd17_3 [4, 5] = true := by decide +kernel
theorem subd17_3_1203 : subd17_3 [4, 6] = true := by decide +kernel
theorem subd17_3_1204 : subd17_3 [5, -4] = true := by decide +kernel
theorem subd17_3_1205 : subd17_3 [5, -3] = true := by decide +kernel
theorem subd17_3_1206 : subd17_3 [5, -2] = true := by decide +kernel
theorem subd17_3_1207 : subd17_3 [5, -1] = true := by decide +kernel
theorem subd17_3_1208 : subd17_3 [5, 0] = true := by decide +kernel
theorem subd17_3_1209 : subd17_3 [5, 1] = true := by decide +kernel
theorem subd17_3_1210 : subd17_3 [5, 2] = true := by decide +kernel
theorem subd17_3_1211 : subd17_3 [5, 3] = true := by decide +kernel
theorem subd17_3_1212 : subd17_3 [5, 4] = true := by decide +kernel
theorem subd17_3_1213 : subd17_3 [5, 5] = true := by decide +kernel
theorem subd17_3_1214 : subd17_3 [6, -2] = true := by decide +kernel
theorem subd17_3_1215 : subd17_3 [6, -1] = true := by decide +kernel
theorem sbd17_3_37 : ∀ q ∈ blkd17_3_37, subd17_3 q = true := by
  unfold blkd17_3_37
  exact List.forall_mem_cons.2 ⟨subd17_3_1184, List.forall_mem_cons.2 ⟨subd17_3_1185, List.forall_mem_cons.2 ⟨subd17_3_1186, List.forall_mem_cons.2 ⟨subd17_3_1187, List.forall_mem_cons.2 ⟨subd17_3_1188, List.forall_mem_cons.2 ⟨subd17_3_1189, List.forall_mem_cons.2 ⟨subd17_3_1190, List.forall_mem_cons.2 ⟨subd17_3_1191, List.forall_mem_cons.2 ⟨subd17_3_1192, List.forall_mem_cons.2 ⟨subd17_3_1193, List.forall_mem_cons.2 ⟨subd17_3_1194, List.forall_mem_cons.2 ⟨subd17_3_1195, List.forall_mem_cons.2 ⟨subd17_3_1196, List.forall_mem_cons.2 ⟨subd17_3_1197, List.forall_mem_cons.2 ⟨subd17_3_1198, List.forall_mem_cons.2 ⟨subd17_3_1199, List.forall_mem_cons.2 ⟨subd17_3_1200, List.forall_mem_cons.2 ⟨subd17_3_1201, List.forall_mem_cons.2 ⟨subd17_3_1202, List.forall_mem_cons.2 ⟨subd17_3_1203, List.forall_mem_cons.2 ⟨subd17_3_1204, List.forall_mem_cons.2 ⟨subd17_3_1205, List.forall_mem_cons.2 ⟨subd17_3_1206, List.forall_mem_cons.2 ⟨subd17_3_1207, List.forall_mem_cons.2 ⟨subd17_3_1208, List.forall_mem_cons.2 ⟨subd17_3_1209, List.forall_mem_cons.2 ⟨subd17_3_1210, List.forall_mem_cons.2 ⟨subd17_3_1211, List.forall_mem_cons.2 ⟨subd17_3_1212, List.forall_mem_cons.2 ⟨subd17_3_1213, List.forall_mem_cons.2 ⟨subd17_3_1214, List.forall_mem_cons.2 ⟨subd17_3_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_1216 : subd17_3 [6, 0] = true := by decide +kernel
theorem subd17_3_1217 : subd17_3 [6, 1] = true := by decide +kernel
theorem subd17_3_1218 : subd17_3 [6, 2] = true := by decide +kernel
theorem subd17_3_1219 : subd17_3 [6, 3] = true := by decide +kernel
theorem subd17_3_1220 : subd17_3 [6, 4] = true := by decide +kernel
theorem sbd17_3_38 : ∀ q ∈ blkd17_3_38, subd17_3 q = true := by
  unfold blkd17_3_38
  exact List.forall_mem_cons.2 ⟨subd17_3_1216, List.forall_mem_cons.2 ⟨subd17_3_1217, List.forall_mem_cons.2 ⟨subd17_3_1218, List.forall_mem_cons.2 ⟨subd17_3_1219, List.forall_mem_cons.2 ⟨subd17_3_1220, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
