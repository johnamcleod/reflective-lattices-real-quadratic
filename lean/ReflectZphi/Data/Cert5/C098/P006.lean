import ReflectZphi.Data.Cert5.C098.Base

namespace ReflectZphi.Data.Cert5.C098
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_832 : sub7 [2, 2, 8] = true := by decide +kernel
theorem sub7_833 : sub7 [2, 3, -6] = true := by decide +kernel
theorem sub7_834 : sub7 [2, 3, -5] = true := by decide +kernel
theorem sub7_835 : sub7 [2, 3, -4] = true := by decide +kernel
theorem sub7_836 : sub7 [2, 3, -3] = true := by decide +kernel
theorem sub7_837 : sub7 [2, 3, -2] = true := by decide +kernel
theorem sub7_838 : sub7 [2, 3, -1] = true := by decide +kernel
theorem sub7_839 : sub7 [2, 3, 0] = true := by decide +kernel
theorem sub7_840 : sub7 [2, 3, 1] = true := by decide +kernel
theorem sub7_841 : sub7 [2, 3, 2] = true := by decide +kernel
theorem sub7_842 : sub7 [2, 3, 3] = true := by decide +kernel
theorem sub7_843 : sub7 [2, 3, 4] = true := by decide +kernel
theorem sub7_844 : sub7 [2, 3, 5] = true := by decide +kernel
theorem sub7_845 : sub7 [2, 3, 6] = true := by decide +kernel
theorem sub7_846 : sub7 [2, 3, 7] = true := by decide +kernel
theorem sub7_847 : sub7 [2, 3, 8] = true := by decide +kernel
theorem sub7_848 : sub7 [2, 4] = true := by decide +kernel
theorem sub7_849 : sub7 [2, 5] = true := by decide +kernel
theorem sub7_850 : sub7 [2, 6] = true := by decide +kernel
theorem sub7_851 : sub7 [3, -7] = true := by decide +kernel
theorem sub7_852 : sub7 [3, -6] = true := by decide +kernel
theorem sub7_853 : sub7 [3, -5] = true := by decide +kernel
theorem sub7_854 : sub7 [3, -4] = true := by decide +kernel
theorem sub7_855 : sub7 [3, -3, -8] = true := by decide +kernel
theorem sub7_856 : sub7 [3, -3, -7] = true := by decide +kernel
theorem sub7_857 : sub7 [3, -3, -6] = true := by decide +kernel
theorem sub7_858 : sub7 [3, -3, -5] = true := by decide +kernel
theorem sub7_859 : sub7 [3, -3, -4] = true := by decide +kernel
theorem sub7_860 : sub7 [3, -3, -3] = true := by decide +kernel
theorem sub7_861 : sub7 [3, -3, -2] = true := by decide +kernel
theorem sub7_862 : sub7 [3, -3, -1] = true := by decide +kernel
theorem sub7_863 : sub7 [3, -3, 0] = true := by decide +kernel
theorem sb7_26 : ∀ q ∈ blk7_26, sub7 q = true := by
  unfold blk7_26
  exact List.forall_mem_cons.2 ⟨sub7_832, List.forall_mem_cons.2 ⟨sub7_833, List.forall_mem_cons.2 ⟨sub7_834, List.forall_mem_cons.2 ⟨sub7_835, List.forall_mem_cons.2 ⟨sub7_836, List.forall_mem_cons.2 ⟨sub7_837, List.forall_mem_cons.2 ⟨sub7_838, List.forall_mem_cons.2 ⟨sub7_839, List.forall_mem_cons.2 ⟨sub7_840, List.forall_mem_cons.2 ⟨sub7_841, List.forall_mem_cons.2 ⟨sub7_842, List.forall_mem_cons.2 ⟨sub7_843, List.forall_mem_cons.2 ⟨sub7_844, List.forall_mem_cons.2 ⟨sub7_845, List.forall_mem_cons.2 ⟨sub7_846, List.forall_mem_cons.2 ⟨sub7_847, List.forall_mem_cons.2 ⟨sub7_848, List.forall_mem_cons.2 ⟨sub7_849, List.forall_mem_cons.2 ⟨sub7_850, List.forall_mem_cons.2 ⟨sub7_851, List.forall_mem_cons.2 ⟨sub7_852, List.forall_mem_cons.2 ⟨sub7_853, List.forall_mem_cons.2 ⟨sub7_854, List.forall_mem_cons.2 ⟨sub7_855, List.forall_mem_cons.2 ⟨sub7_856, List.forall_mem_cons.2 ⟨sub7_857, List.forall_mem_cons.2 ⟨sub7_858, List.forall_mem_cons.2 ⟨sub7_859, List.forall_mem_cons.2 ⟨sub7_860, List.forall_mem_cons.2 ⟨sub7_861, List.forall_mem_cons.2 ⟨sub7_862, List.forall_mem_cons.2 ⟨sub7_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_864 : sub7 [3, -3, 1] = true := by decide +kernel
theorem sub7_865 : sub7 [3, -3, 2] = true := by decide +kernel
theorem sub7_866 : sub7 [3, -3, 3] = true := by decide +kernel
theorem sub7_867 : sub7 [3, -3, 4] = true := by decide +kernel
theorem sub7_868 : sub7 [3, -3, 5] = true := by decide +kernel
theorem sub7_869 : sub7 [3, -3, 6] = true := by decide +kernel
theorem sub7_870 : sub7 [3, -2, -8] = true := by decide +kernel
theorem sub7_871 : sub7 [3, -2, -7] = true := by decide +kernel
theorem sub7_872 : sub7 [3, -2, -6] = true := by decide +kernel
theorem sub7_873 : sub7 [3, -2, -5] = true := by decide +kernel
theorem sub7_874 : sub7 [3, -2, -4] = true := by decide +kernel
theorem sub7_875 : sub7 [3, -2, -3] = true := by decide +kernel
theorem sub7_876 : sub7 [3, -2, -2] = true := by decide +kernel
theorem sub7_877 : sub7 [3, -2, -1] = true := by decide +kernel
theorem sub7_878 : sub7 [3, -2, 0] = true := by decide +kernel
theorem sub7_879 : sub7 [3, -2, 1] = true := by decide +kernel
theorem sub7_880 : sub7 [3, -2, 2] = true := by decide +kernel
theorem sub7_881 : sub7 [3, -2, 3] = true := by decide +kernel
theorem sub7_882 : sub7 [3, -2, 4] = true := by decide +kernel
theorem sub7_883 : sub7 [3, -2, 5] = true := by decide +kernel
theorem sub7_884 : sub7 [3, -2, 6] = true := by decide +kernel
theorem sub7_885 : sub7 [3, -2, 7] = true := by decide +kernel
theorem sub7_886 : sub7 [3, -1, -8] = true := by decide +kernel
theorem sub7_887 : sub7 [3, -1, -7] = true := by decide +kernel
theorem sub7_888 : sub7 [3, -1, -6] = true := by decide +kernel
theorem sub7_889 : sub7 [3, -1, -5] = true := by decide +kernel
theorem sub7_890 : sub7 [3, -1, -4] = true := by decide +kernel
theorem sub7_891 : sub7 [3, -1, -3] = true := by decide +kernel
theorem sub7_892 : sub7 [3, -1, -2] = true := by decide +kernel
theorem sub7_893 : sub7 [3, -1, -1] = true := by decide +kernel
theorem sub7_894 : sub7 [3, -1, 0] = true := by decide +kernel
theorem sub7_895 : sub7 [3, -1, 1] = true := by decide +kernel
theorem sb7_27 : ∀ q ∈ blk7_27, sub7 q = true := by
  unfold blk7_27
  exact List.forall_mem_cons.2 ⟨sub7_864, List.forall_mem_cons.2 ⟨sub7_865, List.forall_mem_cons.2 ⟨sub7_866, List.forall_mem_cons.2 ⟨sub7_867, List.forall_mem_cons.2 ⟨sub7_868, List.forall_mem_cons.2 ⟨sub7_869, List.forall_mem_cons.2 ⟨sub7_870, List.forall_mem_cons.2 ⟨sub7_871, List.forall_mem_cons.2 ⟨sub7_872, List.forall_mem_cons.2 ⟨sub7_873, List.forall_mem_cons.2 ⟨sub7_874, List.forall_mem_cons.2 ⟨sub7_875, List.forall_mem_cons.2 ⟨sub7_876, List.forall_mem_cons.2 ⟨sub7_877, List.forall_mem_cons.2 ⟨sub7_878, List.forall_mem_cons.2 ⟨sub7_879, List.forall_mem_cons.2 ⟨sub7_880, List.forall_mem_cons.2 ⟨sub7_881, List.forall_mem_cons.2 ⟨sub7_882, List.forall_mem_cons.2 ⟨sub7_883, List.forall_mem_cons.2 ⟨sub7_884, List.forall_mem_cons.2 ⟨sub7_885, List.forall_mem_cons.2 ⟨sub7_886, List.forall_mem_cons.2 ⟨sub7_887, List.forall_mem_cons.2 ⟨sub7_888, List.forall_mem_cons.2 ⟨sub7_889, List.forall_mem_cons.2 ⟨sub7_890, List.forall_mem_cons.2 ⟨sub7_891, List.forall_mem_cons.2 ⟨sub7_892, List.forall_mem_cons.2 ⟨sub7_893, List.forall_mem_cons.2 ⟨sub7_894, List.forall_mem_cons.2 ⟨sub7_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_896 : sub7 [3, -1, 2] = true := by decide +kernel
theorem sub7_897 : sub7 [3, -1, 3] = true := by decide +kernel
theorem sub7_898 : sub7 [3, -1, 4] = true := by decide +kernel
theorem sub7_899 : sub7 [3, -1, 5] = true := by decide +kernel
theorem sub7_900 : sub7 [3, -1, 6] = true := by decide +kernel
theorem sub7_901 : sub7 [3, -1, 7] = true := by decide +kernel
theorem sub7_902 : sub7 [3, 0, -7] = true := by decide +kernel
theorem sub7_903 : sub7 [3, 0, -6] = true := by decide +kernel
theorem sub7_904 : sub7 [3, 0, -5] = true := by decide +kernel
theorem sub7_905 : sub7 [3, 0, -4] = true := by decide +kernel
theorem sub7_906 : sub7 [3, 0, -3] = true := by decide +kernel
theorem sub7_907 : sub7 [3, 0, -2] = true := by decide +kernel
theorem sub7_908 : sub7 [3, 0, -1] = true := by decide +kernel
theorem sub7_909 : sub7 [3, 0, 0] = true := by decide +kernel
theorem sub7_910 : sub7 [3, 0, 1] = true := by decide +kernel
theorem sub7_911 : sub7 [3, 0, 2] = true := by decide +kernel
theorem sub7_912 : sub7 [3, 0, 3] = true := by decide +kernel
theorem sub7_913 : sub7 [3, 0, 4] = true := by decide +kernel
theorem sub7_914 : sub7 [3, 0, 5] = true := by decide +kernel
theorem sub7_915 : sub7 [3, 0, 6] = true := by decide +kernel
theorem sub7_916 : sub7 [3, 0, 7] = true := by decide +kernel
theorem sub7_917 : sub7 [3, 0, 8] = true := by decide +kernel
theorem sub7_918 : sub7 [3, 1, -7] = true := by decide +kernel
theorem sub7_919 : sub7 [3, 1, -6] = true := by decide +kernel
theorem sub7_920 : sub7 [3, 1, -5] = true := by decide +kernel
theorem sub7_921 : sub7 [3, 1, -4] = true := by decide +kernel
theorem sub7_922 : sub7 [3, 1, -3] = true := by decide +kernel
theorem sub7_923 : sub7 [3, 1, -2] = true := by decide +kernel
theorem sub7_924 : sub7 [3, 1, -1] = true := by decide +kernel
theorem sub7_925 : sub7 [3, 1, 0] = true := by decide +kernel
theorem sub7_926 : sub7 [3, 1, 1] = true := by decide +kernel
theorem sub7_927 : sub7 [3, 1, 2] = true := by decide +kernel
theorem sb7_28 : ∀ q ∈ blk7_28, sub7 q = true := by
  unfold blk7_28
  exact List.forall_mem_cons.2 ⟨sub7_896, List.forall_mem_cons.2 ⟨sub7_897, List.forall_mem_cons.2 ⟨sub7_898, List.forall_mem_cons.2 ⟨sub7_899, List.forall_mem_cons.2 ⟨sub7_900, List.forall_mem_cons.2 ⟨sub7_901, List.forall_mem_cons.2 ⟨sub7_902, List.forall_mem_cons.2 ⟨sub7_903, List.forall_mem_cons.2 ⟨sub7_904, List.forall_mem_cons.2 ⟨sub7_905, List.forall_mem_cons.2 ⟨sub7_906, List.forall_mem_cons.2 ⟨sub7_907, List.forall_mem_cons.2 ⟨sub7_908, List.forall_mem_cons.2 ⟨sub7_909, List.forall_mem_cons.2 ⟨sub7_910, List.forall_mem_cons.2 ⟨sub7_911, List.forall_mem_cons.2 ⟨sub7_912, List.forall_mem_cons.2 ⟨sub7_913, List.forall_mem_cons.2 ⟨sub7_914, List.forall_mem_cons.2 ⟨sub7_915, List.forall_mem_cons.2 ⟨sub7_916, List.forall_mem_cons.2 ⟨sub7_917, List.forall_mem_cons.2 ⟨sub7_918, List.forall_mem_cons.2 ⟨sub7_919, List.forall_mem_cons.2 ⟨sub7_920, List.forall_mem_cons.2 ⟨sub7_921, List.forall_mem_cons.2 ⟨sub7_922, List.forall_mem_cons.2 ⟨sub7_923, List.forall_mem_cons.2 ⟨sub7_924, List.forall_mem_cons.2 ⟨sub7_925, List.forall_mem_cons.2 ⟨sub7_926, List.forall_mem_cons.2 ⟨sub7_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_928 : sub7 [3, 1, 3] = true := by decide +kernel
theorem sub7_929 : sub7 [3, 1, 4] = true := by decide +kernel
theorem sub7_930 : sub7 [3, 1, 5] = true := by decide +kernel
theorem sub7_931 : sub7 [3, 1, 6] = true := by decide +kernel
theorem sub7_932 : sub7 [3, 1, 7] = true := by decide +kernel
theorem sub7_933 : sub7 [3, 1, 8] = true := by decide +kernel
theorem sub7_934 : sub7 [3, 2, -6] = true := by decide +kernel
theorem sub7_935 : sub7 [3, 2, -5] = true := by decide +kernel
theorem sub7_936 : sub7 [3, 2, -4] = true := by decide +kernel
theorem sub7_937 : sub7 [3, 2, -3] = true := by decide +kernel
theorem sub7_938 : sub7 [3, 2, -2] = true := by decide +kernel
theorem sub7_939 : sub7 [3, 2, -1] = true := by decide +kernel
theorem sub7_940 : sub7 [3, 2, 0] = true := by decide +kernel
theorem sub7_941 : sub7 [3, 2, 1] = true := by decide +kernel
theorem sub7_942 : sub7 [3, 2, 2] = true := by decide +kernel
theorem sub7_943 : sub7 [3, 2, 3] = true := by decide +kernel
theorem sub7_944 : sub7 [3, 2, 4] = true := by decide +kernel
theorem sub7_945 : sub7 [3, 2, 5] = true := by decide +kernel
theorem sub7_946 : sub7 [3, 2, 6] = true := by decide +kernel
theorem sub7_947 : sub7 [3, 2, 7] = true := by decide +kernel
theorem sub7_948 : sub7 [3, 2, 8] = true := by decide +kernel
theorem sub7_949 : sub7 [3, 3] = true := by decide +kernel
theorem sub7_950 : sub7 [3, 4] = true := by decide +kernel
theorem sub7_951 : sub7 [3, 5] = true := by decide +kernel
theorem sub7_952 : sub7 [4, -7] = true := by decide +kernel
theorem sub7_953 : sub7 [4, -6] = true := by decide +kernel
theorem sub7_954 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_955 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_956 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_957 : sub7 [4, -2] = true := by decide +kernel
theorem sub7_958 : sub7 [4, -1, -7] = true := by decide +kernel
theorem sub7_959 : sub7 [4, -1, -6] = true := by decide +kernel
theorem sb7_29 : ∀ q ∈ blk7_29, sub7 q = true := by
  unfold blk7_29
  exact List.forall_mem_cons.2 ⟨sub7_928, List.forall_mem_cons.2 ⟨sub7_929, List.forall_mem_cons.2 ⟨sub7_930, List.forall_mem_cons.2 ⟨sub7_931, List.forall_mem_cons.2 ⟨sub7_932, List.forall_mem_cons.2 ⟨sub7_933, List.forall_mem_cons.2 ⟨sub7_934, List.forall_mem_cons.2 ⟨sub7_935, List.forall_mem_cons.2 ⟨sub7_936, List.forall_mem_cons.2 ⟨sub7_937, List.forall_mem_cons.2 ⟨sub7_938, List.forall_mem_cons.2 ⟨sub7_939, List.forall_mem_cons.2 ⟨sub7_940, List.forall_mem_cons.2 ⟨sub7_941, List.forall_mem_cons.2 ⟨sub7_942, List.forall_mem_cons.2 ⟨sub7_943, List.forall_mem_cons.2 ⟨sub7_944, List.forall_mem_cons.2 ⟨sub7_945, List.forall_mem_cons.2 ⟨sub7_946, List.forall_mem_cons.2 ⟨sub7_947, List.forall_mem_cons.2 ⟨sub7_948, List.forall_mem_cons.2 ⟨sub7_949, List.forall_mem_cons.2 ⟨sub7_950, List.forall_mem_cons.2 ⟨sub7_951, List.forall_mem_cons.2 ⟨sub7_952, List.forall_mem_cons.2 ⟨sub7_953, List.forall_mem_cons.2 ⟨sub7_954, List.forall_mem_cons.2 ⟨sub7_955, List.forall_mem_cons.2 ⟨sub7_956, List.forall_mem_cons.2 ⟨sub7_957, List.forall_mem_cons.2 ⟨sub7_958, List.forall_mem_cons.2 ⟨sub7_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_960 : sub7 [4, -1, -5] = true := by decide +kernel
theorem sub7_961 : sub7 [4, -1, -4] = true := by decide +kernel
theorem sub7_962 : sub7 [4, -1, -3] = true := by decide +kernel
theorem sub7_963 : sub7 [4, -1, -2] = true := by decide +kernel
theorem sub7_964 : sub7 [4, -1, -1] = true := by decide +kernel
theorem sub7_965 : sub7 [4, -1, 0] = true := by decide +kernel
theorem sub7_966 : sub7 [4, -1, 1] = true := by decide +kernel
theorem sub7_967 : sub7 [4, -1, 2] = true := by decide +kernel
theorem sub7_968 : sub7 [4, -1, 3] = true := by decide +kernel
theorem sub7_969 : sub7 [4, -1, 4] = true := by decide +kernel
theorem sub7_970 : sub7 [4, -1, 5] = true := by decide +kernel
theorem sub7_971 : sub7 [4, -1, 6] = true := by decide +kernel
theorem sub7_972 : sub7 [4, -1, 7] = true := by decide +kernel
theorem sub7_973 : sub7 [4, 0] = true := by decide +kernel
theorem sub7_974 : sub7 [4, 1] = true := by decide +kernel
theorem sub7_975 : sub7 [4, 2] = true := by decide +kernel
theorem sub7_976 : sub7 [4, 3] = true := by decide +kernel
theorem sub7_977 : sub7 [4, 4] = true := by decide +kernel
theorem sub7_978 : sub7 [5, -6] = true := by decide +kernel
theorem sub7_979 : sub7 [5, -5] = true := by decide +kernel
theorem sub7_980 : sub7 [5, -4] = true := by decide +kernel
theorem sub7_981 : sub7 [5, -3] = true := by decide +kernel
theorem sub7_982 : sub7 [5, -2] = true := by decide +kernel
theorem sub7_983 : sub7 [5, -1] = true := by decide +kernel
theorem sub7_984 : sub7 [5, 0] = true := by decide +kernel
theorem sub7_985 : sub7 [5, 1] = true := by decide +kernel
theorem sub7_986 : sub7 [5, 2] = true := by decide +kernel
theorem sub7_987 : sub7 [5, 3] = true := by decide +kernel
theorem sub7_988 : sub7 [6, -4] = true := by decide +kernel
theorem sub7_989 : sub7 [6, -3] = true := by decide +kernel
theorem sub7_990 : sub7 [6, -2] = true := by decide +kernel
theorem sub7_991 : sub7 [6, -1] = true := by decide +kernel
theorem sb7_30 : ∀ q ∈ blk7_30, sub7 q = true := by
  unfold blk7_30
  exact List.forall_mem_cons.2 ⟨sub7_960, List.forall_mem_cons.2 ⟨sub7_961, List.forall_mem_cons.2 ⟨sub7_962, List.forall_mem_cons.2 ⟨sub7_963, List.forall_mem_cons.2 ⟨sub7_964, List.forall_mem_cons.2 ⟨sub7_965, List.forall_mem_cons.2 ⟨sub7_966, List.forall_mem_cons.2 ⟨sub7_967, List.forall_mem_cons.2 ⟨sub7_968, List.forall_mem_cons.2 ⟨sub7_969, List.forall_mem_cons.2 ⟨sub7_970, List.forall_mem_cons.2 ⟨sub7_971, List.forall_mem_cons.2 ⟨sub7_972, List.forall_mem_cons.2 ⟨sub7_973, List.forall_mem_cons.2 ⟨sub7_974, List.forall_mem_cons.2 ⟨sub7_975, List.forall_mem_cons.2 ⟨sub7_976, List.forall_mem_cons.2 ⟨sub7_977, List.forall_mem_cons.2 ⟨sub7_978, List.forall_mem_cons.2 ⟨sub7_979, List.forall_mem_cons.2 ⟨sub7_980, List.forall_mem_cons.2 ⟨sub7_981, List.forall_mem_cons.2 ⟨sub7_982, List.forall_mem_cons.2 ⟨sub7_983, List.forall_mem_cons.2 ⟨sub7_984, List.forall_mem_cons.2 ⟨sub7_985, List.forall_mem_cons.2 ⟨sub7_986, List.forall_mem_cons.2 ⟨sub7_987, List.forall_mem_cons.2 ⟨sub7_988, List.forall_mem_cons.2 ⟨sub7_989, List.forall_mem_cons.2 ⟨sub7_990, List.forall_mem_cons.2 ⟨sub7_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_992 : sub7 [6, 0] = true := by decide +kernel
theorem sub7_993 : sub7 [6, 1] = true := by decide +kernel
theorem sub7_994 : sub7 [6, 2] = true := by decide +kernel
theorem sb7_31 : ∀ q ∈ blk7_31, sub7 q = true := by
  unfold blk7_31
  exact List.forall_mem_cons.2 ⟨sub7_992, List.forall_mem_cons.2 ⟨sub7_993, List.forall_mem_cons.2 ⟨sub7_994, List.forall_mem_nil _⟩⟩⟩
theorem sub8_0 : sub8 [-5, -1] = true := by decide +kernel
theorem sub8_1 : sub8 [-5, 0] = true := by decide +kernel
theorem sub8_2 : sub8 [-5, 1] = true := by decide +kernel
theorem sub8_3 : sub8 [-5, 2] = true := by decide +kernel
theorem sub8_4 : sub8 [-5, 3] = true := by decide +kernel
theorem sub8_5 : sub8 [-5, 4] = true := by decide +kernel
theorem sub8_6 : sub8 [-4, -3] = true := by decide +kernel
theorem sub8_7 : sub8 [-4, -2] = true := by decide +kernel
theorem sub8_8 : sub8 [-4, -1] = true := by decide +kernel
theorem sub8_9 : sub8 [-4, 0] = true := by decide +kernel
theorem sub8_10 : sub8 [-4, 1] = true := by decide +kernel
theorem sub8_11 : sub8 [-4, 2] = true := by decide +kernel
theorem sub8_12 : sub8 [-4, 3] = true := by decide +kernel
theorem sub8_13 : sub8 [-4, 4] = true := by decide +kernel
theorem sub8_14 : sub8 [-4, 5] = true := by decide +kernel
theorem sub8_15 : sub8 [-3, -5] = true := by decide +kernel
theorem sub8_16 : sub8 [-3, -4] = true := by decide +kernel
theorem sub8_17 : sub8 [-3, -3] = true := by decide +kernel
theorem sub8_18 : sub8 [-3, -2] = true := by decide +kernel
theorem sub8_19 : sub8 [-3, -1] = true := by decide +kernel
theorem sub8_20 : sub8 [-3, 0] = true := by decide +kernel
theorem sub8_21 : sub8 [-3, 1] = true := by decide +kernel
theorem sub8_22 : sub8 [-3, 2] = true := by decide +kernel
theorem sub8_23 : sub8 [-3, 3] = true := by decide +kernel
theorem sub8_24 : sub8 [-3, 4] = true := by decide +kernel
theorem sub8_25 : sub8 [-3, 5] = true := by decide +kernel
theorem sub8_26 : sub8 [-3, 6] = true := by decide +kernel
theorem sub8_27 : sub8 [-2, -6] = true := by decide +kernel
theorem sub8_28 : sub8 [-2, -5] = true := by decide +kernel
theorem sub8_29 : sub8 [-2, -4] = true := by decide +kernel
theorem sub8_30 : sub8 [-2, -3] = true := by decide +kernel
theorem sub8_31 : sub8 [-2, -2] = true := by decide +kernel
theorem sb8_0 : ∀ q ∈ blk8_0, sub8 q = true := by
  unfold blk8_0
  exact List.forall_mem_cons.2 ⟨sub8_0, List.forall_mem_cons.2 ⟨sub8_1, List.forall_mem_cons.2 ⟨sub8_2, List.forall_mem_cons.2 ⟨sub8_3, List.forall_mem_cons.2 ⟨sub8_4, List.forall_mem_cons.2 ⟨sub8_5, List.forall_mem_cons.2 ⟨sub8_6, List.forall_mem_cons.2 ⟨sub8_7, List.forall_mem_cons.2 ⟨sub8_8, List.forall_mem_cons.2 ⟨sub8_9, List.forall_mem_cons.2 ⟨sub8_10, List.forall_mem_cons.2 ⟨sub8_11, List.forall_mem_cons.2 ⟨sub8_12, List.forall_mem_cons.2 ⟨sub8_13, List.forall_mem_cons.2 ⟨sub8_14, List.forall_mem_cons.2 ⟨sub8_15, List.forall_mem_cons.2 ⟨sub8_16, List.forall_mem_cons.2 ⟨sub8_17, List.forall_mem_cons.2 ⟨sub8_18, List.forall_mem_cons.2 ⟨sub8_19, List.forall_mem_cons.2 ⟨sub8_20, List.forall_mem_cons.2 ⟨sub8_21, List.forall_mem_cons.2 ⟨sub8_22, List.forall_mem_cons.2 ⟨sub8_23, List.forall_mem_cons.2 ⟨sub8_24, List.forall_mem_cons.2 ⟨sub8_25, List.forall_mem_cons.2 ⟨sub8_26, List.forall_mem_cons.2 ⟨sub8_27, List.forall_mem_cons.2 ⟨sub8_28, List.forall_mem_cons.2 ⟨sub8_29, List.forall_mem_cons.2 ⟨sub8_30, List.forall_mem_cons.2 ⟨sub8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_32 : sub8 [-2, -1, -6] = true := by decide +kernel
theorem sub8_33 : sub8 [-2, -1, -5] = true := by decide +kernel
theorem sub8_34 : sub8 [-2, -1, -4] = true := by decide +kernel
theorem sub8_35 : sub8 [-2, -1, -3] = true := by decide +kernel
theorem sub8_36 : sub8 [-2, -1, -2] = true := by decide +kernel
theorem sub8_37 : sub8 [-2, -1, -1] = true := by decide +kernel
theorem sub8_38 : sub8 [-2, -1, 0] = true := by decide +kernel
theorem sub8_39 : sub8 [-2, -1, 1] = true := by decide +kernel
theorem sub8_40 : sub8 [-2, -1, 2] = true := by decide +kernel
theorem sub8_41 : sub8 [-2, -1, 3] = true := by decide +kernel
theorem sub8_42 : sub8 [-2, -1, 4] = true := by decide +kernel
theorem sub8_43 : sub8 [-2, -1, 5] = true := by decide +kernel
theorem sub8_44 : sub8 [-2, -1, 6] = true := by decide +kernel
theorem sub8_45 : sub8 [-2, -1, 7] = true := by decide +kernel
theorem sub8_46 : sub8 [-2, 0, -7] = true := by decide +kernel
theorem sub8_47 : sub8 [-2, 0, -6] = true := by decide +kernel
theorem sub8_48 : sub8 [-2, 0, -5] = true := by decide +kernel
theorem sub8_49 : sub8 [-2, 0, -4] = true := by decide +kernel
theorem sub8_50 : sub8 [-2, 0, -3] = true := by decide +kernel
theorem sub8_51 : sub8 [-2, 0, -2] = true := by decide +kernel
theorem sub8_52 : sub8 [-2, 0, -1] = true := by decide +kernel
theorem sub8_53 : sub8 [-2, 0, 0] = true := by decide +kernel
theorem sub8_54 : sub8 [-2, 0, 1] = true := by decide +kernel
theorem sub8_55 : sub8 [-2, 0, 2] = true := by decide +kernel
theorem sub8_56 : sub8 [-2, 0, 3] = true := by decide +kernel
theorem sub8_57 : sub8 [-2, 0, 4] = true := by decide +kernel
theorem sub8_58 : sub8 [-2, 0, 5] = true := by decide +kernel
theorem sub8_59 : sub8 [-2, 0, 6] = true := by decide +kernel
theorem sub8_60 : sub8 [-2, 0, 7] = true := by decide +kernel
theorem sub8_61 : sub8 [-2, 1, -7] = true := by decide +kernel
theorem sub8_62 : sub8 [-2, 1, -6] = true := by decide +kernel
theorem sub8_63 : sub8 [-2, 1, -5] = true := by decide +kernel
theorem sb8_1 : ∀ q ∈ blk8_1, sub8 q = true := by
  unfold blk8_1
  exact List.forall_mem_cons.2 ⟨sub8_32, List.forall_mem_cons.2 ⟨sub8_33, List.forall_mem_cons.2 ⟨sub8_34, List.forall_mem_cons.2 ⟨sub8_35, List.forall_mem_cons.2 ⟨sub8_36, List.forall_mem_cons.2 ⟨sub8_37, List.forall_mem_cons.2 ⟨sub8_38, List.forall_mem_cons.2 ⟨sub8_39, List.forall_mem_cons.2 ⟨sub8_40, List.forall_mem_cons.2 ⟨sub8_41, List.forall_mem_cons.2 ⟨sub8_42, List.forall_mem_cons.2 ⟨sub8_43, List.forall_mem_cons.2 ⟨sub8_44, List.forall_mem_cons.2 ⟨sub8_45, List.forall_mem_cons.2 ⟨sub8_46, List.forall_mem_cons.2 ⟨sub8_47, List.forall_mem_cons.2 ⟨sub8_48, List.forall_mem_cons.2 ⟨sub8_49, List.forall_mem_cons.2 ⟨sub8_50, List.forall_mem_cons.2 ⟨sub8_51, List.forall_mem_cons.2 ⟨sub8_52, List.forall_mem_cons.2 ⟨sub8_53, List.forall_mem_cons.2 ⟨sub8_54, List.forall_mem_cons.2 ⟨sub8_55, List.forall_mem_cons.2 ⟨sub8_56, List.forall_mem_cons.2 ⟨sub8_57, List.forall_mem_cons.2 ⟨sub8_58, List.forall_mem_cons.2 ⟨sub8_59, List.forall_mem_cons.2 ⟨sub8_60, List.forall_mem_cons.2 ⟨sub8_61, List.forall_mem_cons.2 ⟨sub8_62, List.forall_mem_cons.2 ⟨sub8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_64 : sub8 [-2, 1, -4] = true := by decide +kernel
theorem sub8_65 : sub8 [-2, 1, -3] = true := by decide +kernel
theorem sub8_66 : sub8 [-2, 1, -2] = true := by decide +kernel
theorem sub8_67 : sub8 [-2, 1, -1] = true := by decide +kernel
theorem sub8_68 : sub8 [-2, 1, 0] = true := by decide +kernel
theorem sub8_69 : sub8 [-2, 1, 1] = true := by decide +kernel
theorem sub8_70 : sub8 [-2, 1, 2] = true := by decide +kernel
theorem sub8_71 : sub8 [-2, 1, 3] = true := by decide +kernel
theorem sub8_72 : sub8 [-2, 1, 4] = true := by decide +kernel
theorem sub8_73 : sub8 [-2, 1, 5] = true := by decide +kernel
theorem sub8_74 : sub8 [-2, 1, 6] = true := by decide +kernel
theorem sub8_75 : sub8 [-2, 1, 7] = true := by decide +kernel
theorem sub8_76 : sub8 [-2, 2, -7] = true := by decide +kernel
theorem sub8_77 : sub8 [-2, 2, -6] = true := by decide +kernel
theorem sub8_78 : sub8 [-2, 2, -5] = true := by decide +kernel
theorem sub8_79 : sub8 [-2, 2, -4] = true := by decide +kernel
theorem sub8_80 : sub8 [-2, 2, -3] = true := by decide +kernel
theorem sub8_81 : sub8 [-2, 2, -2] = true := by decide +kernel
theorem sub8_82 : sub8 [-2, 2, -1] = true := by decide +kernel
theorem sub8_83 : sub8 [-2, 2, 0] = true := by decide +kernel
theorem sub8_84 : sub8 [-2, 2, 1] = true := by decide +kernel
theorem sub8_85 : sub8 [-2, 2, 2] = true := by decide +kernel
theorem sub8_86 : sub8 [-2, 2, 3] = true := by decide +kernel
theorem sub8_87 : sub8 [-2, 2, 4] = true := by decide +kernel
theorem sub8_88 : sub8 [-2, 2, 5] = true := by decide +kernel
theorem sub8_89 : sub8 [-2, 2, 6] = true := by decide +kernel
theorem sub8_90 : sub8 [-2, 3] = true := by decide +kernel
theorem sub8_91 : sub8 [-2, 4] = true := by decide +kernel
theorem sub8_92 : sub8 [-2, 5] = true := by decide +kernel
theorem sub8_93 : sub8 [-2, 6] = true := by decide +kernel
theorem sub8_94 : sub8 [-1, -6] = true := by decide +kernel
theorem sub8_95 : sub8 [-1, -5] = true := by decide +kernel
theorem sb8_2 : ∀ q ∈ blk8_2, sub8 q = true := by
  unfold blk8_2
  exact List.forall_mem_cons.2 ⟨sub8_64, List.forall_mem_cons.2 ⟨sub8_65, List.forall_mem_cons.2 ⟨sub8_66, List.forall_mem_cons.2 ⟨sub8_67, List.forall_mem_cons.2 ⟨sub8_68, List.forall_mem_cons.2 ⟨sub8_69, List.forall_mem_cons.2 ⟨sub8_70, List.forall_mem_cons.2 ⟨sub8_71, List.forall_mem_cons.2 ⟨sub8_72, List.forall_mem_cons.2 ⟨sub8_73, List.forall_mem_cons.2 ⟨sub8_74, List.forall_mem_cons.2 ⟨sub8_75, List.forall_mem_cons.2 ⟨sub8_76, List.forall_mem_cons.2 ⟨sub8_77, List.forall_mem_cons.2 ⟨sub8_78, List.forall_mem_cons.2 ⟨sub8_79, List.forall_mem_cons.2 ⟨sub8_80, List.forall_mem_cons.2 ⟨sub8_81, List.forall_mem_cons.2 ⟨sub8_82, List.forall_mem_cons.2 ⟨sub8_83, List.forall_mem_cons.2 ⟨sub8_84, List.forall_mem_cons.2 ⟨sub8_85, List.forall_mem_cons.2 ⟨sub8_86, List.forall_mem_cons.2 ⟨sub8_87, List.forall_mem_cons.2 ⟨sub8_88, List.forall_mem_cons.2 ⟨sub8_89, List.forall_mem_cons.2 ⟨sub8_90, List.forall_mem_cons.2 ⟨sub8_91, List.forall_mem_cons.2 ⟨sub8_92, List.forall_mem_cons.2 ⟨sub8_93, List.forall_mem_cons.2 ⟨sub8_94, List.forall_mem_cons.2 ⟨sub8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C098
