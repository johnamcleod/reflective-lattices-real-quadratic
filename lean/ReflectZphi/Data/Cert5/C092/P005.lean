import ReflectZphi.Data.Cert5.C092.Base

namespace ReflectZphi.Data.Cert5.C092
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_832 : sub6 [2, 0, 9] = true := by decide +kernel
theorem sub6_833 : sub6 [2, 1, -8] = true := by decide +kernel
theorem sub6_834 : sub6 [2, 1, -7] = true := by decide +kernel
theorem sub6_835 : sub6 [2, 1, -6] = true := by decide +kernel
theorem sub6_836 : sub6 [2, 1, -5] = true := by decide +kernel
theorem sub6_837 : sub6 [2, 1, -4] = true := by decide +kernel
theorem sub6_838 : sub6 [2, 1, -3] = true := by decide +kernel
theorem sub6_839 : sub6 [2, 1, -2] = true := by decide +kernel
theorem sub6_840 : sub6 [2, 1, -1] = true := by decide +kernel
theorem sub6_841 : sub6 [2, 1, 0] = true := by decide +kernel
theorem sub6_842 : sub6 [2, 1, 1] = true := by decide +kernel
theorem sub6_843 : sub6 [2, 1, 2] = true := by decide +kernel
theorem sub6_844 : sub6 [2, 1, 3] = true := by decide +kernel
theorem sub6_845 : sub6 [2, 1, 4] = true := by decide +kernel
theorem sub6_846 : sub6 [2, 1, 5] = true := by decide +kernel
theorem sub6_847 : sub6 [2, 1, 6] = true := by decide +kernel
theorem sub6_848 : sub6 [2, 1, 7] = true := by decide +kernel
theorem sub6_849 : sub6 [2, 1, 8] = true := by decide +kernel
theorem sub6_850 : sub6 [2, 1, 9] = true := by decide +kernel
theorem sub6_851 : sub6 [2, 2, -8] = true := by decide +kernel
theorem sub6_852 : sub6 [2, 2, -7] = true := by decide +kernel
theorem sub6_853 : sub6 [2, 2, -6] = true := by decide +kernel
theorem sub6_854 : sub6 [2, 2, -5] = true := by decide +kernel
theorem sub6_855 : sub6 [2, 2, -4] = true := by decide +kernel
theorem sub6_856 : sub6 [2, 2, -3] = true := by decide +kernel
theorem sub6_857 : sub6 [2, 2, -2] = true := by decide +kernel
theorem sub6_858 : sub6 [2, 2, -1] = true := by decide +kernel
theorem sub6_859 : sub6 [2, 2, 0] = true := by decide +kernel
theorem sub6_860 : sub6 [2, 2, 1] = true := by decide +kernel
theorem sub6_861 : sub6 [2, 2, 2] = true := by decide +kernel
theorem sub6_862 : sub6 [2, 2, 3] = true := by decide +kernel
theorem sub6_863 : sub6 [2, 2, 4] = true := by decide +kernel
theorem sb6_26 : ∀ q ∈ blk6_26, sub6 q = true := by
  unfold blk6_26
  exact List.forall_mem_cons.2 ⟨sub6_832, List.forall_mem_cons.2 ⟨sub6_833, List.forall_mem_cons.2 ⟨sub6_834, List.forall_mem_cons.2 ⟨sub6_835, List.forall_mem_cons.2 ⟨sub6_836, List.forall_mem_cons.2 ⟨sub6_837, List.forall_mem_cons.2 ⟨sub6_838, List.forall_mem_cons.2 ⟨sub6_839, List.forall_mem_cons.2 ⟨sub6_840, List.forall_mem_cons.2 ⟨sub6_841, List.forall_mem_cons.2 ⟨sub6_842, List.forall_mem_cons.2 ⟨sub6_843, List.forall_mem_cons.2 ⟨sub6_844, List.forall_mem_cons.2 ⟨sub6_845, List.forall_mem_cons.2 ⟨sub6_846, List.forall_mem_cons.2 ⟨sub6_847, List.forall_mem_cons.2 ⟨sub6_848, List.forall_mem_cons.2 ⟨sub6_849, List.forall_mem_cons.2 ⟨sub6_850, List.forall_mem_cons.2 ⟨sub6_851, List.forall_mem_cons.2 ⟨sub6_852, List.forall_mem_cons.2 ⟨sub6_853, List.forall_mem_cons.2 ⟨sub6_854, List.forall_mem_cons.2 ⟨sub6_855, List.forall_mem_cons.2 ⟨sub6_856, List.forall_mem_cons.2 ⟨sub6_857, List.forall_mem_cons.2 ⟨sub6_858, List.forall_mem_cons.2 ⟨sub6_859, List.forall_mem_cons.2 ⟨sub6_860, List.forall_mem_cons.2 ⟨sub6_861, List.forall_mem_cons.2 ⟨sub6_862, List.forall_mem_cons.2 ⟨sub6_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_864 : sub6 [2, 2, 5] = true := by decide +kernel
theorem sub6_865 : sub6 [2, 2, 6] = true := by decide +kernel
theorem sub6_866 : sub6 [2, 2, 7] = true := by decide +kernel
theorem sub6_867 : sub6 [2, 2, 8] = true := by decide +kernel
theorem sub6_868 : sub6 [2, 2, 9] = true := by decide +kernel
theorem sub6_869 : sub6 [2, 3, -7] = true := by decide +kernel
theorem sub6_870 : sub6 [2, 3, -6] = true := by decide +kernel
theorem sub6_871 : sub6 [2, 3, -5] = true := by decide +kernel
theorem sub6_872 : sub6 [2, 3, -4] = true := by decide +kernel
theorem sub6_873 : sub6 [2, 3, -3] = true := by decide +kernel
theorem sub6_874 : sub6 [2, 3, -2] = true := by decide +kernel
theorem sub6_875 : sub6 [2, 3, -1] = true := by decide +kernel
theorem sub6_876 : sub6 [2, 3, 0] = true := by decide +kernel
theorem sub6_877 : sub6 [2, 3, 1] = true := by decide +kernel
theorem sub6_878 : sub6 [2, 3, 2] = true := by decide +kernel
theorem sub6_879 : sub6 [2, 3, 3] = true := by decide +kernel
theorem sub6_880 : sub6 [2, 3, 4] = true := by decide +kernel
theorem sub6_881 : sub6 [2, 3, 5] = true := by decide +kernel
theorem sub6_882 : sub6 [2, 3, 6] = true := by decide +kernel
theorem sub6_883 : sub6 [2, 3, 7] = true := by decide +kernel
theorem sub6_884 : sub6 [2, 3, 8] = true := by decide +kernel
theorem sub6_885 : sub6 [2, 4] = true := by decide +kernel
theorem sub6_886 : sub6 [2, 5] = true := by decide +kernel
theorem sub6_887 : sub6 [3, -5] = true := by decide +kernel
theorem sub6_888 : sub6 [3, -4] = true := by decide +kernel
theorem sub6_889 : sub6 [3, -3] = true := by decide +kernel
theorem sub6_890 : sub6 [3, -2, -7] = true := by decide +kernel
theorem sub6_891 : sub6 [3, -2, -6] = true := by decide +kernel
theorem sub6_892 : sub6 [3, -2, -5] = true := by decide +kernel
theorem sub6_893 : sub6 [3, -2, -4] = true := by decide +kernel
theorem sub6_894 : sub6 [3, -2, -3] = true := by decide +kernel
theorem sub6_895 : sub6 [3, -2, -2] = true := by decide +kernel
theorem sb6_27 : ∀ q ∈ blk6_27, sub6 q = true := by
  unfold blk6_27
  exact List.forall_mem_cons.2 ⟨sub6_864, List.forall_mem_cons.2 ⟨sub6_865, List.forall_mem_cons.2 ⟨sub6_866, List.forall_mem_cons.2 ⟨sub6_867, List.forall_mem_cons.2 ⟨sub6_868, List.forall_mem_cons.2 ⟨sub6_869, List.forall_mem_cons.2 ⟨sub6_870, List.forall_mem_cons.2 ⟨sub6_871, List.forall_mem_cons.2 ⟨sub6_872, List.forall_mem_cons.2 ⟨sub6_873, List.forall_mem_cons.2 ⟨sub6_874, List.forall_mem_cons.2 ⟨sub6_875, List.forall_mem_cons.2 ⟨sub6_876, List.forall_mem_cons.2 ⟨sub6_877, List.forall_mem_cons.2 ⟨sub6_878, List.forall_mem_cons.2 ⟨sub6_879, List.forall_mem_cons.2 ⟨sub6_880, List.forall_mem_cons.2 ⟨sub6_881, List.forall_mem_cons.2 ⟨sub6_882, List.forall_mem_cons.2 ⟨sub6_883, List.forall_mem_cons.2 ⟨sub6_884, List.forall_mem_cons.2 ⟨sub6_885, List.forall_mem_cons.2 ⟨sub6_886, List.forall_mem_cons.2 ⟨sub6_887, List.forall_mem_cons.2 ⟨sub6_888, List.forall_mem_cons.2 ⟨sub6_889, List.forall_mem_cons.2 ⟨sub6_890, List.forall_mem_cons.2 ⟨sub6_891, List.forall_mem_cons.2 ⟨sub6_892, List.forall_mem_cons.2 ⟨sub6_893, List.forall_mem_cons.2 ⟨sub6_894, List.forall_mem_cons.2 ⟨sub6_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_896 : sub6 [3, -2, -1] = true := by decide +kernel
theorem sub6_897 : sub6 [3, -2, 0] = true := by decide +kernel
theorem sub6_898 : sub6 [3, -2, 1] = true := by decide +kernel
theorem sub6_899 : sub6 [3, -2, 2] = true := by decide +kernel
theorem sub6_900 : sub6 [3, -2, 3] = true := by decide +kernel
theorem sub6_901 : sub6 [3, -2, 4] = true := by decide +kernel
theorem sub6_902 : sub6 [3, -2, 5] = true := by decide +kernel
theorem sub6_903 : sub6 [3, -2, 6] = true := by decide +kernel
theorem sub6_904 : sub6 [3, -2, 7] = true := by decide +kernel
theorem sub6_905 : sub6 [3, -1, -7] = true := by decide +kernel
theorem sub6_906 : sub6 [3, -1, -6] = true := by decide +kernel
theorem sub6_907 : sub6 [3, -1, -5] = true := by decide +kernel
theorem sub6_908 : sub6 [3, -1, -4] = true := by decide +kernel
theorem sub6_909 : sub6 [3, -1, -3] = true := by decide +kernel
theorem sub6_910 : sub6 [3, -1, -2] = true := by decide +kernel
theorem sub6_911 : sub6 [3, -1, -1] = true := by decide +kernel
theorem sub6_912 : sub6 [3, -1, 0] = true := by decide +kernel
theorem sub6_913 : sub6 [3, -1, 1] = true := by decide +kernel
theorem sub6_914 : sub6 [3, -1, 2] = true := by decide +kernel
theorem sub6_915 : sub6 [3, -1, 3] = true := by decide +kernel
theorem sub6_916 : sub6 [3, -1, 4] = true := by decide +kernel
theorem sub6_917 : sub6 [3, -1, 5] = true := by decide +kernel
theorem sub6_918 : sub6 [3, -1, 6] = true := by decide +kernel
theorem sub6_919 : sub6 [3, -1, 7] = true := by decide +kernel
theorem sub6_920 : sub6 [3, -1, 8] = true := by decide +kernel
theorem sub6_921 : sub6 [3, 0, -7] = true := by decide +kernel
theorem sub6_922 : sub6 [3, 0, -6] = true := by decide +kernel
theorem sub6_923 : sub6 [3, 0, -5] = true := by decide +kernel
theorem sub6_924 : sub6 [3, 0, -4] = true := by decide +kernel
theorem sub6_925 : sub6 [3, 0, -3] = true := by decide +kernel
theorem sub6_926 : sub6 [3, 0, -2] = true := by decide +kernel
theorem sub6_927 : sub6 [3, 0, -1] = true := by decide +kernel
theorem sb6_28 : ∀ q ∈ blk6_28, sub6 q = true := by
  unfold blk6_28
  exact List.forall_mem_cons.2 ⟨sub6_896, List.forall_mem_cons.2 ⟨sub6_897, List.forall_mem_cons.2 ⟨sub6_898, List.forall_mem_cons.2 ⟨sub6_899, List.forall_mem_cons.2 ⟨sub6_900, List.forall_mem_cons.2 ⟨sub6_901, List.forall_mem_cons.2 ⟨sub6_902, List.forall_mem_cons.2 ⟨sub6_903, List.forall_mem_cons.2 ⟨sub6_904, List.forall_mem_cons.2 ⟨sub6_905, List.forall_mem_cons.2 ⟨sub6_906, List.forall_mem_cons.2 ⟨sub6_907, List.forall_mem_cons.2 ⟨sub6_908, List.forall_mem_cons.2 ⟨sub6_909, List.forall_mem_cons.2 ⟨sub6_910, List.forall_mem_cons.2 ⟨sub6_911, List.forall_mem_cons.2 ⟨sub6_912, List.forall_mem_cons.2 ⟨sub6_913, List.forall_mem_cons.2 ⟨sub6_914, List.forall_mem_cons.2 ⟨sub6_915, List.forall_mem_cons.2 ⟨sub6_916, List.forall_mem_cons.2 ⟨sub6_917, List.forall_mem_cons.2 ⟨sub6_918, List.forall_mem_cons.2 ⟨sub6_919, List.forall_mem_cons.2 ⟨sub6_920, List.forall_mem_cons.2 ⟨sub6_921, List.forall_mem_cons.2 ⟨sub6_922, List.forall_mem_cons.2 ⟨sub6_923, List.forall_mem_cons.2 ⟨sub6_924, List.forall_mem_cons.2 ⟨sub6_925, List.forall_mem_cons.2 ⟨sub6_926, List.forall_mem_cons.2 ⟨sub6_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_928 : sub6 [3, 0, 0] = true := by decide +kernel
theorem sub6_929 : sub6 [3, 0, 1] = true := by decide +kernel
theorem sub6_930 : sub6 [3, 0, 2] = true := by decide +kernel
theorem sub6_931 : sub6 [3, 0, 3] = true := by decide +kernel
theorem sub6_932 : sub6 [3, 0, 4] = true := by decide +kernel
theorem sub6_933 : sub6 [3, 0, 5] = true := by decide +kernel
theorem sub6_934 : sub6 [3, 0, 6] = true := by decide +kernel
theorem sub6_935 : sub6 [3, 0, 7] = true := by decide +kernel
theorem sub6_936 : sub6 [3, 0, 8] = true := by decide +kernel
theorem sub6_937 : sub6 [3, 1, -7] = true := by decide +kernel
theorem sub6_938 : sub6 [3, 1, -6] = true := by decide +kernel
theorem sub6_939 : sub6 [3, 1, -5] = true := by decide +kernel
theorem sub6_940 : sub6 [3, 1, -4] = true := by decide +kernel
theorem sub6_941 : sub6 [3, 1, -3] = true := by decide +kernel
theorem sub6_942 : sub6 [3, 1, -2] = true := by decide +kernel
theorem sub6_943 : sub6 [3, 1, -1] = true := by decide +kernel
theorem sub6_944 : sub6 [3, 1, 0] = true := by decide +kernel
theorem sub6_945 : sub6 [3, 1, 1] = true := by decide +kernel
theorem sub6_946 : sub6 [3, 1, 2] = true := by decide +kernel
theorem sub6_947 : sub6 [3, 1, 3] = true := by decide +kernel
theorem sub6_948 : sub6 [3, 1, 4] = true := by decide +kernel
theorem sub6_949 : sub6 [3, 1, 5] = true := by decide +kernel
theorem sub6_950 : sub6 [3, 1, 6] = true := by decide +kernel
theorem sub6_951 : sub6 [3, 1, 7] = true := by decide +kernel
theorem sub6_952 : sub6 [3, 1, 8] = true := by decide +kernel
theorem sub6_953 : sub6 [3, 2, -7] = true := by decide +kernel
theorem sub6_954 : sub6 [3, 2, -6] = true := by decide +kernel
theorem sub6_955 : sub6 [3, 2, -5] = true := by decide +kernel
theorem sub6_956 : sub6 [3, 2, -4] = true := by decide +kernel
theorem sub6_957 : sub6 [3, 2, -3] = true := by decide +kernel
theorem sub6_958 : sub6 [3, 2, -2] = true := by decide +kernel
theorem sub6_959 : sub6 [3, 2, -1] = true := by decide +kernel
theorem sb6_29 : ∀ q ∈ blk6_29, sub6 q = true := by
  unfold blk6_29
  exact List.forall_mem_cons.2 ⟨sub6_928, List.forall_mem_cons.2 ⟨sub6_929, List.forall_mem_cons.2 ⟨sub6_930, List.forall_mem_cons.2 ⟨sub6_931, List.forall_mem_cons.2 ⟨sub6_932, List.forall_mem_cons.2 ⟨sub6_933, List.forall_mem_cons.2 ⟨sub6_934, List.forall_mem_cons.2 ⟨sub6_935, List.forall_mem_cons.2 ⟨sub6_936, List.forall_mem_cons.2 ⟨sub6_937, List.forall_mem_cons.2 ⟨sub6_938, List.forall_mem_cons.2 ⟨sub6_939, List.forall_mem_cons.2 ⟨sub6_940, List.forall_mem_cons.2 ⟨sub6_941, List.forall_mem_cons.2 ⟨sub6_942, List.forall_mem_cons.2 ⟨sub6_943, List.forall_mem_cons.2 ⟨sub6_944, List.forall_mem_cons.2 ⟨sub6_945, List.forall_mem_cons.2 ⟨sub6_946, List.forall_mem_cons.2 ⟨sub6_947, List.forall_mem_cons.2 ⟨sub6_948, List.forall_mem_cons.2 ⟨sub6_949, List.forall_mem_cons.2 ⟨sub6_950, List.forall_mem_cons.2 ⟨sub6_951, List.forall_mem_cons.2 ⟨sub6_952, List.forall_mem_cons.2 ⟨sub6_953, List.forall_mem_cons.2 ⟨sub6_954, List.forall_mem_cons.2 ⟨sub6_955, List.forall_mem_cons.2 ⟨sub6_956, List.forall_mem_cons.2 ⟨sub6_957, List.forall_mem_cons.2 ⟨sub6_958, List.forall_mem_cons.2 ⟨sub6_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_960 : sub6 [3, 2, 0] = true := by decide +kernel
theorem sub6_961 : sub6 [3, 2, 1] = true := by decide +kernel
theorem sub6_962 : sub6 [3, 2, 2] = true := by decide +kernel
theorem sub6_963 : sub6 [3, 2, 3] = true := by decide +kernel
theorem sub6_964 : sub6 [3, 2, 4] = true := by decide +kernel
theorem sub6_965 : sub6 [3, 2, 5] = true := by decide +kernel
theorem sub6_966 : sub6 [3, 2, 6] = true := by decide +kernel
theorem sub6_967 : sub6 [3, 2, 7] = true := by decide +kernel
theorem sub6_968 : sub6 [3, 2, 8] = true := by decide +kernel
theorem sub6_969 : sub6 [3, 3, -6] = true := by decide +kernel
theorem sub6_970 : sub6 [3, 3, -5] = true := by decide +kernel
theorem sub6_971 : sub6 [3, 3, -4] = true := by decide +kernel
theorem sub6_972 : sub6 [3, 3, -3] = true := by decide +kernel
theorem sub6_973 : sub6 [3, 3, -2] = true := by decide +kernel
theorem sub6_974 : sub6 [3, 3, -1] = true := by decide +kernel
theorem sub6_975 : sub6 [3, 3, 0] = true := by decide +kernel
theorem sub6_976 : sub6 [3, 3, 1] = true := by decide +kernel
theorem sub6_977 : sub6 [3, 3, 2] = true := by decide +kernel
theorem sub6_978 : sub6 [3, 3, 3] = true := by decide +kernel
theorem sub6_979 : sub6 [3, 3, 4] = true := by decide +kernel
theorem sub6_980 : sub6 [3, 3, 5] = true := by decide +kernel
theorem sub6_981 : sub6 [3, 3, 6] = true := by decide +kernel
theorem sub6_982 : sub6 [3, 3, 7] = true := by decide +kernel
theorem sub6_983 : sub6 [3, 4] = true := by decide +kernel
theorem sub6_984 : sub6 [3, 5] = true := by decide +kernel
theorem sub6_985 : sub6 [4, -4] = true := by decide +kernel
theorem sub6_986 : sub6 [4, -3] = true := by decide +kernel
theorem sub6_987 : sub6 [4, -2] = true := by decide +kernel
theorem sub6_988 : sub6 [4, -1, -6] = true := by decide +kernel
theorem sub6_989 : sub6 [4, -1, -5] = true := by decide +kernel
theorem sub6_990 : sub6 [4, -1, -4] = true := by decide +kernel
theorem sub6_991 : sub6 [4, -1, -3] = true := by decide +kernel
theorem sb6_30 : ∀ q ∈ blk6_30, sub6 q = true := by
  unfold blk6_30
  exact List.forall_mem_cons.2 ⟨sub6_960, List.forall_mem_cons.2 ⟨sub6_961, List.forall_mem_cons.2 ⟨sub6_962, List.forall_mem_cons.2 ⟨sub6_963, List.forall_mem_cons.2 ⟨sub6_964, List.forall_mem_cons.2 ⟨sub6_965, List.forall_mem_cons.2 ⟨sub6_966, List.forall_mem_cons.2 ⟨sub6_967, List.forall_mem_cons.2 ⟨sub6_968, List.forall_mem_cons.2 ⟨sub6_969, List.forall_mem_cons.2 ⟨sub6_970, List.forall_mem_cons.2 ⟨sub6_971, List.forall_mem_cons.2 ⟨sub6_972, List.forall_mem_cons.2 ⟨sub6_973, List.forall_mem_cons.2 ⟨sub6_974, List.forall_mem_cons.2 ⟨sub6_975, List.forall_mem_cons.2 ⟨sub6_976, List.forall_mem_cons.2 ⟨sub6_977, List.forall_mem_cons.2 ⟨sub6_978, List.forall_mem_cons.2 ⟨sub6_979, List.forall_mem_cons.2 ⟨sub6_980, List.forall_mem_cons.2 ⟨sub6_981, List.forall_mem_cons.2 ⟨sub6_982, List.forall_mem_cons.2 ⟨sub6_983, List.forall_mem_cons.2 ⟨sub6_984, List.forall_mem_cons.2 ⟨sub6_985, List.forall_mem_cons.2 ⟨sub6_986, List.forall_mem_cons.2 ⟨sub6_987, List.forall_mem_cons.2 ⟨sub6_988, List.forall_mem_cons.2 ⟨sub6_989, List.forall_mem_cons.2 ⟨sub6_990, List.forall_mem_cons.2 ⟨sub6_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_992 : sub6 [4, -1, -2] = true := by decide +kernel
theorem sub6_993 : sub6 [4, -1, -1] = true := by decide +kernel
theorem sub6_994 : sub6 [4, -1, 0] = true := by decide +kernel
theorem sub6_995 : sub6 [4, -1, 1] = true := by decide +kernel
theorem sub6_996 : sub6 [4, -1, 2] = true := by decide +kernel
theorem sub6_997 : sub6 [4, -1, 3] = true := by decide +kernel
theorem sub6_998 : sub6 [4, -1, 4] = true := by decide +kernel
theorem sub6_999 : sub6 [4, -1, 5] = true := by decide +kernel
theorem sub6_1000 : sub6 [4, -1, 6] = true := by decide +kernel
theorem sub6_1001 : sub6 [4, -1, 7] = true := by decide +kernel
theorem sub6_1002 : sub6 [4, 0, -6] = true := by decide +kernel
theorem sub6_1003 : sub6 [4, 0, -5] = true := by decide +kernel
theorem sub6_1004 : sub6 [4, 0, -4] = true := by decide +kernel
theorem sub6_1005 : sub6 [4, 0, -3] = true := by decide +kernel
theorem sub6_1006 : sub6 [4, 0, -2] = true := by decide +kernel
theorem sub6_1007 : sub6 [4, 0, -1] = true := by decide +kernel
theorem sub6_1008 : sub6 [4, 0, 0] = true := by decide +kernel
theorem sub6_1009 : sub6 [4, 0, 1] = true := by decide +kernel
theorem sub6_1010 : sub6 [4, 0, 2] = true := by decide +kernel
theorem sub6_1011 : sub6 [4, 0, 3] = true := by decide +kernel
theorem sub6_1012 : sub6 [4, 0, 4] = true := by decide +kernel
theorem sub6_1013 : sub6 [4, 0, 5] = true := by decide +kernel
theorem sub6_1014 : sub6 [4, 0, 6] = true := by decide +kernel
theorem sub6_1015 : sub6 [4, 0, 7] = true := by decide +kernel
theorem sub6_1016 : sub6 [4, 1, -6] = true := by decide +kernel
theorem sub6_1017 : sub6 [4, 1, -5] = true := by decide +kernel
theorem sub6_1018 : sub6 [4, 1, -4] = true := by decide +kernel
theorem sub6_1019 : sub6 [4, 1, -3] = true := by decide +kernel
theorem sub6_1020 : sub6 [4, 1, -2] = true := by decide +kernel
theorem sub6_1021 : sub6 [4, 1, -1] = true := by decide +kernel
theorem sub6_1022 : sub6 [4, 1, 0] = true := by decide +kernel
theorem sub6_1023 : sub6 [4, 1, 1] = true := by decide +kernel
theorem sb6_31 : ∀ q ∈ blk6_31, sub6 q = true := by
  unfold blk6_31
  exact List.forall_mem_cons.2 ⟨sub6_992, List.forall_mem_cons.2 ⟨sub6_993, List.forall_mem_cons.2 ⟨sub6_994, List.forall_mem_cons.2 ⟨sub6_995, List.forall_mem_cons.2 ⟨sub6_996, List.forall_mem_cons.2 ⟨sub6_997, List.forall_mem_cons.2 ⟨sub6_998, List.forall_mem_cons.2 ⟨sub6_999, List.forall_mem_cons.2 ⟨sub6_1000, List.forall_mem_cons.2 ⟨sub6_1001, List.forall_mem_cons.2 ⟨sub6_1002, List.forall_mem_cons.2 ⟨sub6_1003, List.forall_mem_cons.2 ⟨sub6_1004, List.forall_mem_cons.2 ⟨sub6_1005, List.forall_mem_cons.2 ⟨sub6_1006, List.forall_mem_cons.2 ⟨sub6_1007, List.forall_mem_cons.2 ⟨sub6_1008, List.forall_mem_cons.2 ⟨sub6_1009, List.forall_mem_cons.2 ⟨sub6_1010, List.forall_mem_cons.2 ⟨sub6_1011, List.forall_mem_cons.2 ⟨sub6_1012, List.forall_mem_cons.2 ⟨sub6_1013, List.forall_mem_cons.2 ⟨sub6_1014, List.forall_mem_cons.2 ⟨sub6_1015, List.forall_mem_cons.2 ⟨sub6_1016, List.forall_mem_cons.2 ⟨sub6_1017, List.forall_mem_cons.2 ⟨sub6_1018, List.forall_mem_cons.2 ⟨sub6_1019, List.forall_mem_cons.2 ⟨sub6_1020, List.forall_mem_cons.2 ⟨sub6_1021, List.forall_mem_cons.2 ⟨sub6_1022, List.forall_mem_cons.2 ⟨sub6_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_1024 : sub6 [4, 1, 2] = true := by decide +kernel
theorem sub6_1025 : sub6 [4, 1, 3] = true := by decide +kernel
theorem sub6_1026 : sub6 [4, 1, 4] = true := by decide +kernel
theorem sub6_1027 : sub6 [4, 1, 5] = true := by decide +kernel
theorem sub6_1028 : sub6 [4, 1, 6] = true := by decide +kernel
theorem sub6_1029 : sub6 [4, 1, 7] = true := by decide +kernel
theorem sub6_1030 : sub6 [4, 2] = true := by decide +kernel
theorem sub6_1031 : sub6 [4, 3] = true := by decide +kernel
theorem sub6_1032 : sub6 [4, 4] = true := by decide +kernel
theorem sub6_1033 : sub6 [5, -3] = true := by decide +kernel
theorem sub6_1034 : sub6 [5, -2] = true := by decide +kernel
theorem sub6_1035 : sub6 [5, -1] = true := by decide +kernel
theorem sub6_1036 : sub6 [5, 0] = true := by decide +kernel
theorem sub6_1037 : sub6 [5, 1] = true := by decide +kernel
theorem sub6_1038 : sub6 [5, 2] = true := by decide +kernel
theorem sb6_32 : ∀ q ∈ blk6_32, sub6 q = true := by
  unfold blk6_32
  exact List.forall_mem_cons.2 ⟨sub6_1024, List.forall_mem_cons.2 ⟨sub6_1025, List.forall_mem_cons.2 ⟨sub6_1026, List.forall_mem_cons.2 ⟨sub6_1027, List.forall_mem_cons.2 ⟨sub6_1028, List.forall_mem_cons.2 ⟨sub6_1029, List.forall_mem_cons.2 ⟨sub6_1030, List.forall_mem_cons.2 ⟨sub6_1031, List.forall_mem_cons.2 ⟨sub6_1032, List.forall_mem_cons.2 ⟨sub6_1033, List.forall_mem_cons.2 ⟨sub6_1034, List.forall_mem_cons.2 ⟨sub6_1035, List.forall_mem_cons.2 ⟨sub6_1036, List.forall_mem_cons.2 ⟨sub6_1037, List.forall_mem_cons.2 ⟨sub6_1038, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_0 : sub7 [-8] = true := by decide +kernel
theorem sub7_1 : sub7 [-7, -6] = true := by decide +kernel
theorem sub7_2 : sub7 [-7, -5] = true := by decide +kernel
theorem sub7_3 : sub7 [-7, -4] = true := by decide +kernel
theorem sub7_4 : sub7 [-7, -3] = true := by decide +kernel
theorem sub7_5 : sub7 [-7, -2] = true := by decide +kernel
theorem sub7_6 : sub7 [-7, -1] = true := by decide +kernel
theorem sub7_7 : sub7 [-7, 0] = true := by decide +kernel
theorem sub7_8 : sub7 [-7, 1] = true := by decide +kernel
theorem sub7_9 : sub7 [-7, 2] = true := by decide +kernel
theorem sub7_10 : sub7 [-6, -7] = true := by decide +kernel
theorem sub7_11 : sub7 [-6, -6] = true := by decide +kernel
theorem sub7_12 : sub7 [-6, -5] = true := by decide +kernel
theorem sub7_13 : sub7 [-6, -4] = true := by decide +kernel
theorem sub7_14 : sub7 [-6, -3] = true := by decide +kernel
theorem sub7_15 : sub7 [-6, -2] = true := by decide +kernel
theorem sub7_16 : sub7 [-6, -1] = true := by decide +kernel
theorem sub7_17 : sub7 [-6, 0] = true := by decide +kernel
theorem sub7_18 : sub7 [-6, 1] = true := by decide +kernel
theorem sub7_19 : sub7 [-6, 2] = true := by decide +kernel
theorem sub7_20 : sub7 [-6, 3] = true := by decide +kernel
theorem sub7_21 : sub7 [-5, -7] = true := by decide +kernel
theorem sub7_22 : sub7 [-5, -6] = true := by decide +kernel
theorem sub7_23 : sub7 [-5, -5] = true := by decide +kernel
theorem sub7_24 : sub7 [-5, -4] = true := by decide +kernel
theorem sub7_25 : sub7 [-5, -3] = true := by decide +kernel
theorem sub7_26 : sub7 [-5, -2] = true := by decide +kernel
theorem sub7_27 : sub7 [-5, -1, -8] = true := by decide +kernel
theorem sub7_28 : sub7 [-5, -1, -7] = true := by decide +kernel
theorem sub7_29 : sub7 [-5, -1, -6] = true := by decide +kernel
theorem sub7_30 : sub7 [-5, -1, -5] = true := by decide +kernel
theorem sub7_31 : sub7 [-5, -1, -4] = true := by decide +kernel
theorem sb7_0 : ∀ q ∈ blk7_0, sub7 q = true := by
  unfold blk7_0
  exact List.forall_mem_cons.2 ⟨sub7_0, List.forall_mem_cons.2 ⟨sub7_1, List.forall_mem_cons.2 ⟨sub7_2, List.forall_mem_cons.2 ⟨sub7_3, List.forall_mem_cons.2 ⟨sub7_4, List.forall_mem_cons.2 ⟨sub7_5, List.forall_mem_cons.2 ⟨sub7_6, List.forall_mem_cons.2 ⟨sub7_7, List.forall_mem_cons.2 ⟨sub7_8, List.forall_mem_cons.2 ⟨sub7_9, List.forall_mem_cons.2 ⟨sub7_10, List.forall_mem_cons.2 ⟨sub7_11, List.forall_mem_cons.2 ⟨sub7_12, List.forall_mem_cons.2 ⟨sub7_13, List.forall_mem_cons.2 ⟨sub7_14, List.forall_mem_cons.2 ⟨sub7_15, List.forall_mem_cons.2 ⟨sub7_16, List.forall_mem_cons.2 ⟨sub7_17, List.forall_mem_cons.2 ⟨sub7_18, List.forall_mem_cons.2 ⟨sub7_19, List.forall_mem_cons.2 ⟨sub7_20, List.forall_mem_cons.2 ⟨sub7_21, List.forall_mem_cons.2 ⟨sub7_22, List.forall_mem_cons.2 ⟨sub7_23, List.forall_mem_cons.2 ⟨sub7_24, List.forall_mem_cons.2 ⟨sub7_25, List.forall_mem_cons.2 ⟨sub7_26, List.forall_mem_cons.2 ⟨sub7_27, List.forall_mem_cons.2 ⟨sub7_28, List.forall_mem_cons.2 ⟨sub7_29, List.forall_mem_cons.2 ⟨sub7_30, List.forall_mem_cons.2 ⟨sub7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_32 : sub7 [-5, -1, -3] = true := by decide +kernel
theorem sub7_33 : sub7 [-5, -1, -2] = true := by decide +kernel
theorem sub7_34 : sub7 [-5, -1, -1] = true := by decide +kernel
theorem sub7_35 : sub7 [-5, -1, 0] = true := by decide +kernel
theorem sub7_36 : sub7 [-5, -1, 1] = true := by decide +kernel
theorem sub7_37 : sub7 [-5, -1, 2] = true := by decide +kernel
theorem sub7_38 : sub7 [-5, -1, 3] = true := by decide +kernel
theorem sub7_39 : sub7 [-5, -1, 4] = true := by decide +kernel
theorem sub7_40 : sub7 [-5, -1, 5] = true := by decide +kernel
theorem sub7_41 : sub7 [-5, 0] = true := by decide +kernel
theorem sub7_42 : sub7 [-5, 1] = true := by decide +kernel
theorem sub7_43 : sub7 [-5, 2] = true := by decide +kernel
theorem sub7_44 : sub7 [-5, 3] = true := by decide +kernel
theorem sub7_45 : sub7 [-5, 4] = true := by decide +kernel
theorem sub7_46 : sub7 [-4, -8] = true := by decide +kernel
theorem sub7_47 : sub7 [-4, -7] = true := by decide +kernel
theorem sub7_48 : sub7 [-4, -6] = true := by decide +kernel
theorem sub7_49 : sub7 [-4, -5] = true := by decide +kernel
theorem sub7_50 : sub7 [-4, -4] = true := by decide +kernel
theorem sub7_51 : sub7 [-4, -3, -8] = true := by decide +kernel
theorem sub7_52 : sub7 [-4, -3, -7] = true := by decide +kernel
theorem sub7_53 : sub7 [-4, -3, -6] = true := by decide +kernel
theorem sub7_54 : sub7 [-4, -3, -5] = true := by decide +kernel
theorem sub7_55 : sub7 [-4, -3, -4] = true := by decide +kernel
theorem sub7_56 : sub7 [-4, -3, -3] = true := by decide +kernel
theorem sub7_57 : sub7 [-4, -3, -2] = true := by decide +kernel
theorem sub7_58 : sub7 [-4, -3, -1] = true := by decide +kernel
theorem sub7_59 : sub7 [-4, -3, 0] = true := by decide +kernel
theorem sub7_60 : sub7 [-4, -3, 1] = true := by decide +kernel
theorem sub7_61 : sub7 [-4, -3, 2] = true := by decide +kernel
theorem sub7_62 : sub7 [-4, -3, 3] = true := by decide +kernel
theorem sub7_63 : sub7 [-4, -3, 4] = true := by decide +kernel
theorem sb7_1 : ∀ q ∈ blk7_1, sub7 q = true := by
  unfold blk7_1
  exact List.forall_mem_cons.2 ⟨sub7_32, List.forall_mem_cons.2 ⟨sub7_33, List.forall_mem_cons.2 ⟨sub7_34, List.forall_mem_cons.2 ⟨sub7_35, List.forall_mem_cons.2 ⟨sub7_36, List.forall_mem_cons.2 ⟨sub7_37, List.forall_mem_cons.2 ⟨sub7_38, List.forall_mem_cons.2 ⟨sub7_39, List.forall_mem_cons.2 ⟨sub7_40, List.forall_mem_cons.2 ⟨sub7_41, List.forall_mem_cons.2 ⟨sub7_42, List.forall_mem_cons.2 ⟨sub7_43, List.forall_mem_cons.2 ⟨sub7_44, List.forall_mem_cons.2 ⟨sub7_45, List.forall_mem_cons.2 ⟨sub7_46, List.forall_mem_cons.2 ⟨sub7_47, List.forall_mem_cons.2 ⟨sub7_48, List.forall_mem_cons.2 ⟨sub7_49, List.forall_mem_cons.2 ⟨sub7_50, List.forall_mem_cons.2 ⟨sub7_51, List.forall_mem_cons.2 ⟨sub7_52, List.forall_mem_cons.2 ⟨sub7_53, List.forall_mem_cons.2 ⟨sub7_54, List.forall_mem_cons.2 ⟨sub7_55, List.forall_mem_cons.2 ⟨sub7_56, List.forall_mem_cons.2 ⟨sub7_57, List.forall_mem_cons.2 ⟨sub7_58, List.forall_mem_cons.2 ⟨sub7_59, List.forall_mem_cons.2 ⟨sub7_60, List.forall_mem_cons.2 ⟨sub7_61, List.forall_mem_cons.2 ⟨sub7_62, List.forall_mem_cons.2 ⟨sub7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_64 : sub7 [-4, -3, 5] = true := by decide +kernel
theorem sub7_65 : sub7 [-4, -2, -8] = true := by decide +kernel
theorem sub7_66 : sub7 [-4, -2, -7] = true := by decide +kernel
theorem sub7_67 : sub7 [-4, -2, -6] = true := by decide +kernel
theorem sub7_68 : sub7 [-4, -2, -5] = true := by decide +kernel
theorem sub7_69 : sub7 [-4, -2, -4] = true := by decide +kernel
theorem sub7_70 : sub7 [-4, -2, -3] = true := by decide +kernel
theorem sub7_71 : sub7 [-4, -2, -2] = true := by decide +kernel
theorem sub7_72 : sub7 [-4, -2, -1] = true := by decide +kernel
theorem sub7_73 : sub7 [-4, -2, 0] = true := by decide +kernel
theorem sub7_74 : sub7 [-4, -2, 1] = true := by decide +kernel
theorem sub7_75 : sub7 [-4, -2, 2] = true := by decide +kernel
theorem sub7_76 : sub7 [-4, -2, 3] = true := by decide +kernel
theorem sub7_77 : sub7 [-4, -2, 4] = true := by decide +kernel
theorem sub7_78 : sub7 [-4, -2, 5] = true := by decide +kernel
theorem sub7_79 : sub7 [-4, -2, 6] = true := by decide +kernel
theorem sub7_80 : sub7 [-4, -1, -8] = true := by decide +kernel
theorem sub7_81 : sub7 [-4, -1, -7] = true := by decide +kernel
theorem sub7_82 : sub7 [-4, -1, -6] = true := by decide +kernel
theorem sub7_83 : sub7 [-4, -1, -5] = true := by decide +kernel
theorem sub7_84 : sub7 [-4, -1, -4] = true := by decide +kernel
theorem sub7_85 : sub7 [-4, -1, -3] = true := by decide +kernel
theorem sub7_86 : sub7 [-4, -1, -2] = true := by decide +kernel
theorem sub7_87 : sub7 [-4, -1, -1] = true := by decide +kernel
theorem sub7_88 : sub7 [-4, -1, 0] = true := by decide +kernel
theorem sub7_89 : sub7 [-4, -1, 1] = true := by decide +kernel
theorem sub7_90 : sub7 [-4, -1, 2] = true := by decide +kernel
theorem sub7_91 : sub7 [-4, -1, 3] = true := by decide +kernel
theorem sub7_92 : sub7 [-4, -1, 4] = true := by decide +kernel
theorem sub7_93 : sub7 [-4, -1, 5] = true := by decide +kernel
theorem sub7_94 : sub7 [-4, -1, 6] = true := by decide +kernel
theorem sub7_95 : sub7 [-4, 0, -8] = true := by decide +kernel
theorem sb7_2 : ∀ q ∈ blk7_2, sub7 q = true := by
  unfold blk7_2
  exact List.forall_mem_cons.2 ⟨sub7_64, List.forall_mem_cons.2 ⟨sub7_65, List.forall_mem_cons.2 ⟨sub7_66, List.forall_mem_cons.2 ⟨sub7_67, List.forall_mem_cons.2 ⟨sub7_68, List.forall_mem_cons.2 ⟨sub7_69, List.forall_mem_cons.2 ⟨sub7_70, List.forall_mem_cons.2 ⟨sub7_71, List.forall_mem_cons.2 ⟨sub7_72, List.forall_mem_cons.2 ⟨sub7_73, List.forall_mem_cons.2 ⟨sub7_74, List.forall_mem_cons.2 ⟨sub7_75, List.forall_mem_cons.2 ⟨sub7_76, List.forall_mem_cons.2 ⟨sub7_77, List.forall_mem_cons.2 ⟨sub7_78, List.forall_mem_cons.2 ⟨sub7_79, List.forall_mem_cons.2 ⟨sub7_80, List.forall_mem_cons.2 ⟨sub7_81, List.forall_mem_cons.2 ⟨sub7_82, List.forall_mem_cons.2 ⟨sub7_83, List.forall_mem_cons.2 ⟨sub7_84, List.forall_mem_cons.2 ⟨sub7_85, List.forall_mem_cons.2 ⟨sub7_86, List.forall_mem_cons.2 ⟨sub7_87, List.forall_mem_cons.2 ⟨sub7_88, List.forall_mem_cons.2 ⟨sub7_89, List.forall_mem_cons.2 ⟨sub7_90, List.forall_mem_cons.2 ⟨sub7_91, List.forall_mem_cons.2 ⟨sub7_92, List.forall_mem_cons.2 ⟨sub7_93, List.forall_mem_cons.2 ⟨sub7_94, List.forall_mem_cons.2 ⟨sub7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_96 : sub7 [-4, 0, -7] = true := by decide +kernel
theorem sub7_97 : sub7 [-4, 0, -6] = true := by decide +kernel
theorem sub7_98 : sub7 [-4, 0, -5] = true := by decide +kernel
theorem sub7_99 : sub7 [-4, 0, -4] = true := by decide +kernel
theorem sub7_100 : sub7 [-4, 0, -3] = true := by decide +kernel
theorem sub7_101 : sub7 [-4, 0, -2] = true := by decide +kernel
theorem sub7_102 : sub7 [-4, 0, -1] = true := by decide +kernel
theorem sub7_103 : sub7 [-4, 0, 0] = true := by decide +kernel
theorem sub7_104 : sub7 [-4, 0, 1] = true := by decide +kernel
theorem sub7_105 : sub7 [-4, 0, 2] = true := by decide +kernel
theorem sub7_106 : sub7 [-4, 0, 3] = true := by decide +kernel
theorem sub7_107 : sub7 [-4, 0, 4] = true := by decide +kernel
theorem sub7_108 : sub7 [-4, 0, 5] = true := by decide +kernel
theorem sub7_109 : sub7 [-4, 0, 6] = true := by decide +kernel
theorem sub7_110 : sub7 [-4, 1, -8] = true := by decide +kernel
theorem sub7_111 : sub7 [-4, 1, -7] = true := by decide +kernel
theorem sub7_112 : sub7 [-4, 1, -6] = true := by decide +kernel
theorem sub7_113 : sub7 [-4, 1, -5] = true := by decide +kernel
theorem sub7_114 : sub7 [-4, 1, -4] = true := by decide +kernel
theorem sub7_115 : sub7 [-4, 1, -3] = true := by decide +kernel
theorem sub7_116 : sub7 [-4, 1, -2] = true := by decide +kernel
theorem sub7_117 : sub7 [-4, 1, -1] = true := by decide +kernel
theorem sub7_118 : sub7 [-4, 1, 0] = true := by decide +kernel
theorem sub7_119 : sub7 [-4, 1, 1] = true := by decide +kernel
theorem sub7_120 : sub7 [-4, 1, 2] = true := by decide +kernel
theorem sub7_121 : sub7 [-4, 1, 3] = true := by decide +kernel
theorem sub7_122 : sub7 [-4, 1, 4] = true := by decide +kernel
theorem sub7_123 : sub7 [-4, 1, 5] = true := by decide +kernel
theorem sub7_124 : sub7 [-4, 1, 6] = true := by decide +kernel
theorem sub7_125 : sub7 [-4, 2, -7] = true := by decide +kernel
theorem sub7_126 : sub7 [-4, 2, -6] = true := by decide +kernel
theorem sub7_127 : sub7 [-4, 2, -5] = true := by decide +kernel
theorem sb7_3 : ∀ q ∈ blk7_3, sub7 q = true := by
  unfold blk7_3
  exact List.forall_mem_cons.2 ⟨sub7_96, List.forall_mem_cons.2 ⟨sub7_97, List.forall_mem_cons.2 ⟨sub7_98, List.forall_mem_cons.2 ⟨sub7_99, List.forall_mem_cons.2 ⟨sub7_100, List.forall_mem_cons.2 ⟨sub7_101, List.forall_mem_cons.2 ⟨sub7_102, List.forall_mem_cons.2 ⟨sub7_103, List.forall_mem_cons.2 ⟨sub7_104, List.forall_mem_cons.2 ⟨sub7_105, List.forall_mem_cons.2 ⟨sub7_106, List.forall_mem_cons.2 ⟨sub7_107, List.forall_mem_cons.2 ⟨sub7_108, List.forall_mem_cons.2 ⟨sub7_109, List.forall_mem_cons.2 ⟨sub7_110, List.forall_mem_cons.2 ⟨sub7_111, List.forall_mem_cons.2 ⟨sub7_112, List.forall_mem_cons.2 ⟨sub7_113, List.forall_mem_cons.2 ⟨sub7_114, List.forall_mem_cons.2 ⟨sub7_115, List.forall_mem_cons.2 ⟨sub7_116, List.forall_mem_cons.2 ⟨sub7_117, List.forall_mem_cons.2 ⟨sub7_118, List.forall_mem_cons.2 ⟨sub7_119, List.forall_mem_cons.2 ⟨sub7_120, List.forall_mem_cons.2 ⟨sub7_121, List.forall_mem_cons.2 ⟨sub7_122, List.forall_mem_cons.2 ⟨sub7_123, List.forall_mem_cons.2 ⟨sub7_124, List.forall_mem_cons.2 ⟨sub7_125, List.forall_mem_cons.2 ⟨sub7_126, List.forall_mem_cons.2 ⟨sub7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C092
